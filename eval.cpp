/*
 * this is kind of a lisp interpreter for my own amusement
 * not at all standards compliant or industrial strength
 * dynamically scoped, without tail call optimization
 *
 * cyclic lists cause trouble
 * syntactic atoms need meta-syntax when displayed
 * quasiquote
 * 
 * Robert Kelley October 2019
 */
#define PSIZE   16384
#define MAX     262144
#undef  BROKEN

#define UNW_LOCAL_ONLY
#ifdef  UNWIND
#include <libunwind.h>
#include <cxxabi.h>
#endif
#include <cmath>
#include <csetjmp>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <set>
#include <ctype.h>

#ifdef BROKEN
#include <assert.h>
#define error(s) do { printf("%s\n", s); assert(0); } while(0)
#else
#define error(s) longjmp(the_jmpbuf, (long)s)
#endif

char errorBuffer[256];

/*
 * storage is managed as a freelist of cells, each potentially containing two pointers
 *
 * if bit 0 is 0 it's a Cons
 * otherwise the type is in the second byte
 * if bit 1 is set then it's marked
 */
enum Tag0
{
    CONS   = 0,
    OTHER  = 1,
    MARK   = 2
};

enum Tag1
{
    ATOM   = 0,
    STRING = 1,
    CHUNK  = 2,
    FORM   = 3,
    FIXNUM = 4,
    FUNCT  = 5,
    FLOAT  = 6,
    DOUBLE = 7,
    CHAR   = 8
};

typedef struct Cons *sexp;
typedef sexp (*Formp)(sexp, sexp);
typedef sexp (*Varargp)(sexp);
typedef sexp (*Oneargp)(sexp);
typedef sexp (*Twoargp)(sexp, sexp);

/*
 * setting up union declarations isn't all that fun but casts are ugly and error-prone.
 */
struct Cons   { sexp                cdr; sexp                     car; };
struct Other  { char                             tags[sizeof(Cons)-0]; };
struct Chunk  { char tags[2];            char    text[sizeof(Cons)-2]; };
struct Atom   { char tags[sizeof(sexp)]; sexp                  chunks; };
struct String { char tags[sizeof(sexp)]; sexp                  chunks; };
struct Fixnum { char tags[sizeof(sexp)]; long                  fixnum; };
struct Float  { char tags[sizeof(Cons)-sizeof(float)];  float  flonum; };
struct Double { char tags[sizeof(Cons)-sizeof(double)]; double flonum; };
struct Funct  { char tags[sizeof(sexp)]; void*                  funcp; };
struct Form   { char tags[sizeof(sexp)]; Formp                  formp; };
struct Char   { char tags[2];            char    text[sizeof(Cons)-2]; };

sexp scan(FILE* fin);
sexp set(sexp p, sexp r);
bool cyclic(sexp p);
sexp define(sexp p, sexp r);
sexp eval(sexp p, sexp env);
sexp evlis(sexp p, sexp env);
sexp read(FILE* fin, int level);
void display(FILE* fout, sexp p, bool write);
void display(FILE* fout, sexp p, std::set<sexp>& seenSet, bool write);
sexp assoc(sexp formals, sexp actuals, sexp env);

// these are the built-in atoms

sexp acosa, adda, alphapa, ampera, anda, applya, asina, atana, atompa, atomsa, begin;
sexp cara, cdra, ceilinga, char2ia, char2inta, charcieqa, charcigea, charcigta;
sexp charcilea, charcilta, chareqa, chargea, chargta, charlea, charlta, charpa;
sexp closurea, cond, consa, cosa, cyclicpa, definea, delaya, displaya, diva, dot;
sexp downcasea, e2ia, elsea, endl, eofa, eofobjp, eqa, eqna, eqva, evala, exactpa;
sexp expa, f, floora, forcea, forcedpa, gea, gta, i2ea, ifa, inexactpa, int2chara;
sexp integerpa, intenva, lambda, lea, let, listpa, loada, loga, lowercasepa, lparen;
sexp lsha, lta, makestringa, minus, moda, modulo, mula, newlinea, nil, nota, nulenva;
sexp nullpa, num2stringa, numberpa, numericpa, ora, pairpa, peekchara, pipea, plus;
sexp powa, procedurepa, promisea, promisepa, promiseva, qchar, quote, rationala;
sexp reada, readchara, readypa, realpa, reversea, rounda, rparen, rsha, s2sya;
sexp seta, setcara, setcdra, sina, sqrta, stringappenda, stringcieq, stringcige;
sexp stringcigt, stringcile, stringcilt, stringcopy, stringeq, stringfill, stringge;
sexp stringgt, stringle, stringlength, stringlt, stringpa, stringref, stringset;
sexp suba, substringa, sy2sa, symbolpa, t, tana, tilde, times, upcasea, uppercasepa;
sexp voida, whilea, whitespacepa, writea, writechara, xora, equalpa;

static inline int  evalType(const sexp p) { return                      ((Other*)p)->tags[1];  }
static inline int  arity(const sexp p)    { return                      ((Other*)p)->tags[2];  }
static inline bool isMarked(const sexp p) { return       (MARK        & ((Other*)p)->tags[0]); }
static inline bool isCons(const sexp p)   { return p && !(OTHER       & ((Other*)p)->tags[0]); }
static inline bool isOther(const sexp p)  { return p &&  (OTHER       & ((Other*)p)->tags[0]); }
static inline bool isAtom(const sexp p)   { return isOther(p) && ATOM   == evalType(p);        }
static inline bool isString(const sexp p) { return isOther(p) && STRING == evalType(p);        }
static inline bool isFunct(const sexp p)  { return isOther(p) && FUNCT  == evalType(p);        }
static inline bool isForm(const sexp p)   { return isOther(p) && FORM   == evalType(p);        }
static inline bool isFixnum(const sexp p) { return isOther(p) && FIXNUM == evalType(p);        }
static inline bool isFloat(const sexp p)  { return isOther(p) && FLOAT  == evalType(p);        }
static inline bool isDouble(const sexp p) { return isOther(p) && DOUBLE == evalType(p);        }
static inline bool isChar(const sexp p)   { return isOther(p) && CHAR   == evalType(p);        }
static inline bool isFlonum(const sexp p) { return isFloat(p) || isDouble(p);                  }

jmp_buf the_jmpbuf;

bool killed = 0;        // to catch consecutive SIGINTs
sexp atoms = 0;         // all atoms are linked in a list
sexp block = 0;         // all the storage starts here
sexp global = 0;        // this is the global symbol table (a list)
sexp freelist = 0;      // available cells are linked in a list
int  marked = 0;        // how many cells were marked during gc
int  allocated = 0;     // how many cells have been allocated
int  total = 0;         // total allocation across gc's
int  collected = 0;     // how many gc's
sexp protect[PSIZE];    // protection stack
sexp *psp = protect;    // protection stack pointer

/*
 * save the argument on the protection stack, return it
 */
sexp save(sexp p)
{
    *psp++ = p;
    if (psp >= protect+PSIZE)
        error("error: protection stack overflow");
    return p;
}

/*
 * pop n items from the protection stack then return p
 */
sexp lose(int n, sexp p)
{
    if (psp-n < protect)
        error("error: protection stack underflow");
    for ( ; n > 0; --n)
    {
        sexp p = *--psp;
        *psp = 0;
    }
    return p;
}

static inline void markCell(sexp p)
{
    ((Other*)p)->tags[0] |=  MARK;
    ++marked;
}

static inline void unmarkCell(sexp p)
{
    ((Other*)p)->tags[0] &= ~MARK;
    --marked;
}

void mark(sexp p);

void markCons(sexp p, std::set<sexp>& seenSet)
{
    if (!p || isMarked(p))
        return;

    // this ought be unnecessary...
    if (seenSet.find(p) != seenSet.end())
        return;

    seenSet.insert(p);

    if (isCons(p->car))
        markCons(p->car, seenSet);
    else
        mark(p->car);
    if (isCons(p->cdr))
        markCons(p->cdr, seenSet);
    else
        mark(p->cdr);
    markCell(p);
}

/*
 * visit objects reachable from p, setting their MARK bit
 */
void mark(sexp p)
{
    if (!p || isMarked(p))
        return;

    if (isCons(p)) {
        std::set<sexp> seenSet;
        markCons(p, seenSet);
    } else if (isAtom(p)) {
        mark(((Atom*)p)->chunks);
        markCell(p);
    } else if (isString(p)) {
        mark(((String*)p)->chunks);
        markCell(p);
    } else
        markCell(p);
}

/*
 * mark all reachable objects
 *
 * sweep all storage, putting unmarked objects on the freelist
 */
void gc(bool verbose)
{
    int werefree = MAX-allocated;
    int wereprot = psp-protect;

    marked = 0;
    mark(atoms);
    mark(global);
    for (sexp *p = protect; p < psp; ++p)
        mark(*p);

    int weremark = marked;
    int reclaimed = 0;

    freelist = 0;
    for (sexp p = block; p < block+MAX; ++p)
    {
        if (!isMarked(p))
        {
            p->car = 0;
            p->cdr = freelist;
            freelist = p;
            ++reclaimed;
        } else 
            unmarkCell(p);
    }

    if (verbose)
        printf("gc: allocated: %d protected: %d marked: %d reclaimed: %d collections: %d allocation: %d\n",
               allocated, wereprot, weremark, reclaimed, collected, total);

    allocated -= reclaimed-werefree;
    total += allocated;
    ++collected;
    if (!freelist)
        error("error: storage exhausted");
}

/*
 * allocate a cell from the freelist
 */
sexp cell(void)
{
    if (allocated >= MAX)
        gc(false);

    ++allocated;
    Cons* p = freelist;
    freelist = freelist->cdr;
    p->cdr = 0;
    return p;
}

sexp atom(sexp chunks)
{
    save(chunks);
    Atom* p = (Atom*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = ATOM;
    p->chunks = chunks;
    return lose(1, (sexp)p);
}

sexp string(sexp chunks)
{
    save(chunks);
    String* p = (String*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = STRING;
    p->chunks = chunks;
    return lose(1, (sexp)p);
}

sexp fixnum(long number)
{
    Fixnum* p = (Fixnum*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = FIXNUM;
    p->fixnum = number;
    return (sexp)p;
}

sexp character(char c)
{
    Char* p = (Char*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = CHAR;
    p->text[0] = c;
    return (sexp)p;
}

sexp flonum(double number)
{
    if (sizeof(double) > sizeof(void*)) {
        Float* p = (Float*)cell();
        p->tags[0] = OTHER;
        p->tags[1] = FLOAT;
        p->flonum = number;
        return (sexp)p;
    } else {
        Double* p = (Double*)cell();
        p->tags[0] = OTHER;
        p->tags[1] = DOUBLE;
        p->flonum = number;
        return (sexp)p;
    }
}

sexp define_form(sexp name, Formp f)
{
    Form* p = (Form*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = FORM;
    p->formp = f;
    return lose(1, define(name, save((sexp)p)));
}

sexp define_funct(sexp name, int arity, void* f)
{
    Funct* p = (Funct*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = FUNCT;
    p->tags[2] = arity;
    p->funcp = f;
    return lose(1, define(name, save((sexp)p)));
}

sexp cons(sexp car, sexp cdr)
{
    save(car);
    save(cdr);
    sexp p = cell();
    p->car = car;
    p->cdr = cdr;
    return lose(2, p);
}

sexp car(sexp p)
{
    if (!isCons(p))
        error("error: car of non-pair");
    return p->car;
}

sexp cdr(sexp p)
{
    if (!isCons(p))
        error("error: cdr of non-pair");
    return p->cdr;
}

sexp setcarf(sexp p, sexp q)
{
    if (!isCons(p))
        error("error: set-car! of non-pair");
    sexp r = p->car;
    p->car = q;
    return r;
}

sexp setcdrf(sexp p, sexp q)
{
    if (!isCons(p))
        error("error: set-cdr! of non-pair");
    sexp r = p->cdr;
    p->cdr = q;
    return r;
}

sexp andform(sexp p, sexp env)
{
    save(p);
    save(env);
    sexp q = t;
    while (p = p->cdr)
    {
        q = eval(p->car, env);
        if (!q)
            break;
    }
    return lose(2, q);
}

sexp orform(sexp p, sexp env)
{
    save(p);
    save(env);
    sexp q = 0;
    while (p = p->cdr)
    {
        q = eval(p->car, env);
        if (q)
            break;
    }
    return lose(2, q);
}

long asFixnum(sexp p)
{
    return isDouble(p) ? (long)((Double*)p)->flonum :
           isFloat(p)  ? (long)((Float*)p)->flonum :
                         ((Fixnum*)p)->fixnum;
}

double asFlonum(sexp p)
{
    return isFixnum(p) ? (double)((Fixnum*)p)->fixnum :
           isDouble(p) ? ((Double*)p)->flonum :
                         ((Float*)p)->flonum;
}

bool cmplt(sexp x, sexp y)
{
    if (isFlonum(x)) {
        if (isFlonum(y))
            return asFlonum(x) < asFlonum(y);
        if (isFixnum(y))
            return asFlonum(x) < (double)asFixnum(y);
    } else if (isFixnum(x)) {
        if (isFixnum(y))
            return asFixnum(x) < asFixnum(y);
        if (isFlonum(y))
            return (double)asFixnum(x) < asFixnum(y);
    }
    error("error: comparison bad argument");
}

bool cmple(sexp x, sexp y)
{
    if (isFlonum(x)) {
        if (isFlonum(y))
            return asFlonum(x) <= asFlonum(y);
        if (isFixnum(y))
            return asFlonum(x) <= (double)asFixnum(y);
    } else if (isFixnum(x)) {
        if (isFixnum(y))
            return asFixnum(x) <= asFixnum(y);
        if (isFlonum(y))
            return (double)asFixnum(x) <= asFixnum(y);
    }
    error("error: comparison bad argument");
}

sexp lt(sexp x, sexp y)
{
    return cmplt(x, y) ? t : 0;
}

sexp le(sexp x, sexp y)
{
    return cmple(x, y) ? t : 0;
}

sexp ge(sexp x, sexp y)
{
    return cmplt(x, y) ? 0 : t;
}

sexp gt(sexp x, sexp y)
{
    return cmple(x, y) ? 0 : t;
}

sexp addf(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return fixnum(asFixnum(x) + asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFixnum(x) + asFlonum(y));
        else
            return 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return flonum(asFlonum(x) + asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFlonum(x) + asFlonum(y));
        else
            return 0;
    } else
        return 0;
}

sexp subf(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return fixnum(asFixnum(x) - asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFixnum(x) - asFlonum(y));
        else
            return 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return flonum(asFlonum(x) - asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFlonum(x) - asFlonum(y));
        else
            return 0;
    } else
        return 0;
}

sexp mulf(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return fixnum(asFixnum(x) * asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFixnum(x) * asFlonum(y));
        else
            return 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return flonum(asFlonum(x) * asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFlonum(x) * asFlonum(y));
        else
            return 0;
    } else
        return 0;
}

sexp divf(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return fixnum(asFixnum(x) / asFixnum(y));
        else if (isFlonum(y))
            return flonum((double)asFixnum(x) / asFlonum(y));
        else
            return 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return flonum(asFlonum(x) / asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFlonum(x) / asFlonum(y));
        else
            return 0;
    } else
        return 0;
}

sexp modfn(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return fixnum(asFixnum(x) % asFixnum(y));
        else if (isFlonum(y))
            return flonum(fmod((double)asFixnum(x), asFlonum(y)));
        else
            return 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return flonum(fmod(asFlonum(x), (double)asFixnum(y)));
        else if (isFlonum(y))
            return flonum(fmod(asFlonum(x), asFlonum(y)));
        else
            return 0;
    } else
        return 0;
}

/*
 * a rational is really just a list (rational numerator denominator)
 */
bool isRational(sexp exp)
{
    return isCons(exp) &&
           rationala == exp->car && exp->cdr && exp->cdr->car &&
           exp->cdr->cdr && exp->cdr->cdr->car && !exp->cdr->cdr->cdr;
}

// functions on real numbers
sexp sinff(sexp x) { return isFlonum(x) ? flonum(sin(asFlonum(x))) : 0; }
sexp cosff(sexp x) { return isFlonum(x) ? flonum(cos(asFlonum(x))) : 0; }
sexp tanff(sexp x) { return isFlonum(x) ? flonum(tan(asFlonum(x))) : 0; }
sexp expff(sexp x) { return isFlonum(x) ? flonum(exp(asFlonum(x))) : 0; }
sexp logff(sexp x) { return isFlonum(x) ? flonum(log(asFlonum(x))) : 0; }
sexp asinff(sexp x) { return isFlonum(x) ? flonum(asin(asFlonum(x))) : 0; }
sexp acosff(sexp x) { return isFlonum(x) ? flonum(acos(asFlonum(x))) : 0; }
sexp atanff(sexp x) { return isFlonum(x) ? flonum(atan(asFlonum(x))) : 0; }
sexp ceilingff(sexp x) { return isFlonum(x) ? flonum(ceil(asFlonum(x))) : 0; }
sexp floorff(sexp x) { return isFlonum(x) ? flonum(floor(asFlonum(x))) : 0; }
sexp roundff(sexp x) { return isFlonum(x) ? flonum(round(asFlonum(x))) : 0; }
sexp sqrtff(sexp x) { return isFlonum(x) ? flonum(sqrt(asFlonum(x))) : 0; }
sexp powff(sexp x, sexp y) { return isFlonum(x) && isFlonum(y) ? flonum(pow(asFlonum(x), asFlonum(y))) : 0; }

// exact, inexact
sexp exactp(sexp x) { return isFixnum(x) ? t : 0; }
sexp integerp(sexp x) { return isFixnum(x) ? t : 0; }
sexp inexactp(sexp x) { return isFlonum(x) ? t : 0; }
sexp realp(sexp x) { return isFlonum(x) ? t : 0; }
sexp i2ef(sexp x) { return isFlonum(x) ? fixnum((long)asFlonum(x)) : 0; }
sexp e2if(sexp x) { return isFixnum(x) ? flonum((double)asFixnum(x)) : 0; }

// shifts
sexp lsh(sexp x, sexp y) { return isFixnum(x) && isFixnum(y) ? fixnum(asFixnum(x) << asFixnum(y)) : 0; }
sexp rsh(sexp x, sexp y) { return isFixnum(x) && isFixnum(y) ? fixnum(asFixnum(x) >> asFixnum(y)) : 0; }

// list structure predicates
sexp isnot(sexp x) { return x ? 0 : t; }
sexp nullp(sexp x) { return x ? 0 : t; }
sexp cyclicp(sexp x) { return cyclic(x) ? t : 0; }
sexp listp(sexp x) { return !isCons(x) ? 0 : listp(x->cdr) ? t : 0; }
sexp pairp(sexp x) { return isCons(x) ? t : 0; }
sexp numberp(sexp x) { return isFixnum(x) || isFlonum(x) ? t : 0; }
sexp stringp(sexp x) { return isString(x) ? t : 0; }
sexp symbolp(sexp x) { return isAtom(x) ? t : 0; }
sexp procedurep(sexp p) { return p && (isFunct(p) || isCons(p) && closurea == p->car) ? t : 0; }

void assertString(sexp s)
{
    if (!isString(s))
        error("not a string");
}

int slen(sexp s)
{
    if (!isString(s) && !isAtom(s))
        error("length of non-string, non-atom");

    int length = 0;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        int i = 0;
        Chunk* t = (Chunk*)(p->car);
        while (i < sizeof(t->text) && t->text[i])
            ++i;
        length += i;
    }
    return length;
}

sexp stringlengthf(sexp s)
{
    assertString(s);
    return fixnum(slen(s));
}

char* sref(sexp s, int i)
{
    assertString(s);

    int j = 0;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        if (j <= i && i < j+sizeof(t->text))
            return t->text + (i - j);
        j += sizeof(t->text);
    }

    return 0;
}

/*
 * construct a linked list of chunks of characters
 */
sexp chunk(const char *t)
{
    if (0 == *t)
        return 0;

    sexp p = cell();
    save(p);
    sexp q = p;
    Chunk* r = (Chunk*) cell();
    r->tags[0] = OTHER;
    r->tags[1] = CHUNK;
    q->car = (sexp) r;

    int i = 0;
    for (;;)
    {
        char c = *t++;

        if (!c)
        {
            while (i < sizeof(r->text))
                r->text[i++] = 0;
            return lose(1, p);
        }

        r->text[i++] = c;

        if (i == sizeof(r->text))
        {
            i = 0;
            q = q->cdr = cell();
            r = (Chunk*) cell();
            r->tags[0] = OTHER;
            r->tags[1] = CHUNK;
            q->car = (sexp) r;
        }
    }
}

sexp num2string(sexp num)
{
    char b[32];
    if (isFixnum(num))
        sprintf(b, "%ld", ((Fixnum*)num)->fixnum);
    else if (isFloat(num))
        sprintf(b, "%#.8g", asFlonum(num));
    else if (isDouble(num))
        sprintf(b, "%#.15g", asFlonum(num));
    return lose(1, string(save(chunk(b))));
}

sexp makestring(sexp args)
{
    if (!args || !isFixnum(args->car))
        error("make-string: args missing");

    int l = asFixnum(args->car);
    char *b = (char*) alloca(l+1);
    char *q = b;
    char c = args->cdr && isChar(args->cdr->car) ? ((Char*)(args->cdr->car))->text[0] : ' ';
    for (int i = 0; i < l; ++i)
        *q++ = c;
    *q++ = 0;
    return lose(1, string(save(chunk(b))));
}

sexp stringcopyf(sexp s)
{
    assertString(s);

    char *b = (char*) alloca(slen(s)+1);
    char *q = b;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; *q++ = t->text[i++]) {}
    }
    *q++ = 0;
    return string(save(chunk(b)));
}

sexp stringappend(sexp p, sexp q)
{
    assertString(p);
    assertString(q);

    char *b = (char*) alloca(slen(p)+slen(q)+1);
    char *s = b;
    for (sexp r = ((String*)p)->chunks; r; r = r->cdr)
    {
        Chunk* t = (Chunk*)(r->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; *s++ = t->text[i++]) {}
    }
    for (sexp r = ((String*)q)->chunks; r; r = r->cdr)
    {
        Chunk* t = (Chunk*)(r->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; *s++ = t->text[i++]) {}
    }
    *s++ = 0;
    return string(save(chunk(b)));
}

void assertChar(sexp c)
{
    if (!isChar(c))
        error("not a character");
}

void assertFixnum(sexp i)
{
    if (!isFixnum(i))
        error("not an integer");
}

sexp stringfillf(sexp s, sexp c)
{
    assertString(s);
    assertChar(c);

    char k = ((Char*)c)->text[0];
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; t->text[i++] = k) {}
    }
    return s;
}

/*
 * compare chunks
 */
int scmp(sexp p, sexp q)
{
    for (;;)
    {
        if (p == q)
            return  0;
        if (!q)
            return  1;
        if (!p)
            return -1;
        Chunk* s = (Chunk*)(p->car);
        Chunk* t = (Chunk*)(q->car);
        for (int i = 0; i < sizeof(s->text); ++i)
        {
            int r = s->text[i] - t->text[i];
            if (r)
                return r;
            if (0 == s->text[i])
                return 0;
        }
        p = p->cdr;
        q = q->cdr;
    }
}

/*
 * compare chunks, case insensitive
 */
int scmpi(sexp p, sexp q)
{
    for (;;)
    {
        if (p == q)
            return  0;
        if (!q)
            return  1;
        if (!p)
            return -1;
        Chunk* s = (Chunk*)(p->car);
        Chunk* t = (Chunk*)(q->car);
        for (int i = 0; i < sizeof(s->text); ++i)
        {
            int r = tolower(s->text[i]) - tolower(t->text[i]);
            if (r)
                return r;
            if (0 == s->text[i])
                return 0;
        }
        p = p->cdr;
        q = q->cdr;
    }
}

sexp alphap(sexp c) { return isChar(c) && isalpha(((Char*)c)->text[0]) ? t : 0; }
sexp char2int(sexp c) { assertChar(c); return  fixnum(((Char*)c)->text[0]); }
sexp charcieq(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->text[0]) == tolower(((Char*)q)->text[0]) ? t : 0; }
sexp charcige(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->text[0]) >= tolower(((Char*)q)->text[0]) ? t : 0; }
sexp charcigt(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->text[0]) >  tolower(((Char*)q)->text[0]) ? t : 0; }
sexp charcile(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->text[0]) <= tolower(((Char*)q)->text[0]) ? t : 0; }
sexp charcilt(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->text[0]) <  tolower(((Char*)q)->text[0]) ? t : 0; }
sexp chareq(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->text[0] == ((Char*)q)->text[0] ? t : 0; }
sexp charge(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->text[0] >= ((Char*)q)->text[0] ? t : 0; }
sexp chargt(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->text[0] >  ((Char*)q)->text[0] ? t : 0; }
sexp charle(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->text[0] <= ((Char*)q)->text[0] ? t : 0; }
sexp charlt(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->text[0] <  ((Char*)q)->text[0] ? t : 0; }
sexp charp(sexp c) { return isChar(c) ? t : 0; }
sexp downcase(sexp c) { assertChar(c); return character(tolower(((Char*)c)->text[0])); }
sexp int2char(sexp c) { assertFixnum(c); return character(asFixnum(c)); }
sexp lowercasep(sexp c) { return isChar(c) && islower(((Char*)c)->text[0]) ? t : 0; }
sexp numericp(sexp c) { return isChar(c) && isdigit(((Char*)c)->text[0]) ? t : 0; }
sexp readyp(sexp c) { return 0; }
sexp upcase(sexp c) { assertChar(c); return character(toupper(((Char*)c)->text[0])); }
sexp uppercasep(sexp c) { return isChar(c) && isupper(((Char*)c)->text[0]) ? t : 0; }
sexp whitespacep(sexp c) { return isChar(c) && isspace(((Char*)c)->text[0]) ? t : 0; }

sexp peekchar(sexp args)
{
    if (args)
        error("ports not implemented");
    char c = getc(stdin);
    ungetc(c, stdin);
    return character(c);
}

sexp readchar(sexp args)
{
    if (args)
        error("ports not implemented");
    char c = getc(stdin);
    return character(c);
}

sexp writechar(sexp args)
{
    if (args)
    {
        assertChar(args->car);
        if (args->cdr)
            error("ports not implemented");
    }
    fprintf(stdout, "#\\%c", ((Char*)(args->car))->text[0]);
    return args->car;
}

sexp achunk(sexp s)
{
    assertString(s);
    return ((String*)s)->chunks;
}

sexp stringlef(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) <= 0 ? t : 0; }
sexp stringltf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) <  0 ? t : 0; }
sexp stringeqf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) == 0 ? t : 0; }
sexp stringgef(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) >= 0 ? t : 0; }
sexp stringgtf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) >  0 ? t : 0; }

sexp stringcilef(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) <= 0 ? t : 0; }
sexp stringciltf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) <  0 ? t : 0; }
sexp stringcieqf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) == 0 ? t : 0; }
sexp stringcigef(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) >= 0 ? t : 0; }
sexp stringcigtf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) >  0 ? t : 0; }

sexp stringreff(sexp s, sexp i)
{
    assertString(s);
    assertFixnum(i);

    char* p = sref(s, asFixnum(i));
    if (!p)
        return 0;

    return character(*p);
}

sexp stringsetf(sexp s, sexp k, sexp c)
{
    assertString(s);
    assertFixnum(k);
    assertChar(c);

    char* p = sref(s, asFixnum(k));
    if (!p)
        return 0;

    *p = ((Char*)c)->text[0];

    return s;
}

sexp substringf(sexp s, sexp i, sexp j)
{
    if (!isString(s) || !isFixnum(i) || !isFixnum(j))
        return 0;

    int ii = asFixnum(i);
    int jj = asFixnum(j);

    if (ii < 0 || jj <= ii)
        return 0;

    char* b = (char*)alloca(jj-ii+1);

    int k = 0;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        if (k <= ii && ii < k+sizeof(t->text))
        {
            for (int m = 0; m < sizeof(t->text); ++m)
            {
                int n = k+m;
                if (n == jj) {
                    b[n-ii] = 0;
                    return lose(1, string(save(chunk(b))));
                } else if (ii <= n && n < jj)
                    b[n-ii] = t->text[m];
            }
        }
        k += sizeof(t->text);
    }

    return 0;
}

sexp reverse(sexp x) { sexp t = 0; while (isCons(x)) { t = cons(car(x), t); x = x->cdr; } return t; }

sexp eqp(sexp x, sexp y) { return x == y ? t : 0; }

// numeric equality =
sexp eqnp(sexp x, sexp y) { return isFixnum(x) && isFixnum(y) && asFixnum(x) == asFixnum(y) ? t :
                                   isFlonum(x) && isFlonum(y) && asFlonum(x) == asFlonum(y) ? t : 0; }

// ~ fixnum
sexp complement(sexp x) { return isFixnum(x) ? fixnum(~asFixnum(x)) : 0; }

sexp allfixnums(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
        if (!isFixnum(p->car))
            return 0;
    return t;
}

// boolean operators

sexp andf(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = ~0;
        for (sexp p = args; p; p = p->cdr)
            result = result & asFixnum(p->car);
        return lose(1, fixnum(result));
    } else
        return lose(1, 0);
}

sexp orf(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = 0;
        for (sexp p = args; p; p = p->cdr)
            result = result | asFixnum(p->car);
        return lose(1, fixnum(result));
    } else
        return lose(1, 0);
}

sexp xorf(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = 0;
        for (sexp p = args; p; p = p->cdr)
            result = result ^ asFixnum(p->car);
        return lose(1, fixnum(result));
    } else
        return lose(1, 0);
}

/*
 * (promise forced value exp env)
 */
sexp delayform(sexp exp, sexp env)
{
    return lose(4, cons(promisea,
                        save(cons(0,
                        save(cons(0,
                        save(cons(exp->cdr->car,
                        save(cons(env, 0))))))))));
}

bool isPromise(sexp p)
{
    return isCons(p) &&
           promisea == p->car &&
           p->cdr &&                   // car has forced flag
           p->cdr->cdr &&              // car has value
           p->cdr->cdr->cdr &&         // car has exp
           p->cdr->cdr->cdr->cdr &&    // car has env
          !p->cdr->cdr->cdr->cdr->cdr; // correct length
}

sexp promisep(sexp p)
{
    return isPromise(p) ? t : 0;
}

sexp force(sexp p)
{
    if (!isPromise(p))
        error("force: not a promise");
    if (!p->cdr->car)
    {
        p->cdr->car = t;
        p->cdr->cdr->car = eval(p->cdr->cdr->cdr->car,
                                p->cdr->cdr->cdr->cdr->car);
    }
    return p->cdr->cdr->car;
}

sexp forcedp(sexp p)
{
    if (!isPromise(p))
        error("promise-forced?: not a promise");
    return p->cdr->car;
}

sexp promisev(sexp p)
{
    if (!isPromise(p))
        error("promise-value: not a promise");
    if (p->cdr->car)
        return p->cdr->cdr->car;
    else
        error("promise not forced yet");
}

void renderedContent(char* buffer, sexp s)
{
    int j = 0;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; buffer[j++] = t->text[i++]) {}
    }
    buffer[j++] = 0;
}

/*
 * open a file and process its contents
 */
sexp load(sexp x)
{
    sexp r = 0;
    if (!isString(x))
        return r;

    char *name = (char*) alloca(slen(x));
    renderedContent(name, x);
    printf("; load: %s\n", name);

    FILE* fin = fopen(name, "r");
    if (fin)
    {
        while (!feof(fin))
        {
            sexp input = read(fin, 0);
            if (!input)
                break;
            //display(stdout, input, true); putchar('\n');
            save(input);
            r = lose(1, eval(input, global));
        }
        fclose(fin);
    }
    return r;
}

sexp newlinef(sexp args)
{
    return endl;
}

sexp eofp(sexp a)
{
    return eofa == a ? t : 0;
}

sexp displayf(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
    {
        display(stdout, p->car, false);
        if (p->cdr)
            putchar(' ');
    }
    return voida;
}

sexp write(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
    {
        display(stdout, p->car, true);
        if (p->cdr)
            putchar(' ');
    }
    return voida;
}

void displayChunks(FILE* fout, sexp p, bool write)
{
    if (write)
        fputc('"', fout);
    while (p)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text); ++i)
        {
            char c = t->text[i];
            if (!c)
                break;
            putc(c, fout);
        }
        p = p->cdr;
    }
    if (write)
        fputc('"', fout);
}

/*
 * a closure is really just a list (closure exp env)
 */
bool isClosure(sexp exp)
{
    return isCons(exp) &&
           closurea == exp->car && exp->cdr && exp->cdr->car &&
           exp->cdr->cdr && exp->cdr->cdr->car && !exp->cdr->cdr->cdr;
}

bool cyclic(std::set<sexp>& seenSet, sexp exp)
{
    if (!exp || !isCons(exp) || isClosure(exp) || isPromise(exp))
        return false;
    if (seenSet.find(exp) == seenSet.end()) {
        seenSet.insert(exp);
        return cyclic(seenSet, exp->car) || cyclic(seenSet, exp->cdr);
    } else
        return true;
}

/*
 * test for cyclic data structures
 */
bool cyclic(sexp exp)
{
    std::set<sexp> seenSet;
    return cyclic(seenSet, exp);
}

/*
 * display an s-expression
 * attempts to deal with cyclic structures are purely defensive
 */
void display(FILE* fout, sexp exp, bool write)
{
    std::set<sexp> seenSet;
    // ideally: #0=(#1=(b) #1# #1# #1# #1# . #0#)
    if (cyclic(exp))
        printf("; cyclic!\n{");
    display(fout, exp, seenSet, write);
}

bool safe(std::set<sexp>& seenSet, sexp exp)
{
    return seenSet.find(exp) == seenSet.end();
}

void insert(std::set<sexp>& seenSet, sexp exp)
{
    seenSet.insert(exp);
}

void displayList(FILE* fout, sexp exp, std::set<sexp>& seenSet, bool write)
{
    if (isClosure(exp))
        fprintf(fout, "#<closure@%p>", (void*)exp);
    else if (isPromise(exp))
        fprintf(fout, "#<promise@%p>", (void*)exp);
    else {
        putc('(', fout);
        while (exp && safe(seenSet, exp)) {
            display(fout, exp->car, seenSet, write);
            insert(seenSet, exp);
            if (exp->cdr) {
                if (isCons(exp->cdr) && !isClosure(exp->cdr) && !isPromise(exp->cdr))
                {
                    if (safe(seenSet, exp->cdr))
                    {
                        putc(' ', fout);
                        exp = exp->cdr;
                    }
                } else {
                    fprintf(fout, " . ");
                    exp = exp->cdr;
                    if (isClosure(exp))
                        fprintf(fout, "#<closure@%p>", (void*)exp);
                    else if (isPromise(exp))
                        fprintf(fout, "#<promise@%p>", (void*)exp);
                    else
                        display(fout, exp, seenSet, write);
                    exp = 0;
                }
            } else
                exp = exp->cdr;
        }
        putc(')', fout);
    }
}

void display(FILE* fout, sexp exp, std::set<sexp>& seenSet, bool write)
{
    if (!exp)
        fprintf(fout, "%s", "#f");
    else if (isCons(exp) && safe(seenSet, exp))
        displayList(fout, exp, seenSet, write);
    else if (isString(exp)) {
        displayChunks(fout, ((String*)exp)->chunks, write);
    } else if (isAtom(exp))
        displayChunks(fout, ((Atom*)exp)->chunks, false);
    else if (isFixnum(exp))
        fprintf(fout, "%ld", ((Fixnum*)exp)->fixnum);
    else if (isFloat(exp))
        fprintf(fout, "%#.8g", asFlonum(exp));
    else if (isDouble(exp))
        fprintf(fout, "%#.15g", asFlonum(exp));
    else if (isFunct(exp))
        fprintf(fout, "#<function%d@%p>", arity(exp), (void*)((Funct*)exp)->funcp);
    else if (isForm(exp))
        fprintf(fout, "#<form@%p>", (void*)((Form*)exp)->formp);
    else if (isChar(exp))
        fprintf(fout, write ? "#\\%c" : "%c", ((Char*)exp)->text[0]);
}

/*
 * every atom must be unique and saved in the atoms list
 */
sexp intern(sexp p)
{
    for (sexp q = atoms; q; q = q->cdr)
    {
        sexp r = q->car;
        if (0 == scmp(((Atom*)p)->chunks, ((Atom*)r)->chunks))
            return r;
    }
    atoms = cons(p, atoms);
    return p;
}

// string->symbol
sexp s2sy(sexp x) { return isString(x) ? intern(atom(((String*)x)->chunks)) : 0; }

// symbol->string
sexp sy2s(sexp x) { return isAtom(x) ? string(((Atom*)x)->chunks) : 0; }

/*
 * vulnerable to cycles, unreasonable to fix
 */
bool eqvb(sexp x, sexp y)
{
    if (x == y)
        return true;
    if (!x || !y)
        return false;
    if (isAtom(x) || isAtom(y))
        return false;
    if (evalType(x) != evalType(y))
        return false;
    if (isCons(x))
        return eqvb(x->car, y->car) && eqvb(x->cdr, y->cdr);
    switch (evalType(x)) 
    {
    case CHUNK : return 0 == scmp(x, y);
    case STRING: return 0 == scmp(((String*)x)->chunks, ((String*)y)->chunks);
    case FIXNUM: return asFixnum(x) == asFixnum(y);
    case FLOAT :
    case DOUBLE: return asFlonum(x) == asFlonum(y);
    default:     return 0;
    }
}

sexp eqv(sexp x, sexp y)
{
    return eqvb(x, y) ? t : 0;
}

sexp equalp(sexp x, sexp y)
{
    return eqvb(x, y) ? t : 0;
}

sexp define(sexp p, sexp r)
{
    sexp s = 0;
    for (sexp q = global; q; q = q->cdr)
        if (p == q->car->car)
        {
            s = q->car->cdr;
            q->car->cdr = r;
            return s;
        }
    global = cons(save(cons(save(p), save(r))), global);
    return lose(3, 0);
}

sexp get(sexp p, sexp env)
{
    // printf("get env: "); display(stdout, env); putchar('\n');
    for (sexp q = env; q; q = q->cdr)
        if (q->car && p == q->car->car)
            return q->car->cdr;

    char msg[] = "error: get unbound";
    int  len = slen(p);
    char *name = (char *) alloca(slen(p)+1);
    renderedContent(name, p);
    char *buff = (char*) alloca(sizeof(msg)+1+len);
    sprintf(buff, "%s %s", msg, name);
    strncpy(errorBuffer, buff, sizeof(errorBuffer));
    error(errorBuffer);
}

sexp set(sexp p, sexp r, sexp env)
{
    sexp s = 0;
    //printf("set env: "); display(stdout, env); putchar('\n');
    for (sexp q = env; q; q = q->cdr)
        if (p == q->car->car)
        {
            s = q->car->cdr;
            q->car->cdr = r;
            return s;
        }

    char msg[] = "error: set! unbound";
    int  len = slen(p);
    char *name = (char*) alloca(slen(p)+1);
    renderedContent(name, p);
    char *buff = (char*) alloca(sizeof(msg)+1+len);
    sprintf(buff, "%s %s", msg, name);
    strncpy(errorBuffer, buff, sizeof(errorBuffer));
    error(errorBuffer);
}

sexp evlis(sexp p, sexp env)
{
    if (!p)
        return 0;
    return lose(4, cons(save(eval(p->car, env)), save(evlis(save(p)->cdr, save(env)))));
}

sexp assoc(sexp formals, sexp actuals, sexp env)
{
    if (!actuals || !formals)
        return env;
    return lose(5, cons(save(cons(formals->car, actuals->car)), save(assoc(save(formals)->cdr, save(actuals)->cdr, save(env)))));
}

sexp nulenvform(sexp exp, sexp env)
{
    return global;
}

sexp intenvform(sexp exp, sexp env)
{
    return env;
}

sexp beginform(sexp exp, sexp env)
{
    save(env);
    sexp v = 0;
    for (sexp p = save(exp)->cdr; p; p = p->cdr)
        v = eval(p->car, env);
    return lose(2, v);
}

sexp whileform(sexp exp, sexp env)
{
    save(env);
    sexp v = 0;
    exp = save(exp)->cdr;
    while (eval(exp->car, env))
        for (sexp p = exp->cdr; p; p = p->cdr)
            v = eval(p->car, env);
    return lose(2, v);
}

/*
 * (cond (test1 val1)
 *       (test2 val2)
 *       ...
 *       (else valn))
 *
 * the first true test returns its corresponding val
 */
sexp condform(sexp exp, sexp env)
{
    save(env);
    sexp r = 0;
    for (sexp p = save(exp)->cdr; p; p = p->cdr)
        if (elsea == p->car->car || eval(p->car->car, env)) {
            r = eval(p->car->cdr->car, env);
            break;
        }
    return lose(2, r);
}

/*
 * (lambda ...) should evaluate to a procedure
 */
sexp lambdaform(sexp exp, sexp env)
{
    return lose(3, cons(closurea, save(cons(save(exp), save(cons(save(env), 0))))));
}

/*
 * rewrite
 *      (define (mycar x) (car x))
 * as
 *      (define mycar (lambda (x) (car x)))
 * or
 *      (define (mycar . x) (car x))
 * as
 *      (define mycar (lambda (mycar . x) (car x)))
 */
sexp defineform(sexp p, sexp env)
{
    if (isCons(p->cdr->car))
    {
        if (isCons(p->cdr->car->cdr))
        {
            save(env);
            sexp k = p->cdr->car->car;
            sexp v = save(cons(lambda, save(cons(p->cdr->car->cdr, save(p)->cdr->cdr))));
            // v is the transformed definition (lambda (x) ...)
            v = lambdaform(v, env);
            // v is a closure (closure exp env)
            for (sexp q = global; q; q = q->cdr)
                if (k == q->car->car)
                {
                    q->car->cdr = v;
                    return lose(4, voida);
                }
            // update the closure definition to include the one we just made
            global = v->cdr->cdr->car = cons(save(cons(p->cdr->car->car, save(v))), global);
            return lose(6, voida);
        } else {
            save(env);
            sexp k = p->cdr->car->car;
            sexp v = save(cons(lambda, save(cons(save(cons(p->cdr->car->car, p->cdr->car->cdr)), save(p)->cdr->cdr))));
            // v is the transformed definition (lambda (mycar . x) ...)
            v = lambdaform(v, env);
            // v is a closure (closure exp env)
            for (sexp q = global; q; q = q->cdr)
                if (k == q->car->car)
                {
                    q->car->cdr = v;
                    return lose(5, voida);
                }
            // update the closure definition to include the one we just made
            global = v->cdr->cdr->car = cons(save(cons(p->cdr->car->car, v)), global);
            return lose(6, voida);
        }
    } else {
        for (sexp q = global; q; q = q->cdr)
            if (p->cdr->car == q->car->car)
            {
                q->car->cdr = eval(save(p)->cdr->cdr->car, save(env));
                return lose(2, voida);
            }
        global = cons(save(cons(p->cdr->car, save(eval(save(p)->cdr->cdr->car, save(env))))), global);
        return lose(4, voida);
    }
}

sexp atomsf(sexp args)
{
    return atoms;
}

sexp quoteform(sexp exp, sexp env)
{
    return exp->cdr->car;
}

sexp readform(sexp exp, sexp env)
{
    return read(stdin, 0);
}

/*
 * (if predicate consequent alternative)
 *
 * if the predicate evaluates non-null
 *    then evaluate the consequent
 *    else evaluate the alternative
 */
sexp ifform(sexp exp, sexp env)
{
    return lose(2, eval(save(exp)->cdr->car, save(env)) ?
                          eval(exp->cdr->cdr->car, env) : eval(exp->cdr->cdr->cdr->car, env));
}

/*
 * (set! name value) alters an existing binding
 */
sexp setform(sexp exp, sexp env)
{
    return lose(3, set(exp->cdr->car, save(eval(save(exp)->cdr->cdr->car, env)), save(env)));
}

/*
 * associate variables with values, used by letform
 */
sexp augment(sexp exp, sexp env)
{
    if (!exp)
        return env;
    return lose(5, cons(save(cons(exp->car->car, save(eval(exp->car->cdr->car, env)))), save(augment(save(exp)->cdr, save(env)))));
}

/*
 * (let ((var value) ..) exp)
 */
sexp letform(sexp exp, sexp env)
{
    sexp r;
    //printf("let org env: "); display(stdout, env); putchar('\n');
    sexp e = save(augment(save(exp)->cdr->car, save(env)));
    //printf("let old env: "); display(stdout, e); putchar('\n');
    for (sexp f = e; f; f = f->cdr)
        if (isCons(f->car->cdr) && closurea == f->car->cdr->car)
            f->car->cdr->cdr->cdr->car = e;
    //printf("let fix env: "); display(stdout, e); putchar('\n');
    for (sexp p = exp->cdr->cdr; p; p = p->cdr)
        r = eval(p->car, e);
    //printf("let new env: "); display(stdout, e); putchar('\n');
    return lose(3, r);
}

sexp apply(sexp fun, sexp args)
{
    save(fun);
    save(args);

    if (isFunct(fun))
    {
        if (0 == arity(fun))
            return lose(2, (*(Varargp)((Funct*)fun)->funcp)(args));
        if (1 == arity(fun) && args)
            return lose(2, (*(Oneargp)((Funct*)fun)->funcp)(args->car));
        if (2 == arity(fun) && args->cdr)
            return lose(2, (*(Twoargp)((Funct*)fun)->funcp)(args->car, args->cdr->car));
    }

    if (isClosure(fun))
    {
        sexp cenv = fun->cdr->cdr->car;

        sexp s = 0;
        if (!fun->cdr->car->cdr->car) {
            // fun->cdr->car = (lambda () foo)
            for (sexp r = fun->cdr->car->cdr->cdr; r; r = r->cdr)
                s = eval(r->car, cenv);
            return lose(2, s);
        } else if (isAtom(fun->cdr->car->cdr->car->cdr)) {
            // fun->cdr->car = (lambda (f . s) foo)
            sexp e = save(cons(save(cons(fun->cdr->car->cdr->car->cdr, args)), cenv));
            for (sexp r = fun->cdr->car->cdr->cdr; r; r = r->cdr)
                s = eval(r->car, e);
            return lose(4, s);
        } else {
            // fun->cdr->car = (lambda (n) (car x))
            sexp e = save(assoc(fun->cdr->car->cdr->car, args, cenv));
            for (sexp r = fun->cdr->car->cdr->cdr; r; r = r->cdr)
                s = eval(r->car, e);
            return lose(3, s);
        }
    }

    error("apply bad function");

    return 0;
}

/*
 * malformed constructs will fail without grace
 */
sexp eval(sexp p, sexp env)
{
    if (!p || f == p || t == p || isOther(p) && ATOM != evalType(p))
        return p;

    if (isAtom(p))
        return get(p, env);

    sexp fun = save(eval(save(p)->car, save(env)));

    if (isForm(fun))
        return lose(3, (*((Form*)fun)->formp)(p, env));

    sexp args = save(evlis(p->cdr, env));

    return lose(4, apply(fun, args));
}

/*
 * read Chunks terminated by some character
 */
sexp readChunks(FILE* fin, const char *ends)
{
    sexp p = cell();
    sexp q = p;
    save(p);
    Chunk* r = (Chunk*) cell();
    r->tags[0] = OTHER;
    r->tags[1] = CHUNK;
    q->car = (sexp) r;

    for (int i = 0; ; )
    {
        char c = getc(fin);

        if (strchr(ends, c))
        {
            while (i < sizeof(r->text))
                r->text[i++] = 0;
            ungetc(c, fin);
            return lose(1, p);
        }

        r->text[i++] = c;

        if (i == sizeof(r->text))
        {
            i = 0;
            q = q->cdr = cell();
            r = (Chunk*) cell();
            r->tags[0] = OTHER;
            r->tags[1] = CHUNK;
            q->car = (sexp) r;
        }
    }
}

char whitespace(FILE* fin, char c)
{
    while (strchr(" \t\r\n", c))
        c = getc(fin);

    while (';' == c)
    {
        while ('\n' != c)
            c = getc(fin);
        while (strchr(" \t\r\n", c))
            c = getc(fin);
    }

    return c;
}

enum { NON_NUMERIC, INT_NUMERIC, FLO_NUMERIC };

/*
 * read an atom, number or string from the input stream
 */
sexp scan(FILE* fin)
{
    char buffer[256];
    char *p = buffer;
    char *pend = buffer + sizeof(buffer) - 1;

    char c = whitespace(fin, getc(fin));

    if (c < 0)
        return 0;

    if ('(' == c)
        return lparen;
    else if ('.' == c)
        return dot;
    else if (')' == c)
        return rparen;
    else if ('\'' == c)
        return qchar;
    else if ('#' == c) {
        c = getc(fin);
        if ('f' == c)
            return 0;
        if ('t' == c)
            return t;
        if ('\\' == c)
            return character(getc(fin));
    } else if ('-' == c) {
        c = getc(fin);
        if ('.' == c || isdigit(c))
            *p++ = '-';
        else
            { ungetc(c, fin); return minus; } 
    }

    int rc = NON_NUMERIC;

    for (;;)
    {
        while (' ' == c || '\t' == c || '\n' == c)
            c = getc(fin);

        while (p < pend && isdigit(c))
        {
            rc = INT_NUMERIC;
            *p++ = c;
            c = getc(fin);
        }

        if (p < pend && '.' == c)
        {
            rc = FLO_NUMERIC;
            *p++ = c;
            c = getc(fin);
        }

        while (p < pend && isdigit(c))
        {
            *p++ = c;
            c = getc(fin);
        }

        if (p < pend && NON_NUMERIC != rc && ('e' == c || 'E' == c))
        {
            rc = NON_NUMERIC;
            *p++ = c;
            c = getc(fin);
            if (p < pend && '-' == c) {
                *p++ = c;
                c = getc(fin);
            } else if (p < pend && '+' == c) {
                *p++ = c;
                c = getc(fin);
            }
            while (p < pend && isdigit(c))
            {
                rc = FLO_NUMERIC;
                *p++ = c;
                c = getc(fin);
            }
        }

        *p++ = 0;
        ungetc(c, fin);
        break;
    }

    if (FLO_NUMERIC == rc)
    {
        char *nptr;
        double floater = strtod(buffer, &nptr);
        if (nptr == strchr(buffer, '\0'))
            return flonum(floater);
    }

    if (INT_NUMERIC == rc)
    {
        char *nptr;
        long fixer = strtol(buffer, &nptr, 10);
        if (nptr == strchr(buffer, '\0'))
            return fixnum(fixer);
    }

    if ('"' == c)
    {
        c = getc(fin);
        sexp r = string(save(readChunks(fin, "\"")));
        (void)getc(fin);  // read the " again
        return lose(1, r);
    }

    return intern(atom(readChunks(fin, "( )\t\r\n")));
}

sexp readTail(FILE* fin, int level)
{
    sexp q = read(fin, level);
    if (rparen == q)
        return 0;
    save(q);
    sexp r = save(readTail(fin, level));
    return lose(2, r && dot == r->car ? cons(q, r->cdr->car) : cons(q, r));
}

/*
 * read an s-expression
 */
sexp read(FILE* fin, int level)
{
    sexp p = scan(fin);
    if (nil == p)
        return 0;
    if (lparen == p)
        return readTail(fin, level+1);
    if (qchar == p)
        return lose(2, cons(quote, save(cons(save(read(fin, level)), 0))));
    if (level == 0 && rparen == p)
        error("error: an s-expression cannot begin with ')'");
    return p;
}

sexp intern_atom_chunk(const char *s)
{
    return intern(atom(chunk(s)));
}

void intr_handler(int sig, siginfo_t *si, void *ctx)
{
    if (killed++)
        exit(0);
    if (SIGINT == sig)
        error("SIGINT");
}

void segv_handler(int sig, siginfo_t *si, void *ctx)
{
    putchar('\n');
#ifdef UNWIND
    unw_cursor_t cursor;
    unw_context_t context;

    unw_getcontext(&context);
    unw_init_local(&cursor, &context);

    int n=0;
    while ( unw_step(&cursor) )
    {
        unw_word_t ip, sp, off;

        unw_get_reg(&cursor, UNW_REG_IP, &ip);
        unw_get_reg(&cursor, UNW_REG_SP, &sp);

        char symbol[256] = {"<unknown>"};
        char *name = symbol;

        if ( !unw_get_proc_name(&cursor, symbol, sizeof(symbol), &off) ) {
          int status;
          if ( (name = abi::__cxa_demangle(symbol, NULL, NULL, &status)) == 0 )
            name = symbol;
        }

        printf("#%2d 0x%p sp=0x%p %s + 0x%lx\n", ++n,
                (void*)(ip), (void*)(sp), name, static_cast<uintptr_t>(off));

        if ( name != symbol )
          free(name);
    }
#endif
    exit(0);
}

int main(int argc, char **argv, char **envp)
{
    // allocate all the cells we will ever have
    block = (sexp)malloc(MAX*sizeof(Cons));
    for (int i = MAX; --i >= 0; )
    {
        block[i].car = 0;
        block[i].cdr = freelist;
        freelist = block+i;
    }

    // set up all predefined atoms

    endl         = intern_atom_chunk("\n");
    acosa        = intern_atom_chunk("acos");
    adda         = intern_atom_chunk("add");
    alphapa      = intern_atom_chunk("char-alphabetic?");
    ampera       = intern_atom_chunk("&");
    anda         = intern_atom_chunk("and");
    applya       = intern_atom_chunk("apply");
    asina        = intern_atom_chunk("asin");
    atana        = intern_atom_chunk("atan");
    atompa       = intern_atom_chunk("atom?");
    atomsa       = intern_atom_chunk("atoms");
    begin        = intern_atom_chunk("begin");
    cara	     = intern_atom_chunk("car");
    cdra	     = intern_atom_chunk("cdr");
    ceilinga     = intern_atom_chunk("ceiling");
    char2ia      = intern_atom_chunk("char->integer");
    charcieqa    = intern_atom_chunk("char-ci=?");
    charcigea    = intern_atom_chunk("char-ci>=?");
    charcigta    = intern_atom_chunk("char-ci>?");
    charcilea    = intern_atom_chunk("char-ci<=?");
    charcilta    = intern_atom_chunk("char-ci<?");
    chareqa      = intern_atom_chunk("char=?");
    chargea      = intern_atom_chunk("char>=?");
    chargta      = intern_atom_chunk("char>?");
    charlea      = intern_atom_chunk("char<=?");
    charlta      = intern_atom_chunk("char<?");
    charpa       = intern_atom_chunk("char?");
    closurea     = intern_atom_chunk("closure");
    cond         = intern_atom_chunk("cond");
    consa        = intern_atom_chunk("cons");
    cosa         = intern_atom_chunk("cos");
    cyclicpa     = intern_atom_chunk("cyclic?");
    definea      = intern_atom_chunk("define");
    delaya       = intern_atom_chunk("delay");
    displaya     = intern_atom_chunk("display");
    diva         = intern_atom_chunk("div");
    dot          = intern_atom_chunk(".");
    downcasea    = intern_atom_chunk("char-downcase");
    e2ia         = intern_atom_chunk("exact->inexact");
    elsea        = intern_atom_chunk("else");
    eofa         = intern_atom_chunk("");
    eofobjp      = intern_atom_chunk("eof-object?");
    eqa          = intern_atom_chunk("eq?");
    eqna         = intern_atom_chunk("=");
    equalpa      = intern_atom_chunk("equal?");
    eqva         = intern_atom_chunk("eqv?");
    evala        = intern_atom_chunk("eval");
    exactpa      = intern_atom_chunk("exact?");
    expa         = intern_atom_chunk("exp");
    f            = intern_atom_chunk("#f");
    floora       = intern_atom_chunk("floor");
    forcea       = intern_atom_chunk("force");
    forcedpa     = intern_atom_chunk("promise-forced?");
    gea          = intern_atom_chunk(">=");
    gta          = intern_atom_chunk(">");
    i2ea         = intern_atom_chunk("inexact->exact");
    ifa          = intern_atom_chunk("if");
    inexactpa    = intern_atom_chunk("inexact?");
    int2chara    = intern_atom_chunk("integer->char");
    integerpa    = intern_atom_chunk("integer?");
    intenva      = intern_atom_chunk("interaction-environment");
    lambda       = intern_atom_chunk("lambda");
    lea          = intern_atom_chunk("<=");
    let          = intern_atom_chunk("let");
    listpa       = intern_atom_chunk("list?");
    loada        = intern_atom_chunk("load");
    loga         = intern_atom_chunk("log");
    lowercasepa  = intern_atom_chunk("char-lower-case?");
    lparen       = intern_atom_chunk("(");
    lsha         = intern_atom_chunk("<<");
    lta          = intern_atom_chunk("<");
    makestringa  = intern_atom_chunk("make-string");
    minus        = intern_atom_chunk("-");
    moda         = intern_atom_chunk("mod");
    mula         = intern_atom_chunk("mul");
    newlinea     = intern_atom_chunk("newline");
    nil          = intern_atom_chunk("#f");
    nota         = intern_atom_chunk("not");
    num2stringa  = intern_atom_chunk("number->string");
    nulenva      = intern_atom_chunk("null-environment");
    nullpa       = intern_atom_chunk("null?");
    numberpa     = intern_atom_chunk("number?");
    numericpa    = intern_atom_chunk("char-numeric?");
    ora          = intern_atom_chunk("or");
    pairpa       = intern_atom_chunk("pair?");
    peekchara    = intern_atom_chunk("peek-char");
    pipea        = intern_atom_chunk("|");
    powa         = intern_atom_chunk("pow");
    procedurepa  = intern_atom_chunk("procedure?");
    promisea     = intern_atom_chunk("promise");
    promisepa    = intern_atom_chunk("promise?");
    promiseva    = intern_atom_chunk("promise-value");
    qchar        = intern_atom_chunk("'");
    quote        = intern_atom_chunk("quote");
    rationala    = intern_atom_chunk("rational");
    reada        = intern_atom_chunk("read");
    readchara    = intern_atom_chunk("read-char");
    readypa      = intern_atom_chunk("char-ready?");
    realpa       = intern_atom_chunk("real?");
    reversea     = intern_atom_chunk("reverse");
    rounda       = intern_atom_chunk("round");
    rparen       = intern_atom_chunk(")");
    rsha         = intern_atom_chunk(">>");
    s2sya        = intern_atom_chunk("string->symbol");
    seta         = intern_atom_chunk("set!");
    setcara      = intern_atom_chunk("set-car!");
    setcdra      = intern_atom_chunk("set-cdr!");
    sina         = intern_atom_chunk("sin");
    sqrta        = intern_atom_chunk("sqrt");
    stringcieq   = intern_atom_chunk("string-ci=?");
    stringcige   = intern_atom_chunk("string-ci>=?");
    stringcigt   = intern_atom_chunk("string-ci>?");
    stringcile   = intern_atom_chunk("string-ci<=?");
    stringcilt   = intern_atom_chunk("string-ci<?");
    stringcopy   = intern_atom_chunk("string-copy");
    stringeq     = intern_atom_chunk("string=?");
    stringfill   = intern_atom_chunk("string-fill!");
    stringge     = intern_atom_chunk("string>=?");
    stringgt     = intern_atom_chunk("string>?");
    stringle     = intern_atom_chunk("string<=?");
    stringlength = intern_atom_chunk("string-length");
    stringlt     = intern_atom_chunk("string<?");
    stringpa     = intern_atom_chunk("string?");
    stringref    = intern_atom_chunk("string-ref");
    stringset    = intern_atom_chunk("string-set!");
    suba         = intern_atom_chunk("sub");
    substringa   = intern_atom_chunk("substring");
    sy2sa        = intern_atom_chunk("symbol->string");
    symbolpa     = intern_atom_chunk("symbol?");
    tana         = intern_atom_chunk("tan");
    tilde        = intern_atom_chunk("~");
    t            = intern_atom_chunk("#t");
    upcasea      = intern_atom_chunk("char-upcase");
    uppercasepa  = intern_atom_chunk("char-upper-case?");
    voida        = intern_atom_chunk("");
    whilea       = intern_atom_chunk("while");
    whitespacepa = intern_atom_chunk("char-whitespace?");
    writea       = intern_atom_chunk("write");
    writechara   = intern_atom_chunk("write-char");
    xora         = intern_atom_chunk("^");


    // set the definitions (special forms)

    define_form(anda,         andform);
    define_form(begin,        beginform);
    define_form(cond,         condform);
    define_form(definea,      defineform);
    define_form(delaya,       delayform);
    define_form(intenva,      intenvform);
    define_form(nulenva,      nulenvform);
    define_form(ifa,          ifform);
    define_form(lambda,       lambdaform);
    define_form(let,          letform);
    define_form(ora,          orform);
    define_form(quote,        quoteform);
    define_form(reada,        readform);
    define_form(seta,         setform);
    define_form(whilea,       whileform);

    // set the definitions (functions)
    define_funct(acosa,         1, (void*)acosff);
    define_funct(adda,          2, (void*)addf);
    define_funct(alphapa,       1, (void*)alphap);
    define_funct(ampera,        0, (void*)andf);
    define_funct(applya,        2, (void*)apply);
    define_funct(asina,         1, (void*)asinff);
    define_funct(atana,         1, (void*)atanff);
    define_funct(atomsa,        0, (void*)atomsf);
    define_funct(cara,          1, (void*)car);
    define_funct(cdra,          1, (void*)cdr);
    define_funct(ceilinga,      1, (void*)ceilingff);
    define_funct(char2ia,       1, (void*)char2int);
    define_funct(charcieqa,     2, (void*)charcieq);
    define_funct(charcigea,     2, (void*)charcige);
    define_funct(charcigta,     2, (void*)charcigt);
    define_funct(charcilea,     2, (void*)charcile);
    define_funct(charcilta,     2, (void*)charcilt);
    define_funct(chareqa,       2, (void*)chareq);
    define_funct(chargea,       2, (void*)charge);
    define_funct(chargta,       2, (void*)chargt);
    define_funct(charlea,       2, (void*)charle);
    define_funct(charlta,       2, (void*)charlt);
    define_funct(charpa ,       1, (void*)charpa );
    define_funct(consa,         2, (void*)cons);
    define_funct(cosa,          1, (void*)cosff);
    define_funct(cyclicpa,      1, (void*)cyclicp);
    define_funct(displaya,      0, (void*)displayf);
    define_funct(diva,          2, (void*)divf);
    define_funct(downcasea,     2, (void*)downcase);
    define_funct(e2ia,          1, (void*)e2if);
    define_funct(eofobjp,       1, (void*)eofp);
    define_funct(eqa,           2, (void*)eqp);
    define_funct(eqna,          1, (void*)eqnp);
    define_funct(eqva,          2, (void*)eqv);
    define_funct(equalpa,       2, (void*)equalp);
    define_funct(evala,         2, (void*)eval);
    define_funct(exactpa,       1, (void*)exactp);
    define_funct(expa,          1, (void*)expff);
    define_funct(floora,        1, (void*)floorff);
    define_funct(forcea,        1, (void*)force);
    define_funct(forcedpa,      1, (void*)forcedp);
    define_funct(gea,           2, (void*)ge);
    define_funct(gta,           2, (void*)gt);
    define_funct(i2ea,          1, (void*)i2ef);
    define_funct(inexactpa,     1, (void*)inexactp);
    define_funct(int2chara,     1, (void*)int2char);
    define_funct(integerpa,     1, (void*)integerp);
    define_funct(lea,           2, (void*)le);
    define_funct(listpa,        1, (void*)listp);
    define_funct(loada,         1, (void*)load);
    define_funct(loga,          1, (void*)logff);
    define_funct(lowercasepa,   1, (void*)lowercasep);
    define_funct(lsha,          2, (void*)lsh);
    define_funct(lta,           2, (void*)lt);
    define_funct(makestringa,   0, (void*)makestring);
    define_funct(moda,          2, (void*)modfn);
    define_funct(mula,          2, (void*)mulf);
    define_funct(newlinea,      0, (void*)newlinef);
    define_funct(nota,          1, (void*)isnot);
    define_funct(nullpa,        1, (void*)nullp);
    define_funct(numberpa,      1, (void*)numberp);
    define_funct(numericpa,     1, (void*)numericp);
    define_funct(num2stringa,   1, (void*)num2string);
    define_funct(pairpa,        1, (void*)pairp);
    define_funct(peekchara,     0, (void*)peekchar);
    define_funct(pipea,         0, (void*)orf);
    define_funct(powa,          2, (void*)powff);
    define_funct(procedurepa,   1, (void*)procedurep);
    define_funct(promisepa,     1, (void*)promisep);
    define_funct(promiseva,     1, (void*)promisev);
    define_funct(readypa,       0, (void*)readyp);
    define_funct(readchara,     0, (void*)readchar);
    define_funct(realpa,        1, (void*)realp);
    define_funct(reversea,      1, (void*)reverse);
    define_funct(rounda,        1, (void*)roundff);
    define_funct(rsha,          2, (void*)rsh);
    define_funct(setcara,       2, (void*)setcarf);
    define_funct(setcdra,       2, (void*)setcdrf);
    define_funct(sina,          1, (void*)sinff);
    define_funct(sqrta,         1, (void*)sqrtff);
    define_funct(stringappenda, 2, (void*)stringappend);
    define_funct(stringcieq,    2, (void*)stringcieqf);
    define_funct(stringcige,    2, (void*)stringcigef);
    define_funct(stringcigt,    2, (void*)stringcigtf);
    define_funct(stringcile,    2, (void*)stringcilef);
    define_funct(stringcilt,    2, (void*)stringciltf);
    define_funct(stringcopy,    2, (void*)stringcopyf);
    define_funct(stringeq,      2, (void*)stringeqf);
    define_funct(stringfill,    2, (void*)stringfillf);
    define_funct(stringge,      2, (void*)stringgef);
    define_funct(stringgt,      2, (void*)stringgtf);
    define_funct(stringle,      2, (void*)stringlef);
    define_funct(stringlength,  1, (void*)stringlengthf);
    define_funct(stringlt,      2, (void*)stringltf);
    define_funct(stringpa,      1, (void*)stringp);
    define_funct(stringref,     2, (void*)stringreff);
    define_funct(stringset,     3, (void*)stringsetf);
    define_funct(suba,          2, (void*)subf);
    define_funct(substringa,    3, (void*)substringf);
    define_funct(sy2sa,         1, (void*)sy2s);
    define_funct(symbolpa,      1, (void*)symbolp);
    define_funct(tana,          1, (void*)tanff);
    define_funct(tilde,         1, (void*)complement);
    define_funct(upcasea,       1, (void*)upcase);
    define_funct(uppercasepa,   1, (void*)uppercasep);
    define_funct(whitespacepa,  1, (void*)whitespacep);
    define_funct(writea,        1, (void*)write);
    define_funct(writechara,    0, (void*)writechar);
    define_funct(xora,          0, (void*)xorf);

    load(string(chunk("init.l")));

    struct sigaction intr_action;
    intr_action.sa_flags = SA_SIGINFO;
    intr_action.sa_sigaction = intr_handler;
    struct sigaction segv_action;
    segv_action.sa_flags = SA_SIGINFO;
    segv_action.sa_sigaction = segv_handler;
    char *s = (char*) sigsetjmp(the_jmpbuf, 1);
    if (s)
        printf("%s\n", s);

    sigaction(SIGSEGV, &segv_action, NULL);
    sigaction(SIGINT,  &intr_action, NULL);

    // read evaluate display ...
    for (;;)
    {
        gc(true);
        total = 0;
        collected = 0;
        psp = protect;
        sexp e = feof(stdin) ? eofa : read(stdin, 0);
        if (eofa == e)
            break;
        killed = 0;
        sexp v = eval(e, global);
        if (voida != v)
        {
            display(stdout, v, false);
            putchar('\n');
        }
    }
    return 0;
}

