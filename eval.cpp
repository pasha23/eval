/*
 * this is kind of a lisp interpreter for my own amusement
 * not at all standards compliant or industrial strength
 * dynamically scoped, without tail call optimization
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
#define error(s) do { printf("%s\n", s); assert(false); } while(0)
#else
#define error(s) do { psp = protect; longjmp(the_jmpbuf, (long)s); } while(0)
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
    ATOM    =  0,
    STRING  =  1,
    CHUNK   =  2,
    FORM    =  3,
    FIXNUM  =  4,
    FUNCT   =  5,
    FLOAT   =  6,
    DOUBLE  =  7,
    CHAR    =  8,
    INPORT  =  9,
    OUTPORT = 10,
    VECTOR  = 11
};

typedef struct Cons *sexp;
typedef sexp (*Formp)(sexp, sexp);
typedef sexp (*Varargp)(sexp);
typedef sexp (*Oneargp)(sexp);
typedef sexp (*Twoargp)(sexp, sexp);
typedef sexp (*Threeargp)(sexp, sexp, sexp);


/*
 * setting up union declarations isn't all that fun but casts are ugly and error-prone.
 */
struct Cons    { sexp                cdr; sexp                     car; };
struct Other   { char                             tags[sizeof(Cons)-0]; };
struct Chunk   { char tags[2];            char    text[sizeof(Cons)-2]; };
struct Atom    { char tags[sizeof(sexp)]; sexp                  chunks; };
struct String  { char tags[sizeof(sexp)]; sexp                  chunks; };
struct Fixnum  { char tags[sizeof(sexp)]; long                  fixnum; };
struct Float   { char tags[sizeof(Cons)-sizeof(float)];  float  flonum; };
struct Double  { char tags[sizeof(Cons)-sizeof(double)]; double flonum; };
struct Funct   { char tags[sizeof(sexp)]; void*                  funcp; };
struct Form    { char tags[sizeof(sexp)]; Formp                  formp; };
struct Char    { char tags[2];            char    text[sizeof(Cons)-2]; };
struct InPort  { char tags[sizeof(sexp)]; FILE*                   file; };
struct OutPort { char tags[sizeof(sexp)]; FILE*                   file; };
struct Vector  { char tags[sizeof(sexp)-sizeof(short)]; short length; sexp* elements; };

sexp scan(FILE* fin);
sexp set(sexp p, sexp r);
bool cyclic(sexp p);
sexp define(sexp p, sexp r);
sexp eval(sexp p, sexp env);
sexp evlis(sexp p, sexp env);
sexp apply(sexp fun, sexp args);
sexp read(FILE* fin, int level);
void display(FILE* fout, sexp p, bool write);
void display(FILE* fout, sexp p, std::set<sexp>& seenSet, bool write);
sexp assoc(sexp formals, sexp actuals, sexp env);
void debug(const char *label, sexp exp);
void envto(const char *label, sexp e0, sexp e1);

// these are the built-in atoms

sexp acosa, adda, alphapa, ampera, anda, anglea, appenda, applya, asina, atana;
sexp ata, atompa, atomsa, begin, callwithina, callwithouta, cara, cdra, ceilinga;
sexp char2ia, char2inta, charcieqa, charcigea, charcigta, charcilea, charcilta;
sexp chareqa, chargea, chargta, charlea, charlta, charpa, clinporta, closurea;
sexp cloutporta, comma, commaat, complexa, cond, consa, cosa, curinporta;
sexp curoutporta, cyclicpa, definea, delaya, displaya, diva, doa, dot, downcasea;
sexp e2ia, elsea, eofa, eofobjp, eqa, eqna, equalpa, eqva, evala, exactpa;
sexp expa, f, floora, forcea, forcedpa, gca, gea, gta, i2ea, ifa, inexactpa;
sexp inportpa, int2chara, integerpa, intenva, lambda, lea, let, letrec, letstar;
sexp list2sa, list2vector, listpa, loada, loga, lowercasepa, lparen, lsha, lta;
sexp makestringa, makevector, minus, moda, modulo, mula, newlinea, nil, nota;
sexp nulenva, nullpa, num2stringa, numberpa, numericpa, openina, openouta, ora;
sexp outportpa, pairpa, peekchara, pipea, plus, powa, procedurepa, promisea;
sexp promisepa, promiseva, qchar, quasiquote, quote, rationala, reada, readchara;
sexp readypa, realpa, reversea, rounda, rparen, rsha, s2lista, s2numa, s2sya;
sexp seta, setcara, setcdra, sina, spacea, sqrta, stringa, stringappenda;
sexp stringcieq, stringcige, stringcigt, stringcile, stringcilt, stringcopy;
sexp stringeq, stringfill, stringge, stringgt, stringle, stringlength, stringlt;
sexp stringpa, stringref, stringset, suba, substringa, sy2sa, symbolpa, t, tana, tick;
sexp tilde, times, truncatea, unquote, unquotesplicing, upcasea, uppercasepa;
sexp vec2lista, vectora, vectorfill, vectorlength, vectorpa, vectorref, vectorset;
sexp voida, whilea, whitespacepa, withina, withouta, writea, writechara, xora;
sexp lbracket, rbracket, polara, magnitudea, rectangulara, gcda, lcma, nega;

static inline int  evalType(const sexp p)  { return                 ((Other*)p)->tags[1]; }
static inline int  arity(const sexp p)     { return                 ((Other*)p)->tags[2]; }
static inline bool isMarked(const sexp p)  { return       (MARK  & ((Other*)p)->tags[0]); }
static inline bool isCons(const sexp p)    { return p && !(OTHER & ((Other*)p)->tags[0]); }
static inline bool isOther(const sexp p)   { return p &&  (OTHER & ((Other*)p)->tags[0]); }
static inline bool isAtom(const sexp p)    { return isOther(p) && ATOM    == evalType(p); }
static inline bool isString(const sexp p)  { return isOther(p) && STRING  == evalType(p); }
static inline bool isFunct(const sexp p)   { return isOther(p) && FUNCT   == evalType(p); }
static inline bool isForm(const sexp p)    { return isOther(p) && FORM    == evalType(p); }
static inline bool isFixnum(const sexp p)  { return isOther(p) && FIXNUM  == evalType(p); }
static inline bool isFloat(const sexp p)   { return isOther(p) && FLOAT   == evalType(p); }
static inline bool isDouble(const sexp p)  { return isOther(p) && DOUBLE  == evalType(p); }
static inline bool isChar(const sexp p)    { return isOther(p) && CHAR    == evalType(p); }
static inline bool isInPort(const sexp p)  { return isOther(p) && INPORT  == evalType(p); }
static inline bool isOutPort(const sexp p) { return isOther(p) && OUTPORT == evalType(p); }
static inline bool isVector(const sexp p)  { return isOther(p) && VECTOR  == evalType(p); }
static inline bool isFlonum(const sexp p)  { return isFloat(p) || isDouble(p);            }

bool isClosure(sexp p)
{
    return isCons(p) &&
           closurea == p->car &&      // (closure
           (p = p->cdr) && p->car &&  //  exp
           (p = p->cdr) && p->car &&  //  env)
           !p->cdr;
}

bool isPromise(sexp p)
{
    return isCons(p) &&
           promisea == p->car &&       // (promise
           (p = p->cdr) &&             // forced
           (p = p->cdr) &&             // value
           (p = p->cdr) &&             // exp
           (p = p->cdr) &&             // env)
          !p->cdr;
}

bool isRational(sexp exp)
{
    return isCons(exp) &&
           rationala == exp->car &&             // (rational
           (exp = exp->cdr) && exp->car &&      //  real
           (exp = exp->cdr) && exp->car &&      //  imag)
           !exp->cdr;
}

bool isRectangular(sexp p)
{
    return isCons(p) &&
           rectangulara == p->car &&   // (rectangular
           (p = p->cdr) && p->car &&   //  real
           (p = p->cdr) && p->car &&   //  imaginary)
           !p->cdr;
}

bool isPolar(sexp p)
{
    return isCons(p) &&
           polara == p->car &&         // (polar
           (p = p->cdr) && p->car &&   //  r
           (p = p->cdr) && p->car &&   //  theta)
           !p->cdr;
}

bool isComplex(sexp p)
{
    return isRectangular(p) || isPolar(p);
}

jmp_buf the_jmpbuf;

bool killed = 0;        // to catch consecutive SIGINTs
sexp atoms = 0;         // all atoms are linked in a list
sexp block = 0;         // all the storage starts here
sexp global = 0;        // this is the global symbol table (a list)
sexp inport = 0;        // the current input port
sexp outport = 0;       // the current output port
sexp freelist = 0;      // available cells are linked in a list
int  marked = 0;        // how many cells were marked during gc
int  allocated = 0;     // how many cells have been allocated
int  total = 0;         // total allocation across gc's
int  collected = 0;     // how many gc's
sexp *protect = 0;      // protection stack
sexp *psp = 0;          // protection stack pointer

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
 * replace the top of the protection stack, return it
 */
sexp replace(sexp p)
{
    return *psp = p;
}

/*
 * pop n items from the protection stack then return p
 */
sexp lose(int n, sexp p)
{
    if (psp-n < protect)
    {
        psp = protect;
        error("error: protection stack underflow");
    }
    psp -= n;
    return p;
}

sexp lose(sexp* mark, sexp p)
{
    psp = mark;
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
    } else if (isVector(p)) {
        Vector* v = (Vector*)p;
        for (int i = v->length; --i >= 0; mark(v->elements[i])) {}
        markCell(p);
    } else
        markCell(p);
}

void deleteinport(sexp v) { fclose(((InPort*)v)->file); }
void deleteoutport(sexp v) { fclose(((OutPort*)v)->file); }
void deletevector(sexp v) { delete ((Vector*)v)->elements; }

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
    mark(inport);
    mark(outport);
    for (sexp *p = protect; p < psp; ++p)
        mark(*p);

    int weremark = marked;
    int reclaimed = 0;

    freelist = 0;
    for (sexp p = block; p < block+MAX; ++p)
    {
        if (!isMarked(p))
        {
            if (isOutPort(p))
                deleteoutport(p);
            else if (isInPort(p))
                deleteinport(p);
            else if (isVector(p))
                deletevector(p);
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

sexp gcf(sexp l)
{
    gc(!!l);
    return 0;
}

void assertAtom(sexp s)        { if (!isAtom(s))        error("not symbol"); }
void assertChar(sexp c)        { if (!isChar(c))        error("not a character"); }
void assertRectangular(sexp s) { if (!isRectangular(s)) error("not rectangular"); }
void assertComplex(sexp s)     { if (!isComplex(s))     error("not complex"); }
void assertPolar(sexp s)       { if (!isPolar(s))       error("not polar"); }
void assertFixnum(sexp i)      { if (!isFixnum(i))      error("not an integer"); }
void assertInPort(sexp s)      { if (!isInPort(s))      error("not an input port"); }
void assertOutPort(sexp s)     { if (!isOutPort(s))     error("not an output port"); }
void assertString(sexp s)      { if (!isString(s))      error("not a string"); }

/*
 * allocate a cell from the freelist
 */
sexp newcell(void)
{
    if (allocated >= MAX)
        gc(false);

    ++allocated;
    Cons* p = freelist;
    freelist = freelist->cdr;
    p->cdr = 0;
    return p;
}

sexp newatom(sexp chunks)
{
    save(chunks);
    Atom* p = (Atom*)newcell();
    p->tags[0] = OTHER;
    p->tags[1] = ATOM;
    p->chunks = chunks;
    return lose(1, (sexp)p);
}

sexp newstring(sexp chunks)
{
    save(chunks);
    String* p = (String*)newcell();
    p->tags[0] = OTHER;
    p->tags[1] = STRING;
    p->chunks = chunks;
    return lose(1, (sexp)p);
}

sexp newfixnum(long number)
{
    Fixnum* p = (Fixnum*)newcell();
    p->tags[0] = OTHER;
    p->tags[1] = FIXNUM;
    p->fixnum = number;
    return (sexp)p;
}

sexp newcharacter(char c)
{
    Char* p = (Char*)newcell();
    p->tags[0] = OTHER;
    p->tags[1] = CHAR;
    p->text[0] = c;
    return (sexp)p;
}

sexp newinport(char* name)
{
    InPort* p = (InPort*)newcell();
    p->tags[0] = OTHER;
    p->tags[1] = INPORT;
    p->file = fopen(name, "r");
    return (sexp)p;
}

sexp newoutport(char* name)
{
    OutPort* p = (OutPort*)newcell();
    p->tags[0] = OTHER;
    p->tags[1] = OUTPORT;
    p->file = fopen(name, "w");
    return (sexp)p;
}

sexp newflonum(double number)
{
    if (sizeof(double) > sizeof(void*)) {
        Float* p = (Float*)newcell();
        p->tags[0] = OTHER;
        p->tags[1] = FLOAT;
        p->flonum = number;
        return (sexp)p;
    } else {
        Double* p = (Double*)newcell();
        p->tags[0] = OTHER;
        p->tags[1] = DOUBLE;
        p->flonum = number;
        return (sexp)p;
    }
}

sexp define_form(sexp name, Formp f)
{
    Form* p = (Form*)save(newcell());
    p->tags[0] = OTHER;
    p->tags[1] = FORM;
    p->formp = f;
    return lose(1, define(name, (sexp)p));
}

sexp define_funct(sexp name, int arity, void* f)
{
    Funct* p = (Funct*)save(newcell());
    p->tags[0] = OTHER;
    p->tags[1] = FUNCT;
    p->tags[2] = arity;
    p->funcp = f;
    return lose(1, define(name, (sexp)p));
}

sexp cons(sexp car, sexp cdr)
{
    save(car);
    save(cdr);
    sexp p = newcell();
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
    p->car = q;
    return voida;
}

sexp setcdrf(sexp p, sexp q)
{
    if (!isCons(p))
        error("error: set-cdr! of non-pair");
    p->cdr = q;
    return voida;
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
            return newfixnum(asFixnum(x) + asFixnum(y));
        else if (isFlonum(y))
            return newflonum(asFixnum(x) + asFlonum(y));
        else
            error("add: bad right argument");
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return newflonum(asFlonum(x) + asFixnum(y));
        else if (isFlonum(y))
            return newflonum(asFlonum(x) + asFlonum(y));
        else
            error("add: bad right argument");
    } else
        error("add: bad left argument");
}

sexp subf(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return newfixnum(asFixnum(x) - asFixnum(y));
        else if (isFlonum(y))
            return newflonum(asFixnum(x) - asFlonum(y));
        else
            error("sub: bad right argument");
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return newflonum(asFlonum(x) - asFixnum(y));
        else if (isFlonum(y))
            return newflonum(asFlonum(x) - asFlonum(y));
        else
            error("sub: bad right argument");
    } else
        error("sub: bad left argument");
}

sexp mulf(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return newfixnum(asFixnum(x) * asFixnum(y));
        else if (isFlonum(y))
            return newflonum(asFixnum(x) * asFlonum(y));
        else
            error("mul: bad right argument");
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return newflonum(asFlonum(x) * asFixnum(y));
        else if (isFlonum(y))
            return newflonum(asFlonum(x) * asFlonum(y));
        else
            error("mul: bad right argument");
    } else
        error("mul: bad left argument");
}

sexp divf(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y) && asFixnum(y))
            return newfixnum(asFixnum(x) / asFixnum(y));
        else if (isFlonum(y) && asFlonum(y))
            return newflonum((double)asFixnum(x) / asFlonum(y));
        else
            error("div: bad right argument");
    } else if (isFlonum(x)) {
        if (isFixnum(y) && asFixnum(y))
            return newflonum(asFlonum(x) / asFixnum(y));
        else if (isFlonum(y) && asFlonum(y))
            return newflonum(asFlonum(x) / asFlonum(y));
        else
            error("div: bad right argument");
    } else
        error("div: bad left argument");
}

sexp modfn(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y) && asFixnum(y))
            return newfixnum(asFixnum(x) % asFixnum(y));
        else if (isFlonum(y) && asFlonum(y))
            return newflonum(fmod((double)asFixnum(x), asFlonum(y)));
        else
            error("mod: bad right argument");
    } else if (isFlonum(x)) {
        if (isFixnum(y) && asFixnum(y))
            return newflonum(fmod(asFlonum(x), (double)asFixnum(y)));
        else if (isFlonum(y) && asFlonum(y))
            return newflonum(fmod(asFlonum(x), asFlonum(y)));
        else
            error("mod: bad right argument");
    } else
        error("mod: bad left argument");
}

sexp negf(sexp x)
{
    if (isFixnum(x))
        return newfixnum(-asFixnum(x));
    if (isFlonum(x))
        return newflonum(-asFlonum(x));
    error("neg: not a number");
}

// (define (magnitude z) (sqrt (add (square (real-part z)) (square (imag-part z)))))

sexp magnitude(sexp z)
{
    save(z);
    assertRectangular(z);
    return lose(1, newflonum(sqrt(asFlonum(z->cdr->car)*
                                  asFlonum(z->cdr->car)+
                                  asFlonum(z->cdr->cdr->car)*
                                  asFlonum(z->cdr->cdr->car))));
}

// (define (angle z) (atan2 (imag-part z) (real-part z)))

sexp angle(sexp z)
{
    assertRectangular(z);
    return newflonum(atan2(asFlonum(z->cdr->cdr->car), asFlonum(z->cdr->car)));
}

// (define (gcd x y) (if (zero? y) x (gcd y (mod x y))))

long gcd(long x, long y)
{
    return y ? gcd(y, x % y) : x;
}

sexp gcdf(sexp x, sexp y)
{
    assertFixnum(x);
    assertFixnum(y);
    return newfixnum(gcd(asFixnum(x), asFixnum(y)));
}

// (define (lcm x y) (let ((g (gcd x y))) (mul (div x g) (div y g))))

long lcm(long x, long y)
{
    long g = gcd(x, y);
    return (x / g) * (y / g);
}

sexp lcmf(sexp x, sexp y)
{
    assertFixnum(x);
    assertFixnum(y);
    return newfixnum(lcm(asFixnum(x), asFixnum(y)));
}

// functions on real numbers
sexp sinff(sexp x) { return isFlonum(x) ? newflonum(sin(asFlonum(x))) : 0; }
sexp cosff(sexp x) { return isFlonum(x) ? newflonum(cos(asFlonum(x))) : 0; }
sexp tanff(sexp x) { return isFlonum(x) ? newflonum(tan(asFlonum(x))) : 0; }
sexp expff(sexp x) { return isFlonum(x) ? newflonum(exp(asFlonum(x))) : 0; }
sexp logff(sexp x) { return isFlonum(x) ? newflonum(log(asFlonum(x))) : 0; }
sexp asinff(sexp x) { return isFlonum(x) ? newflonum(asin(asFlonum(x))) : 0; }
sexp acosff(sexp x) { return isFlonum(x) ? newflonum(acos(asFlonum(x))) : 0; }
sexp atanff(sexp x) { return isFlonum(x) ? newflonum(atan(asFlonum(x))) : 0; }
sexp ceilingff(sexp x) { return isFlonum(x) ? newflonum(ceil(asFlonum(x))) : 0; }
sexp floorff(sexp x) { return isFlonum(x) ? newflonum(floor(asFlonum(x))) : 0; }
sexp roundff(sexp x) { return isFlonum(x) ? newflonum(round(asFlonum(x))) : 0; }
sexp sqrtff(sexp x) { return isFlonum(x) ? newflonum(sqrt(asFlonum(x))) : 0; }
sexp powff(sexp x, sexp y) { return isFlonum(x) && isFlonum(y) ? newflonum(pow(asFlonum(x), asFlonum(y))) : 0; }
sexp truncate(sexp x) { return isFlonum(x) ? newflonum(asFlonum(x) < 0 ? ceil(asFlonum(x)) : floor(asFlonum(x))) : 0; }

// exact, inexact
sexp exactp(sexp x) { return isFixnum(x) ? t : 0; }
sexp integerp(sexp x) { return isFixnum(x) ? t : 0; }
sexp inexactp(sexp x) { return isFlonum(x) ? t : 0; }
sexp realp(sexp x) { return isFlonum(x) ? t : 0; }
sexp i2ef(sexp x) { return isFlonum(x) ? newfixnum((long)asFlonum(x)) : 0; }
sexp e2if(sexp x) { return isFixnum(x) ? newflonum((double)asFixnum(x)) : 0; }

// shifts
sexp lsh(sexp x, sexp y) { return isFixnum(x) && isFixnum(y) ? newfixnum(asFixnum(x) << asFixnum(y)) : 0; }
sexp rsh(sexp x, sexp y) { return isFixnum(x) && isFixnum(y) ? newfixnum(asFixnum(x) >> asFixnum(y)) : 0; }

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

// length of String or Atom

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
    return newfixnum(slen(s));
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
sexp newchunk(const char *t)
{
    if (0 == *t)
        return 0;

    sexp p = save(newcell());
    sexp q = p;
    Chunk* r = (Chunk*) newcell();
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
            q = q->cdr = newcell();
            r = (Chunk*) newcell();
            r->tags[0] = OTHER;
            r->tags[1] = CHUNK;
            q->car = (sexp) r;
        }
    }
}

void renderFloat(char* b, float x)
{
    if ((long)x == x)
        sprintf(b, "%ld.0", (long)x);
    else
        sprintf(b, "%#.8g", x);
}

void renderDouble(char* b, double x)
{
    if ((long)x == x)
        sprintf(b, "%ld.0", (long)x);
    else
        sprintf(b, "%#.15g", x);
}

sexp num2string(sexp exp)
{
    char b[32];
    if (isFixnum(exp))
        sprintf(b, "%ld", ((Fixnum*)exp)->fixnum);
    else if (isFloat(exp)) {
        char b[32];
        renderFloat(b, asFlonum(exp));
        sprintf(b, "%s", b);
    } else if (isDouble(exp)) {
        char b[32];
        renderDouble(b, asFlonum(exp));
        sprintf(b, "%s", b);
    } else if (isRational(exp))
        sprintf(b, "%ld/%ld", asFixnum(exp->cdr->car), asFixnum(exp->cdr->cdr->car));
    else if (isRectangular(exp)) {
        if (asFlonum(exp->cdr->car)) {
            char b0[32], b1[32];
            renderFloat(b0, asFlonum(exp->cdr->car));
            renderFloat(b1, asFlonum(exp->cdr->cdr->car));
            if (asFlonum(exp->cdr->cdr->car) >= 0)
                sprintf(b, "%s+%si", b0, b1);
            else if (asFlonum(exp->cdr->cdr->car) < 0)
                sprintf(b, "%s%si", b0, b1);
            else
                sprintf(b, "%s", b0);
        } else if (asFlonum(exp->cdr->cdr->car)) {
            char b1[32];
            renderFloat(b1, asFlonum(exp->cdr->cdr->car));
            sprintf(b, "%si", b1);
        } else
            sprintf(b, "0.0+0.0i");
    } else if (isPolar(exp)) {
        char b0[32], b1[32];
        renderFloat(b0, asFlonum(exp->cdr->car));
        renderFloat(b1, asFlonum(exp->cdr->cdr->car));
        sprintf(b, "%s@%s", b0, b1);
    }
    return lose(1, newstring(save(newchunk(b))));
}

sexp makestring(sexp args)
{
    if (!args || !isFixnum(args->car))
        error("make-string: args expected");

    int l = asFixnum(args->car);
    char *b = (char*) alloca(l+1);
    char *q = b;
    char c = args->cdr && isChar(args->cdr->car) ? ((Char*)(args->cdr->car))->text[0] : ' ';
    for (int i = 0; i < l; ++i)
        *q++ = c;
    *q++ = 0;
    return lose(1, newstring(save(newchunk(b))));
}

char* sstr(char* b, sexp s)
{
    assertString(s);

    char *q = b;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; *q++ = t->text[i++]) {}
    }
    *q++ = 0;
    return b;
}

sexp stringcopyf(sexp s)
{
    assertString(s);

    return lose(1, newstring(save(newchunk(sstr((char*)alloca(slen(s)+1), s)))));
}

sexp stringappend(sexp p, sexp q)
{
    assertString(p);
    assertString(q);

    int pl = slen(p);
    int ql = slen(q);

    char *b = (char*) alloca(pl+ql+1);

    sstr(b, p);
    sstr(b+pl, q);
    b[pl+ql+1] = '\0';

    return lose(1, newstring(save(newchunk(b))));
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

// close-input-port
sexp clinport(sexp p) { assertOutPort(p); fclose(((OutPort*)p)->file); ((OutPort*)p)->file = 0; }

// close-output-port
sexp cloutport(sexp p) { assertInPort(p); fclose(((InPort*)p)->file); ((InPort*)p)->file = 0; }

// current-input-port
sexp curinport(sexp p) { return inport ? inport : 0; }

// current-output-port
sexp curoutport(sexp p) { return outport ? outport : 0; }

// input-port?
sexp inportp(sexp p) { return isInPort(p) ? t : 0; }

// open-input-file
sexp openin(sexp p) { assertString(p); char* b = (char*) alloca(slen(p)+1); sstr(b, p); return newinport(b); }

// open-output-file
sexp openout(sexp p) { assertString(p); char* b = (char*) alloca(slen(p)+1); sstr(b, p); return newoutport(b); }

// output-port?
sexp outportp(sexp p) { return isOutPort(p) ? t : 0; }

// with-input-from-file
sexp within(sexp p, sexp f) { sexp t = inport; inport = openin(p); sexp q = apply(f, 0); clinport(inport); inport = t; return q; }

// with-output-to-file
sexp without(sexp p, sexp f) { sexp t = outport; outport = openout(p); sexp q = apply(f, 0); cloutport(outport); outport = t; return q; }

// call-with-input-file
sexp callwithin(sexp p, sexp f) { sexp inp = openin(p); sexp q = apply(f, cons(inp, 0)); clinport(inp); return q; }

// call-with-output-file
sexp callwithout(sexp p) { sexp oup = openout(p); sexp q = apply(f, cons(oup, 0)); cloutport(oup); return q; }

sexp vectorp(sexp v)
{
    return isVector(v) ? t : 0;
}

sexp newvector(int len, sexp fill)
{
    Vector* v = (Vector*) save(newcell());
    v->tags[0] = OTHER;
    v->tags[1] = VECTOR;
    v->length = len;
    v->elements = new sexp[len];
    for (int i = v->length; --i >= 0; v->elements[i] = fill) {}
    return lose(1, (sexp)v);
}

sexp makevec(sexp args)
{
    save(args);
    int len = 0;
    if (args->car && isFixnum(args->car))
        len = asFixnum(args->car);
    sexp fill = 0;
    if (args->cdr && args->cdr->car)
        fill = args->cdr->car;
    return lose(1, newvector(len, fill));
}

sexp list2vec(sexp list)
{
    save(list);
    int length = 0;
    for (sexp p = list; p; p = p->cdr)
        ++length;
    Vector* v = (Vector*) save(newvector(length, 0));
    int index = 0;
    for (sexp p = list; p; p = p->cdr)
        v->elements[index++] = p->car;
    return lose(2, (sexp)v);
}

void assertVector(sexp v)
{
    if (!isVector(v))
        error("not a vector");
}

sexp vec2list(sexp vector)
{
    assertVector(vector);
    save(vector);
    Vector* v = (Vector*)vector;
    int index = v->length;
    sexp list = save(0);
    while (index > 0)
        replace(list = cons(v->elements[--index], list));
    return lose(2, list);
}

sexp vecfill(sexp vector, sexp value)
{
    assertVector(vector);
    save(value);
    save(vector);
    Vector* v = (Vector*)vector;
    int index = v->length;
    while (index > 0)
        v->elements[--index] = value;
    return lose(2, vector);
}

sexp veclength(sexp vector)
{
    assertVector(vector);
    save(vector);
    return lose(1, newfixnum(((Vector*)vector)->length));
}

sexp vecref(sexp vector, sexp index)
{
    assertFixnum(index);
    assertVector(vector);
    return ((Vector*)vector)->elements[asFixnum(index)];
}

sexp vector(sexp args)
{
    save(args);
    int index = 0;
    for (sexp p = args; p; p = p->cdr)
        ++index;
    Vector* v = (Vector*) save(newvector(index, 0));
    index = 0;
    for (sexp p = args; p; p = p->cdr)
        v->elements[index++] = p->car;
    return lose(2, (sexp)v);
}

sexp vecset(sexp vector, sexp index, sexp value)
{
    assertFixnum(index);
    assertVector(vector);
    Vector* v = (Vector*)vector;
    v->elements[asFixnum(index)] = value;
    return voida;
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
sexp char2int(sexp c) { assertChar(c); return  newfixnum(((Char*)c)->text[0]); }
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
sexp downcase(sexp c) { assertChar(c); return newcharacter(tolower(((Char*)c)->text[0])); }
sexp int2char(sexp c) { assertFixnum(c); return newcharacter(asFixnum(c)); }
sexp lowercasep(sexp c) { return isChar(c) && islower(((Char*)c)->text[0]) ? t : 0; }
sexp numericp(sexp c) { return isChar(c) && isdigit(((Char*)c)->text[0]) ? t : 0; }
sexp readyp(sexp c) { return 0; }
sexp upcase(sexp c) { assertChar(c); return newcharacter(toupper(((Char*)c)->text[0])); }
sexp uppercasep(sexp c) { return isChar(c) && isupper(((Char*)c)->text[0]) ? t : 0; }
sexp whitespacep(sexp c) { return isChar(c) && isspace(((Char*)c)->text[0]) ? t : 0; }

sexp peekchar(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);
    FILE* f = ((InPort*)port)->file;
    char c = getc(f);
    ungetc(c, f);
    return newcharacter(c);
}

sexp readchar(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);
    FILE* f = ((InPort*)port)->file;
    char c = getc(f);
    return newcharacter(c);
}

sexp writechar(sexp args)
{
    sexp port = outport;
    if (args)
    {
        assertChar(args->car);
        if (args->cdr)
            assertOutPort(port = args->cdr->car);
    }
    fprintf(((OutPort*)port)->file, "#\\%c", ((Char*)(args->car))->text[0]);
    return voida;
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
        error("string-ref: out of bounds");

    return newcharacter(*p);
}

sexp stringsetf(sexp s, sexp k, sexp c)
{
    assertString(s);
    assertFixnum(k);
    assertChar(c);

    char* p = sref(s, asFixnum(k));
    if (!p)
        error("string-set!: out of bounds");

    *p = ((Char*)c)->text[0];

    return s;
}

sexp substringf(sexp s, sexp i, sexp j)
{
    if (!s || !isString(s->car) || !s->cdr || !isFixnum(s->cdr->car))
        error("substring: bad arguments");

    int ii = asFixnum(s->cdr->car);
    int jj = slen(s->car);
    if (s->cdr->cdr && isFixnum(s->cdr->cdr->car))
        jj = asFixnum(s->cdr->cdr->car);

    s = s->car;

    if (ii < 0 || jj <= ii)
        error("substring: bad arguments");

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
                    return lose(1, newstring(save(newchunk(b))));
                } else if (ii <= n && n < jj)
                    b[n-ii] = t->text[m];
            }
        }
        k += sizeof(t->text);
    }

    error("substring: bad arguments");
}

// (define (append p q) (if p (cons (car p) (append (cdr p) q)) q))

sexp append(sexp p, sexp q)
{
    return p ? lose(3, cons(p->car, save(append(save(p)->cdr, save(q))))) : q;
}

sexp reverse(sexp x) { sexp t = 0; while (isCons(x)) { t = cons(car(x), t); x = x->cdr; } return t; }

sexp eqp(sexp x, sexp y) { return x == y ? t : 0; }

// numeric equality =
sexp eqnp(sexp x, sexp y) { return isFixnum(x) && isFixnum(y) && asFixnum(x) == asFixnum(y) ? t :
                                   isFlonum(x) && isFlonum(y) && asFlonum(x) == asFlonum(y) ? t : 0; }

// ~ fixnum
sexp complement(sexp x) { return isFixnum(x) ? newfixnum(~asFixnum(x)) : 0; }

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
        return lose(1, newfixnum(result));
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
        return lose(1, newfixnum(result));
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
        return lose(1, newfixnum(result));
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

/*
 * open a file and process its contents
 */
sexp load(sexp x)
{
    assertString(x);

    char *name = sstr((char*)alloca(slen(x)+1), x);

    printf("; load: %s\n", name);

    FILE* fin = fopen(name, "r");
    if (fin)
    {
        while (!feof(fin))
        {
            sexp input = read(fin, 0);
            if (!input || eofa == input)
                break;
            //debug("input", input);
            eval(input, global);
        }
        fclose(fin);
        return t;
    }
    return 0;
}

sexp spacef(sexp args)
{
    sexp port = args ? args->car : outport;
    assertOutPort(port);
    fputc(' ', (((OutPort*)port)->file));
    return voida;
}

sexp newlinef(sexp args)
{
    sexp port = args ? args->car : outport;
    assertOutPort(port);
    fputc('\n', (((OutPort*)port)->file));
    return voida;
}

sexp eofp(sexp a)
{
    return eofa == a ? t : 0;
}

sexp displayf(sexp args)
{
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    display(((OutPort*)port)->file, args->car, false);
    return voida;
}

sexp write(sexp args)
{
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    display(((OutPort*)port)->file, args->car, true);
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

bool cyclic(std::set<sexp>& seenSet, sexp exp)
{
    if (!exp || !(isCons(exp) || isVector(exp)) || isClosure(exp) || isPromise(exp))
        return false;
    if (isCons(exp) && seenSet.find(exp) == seenSet.end()) {
        seenSet.insert(exp);
        return cyclic(seenSet, exp->car) || cyclic(seenSet, exp->cdr);
    } else if (isVector(exp) && seenSet.find(exp) == seenSet.end()) {
        seenSet.insert(exp);
        Vector* v = (Vector*)exp;
        for (int i = v->length; --i >= 0; )
            if (cyclic(seenSet, v->elements[i]))
                return true;
        return false;
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
                display(fout, exp, seenSet, write);
                exp = 0;
            }
        } else
            exp = exp->cdr;
    }
    putc(')', fout);
}

void displayVector(FILE* fout, sexp v, std::set<sexp>& seenSet, bool write)
{
    putchar('[');
    Vector *vv = (Vector*)v;
    for (int i = 0; i < vv->length; ++i)
    {
        if (i)
            fprintf(fout, ", ");
        if (safe(seenSet, vv->elements[i]))
            display(fout, vv->elements[i], write);
    }
    putchar(']');
}

const char *char_names[] =
{
  "nul","soh","stx","etx","eot","enq","ack","bel","bs", "ht", "nl", "vt", "np", "cr", "so", "si",
  "dle","dc1","dc2","dc3","dc4","nak","syn","etb","can", "em","sub","esc", "fs", "gs", "rs", "us",
  "space", "newline", "tab", "backspace", "return", "page", "escape", "del", 0
};

static unsigned char char_codes[] =
    "\000\001\002\003\004\005\006\007\010\011\012\013\014\015\016\017"
    "\020\021\022\023\024\025\026\027\030\031\032\033\034\035\036\037"
    " \n\t\b\r\f\033\177";

void display(FILE* fout, sexp exp, std::set<sexp>& seenSet, bool write)
{
    if (!exp)
        fprintf(fout, "%s", "#f");
    else if (isClosure(exp))
        fprintf(fout, "#<closure@%p>", (void*)exp);
    else if (isPromise(exp))
        fprintf(fout, "#<promise@%p>", (void*)exp);
    else if (isRational(exp))
        fprintf(fout, "%ld/%ld", asFixnum(exp->cdr->car), asFixnum(exp->cdr->cdr->car));
    else if (isRectangular(exp)) {
        if (asFlonum(exp->cdr->car)) {
            char b0[32], b1[32];
            renderFloat(b0, asFlonum(exp->cdr->car));
            renderFloat(b1, asFlonum(exp->cdr->cdr->car));
            if (asFlonum(exp->cdr->cdr->car) >= 0)
                fprintf(fout, "%s+%si", b0, b1);
            else if (asFlonum(exp->cdr->cdr->car) < 0)
                fprintf(fout, "%s%si", b0, b1);
            else
                fprintf(fout, "%s", b0);
        } else if (asFlonum(exp->cdr->cdr->car)) {
            char b1[32];
            renderFloat(b1, asFlonum(exp->cdr->cdr->car));
            fprintf(fout, "%si", b1);
        } else
            fprintf(fout, "0.0+0.0i");
    } else if (isPolar(exp)) {
        char b0[32], b1[32];
        renderFloat(b0, asFlonum(exp->cdr->car));
        renderFloat(b1, asFlonum(exp->cdr->cdr->car));
        fprintf(fout, "%s@%s", b0, b1);
    } else if (isCons(exp) && safe(seenSet, exp))
        displayList(fout, exp, seenSet, write);
    else if (isString(exp))
        displayChunks(fout, ((String*)exp)->chunks, write);
    else if (isAtom(exp))
        displayChunks(fout, ((Atom*)exp)->chunks, false);
    else if (isFixnum(exp))
        fprintf(fout, "%ld", ((Fixnum*)exp)->fixnum);
    else if (isFloat(exp)) {
        char b[32];
        renderFloat(b, asFlonum(exp));
        fprintf(fout, "%s", b);
    } else if (isDouble(exp)) {
        char b[32];
        renderDouble(b, asFlonum(exp));
        fprintf(fout, "%s", b);
    } else if (isFunct(exp))
        fprintf(fout, "#<function%d@%p>", arity(exp), (void*)((Funct*)exp)->funcp);
    else if (isForm(exp))
        fprintf(fout, "#<form@%p>", (void*)((Form*)exp)->formp);
    else if (isVector(exp) && safe(seenSet, exp))
        displayVector(fout, exp, seenSet, write);
    else if (isInPort(exp))
        fprintf(fout, "#<input@%d>", ((InPort*)exp)->file->_fileno);
    else if (isOutPort(exp))
        fprintf(fout, "#<output@%d>", ((OutPort*)exp)->file->_fileno);
    else if (isChar(exp)) {
        if (write)
        {
            char c = ((Char*)exp)->text[0];
            for (int i = 0; char_names[i]; ++i)
                if (c == char_codes[i])
                    { fprintf(fout, "#\\%s", char_names[i]); return; }
        }
        fprintf(fout, write ? "#\\%c" : "%c", ((Char*)exp)->text[0]);
    }
}

void debug(const char *label, sexp exp)
{
    printf("%s: ", label);
    display(stdout, exp, true);
    putchar('\n');
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
sexp s2sy(sexp x) { assertString(x); return intern(newatom(((String*)x)->chunks)); }

// symbol->string
sexp sy2s(sexp x) { assertAtom(x); return newstring(((Atom*)x)->chunks); }

// string->number
sexp s2num(sexp s)
{
    assertString(s);
    char* b = (char*) alloca(slen(s)+1);
    char *q = b;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; *q++ = t->text[i++]) {}
    }
    *q++ = 0;

    double x, y; long z, w;
    if (2 == sscanf(b, "%lf%lfi", &x, &y))
        return lose(4, cons(rectangulara, save(cons(save(newflonum(x)), save(cons(save(newflonum(y)), 0))))));
    if (2 == sscanf(b, "%lf@%lf", &x, &y))
        return lose(4, cons(polara, save(cons(save(newflonum(x)), save(cons(save(newflonum(y)), 0))))));
    if (2 == sscanf(b, "%ld/%ld", &z, &w))
        return lose(4, cons(rationala, save(cons(save(newfixnum(z)), save(cons(save(newfixnum(w)), 0))))));
    if ((strchr(b, '.') || strchr(b, 'e') || strchr(b, 'E')) && (1 == sscanf(b, "%lf", &x)))
        return newflonum(x);
    if (1 == sscanf(b, "%ld", &z))
        return newfixnum(z);
    error("string->number: not a number");
}

sexp s2list(sexp x)
{
    assertString(x);
    char* b = (char*) alloca(slen(x));
    char *q = b;
    for (sexp p = ((String*)x)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; *q++ = t->text[i++]) {}
    }

    sexp p = 0;
    while (--q >= b)
        p = lose(2, cons(save(newcharacter(*q)), save(p)));

    return p;
}

/*
 * list->string
 */
sexp list2s(sexp s)
{
    if (!s)
        return newstring(0);

    save(s);
    sexp p = save(newcell());
    sexp q = p;
    Chunk* r = (Chunk*) newcell();
    r->tags[0] = OTHER;
    r->tags[1] = CHUNK;
    q->car = (sexp) r;

    int i = 0;
    for ( ; s; s = s->cdr)
    {
        assertChar(s->car);

        r->text[i++] = ((Char*)(s->car))->text[0];

        if (i == sizeof(r->text))
        {
            i = 0;
            q = q->cdr = newcell();
            r = (Chunk*) newcell();
            r->tags[0] = OTHER;
            r->tags[1] = CHUNK;
            q->car = (sexp) r;
        }
    }

    while (i < sizeof(r->text))
        r->text[i++] = 0;

    return lose(2, newstring(p));
}

sexp string(sexp args)
{
    return list2s(args);
}

bool eqvb(sexp x, sexp y);

bool cmpv(sexp p, sexp q)
{
    Vector* pv = (Vector*)p;
    Vector* qv = (Vector*)q;

    if (pv->length != qv->length)
        return false;

    for (int i = pv->length; --i >= 0; )
        if (!eqvb(pv->elements[i], qv->elements[i]))
            return false;

    return true;
}

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
    if (isCons(x) && isCons(y))
        return eqvb(x->car, y->car) && eqvb(x->cdr, y->cdr);
    if (evalType(x) != evalType(y))
        return false;
    switch (evalType(x)) 
    {
    case CHUNK : return 0 == scmp(x, y);
    case STRING: return 0 == scmp(((String*)x)->chunks, ((String*)y)->chunks);
    case FIXNUM: return asFixnum(x) == asFixnum(y);
    case FLOAT :
    case DOUBLE: return asFlonum(x) == asFlonum(y);
    case VECTOR: return cmpv(x, y);
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

void fixenvs(sexp env)
{
    for (sexp f = env; f; f = f->cdr)
        if (isCons(f->car->cdr) && closurea == f->car->cdr->car)
            f->car->cdr->cdr->cdr->car = env;
}

sexp define(sexp p, sexp r)
{
    for (sexp q = global; q; q = q->cdr)
        if (p == q->car->car)
        {
            q->car->cdr = r;
            return voida;
        }
    global = cons(save(cons(save(p), save(r))), global);
    return lose(3, voida);
}

sexp get(sexp p, sexp env)
{
    //debug("get env", env);
    for (sexp q = env; q; q = q->cdr)
        if (q->car && p == q->car->car)
            return q->car->cdr;
#if 1
    debug("unbound", p);
    error("get");
#else
    char msg[] = "error: get unbound";
    int  len = slen(p);
    char *name = (char *) alloca(slen(p)+1);
    sstr(name, p);
    char *buff = (char*) alloca(sizeof(msg)+1+len);
    sprintf(buff, "%s %s", msg, name);
    strncpy(errorBuffer, buff, sizeof(errorBuffer));
    error(errorBuffer);
#endif
}

sexp set(sexp p, sexp r, sexp env)
{
    //debug("set env", env);
    for (sexp q = env; q; q = q->cdr)
        if (p == q->car->car)
        {
            q->car->cdr = r;
            return voida;
        }
#if 1
    debug("unbound", p);
    error("set");
#else
    char msg[] = "error: set! unbound";
    int  len = slen(p);
    char *name = (char*) alloca(slen(p)+1);
    sstr(name, p);
    char *buff = (char*) alloca(sizeof(msg)+1+len);
    sprintf(buff, "%s %s", msg, name);
    strncpy(errorBuffer, buff, sizeof(errorBuffer));
    error(errorBuffer);
#endif
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
    return lose(4, cons(closurea, save(cons(save(exp), save(cons(save(env), 0))))));
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
    sexp* mark = psp;
    if (isCons(p->cdr->car))
    {
        if (isCons(p->cdr->car->cdr))
        {
            save(env);
            sexp k = p->cdr->car->car;
            sexp v = save(cons(lambda, save(cons(p->cdr->car->cdr, save(p)->cdr->cdr))));
            // v is the transformed definition (lambda (x) ...)
            v = save(lambdaform(v, env));
            // v is a closure (closure exp env)
            for (sexp q = global; q; q = q->cdr)
                if (k == q->car->car)
                {
                    q->car->cdr = v;
                    return lose(mark, voida);
                }
            // update the closure definition to include the one we just made
            global = v->cdr->cdr->car = cons(save(cons(p->cdr->car->car, save(v))), global);
            return lose(mark, voida);
        } else {
            save(env);
            sexp k = p->cdr->car->car;
            sexp v = save(cons(lambda, save(cons(save(cons(p->cdr->car->car, p->cdr->car->cdr)), save(p)->cdr->cdr))));
            // v is the transformed definition (lambda (mycar . x) ...)
            v = save(lambdaform(v, env));
            // v is a closure (closure exp env)
            for (sexp q = global; q; q = q->cdr)
                if (k == q->car->car)
                {
                    q->car->cdr = v;
                    return lose(mark, voida);
                }
            // update the closure definition to include the one we just made
            global = v->cdr->cdr->car = cons(save(cons(p->cdr->car->car, v)), global);
            return lose(mark, voida);
        }
    } else {
        for (sexp q = global; q; q = q->cdr)
            if (p->cdr->car == q->car->car)
            {
                q->car->cdr = eval(save(p)->cdr->cdr->car, save(env));
                return lose(mark, voida);
            }
        global = cons(save(cons(p->cdr->car, save(eval(save(p)->cdr->cdr->car, save(env))))), global);
        return lose(mark, voida);
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

sexp unquoteform(sexp exp, sexp env)
{
    sexp* mark = psp;
    if (!exp || !isCons(exp))
        return exp;
    else if (unquote == exp->car && isCons(exp->cdr))
        return lose(mark, eval(save(exp)->cdr->car, save(env)));
    else if (exp->car && unquotesplicing == exp->car->car) {
        save(exp); save(env);
        return lose(mark, save(append(save(eval(exp->car->cdr->car, env)),
                                      save(unquoteform(exp->cdr, env)))));
    } else {
        save(exp); save(env);
        return lose(mark, cons(save(unquoteform(exp->car, env)),
                               save(unquoteform(exp->cdr, env))));
    }
}

sexp quasiquoteform(sexp exp, sexp env)
{
    return unquoteform(exp->cdr->car, env);
}

sexp readf(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);
    FILE* f = ((InPort*)port)->file;
    return read(f, 0);
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

void envto(const char *label, sexp e0, sexp e1)
{
    printf("%s: ", label);
    for (sexp e = e1; e && e != e0; e = e->cdr)
        display(stdout, e->car, true);
    putchar('\n');
}

sexp letform(sexp exp, sexp env)
{
    sexp r;
    sexp e = env;
    sexp* mark = psp;
    save(env); save(exp);
    for (sexp v = exp->cdr->car; v; v = v->cdr)
        e = save(cons(save(cons(v->car->car, save(eval(v->car->cdr->car, env)))), e));
    for (sexp p = exp->cdr->cdr; p; p = p->cdr)
        r = save(eval(p->car, e));
    return lose(mark, r);
}

sexp letstarform(sexp exp, sexp env)
{
    sexp r;
    sexp e = env;
    sexp* mark = psp;
    save(env); save(exp);
    for (sexp v = exp->cdr->car; v; v = v->cdr)
        e = save(cons(save(cons(v->car->car, save(eval(v->car->cdr->car, e)))), e));
    for (sexp p = exp->cdr->cdr; p; p = p->cdr)
        r = save(eval(p->car, e));
    return lose(mark, r);
}

sexp letrecform(sexp exp, sexp env)
{
    sexp r;
    sexp e = env;
    sexp* mark = psp;
    save(env); save(exp);
    for (sexp v = exp->cdr->car; v; v = v->cdr)
        e = save(cons(save(cons(v->car->car, v->car->cdr->car)), e));
    for (sexp v = exp->cdr->car; v; v = v->cdr)
        set(v->car->car, eval(v->car->cdr->car, e), e);
    for (sexp p = exp->cdr->cdr; p; p = p->cdr)
        r = save(eval(p->car, e));
    return lose(mark, r);
}

/*
 * (do ((var value step)
 *      (var value step) ...)
 *      ((test) ..)
 *      body)
 */
sexp doform(sexp exp, sexp env)
{
    // loop {
    //    set value step
    //    body
    // }
    sexp e = env;
    sexp* mark = psp;
    // bind all the variables to their values
    for (sexp v = exp->cdr->car; v; v = v->cdr)
        e = save(cons(save(cons(v->car->car, v->car->cdr->car)), e));
    sexp s = save(0);
    for (;;)
    {
        // if any test succeeds, return s
        for (sexp t = exp->cdr->cdr->car; t; t = t->cdr)
            if (eval(t->car, e))
                return lose(mark, s);

        // execute each body expression
        for (sexp r = exp->cdr->cdr->cdr; r; r = r->cdr)
            s = replace(eval(r->car, e));

        // step each variable
        for (sexp v = exp->cdr->car; v; v = v->cdr)
            set(v->car->car, eval(v->car->cdr->cdr->car, e), e);
    }
}

sexp apply(sexp fun, sexp args)
{
    sexp* mark = psp;

    save(fun);
    save(args);

    if (isFunct(fun))
    {
        if (0 == arity(fun))
            return lose(mark, (*(Varargp)((Funct*)fun)->funcp)(args));
        if (1 == arity(fun) && args)
            return lose(mark, (*(Oneargp)((Funct*)fun)->funcp)(args->car));
        if (2 == arity(fun) && args->cdr)
            return lose(mark, (*(Twoargp)((Funct*)fun)->funcp)(args->car, args->cdr->car));
        if (3 == arity(fun) && args->cdr && args->cdr->cdr)
            return lose(mark, (*(Threeargp)((Funct*)fun)->funcp)(args->car, args->cdr->car, args->cdr->cdr->car));
    }

    if (isClosure(fun))
    {
        sexp cenv = fun->cdr->cdr->car;

        sexp s = 0;
        if (!fun->cdr->car->cdr->car) {
            // fun->cdr->car = (lambda () foo)
            for (sexp r = fun->cdr->car->cdr->cdr; r; r = r->cdr)
                s = eval(r->car, cenv);
            return lose(mark, s);
        } else if (isAtom(fun->cdr->car->cdr->car->cdr)) {
            // fun->cdr->car = (lambda (f . s) foo)
            sexp e = save(cons(save(cons(fun->cdr->car->cdr->car->cdr, args)), cenv));
            for (sexp r = fun->cdr->car->cdr->cdr; r; r = r->cdr)
                s = eval(r->car, e);
            return lose(mark, s);
        } else {
            // fun->cdr->car = (lambda (n) (car x))
            sexp e = save(assoc(fun->cdr->car->cdr->car, args, cenv));
            for (sexp r = fun->cdr->car->cdr->cdr; r; r = r->cdr)
                s = eval(r->car, e);
            return lose(mark, s);
        }
    }

    debug("not fun", fun);

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

    if (isRational(p) || isRectangular(p) || isPolar(p))
        return p;

    sexp* mark = psp;

    sexp fun = save(eval(save(p)->car, save(env)));

    if (isForm(fun))
        return lose(mark, (*((Form*)fun)->formp)(p, env));

    sexp args = save(evlis(p->cdr, env));

    return lose(mark, apply(fun, args));
}

/*
 * read Chunks terminated by some character
 */
sexp readChunks(FILE* fin, const char *ends)
{
    sexp p = save(newcell());
    sexp q = p;
    Chunk* r = (Chunk*) newcell();
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
            q = q->cdr = newcell();
            r = (Chunk*) newcell();
            r->tags[0] = OTHER;
            r->tags[1] = CHUNK;
            q->car = (sexp) r;
        }
    }
}

char whitespace(FILE* fin, char c)
{
    if (c > 0)
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
    }

    return c;
}

enum { NON_NUMERIC, INT_NUMERIC, INT_RATIONAL, FLO_NUMERIC, FLO_IMAGINARY };

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
        return eofa;

    if ('(' == c)
        return lparen;
    else if ('.' == c)
        return dot;
    else if (')' == c)
        return rparen;
    else if ('\'' == c)
        return qchar;
    else if ('`' == c)
        return tick;
    else if ('[' == c)
        return lbracket;
    else if (']' == c)
        return rbracket;
    else if (',' == c) {
        c = getc(fin);
        if ('@' != c) {
            ungetc(c, fin);
            return comma;
        } else
            return commaat;
    } else if ('#' == c) {
        c = getc(fin);
        if ('f' == c)
            return 0;
        if ('t' == c)
            return t;
        if ('\\' == c)
        {
            c = getc(fin);
            while (!isspace(c) && ')' != c && ']' != c && ',' != c)
                { *p++ = c; c = getc(fin); }
            ungetc(c, fin);
            *p = 0;
            for (int i = 0; char_names[i]; ++i)
                if (!strcmp(buffer, char_names[i]))
                    return newcharacter(char_codes[i]);
            return newcharacter(*buffer);
        }
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
        while (isspace(c))
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

        if (INT_NUMERIC == rc && '/' == c)
            rc = INT_RATIONAL;

        if (FLO_NUMERIC == rc && 'i' == c)
            rc = FLO_IMAGINARY;

        ungetc(c, fin);
        *p++ = 0;
        break;
    }

    if (FLO_IMAGINARY == rc)
    {
        char *nptr;
        c = getc(fin);
        double floater = strtod(buffer, &nptr);
        if (nptr == strchr(buffer, '\0'))
            return lose(4, cons(rectangulara, save(cons(save(newflonum(0.0)), save(cons(save(newflonum(floater)), 0))))));
    }

    if (FLO_NUMERIC == rc)
    {
        char *nptr;
        double floater = strtod(buffer, &nptr);
        if (nptr == strchr(buffer, '\0'))
            if ('-' == c || '+' == c) {
                if ('+' == c)
                    c = getc(fin);
                sexp im = save(scan(fin));
                im->cdr->car = newflonum(floater);
                return lose(1, im);
            } else
                return newflonum(floater);
    }

    if (INT_RATIONAL == rc)
    {
        char *nptr;
        long fixer = strtol(buffer, &nptr, 10);
        if (nptr == strchr(buffer, '\0'))
            if ('/' == c) {
                c = getc(fin);
                sexp den = save(scan(fin));
                sexp num = save(newfixnum(fixer));
                return lose(4, cons(rationala, save(cons(num, save(cons(den, 0))))));
            } else
                return newfixnum(fixer);
    }

    if (INT_NUMERIC == rc)
    {
        char *nptr;
        long fixer = strtol(buffer, &nptr, 10);
        if (nptr == strchr(buffer, '\0'))
            return newfixnum(fixer);
    }

    if ('"' == c)
    {
        c = getc(fin);
        sexp r = newstring(save(readChunks(fin, "\"")));
        (void)getc(fin);  // read the " again
        return lose(1, r);
    }

    return lose(2, intern(save(newatom(save(readChunks(fin, "( )[,]\t\r\n"))))));
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

sexp readVector(FILE* fin, int level)
{
    sexp q = 0;
    sexp* mark = psp;
    for (;;)
    {
        sexp s = save(read(fin, level));
        if (rbracket == s)
            return lose(mark, list2vec(save(reverse(q))));
        while (unquote == s->car)
            s = s->cdr->car;
        q = replace(cons(s, q));
        s = scan(fin);
        if (rbracket == s)
            return lose(mark, list2vec(save(reverse(q))));
        if (comma != s)
            error("comma expected in vector");
    }
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
    if (lbracket == p)
        return readVector(fin, level+1);
    if (qchar == p)
        return lose(2, cons(quote, save(cons(save(read(fin, level)), 0))));
    if (tick == p)
        return lose(2, cons(quasiquote, save(cons(save(read(fin, level)), 0))));
    if (comma == p)
        return lose(2, cons(unquote, save(cons(save(read(fin, level)), 0))));
    if (commaat == p)
        return lose(2, cons(unquotesplicing, save(cons(save(read(fin, level)), 0))));
    if (level == 0 && (rbracket == p || rparen == p))
        error("error: an s-expression cannot begin with ')' or ']'");
    return p;
}

sexp atomize(const char *s)
{
    return lose(2, intern(save(newatom(save(newchunk(s))))));
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

    // allocate the protection stack
    psp = protect = (sexp*)malloc(PSIZE*sizeof(sexp));

    InPort* p = (InPort*)newcell();
    p->tags[0] = OTHER;
    p->tags[1] = INPORT;
    p->file = stdin;
    inport = (sexp)p;

    OutPort* q = (OutPort*)newcell();
    q->tags[0] = OTHER;
    q->tags[1] = OUTPORT;
    q->file = stdout;
    outport = (sexp)q;

    // set up all predefined atoms

    acosa           = atomize("acos");
    adda            = atomize("add");
    alphapa         = atomize("char-alphabetic?");
    ampera          = atomize("&");
    anda            = atomize("and");
    anglea          = atomize("angle");
    appenda         = atomize("append");
    applya          = atomize("apply");
    asina           = atomize("asin");
    ata             = atomize("@");
    atana           = atomize("atan");
    atompa          = atomize("atom?");
    atomsa          = atomize("atoms");
    begin           = atomize("begin");
    callwithina     = atomize("call-with-input-file");
    callwithouta    = atomize("call-with-output-file");
    cara            = atomize("car");
    cdra            = atomize("cdr");
    ceilinga        = atomize("ceiling");
    char2ia         = atomize("char->integer");
    charcieqa       = atomize("char-ci=?");
    charcigea       = atomize("char-ci>=?");
    charcigta       = atomize("char-ci>?");
    charcilea       = atomize("char-ci<=?");
    charcilta       = atomize("char-ci<?");
    chareqa         = atomize("char=?");
    chargea         = atomize("char>=?");
    chargta         = atomize("char>?");
    charlea         = atomize("char<=?");
    charlta         = atomize("char<?");
    charpa          = atomize("char?");
    clinporta       = atomize("close-input-port");
    closurea        = atomize("closure");
    cloutporta      = atomize("close-output-port");
    comma           = atomize(",");
    commaat         = atomize(",@");
    complexa        = atomize("complex");
    cond            = atomize("cond");
    consa           = atomize("cons");
    cosa            = atomize("cos");
    curinporta      = atomize("current-input-port");
    curoutporta     = atomize("current-output-port");
    cyclicpa        = atomize("cyclic?");
    definea         = atomize("define");
    delaya          = atomize("delay");
    displaya        = atomize("display");
    diva            = atomize("div");
    doa             = atomize("do");
    dot             = atomize(".");
    downcasea       = atomize("char-downcase");
    e2ia            = atomize("exact->inexact");
    elsea           = atomize("else");
    eofa            = atomize("");
    eofobjp         = atomize("eof-object?");
    eqa             = atomize("eq?");
    eqna            = atomize("=");
    equalpa         = atomize("equal?");
    eqva            = atomize("eqv?");
    evala           = atomize("eval");
    exactpa         = atomize("exact?");
    expa            = atomize("exp");
    f               = atomize("#f");
    floora          = atomize("floor");
    forcea          = atomize("force");
    forcedpa        = atomize("promise-forced?");
    gca             = atomize("gc");
    gcda            = atomize("gcd");
    gea             = atomize(">=");
    gta             = atomize(">");
    i2ea            = atomize("inexact->exact");
    ifa             = atomize("if");
    inexactpa       = atomize("inexact?");
    inportpa        = atomize("input-port?");
    int2chara       = atomize("integer->char");
    integerpa       = atomize("integer?");
    intenva         = atomize("interaction-environment");
    lambda          = atomize("lambda");
    lbracket        = atomize("[");
    lcma            = atomize("lcm");
    lea             = atomize("<=");
    let             = atomize("let");
    letrec          = atomize("letrec");
    letstar         = atomize("let*");
    list2sa         = atomize("list->string");
    list2vector     = atomize("list->vector");
    listpa          = atomize("list?");
    loada           = atomize("load");
    loga            = atomize("log");
    lowercasepa     = atomize("char-lower-case?");
    lparen          = atomize("(");
    lsha            = atomize("<<");
    lta             = atomize("<");
    magnitudea      = atomize("magnitude");
    makestringa     = atomize("make-string");
    makevector      = atomize("make-vector");
    minus           = atomize("-");
    moda            = atomize("mod");
    mula            = atomize("mul");
    nega            = atomize("neg");
    newlinea        = atomize("newline");
    nil             = atomize("#f");
    nota            = atomize("not");
    nulenva         = atomize("null-environment");
    nullpa          = atomize("null?");
    num2stringa     = atomize("number->string");
    numberpa        = atomize("number?");
    numericpa       = atomize("char-numeric?");
    openina         = atomize("open-input-file");
    openouta        = atomize("open-output-file");
    ora             = atomize("or");
    outportpa       = atomize("output-port?");
    pairpa          = atomize("pair?");
    peekchara       = atomize("peek-char");
    pipea           = atomize("|");
    polara          = atomize("polar");
    powa            = atomize("pow");
    procedurepa     = atomize("procedure?");
    promisea        = atomize("promise");
    promisepa       = atomize("promise?");
    promiseva       = atomize("promise-value");
    qchar           = atomize("'");
    quasiquote      = atomize("quasiquote");
    quote           = atomize("quote");
    rationala       = atomize("rational");
    rbracket        = atomize("]");
    reada           = atomize("read");
    readchara       = atomize("read-char");
    readypa         = atomize("char-ready?");
    realpa          = atomize("real?");
    rectangulara    = atomize("rectangular");
    reversea        = atomize("reverse");
    rounda          = atomize("round");
    rparen          = atomize(")");
    rsha            = atomize(">>");
    stringa         = atomize("string");
    s2lista         = atomize("string->list");
    s2numa          = atomize("string->number");
    s2sya           = atomize("string->symbol");
    seta            = atomize("set!");
    setcara         = atomize("set-car!");
    setcdra         = atomize("set-cdr!");
    sina            = atomize("sin");
    spacea          = atomize("space");
    sqrta           = atomize("sqrt");
    stringcieq      = atomize("string-ci=?");
    stringcige      = atomize("string-ci>=?");
    stringcigt      = atomize("string-ci>?");
    stringcile      = atomize("string-ci<=?");
    stringcilt      = atomize("string-ci<?");
    stringcopy      = atomize("string-copy");
    stringeq        = atomize("string=?");
    stringfill      = atomize("string-fill!");
    stringge        = atomize("string>=?");
    stringgt        = atomize("string>?");
    stringle        = atomize("string<=?");
    stringlength    = atomize("string-length");
    stringlt        = atomize("string<?");
    stringpa        = atomize("string?");
    stringref       = atomize("string-ref");
    stringset       = atomize("string-set!");
    suba            = atomize("sub");
    substringa      = atomize("substring");
    sy2sa           = atomize("symbol->string");
    symbolpa        = atomize("symbol?");
    tana            = atomize("tan");
    t               = atomize("#t");
    tick            = atomize("`");
    tilde           = atomize("~");
    truncatea       = atomize("truncate");
    unquote         = atomize("unquote");
    unquotesplicing = atomize("unquote-splicing");
    upcasea         = atomize("char-upcase");
    uppercasepa     = atomize("char-upper-case?");
    vec2lista       = atomize("vector->list");
    vectora         = atomize("vector");
    vectorfill      = atomize("vector-fill!");
    vectorlength    = atomize("vector-length");
    vectorpa        = atomize("vector?");
    vectorref       = atomize("vector-ref");
    vectorset       = atomize("vector-set!");
    voida           = atomize("");
    whilea          = atomize("while");
    whitespacepa    = atomize("char-whitespace?");
    withina         = atomize("with-input-from-file");
    withouta        = atomize("with-output-to-file");
    writea          = atomize("write");
    writechara      = atomize("write-char");
    xora            = atomize("^");

    // set the definitions (special forms)

    define_form(anda,         andform);
    define_form(begin,        beginform);
    define_form(cond,         condform);
    define_form(definea,      defineform);
    define_form(delaya,       delayform);
    define_form(doa,          doform);
    define_form(intenva,      intenvform);
    define_form(nulenva,      nulenvform);
    define_form(ifa,          ifform);
    define_form(lambda,       lambdaform);
    define_form(let,          letform);
    define_form(letstar,      letstarform);
    define_form(letrec,       letrecform);
    define_form(ora,          orform);
    define_form(quasiquote,   quasiquoteform);
    define_form(quote,        quoteform);
    define_form(seta,         setform);
    define_form(whilea,       whileform);

    // set the definitions (functions)
    define_funct(acosa,         1, (void*)acosff);
    define_funct(adda,          2, (void*)addf);
    define_funct(alphapa,       1, (void*)alphap);
    define_funct(ampera,        0, (void*)andf);
    define_funct(anglea,        1, (void*)angle);
    define_funct(appenda,       2, (void*)append);
    define_funct(applya,        2, (void*)apply);
    define_funct(asina,         1, (void*)asinff);
    define_funct(atana,         1, (void*)atanff);
    define_funct(atomsa,        0, (void*)atomsf);
    define_funct(callwithina,   1, (void*)callwithin);
    define_funct(callwithouta,  1, (void*)callwithout);
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
    define_funct(charpa,        1, (void*)charp);
    define_funct(clinporta,     1, (void*)clinport);
    define_funct(cloutporta,    1, (void*)cloutport);
    define_funct(consa,         2, (void*)cons);
    define_funct(cosa,          1, (void*)cosff);
    define_funct(curinporta,    0, (void*)curinport);
    define_funct(curoutporta,   0, (void*)curoutport);
    define_funct(cyclicpa,      1, (void*)cyclicp);
    define_funct(displaya,      0, (void*)displayf);
    define_funct(diva,          2, (void*)divf);
    define_funct(downcasea,     1, (void*)downcase);
    define_funct(e2ia,          1, (void*)e2if);
    define_funct(eofobjp,       1, (void*)eofp);
    define_funct(eqa,           2, (void*)eqp);
    define_funct(eqna,          2, (void*)eqnp);
    define_funct(equalpa,       2, (void*)equalp);
    define_funct(eqva,          2, (void*)eqv);
    define_funct(evala,         2, (void*)eval);
    define_funct(exactpa,       1, (void*)exactp);
    define_funct(expa,          1, (void*)expff);
    define_funct(floora,        1, (void*)floorff);
    define_funct(forcea,        1, (void*)force);
    define_funct(forcedpa,      1, (void*)forcedp);
    define_funct(gca,           0, (void*)gcf);
    define_funct(gcda,          2, (void*)gcdf);
    define_funct(gea,           2, (void*)ge);
    define_funct(gta,           2, (void*)gt);
    define_funct(i2ea,          1, (void*)i2ef);
    define_funct(inexactpa,     1, (void*)inexactp);
    define_funct(inportpa,      1, (void*)inportp);
    define_funct(int2chara,     1, (void*)int2char);
    define_funct(integerpa,     1, (void*)integerp);
    define_funct(lcma,          2, (void*)lcmf);
    define_funct(lea,           2, (void*)le);
    define_funct(list2sa,       1, (void*)list2s);
    define_funct(list2vector,   1, (void*)list2vec);
    define_funct(listpa,        1, (void*)listp);
    define_funct(loada,         1, (void*)load);
    define_funct(loga,          1, (void*)logff);
    define_funct(lowercasepa,   1, (void*)lowercasep);
    define_funct(lsha,          2, (void*)lsh);
    define_funct(lta,           2, (void*)lt);
    define_funct(magnitudea,    1, (void*)magnitude);
    define_funct(makestringa,   0, (void*)makestring);
    define_funct(makevector,    0, (void*)makevec);
    define_funct(moda,          2, (void*)modfn);
    define_funct(mula,          2, (void*)mulf);
    define_funct(nega,          1, (void*)negf);
    define_funct(newlinea,      0, (void*)newlinef);
    define_funct(nota,          1, (void*)isnot);
    define_funct(nullpa,        1, (void*)nullp);
    define_funct(num2stringa,   1, (void*)num2string);
    define_funct(numberpa,      1, (void*)numberp);
    define_funct(numericpa,     1, (void*)numericp);
    define_funct(openina,       1, (void*)openin);
    define_funct(openouta,      1, (void*)openout);
    define_funct(outportpa,     1, (void*)outportp);
    define_funct(pairpa,        1, (void*)pairp);
    define_funct(peekchara,     0, (void*)peekchar);
    define_funct(pipea,         0, (void*)orf);
    define_funct(powa,          2, (void*)powff);
    define_funct(procedurepa,   1, (void*)procedurep);
    define_funct(promisepa,     1, (void*)promisep);
    define_funct(promiseva,     1, (void*)promisev);
    define_funct(reada,         0, (void*)readf);
    define_funct(readchara,     0, (void*)readchar);
    define_funct(readypa,       0, (void*)readyp);
    define_funct(realpa,        1, (void*)realp);
    define_funct(reversea,      1, (void*)reverse);
    define_funct(rounda,        1, (void*)roundff);
    define_funct(rsha,          2, (void*)rsh);
    define_funct(s2lista,       1, (void*)s2list);
    define_funct(s2numa,        1, (void*)s2num);
    define_funct(setcara,       2, (void*)setcarf);
    define_funct(setcdra,       2, (void*)setcdrf);
    define_funct(sina,          1, (void*)sinff);
    define_funct(spacea,        0, (void*)spacef);
    define_funct(sqrta,         1, (void*)sqrtff);
    define_funct(stringa,       0, (void*)string);
    define_funct(stringappenda, 2, (void*)stringappend);
    define_funct(stringcieq,    2, (void*)stringcieqf);
    define_funct(stringcige,    2, (void*)stringcigef);
    define_funct(stringcigt,    2, (void*)stringcigtf);
    define_funct(stringcile,    2, (void*)stringcilef);
    define_funct(stringcilt,    2, (void*)stringciltf);
    define_funct(stringcopy,    1, (void*)stringcopyf);
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
    define_funct(substringa,    0, (void*)substringf);
    define_funct(sy2sa,         1, (void*)sy2s);
    define_funct(symbolpa,      1, (void*)symbolp);
    define_funct(tana,          1, (void*)tanff);
    define_funct(tilde,         1, (void*)complement);
    define_funct(truncatea,     1, (void*)truncate);
    define_funct(upcasea,       1, (void*)upcase);
    define_funct(uppercasepa,   1, (void*)uppercasep);
    define_funct(vec2lista,     1, (void*)vec2list);
    define_funct(vectora,       0, (void*)vector);
    define_funct(vectorfill,    2, (void*)vecfill);
    define_funct(vectorlength,  1, (void*)veclength);
    define_funct(vectorpa,      1, (void*)vectorp);
    define_funct(vectorref,     2, (void*)vecref);
    define_funct(vectorset,     3, (void*)vecset);
    define_funct(whitespacepa,  1, (void*)whitespacep);
    define_funct(withina,       1, (void*)within);
    define_funct(withouta,      1, (void*)without);
    define_funct(writea,        0, (void*)write);
    define_funct(writechara,    0, (void*)writechar);
    define_funct(xora,          0, (void*)xorf);

    load(newstring(newchunk("init.l")));

    if (argc > 1)
    {
        load(newstring(newchunk(argv[1])));
        return 0;
    }

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
        if (psp > protect)
            if ((long)(psp-protect) > 1)
                printf("%ld items remain on protection stack\n", (long)(psp-protect));
            else
                printf("one item remains on protection stack\n");
        gc(true);
        total = 0;
        collected = 0;
        sexp e = read(stdin, 0);
        if (!e || eofa == e)
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

