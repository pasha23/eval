/*
 * this is kind of a lisp interpreter for my own amusement
 * not at all standards compliant or industrial strength
 * needs tail call optimization
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
#include <assert.h>
#include <cmath>
#include <csetjmp>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctype.h>
#include <errno.h>
#include <iomanip>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <termios.h>
#include <unistd.h>

bool killed = true;

#ifdef BROKEN
#define error(s) do { printf("%s\n", s); assert(false); } while(0)
#else
#define error(s) do { if (killed) { printf("%s\n", s); assert(false); }\
                      psp = protect; longjmp(the_jmpbuf, (long)s); } while(0)
#endif

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
struct Cons    { sexp                cdr; sexp                       car; };
struct Other   { char                               tags[sizeof(Cons)-0]; };
struct Chunk   { char tags[2];            char      text[sizeof(Cons)-2]; };
struct Atom    { char tags[sizeof(sexp)]; sexp                    chunks; };
struct String  { char tags[sizeof(sexp)]; sexp                    chunks; };
struct Fixnum  { char tags[sizeof(sexp)]; long                    fixnum; };
struct Float   { char tags[sizeof(Cons)-sizeof(float)];  float    flonum; };
struct Double  { char tags[sizeof(Cons)-sizeof(double)]; double   flonum; };
struct Funct   { char tags[sizeof(sexp)]; void*                    funcp; };
struct Form    { char tags[sizeof(sexp)]; Formp                    formp; };
struct Char    { char tags[sizeof(sexp)-sizeof(char)];   char         ch; };
struct InPort  { char tags[sizeof(sexp)-2]; char avail,peek; FILE*  file; };
struct OutPort { char tags[sizeof(sexp)]; FILE*                     file; };
struct Vector  { char tags[sizeof(sexp)-sizeof(short)]; short l; sexp* e; };

bool cyclic(sexp p);
sexp scan(FILE* fin);
sexp set(sexp p, sexp r);
sexp define(sexp p, sexp r);
sexp eval(sexp p, sexp env);
sexp evlis(sexp p, sexp env);
sexp apply(sexp fun, sexp args);
sexp read(FILE* fin, int level);
char* sstr(char* b, int len, sexp s);
void debug(const char *label, sexp exp);
sexp assoc(sexp formals, sexp actuals, sexp env);

/*
 * not pretty yet
 */
class ugly
{
    static const int tabs = 4;
    static const int eol = 70;

    std::stringstream& s;
    std::streampos pos;
    int level;
public:
    ugly(std::stringstream& s) : s(s) { level = 0; pos = s.tellp(); }
    void enter() { level += tabs; if (s.tellp() - pos > eol) newline(); }
    void leave() { level -= tabs; }
    void wrapminor() { if (s.tellp() - pos > eol) newline(); else space(); }
    void wrapmajor() { if (s.tellp() - pos > eol-tabs-tabs) newline(); else space(); }
    void newline() { s << '\n'; pos = s.tellp(); for (int i = level; --i >= 0; s << ' ') {} }
    void space() { s << ' '; }
};

std::stringstream& display(std::stringstream& s, sexp p, std::set<sexp>& seenSet, ugly& ugly, bool write);

// these are the built-in atoms

sexp acosa, alphapa, ampera, anda, anglea, appenda, applya, asina, ata, atana;
sexp atompa, atomsa, begin, booleanpa, boundpa, callwithina, callwithouta;
sexp cara, cdra, ceilinga, char2ia, char2inta, charcieqa, charcigea;
sexp charcigta, charcilea, charcilta, chareqa, chargea, chargta, charlea;
sexp charlta, charpa, clinporta, closurea, closurepa, cloutporta, comma;
sexp commaat, complexa, complexpa, cond, consa, cosa, curinporta, curoutporta;
sexp cyclicpa, definea, delaya, displaya, doa, dot, downcasea, e2ia, elsea;
sexp eofa, eofobjp, eqa, eqna, equalpa, eqva, evala, exactpa, expa, f, floora;
sexp forcea, forcedpa, gca, gcda, gea, gta, i2ea, ifa, inexactpa, inportpa;
sexp int2chara, integerpa, intenva, lambda, lbracket, lcma, lea, let, letrec;
sexp letstar, list2sa, list2vector, listpa, loada, loga, lowercasepa, lparen;
sexp lsha, lta, magnitudea, makestringa, makevector, minus, nega, negativepa;
sexp newlinea, nil, nota, nulenva, nullpa, num2stringa, numberpa, numericpa;
sexp openina, openouta, ora, outportpa, pairpa, peekchara, percent, pipea;
sexp plus, positivepa, powa, procedurepa, promisea, promisepa, promiseva;
sexp qchar, quasiquote, quote, rationala, rationalpa, rbracket, reada;
sexp readchara, readypa, realpa, reversea, rounda, rparen, rsha, s2lista;
sexp s2numa, s2sya, seta, setcara, setcdra, sina, slash, spacea, sqrta;
sexp star, stdina, stdouta, stringa, stringappenda, stringcieq, stringcige;
sexp stringcigt, stringcile, stringcilt, stringcopy, stringeq, stringfill;
sexp stringge, stringgt, stringle, stringlength, stringlt, stringpa, stringref;
sexp stringset, substringa, sy2sa, symbolpa, t, tana, tick, tilde, times;
sexp tracea, truncatea, unquote, unquotesplicing, upcasea, uppercasepa;
sexp vec2lista, vectora, vectorfill, vectorlength, vectorpa, vectorref;
sexp vectorset, voida, whilea, whitespacepa, withina, withouta, writea;
sexp writechara, xora, stderra;

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
           closurea == p->car &&                        // (closure
           isCons(p = p->cdr) && p->car &&              //  exp
           isCons(p = p->cdr) && p->car &&              //  env)
           !p->cdr;
}

sexp closurep(sexp s) { return isClosure(s) ? t : 0; }

bool isPromise(sexp p)
{
    return isCons(p) && promisea == p->car &&           // (promise
           isCons(p = p->cdr) &&                        // forced
           isCons(p = p->cdr) &&                        // value
           isCons(p = p->cdr) &&                        // exp
           isCons(p = p->cdr) &&                        // env)
          !p->cdr;
}

sexp promisep(sexp s) { return isPromise(s) ? t : 0; }

bool isRational(sexp p)
{
    return isCons(p) && rationala == p->car &&          // (rational
           isCons(p = p->cdr) && isFixnum(p->car) &&    // numerator
           isCons(p = p->cdr) && isFixnum(p->car) &&    // denominator
           !p->cdr;                                     // )
}

sexp rationalp(sexp s) { return isRational(s) ? t : 0; }

bool isComplex(sexp p)
{
    return isCons(p) && complexa == p->car &&           // (complex
           isCons(p = p->cdr) && isFlonum(p->car) &&    // real-part
           isCons(p = p->cdr) && isFlonum(p->car) &&    // imag-part
           !p->cdr;                                     // )
}

sexp complexp(sexp s) { return isComplex(s) ? t : 0; }

jmp_buf the_jmpbuf;

sexp tracing = 0;       // trace calls to eval
sexp atoms = 0;         // all atoms are linked in a list
sexp block = 0;         // all the storage starts here
sexp global = 0;        // this is the global symbol table (a list)
sexp inport = 0;        // the current input port
sexp errport = 0;       // the stderr port
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
        for (int i = v->l; --i >= 0; mark(v->e[i])) {}
        markCell(p);
    } else
        markCell(p);
}

void deleteinport(sexp v) { fclose(((InPort*)v)->file); }
void deleteoutport(sexp v) { fclose(((OutPort*)v)->file); }
void deletevector(sexp v) { delete ((Vector*)v)->e; }

/*
 * mark all reachable objects
 *
 * sweep all storage, putting unmarked objects on the freelist
 */
sexp gc(sexp args)
{
    bool verbose = isCons(args) && args->car;
    int werefree = MAX-allocated;
    int wereprot = psp-protect;

    marked = 0;
    mark(atoms);
    mark(global);
    mark(inport);
    mark(errport);
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
    return voida;
}

void assertAtom(sexp s)        { if (!isAtom(s))        error("not symbol"); }
void assertChar(sexp c)        { if (!isChar(c))        error("not a character"); }
void assertComplex(sexp s)     { if (!isComplex(s))     error("not complex"); }
void assertFixnum(sexp i)      { if (!isFixnum(i))      error("not an integer"); }
void assertFlonum(sexp i)      { if (!isFlonum(i))      error("not real"); }
void assertRational(sexp s)    { if (!isRational(s))    error("not rational"); }
void assertInPort(sexp s)      { if (!isInPort(s))      error("not an input port"); }
void assertOutPort(sexp s)     { if (!isOutPort(s))     error("not an output port"); }
void assertString(sexp s)      { if (!isString(s))      error("not a string"); }

/*
 * allocate a cell from the freelist
 */
sexp newcell(void)
{
    if (allocated >= MAX)
        gc(0);

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
    p->ch = c;
    return (sexp)p;
}

sexp newinport(char* name)
{
    InPort* p = (InPort*)newcell();
    p->tags[0] = OTHER;
    p->tags[1] = INPORT;
    p->avail = 0;
    p->peek = 0;
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

sexp trace(sexp arg)
{
    sexp r = tracing;
    tracing = arg ? t : 0;
    return r;
}

long asFixnum(sexp p)
{
    if (isFixnum(p))
        return ((Fixnum*)p)->fixnum;
    error("asFixnum: not a fixnum");
}

double asFlonum(sexp p)
{
    if (sizeof(double) > sizeof(void*)) {
        if (isFloat(p))
            return ((Float*)p)->flonum;
    } else {
        if (isDouble(p))
            return ((Double*)p)->flonum;
    }
    error("asFlonum: not a flonum");
}

double rat2real(sexp x)
{
    return (double)asFixnum(x->cdr->car) / (double)asFixnum(x->cdr->cdr->car);
}

sexp negativep(sexp x)
{
    if (isFixnum(x)) return asFixnum(x) < 0 ? t : 0;
    if (isFlonum(x)) return asFlonum(x) < 0.0 ? t : 0;
    if (isRational(x))
        return asFixnum(x->cdr->car) < 0 && asFixnum(x->cdr->cdr->car) > 0 ||
               asFixnum(x->cdr->car) > 0 && asFixnum(x->cdr->cdr->car) < 0 ? t : 0;
    error("negative? needs a real number");
}

sexp positivep(sexp x)
{
    if (isFixnum(x)) return asFixnum(x) > 0 ? t : 0;
    if (isFlonum(x)) return asFlonum(x) > 0.0 ? t : 0;
    if (isRational(x))
        return asFixnum(x->cdr->car) > 0 && asFixnum(x->cdr->cdr->car) > 0 ||
               asFixnum(x->cdr->car) < 0 && asFixnum(x->cdr->cdr->car) < 0 ? t : 0;
    error("positive? needs a real number");
}

sexp booleanp(sexp x) { return t == x || 0 == x ? t : 0; }

bool cmplt(sexp x, sexp y)
{
    if (isFlonum(x)) {
        if (isFlonum(y))
            return asFlonum(x) < asFlonum(y);
        if (isFixnum(y))
            return asFlonum(x) < (double)asFixnum(y);
        if (isRational(y))
            return asFlonum(x) < rat2real(y);
    } else if (isFixnum(x)) {
        if (isFixnum(y))
            return asFixnum(x) < asFixnum(y);
        if (isFlonum(y))
            return (double)asFixnum(x) < asFixnum(y);
        if (isRational(y))
            return asFixnum(x) < rat2real(y);
    } else if (isRational(x)) {
        if (isFlonum(y))
            return rat2real(x) < asFlonum(y);
        if (isFixnum(y))
            return rat2real(x) < (double)asFixnum(y);
        if (isRational(y))
            return rat2real(x) < rat2real(y);
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
        if (isRational(y))
            return asFlonum(x) <= rat2real(y);
    } else if (isFixnum(x)) {
        if (isFixnum(y))
            return asFixnum(x) <= asFixnum(y);
        if (isFlonum(y))
            return (double)asFixnum(x) <= asFixnum(y);
        if (isRational(y))
            return asFixnum(x) <= rat2real(y);
    } else if (isRational(x)) {
        if (isFlonum(y))
            return rat2real(x) <= asFlonum(y);
        if (isFixnum(y))
            return rat2real(x) <= (double)asFixnum(y);
        if (isRational(y))
            return rat2real(x) <= rat2real(y);
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

sexp newrational(long n, long d)
{
    return lose(4, cons(rationala, save(cons(save(newfixnum(n)), save(cons(save(newfixnum(d)), 0))))));
}

sexp newcomplex(double re, double im)
{
    return lose(4, cons(complexa, save(cons(save(newflonum(re)), save(cons(save(newflonum(im)), 0))))));
}

double realpart(sexp x)
{
    assertComplex(x); return asFlonum(x->cdr->car);
}

double imagpart(sexp x)
{
    assertComplex(x); return asFlonum(x->cdr->cdr->car);
}

sexp magnitude(sexp z)
{
    assertComplex(z);
    return newflonum(sqrt(asFlonum(z->cdr->car) * asFlonum(z->cdr->car) +
                          asFlonum(z->cdr->cdr->car) * asFlonum(z->cdr->cdr->car)));
}

sexp angle(sexp z)
{
    assertComplex(z);
    return newflonum(atan2(asFlonum(z->cdr->cdr->car), asFlonum(z->cdr->car)));
}

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

sexp rational_reduce(long n, long d)
{
    long g = gcd(n, d);
    long ng = n / g;
    long dg = d / g;
    if (dg < 0)
        { dg = -dg; ng = -ng; }
    if (1 == dg)
        return newfixnum(ng);
    else
        return newrational(ng, dg);
}

long num(sexp x)
{
    return asFixnum(x->cdr->car);
}

long den(sexp x)
{
    return asFixnum(x->cdr->cdr->car);
}

sexp rational_add(sexp x, sexp y)
{
    long d = lcm(den(x), den(y));
    long xn = num(x) * d / den(x);
    long yn = num(y) * d / den(y);
    return rational_reduce(xn + yn, d);
}

sexp rational_sub(sexp x, sexp y)
{
    long d = lcm(den(x), den(y));
    long xn = num(x) * d / den(x);
    long yn = num(y) * d / den(y);
    return rational_reduce(xn - yn, d);
}

sexp rational_mul(sexp x, sexp y)
{
    long g = gcd(den(x), den(y));
    return rational_reduce(num(x) * num(y) / g, den(x) * den(y) / g);
}

sexp rational_div(sexp x, sexp y)
{
    long g = gcd(den(x), den(y));
    return rational_reduce(num(x) * den(y) / g, den(x) * num(y) / g);
}

sexp complex_add(sexp z, sexp w)
{
    double re = realpart(z)+realpart(w);
    double im = imagpart(z)+imagpart(w);
    return 0.0 == im ? newflonum(re) : newcomplex(re, im);
}

sexp complex_sub(sexp z, sexp w)
{
    double re = realpart(z)-realpart(w);
    double im = imagpart(z)-imagpart(w);
    return 0.0 == im ? newflonum(re) : newcomplex(re, im);
}

sexp complex_mul(sexp z, sexp w)
{
    double x = realpart(z);
    double y = imagpart(z);
    double u = realpart(w);
    double v = imagpart(w);
    double re = x*u - y*v;
    double im = x*v + y*u;
    return 0.0 == im ? newflonum(re) : newcomplex(re, im);
}

sexp complex_div(sexp z, sexp w)
{
    double x = realpart(z);
    double y = imagpart(z);
    double u = realpart(w);
    double v = imagpart(w);
    double d = u*u + v*v;
    double re = (x*u + y*v) / d;
    double im = (y*u - x*v) / d;
    return 0.0 == im ? newflonum(re) : newcomplex(re, im);
}

sexp uniadd(sexp l)
{
    sexp* mark = psp;
    sexp sum = replace(l->car);
    save(sum); save(l);
    while (l = l->cdr) {
        sexp x = l->car;
        if (isFixnum(sum)) {
            if (isFixnum(x))
                sum = replace(newfixnum(asFixnum(sum) + asFixnum(x)));
            else if (isFlonum(x))
                sum = replace(newflonum((double)asFixnum(sum) + asFlonum(x)));
            else if (isRational(x))
                sum = replace(rational_add(newrational(asFixnum(sum), 1), x));
            else if (isComplex(x))
                sum = replace(complex_add(newcomplex((double)asFixnum(sum), 0.0), x));
            else
                error("not a number");
        } else if (isFlonum(sum)) {
            if (isFixnum(x))
                sum = replace(newflonum(asFlonum(sum) + (double)asFixnum(x)));
            else if (isFlonum(x))
                sum = replace(newflonum(asFlonum(sum) + asFlonum(x)));
            else if (isRational(x))
                sum = replace(newflonum(asFlonum(sum) + rat2real(x)));
            else if (isComplex(x))
                sum = replace(complex_add(newcomplex(asFlonum(sum), 0.0), x));
            else
                error("not a number");
        } else if (isRational(sum)) {
            if (isFixnum(x))
                sum = replace(rational_add(sum, newrational(asFixnum(x), 1)));
            else if (isFlonum(x))
                sum = replace(newflonum(rat2real(sum) + asFlonum(x)));
            else if (isRational(x))
                sum = replace(rational_add(sum, x));
            else if (isComplex(x))
                sum = replace(complex_add(newcomplex(rat2real(sum), 0.0), x));
            else
                error("not a number");
        } else if (isComplex(sum)) {
            if (isFixnum(x))
                sum = replace(complex_add(sum, newcomplex((double)asFixnum(x), 0.0)));
            else if (isFlonum(x))
                sum = replace(complex_add(sum, newcomplex(asFlonum(x), 0.0)));
            else if (isRational(x))
                sum = replace(complex_add(sum, newcomplex(rat2real(x), 0.0)));
            else if (isComplex(x))
                sum = replace(complex_add(sum, x));
            else
                error("not a number");
        } else
            error("not a number");
    }
    return lose(mark, sum);
}

sexp negf(sexp x)
{
    if (isFixnum(x))
        return newfixnum(-asFixnum(x));
    if (isFlonum(x))
        return newflonum(-asFlonum(x));
    if (isRational(x))
        return rational_reduce(-asFixnum(x->cdr->car), asFixnum(x->cdr->cdr->car));
    if (isComplex(x))
        return newcomplex(-asFlonum(x->cdr->car), -asFlonum(x->cdr->cdr->car));
    error("neg: not a number");
}

sexp unisub(sexp l)
{
    if (!l)
        return newfixnum(0);
    if (!l->cdr)
        return negf(l->car);
    return lose(2, uniadd(cons(l->car, save(cons(negf(save(uniadd(l->cdr))), 0)))));
}

sexp unimul(sexp l)
{
    sexp* mark = psp;
    sexp product = l->car;
    save(product); save(l);

    while (l = l->cdr) {
        sexp x = l->car;
        if (isFixnum(product)) {
            if (isFixnum(x))
                product = replace(newfixnum(asFixnum(product) * asFixnum(x)));
            else if (isFlonum(x))
                product = replace(newflonum((double)asFixnum(product) * asFlonum(x)));
            else if (isRational(x))
                product = replace(rational_mul(newrational(asFixnum(product), 1), x));
            else if (isComplex(x))
                product = replace(complex_mul(newcomplex((double)asFixnum(product), 0.0), x));
            else
                error("not a number");
        } else if (isFlonum(product)) {
            if (isFixnum(x))
                product = replace(newflonum(asFlonum(product) * (double)asFixnum(x)));
            else if (isFlonum(x))
                product = replace(newflonum(asFlonum(product) * asFlonum(x)));
            else if (isRational(x))
                product = replace(newflonum(asFlonum(product) * rat2real(x)));
            else if (isComplex(x))
                product = replace(newcomplex(asFlonum(product)*realpart(x), asFlonum(product)*imagpart(x)));
            else
                error("not a number");
        } else if (isRational(product)) {
            if (isFixnum(x))
                product = replace(rational_mul(product, newrational(asFixnum(x), 1)));
            else if (isFlonum(x))
                product = replace(newflonum(rat2real(product) * asFlonum(x)));
            else if (isRational(x))
                product = replace(rational_mul(product, x));
            else if (isComplex(x))
                product = replace(newcomplex(rat2real(product)*realpart(x), rat2real(product)*imagpart(x)));
            else
                error("not a number");
        } else if (isComplex(product)) {
            if (isFixnum(x)) {
                double re = realpart(product) * (double)asFixnum(x);
                double im = realpart(product) * (double)asFixnum(x);
                return 0.0 == im ? newflonum(re) : newcomplex(re, im);
            } else if (isFlonum(x)) {
                double re = realpart(product) * asFlonum(x);
                double im = realpart(product) * asFlonum(x);
                return 0.0 == im ? newflonum(re) : newcomplex(re, im);
            } else if (isRational(x)) {
                double re = realpart(product) * rat2real(x);
                double im = realpart(product) * rat2real(x);
                return 0.0 == im ? newflonum(re) : newcomplex(re, im);
            } else if (isComplex(x))
                product = replace(complex_mul(product, x));
            else
                error("not a number");
        } else
            error("not a number");
    }
    return lose(mark, product);
}

sexp unidiv(sexp l)
{
    sexp* mark = psp;
    sexp product = l->car;
    save(l); save(product);

    while (l = l->cdr) {
        sexp x = l->car;
        if (isFixnum(product)) {
            if (isFixnum(x))
                product = replace(rational_reduce(asFixnum(product), asFixnum(x)));
            else if (isFlonum(x))
                product = replace(newflonum((double)asFixnum(product) / asFlonum(x)));
            else if (isRational(x))
                product = replace(rational_div(newrational(asFixnum(product), 1), x));
            else if (isComplex(x))
                product = replace(complex_div(newcomplex((double)asFixnum(product), 0.0), x));
            else
                error("not a number");
        } else if (isFlonum(product)) {
            if (isFixnum(x))
                product = replace(newflonum(asFlonum(product) / (double)asFixnum(x)));
            else if (isFlonum(x))
                product = replace(newflonum(asFlonum(product) / asFlonum(x)));
            else if (isRational(x))
                product = replace(newflonum(asFlonum(product) / rat2real(x)));
            else if (isComplex(x))
                product = replace(complex_div(newcomplex(asFlonum(product), 0.0), x));
            else
                error("not a number");
        } else if (isRational(product)) {
            if (isFixnum(x))
                product = replace(rational_div(product, newrational(asFixnum(x), 1)));
            else if (isFlonum(x))
                product = replace(newflonum(rat2real(product) / asFlonum(x)));
            else if (isRational(x))
                product = replace(rational_div(product, x));
            else if (isComplex(x))
                product = replace(complex_div(newcomplex(rat2real(product), 0.0), x));
            else
                error("not a number");
        } else if (isComplex(product)) {
            if (isFixnum(x))
                product = replace(complex_div(product, newcomplex((double)asFixnum(x), 0.0)));
            else if (isFlonum(x))
                product = replace(complex_div(product, newcomplex(asFlonum(x), 0.0)));
            else if (isRational(x))
                product = replace(newcomplex(realpart(product)/rat2real(x), imagpart(product)/rat2real(x)));
            else if (isComplex(x))
                product = replace(complex_div(product, x));
            else
                error("not a number");
        } else
            error("not a number");
    }
    return lose(mark, product);
}

sexp rational_mod(sexp x, sexp y)
{
    long d = lcm(den(x), den(y));
    long xn = num(x) * d / den(x);
    long yn = num(y) * d / den(y);
    return rational_reduce(xn % yn, d);
}

sexp complex_mod(sexp x, sexp y)
{
    error("complex_mod: not implemented");
}

sexp unimod(sexp l)
{
    sexp* mark = psp;
    sexp product = l->car;
    save(l); save(product);

    while (l = l->cdr) {
        sexp x = l->car;
        if (isFixnum(product)) {
            if (isFixnum(x))
                product = replace(newfixnum(asFixnum(product) % asFixnum(x)));
            else if (isFlonum(x))
                product = replace(newflonum(fmod((double)asFixnum(product), asFlonum(x))));
            else if (isRational(x))
                product = replace(rational_mod(newrational(asFixnum(product), 1), x));
            else if (isComplex(x))
                product = replace(complex_mod(newcomplex((double)asFixnum(product), 0.0), x));
            else
                error("not a number");
        } else if (isFlonum(product)) {
            if (isFixnum(x))
                product = replace(newflonum(fmod(asFlonum(product), (double)asFixnum(x))));
            else if (isFlonum(x))
                product = replace(newflonum(fmod(asFlonum(product), asFlonum(x))));
            else if (isRational(x))
                product = replace(newflonum(fmod(asFlonum(product), rat2real(x))));
            else if (isComplex(x))
                product = replace(complex_mod(newcomplex(asFlonum(product), 0.0), x));
            else
                error("not a number");
        } else if (isRational(product)) {
            if (isFixnum(x))
                product = replace(rational_mod(product, newrational(asFixnum(x), 1)));
            else if (isFlonum(x))
                product = replace(newflonum(fmod(rat2real(product), asFlonum(x))));
            else if (isRational(x))
                product = replace(rational_mod(product, x));
            else if (isComplex(x))
                product = replace(complex_mod(newcomplex(rat2real(product), 0.0), x));
            else
                error("not a number");
        } else if (isComplex(product)) {
            if (isFixnum(x))
                product = replace(newcomplex(fmod(realpart(product), (double)asFixnum(x)),
                                             fmod(imagpart(product), (double)asFixnum(x))));
            else if (isFlonum(x))
                product = replace(newcomplex(fmod(realpart(product), asFlonum(x)),
                                             fmod(imagpart(product), asFlonum(x))));
            else if (isRational(x))
                product = replace(newcomplex(fmod(realpart(product), rat2real(x)),
                                             fmod(imagpart(product), rat2real(x))));
            else if (isComplex(x))
                product = replace(complex_mod(product, x));
            else
                error("not a number");
        } else
            error("not a number");
    }
    return lose(mark, product);
}

// functions on real numbers
sexp sinff(sexp x) { assertFlonum(x); return newflonum(sin(asFlonum(x))); }
sexp cosff(sexp x) { assertFlonum(x); return newflonum(cos(asFlonum(x))); }
sexp tanff(sexp x) { assertFlonum(x); return newflonum(tan(asFlonum(x))); }
sexp expff(sexp x) { assertFlonum(x); return newflonum(exp(asFlonum(x))); }
sexp logff(sexp x) { assertFlonum(x); return newflonum(log(asFlonum(x))); }
sexp asinff(sexp x) { assertFlonum(x); return newflonum(asin(asFlonum(x))); }
sexp acosff(sexp x) { assertFlonum(x); return newflonum(acos(asFlonum(x))); }
sexp atanff(sexp x) { assertFlonum(x); return newflonum(atan(asFlonum(x))); }
sexp ceilingff(sexp x) { assertFlonum(x); return newflonum(ceil(asFlonum(x))); }
sexp floorff(sexp x) { assertFlonum(x); return newflonum(floor(asFlonum(x))); }
sexp roundff(sexp x) { assertFlonum(x); return newflonum(round(asFlonum(x))); }
sexp sqrtff(sexp x) { assertFlonum(x); return newflonum(sqrt(asFlonum(x))); }

sexp powff(sexp x, sexp y)
{
    assertFlonum(x); assertFlonum(y); return newflonum(pow(asFlonum(x), asFlonum(y)));
}

sexp truncateff(sexp x)
{
    assertFlonum(x); return newflonum(asFlonum(x) < 0 ? ceil(asFlonum(x)) : floor(asFlonum(x)));
}

// exact, inexact
sexp exactp(sexp x) { return isFixnum(x) ? t : 0; }
sexp integerp(sexp x) { return isFixnum(x) ? t : isFlonum(x) && (long)asFlonum(x) == asFlonum(x) ? t : 0; }
sexp inexactp(sexp x) { return isFlonum(x) ? t : 0; }
sexp realp(sexp x) { return (isFixnum(x) || isFlonum(x)) ? t : 0; }
sexp i2ef(sexp x) { assertFlonum(x); return newfixnum((long)asFlonum(x)); }
sexp e2if(sexp x) { assertFixnum(x); return newflonum((double)asFixnum(x)); }

// shifts
sexp lsh(sexp x, sexp y) { assertFixnum(x); assertFixnum(y); return newfixnum(asFixnum(x) << asFixnum(y)); }
sexp rsh(sexp x, sexp y) { assertFixnum(x); assertFixnum(y); return newfixnum(asFixnum(x) >> asFixnum(y)); }

// list structure predicates
sexp isnot(sexp x) { return x ? 0 : t; }
sexp nullp(sexp x) { return x ? 0 : t; }
sexp cyclicp(sexp x) { return cyclic(x) ? t : 0; }
sexp listp(sexp x) { return !isCons(x) ? 0 : listp(x->cdr) ? t : 0; }
sexp pairp(sexp x) { return isCons(x) ? t : 0; }
sexp numberp(sexp x) { return isFixnum(x) || isFlonum(x) ? t : 0; }
sexp stringp(sexp x) { return isString(x) ? t : 0; }
sexp symbolp(sexp x) { return isAtom(x) ? t : 0; }
sexp procedurep(sexp p) { return isFunct(p) || isClosure(p) ? t : 0; }

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

std::stringstream& num2string(std::stringstream& s, sexp exp)
{
    if (isFixnum(exp))
        s << asFixnum(exp);
    else if (isFlonum(exp))
        s << asFlonum(exp);
    else if (isRational(exp))
        s << asFixnum(exp->cdr->car) << '/' << asFixnum(exp->cdr->cdr->car);
    else if (isComplex(exp)) {
        s << asFlonum(exp->cdr->car);
        double im = asFlonum(exp->cdr->cdr->car);
        if (im > 0.0)
            s << '+' << im << 'i';
        else if (im < 0.0)
            s << im << 'i';
    } else
        error("number->string: not a number");
    return s;
}

sexp number2string(sexp exp)
{
    std::stringstream s;
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    num2string(s, exp);
    return lose(1, newstring(save(newchunk(s.str().c_str()))));
}

sexp makestring(sexp args)
{
    if (!args || !isFixnum(args->car))
        error("make-string: args expected");

    int l = asFixnum(args->car);
    char *b = (char*) alloca(l+1);
    char *q = b;
    char c = args->cdr &&
             isChar(args->cdr->car) ?
             ((Char*)(args->cdr->car))->ch : ' ';
    for (int i = 0; i < l; ++i)
        *q++ = c;
    *q++ = 0;
    return lose(1, newstring(save(newchunk(b))));
}

char* sstr(char* b, int len, sexp s)
{
    if (!isString(s))
        assertAtom(s);
    if (!isAtom(s))
        assertString(s);

    char *q = b;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        if (q >= b+len-1)
            break;
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; *q++ = t->text[i++]) {}
    }
    *q++ = 0;
    return b;
}

sexp stringcopyf(sexp s)
{
    assertString(s);

    int len = slen(s)+1;
    return lose(1, newstring(save(newchunk(sstr((char*)alloca(len), len, s)))));
}

sexp stringappend(sexp p, sexp q)
{
    assertString(p);
    assertString(q);

    int pl = slen(p);
    int ql = slen(q);

    char *b = (char*) alloca(pl+ql+1);

    sstr(b, pl+1, p);
    sstr(b+pl, ql+1, q);

    return lose(1, newstring(save(newchunk(b))));
}

sexp stringfillf(sexp s, sexp c)
{
    assertString(s);
    assertChar(c);

    char k = ((Char*)c)->ch;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; t->text[i++] = k) {}
    }
    return s;
}

// close-input-port
sexp clinport(sexp p)
{
    assertInPort(p);
    if (inport == p)
        inport = 0;
    fclose(((OutPort*)p)->file);
    ((OutPort*)p)->file = 0;
}

// close-output-port
sexp cloutport(sexp p)
{
    assertOutPort(p);
    if (outport == p)
        outport = 0;
    fclose(((InPort*)p)->file);
    ((InPort*)p)->file = 0;
}

// current-input-port
sexp curinport(sexp p) { return inport ? inport : 0; }

// current-output-port
sexp curoutport(sexp p) { return outport ? outport : 0; }

// input-port?
sexp inportp(sexp p) { return isInPort(p) ? t : 0; }

// open-input-file
sexp openin(sexp p)
{
    assertString(p);
    int len = slen(p)+1;
    char* b = (char*) alloca(len); sstr(b, len, p);
    return newinport(b);
}

// open-output-file
sexp openout(sexp p)
{
    assertString(p);
    int len = slen(p)+1;
    char* b = (char*) alloca(slen(p)+1);
    sstr(b, len, p);
    return newoutport(b);
}

// output-port?
sexp outportp(sexp p) { return isOutPort(p) ? t : 0; }

// with-input-from-file
sexp within(sexp p, sexp f)
{
    sexp t = inport;
    inport = openin(p);
    sexp q = apply(f, 0);
    clinport(inport);
    inport = t;
    return q;
}

// with-output-to-file
sexp without(sexp p, sexp f)
{
    sexp t = outport;
    outport = openout(p);
    sexp q = apply(f, 0);
    cloutport(outport);
    outport = t;
    return q;
}

// call-with-input-file
sexp callwithin(sexp p, sexp f)
{
    sexp inp = openin(p);
    sexp q = apply(f, cons(inp, 0));
    clinport(inp);
    return q;
}

// call-with-output-file
sexp callwithout(sexp p)
{
    sexp oup = openout(p);
    sexp q = apply(f, cons(oup, 0));
    cloutport(oup);
    return q;
}

sexp vectorp(sexp v)
{
    return isVector(v) ? t : 0;
}

sexp newvector(int len, sexp fill)
{
    Vector* v = (Vector*) save(newcell());
    v->tags[0] = OTHER;
    v->tags[1] = VECTOR;
    v->l = len;
    v->e = new sexp[len];
    for (int i = v->l; --i >= 0; v->e[i] = fill) {}
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
        v->e[index++] = p->car;
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
    int index = v->l;
    sexp list = save(0);
    while (index > 0)
        replace(list = cons(v->e[--index], list));
    return lose(2, list);
}

sexp vecfill(sexp vector, sexp value)
{
    assertVector(vector);
    save(value);
    save(vector);
    Vector* v = (Vector*)vector;
    int index = v->l;
    while (index > 0)
        v->e[--index] = value;
    return lose(2, vector);
}

sexp veclength(sexp vector)
{
    assertVector(vector);
    save(vector);
    return lose(1, newfixnum(((Vector*)vector)->l));
}

sexp vecref(sexp vector, sexp index)
{
    assertFixnum(index);
    assertVector(vector);
    return ((Vector*)vector)->e[asFixnum(index)];
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
        v->e[index++] = p->car;
    return lose(2, (sexp)v);
}

sexp vecset(sexp vector, sexp index, sexp value)
{
    assertFixnum(index);
    assertVector(vector);
    Vector* v = (Vector*)vector;
    v->e[asFixnum(index)] = value;
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

sexp alphap(sexp c) { return isChar(c) && isalpha(((Char*)c)->ch) ? t : 0; }
sexp char2int(sexp c) { assertChar(c); return  newfixnum(((Char*)c)->ch); }
sexp charcieq(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) == tolower(((Char*)q)->ch) ? t : 0; }
sexp charcige(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) >= tolower(((Char*)q)->ch) ? t : 0; }
sexp charcigt(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) >  tolower(((Char*)q)->ch) ? t : 0; }
sexp charcile(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) <= tolower(((Char*)q)->ch) ? t : 0; }
sexp charcilt(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) <  tolower(((Char*)q)->ch) ? t : 0; }
sexp chareq(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch == ((Char*)q)->ch ? t : 0; }
sexp charge(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch >= ((Char*)q)->ch ? t : 0; }
sexp chargt(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch >  ((Char*)q)->ch ? t : 0; }
sexp charle(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch <= ((Char*)q)->ch ? t : 0; }
sexp charlt(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch <  ((Char*)q)->ch ? t : 0; }
sexp charp(sexp c) { return isChar(c) ? t : 0; }
sexp downcase(sexp c) { assertChar(c); return newcharacter(tolower(((Char*)c)->ch)); }
sexp int2char(sexp c) { assertFixnum(c); return newcharacter(asFixnum(c)); }
sexp lowercasep(sexp c) { return isChar(c) && islower(((Char*)c)->ch) ? t : 0; }
sexp numericp(sexp c) { return isChar(c) && isdigit(((Char*)c)->ch) ? t : 0; }
sexp upcase(sexp c) { assertChar(c); return newcharacter(toupper(((Char*)c)->ch)); }
sexp uppercasep(sexp c) { return isChar(c) && isupper(((Char*)c)->ch) ? t : 0; }
sexp whitespacep(sexp c) { return isChar(c) && isspace(((Char*)c)->ch) ? t : 0; }

void setTermios(struct termios* original, struct termios* working, int vmin)
{
    memcpy((void*)working, (void*)original, sizeof(struct termios));
    working->c_cc[VMIN] = vmin;
    working->c_cc[VTIME] = 0;
    working->c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP | INLCR | IGNCR | ICRNL | IXON);
    working->c_oflag &= ~OPOST;
    working->c_lflag &= ~(ECHO | ECHONL | ICANON | ISIG | IEXTEN);
    working->c_cflag &= ~(CSIZE | PARENB);
    working->c_cflag |= CS8;
}

sexp readyp(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);

    InPort* inPort = (InPort*)port;

    struct termios original;

    if (0 == tcgetattr(fileno(inPort->file), &original))
    {
        struct termios working;

        if (inPort->avail)
            return t;

        setTermios(&original, &working, 0);

        if (0 == tcsetattr(fileno(stdin), TCSANOW, &working))
        {
            inPort->avail = read(fileno(stdin), &inPort->peek, 1) > 0;
            tcsetattr(fileno(stdin), TCSANOW, &original);
        }
        return inPort->avail ? t : 0;
    } else
        return t;
}

sexp readchar(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);

    InPort* inPort = (InPort*)port;

    struct termios original;

    if (0 == tcgetattr(fileno(stdin), &original))
    {
        if (inPort->avail)
        {
            inPort->avail = false;
            return newcharacter(inPort->peek);
        }

        struct termios working;

        setTermios(&original, &working, 1);

        if (0 == tcsetattr(fileno(stdin), TCSANOW, &working))
        {
            while (0 == read(fileno(stdin), &inPort->peek, 1)) {}
            tcsetattr(fileno(stdin), TCSANOW, &original);
        }
        return newcharacter(inPort->peek);
    }
    return newcharacter(getc(inPort->file));
}

sexp peekchar(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);

    InPort* inPort = (InPort*)port;

    struct termios original;

    if (0 == tcgetattr(fileno(stdin), &original))
    {
        if (inPort->avail)
            return newcharacter(inPort->peek);

        struct termios working;

        setTermios(&original, &working, 1);

        if (0 == tcsetattr(fileno(stdin), TCSANOW, &working))
        {
            while (0 == read(fileno(stdin), &inPort->peek, 1)) {}
            inPort->avail = true;
            tcsetattr(fileno(stdin), TCSANOW, &original);
        }
        return newcharacter(inPort->peek);
    }

    int c = getc(inPort->file);
    ungetc(c, inPort->file);
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
    fprintf(((OutPort*)port)->file, "#\\%c", ((Char*)(args->car))->ch);
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

    *p = ((Char*)c)->ch;

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
sexp eqnp(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return asFixnum(x) == asFixnum(y) ? t : 0;
        else if (isFlonum(y))
            return asFixnum(x) == asFlonum(y) ? t : 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return asFlonum(x) == asFixnum(y) ? t : 0;
        else if (isFlonum(y))
            return asFlonum(x) == asFlonum(y) ? t : 0;
    } else if (isRational(x) && isRational(y))
        return (asFixnum(x->cdr->car) == asFixnum(y->cdr->car) &&
                asFixnum(x->cdr->car) == asFixnum(y->cdr->car)) ? t : 0;
    else if (isComplex(x) && isComplex(y))
        return (asFlonum(x->cdr->car) == asFlonum(y->cdr->car) &&
                asFlonum(x->cdr->cdr->car) == asFlonum(y->cdr->cdr->car)) ? t : 0;
    else
        return 0;
}

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
    if (allfixnums(save(args))) {
        long result = ~0;
        for (sexp p = args; p; p = p->cdr)
            result = result & asFixnum(p->car);
        return lose(1, newfixnum(result));
    } else
        return lose(1, 0);
}

sexp orf(sexp args)
{
    if (allfixnums(save(args))) {
        long result = 0;
        for (sexp p = args; p; p = p->cdr)
            result = result | asFixnum(p->car);
        return lose(1, newfixnum(result));
    } else
        return lose(1, 0);
}

sexp xorf(sexp args)
{
    if (allfixnums(save(args))) {
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

    int len = slen(x)+1;

    char *name = sstr((char*)alloca(len), len, x);

    printf("; load: %s\n", name);

    FILE* fin = fopen(name, "r");
    if (fin)
    {
        while (!feof(fin))
        {
            sexp input = read(fin, 0);
            if (eofa == input)
                break;
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
    std::stringstream s;
    ugly ugly(s);
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    std::set<sexp> seenSet;
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    display(s, args->car, seenSet, ugly, false);
    fwrite(s.str().c_str(), 1, s.str().length(), ((OutPort*)port)->file);
    return voida;
}

sexp writef(sexp args)
{
    std::stringstream s;
    ugly ugly(s);
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    std::set<sexp> seenSet;
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    display(s, args->car, seenSet, ugly, true);
    fwrite(s.str().c_str(), 1, s.str().length(), ((OutPort*)port)->file);
    return voida;
}

std::stringstream& displayChunks(std::stringstream& s, sexp exp, bool write)
{
    if (write)
        s << '"';
    while (exp)
    {
        Chunk* t = (Chunk*)(exp->car);
        for (int i = 0; i < sizeof(t->text); ++i)
        {
            char c = t->text[i];
            if (!c)
                break;
            s << c;
        }
        exp = exp->cdr;
    }
    if (write)
        s << '"';
    return s;
}

bool cyclic(std::set<sexp>& seenSet, sexp exp)
{
    if (!exp || isClosure(exp) || isPromise(exp))
        return false;
    if (isCons(exp)) {
        if (seenSet.find(exp) != seenSet.end())
            return true;
        seenSet.insert(exp);
        return cyclic(seenSet, exp->car) || cyclic(seenSet, exp->cdr);
    } else if (isVector(exp)) {
        if (seenSet.find(exp) != seenSet.end())
            return true;
        seenSet.insert(exp);
        Vector* v = (Vector*)exp;
        for (int i = v->l; --i >= 0; )
            if (cyclic(seenSet, v->e[i]))
                return true;
        return false;
    }
    return false;
}

/*
 * test for cyclic data structures
 */
bool cyclic(sexp exp)
{
    std::set<sexp> seenSet;
    return cyclic(seenSet, exp);
}

bool safe(std::set<sexp>& seenSet, sexp exp)
{
    return seenSet.find(exp) == seenSet.end();
}

void insert(std::set<sexp>& seenSet, sexp exp)
{
    seenSet.insert(exp);
}

std::stringstream& displayList(std::stringstream& s, sexp exp, std::set<sexp>& seenSet, ugly& ugly, bool write)
{
    ugly.enter();
    s << '(';
    while (exp && safe(seenSet, exp)) {
        display(s, exp->car, seenSet, ugly, write);
        insert(seenSet, exp);
        if (exp->cdr) {
            if (isCons(exp->cdr) && !isClosure(exp->cdr) && !isPromise(exp->cdr))
            {
                if (safe(seenSet, exp->cdr))
                {
                    exp = exp->cdr;
                    if (isCons(exp->car) || isVector(exp->car))
                        ugly.wrapmajor();
                    else
                        ugly.wrapminor();
                }
            } else {
                s << " . ";
                exp = exp->cdr;
                display(s, exp, seenSet, ugly, write);
                exp = 0;
            }
        } else
            exp = exp->cdr;
    }
    s << ')';
    ugly.leave();
    return s;
}

std::stringstream& displayVector(std::stringstream& s, sexp v, std::set<sexp>& seenSet, ugly& ugly, bool write)
{
    ugly.enter();
    s << '[';
    Vector *vv = (Vector*)v;
    for (int i = 0; i < vv->l; ++i)
    {
        s << ',';
        if (isCons(vv->e[i]) || isVector(vv->e[i]))
            ugly.wrapmajor();
        else
            ugly.wrapminor();
        if (safe(seenSet, vv->e[i]))
            display(s, vv->e[i], seenSet, ugly, write);
    }
    s << ']';
    ugly.leave();
    return s;
}

const char *character_table[] =
{
    "\000nul",       "\001soh", "\002stx",     "\003etx", "\004eot", "\005enq",    "\006ack", "\007bell",
    "\010backspace", "\011tab", "\012newline", "\013vt",  "\014ff",  "\015return", "\016so",  "\017si",
    "\020dle",       "\021dc1", "\022dc2",     "\023dc3", "\024dc4", "\025nak",    "\026syn", "\027etb",
    "\030can",       "\031em",  "\032sub",     "\033esc", "\034fs",  "\035gs",     "\036rs",  "\037us",
    "\040space",     "\177del", 0
};

std::stringstream& display(std::stringstream& s, sexp exp, std::set<sexp>& seenSet, ugly& ugly, bool write)
{
    if (!exp)
        s << "#f";
    else if (isFixnum(exp))
        s << asFixnum(exp);
    else if (isFlonum(exp))
        s << asFlonum(exp);
    else if (isRational(exp))
        s << asFixnum(exp->cdr->car) << '/' << asFixnum(exp->cdr->cdr->car);
    else if (isComplex(exp)) {
        s << asFlonum(exp->cdr->car);
        double im = asFlonum(exp->cdr->cdr->car);
        if (im > 0.0)
            s << '+' << im << 'i';
        else if (im < 0.0)
            s << im << 'i';
    } else if (isClosure(exp))
        s << "#<closure@" << std::hex << (void*)exp << std::dec << '>';
    else if (isPromise(exp))
        s << "#<promise@" << std::hex << (void*)exp << std::dec << '>';
    else if (isCons(exp)) {
        if (safe(seenSet, exp))
            displayList(s, exp, seenSet, ugly, write);
    } else if (isString(exp))
        displayChunks(s, ((String*)exp)->chunks, write);
    else if (isAtom(exp))
        displayChunks(s, ((Atom*)exp)->chunks, false);
    else if (isVector(exp) && safe(seenSet, exp))
        displayVector(s, exp, seenSet, ugly, write);
    else if (isFunct(exp))
        s << "#<function" << arity(exp) << '@' << std::hex << (void*)((Funct*)exp)->funcp << std::dec << '>';
    else if (isForm(exp))
        s << "#<form@" << std::hex << (void*)((Form*)exp)->formp << std::dec << '>';
    else if (isInPort(exp))
        s << "#<input@" << fileno(((InPort*)exp)->file) << '>';
    else if (isOutPort(exp))
        s << "#<output@" << fileno(((OutPort*)exp)->file) << '>';
    else if (isChar(exp)) {
        if (write) {
            char c = ((Char*)exp)->ch;
            for (int i = 0; character_table[i]; ++i)
                if (c == *character_table[i]) {
                    s << "#\\" << 1+character_table[i];
                    return s;
                }
            s << "#\\" << ((Char*)exp)->ch;;
        } else
            s << ((Char*)exp)->ch;
    } else
        error("display: unknown object");
    return s;
}

void debug(const char *label, sexp exp)
{
    std::stringstream s;
    ugly ugly(s);
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    std::set<sexp> seenSet;
    s << label << ':';
    display(s, exp, seenSet, ugly, true);
    s << '\n';
    fwrite(s.str().c_str(), 1, s.str().length(), stdout);
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
        return newcomplex(x, y);
    if (2 == sscanf(b, "%lf@%lf", &x, &y))
        return newcomplex(x * cos(y), x * sin(y));
    if (2 == sscanf(b, "%ld/%ld", &z, &w))
        return rational_reduce(z, w);
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

        r->text[i++] = ((Char*)(s->car))->ch;

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

bool eqvb(std::set<sexp>& seenx, std::set<sexp>& seeny, sexp x, sexp y);

bool cmpv(std::set<sexp>& seenx, std::set<sexp>& seeny, sexp p, sexp q)
{
    Vector* pv = (Vector*)p;
    Vector* qv = (Vector*)q;

    if (pv->l != qv->l)
        return false;

    for (int i = pv->l; --i >= 0; )
        if (!eqvb(seenx, seeny, pv->e[i], qv->e[i]))
            return false;

    return true;
}

bool eqvb(std::set<sexp>& seenx, std::set<sexp>& seeny, sexp x, sexp y)
{
    if (x == y)
        return true;
    if (!x || !y)
        return false;
    if (isAtom(x) || isAtom(y))
        return false;
    if (isCons(x) && isCons(y))
    {
        if (seenx.find(x) != seenx.end() &&
            seeny.find(y) != seeny.end())
            return true;
        seenx.insert(x);
        seeny.insert(y);
        return eqvb(seenx, seeny, x->car, y->car) && eqvb(seenx, seeny, x->cdr, y->cdr);
    }
    if (evalType(x) != evalType(y))
        return false;
    switch (evalType(x)) 
    {
    case CHUNK : return 0 == scmp(x, y);
    case STRING: return 0 == scmp(((String*)x)->chunks, ((String*)y)->chunks);
    case FIXNUM: return asFixnum(x) == asFixnum(y);
    case FLOAT :
    case DOUBLE: return asFlonum(x) == asFlonum(y);
    case VECTOR: return cmpv(seenx, seeny, x, y);
    case CHAR:   return ((Char*)x)->ch == ((Char*)y)->ch;
    default:     return 0;
    }
}

sexp eqv(sexp x, sexp y)
{
    std::set<sexp> seenx;
    std::set<sexp> seeny;
    return eqvb(seenx, seeny, x, y) ? t : 0;
}

sexp equalp(sexp x, sexp y)
{
    std::set<sexp> seenx;
    std::set<sexp> seeny;
    return eqvb(seenx, seeny, x, y) ? t : 0;
}

void fixenvs(sexp env)
{
    for (sexp f = env; f; f = f->cdr)
        if (isClosure(f->car->cdr))
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

static char errorBuffer[128];   // used by get and set

sexp boundp(sexp p, sexp env)
{
    for (sexp q = env; q; q = q->cdr)
        if (q->car && p->cdr->car == q->car->car)
            return t;
    return 0;
}

sexp get(sexp p, sexp env)
{
    for (sexp q = env; q; q = q->cdr)
        if (q->car && p == q->car->car)
            return q->car->cdr;

    char msg[] = "error: get unbound ";
    strcpy(errorBuffer, msg);
    int  len = slen(p);
    if (len > sizeof(errorBuffer)-sizeof(msg))
        len = sizeof(errorBuffer)-sizeof(msg);
    sstr(errorBuffer+sizeof(msg)-1, len, p);
    error(errorBuffer);
}

sexp set(sexp p, sexp r, sexp env)
{
    for (sexp q = env; q; q = q->cdr)
        if (p == q->car->car)
        {
            q->car->cdr = r;
            return voida;
        }

    char msg[] = "error: set unbound ";
    strcpy(errorBuffer, msg);
    int  len = slen(p);
    if (len > sizeof(errorBuffer)-sizeof(msg))
        len = sizeof(errorBuffer)-sizeof(msg);
    sstr(errorBuffer+sizeof(msg)-1, len, p);
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
    return lose(5, cons(save(cons(formals->car, actuals->car)),
                       save(assoc(save(formals)->cdr, save(actuals)->cdr, save(env)))));
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
    else if (exp->car && unquotesplicing == exp->car->car)
        return lose(mark, save(append(save(eval(exp->car->cdr->car, env)),
                                      save(unquoteform(save(exp)->cdr, save(env))))));
    else
        return lose(mark, cons(save(unquoteform(exp->car, env)),
                               save(unquoteform(save(exp)->cdr, save(env)))));
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

sexp letform(sexp exp, sexp env)
{
    sexp r;
    sexp* mark = psp;
    sexp e = save(env);
    for (sexp v = save(exp)->cdr->car; v; v = v->cdr)
        e = save(cons(save(cons(v->car->car, save(eval(v->car->cdr->car, env)))), e));
    for (sexp p = exp->cdr->cdr; p; p = p->cdr)
        r = save(eval(p->car, e));
    return lose(mark, r);
}

sexp letstarform(sexp exp, sexp env)
{
    sexp r;
    sexp* mark = psp;
    sexp e = save(env);
    for (sexp v = save(exp)->cdr->car; v; v = v->cdr)
        e = save(cons(save(cons(v->car->car, save(eval(v->car->cdr->car, e)))), e));
    for (sexp p = exp->cdr->cdr; p; p = p->cdr)
        r = save(eval(p->car, e));
    return lose(mark, r);
}

sexp letrecform(sexp exp, sexp env)
{
    sexp r;
    sexp* mark = psp;
    sexp e = save(env);
    for (sexp v = save(exp)->cdr->car; v; v = v->cdr)
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
    sexp* mark = psp;
    sexp e = save(env);
    // bind all the variables to their values
    for (sexp v = save(exp)->cdr->car; v; v = v->cdr)
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
        if (1 == arity(fun))
                return lose(mark, (*(Oneargp)((Funct*)fun)->funcp)(args ? args->car : 0));
        if (2 == arity(fun) && args->cdr)
            return lose(mark, (*(Twoargp)((Funct*)fun)->funcp)(args->car, args->cdr->car));
        if (3 == arity(fun) && args->cdr && args->cdr->cdr)
            return lose(mark, (*(Threeargp)((Funct*)fun)->funcp)(args->car, args->cdr->car, args->cdr->cdr->car));

        debug("missing args", fun);
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

        debug("bad closure", fun);
    }

    error("apply bad function");

    return 0;
}

sexp rationalform(sexp exp, sexp env)
{
    assertRational(exp);
    return exp;
}

sexp complexform(sexp exp, sexp env)
{
    assertComplex(exp);
    return exp;
}

/*
 * malformed constructs will fail without grace
 */
sexp eval(sexp p, sexp env)
{
    if (tracing)
        debug("eval", p);

    if (!p || f == p || t == p || isOther(p) && ATOM != evalType(p))
        return p;

    if (isAtom(p))
        return get(p, env);

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

enum
{
    NON_NUMERIC,
    INT_NUMERIC,
    INT_RATIONAL,
    FLO_NUMERIC,
    FLO_RECTANGULAR,
    INT_RECTANGULAR,
    INT_POLAR,
    FLO_POLAR
};

/*
 * read an atom, number or string from the input stream
 */
sexp scan(FILE* fin)
{
    sexp* mark = psp;
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
            for (int i = 0; character_table[i]; ++i)
                if (!strcmp(buffer, 1+character_table[i]))
                    return newcharacter(*character_table[i]);
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
        else if (INT_NUMERIC == rc && 'i' == c)
            rc = INT_RECTANGULAR;
        else if (FLO_NUMERIC == rc && 'i' == c)
            rc = FLO_RECTANGULAR;
        else if (INT_NUMERIC == rc && '@' == c)
            rc = INT_POLAR;
        else if (FLO_NUMERIC == rc && '@' == c)
            rc = FLO_POLAR;

        ungetc(c, fin);
        *p++ = 0;
        break;
    }

    if (FLO_RECTANGULAR == rc || INT_RECTANGULAR == rc)
    {
        char *nptr;
        c = getc(fin);
        double floater = strtod(buffer, &nptr);
        //printf("double %#.15g ", floater);
        if (nptr == strchr(buffer, '\0'))
            return lose(mark, newcomplex(0.0, floater));
    }

    if (FLO_POLAR == rc || INT_POLAR == rc)
    {
        char *nptr;
        c = getc(fin);
        double r = strtod(buffer, &nptr);
        //printf("double %#.15g ", floater);
        if (nptr == strchr(buffer, '\0')) {
            sexp tv = save(scan(fin));
            double theta = isFixnum(tv) ? (double)asFixnum(tv) : asFlonum(tv);
            double re = r * cos(theta);
            double im = r * sin(theta);
            return lose(mark, newcomplex(re, im));
        }
    }

    if (FLO_NUMERIC == rc)
    {
        char *nptr;
        double floater = strtod(buffer, &nptr);
        //printf("double %#.15g ", floater);
        if (nptr == strchr(buffer, '\0'))
            if ('-' == c || '+' == c) {
                if ('+' == c)
                    c = getc(fin);
                sexp im = save(scan(fin));
                im->cdr->car = newflonum(floater);
                return lose(mark, im);
            } else
                return newflonum(floater);
    }

    if (INT_RATIONAL == rc)
    {
        char *nptr;
        long fixer = strtol(buffer, &nptr, 10);
        //printf("long %ld\n", fixer);
        if (nptr == strchr(buffer, '\0'))
            if ('/' == c) {
                c = getc(fin);
                sexp dv = save(scan(fin));
                assertFixnum(dv);
                return lose(1, rational_reduce(fixer, asFixnum(dv)));
            } else
                return newfixnum(fixer);
    }

    if (INT_NUMERIC == rc)
    {
        char *nptr;
        long fixer = strtol(buffer, &nptr, 10);
        //printf("long %ld\n", fixer);
        if (nptr == strchr(buffer, '\0'))
            if ('-' == c || '+' == c) {
                if ('+' == c)
                    c = getc(fin);
                sexp iv = save(scan(fin));
                if (isFixnum(iv->cdr->cdr->car))
                    iv->cdr->cdr->car = newflonum((double)asFixnum(iv->cdr->cdr->car));
                iv->cdr->car = newflonum((double)fixer);
                return lose(1, iv);
            } else
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
    if (eofa == q)
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
        if (eofa == s)
            return 0;
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

    // allocate ports for stdin, stdout, stderr
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

    OutPort* r = (OutPort*)newcell();
    r->tags[0] = OTHER;
    r->tags[1] = OUTPORT;
    r->file = stderr;
    errport = (sexp)r;

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

    // set up all predefined atoms

    acosa           = atomize("acos");
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
    booleanpa       = atomize("boolean?");
    boundpa         = atomize("bound?");
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
    closurepa       = atomize("closure?");
    cloutporta      = atomize("close-output-port");
    commaat         = atomize(",@");
    comma           = atomize(",");
    complexa        = atomize("complex");
    complexpa       = atomize("complex?");
    cond            = atomize("cond");
    consa           = atomize("cons");
    cosa            = atomize("cos");
    curinporta      = atomize("current-input-port");
    curoutporta     = atomize("current-output-port");
    cyclicpa        = atomize("cyclic?");
    definea         = atomize("define");
    delaya          = atomize("delay");
    displaya        = atomize("display");
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
    nega            = atomize("neg");
    negativepa      = atomize("negative?");
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
    percent         = atomize("%");
    pipea           = atomize("|");
    plus            = atomize("+");
    positivepa      = atomize("positive?");
    powa            = atomize("pow");
    procedurepa     = atomize("procedure?");
    promisea        = atomize("promise");
    promisepa       = atomize("promise?");
    promiseva       = atomize("promise-value");
    qchar           = atomize("'");
    quasiquote      = atomize("quasiquote");
    quote           = atomize("quote");
    rationala       = atomize("rational");
    rationalpa      = atomize("rational?");
    rbracket        = atomize("]");
    reada           = atomize("read");
    readchara       = atomize("read-char");
    readypa         = atomize("char-ready?");
    realpa          = atomize("real?");
    reversea        = atomize("reverse");
    rounda          = atomize("round");
    rparen          = atomize(")");
    rsha            = atomize(">>");
    s2lista         = atomize("string->list");
    s2numa          = atomize("string->number");
    s2sya           = atomize("string->symbol");
    seta            = atomize("set!");
    setcara         = atomize("set-car!");
    setcdra         = atomize("set-cdr!");
    sina            = atomize("sin");
    slash           = atomize("/");
    spacea          = atomize("space");
    sqrta           = atomize("sqrt");
    star            = atomize("*");
    stderra         = atomize("stderr");
    stdina          = atomize("stdin");
    stdouta         = atomize("stdout");
    stringa         = atomize("string");
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
    substringa      = atomize("substring");
    sy2sa           = atomize("symbol->string");
    symbolpa        = atomize("symbol?");
    tana            = atomize("tan");
    t               = atomize("#t");
    tick            = atomize("`");
    tilde           = atomize("~");
    tracea          = atomize("trace");
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

    define(stderra, errport);
    define(stdina,  inport);
    define(stdouta, outport);

    // set the definitions (functions)
    define_funct(acosa,         1, (void*)acosff);
    define_funct(alphapa,       1, (void*)alphap);
    define_funct(ampera,        0, (void*)andf);
    define_funct(anglea,        1, (void*)angle);
    define_funct(appenda,       2, (void*)append);
    define_funct(applya,        2, (void*)apply);
    define_funct(asina,         1, (void*)asinff);
    define_funct(atana,         1, (void*)atanff);
    define_funct(atomsa,        0, (void*)atomsf);
    define_funct(booleanpa,     1, (void*)booleanp);
    define_funct(callwithina,   1, (void*)callwithin);
    define_funct(callwithouta,  1, (void*)callwithout);
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
    define_funct(closurepa,     1, (void*)closurep);
    define_funct(cloutporta,    1, (void*)cloutport);
    define_funct(complexpa,     1, (void*)complexp);
    define_funct(cosa,          1, (void*)cosff);
    define_funct(curinporta,    0, (void*)curinport);
    define_funct(curoutporta,   0, (void*)curoutport);
    define_funct(cyclicpa,      1, (void*)cyclicp);
    define_funct(displaya,      0, (void*)displayf);
    define_funct(downcasea,     1, (void*)downcase);
    define_funct(e2ia,          1, (void*)e2if);
    define_funct(eofobjp,       1, (void*)eofp);
    define_funct(evala,         2, (void*)eval);
    define_funct(exactpa,       1, (void*)exactp);
    define_funct(expa,          1, (void*)expff);
    define_funct(floora,        1, (void*)floorff);
    define_funct(forcea,        1, (void*)force);
    define_funct(forcedpa,      1, (void*)forcedp);
    define_funct(gca,           0, (void*)gc);
    define_funct(gcda,          2, (void*)gcdf);
    define_funct(i2ea,          1, (void*)i2ef);
    define_funct(inexactpa,     1, (void*)inexactp);
    define_funct(inportpa,      1, (void*)inportp);
    define_funct(int2chara,     1, (void*)int2char);
    define_funct(integerpa,     1, (void*)integerp);
    define_funct(lcma,          2, (void*)lcmf);
    define_funct(list2sa,       1, (void*)list2s);
    define_funct(list2vector,   1, (void*)list2vec);
    define_funct(listpa,        1, (void*)listp);
    define_funct(loada,         1, (void*)load);
    define_funct(loga,          1, (void*)logff);
    define_funct(lowercasepa,   1, (void*)lowercasep);
    define_funct(lsha,          2, (void*)lsh);
    define_funct(magnitudea,    1, (void*)magnitude);
    define_funct(makestringa,   0, (void*)makestring);
    define_funct(makevector,    0, (void*)makevec);
    define_funct(newlinea,      0, (void*)newlinef);
    define_funct(nullpa,        1, (void*)nullp);
    define_funct(num2stringa,   1, (void*)number2string);
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
    define_funct(rationalpa,    1, (void*)rationalp);
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
    define_funct(substringa,    0, (void*)substringf);
    define_funct(sy2sa,         1, (void*)sy2s);
    define_funct(symbolpa,      1, (void*)symbolp);
    define_funct(tana,          1, (void*)tanff);
    define_funct(tilde,         1, (void*)complement);
    define_funct(tracea,        1, (void*)trace);
    define_funct(truncatea,     1, (void*)truncateff);
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
    define_funct(writea,        0, (void*)writef);
    define_funct(writechara,    0, (void*)writechar);
    define_funct(xora,          0, (void*)xorf);
    
    // moved here because of frequent use
    define_funct(negativepa,    1, (void*)negativep);
    define_funct(positivepa,    1, (void*)positivep);
    define_funct(percent,       0, (void*)unimod);
    define_funct(slash,         0, (void*)unidiv);
    define_funct(nota,          1, (void*)isnot);
    define_funct(nega,          1, (void*)negf);
    define_funct(lta,           2, (void*)lt);
    define_funct(lea,           2, (void*)le);
    define_funct(gea,           2, (void*)ge);
    define_funct(gta,           2, (void*)gt);
    define_funct(eqa,           2, (void*)eqp);
    define_funct(eqna,          2, (void*)eqnp);
    define_funct(equalpa,       2, (void*)equalp);
    define_funct(eqva,          2, (void*)eqv);
    define_funct(plus,          0, (void*)uniadd);
    define_funct(star,          0, (void*)unimul);
    define_funct(minus,         0, (void*)unisub);
    define_funct(cara,          1, (void*)car);
    define_funct(cdra,          1, (void*)cdr);
    define_funct(consa,         2, (void*)cons);

    // set the definitions (special forms)
    define_form(begin,        beginform);
    define_form(boundpa,      boundp);
    define_form(cond,         condform);
    define_form(definea,      defineform);
    define_form(delaya,       delayform);
    define_form(doa,          doform);
    define_form(intenva,      intenvform);
    define_form(nulenva,      nulenvform);
    define_form(let,          letform);
    define_form(letstar,      letstarform);
    define_form(letrec,       letrecform);
    define_form(quasiquote,   quasiquoteform);
    define_form(seta,         setform);
    define_form(whilea,       whileform);
    define_form(anda,         andform);
    define_form(ora,          orform);
    define_form(ifa,          ifform);
    define_form(quote,        quoteform);
    define_form(lambda,       lambdaform);
    define_form(complexa,     complexform);
    define_form(rationala,    rationalform);

    load(newstring(newchunk("init.ss")));

    fixenvs(global);

    if (argc > 1)
    {
        load(newstring(newchunk(argv[1])));
        return 0;
    }

    killed = 0;

    s = (char*) sigsetjmp(the_jmpbuf, 1);
    if (s)
        printf("%s\n", s);

    // read evaluate display ...

    gc(atoms);

    for (;;)
    {
        if (psp > protect)
            if ((long)(psp-protect) > 1)
                printf("%ld items remain on protection stack\n", (long)(psp-protect));
            else
                printf("one item remains on protection stack\n");
        total = 0;
        collected = 0;
        printf("> ");
        fflush(stdout);
        sexp e = read(stdin, 0);
        if (eofa == e)
            break;
        killed = 0;
        sexp v = eval(e, global);
        {
            std::stringstream s;
            ugly ugly(s);
            s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
            std::set<sexp> seenSet;
            display(s, v, seenSet, ugly, false);
            fwrite(s.str().c_str(), 1, s.str().length(), stdout);
            if (voida != v)
                putchar('\n');
        }
    }
    return 0;
}

