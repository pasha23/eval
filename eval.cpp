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

sexp define(sexp p, sexp r);
sexp eval(sexp p, sexp env);
sexp apply(sexp fun, sexp args);
sexp read(FILE* fin, int level);
void debug(const char* label, sexp exp);

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

sexp closure, comma, commaat, complex, dot, elsea, eof, f, lambda, lbracket;
sexp lparen, minus, nil, promise, qchar, quasiquote, quote, rational, rbracket;
sexp rparen, stderra, stdina, stdouta, t, tick, unquote, unquotesplicing, voida;

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
           closure == p->car &&                         // (closure
           isCons(p = p->cdr) && p->car &&              //  exp
           isCons(p = p->cdr) && p->car &&              //  env)
           !p->cdr;
}

// closure?
sexp closurep(sexp s) { return isClosure(s) ? t : 0; }

bool isPromise(sexp p)
{
    return isCons(p) && promise == p->car &&            // (promise
           isCons(p = p->cdr) &&                        //  forced
           isCons(p = p->cdr) &&                        //  value
           isCons(p = p->cdr) &&                        //  exp
           isCons(p = p->cdr) &&                        //  env)
          !p->cdr;
}

// promise?
sexp promisep(sexp s) { return isPromise(s) ? t : 0; }

bool isRational(sexp p)
{
    return isCons(p) && rational == p->car &&          // (rational
           isCons(p = p->cdr) && isFixnum(p->car) &&   //  numerator
           isCons(p = p->cdr) && isFixnum(p->car) &&   //  denominator
           !p->cdr;                                    // )
}

// rational?
sexp rationalp(sexp s) { return isRational(s) ? t : 0; }

bool isComplex(sexp p)
{
    return isCons(p) && complex == p->car &&            // (complex
           isCons(p = p->cdr) && isFlonum(p->car) &&    //  real-part
           isCons(p = p->cdr) && isFlonum(p->car) &&    //  imag-part
           !p->cdr;                                     // )
}

// complex?
sexp complexp(sexp s) { return isComplex(s) ? t : 0; }

jmp_buf the_jmpbuf;

sexp tracing = 0;       // trace everything
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

void deleteinport(sexp v)
{
    FILE* f = ((InPort*)v)->file;
    if (f)
    {
        ((InPort*)v)->file = 0;
        fclose(f);
    }
}

void deleteoutport(sexp v)
{
    FILE* f = ((OutPort*)v)->file;
    if (f)
    {
        ((OutPort*)v)->file = 0;
        fclose(f);
    }
}

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
void assertRational(sexp s)    { if (!isRational(s))    error("not rational"); }
void assertInPort(sexp s)      { if (!isInPort(s))      error("not an input port"); }
void assertOutPort(sexp s)     { if (!isOutPort(s))     error("not an output port"); }
void assertString(sexp s)      { if (!isString(s))      error("not a string"); }

void assertFlonum(sexp s)
{
    if (!isFlonum(s) && !isFixnum(s) && !isRational(s))
        error("not a real number");
}

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
    assert(name);
    Form* p = (Form*)save(newcell());
    p->tags[0] = OTHER;
    p->tags[1] = FORM;
    p->formp = f;
    define(name, (sexp)p);
    return lose(1, name);
}

sexp define_funct(sexp name, int arity, void* f)
{
    assert(name);
    Funct* p = (Funct*)save(newcell());
    p->tags[0] = OTHER;
    p->tags[1] = FUNCT;
    p->tags[2] = arity;
    p->funcp = f;
    define(name, (sexp)p);
    return lose(1, name);
}

// cons
sexp cons(sexp car, sexp cdr)
{
    save(car);
    save(cdr);
    sexp p = newcell();
    p->car = car;
    p->cdr = cdr;
    return lose(2, p);
}

// car
sexp car(sexp p)
{
    if (!isCons(p))
        error("error: car of non-pair");
    return p->car;
}

// cdr
sexp cdr(sexp p)
{
    if (!isCons(p))
        error("error: cdr of non-pair");
    return p->cdr;
}

// set-car!
sexp setcarf(sexp p, sexp q)
{
    if (!isCons(p))
        error("error: set-car! of non-pair");
    p->car = q;
    return voida;
}

// set-cdr!
sexp setcdrf(sexp p, sexp q)
{
    if (!isCons(p))
        error("error: set-cdr! of non-pair");
    p->cdr = q;
    return voida;
}

// and
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

// or
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

// trace
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

double rat2real(sexp x)
{
    return (double)asFixnum(x->cdr->car) / (double)asFixnum(x->cdr->cdr->car);
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

    if (isFixnum(p))
        return (double) asFixnum(p);

    if (isRational(p))
        return rat2real(p);

    error("asFlonum: not a flonum");
}

// negative?
sexp negativep(sexp x)
{
    if (isFixnum(x)) return asFixnum(x) < 0 ? t : 0;
    if (isFlonum(x)) return asFlonum(x) < 0.0 ? t : 0;
    if (isRational(x))
        return asFixnum(x->cdr->car) < 0 && asFixnum(x->cdr->cdr->car) > 0 ||
               asFixnum(x->cdr->car) > 0 && asFixnum(x->cdr->cdr->car) < 0 ? t : 0;
    error("negative? needs a real number");
}

// positive?
sexp positivep(sexp x)
{
    if (isFixnum(x)) return asFixnum(x) > 0 ? t : 0;
    if (isFlonum(x)) return asFlonum(x) > 0.0 ? t : 0;
    if (isRational(x))
        return asFixnum(x->cdr->car) > 0 && asFixnum(x->cdr->cdr->car) > 0 ||
               asFixnum(x->cdr->car) < 0 && asFixnum(x->cdr->cdr->car) < 0 ? t : 0;
    error("positive? needs a real number");
}

// boolean?
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
            return (double)asFixnum(x) < asFlonum(y);
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
            return (double)asFixnum(x) <= asFlonum(y);
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

// <
sexp lt(sexp x, sexp y)
{
    return cmplt(x, y) ? t : 0;
}

// <=
sexp le(sexp x, sexp y)
{
    return cmple(x, y) ? t : 0;
}

// >=
sexp ge(sexp x, sexp y)
{
    return cmplt(x, y) ? 0 : t;
}

// >
sexp gt(sexp x, sexp y)
{
    return cmple(x, y) ? 0 : t;
}

sexp newrational(long n, long d)
{
    return lose(4, cons(rational, save(cons(save(newfixnum(n)), save(cons(save(newfixnum(d)), 0))))));
}

sexp newcomplex(double re, double im)
{
    return lose(4, cons(complex, save(cons(save(newflonum(re)), save(cons(save(newflonum(im)), 0))))));
}

double realpart(sexp x)
{
    assertComplex(x); return asFlonum(x->cdr->car);
}

double imagpart(sexp x)
{
    assertComplex(x); return asFlonum(x->cdr->cdr->car);
}

// magnitude
sexp magnitude(sexp z)
{
    assertComplex(z);
    return newflonum(sqrt(asFlonum(z->cdr->car)      * asFlonum(z->cdr->car) +
                          asFlonum(z->cdr->cdr->car) * asFlonum(z->cdr->cdr->car)));
}

// angle
sexp angle(sexp z)
{
    assertComplex(z);
    return newflonum(atan2(asFlonum(z->cdr->cdr->car), asFlonum(z->cdr->car)));
}

long gcd(long x, long y)
{
    return y ? gcd(y, x % y) : x;
}

// gcd
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

// lcm
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

// +
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

// -
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

// - x
// x - y
// x - y - z - w ...
sexp unisub(sexp l)
{
    if (!l)
        return newfixnum(0);
    if (!l->cdr)
        return negf(l->car);
    return lose(2, uniadd(cons(l->car, save(cons(negf(save(uniadd(l->cdr))), 0)))));
}

// *
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

// /
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

// %
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
sexp sinff(sexp x)     { assertFlonum(x); return newflonum(sin(asFlonum(x)));   } // sin
sexp cosff(sexp x)     { assertFlonum(x); return newflonum(cos(asFlonum(x)));   } // cos
sexp tanff(sexp x)     { assertFlonum(x); return newflonum(tan(asFlonum(x)));   } // tan
sexp expff(sexp x)     { assertFlonum(x); return newflonum(exp(asFlonum(x)));   } // exp
sexp logff(sexp x)     { assertFlonum(x); return newflonum(log(asFlonum(x)));   } // log
sexp asinff(sexp x)    { assertFlonum(x); return newflonum(asin(asFlonum(x)));  } // asin
sexp acosff(sexp x)    { assertFlonum(x); return newflonum(acos(asFlonum(x)));  } // acos
sexp atanff(sexp x)    { assertFlonum(x); return newflonum(atan(asFlonum(x)));  } // atan
sexp sqrtff(sexp x)    { assertFlonum(x); return newflonum(sqrt(asFlonum(x)));  } // sqrt
sexp floorff(sexp x)   { assertFlonum(x); return newflonum(floor(asFlonum(x))); } // floor
sexp roundff(sexp x)   { assertFlonum(x); return newflonum(round(asFlonum(x))); } // round
sexp ceilingff(sexp x) { assertFlonum(x); return newflonum(ceil(asFlonum(x)));  } // ceiling

// pow
sexp powff(sexp x, sexp y)
{
    assertFlonum(x); assertFlonum(y); return newflonum(pow(asFlonum(x), asFlonum(y)));
}

// truncate
sexp truncateff(sexp x)
{
    assertFlonum(x); return newflonum(asFlonum(x) < 0 ? ceil(asFlonum(x)) : floor(asFlonum(x)));
}

// exact?
sexp exactp(sexp x) { return isFixnum(x) ? t : 0; }

// integer?
sexp integerp(sexp x) { return isFixnum(x) ? t : isFlonum(x) && (long)asFlonum(x) == asFlonum(x) ? t : 0; }

// inexact?
sexp inexactp(sexp x) { return isFlonum(x) ? t : 0; }

// real?
sexp realp(sexp x) { return (isFixnum(x) || isFlonum(x)) ? t : 0; }

// inexact->exact
sexp i2ef(sexp x) { assertFlonum(x); return newfixnum((long)asFlonum(x)); }

// exact->inexact
sexp e2if(sexp x) { assertFixnum(x); return newflonum((double)asFixnum(x)); }

// <<
sexp lsh(sexp x, sexp y) { assertFixnum(x); assertFixnum(y); return newfixnum(asFixnum(x) << asFixnum(y)); }

// >>
sexp rsh(sexp x, sexp y) { assertFixnum(x); assertFixnum(y); return newfixnum(asFixnum(x) >> asFixnum(y)); }

// not
sexp isnot(sexp x) { return x ? 0 : t; }

// null?
sexp nullp(sexp x) { return x ? 0 : t; }

// list?
sexp listp(sexp x) { return !isCons(x) ? 0 : listp(x->cdr) ? t : 0; }

// atom?
sexp atomp(sexp x) { return isAtom(x) ? t : 0; }

// pair?
sexp pairp(sexp x) { return isCons(x) ? t : 0; }

// number?
sexp numberp(sexp x) { return isFixnum(x) || isFlonum(x) ? t : 0; }

// string?
sexp stringp(sexp x) { return isString(x) ? t : 0; }

// symbol?
sexp symbolp(sexp x) { return isAtom(x) ? t : 0; }

// procedure?
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

// string-length
sexp stringlengthf(sexp s)
{
    assertString(s);
    return newfixnum(slen(s));
}

// index a character in a string
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

const char* escapes[] = { "\007a", "\010b", "\011t", "\012n", "\015r", "\"\"", "\\\\", 0 };

char decodeEscape(char c)
{
    for (const char** p = escapes; *p; ++p)
        if ((*p)[1] == c)
            return (*p)[0];
    return c;
}

char encodeEscape(char c)
{
    for (const char** p = escapes; *p; ++p)
        if ((*p)[0] == c)
            return (*p)[1];
    return c;
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

        if ('\\' == c)
            c = decodeEscape(*t++);

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

// number->string
sexp number2string(sexp exp)
{
    std::stringstream s;
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    num2string(s, exp);
    return lose(1, newstring(save(newchunk(s.str().c_str()))));
}

// make-string
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

// copy characters from a String or Atom into a buffer
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

// string-copy
sexp stringcopyf(sexp s)
{
    assertString(s);

    int len = slen(s)+1;
    return lose(1, newstring(save(newchunk(sstr((char*)alloca(len), len, s)))));
}

// string-append
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

// string-fill
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
    fclose(((InPort*)p)->file);
    ((InPort*)p)->file = 0;
}

// close-output-port
sexp cloutport(sexp p)
{
    assertOutPort(p);
    if (outport == p)
        outport = 0;
    fclose(((OutPort*)p)->file);
    ((OutPort*)p)->file = 0;
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
sexp callwithout(sexp p, sexp f)
{
    sexp oup = openout(p);
    sexp q = apply(f, cons(oup, 0));
    cloutport(oup);
    return q;
}

// vector?
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

// make-vector
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

// list->vector
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

// vector->list
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

// vector-fill
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

// vector-length
sexp veclength(sexp vector)
{
    assertVector(vector);
    save(vector);
    return lose(1, newfixnum(((Vector*)vector)->l));
}

// vector-ref
sexp vecref(sexp vector, sexp index)
{
    assertFixnum(index);
    assertVector(vector);
    return ((Vector*)vector)->e[asFixnum(index)];
}

// (vector e0 e1 e2 ...)
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

// vector-set
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

// char-alphabetic?
sexp alphap(sexp c) { return isChar(c) && isalpha(((Char*)c)->ch) ? t : 0; }

// char->integer
sexp char2int(sexp c) { assertChar(c); return  newfixnum(((Char*)c)->ch); }

// char-ci=?
sexp charcieq(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) == tolower(((Char*)q)->ch) ? t : 0; }

// char-ci>=?
sexp charcige(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) >= tolower(((Char*)q)->ch) ? t : 0; }

// char-ci>?
sexp charcigt(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) >  tolower(((Char*)q)->ch) ? t : 0; }

// char-ci<=?
sexp charcile(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) <= tolower(((Char*)q)->ch) ? t : 0; }

// char-ci<?
sexp charcilt(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) <  tolower(((Char*)q)->ch) ? t : 0; }

// char=?
sexp chareq(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch == ((Char*)q)->ch ? t : 0; }

// char>=?
sexp charge(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch >= ((Char*)q)->ch ? t : 0; }

// char>?
sexp chargt(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch >  ((Char*)q)->ch ? t : 0; }

// char<=?
sexp charle(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch <= ((Char*)q)->ch ? t : 0; }

// char<?
sexp charlt(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch <  ((Char*)q)->ch ? t : 0; }

// character?
sexp charp(sexp c) { return isChar(c) ? t : 0; }

// char-downcase
sexp downcase(sexp c) { assertChar(c); return newcharacter(tolower(((Char*)c)->ch)); }

// integer->char
sexp int2char(sexp c) { assertFixnum(c); return newcharacter(asFixnum(c)); }

// char-lowercase?
sexp lowercasep(sexp c) { return isChar(c) && islower(((Char*)c)->ch) ? t : 0; }

// char-numeric?
sexp numericp(sexp c) { return isChar(c) && isdigit(((Char*)c)->ch) ? t : 0; }

// char-upcase
sexp upcase(sexp c) { assertChar(c); return newcharacter(toupper(((Char*)c)->ch)); }

// char-uppercase?
sexp uppercasep(sexp c) { return isChar(c) && isupper(((Char*)c)->ch) ? t : 0; }

// char-whitespace?
sexp whitespacep(sexp c) { return isChar(c) && isspace(((Char*)c)->ch) ? t : 0; }

// copy the original termios then modify it for cbreak style input
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

// char-ready?
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

// read-char
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

// peek-char
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

// write-char
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

// string<=?
sexp stringlef(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) <= 0 ? t : 0; }

// string<?
sexp stringltf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) <  0 ? t : 0; }

// string=?
sexp stringeqf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) == 0 ? t : 0; }

// string>=?
sexp stringgef(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) >= 0 ? t : 0; }

// string>?
sexp stringgtf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) >  0 ? t : 0; }

// string-ci-<=?
sexp stringcilef(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) <= 0 ? t : 0; }

// string-ci<?
sexp stringciltf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) <  0 ? t : 0; }

// string-ci=?
sexp stringcieqf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) == 0 ? t : 0; }

// string-ci>=?
sexp stringcigef(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) >= 0 ? t : 0; }

// string-ci>?
sexp stringcigtf(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) >  0 ? t : 0; }

// string-ref
sexp stringreff(sexp s, sexp i)
{
    assertString(s);
    assertFixnum(i);

    char* p = sref(s, asFixnum(i));
    if (!p)
        error("string-ref: out of bounds");

    return newcharacter(*p);
}

// string-set!
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

// substring
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

// reverse
sexp reverse(sexp x) { sexp t = 0; while (isCons(x)) { t = cons(car(x), t); x = x->cdr; } return t; }

// eq?
sexp eqp(sexp x, sexp y) { return x == y ? t : 0; }

// =
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

// all arguments must be fixnums for these logical operations
sexp allfixnums(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
        if (!isFixnum(p->car))
            return 0;
    return t;
}

// &
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

// |
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

// ^
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

// delay
sexp delayform(sexp exp, sexp env)
{
    return lose(4, cons(promise,
                        save(cons(0,
                        save(cons(0,
                        save(cons(exp->cdr->car,
                        save(cons(env, 0))))))))));
}

// force
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

// forced?
sexp forcedp(sexp p)
{
    if (!isPromise(p))
        error("promise-forced?: not a promise");
    return p->cdr->car;
}

// promise-value
sexp promisev(sexp p)
{
    if (!isPromise(p))
        error("promise-value: not a promise");
    if (p->cdr->car)
        return p->cdr->cdr->car;
    else
        error("promise not forced yet");
}

// load
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
            if (eof == input)
                break;
            if (tracing)
                debug("load", input);
            eval(input, global);
        }
        fclose(fin);
        return t;
    }
    return 0;
}

// space
sexp spacef(sexp args)
{
    sexp port = args ? args->car : outport;
    assertOutPort(port);
    fputc(' ', (((OutPort*)port)->file));
    return voida;
}

// newline
sexp newlinef(sexp args)
{
    sexp port = args ? args->car : outport;
    assertOutPort(port);
    fputc('\n', (((OutPort*)port)->file));
    return voida;
}

// eof?
sexp eofp(sexp a)
{
    return eof == a ? t : 0;
}

// display
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

// write
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

std::stringstream& displayChunks(std::stringstream& s, sexp exp, bool atom, bool write)
{
    if (write && !atom)
        s << '"';
    while (exp)
    {
        Chunk* t = (Chunk*)(exp->car);
        for (int i = 0; i < sizeof(t->text); ++i)
        {
            char c = t->text[i];
            if (!c)
                break;
            if (write && strchr("\007\b\t\n\r\"\\", c))
                s << '\\' << encodeEscape(c);
            else
                s << c;
        }
        exp = exp->cdr;
    }
    if (write && !atom)
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

bool cyclic(sexp exp)
{
    std::set<sexp> seenSet;
    return cyclic(seenSet, exp);
}

// cyclic?
sexp cyclicp(sexp x) { return cyclic(x) ? t : 0; }

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
        if (safe(seenSet, vv->e[i]))
            display(s, vv->e[i], seenSet, ugly, write);
        if (i < vv->l-1)
        {
            s << ",";
            if (isCons(vv->e[i]) || isVector(vv->e[i]))
                ugly.wrapmajor();
            else
                ugly.wrapminor();
        }
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

std::stringstream& displayAtom(std::stringstream& s, sexp exp, bool write)
{
    displayChunks(s, ((Atom*)exp)->chunks, true, write);
}

std::stringstream& displayString(std::stringstream& s, sexp exp, bool write)
{
    displayChunks(s, ((Atom*)exp)->chunks, false, write);
}

// used for displaying functions, forms. and closures by name
sexp getName(sexp exp)
{
    for (sexp p = global; p; p = p->cdr)
        if (exp == p->car->cdr)
            return p->car->car;
    return 0;
}

std::stringstream& displayFunction(std::stringstream& s, sexp exp, bool write)
{
    s << "#<function" << arity(exp) << '@';
    sexp name = getName(exp);
    if (name)
        displayAtom(s, name, write);
    else
        s << std::hex << (void*)exp << std::dec;
    s << '>';
    return s;
}

std::stringstream& displayNamed(std::stringstream& s, const char *kind, sexp exp, bool write)
{
    s << "#<" << kind << '@';
    sexp name = getName(exp);
    if (name)
        displayAtom(s, name, write);
    else
        s << std::hex << (void*)exp << std::dec;
    s << '>';
    return s;
}

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
    } else if (isClosure(exp)) {
        displayNamed(s, "closure", exp, write);
    } else if (isPromise(exp))
        displayNamed(s, "promise", exp, write);
    else if (isCons(exp)) {
        if (safe(seenSet, exp))
            displayList(s, exp, seenSet, ugly, write);
    } else if (isString(exp))
        displayString(s, exp, write);
    else if (isAtom(exp))
        displayAtom(s, exp, write);
    else if (isVector(exp) && safe(seenSet, exp))
        displayVector(s, exp, seenSet, ugly, write);
    else if (isFunct(exp)) {
        displayFunction(s, exp, write);
    } else if (isForm(exp)) {
        displayNamed(s, "form", exp, write);
    } else if (isInPort(exp))
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

// usual way to see what is happening
void debug(const char *label, sexp exp)
{
    std::stringstream s;
    ugly ugly(s);
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    std::set<sexp> seenSet;
    s << label << ": ";
    if (voida == exp)
        s << "void";
    else
        display(s, exp, seenSet, ugly, true);
    s << '\n';
    fwrite(s.str().c_str(), 1, s.str().length(), stdout);
}

// every atom must be unique and saved in the atoms list
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
sexp str2sym(sexp x) { assertString(x); return intern(newatom(((String*)x)->chunks)); }

// symbol->string
sexp sym2str(sexp x) { assertAtom(x); return newstring(((Atom*)x)->chunks); }

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

// symbol->list
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

// list->string
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

// string
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

// eqv?
sexp eqv(sexp x, sexp y)
{
    std::set<sexp> seenx;
    std::set<sexp> seeny;
    return eqvb(seenx, seeny, x, y) ? t : 0;
}

// equal?
sexp equalp(sexp x, sexp y)
{
    std::set<sexp> seenx;
    std::set<sexp> seeny;
    return eqvb(seenx, seeny, x, y) ? t : 0;
}

// update all the closures in an environment so they reference
// that environment instead of earlier ones for init.ss
void fixenvs(sexp env)
{
    for (sexp f = env; f; f = f->cdr)
        if (isClosure(f->car->cdr))
            f->car->cdr->cdr->cdr->car = env;
}

// define
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

// bound?
sexp boundp(sexp p, sexp env)
{
    for (sexp q = env; q; q = q->cdr)
        if (q->car && p->cdr->car == q->car->car)
            return t;
    return 0;
}

// retrieve the value of a variable in an environment
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

// set!
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

// evaluate a list of arguments in an environment
sexp evlis(sexp p, sexp env)
{
    if (!p)
        return 0;
    return lose(4, cons(save(eval(p->car, env)), save(evlis(save(p)->cdr, save(env)))));
}

// associate a list of formal parameters and actual parameters in an environment
sexp assoc(sexp formals, sexp actuals, sexp env)
{
    if (!actuals || !formals)
        return env;
    return lose(5, cons(save(cons(formals->car, actuals->car)),
                       save(assoc(save(formals)->cdr, save(actuals)->cdr, save(env)))));
}

// null-environment
sexp nulenvform(sexp exp, sexp env)
{
    return global;
}

// interaction-environment
sexp intenvform(sexp exp, sexp env)
{
    return env;
}

// begin
sexp beginform(sexp exp, sexp env)
{
    save(env);
    sexp v = 0;
    for (sexp p = save(exp)->cdr; p; p = p->cdr)
        v = eval(p->car, env);
    return lose(2, v);
}

// while
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

// lambda creates a closure
sexp lambdaform(sexp exp, sexp env)
{
    return lose(4, cons(closure, save(cons(save(exp), save(cons(save(env), 0))))));
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

// atoms
sexp atomsf(sexp args)
{
    return atoms;
}

// quote
sexp quoteform(sexp exp, sexp env)
{
    return exp->cdr->car;
}

// unquote
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

// quasiquote
sexp quasiquoteform(sexp exp, sexp env)
{
    return unquoteform(exp->cdr->car, env);
}

// read
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
    if (!exp->cdr)
        error("if: missing predicate");
    if (!exp->cdr->cdr)
        error("if: missing consequent");
    if (exp->cdr->cdr->cdr)
        return lose(2, eval(save(exp)->cdr->car, save(env)) ?
                              eval(exp->cdr->cdr->car, env) : eval(exp->cdr->cdr->cdr->car, env));
    else
        return lose(2, eval(save(exp)->cdr->car, save(env)) ? eval(exp->cdr->cdr->car, env) : voida);
}

/*
 * (set! name value) alters an existing binding
 */
sexp setform(sexp exp, sexp env)
{
    return lose(3, set(exp->cdr->car, save(eval(save(exp)->cdr->cdr->car, env)), save(env)));
}

// (let ((var val) (var val) ..) body )
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

// (let* ((var val) (var val) ..) body )
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

// (letrec ((var val) (var val) ..) body )
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

// apply
sexp apply(sexp fun, sexp args)
{
    sexp* mark = psp;

    save(fun);
    save(args);

    if (tracing)
    {
        debug("apply-fun", fun);
        debug("apply-args", args);
    }

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

    debug("apply function", fun);

    error("apply bad function");

    return 0;
}

// (rational numerator denominator)
sexp rationalform(sexp exp, sexp env)
{
    assertRational(exp);
    return exp;
}

// (complex real imaginary)
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

        if ('\\' == c)
            c = decodeEscape(getc(fin));

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

// ignore white space and comments
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
sexp scan(FILE* fin);

sexp scans(FILE* fin)
{
    sexp* mark = psp;
    char buffer[256];
    char *p = buffer;
    char *pend = buffer + sizeof(buffer) - 1;

    char c = whitespace(fin, getc(fin));

    if (c < 0)
        return eof;

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
        if (nptr == strchr(buffer, '\0'))
            return lose(mark, newcomplex(0.0, floater));
    }

    if (FLO_POLAR == rc || INT_POLAR == rc)
    {
        char *nptr;
        c = getc(fin);
        double r = strtod(buffer, &nptr);
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

// stub to enable tracing of scans()
sexp scan(FILE* fin)
{
    sexp r = scans(fin);
    if (tracing)
        debug("scan", r);
    return r;
}

// finish reading a list
sexp readTail(FILE* fin, int level)
{
    sexp q = read(fin, level);
    if (rparen == q)
        return 0;
    if (eof == q)
        return 0;
    save(q);
    sexp r = save(readTail(fin, level));
    return lose(2, r && dot == r->car ? cons(q, r->cdr->car) : cons(q, r));
}

// finish reading a vector
sexp readVector(FILE* fin, int level)
{
    sexp q = 0;
    sexp* mark = psp;
    for (;;)
    {
        sexp s = save(read(fin, level));
        if (eof == s)
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
    if (eof == p)
        return p;
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

// construct an atom and keep a unique copy
sexp atomize(const char *s)
{
    return lose(2, intern(save(newatom(save(newchunk(s))))));
}

// the first interrupt will stop everything. the second will exit.
void intr_handler(int sig, siginfo_t *si, void *ctx)
{
    if (killed++)
        exit(0);
    if (SIGINT == sig)
        error("SIGINT");
}

// do a traceback upon a segmentation violation
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

    closure         = atomize("closure");
    commaat         = atomize(",@");
    comma           = atomize(",");
    complex         = atomize("complex");
    dot             = atomize(".");
    elsea           = atomize("else");
    eof             = atomize("#eof");
    f               = atomize("#f");
    lambda          = atomize("lambda");
    lbracket        = atomize("[");
    lparen          = atomize("(");
    minus           = atomize("-");
    nil             = atomize("#f");
    promise         = atomize("promise");
    qchar           = atomize("'");
    quasiquote      = atomize("quasiquote");
    quote           = atomize("quote");
    rational        = atomize("rational");
    rbracket        = atomize("]");
    rparen          = atomize(")");
    t               = atomize("#t");
    tick            = atomize("`");
    unquote         = atomize("unquote");
    unquotesplicing = atomize("unquote-splicing");
    voida           = atomize("");

    define(stderra  = atomize("stderr"), errport);
    define(stdina   = atomize("stdin"),  inport);
    define(stdouta  = atomize("stdout"), outport);

    define_funct(atomize("string->symbol"), 1, (void*)str2sym);
    define_funct(atomize("acos"), 1, (void*)acosff);
    define_funct(atomize("atom?"), 1, (void*)atomp);
    define_funct(atomize("char-alphabetic?"), 1, (void*)alphap);
    define_funct(atomize("&"), 0, (void*)andf);
    define_funct(atomize("angle"), 1, (void*)angle);
    define_funct(atomize("append"), 2, (void*)append);
    define_funct(atomize("apply"), 2, (void*)apply);
    define_funct(atomize("asin"), 1, (void*)asinff);
    define_funct(atomize("atan"), 1, (void*)atanff);
    define_funct(atomize("atoms"), 0, (void*)atomsf);
    define_funct(atomize("boolean?"), 1, (void*)booleanp);
    define_funct(atomize("call-with-input-file"), 2, (void*)callwithin);
    define_funct(atomize("call-with-output-file"), 2, (void*)callwithout);
    define_funct(atomize("ceiling"), 1, (void*)ceilingff);
    define_funct(atomize("char->integer"), 1, (void*)char2int);
    define_funct(atomize("char-ci=?"), 2, (void*)charcieq);
    define_funct(atomize("char-ci>=?"), 2, (void*)charcige);
    define_funct(atomize("char-ci>?"), 2, (void*)charcigt);
    define_funct(atomize("char-ci<=?"), 2, (void*)charcile);
    define_funct(atomize("char-ci<?"), 2, (void*)charcilt);
    define_funct(atomize("char=?"), 2, (void*)chareq);
    define_funct(atomize("char>=?"), 2, (void*)charge);
    define_funct(atomize("char>?"), 2, (void*)chargt);
    define_funct(atomize("char<=?"), 2, (void*)charle);
    define_funct(atomize("char<?"), 2, (void*)charlt);
    define_funct(atomize("char?"), 1, (void*)charp);
    define_funct(atomize("close-input-port"), 1, (void*)clinport);
    define_funct(atomize("closure?"), 1, (void*)closurep);
    define_funct(atomize("close-output-port"), 1, (void*)cloutport);
    define_funct(atomize("complex?"), 1, (void*)complexp);
    define_funct(atomize("cos"), 1, (void*)cosff);
    define_funct(atomize("current-input-port"), 0, (void*)curinport);
    define_funct(atomize("current-output-port"), 0, (void*)curoutport);
    define_funct(atomize("cyclic?"), 1, (void*)cyclicp);
    define_funct(atomize("display"), 0, (void*)displayf);
    define_funct(atomize("char-downcase"), 1, (void*)downcase);
    define_funct(atomize("exact->inexact"), 1, (void*)e2if);
    define_funct(atomize("eof-object?"), 1, (void*)eofp);
    define_funct(atomize("eval"), 2, (void*)eval);
    define_funct(atomize("exact?"), 1, (void*)exactp);
    define_funct(atomize("exp"), 1, (void*)expff);
    define_funct(atomize("floor"), 1, (void*)floorff);
    define_funct(atomize("force"), 1, (void*)force);
    define_funct(atomize("promise-forced?"), 1, (void*)forcedp);
    define_funct(atomize("gc"), 0, (void*)gc);
    define_funct(atomize("gcd"), 2, (void*)gcdf);
    define_funct(atomize("inexact->exact"), 1, (void*)i2ef);
    define_funct(atomize("inexact?"), 1, (void*)inexactp);
    define_funct(atomize("input-port?"), 1, (void*)inportp);
    define_funct(atomize("integer->char"), 1, (void*)int2char);
    define_funct(atomize("integer?"), 1, (void*)integerp);
    define_funct(atomize("lcm"), 2, (void*)lcmf);
    define_funct(atomize("list->string"), 1, (void*)list2s);
    define_funct(atomize("list->vector"), 1, (void*)list2vec);
    define_funct(atomize("list?"), 1, (void*)listp);
    define_funct(atomize("load"), 1, (void*)load);
    define_funct(atomize("log"), 1, (void*)logff);
    define_funct(atomize("char-lower-case?"), 1, (void*)lowercasep);
    define_funct(atomize("<<"), 2, (void*)lsh);
    define_funct(atomize("magnitude"), 1, (void*)magnitude);
    define_funct(atomize("make-string"), 0, (void*)makestring);
    define_funct(atomize("make-vector"), 0, (void*)makevec);
    define_funct(atomize("newline"), 0, (void*)newlinef);
    define_funct(atomize("number->string"), 1, (void*)number2string);
    define_funct(atomize("number?"), 1, (void*)numberp);
    define_funct(atomize("char-numeric?"), 1, (void*)numericp);
    define_funct(atomize("open-input-file"), 1, (void*)openin);
    define_funct(atomize("open-output-file"), 1, (void*)openout);
    define_funct(atomize("output-port?"), 1, (void*)outportp);
    define_funct(atomize("peek-char"), 0, (void*)peekchar);
    define_funct(atomize("|"), 0, (void*)orf);
    define_funct(atomize("pow"), 2, (void*)powff);
    define_funct(atomize("procedure?"), 1, (void*)procedurep);
    define_funct(atomize("promise?"), 1, (void*)promisep);
    define_funct(atomize("promise-value"), 1, (void*)promisev);
    define_funct(atomize("rational?"), 1, (void*)rationalp);
    define_funct(atomize("read"), 0, (void*)readf);
    define_funct(atomize("read-char"), 0, (void*)readchar);
    define_funct(atomize("char-ready?"), 0, (void*)readyp);
    define_funct(atomize("real?"), 1, (void*)realp);
    define_funct(atomize("reverse"), 1, (void*)reverse);
    define_funct(atomize("round"), 1, (void*)roundff);
    define_funct(atomize(">>"), 2, (void*)rsh);
    define_funct(atomize("string->list"), 1, (void*)s2list);
    define_funct(atomize("string->number"), 1, (void*)s2num);
    define_funct(atomize("set-car!"), 2, (void*)setcarf);
    define_funct(atomize("set-cdr!"), 2, (void*)setcdrf);
    define_funct(atomize("sin"), 1, (void*)sinff);
    define_funct(atomize("space"), 0, (void*)spacef);
    define_funct(atomize("sqrt"), 1, (void*)sqrtff);
    define_funct(atomize("string"), 0, (void*)string);
    define_funct(atomize("string-append"), 2, (void*)stringappend);
    define_funct(atomize("string-ci=?"), 2, (void*)stringcieqf);
    define_funct(atomize("string-ci>=?"), 2, (void*)stringcigef);
    define_funct(atomize("string-ci>?"), 2, (void*)stringcigtf);
    define_funct(atomize("string-ci<=?"), 2, (void*)stringcilef);
    define_funct(atomize("string-ci<?"), 2, (void*)stringciltf);
    define_funct(atomize("string-copy"), 1, (void*)stringcopyf);
    define_funct(atomize("string=?"), 2, (void*)stringeqf);
    define_funct(atomize("string-fill!"), 2, (void*)stringfillf);
    define_funct(atomize("string>=?"), 2, (void*)stringgef);
    define_funct(atomize("string>?"), 2, (void*)stringgtf);
    define_funct(atomize("string<=?"), 2, (void*)stringlef);
    define_funct(atomize("string-length"), 1, (void*)stringlengthf);
    define_funct(atomize("string<?"), 2, (void*)stringltf);
    define_funct(atomize("string?"), 1, (void*)stringp);
    define_funct(atomize("string-ref"), 2, (void*)stringreff);
    define_funct(atomize("string-set!"), 3, (void*)stringsetf);
    define_funct(atomize("substring"), 0, (void*)substringf);
    define_funct(atomize("symbol->string"), 1, (void*)sym2str);
    define_funct(atomize("symbol?"), 1, (void*)symbolp);
    define_funct(atomize("tan"), 1, (void*)tanff);
    define_funct(atomize("~"), 1, (void*)complement);
    define_funct(atomize("trace"), 1, (void*)trace);
    define_funct(atomize("truncate"), 1, (void*)truncateff);
    define_funct(atomize("char-upcase"), 1, (void*)upcase);
    define_funct(atomize("char-upper-case?"), 1, (void*)uppercasep);
    define_funct(atomize("vector->list"), 1, (void*)vec2list);
    define_funct(atomize("vector"), 0, (void*)vector);
    define_funct(atomize("vector-fill!"), 2, (void*)vecfill);
    define_funct(atomize("vector-length"), 1, (void*)veclength);
    define_funct(atomize("vector?"), 1, (void*)vectorp);
    define_funct(atomize("vector-ref"), 2, (void*)vecref);
    define_funct(atomize("vector-set!"), 3, (void*)vecset);
    define_funct(atomize("char-whitespace?"), 1, (void*)whitespacep);
    define_funct(atomize("with-input-from-file"), 2, (void*)within);
    define_funct(atomize("with-output-to-file"), 2, (void*)without);
    define_funct(atomize("write"), 0, (void*)writef);
    define_funct(atomize("write-char"), 0, (void*)writechar);
    define_funct(atomize("^"), 0, (void*)xorf);
    define_funct(atomize("null?"), 1, (void*)nullp);
    define_funct(atomize("pair?"), 1, (void*)pairp);
    define_funct(atomize("negative?"), 1, (void*)negativep);
    define_funct(atomize("positive?"), 1, (void*)positivep);
    define_funct(atomize("%"), 0, (void*)unimod);
    define_funct(atomize("/"), 0, (void*)unidiv);
    define_funct(atomize("not"), 1, (void*)isnot);
    define_funct(atomize("neg"), 1, (void*)negf);
    define_funct(atomize("<"), 2, (void*)lt);
    define_funct(atomize("<="), 2, (void*)le);
    define_funct(atomize(">="), 2, (void*)ge);
    define_funct(atomize(">"), 2, (void*)gt);
    define_funct(atomize("eq?"), 2, (void*)eqp);
    define_funct(atomize("="), 2, (void*)eqnp);
    define_funct(atomize("equal?"), 2, (void*)equalp);
    define_funct(atomize("eqv?"), 2, (void*)eqv);
    define_funct(atomize("+"), 0, (void*)uniadd);
    define_funct(atomize("-"), 0, (void*)unisub);
    define_funct(atomize("*"), 0, (void*)unimul);
    define_funct(atomize("car"), 1, (void*)car);
    define_funct(atomize("cdr"), 1, (void*)cdr);
    define_funct(atomize("cons"), 2, (void*)cons);

    define_form(atomize("begin"), beginform);
    define_form(atomize("bound?"), boundp);
    define_form(atomize("cond"), condform);
    define_form(atomize("define"), defineform);
    define_form(atomize("delay"), delayform);
    define_form(atomize("do"), doform);
    define_form(atomize("interaction-environment"), intenvform);
    define_form(atomize("null-environment"), nulenvform);
    define_form(atomize("let"), letform);
    define_form(atomize("let*"), letstarform);
    define_form(atomize("letrec"), letrecform);
    define_form(atomize("quasiquote"), quasiquoteform);
    define_form(atomize("set!"), setform);
    define_form(atomize("while"), whileform);
    define_form(atomize("and"), andform);
    define_form(atomize("or"), orform);
    define_form(atomize("if"), ifform);
    define_form(atomize("quote"), quoteform);
    define_form(atomize("lambda"), lambdaform);
    define_form(atomize("complex"), complexform);
    define_form(atomize("rational"), rationalform);

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
        if (eof == e)
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

