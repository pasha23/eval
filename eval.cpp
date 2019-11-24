/*
 * this aspires to be a scheme interpreter
 * but it lacks tail call optimization, call/cc etc.
 * 
 * Robert Kelley October 2019
 */
#define PSIZE   32768
#define CELLS   262144
#undef  BROKEN

#define UNW_LOCAL_ONLY
#ifdef  UNWIND
#include <libunwind.h>
#include <cxxabi.h>
#endif
#include <alloca.h>
#include <assert.h>
#include <csetjmp>
#include <csignal>
#include <cstring>
#include <ctype.h>
#include <errno.h>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <istream>
#include <limits.h>
#include <math.h>
#include <ostream>
#include <set>
#include <sstream>
#include <stdint.h>
#include <stdlib.h>
#include <string>
#include <termios.h>
#include <unistd.h>

#ifdef BROKEN
#define error(s) do { std::cout << s << std::endl; assert(false); } while(0)
#else
#define error(s) do { longjmp(the_jmpbuf, (long)s); } while(0)
#endif

/*
 * storage is managed as a freelist of cells, each potentially containing two pointers
 *
 * if bit 0 is 0 it's a Cons
 * otherwise the type is in the second byte
 * if bit 1 is set then it's marked
 *
 * vectors are stored on the regular heap new / delete
 */
enum Tag0 { CONS = 0, OTHER = 1, MARK = 2 };

enum Tag1
{
    ATOM    = 0x0001,
    STRING  = 0x0101,
    CHUNK   = 0x0201,
    FORM    = 0x0301,
    FIXNUM  = 0x0401,
    FUNCT   = 0x0501,
    FLOAT   = 0x0601,
    DOUBLE  = 0x0701,
    CHAR    = 0x0801,
    INPORT  = 0x0901,
    OUTPORT = 0x0A01,
    VECTOR  = 0x0B01
};

typedef struct Cons *sexp;
typedef sexp (*Formp)(sexp, sexp);
typedef sexp (*Varargp)(sexp);
typedef sexp (*Oneargp)(sexp);
typedef sexp (*Twoargp)(sexp, sexp);
typedef sexp (*Threeargp)(sexp, sexp, sexp);

jmp_buf the_jmpbuf;

const bool cache = true;    // cache global environment in value cells
int killed = 1;             // we might not make it through initialization
int gcstate;           	    // handling break during gc
int indent;                 // handling eval trace indent
sexp expr;              	// the expression read
sexp valu;              	// the value of it
sexp cell;         	    	// all the storage starts here
sexp atoms;         		// all atoms are linked in a list
sexp global;        		// this is the global symbol table (a list)
sexp inport;        		// the current input port
sexp outport;       		// the current output port
sexp tracing;       		// trace everything
sexp errport;       		// the stderr port
sexp freelist;      		// available cells are linked in a list
sexp *psp;          		// protection stack pointer
sexp *psend;            	// protection stack end
sexp *protect;      		// protection stack

sexp closure, comma, commaat, complex, definea, dot, elsea, eof, f, lambda;
sexp lbracket, lparen, minus, one, promise, qchar, quasiquote, quote;
sexp rational, rbracket, rparen, t, tick, unquote, unquotesplicing, voida, zero;

sexp define(sexp p, sexp r);
sexp eval(sexp p, sexp env);
sexp apply(sexp fun, sexp args);
sexp read(std::istream& fin, int level);
sexp scan(std::istream& fin);
void debug(const char* label, sexp exp);
sexp nesteddefine(sexp exp, sexp env);

struct PortStream
{
    void* streamPointer;
    PortStream(void* streamPointer) : streamPointer(streamPointer) {}
    virtual int get(void) { return -1; }
    virtual void unget(void) { assert(false); }
    virtual void put(int ch) { assert(false); }
    virtual void write(const char* s, int len) { assert(false); }
    virtual sexp read(void) { return eof; }
    virtual sexp scan(void) { return eof; }
    virtual bool good(void) { return false; }
    virtual ~PortStream() {}
};

struct CinPortStream : public PortStream
{
    CinPortStream(std::istream& stdstream) : PortStream(&stdstream) {}
    virtual int get(void) { return ((std::istream*)streamPointer)->get(); }
    virtual void unget(void) { ((std::istream*)streamPointer)->unget(); }
    virtual sexp read(void) { return ::read(*(std::istream*)streamPointer, 0); }
    virtual sexp scan(void) { return ::scan(*(std::istream*)streamPointer); }
    virtual bool good(void) { return ((std::istream*)streamPointer)->good(); }
} cinStream(std::cin);

struct CoutPortStream : public PortStream
{
    CoutPortStream(std::ostream& stdstream) : PortStream(&stdstream) {}
    virtual void put(int ch) { ((std::ostream*)streamPointer)->put(ch); }
    virtual void write(const char *s, int len) { ((std::ostream*)streamPointer)->write(s, len); }
    virtual bool good(void) { return ((std::ostream*)streamPointer)->good(); }
} coutStream(std::cout), cerrStream(std::cerr);

struct IfsPortStream : public PortStream
{
    IfsPortStream(const char *name, std::ios_base::openmode mode) : PortStream(new std::ifstream(name, mode)) {}
    virtual int get(void) { return ((std::ifstream*)streamPointer)->get(); }
    virtual void unget(void) { ((std::ifstream*)streamPointer)->unget(); }
    virtual sexp read(void) { return ::read(*(std::ifstream*)streamPointer, 0); }
    virtual sexp scan(void) { return ::scan(*(std::ifstream*)streamPointer); }
    virtual bool good(void) { return ((std::ifstream*)streamPointer)->good(); }
    virtual ~IfsPortStream() { delete (std::ifstream*) streamPointer; }
};

struct OfsPortStream : public PortStream
{
    OfsPortStream(const char *name, std::ios_base::openmode mode) : PortStream(new std::ofstream(name, mode)) {}
    virtual void put(int ch) { ((std::ofstream*)streamPointer)->put(ch); }
    virtual void write(const char *s, int len) { ((std::ofstream*)streamPointer)->write(s, len); }
    virtual bool good(void) { return ((std::ofstream*)streamPointer)->good(); }
    virtual ~OfsPortStream() { delete (std::ofstream*) streamPointer; }
};

struct StrPortStream : public PortStream
{
    long limit;

    StrPortStream(std::stringstream& stringstream, long limit) : PortStream(&stringstream), limit(limit) {}
    virtual int get(void) { return ((std::stringstream*)streamPointer)->get(); }
    virtual void unget(void) { ((std::stringstream*)streamPointer)->unget(); }
    virtual void put(int ch);
    virtual void write(const char *s, int len);
    virtual sexp read(void) { return ::read(*(std::stringstream*)streamPointer, 0); }
    virtual sexp scan(void) { return ::scan(*(std::stringstream*)streamPointer); }
    virtual bool good(void) { return ((std::stringstream*)streamPointer)->good(); }
    virtual ~StrPortStream() { delete (std::stringstream*) streamPointer; }
};

void StrPortStream::put(int ch)
{ 
    std::stringstream* ss = (std::stringstream*)streamPointer;
    if (ss->tellp() < limit)
        ((std::stringstream*)streamPointer)->put(ch);
}

void StrPortStream::write(const char *s, int len)
{
    std::stringstream* ss = (std::stringstream*)streamPointer;
    if (limit && (long)ss->tellp() + len > limit)
        len = limit - (long)ss->tellp() - 1;
    ss->write(s, len);
}

/*
 * note that there is just no room for virtual function pointers
 */
struct Cons    { sexp                cdr; sexp                         car; };
struct Tags    { char                                   tags[sizeof(Cons)]; };
struct Stags   { short stags; char tags[sizeof(sexp)-2]; sexp          car; };
struct Chunk   { char tags[2];            char        text[sizeof(Cons)-2]; };
struct Atom    { char tags[sizeof(sexp)]; sexp                        body; };
struct String  { char tags[sizeof(sexp)]; sexp                      chunks; };
struct Fixnum  { char tags[sizeof(sexp)]; long                      fixnum; };
struct Float   { char tags[sizeof(Cons)-sizeof(float)];  float      flonum; };
struct Double  { char tags[sizeof(Cons)-sizeof(double)]; double     flonum; };
struct Funct   { char tags[sizeof(sexp)]; void*                      funcp; };
struct Form    { char tags[sizeof(sexp)]; Formp                      formp; };
struct Char    { char tags[sizeof(sexp)-sizeof(short)];  short          ch; };
struct InPort  { char tags[sizeof(sexp)-2]; char avail,peek; PortStream* s; };
struct OutPort { char tags[sizeof(sexp)]; PortStream*                    s; };
struct Vector  { char tags[sizeof(sexp)-sizeof(short)]; short l; sexp*   e; };

// supports uglyprinting
class Ugly
{
    static const int tabs =  4;
    static const int eol  = 50;

    std::ostream& s;
    std::streampos pos;
public:
    Ugly(std::ostream& s) : s(s) { pos = s.tellp(); }
    void wrap(int level, int length) { if (s.tellp() - pos + length > eol) newline(level); else space(); }
    void newline(int level) { s << '\n'; pos = s.tellp(); for (int i = level; --i >= 0; s << ' ') {} }
    void space(void) { s << ' '; }
};

std::ostream& display(std::ostream& s, sexp p, std::set<sexp>& seenSet, Ugly& ugly, int level, bool write);

static inline int  shortType(const sexp p) { return       (~MARK &  ((Stags*)p)->stags);  }
static inline int  arity(const sexp p)     { return                 ((Funct*)p)->tags[2]; }
static inline bool isMarked(const sexp p)  { return       ( MARK &  ((Tags*)p)->tags[0]); }
static inline bool isCons(const sexp p)    { return p && !(OTHER &  ((Tags*)p)->tags[0]); }
static inline bool isAtom(const sexp p)    { return p &&         ATOM    == shortType(p); }
static inline bool isString(const sexp p)  { return p &&         STRING  == shortType(p); }
static inline bool isFunct(const sexp p)   { return p &&         FUNCT   == shortType(p); }
static inline bool isForm(const sexp p)    { return p &&         FORM    == shortType(p); }
static inline bool isFixnum(const sexp p)  { return p &&         FIXNUM  == shortType(p); }
static inline bool isFloat(const sexp p)   { return p &&         FLOAT   == shortType(p); }
static inline bool isDouble(const sexp p)  { return p &&         DOUBLE  == shortType(p); }
static inline bool isChar(const sexp p)    { return p &&         CHAR    == shortType(p); }
static inline bool isInPort(const sexp p)  { return p &&         INPORT  == shortType(p); }
static inline bool isOutPort(const sexp p) { return p &&         OUTPORT == shortType(p); }
static inline bool isVector(const sexp p)  { return p &&         VECTOR  == shortType(p); }

static inline sexp boolwrap(bool x) { return x ? t : f; }

bool isClosure(sexp p)
{
    return isCons(p) &&
           closure == p->car &&                         // (closure
           isCons(p = p->cdr) && p->car &&              //  exp
           isCons(p = p->cdr) && p->car &&              //  env)
           !p->cdr;
}

// closure?
sexp closurep(sexp s) { return boolwrap(isClosure(s)); }

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
sexp promisep(sexp s) { return boolwrap(isPromise(s)); }

bool isRational(sexp p)
{
    return isCons(p) && rational == p->car &&          // (rational
           isCons(p = p->cdr) && isFixnum(p->car) &&   //  numerator
           isCons(p = p->cdr) && isFixnum(p->car) &&   //  denominator
           !p->cdr;                                    // )
}

// rational?
sexp rationalp(sexp s) { return boolwrap(isRational(s)); }

bool isFlonum(const sexp p)  { return isFloat(p) || isDouble(p) || isRational(p); }

bool isComplex(sexp p)
{
    return isCons(p) && complex == p->car &&            // (complex
           isCons(p = p->cdr) && isFlonum(p->car) &&    //  real-part
           isCons(p = p->cdr) && isFlonum(p->car) &&    //  imag-part
           !p->cdr;                                     // )
}

// complex?
sexp complexp(sexp s) { return boolwrap(isComplex(s)); }

/*
 * save the argument on the protection stack, return it
 */
void psoverflow(void)
{
    error("protection stack overflow");
}

static inline sexp save(sexp p)
{
    *psp++ = p;
    if (psp >= psend)
        psoverflow();
    return p;
}

static inline void save(sexp p, sexp q)
{
    sexp* s = psp;
    if (s + 2 >= psend)
        psoverflow();
    *s++ = p;
    *s++ = q;
    psp = s;
}

static inline void save(sexp p, sexp q, sexp r)
{
    sexp* s = psp;
    if (s + 3 >= psend)
        psoverflow();
    *s++ = p;
    *s++ = q;
    *s++ = r;
    psp = s;
}

/*
 * replace the top of the protection stack, return it
 */
static inline sexp replace(sexp p) { return *psp = p; }

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

static inline sexp lose(sexp* mark, sexp p) { psp = mark; return p; }

static inline sexp lose(sexp p) { --psp; return p; }

static inline void markCell(sexp p)   { ((Tags*)p)->tags[0] |=  MARK; }

static inline void unmarkCell(sexp p) { ((Tags*)p)->tags[0] &= ~MARK; }

/*
 * visit objects reachable from p, setting their MARK bit
 */
void mark(sexp p)
{
    if (!p || isMarked(p))
        return;

    if (isCons(p))
    {
        sexp q = p->cdr;
        sexp r = p->car;
        markCell(p);
        mark(q);
        mark(r);
        return;
    }

    switch (((Stags*)p)->stags)
    {
    case ATOM:
        mark(((Atom*)p)->body);
        break;
    case STRING:
        mark(((String*)p)->chunks);
        break;
    case VECTOR:
        Vector* v = (Vector*)p;
        for (int i = v->l; --i >= 0; mark(v->e[i])) {}
    }

    markCell(p);
}

void deleteinport(sexp v)
{
    PortStream* stream = ((InPort*)v)->s;
    ((InPort*)v)->s = 0;
    if (stream != &cinStream)
        delete stream;
}

void deleteoutport(sexp v)
{
    PortStream* stream = ((OutPort*)v)->s;
    ((OutPort*)v)->s = 0;
    if (stream != &coutStream && stream != &cerrStream)
        delete stream;
}

static void deletevector(sexp v) { delete ((Vector*)v)->e; }

/*
 * mark all reachable objects
 *
 * sweep all storage, putting unmarked objects on the freelist
 */
sexp gc(void)
{
    ++gcstate;

    mark(one);
    mark(zero);
    mark(expr);
    mark(valu);
    mark(atoms);
    mark(global);
    mark(inport);
    mark(errport);
    mark(outport);

    for (sexp *p = protect; p < psp; mark(*p++)) {}

    freelist = 0;

    for (sexp p = cell; p < cell+CELLS; ++p)
    {
        if (!isMarked(p))
        {
            switch (((Stags*)p)->stags)
            {
            case OUTPORT: deleteoutport(p); break;
            case INPORT:  deleteinport(p);  break;
            case VECTOR:  deletevector(p);  break;
            }
            p->car = 0;
            p->cdr = freelist;
            freelist = p;
        } else 
            unmarkCell(p);
    }

    if (!freelist)
        error("gc: storage exhausted");

    if (gcstate > 1)
    {
        killed = 0;
        gcstate = 0;
        error("SIGINT");
    }
    gcstate = 0;
    return voida;
}

void assertAtom(sexp s)        { if (!isAtom(s))        error("not symbol"); }
void assertChar(sexp s)        { if (!isChar(s))        error("not a character"); }
void assertFixnum(sexp s)      { if (!isFixnum(s))      error("not an integer"); }
void assertString(sexp s)      { if (!isString(s))      error("not a string"); }
void assertInPort(sexp s)      { if (!isInPort(s))      error("not an input port"); }
void assertOutPort(sexp s)     { if (!isOutPort(s))     error("not an output port"); }
void assertComplex(sexp s)     { if (!isComplex(s))     error("not complex"); }
void assertRational(sexp s)    { if (!isRational(s))    error("not rational"); }
void assertPromise(sexp s)     { if (!isPromise(s))     error("not a promise"); }

void assertFlonum(sexp s) { if (!isFlonum(s) && !isFixnum(s) && !isRational(s)) error("not a real number"); }

/*
 * allocate a cell from the freelist
 */
sexp newcell(void)
{
    if (!freelist)
        gc();
    Cons* p = freelist;
    freelist = freelist->cdr;
    p->cdr = 0; // this is important!
    return p;
}

sexp newcell(short stags)
{
    Stags* t = (Stags*)newcell();
    t->stags = stags;
    return (sexp)t;
}

sexp newcell(short stags, sexp car)
{
    Stags* t = (Stags*)newcell(stags);
    t->car = car;
    return (sexp)t;
}

sexp newfixnum(long number)
{
    Fixnum* p = (Fixnum*)newcell(FIXNUM);
    p->fixnum = number;
    return (sexp)p;
}

sexp newcharacter(int c)
{
    Char* p = (Char*)newcell(CHAR);
    p->ch = c;
    return (sexp)p;
}

sexp newinport(const char* name)
{
    InPort* p = (InPort*)newcell(INPORT);
    p->avail = 0; p->peek = 0;
    p->s = new IfsPortStream(name, std::ifstream::ios_base::in);
    return (sexp)p;
}

sexp newoutport(const char* name)
{
    OutPort* p = (OutPort*)newcell(OUTPORT);
    p->s = new OfsPortStream(name, std::ofstream::ios_base::out);
    return (sexp)p;
}

sexp newflonum(double number)
{
    if (sizeof(double) > sizeof(void*)) {
        Float* p = (Float*)newcell(FLOAT);
        p->flonum = number;
        return (sexp)p;
    } else {
        Double* p = (Double*)newcell(DOUBLE);
        p->flonum = number;
        return (sexp)p;
    }
}

// cons
sexp cons(sexp car, sexp cdr)
{
    sexp* r = psp;
    sexp* s = r;
    *s++ = car;
    *s++ = cdr;
    psp = s;
    if (!freelist)
        gc();
    sexp p = freelist;
    freelist = freelist->cdr;
    p->car = car;
    p->cdr = cdr;
    psp = r;
    return p;
}

// car
sexp car(sexp p) { if (!isCons(p)) error("error: car of non-pair"); return p->car; }

// cdr
sexp cdr(sexp p) { if (!isCons(p)) error("error: cdr of non-pair"); return p->cdr; }

// set-car!
sexp set_car(sexp p, sexp q) { if (!isCons(p)) error("error: set-car! of non-pair"); p->car = q; return voida; }

// set-cdr!
sexp set_cdr(sexp p, sexp q) { if (!isCons(p)) error("error: set-cdr! of non-pair"); p->cdr = q; return voida; }

// and
sexp andform(sexp p, sexp env)
{
    sexp* mark = psp;
    sexp q = t;
    save(env, p, q);
    while ((p = p->cdr) && f != (q = replace(eval(p->car, env)))) {}
    return lose(mark, q);
}

// or
sexp orform(sexp p, sexp env)
{
    sexp* mark = psp;
    sexp q = f;
    save(env, p, q);
    while ((p = p->cdr) && f == (q = replace(eval(p->car, env)))) {}
    return lose(mark, q);
}

// trace
sexp trace(sexp arg)
{
    sexp r = tracing;
    tracing = arg;
    return r;
}

static inline long asFixnum(sexp p) { return ((Fixnum*)p)->fixnum; }

double rat2real(sexp x) { x = x->cdr; return (double)asFixnum(x->car) / (double)asFixnum(x->cdr->car); }

double asFlonum(sexp p)
{
    if (isRational(p))
        return rat2real(p);

    switch (shortType(p))
    {
    default:     error("asFlonum: not a flonum");
    case FLOAT:  return ((Float*)p)->flonum;
    case DOUBLE: return ((Double*)p)->flonum;
    case FIXNUM: return (double) asFixnum(p);
    }
}

// negative?
sexp negativep(sexp x)
{
    if (isRational(x))
    {
        x = x->cdr;
        if (asFixnum(x->car) < 0)
            return boolwrap(asFixnum(x->cdr->car) >= 0);
        else
            return boolwrap(asFixnum(x->cdr->car) <  0);
    }

    return boolwrap(asFlonum(x) < 0);
}

// positive?
sexp positivep(sexp x)
{
    if (isRational(x))
    {
        x = x->cdr;
        if (asFixnum(x->car) < 0)
            return boolwrap(asFixnum(x->cdr->car) <  0);
        else
            return boolwrap(asFixnum(x->cdr->car) >= 0);
    }

    return boolwrap(asFlonum(x) > 0);
}

// boolean?
sexp booleanp(sexp x) { return boolwrap(t == x || f == x); }

// <
sexp ltp(sexp x, sexp y) { return boolwrap(asFlonum(x) < asFlonum(y)); }

// <=
sexp lep(sexp x, sexp y) { return boolwrap(asFlonum(x) <= asFlonum(y)); }

// >=
sexp gep(sexp x, sexp y) { return boolwrap(asFlonum(x) >= asFlonum(y)); }

// >
sexp gtp(sexp x, sexp y) { return boolwrap(asFlonum(x) > asFlonum(y)); }

sexp make_rational(sexp num, sexp den)
{
    return lose(cons(rational, replace(cons(num, save(cons(den, 0))))));
}

sexp newrational(long n, long d)
{
    sexp* mark = psp;
    return lose(mark, make_rational(save(newfixnum(n)), save(newfixnum(d))));
}

sexp make_complex(sexp re, sexp im)
{
    sexp* mark = psp;
    return lose(mark, cons(complex, replace(cons(save(re), replace(cons(save(im), 0))))));
}

sexp newcomplex(double re, double im)
{
    sexp* mark = psp;
    return lose(mark, make_complex(save(newflonum(re)), save(newflonum(im))));
}

double realpart(sexp x) { assertComplex(x); return asFlonum(x->cdr->car); }

double imagpart(sexp x) { assertComplex(x); return asFlonum(x->cdr->cdr->car); }

// magnitude
sexp magnitude(sexp z)
{
    assertComplex(z);
    z = z->cdr;
    return newflonum(sqrt(asFlonum(z->car)      * asFlonum(z->car) +
                          asFlonum(z->cdr->car) * asFlonum(z->cdr->car)));
}

// angle
sexp angle(sexp z)
{
    assertComplex(z);
    z = z->cdr;
    return newflonum(atan2(asFlonum(z->cdr->car), asFlonum(z->car)));
}

long gcd(long x, long y)
{
    for (;;)
    {
        if (0 == x) return y;
        y %= x;
        if (0 == y) return x;
        x %= y;
    }
}

// gcd
sexp gcdf(sexp x, sexp y) { assertFixnum(x); assertFixnum(y); return newfixnum(gcd(asFixnum(x), asFixnum(y))); }

long lcm(long x, long y) { long g = gcd(x, y); return (x / g) * (y / g); }

// lcm
sexp lcmf(sexp x, sexp y) { assertFixnum(x); assertFixnum(y); return newfixnum(lcm(asFixnum(x), asFixnum(y))); }

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

static inline long num(sexp x) { return isRational(x) ? asFixnum(x->cdr->car) : asFixnum(x); }

static inline long den(sexp x) { return isRational(x) ? asFixnum(x->cdr->cdr->car) : 1; }

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

// exact?
sexp exactp(sexp x) { return boolwrap(isFixnum(x) || isRational(x)); }

// inexact?
sexp inexactp(sexp x) { return boolwrap(isFlonum(x)); }

sexp complex_add(sexp z, sexp w)
{
    sexp* mark = psp;
    if (exactp(z->cdr->car) && exactp(z->cdr->cdr->car) &&
        exactp(w->cdr->car) && exactp(z->cdr->cdr->car))
    {
        sexp real = save(rational_add(z->cdr->car, w->cdr->car));
        sexp imag = save(rational_add(z->cdr->cdr->car, w->cdr->cdr->car));
        return lose(mark, make_complex(real, imag));
    }
    double re = realpart(z)+realpart(w);
    double im = imagpart(z)+imagpart(w);
    return 0.0 == im ? newflonum(re) : newcomplex(re, im);
}

sexp complex_sub(sexp z, sexp w)
{
    sexp* mark = psp;
    if (exactp(z->cdr->car) && exactp(z->cdr->cdr->car) &&
        exactp(w->cdr->car) && exactp(z->cdr->cdr->car))
    {
        sexp real = save(rational_sub(z->cdr->car, w->cdr->car));
        sexp imag = save(rational_sub(z->cdr->cdr->car, w->cdr->cdr->car));
        return lose(mark, make_complex(real, imag));
    }
    double re = realpart(z)-realpart(w);
    double im = imagpart(z)-imagpart(w);
    return 0.0 == im ? newflonum(re) : newcomplex(re, im);
}

sexp complex_mul(sexp z, sexp w)
{
    sexp* mark = psp;
    if (exactp(z->cdr->car) && exactp(z->cdr->cdr->car) &&
        exactp(w->cdr->car) && exactp(z->cdr->cdr->car))
    {
        sexp x = z->cdr->car;
        sexp y = z->cdr->cdr->car;
        sexp u = w->cdr->car;
        sexp v = w->cdr->cdr->car;
        sexp real = save(rational_sub(save(rational_mul(x, u)), save(rational_mul(y, v))));
        sexp imag = save(rational_add(save(rational_mul(x, v)), save(rational_mul(y, u))));
        return lose(mark, make_complex(real, imag));
    }
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
    sexp* mark = psp;
    if (exactp(z->cdr->car) && exactp(z->cdr->cdr->car) &&
        exactp(w->cdr->car) && exactp(z->cdr->cdr->car))
    {
        sexp x = z->cdr->car;
        sexp y = z->cdr->cdr->car;
        sexp u = w->cdr->car;
        sexp v = w->cdr->cdr->car;
        sexp d = save(rational_add(save(rational_mul(u, u)), save(rational_mul(v, v))));
        sexp real = save(rational_div(save(rational_add(save(rational_mul(x, u)),
                                                        save(rational_mul(y, v)))), d));
        sexp imag = save(rational_div(save(rational_sub(save(rational_mul(y, u)),
                                                        save(rational_mul(x, v)))), d));
        return lose(mark, make_complex(real, imag));
    }
    double x = realpart(z);
    double y = imagpart(z);
    double u = realpart(w);
    double v = imagpart(w);
    double d = u*u + v*v;
    double re = (x*u + y*v) / d;
    double im = (y*u - x*v) / d;
    return 0.0 == im ? newflonum(re) : newcomplex(re, im);
}

// x + y
sexp sum(sexp x, sexp y)
{
    if (isComplex(x)) {
        if (isComplex(y))
            return complex_add(x, y);
        if (isRational(y) || isFixnum(y) || isFlonum(y))
            return lose(complex_add(x, save(make_complex(y, zero))));
    } else if (isRational(x)) {
        if (isComplex(y))
            return lose(complex_add(y, save(make_complex(x, zero))));
        if (isRational(y) || isFixnum(y))
            return rational_add(x, y);
        if (isFlonum(y))
            return newflonum(rat2real(x) + asFlonum(y));
    } else if (isFixnum(x)) {
        if (isComplex(y))
            return lose(complex_add(y, save(make_complex(x, zero))));
        if (isRational(y))
            return lose(rational_add(save(make_rational(x, one)), y));
        if (isFixnum(y))
            return newfixnum(asFixnum(x) + asFixnum(y));
        if (isFlonum(y))
            return newflonum((double)asFixnum(x) + asFlonum(y));
    } else if (isFlonum(x)) {
        if (isComplex(y))
            return lose(complex_add(save(make_complex(x, zero)), y));
        if (isRational(y))
            return newflonum(asFlonum(x) + rat2real(y));
        if (isFixnum(y))
            return newflonum(asFlonum(x) + (double)asFixnum(y));
        if (isFlonum(y))
            return newflonum(asFlonum(x) + asFlonum(y));
    }

    error("sum: operand");
}

// x0 + x1 + x2 ...
sexp uniadd(sexp l)
{
    sexp* mark = psp;
    sexp result = zero;
    save(l, result);
    while (l)
    {
        result = replace(sum(result, l->car));
        l = l->cdr;
    }
    return lose(mark, result);
}

// - x
sexp unineg(sexp x)
{
    if (isRational(x))
        return rational_reduce(-asFixnum(x->cdr->car), asFixnum(x->cdr->cdr->car));

    if (isComplex(x))
    {
        sexp* mark = psp;
        return lose(mark, make_complex(save(unineg(x->cdr->car)), save(unineg(x->cdr->cdr->car))));
    }

    switch (shortType(x))
    {
    default:     error("neg: operand");
    case FIXNUM: return newfixnum(-((Fixnum*)x)->fixnum);
    case FLOAT:  return newflonum(-((Float*)x)->flonum);
    case DOUBLE: return newflonum(-((Double*)x)->flonum);
    }
}

// x - y
sexp diff(sexp x, sexp y)
{
    if (isComplex(x)) {
        if (isComplex(y))
            return complex_sub(x, y);
        if (isRational(y) || isFixnum(y) || isFlonum(y))
            return lose(complex_sub(x, save(make_complex(y, zero))));
    } else if (isRational(x)) {
        if (isComplex(y))
            return lose(complex_sub(y, save(make_complex(x, zero))));
        if (isRational(y) || isFixnum(y))
            return rational_sub(x, y);
        if (isFlonum(y))
            return newflonum(rat2real(x) - asFlonum(y));
    } else if (isFixnum(x)) {
        if (isComplex(y))
            return lose(complex_sub(y, save(make_complex(x, zero))));
        if (isRational(y))
            return lose(rational_sub(save(make_rational(x, one)), y));
        if (isFixnum(y))
            return newfixnum(asFixnum(x) - asFixnum(y));
        if (isFlonum(y))
            return newflonum((double)asFixnum(x) - asFlonum(y));
    } else if (isFlonum(x)) {
        if (isComplex(y))
            return lose(complex_sub(save(make_complex(x, zero)), y));
        if (isRational(y))
            return newflonum(asFlonum(x) - rat2real(y));
        if (isFixnum(y))
            return newflonum(asFlonum(x) - (double)asFixnum(y));
        if (isFlonum(y))
            return newflonum(asFlonum(x) - asFlonum(y));
    }

    error("diff: operand");
}

// - x0
// x0 - x1
// x0 - x1 - x2 - x3 ...
sexp unisub(sexp l)
{
    if (!l)
        return zero;
    if (!l->cdr)
        return unineg(l->car);
    sexp* mark = psp;
    return lose(diff(l->car, save(uniadd(l->cdr))));
}

// x * y
sexp product(sexp x, sexp y)
{
    if (isComplex(x)) {
        if (isComplex(y))
            return complex_mul(x, y);
        if (isRational(y) || isFixnum(y) || isFlonum(y))
            return lose(complex_mul(x, save(make_complex(y, zero))));
    } else if (isRational(x)) {
        if (isComplex(y))
            return lose(complex_mul(y, save(make_complex(x, zero))));
        if (isRational(y) || isFixnum(y))
            return rational_mul(x, y);
        if (isFlonum(y))
            return newflonum(rat2real(x) * asFlonum(y));
    } else if (isFixnum(x)) {
        if (isComplex(y))
            return lose(complex_mul(y, save(make_complex(x, zero))));
        if (isRational(y))
            return lose(rational_mul(save(make_rational(x, one)), y));
        if (isFixnum(y))
            return newfixnum(asFixnum(x) * asFixnum(y));
        if (isFlonum(y))
            return newflonum((double)asFixnum(x) * asFlonum(y));
    } else if (isFlonum(x)) {
        if (isComplex(y))
            return lose(complex_mul(save(make_complex(x, zero)), y));
        if (isRational(y))
            return newflonum(asFlonum(x) * rat2real(y));
        if (isFixnum(y))
            return newflonum(asFlonum(x) * (double)asFixnum(y));
        if (isFlonum(y))
            return newflonum(asFlonum(x) * asFlonum(y));
    }

    error("product: operand");
}

// x0 * x1 * x2 ...
sexp unimul(sexp l)
{
    sexp* mark = psp;
    sexp result = one;
    save(l, result);
    while (l)
    {
        result = replace(product(result, l->car));
        l = l->cdr;
    }
    return lose(mark, result);
}

// x / y
sexp quotientf(sexp x, sexp y)
{
    if (isComplex(x)) {
        if (isComplex(y))
            return complex_div(x, y);
        if (isRational(y) || isFixnum(y) || isFlonum(y))
            return lose(complex_div(x, save(make_complex(y, zero))));
    } else if (isRational(x)) {
        if (isComplex(y))
            return lose(complex_div(y, save(make_complex(x, zero))));
        if (isRational(y) || isFixnum(y))
            return rational_div(x, y);
        if (isFlonum(y))
            return newflonum(rat2real(x) / asFlonum(y));
    } else if (isFixnum(x)) {
        if (isComplex(y))
            return lose(complex_div(y, save(make_complex(x, zero))));
        if (isFixnum(y) || isRational(y))
            return lose(rational_div(save(make_rational(x, one)), y));
        if (isFlonum(y))
            return newflonum((double)asFixnum(x) / asFlonum(y));
    } else if (isFlonum(x)) {
        if (isComplex(y))
            return lose(complex_div(save(make_complex(x, zero)), y));
        if (isRational(y))
            return newflonum(asFlonum(x) / rat2real(y));
        if (isFixnum(y))
            return newflonum(asFlonum(x) / (double)asFixnum(y));
        if (isFlonum(y))
            return newflonum(asFlonum(x) / asFlonum(y));
    }

    error("quotient: operand");
}

// x0 / x1 / x2 ...
sexp unidiv(sexp l)
{
    sexp* mark = psp;

    sexp result;
    if (l && l->cdr)
    {
        result = l->car;
        l = l->cdr;
    } else
        result = one;

    save(l, result);

    while (l)
    {
        result = replace(quotientf(result, l->car));
        l = l->cdr;
    }

    return lose(mark, result);
}

sexp rational_mod(sexp x, sexp y)
{
    long d = lcm(den(x), den(y));
    long xn = num(x) * d / den(x);
    long yn = num(y) * d / den(y);
    return rational_reduce(xn % yn, d);
}

sexp complex_mod(sexp x, sexp y) { error("complex_mod: not implemented"); }

// x % y
sexp remainderff(sexp x, sexp y)
{
    if (isComplex(x)) {
        if (isComplex(y))
            return complex_mod(x, y);
        if (isRational(y) || isFixnum(y) || isFlonum(y))
            return lose(complex_mod(x, save(make_complex(y, zero))));
    } else if (isRational(x)) {
        if (isComplex(y))
            return lose(complex_mod(y, save(make_complex(x, zero))));
        if (isRational(y) || isFixnum(y))
            return rational_mod(x, y);
        if (isFlonum(y))
            return newflonum(fmod(rat2real(x), asFlonum(y)));
    } else if (isFixnum(x)) {
        if (isComplex(y))
            return lose(complex_mod(y, save(make_complex(x, zero))));
        if (isRational(y))
            return lose(rational_mod(save(make_rational(x, one)), y));
        if (isFixnum(y))
            return newfixnum(asFixnum(x) % asFixnum(y));
        if (isFlonum(y))
            return newflonum(fmod((double)asFixnum(x), asFlonum(y)));
    } else if (isFlonum(x)) {
        if (isComplex(y))
            return lose(complex_mod(save(make_complex(x, zero)), y));
        if (isRational(y))
            return newflonum(fmod(asFlonum(x), rat2real(y)));
        if (isFixnum(y))
            return newflonum(fmod(asFlonum(x), (double)asFixnum(y)));
        if (isFlonum(y))
            return newflonum(fmod(asFlonum(x), asFlonum(y)));
    }

    error("remainder: operand");
}

// x0 % x1 % x2 ...
sexp unimod(sexp l)
{
    sexp* mark = psp;
    sexp result = l->car;
    save(l, result);
    while (l = l->cdr)
        result = replace(remainderff(result, l->car));
    return lose(mark, result);
}

sexp floatstub(double (*f)(double), sexp x) { assertFlonum(x); return newflonum((*f)(asFlonum(x))); }

// functions on real numbers
sexp acosff(sexp x) { return floatstub(acos, x); } // acos
sexp asinff(sexp x) { return floatstub(asin, x); } // asin
sexp atanff(sexp x) { return floatstub(atan, x); } // atan
sexp cosff(sexp x)  { return floatstub(cos,  x); } // cos
sexp coshff(sexp x) { return floatstub(cosh, x); } // cosh
sexp expff(sexp x)  { return floatstub(exp,  x); } // exp
sexp logff(sexp x)  { return floatstub(log,  x); } // log
sexp sinff(sexp x)  { return floatstub(sin,  x); } // sin
sexp sinhff(sexp x) { return floatstub(sinh, x); } // sinh
sexp tanff(sexp x)  { return floatstub(tan,  x); } // tan
sexp tanhff(sexp x) { return floatstub(tanh, x); } // tanh

// ceil
sexp ceilingff(sexp x)
{
    assertFlonum(x);
    double r = ceil(asFlonum(x));
    return (r == (long)r) ? newfixnum((long)r) : newflonum(r);
}

// floor
sexp floorff(sexp x)
{
    assertFlonum(x);
    double r = floor(asFlonum(x));
    return (r == (long)r) ? newfixnum((long)r) : newflonum(r);
}

// round
sexp roundff(sexp x)
{
    assertFlonum(x);
    double r = round(asFlonum(x));
    return (r == (long)r) ? newfixnum((long)r) : newflonum(r);
}

// truncate
sexp truncateff(sexp x)
{
    assertFlonum(x);
    return newflonum(asFlonum(x) < 0 ? ceil(asFlonum(x)) : floor(asFlonum(x)));
}

// integer square root
uint32_t isqrt(uint64_t v)
{
    uint64_t t, r;

    for (t=0x4000000000000000ULL, r=0; t; t >>= 2)
      if (t + r <= v) {
         v -= t + r;
         r = (r >> 1) | t;
      } else
         r = r >> 1;
   return (uint32_t)r;
}

sexp isqrtf(sexp x)
{
    if (isFixnum(x) && 0 <= asFixnum(x))
        return newfixnum(isqrt(asFixnum(x)));
    error("isqrt: not a positive integer");
}

// sqrt
sexp sqrtff(sexp x)
{
    if (isFixnum(x) && 0 <= asFixnum(x))
        return newflonum(sqrt((double)asFixnum(x)));
    double re, im = 0.0;
    if (isComplex(x)) {
        re = asFlonum(x->cdr->car);
        im = asFlonum(x->cdr->cdr->car);
    } else if (isFixnum(x))
        re = (double)asFixnum(x);
    else if (isFlonum(x))
        re = asFlonum(x);

    if (0.0 == im && 0.0 <= re)
        return newflonum(sqrt(re));

    double r = sqrt(re*re + im*im);
    double theta = atan2(im, re);
    re = sqrt(r) * cos(0.5 * theta);
    im = sqrt(r) * sin(0.5 * theta);
    return newcomplex(re, im);
}

// pow
sexp powff(sexp x, sexp y) { assertFlonum(x); assertFlonum(y); return newflonum(pow(asFlonum(x), asFlonum(y))); }

// atan2
sexp atan2ff(sexp x, sexp y) { assertFlonum(x); assertFlonum(y); return newflonum(atan2(asFlonum(x), asFlonum(y))); }

// integer?
sexp integerp(sexp x) { return boolwrap(isFixnum(x) || isFlonum(x) && (long)asFlonum(x) == asFlonum(x)); }

// real?
sexp realp(sexp x) { return boolwrap(isFixnum(x) || isFlonum(x) || isRational(x)); }

// inexact->exact
sexp inexact_exact(sexp x) { assertFlonum(x); return newfixnum((long)asFlonum(x)); }

// exact->inexact
sexp exact_inexact(sexp x)
{
    if (!isRational(x))
        assertFixnum(x);
    return newflonum((double)asFlonum(x));
}

// <<
sexp lsh(sexp x, sexp y) { assertFixnum(x); assertFixnum(y); return newfixnum(asFixnum(x) << asFixnum(y)); }

// >>
sexp rsh(sexp x, sexp y) { assertFixnum(x); assertFixnum(y); return newfixnum(asFixnum(x) >> asFixnum(y)); }

// not
sexp isnot(sexp x) { return boolwrap(f == x); }

// null?
sexp nullp(sexp x) { return boolwrap(0 == x); }

// list?
sexp listp(sexp x) { return boolwrap(isCons(x) && f != listp(x->cdr)); }

// atom?
sexp atomp(sexp x) { return boolwrap(!isCons(x)); }

// pair?
sexp pairp(sexp x) { return boolwrap(isCons(x)); }

// number?
sexp numberp(sexp x) { return boolwrap(isFixnum(x) || isFlonum(x) || isRational(x) || isComplex(x)); }

// string?
sexp stringp(sexp x) { return boolwrap(isString(x)); }

// symbol?
sexp symbolp(sexp x) { return boolwrap(isAtom(x)); }

// procedure?
sexp procedurep(sexp p) { return boolwrap(isFunct(p) || isClosure(p)); }

// length of String
int slen(sexp s)
{
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
sexp string_length(sexp s) { assertString(s); return newfixnum(slen(s)); }

// index a character in a string
char* sref(sexp s, int i)
{
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

const char * const escapes[] = { "\007a", "\010b", "\011t", "\012n", "\015r", "\"\"", "\\\\", 0 };

char decodeEscape(char c)
{
    for (const char * const * p = escapes; *p; ++p)
        if ((*p)[1] == c)
            return (*p)[0];
    return c;
}

char encodeEscape(char c)
{
    for (const char * const * p = escapes; *p; ++p)
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

    Chunk* r = (Chunk*) save(newcell(CHUNK));
    sexp p = replace(cons((sexp)r, 0));
    sexp q = p;

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
            return lose(p);
        }

        r->text[i++] = c;

        if (i == sizeof(r->text))
        {
            i = 0;
            r = (Chunk*) save(newcell(CHUNK));
            q = q->cdr = lose(cons((sexp)r, 0));
        }
    }
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

// every atom must be unique and saved in the atoms list
sexp intern(sexp p)
{
    for (sexp q = atoms; q; q = q->cdr)
    {
        sexp r = q->car;
        if (0 == scmp(((Atom*)p)->body->cdr, ((Atom*)r)->body->cdr))
            return r;
    }
    atoms = cons(p, atoms);
    return p;
}

sexp newatom(const char* s, sexp value)
{
    return lose(intern(replace(newcell(ATOM, replace(cons(value, save(newchunk(s))))))));
}

sexp newstring(const char* s)
{
    return lose(newcell(STRING, save(newchunk(s))));
}

// number->string (actually we will convert arbitrary s-expressions)
sexp number_string(sexp exp)
{
    std::stringstream s; Ugly ugly(s); std::set<sexp> seenSet;
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    display(s, exp, seenSet, ugly, 0, true);
    return newstring(s.str().c_str());
}

// make-string
sexp make_string(sexp args)
{
    if (!args || !isFixnum(args->car))
        error("make-string: args expected");

    int l = asFixnum(args->car);
    char *b = (char*) alloca(l+1);
    char *q = b;
    int c = args->cdr && isChar(args->cdr->car) ?
                  ((Char*)(args->cdr->car))->ch : ' ';
    // utf8
    for (int i = 0; i < l; ++i)
        *q++ = c;
    *q++ = 0;
    return newstring(b);
}

// copy characters from a String
char* sstr(char* b, int len, sexp s)
{
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
sexp string_copy(sexp s)
{
    assertString(s);
    int len = slen(s)+1;
    return newstring(sstr((char*)alloca(len), len, s));
}

// string-append
sexp string_append(sexp p, sexp q)
{
    assertString(p);
    assertString(q);
    int pl = slen(p);
    int ql = slen(q);
    char *b = (char*) alloca(pl+ql+1);
    sstr(b,    pl+1, p);
    sstr(b+pl, ql+1, q);
    return newstring(b);
}

// string-fill
sexp string_fill(sexp s, sexp c)
{
    assertChar(c);
    assertString(s);

    int k = ((Char*)c)->ch;
    // utf8
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; t->text[i++] = k) {}
    }
    return s;
}

// close-input-port
sexp close_input_port(sexp p) { assertInPort(p); if (inport == p) inport = 0; deleteinport(p); return voida; }

// close-output-port
sexp close_output_port(sexp p) { assertOutPort(p); if (outport == p) outport = 0; deleteoutport(p); return voida; }

// current-input-port
sexp current_input_port(sexp p) { return inport; }

// current-output-port
sexp current_output_port(sexp p) { return outport; }

// input-port?
sexp input_portp(sexp p) { return boolwrap(isInPort(p)); }

// open-input-file
sexp open_input_file(sexp p)
{
    assertString(p);
    int len = slen(p)+1;
    char* b = (char*) alloca(len);
    sstr(b, len, p);
    return newinport(b);
}

// open-output-file
sexp open_output_file(sexp p)
{
    assertString(p);
    int len = slen(p)+1;
    char* b = (char*) alloca(slen(p)+1);
    sstr(b, len, p);
    return newoutport(b);
}

// output-port?
sexp output_portp(sexp p) { return boolwrap(isOutPort(p)); }

// with-input-from-file
sexp with_input_from_file(sexp p, sexp thunk)
{
    sexp* mark = psp;
    sexp t = save(inport);
    inport = save(open_input_file(p));
    sexp q = save(apply(thunk, 0));
    close_input_port(inport);
    inport = t;
    return lose(mark, q);
}

// with-output-to-file
sexp with_output_to_file(sexp p, sexp thunk)
{
    sexp* mark = psp;
    sexp t = save(outport);
    outport = save(open_output_file(p));
    sexp q = save(apply(thunk, 0));
    close_output_port(outport);
    outport = t;
    return lose(mark, q);
}

// call-with-input-file
sexp call_with_input_file(sexp p, sexp func)
{
    sexp* mark = psp;
    sexp inp = save(open_input_file(p));
    sexp q = save(apply(func, save(cons(inp, 0))));
    close_input_port(inp);
    return lose(mark, q);
}

// call-with-output-file
sexp call_with_output_file(sexp p, sexp func)
{
    sexp* mark = psp;
    sexp oup = save(open_output_file(p));
    sexp q = save(apply(func, save(cons(oup, 0))));
    close_output_port(oup);
    return lose(mark, q);
}

// open-input-string
sexp open_input_string(sexp args)
{
    sexp s = args->car;
    assertString(s);

    int i = 0;
    if (args->cdr)
    {
        assertFixnum(args->cdr->car);
        i = asFixnum(args->cdr->car);
    }

    int j = slen(s);
    if (args->cdr->cdr)
    {
        assertFixnum(args->cdr->cdr->car);
        j = asFixnum(args->cdr->cdr->car);
    }

    if (i < 0 || j <= i)
        error("open-input-string: bad arguments");

    std::stringstream* ss = new std::stringstream();
    InPort* port = (InPort*)save(newcell(INPORT));
    port->avail = 0;
    port->peek = 0;
    port->s = new StrPortStream(*ss, 0);

    int k = 0;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        if (k <= i && i < k+sizeof(t->text))
        {
            for (int m = 0; m < sizeof(t->text); ++m)
            {
                int n = k+m;
                if (n == j)
                    return lose((sexp)port);
                if (i <= n && n < j)
                    ss->put(t->text[m]);
            }
        }
        k += sizeof(t->text);
    }
    return lose((sexp)port);
}

// get-output-string
sexp get_output_string(sexp port)
{
    assertOutPort(port);
    OutPort* p = (OutPort*)port;
    std::stringstream* ss = (std::stringstream*) p->s->streamPointer;
    return newstring(ss->str().c_str());
}

// open-output-string
sexp open_output_string(sexp args)
{
    std::stringstream* ss = new std::stringstream();
    OutPort* p = (OutPort*)newcell(OUTPORT);
    p->s = new StrPortStream(*ss, 0);
    return (sexp)p;
}

// call-with-output-string
sexp call_with_output_string(sexp proc)
{
    sexp* mark = psp;
    sexp port = save(open_output_string(0));
    apply(proc, save(cons(port, 0)));
    return lose(mark, get_output_string(port));
}

// call-with-truncated-output-string
sexp call_with_truncated_output_string(sexp limit, sexp proc)
{
    sexp* mark = psp;
    assertFixnum(limit);
    std::stringstream* ss = new std::stringstream();
    sexp port = save(newcell(OUTPORT));
    OutPort* p = (OutPort*)port;
    p->s = new StrPortStream(*ss, asFixnum(limit));
    apply(proc, save(cons(port, 0)));
    return lose(mark, get_output_string(port));
}

// write-to-string
sexp write_to_string(sexp args)
{
    sexp* mark = psp;
    sexp object = args->car;
    int limit = 0;
    if (args->cdr)
    {
        assertFixnum(args->cdr->car);
        limit = asFixnum(args->cdr->car);
    }
    std::stringstream ss; Ugly ugly(ss); std::set<sexp> seenSet;
    ss << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    display(ss, object, seenSet, ugly, 0, true);
    if (0 == limit) limit = ss.str().length();
    return newstring(ss.str().substr(0, limit).c_str());
}

// vector?
sexp vectorp(sexp v) { return boolwrap(isVector(v)); }

sexp newvector(int len, sexp fill)
{
    Vector* v = (Vector*) save(newcell(VECTOR));
    v->l = len;
    v->e = new sexp[len];
    for (int i = v->l; --i >= 0; v->e[i] = fill) {}
    return lose((sexp)v);
}

// make-vector
sexp make_vector(sexp args)
{
    int len = 0;
    if (args->car && isFixnum(args->car))
        len = asFixnum(args->car);
    sexp fill = 0;
    if (args->cdr && args->cdr->car)
        fill = args->cdr->car;
    return newvector(len, fill);
}

// list->vector
sexp list_vector(sexp list)
{
    sexp* mark = psp;
    save(list);
    int length = 0;
    for (sexp p = list; p; p = p->cdr)
        ++length;
    Vector* v = (Vector*) save(newvector(length, 0));
    int index = 0;
    for (sexp p = list; p; p = p->cdr)
        v->e[index++] = p->car;
    return lose(mark, (sexp)v);
}

void assertVector(sexp v) { if (!isVector(v)) error("not a vector"); }

// vector->list
sexp vector_list(sexp vector)
{
    sexp* mark = psp;
    assertVector(vector);
    save(vector);
    Vector* v = (Vector*)vector;
    int index = v->l;
    sexp list = save(0);
    while (index > 0)
        replace(list = cons(v->e[--index], list));
    return lose(mark, list);
}

// vector-fill
sexp vector_fill(sexp vector, sexp value)
{
    assertVector(vector);
    Vector* v = (Vector*)vector;
    int index = v->l;
    while (index > 0)
        v->e[--index] = value;
    return vector;
}

// vector-length
sexp vector_length(sexp vector)
{
    assertVector(vector);
    return newfixnum(((Vector*)vector)->l);
}

// vector-ref
sexp vector_ref(sexp vector, sexp index)
{
    assertFixnum(index);
    assertVector(vector);
    return ((Vector*)vector)->e[asFixnum(index)];
}

// (vector e0 e1 e2 ...)
sexp vector(sexp args)
{
    sexp* mark = psp;
    save(args);
    int index = 0;
    for (sexp p = args; p; p = p->cdr)
        ++index;
    Vector* v = (Vector*) save(newvector(index, 0));
    index = 0;
    for (sexp p = args; p; p = p->cdr)
        v->e[index++] = p->car;
    return lose(mark, (sexp)v);
}

// vector-set
sexp vector_set(sexp vector, sexp index, sexp value)
{
    assertFixnum(index);
    assertVector(vector);
    Vector* v = (Vector*)vector;
    v->e[asFixnum(index)] = value;
    return voida;
}

// all of these need to be made utf8

// char-alphabetic?
sexp char_alphabeticp(sexp c) { return boolwrap(isChar(c) && isalpha(((Char*)c)->ch)); }

// char->integer
sexp char_integer(sexp c) { assertChar(c); return newfixnum(((Char*)c)->ch); }

// char-ci=?
sexp char_cieqp(sexp p, sexp q) { assertChar(p); assertChar(q); return boolwrap(tolower(((Char*)p)->ch) == tolower(((Char*)q)->ch)); }

// char-ci>=?
sexp char_cigep(sexp p, sexp q) { assertChar(p); assertChar(q); return boolwrap(tolower(((Char*)p)->ch) >= tolower(((Char*)q)->ch)); }

// char-ci>?
sexp char_cigtp(sexp p, sexp q) { assertChar(p); assertChar(q); return boolwrap(tolower(((Char*)p)->ch) >  tolower(((Char*)q)->ch)); }

// char-ci<=?
sexp char_cilep(sexp p, sexp q) { assertChar(p); assertChar(q); return boolwrap(tolower(((Char*)p)->ch) <= tolower(((Char*)q)->ch)); }

// char-ci<?
sexp char_ciltp(sexp p, sexp q) { assertChar(p); assertChar(q); return boolwrap(tolower(((Char*)p)->ch) <  tolower(((Char*)q)->ch)); }

// char=?
sexp char_eqp(sexp p, sexp q) { assertChar(p); assertChar(q); return boolwrap(((Char*)p)->ch == ((Char*)q)->ch); }

// char>=?
sexp char_gep(sexp p, sexp q) { assertChar(p); assertChar(q); return boolwrap(((Char*)p)->ch >= ((Char*)q)->ch); }

// char>?
sexp char_gtp(sexp p, sexp q) { assertChar(p); assertChar(q); return boolwrap(((Char*)p)->ch >  ((Char*)q)->ch); }

// char<=?
sexp char_lep(sexp p, sexp q) { assertChar(p); assertChar(q); return boolwrap(((Char*)p)->ch <= ((Char*)q)->ch); }

// char<?
sexp char_ltp(sexp p, sexp q) { assertChar(p); assertChar(q); return boolwrap(((Char*)p)->ch <  ((Char*)q)->ch); }

// character?
sexp charp(sexp c) { return boolwrap(isChar(c)); }

// char-downcase
sexp char_downcase(sexp c) { assertChar(c); return newcharacter(tolower(((Char*)c)->ch)); }

// integer->char
sexp integer_char(sexp c) { assertFixnum(c); return newcharacter(asFixnum(c)); }

// char-lowercase?
sexp char_lower_casep(sexp c) { return boolwrap(isChar(c) && islower(((Char*)c)->ch)); }

// char-numeric?
sexp char_numericp(sexp c) { return boolwrap(isChar(c) && isdigit(((Char*)c)->ch)); }

// char-upcase
sexp char_upcase(sexp c) { assertChar(c); return newcharacter(toupper(((Char*)c)->ch)); }

// char-uppercase?
sexp char_upper_casep(sexp c) { return boolwrap(isChar(c) && isupper(((Char*)c)->ch)); }

// char-whitespace?
sexp char_whitespacep(sexp c) { return boolwrap(isChar(c) && isspace(((Char*)c)->ch)); }

// save the original termios then modify it for cbreak style input
bool setTermios(struct termios& original, int vmin)
{
    if (tcgetattr(0, &original))
        return false;
    struct termios working;
    working = original;
    working.c_cc[VMIN] = vmin;
    working.c_cc[VTIME] = 0;
    working.c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP | INLCR | IGNCR | ICRNL | IXON);
    working.c_oflag &= ~OPOST;
    working.c_lflag &= ~(ECHO | ECHONL | ICANON | ISIG | IEXTEN);
    working.c_cflag &= ~(CSIZE | PARENB);
    working.c_cflag |= CS8;
    return 0 == tcsetattr(0, TCSANOW, &working);
}

// char-ready?
sexp char_readyp(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);

    InPort* inPort = (InPort*)port;

    if (!inPort->avail && &cinStream == inPort->s)
    {
        struct termios original;
        if (setTermios(original, 0))
        {
            inPort->avail = read(0, &inPort->peek, 1) > 0;
            tcsetattr(0, TCSANOW, &original);
            return boolwrap(inPort->avail);
        }
    }

    return t;
}

// read-char
sexp read_char(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);

    InPort* inPort = (InPort*)port;

    if (inPort->avail)
    {
        inPort->avail = false;
        return newcharacter(inPort->peek);
    }

    if (&cinStream == inPort->s)
    {
        struct termios original;
        if (setTermios(original, 1))
        {
            while (0 == read(0, &inPort->peek, 1)) {}
            tcsetattr(0, TCSANOW, &original);
            return newcharacter(inPort->peek);
        }
    }

    return newcharacter(inPort->s->get());
}

// peek-char
sexp peek_char(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);

    InPort* inPort = (InPort*)port;

    if (inPort->avail)
        return newcharacter(inPort->peek);

    if (&cinStream == inPort->s)
    {
        struct termios original;
        if (setTermios(original, 1))
        {
            while (0 == read(0, &inPort->peek, 1)) {}
            inPort->avail = true;
            tcsetattr(0, TCSANOW, &original);
            return newcharacter(inPort->peek);
        }
        return newcharacter(std::cin.get());
    }

    int c = inPort->s->get();
    inPort->s->unget();
    return newcharacter(c);
}

// write-char
sexp write_char(sexp args)
{
    sexp port = outport;
    if (args)
    {
        assertChar(args->car);
        if (args->cdr)
            assertOutPort(port = args->cdr->car);
    }

    // utf8
    ((OutPort*)port)->s->put(((Char*)(args->car))->ch);

    return voida;
}

sexp achunk(sexp s) { assertString(s); return ((String*)s)->chunks; }

// string<=?
sexp string_lep(sexp p, sexp q) { p=achunk(p); q = achunk(q); return boolwrap(scmp(p, q) <= 0); }

// string<?
sexp string_ltp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return boolwrap(scmp(p, q) <  0); }

// string=?
sexp string_eqp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return boolwrap(scmp(p, q) == 0); }

// string>=?
sexp string_gep(sexp p, sexp q) { p=achunk(p); q = achunk(q); return boolwrap(scmp(p, q) >= 0); }

// string>?
sexp string_gtp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return boolwrap(scmp(p, q) >  0); }

// string-ci-<=?
sexp string_cilep(sexp p, sexp q) { p=achunk(p); q = achunk(q); return boolwrap(scmpi(p, q) <= 0); }

// string-ci<?
sexp string_ciltp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return boolwrap(scmpi(p, q) <  0); }

// string-ci=?
sexp string_cieqp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return boolwrap(scmpi(p, q) == 0); }

// string-ci>=?
sexp string_cigep(sexp p, sexp q) { p=achunk(p); q = achunk(q); return boolwrap(scmpi(p, q) >= 0); }

// string-ci>?
sexp string_cigtp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return boolwrap(scmpi(p, q) >  0); }

// string-ref
sexp string_ref(sexp s, sexp i)
{
    assertString(s);
    assertFixnum(i);

    char* p = sref(s, asFixnum(i));
    if (!p)
        error("string-ref: out of bounds");

    return newcharacter(*p);
}

// string-set!
sexp string_set(sexp s, sexp k, sexp c)
{
    assertString(s);
    assertFixnum(k);
    assertChar(c);

    // utf8
    char* p = sref(s, asFixnum(k));
    if (!p)
        error("string-set!: out of bounds");

    *p = ((Char*)c)->ch;

    return s;
}

// substring
sexp substringf(sexp s)
{
    if (!s || !isString(s->car) || !s->cdr || !isFixnum(s->cdr->car))
        error("substring: bad arguments");

    int i = asFixnum(s->cdr->car);
    int j = slen(s->car);
    if (s->cdr->cdr && isFixnum(s->cdr->cdr->car))
        j = asFixnum(s->cdr->cdr->car);

    s = s->car;

    if (i < 0 || j <= i)
        error("substring: bad arguments");

    char* b = (char*)alloca(j-i+1);

    int k = 0;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        if (k <= i && i < k+sizeof(t->text))
        {
            for (int m = 0; m < sizeof(t->text); ++m)
            {
                int n = k+m;
                if (n == j) {
                    b[n-i] = 0;
                    return newstring(b);
                }
                if (i <= n && n < j)
                    b[n-i] = t->text[m];
            }
        }
        k += sizeof(t->text);
    }

    error("substring: bad arguments");
}

sexp append(sexp p, sexp q)
{
    sexp* mark = psp;
    save(p, q);
    return lose(mark, p ? cons(p->car, save(append(p->cdr, q))) : q);
}

// reverse
sexp reverse(sexp x) { sexp t = 0; while (isCons(x)) { t = cons(car(x), t); x = x->cdr; } return t; }

// eq?
sexp eqp(sexp x, sexp y) { return boolwrap(x == y); }

// =
sexp eqnp(sexp x, sexp y)
{
    if (isRational(x) && isRational(y))
        return boolwrap(asFixnum(x->cdr->car) == asFixnum(y->cdr->car) &&
                        asFixnum(x->cdr->car) == asFixnum(y->cdr->car));
 
    if (isComplex(x) && isComplex(y))
        return boolwrap(asFlonum(x->cdr->car) == asFlonum(y->cdr->car) &&
                        asFlonum(x->cdr->cdr->car) == asFlonum(y->cdr->cdr->car));

    return boolwrap(asFlonum(x) == asFlonum(y));
}

// zero?
sexp zerop(sexp x)
{
    return eqnp(zero, x);
}

// ~ x
sexp complement(sexp x) { return isFixnum(x) ? newfixnum(~asFixnum(x)) : f; }

// all arguments must be fixnums for these logical operations
void assertAllFixnums(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
        if (!isFixnum(p->car))
            error("bitwise ops require fixnum arguments");
}

// x0 & x1 & x2 ...
sexp andf(sexp args)
{
    assertAllFixnums(args);
    long result = ~0;
    for (sexp p = args; p; p = p->cdr)
        result = result & asFixnum(p->car);
    return lose(newfixnum(result));
}

// x0 | x1 | x2 ...
sexp orf(sexp args)
{
    assertAllFixnums(args);
    long result = 0;
    for (sexp p = args; p; p = p->cdr)
        result = result | asFixnum(p->car);
    return lose(newfixnum(result));
}

// x0 ^ x1 ^ x2 ...
sexp xorf(sexp args)
{
    assertAllFixnums(args);
    long result = 0;
    for (sexp p = args; p; p = p->cdr)
        result = result ^ asFixnum(p->car);
    return lose(newfixnum(result));
}

// delay
sexp delayform(sexp exp, sexp env)
{
    return lose(cons(promise, replace(cons(0, replace(cons(0, replace(cons(exp->cdr->car, save(cons(env, 0))))))))));
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

// promise_forced?
sexp promise_forcedp(sexp p)
{
    if (!isPromise(p))
        error("promise-forced?: not a promise");
    return p->cdr->car;
}

// promise-value
sexp promise_value(sexp p)
{
    if (!isPromise(p))
        error("promise-value: not a promise");
    if (!p->cdr->car)
        error("promise not forced yet");
    return p->cdr->cdr->car;
}

// load
sexp load(sexp x)
{
    assertString(x);

    int len = slen(x)+1;

    char *name = sstr((char*)alloca(len), len, x);

    std::cout << ";; load: " << name << std::endl;

    IfsPortStream fin(name, std::ifstream::in);

    if (fin.good())
    {
        while (fin.good())
        {
            sexp input = fin.read();
            if (eof == input)
                break;
            if (f != tracing)
                debug("load", input);
            eval(input, global);
        }
        return t;
    }
    return f;
}

// space
sexp space(sexp args)
{
    sexp port = args ? args->car : outport;
    assertOutPort(port);
    ((OutPort*)port)->s->put(' ');
    return voida;
}

// newline
sexp newline(sexp args)
{
    sexp port = args ? args->car : outport;
    assertOutPort(port);
    ((OutPort*)port)->s->put('\n');
    return voida;
}

// eof-object?
sexp eof_objectp(sexp a) { return boolwrap(eof == a); }

// display
sexp displayf(sexp args)
{
    std::stringstream s; Ugly ugly(s); std::set<sexp> seenSet;
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    display(s, args->car, seenSet, ugly, 0, false);
    ((OutPort*)port)->s->write(s.str().c_str(), s.str().length());
    return voida;
}

// write
sexp writef(sexp args)
{
    std::stringstream s; Ugly ugly(s); std::set<sexp> seenSet;
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    display(s, args->car, seenSet, ugly, 0, true);
    ((OutPort*)port)->s->write(s.str().c_str(), s.str().length());
    return voida;
}

std::ostream& displayChunks(std::ostream& s, sexp exp, bool atom, bool write)
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

    if (isCons(exp))
    {
        if (seenSet.find(exp) != seenSet.end())
            return true;
        seenSet.insert(exp);
        return cyclic(seenSet, exp->car) || cyclic(seenSet, exp->cdr);
    }

    if (isVector(exp)) {
        if (seenSet.find(exp) != seenSet.end())
            return true;
        seenSet.insert(exp);
        Vector* v = (Vector*)exp;
        for (int i = v->l; --i >= 0; )
            if (cyclic(seenSet, v->e[i]))
                return true;
    }

    return false;
}

bool cyclic(sexp exp) { std::set<sexp> seenSet; return cyclic(seenSet, exp); }

// cyclic?
sexp cyclicp(sexp x) { return boolwrap(cyclic(x)); }

// for prettyprinting
int displayLength(sexp exp)
{
    std::stringstream ss; Ugly ugly(ss); std::set<sexp> seenSet;
    ss << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    display(ss, exp, seenSet, ugly, 0, true);
    return ss.str().length();
}

std::ostream& displayList(std::ostream& s, sexp exp, std::set<sexp>& seenSet, Ugly& ugly, int level, bool write)
{
    s << '(';
    level += 2;
    while (exp && seenSet.find(exp) == seenSet.end())
    {
        display(s, exp->car, seenSet, ugly, level+2, write);
        seenSet.insert(exp);
        if (exp->cdr) {
            if (isCons(exp->cdr) && !isClosure(exp->cdr) && !isPromise(exp->cdr) && global != exp->cdr)
            {
                if (seenSet.find(exp->cdr) == seenSet.end())
                {
                    if (write)
                        s << ' ';
                    else
                        ugly.wrap(level, displayLength(exp->cdr->car));
                    exp = exp->cdr;
                }
            } else {
                s << " . ";
                exp = exp->cdr;
                display(s, exp, seenSet, ugly, level+2, write);
                exp = 0;
            }
        } else
            exp = exp->cdr;
    }
    level -= 2;
    s << ')';
    return s;
}

std::ostream& displayVector(std::ostream& s, sexp v, std::set<sexp>& seenSet, Ugly& ugly, int level, bool write)
{
    s << '[';
    level += 2;
    Vector *vv = (Vector*)v;
    for (int i = 0; i < vv->l; ++i)
    {
        if (seenSet.find(vv->e[i]) == seenSet.end())
            display(s, vv->e[i], seenSet, ugly, level+2, write);
        if (i < vv->l-1)
        {
            s << ",";
            if (write)
                s << ' ';
            else
                ugly.wrap(level, displayLength(vv->e[i+1]));
        }
    }
    level -= 2;
    s << ']';
    return s;
}

const char * const character_table[] =
{
    "\000nul",       "\001soh", "\002stx",     "\003etx", "\004eot", "\005enq",    "\006ack", "\007bell",
    "\010backspace", "\011tab", "\012newline", "\013vt",  "\014ff",  "\015return", "\016so",  "\017si",
    "\020dle",       "\021dc1", "\022dc2",     "\023dc3", "\024dc4", "\025nak",    "\026syn", "\027etb",
    "\030can",       "\031em",  "\032sub",     "\033esc", "\034fs",  "\035gs",     "\036rs",  "\037us",
    "\040space",     "\177del", 0
};

std::ostream& displayAtom(std::ostream& s, sexp exp, bool write)
{
    return displayChunks(s, ((Atom*)exp)->body->cdr, true, write);
}

std::ostream& displayString(std::ostream& s, sexp exp, bool write)
{
    return displayChunks(s, ((String*)exp)->chunks, false, write);
}

// used for displaying functions, forms. and closures by name
sexp getName(sexp exp)
{
    for (sexp p = global; p; p = p->cdr)
        if (exp == p->car->cdr)
            return p->car->car;
    return 0;
}

std::ostream& displayFunction(std::ostream& s, sexp exp, bool write)
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

std::ostream& displayNamed(std::ostream& s, const char *kind, sexp exp, bool write)
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

std::ostream& displayChar(std::ostream& s, sexp exp, bool write)
{
    int c = ((Char*)exp)->ch;
    for (int i = 0; character_table[i]; ++i)
        if (c == *character_table[i]) {
            s << "#\\" << 1+character_table[i];
            return s;
        }
    s << "#\\" << ((Char*)exp)->ch;;
    return s;
}

std::ostream& displayRational(std::ostream& s, sexp exp)
{
    s << asFixnum(exp->cdr->car) << '/' << asFixnum(exp->cdr->cdr->car);
    return s;
}

std::ostream& display(std::ostream& s, sexp exp, std::set<sexp>& seenSet, Ugly& ugly, int level, bool write)
{
    if (!exp)
    {
        s << "()";
        return s;
    }
    if (isCons(exp)) {
        bool quoted = false;
        if (isCons(exp->cdr))
        {
            quoted = true;
            sexp p = exp->car;
            if      (quote           == p) s << '\'';
            else if (quasiquote      == p) s <<  '`';
            else if (unquote         == p) s <<  ',';
            else if (unquotesplicing == p) s << ",@";
            else quoted = false;
        }
        if (quoted)
            display(s, exp->cdr->car, seenSet, ugly, level, write);
        else if (global == exp)
            s << "#<global environment>";
        else if (isRational(exp))
            displayRational(s, exp);
        else if (isClosure(exp))
            displayNamed(s, "closure", exp, write);
        else if (isPromise(exp))
            displayNamed(s, "promise", exp, write);
        else if (isComplex(exp)) {
            if (isRational(exp->cdr->car))
                displayRational(s, exp->cdr->car);
            else
                s << asFlonum(exp->cdr->car);
            double im = asFlonum(exp->cdr->cdr->car);
            if (im > 0.0)
                s << '+';
            if (im)
            {
                if (isRational(exp->cdr->cdr->car))
                    displayRational(s, exp->cdr->cdr->car);
                else
                    s << asFlonum(exp->cdr->cdr->car);
                s << 'i';
            }
        } else if (seenSet.find(exp) == seenSet.end())
            displayList(s, exp, seenSet, ugly, level, write);
        return s;
    }

    switch (((Stags*)exp)->stags)
    {
    default:      error("display: unknown object");
    case FLOAT: 
    case DOUBLE:  s << asFlonum(exp);                                       break;
    case CHUNK:   s << "#<chunk>";                                          break;
    case FIXNUM:  s << asFixnum(exp);                                       break;
    case STRING:  displayString(s, exp, write);                             break;
    case ATOM:    displayAtom(s, exp, write);                               break;
    case FUNCT:   displayFunction(s, exp, write);                           break;
    case FORM:    displayNamed(s, "form", exp, write);                      break;
    case INPORT:  displayNamed(s, "input", exp, write);                     break;
    case OUTPORT: displayNamed(s, "output", exp, write);                    break;
    case CHAR:    displayChar(s, exp, write);                               break;
    case VECTOR:  if (seenSet.find(exp) == seenSet.end())
                    displayVector(s, exp, seenSet, ugly, level, write);
    }
    return s;
}

// usual way to see what is happening
void debug(const char *label, sexp exp)
{
    std::stringstream s; Ugly ugly(s); std::set<sexp> seenSet;
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    s << label << ": ";
    if (voida == exp)
        s << "void";
    else
        display(s, exp, seenSet, ugly, 0, true);
    s << std::endl;
    std::cout.write(s.str().c_str(), s.str().length());
}

// string->symbol
sexp string_symbol(sexp x)
{
    assertString(x);
    sexp y = save(string_copy(x));
    return lose(intern(newcell(ATOM, replace(cons(0, (((String*)y)->chunks)))))); }

// symbol->string
sexp symbol_string(sexp x)
{
    assertAtom(x);
    sexp* mark = psp;
    return lose(mark, string_copy(save(newcell(STRING, ((Atom*)save(x))->body->cdr))));
}

// string->number (actually we will convert arbitrary s-expressions)
sexp string_number(sexp exp)
{
    std::stringstream s;
    displayChunks(s, ((String*)exp)->chunks, false, false);
    return read(s, 0);
}

// string->list
sexp string_list(sexp x)
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
        p = lose(lose(cons(save(newcharacter(*q)), save(p))));

    return p;
}

// list->string
sexp list_string(sexp s)
{
    if (!s)
        return newcell(STRING, 0);

    sexp* mark = psp;
    save(s);
    Chunk* r = (Chunk*) save(newcell(CHUNK));
    sexp p = replace(cons((sexp)r, 0));
    sexp q = p;

    int i = 0;
    for ( ; s; s = s->cdr)
    {
        assertChar(s->car);

        // utf8
        r->text[i++] = ((Char*)(s->car))->ch;

        if (i == sizeof(r->text))
        {
            i = 0;
            r = (Chunk*) save(newcell(CHUNK));
            q = q->cdr = lose(cons((sexp)r, 0));
        }
    }

    while (i < sizeof(r->text))
        r->text[i++] = 0;

    return lose(mark, newcell(STRING, p));
}

// string
sexp string(sexp args) { return list_string(args); }

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

    if (!x || !y || isAtom(x) || isAtom(y))
        return false;

    if (isCons(x) && isCons(y))
    {
        if (seenx.find(x) != seenx.end() && seeny.find(y) != seeny.end())
            return true;
        seenx.insert(x);
        seeny.insert(y);
        return eqvb(seenx, seeny, x->car, y->car) && eqvb(seenx, seeny, x->cdr, y->cdr);
    }

    if (shortType(x) != shortType(y))
        return false;

    switch (shortType(x)) 
    {
    case FLOAT : return ((Float*)x)->flonum  == ((Float*)y)->flonum;
    case DOUBLE: return ((Double*)x)->flonum == ((Double*)y)->flonum;
    case CHUNK : return 0 == scmp(x, y);
    case STRING: return 0 == scmp(((String*)x)->chunks, ((String*)y)->chunks);
    case FIXNUM: return ((Fixnum*)x)->fixnum == ((Fixnum*)y)->fixnum;
    case VECTOR: return cmpv(seenx, seeny, x, y);
    case CHAR:   return ((Char*)x)->ch == ((Char*)y)->ch;
    default:     return 0;
    }
}

// eqv?
sexp eqvp(sexp x, sexp y) { std::set<sexp> seenx; std::set<sexp> seeny; return boolwrap(eqvb(seenx, seeny, x, y)); }

// equal?
sexp equalp(sexp x, sexp y) { std::set<sexp> seenx; std::set<sexp> seeny; return boolwrap(eqvb(seenx, seeny, x, y)); }

// show bindings since ref, for debugging
sexp envhead(sexp env, sexp ref)
{
    return (env == 0 || env == ref) ? 0 : cons(cons(env->car->car, env->car->cdr), envhead(env->cdr, ref));
}

// update all the closures in an environment so they reference
// that environment instead of earlier ones for init.ss
void fixenvs(sexp env)
{
    for (sexp e = env; e; e = e->cdr)
        if (isClosure(e->car->cdr))
            e->car->cdr->cdr->cdr->car = env;
}

static char errorBuffer[128];   // used by get and set

// error messages from set! and get
void lookup_error(const char* msg, sexp p)
{
    strcpy(errorBuffer, msg);
    int len = 0;
    for (sexp q = ((Atom*)p)->body->cdr; q; q = q->cdr)
    {
        int i = 0;
        Chunk* t = (Chunk*)(q->car);
        while (i < sizeof(t->text) && t->text[i])
            ++i;
        len += i;
    }
    if (len > sizeof(errorBuffer)-strlen(msg))
        len = sizeof(errorBuffer)-strlen(msg);
    char *r = errorBuffer+strlen(msg);
    *r++ = '"';
    for (sexp q = ((Atom*)p)->body->cdr; q; q = q->cdr)
    {
        if (r >= errorBuffer+sizeof(errorBuffer)-1)
            break;
        Chunk* t = (Chunk*)(q->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; *r++ = t->text[i++]) {}
    }
    *r++ = '"';
    *r++ = 0;
    error(errorBuffer);
}

// an Atom has a value cell used as an environment cache
static inline sexp value_put(sexp p, sexp v)
{
    return ((Atom*)p)->body->car = v;
}

// lookups in the global environment use the value cell
sexp get_value(sexp p, sexp env)
{
    sexp v = ((Atom*)p)->body->car;
    if (v)
        return v;
    for (sexp q = env; q; q = q->cdr)
        if (q->car && p == q->car->car)
            return value_put(p, q->car->cdr);

    lookup_error("unbound: get value ", p);
}

// lookups in the global environment use the value cell
sexp set_value(sexp p, sexp r, sexp env)
{
    for (sexp q = env; q; q = q->cdr)
        if (p == q->car->car)
        {
            q->car->cdr = value_put(p, r);
            return voida;
        }

    lookup_error("unbound: set value ", p);
}

// define
sexp define(sexp p, sexp r)
{
    for (sexp q = global; q; q = q->cdr)
        if (p == q->car->car)
        {
            q->car->cdr = value_put(p, r);
            return voida;
        }
    global = cons(save(cons(p, r)), global);
    value_put(p, r);
    return lose(voida);
}

// undefine
sexp undefine(sexp p)
{
    if (p == global->car->car)
        global = global->cdr;
    else
        for (sexp q = global; q; q = q->cdr)
            if (q->cdr && p == q->cdr->car)
            {
                q->cdr = q->cdr->cdr;
                break;
            }
    value_put(p, 0);
    return voida;
}

// form?
sexp formp(sexp p)
{
    return boolwrap(isForm(p));
}

// function?
sexp functionp(sexp p)
{
    return boolwrap(isFunct(p));
}

// bound?
sexp boundp(sexp p, sexp env)
{
    for (sexp q = env; q; q = q->cdr)
        if (q->car && p->cdr->car == q->car->car)
            return t;
    return f;
}

// retrieve the value of a variable in an environment
sexp get(sexp p, sexp env)
{
    assertAtom(p);
    for (sexp q = env; q; q = q->cdr)
        if (cache && global == q)
            // global bindings are cached in the Atom's value cell
            return get_value(p, global);
        else if (q->car && p == q->car->car)
            return q->car->cdr;

    lookup_error("unbound: get ", p);
}

// set!
sexp set(sexp p, sexp r, sexp env)
{
    assertAtom(p);
    for (sexp q = env; q; q = q->cdr)
        if (cache && global == q)
            // global bindings are cached in the Atom's value cell
            return set_value(p, r, global);
        else if (p == q->car->car)
        {
            q->car->cdr = r;
            return voida;
        }

    lookup_error("unbound: set ", p);
}

// evaluate a list of arguments in an environment
sexp evlis(sexp p, sexp env)
{
    sexp* mark = psp;
    save(p, env);
    return p ? lose(mark, cons(save(eval(p->car, env)), save(evlis(p->cdr, env)))) : 0;
}

// associate a list of formal parameters and actual parameters in an environment
sexp assoc(sexp formals, sexp actuals, sexp env)
{
    sexp* mark = psp;
    save(actuals, formals, env);
    if (!isCons(formals))
        return lose(mark, cons(save(cons(formals, actuals)), env));
    if (!actuals)
        return lose(mark, cons(save(cons(formals->car, voida)),
                               save(assoc(formals->cdr, actuals, env))));
    return lose(mark, cons(save(cons(formals->car, actuals->car)),
                           save(assoc(formals->cdr, actuals->cdr, env))));
}

// environment
sexp environment(sexp exp, sexp env) { return global; }

// evaluate a list of forms, returning the last value
sexp tailforms(sexp exp, sexp env)
{
    if (!exp)
        return voida;
    sexp* mark = psp;
    save(exp, env);
    while (exp->cdr)
    {
        if (definea == exp->car->car)
            env = replace(nesteddefine(exp->car, env));
        else
            eval(exp->car, env);
        exp = exp->cdr;
    }
    return lose(mark, eval(exp->car, env));
}

// begin
sexp begin(sexp exp, sexp env)
{
    return tailforms(exp->cdr, env);
}

// while
sexp whileform(sexp exp, sexp env)
{
    sexp* mark = psp;
    save(exp, env);
    exp = exp->cdr;
    sexp v = save(0);
    while (f != eval(exp->car, env))
        v = replace(tailforms(exp->cdr, env));
    return lose(mark, v);
}

/*
 * (cond (test1 val1)
 *       (test2 val2)
 *       ...
 *       (else valn))
 *
 * the first true test returns its corresponding val
 */
sexp cond(sexp exp, sexp env)
{
    for (sexp p = exp->cdr; p; p = p->cdr)
        if (elsea == p->car->car || f != eval(p->car->car, env))
            return tailforms(p->car->cdr, env);
    return voida;
}

// lambda creates a closure
sexp lambdaform(sexp exp, sexp env)
{
    return lose(cons(closure, replace(cons(exp, save(cons(env, 0))))));
}

/*
 * rewrite
 * (define (foo . x) body ..)       as (define foo (lambda x body ..)
 * (define (foo x)   body ..)       as (define foo (lambda (x) body ..))
 * (define (foo a b c . x) body ..) as (define foo (lambda (a b c . x) body ..))
 */
sexp nesteddefine(sexp p, sexp env)
{
    sexp* mark = psp;
    if (isCons(p->cdr->car))
    {
        // (define (foo ...)
        sexp k = p->cdr->car->car;
        value_put(k, 0);
        sexp v = replace(cons(lambda, save(cons(p->cdr->car->cdr, p->cdr->cdr))));
        // v is the transformed definition (lambda (x) ...) or (lambda (x y . z) ...)
        v = save(lambdaform(v, env));
        // v is a closure (closure exp env)
        for (sexp q = env; q; q = q->cdr)
            if (k == q->car->car)
            {
                q->car->cdr = v;
                return lose(mark, env);
            }
        // update the closure definition to include the one we just made
        return lose(mark, v->cdr->cdr->car = cons(save(cons(p->cdr->car->car, save(v))), env));
    } else {
        sexp k = p->cdr->car;
        value_put(k, 0);
        for (sexp q = env; q; q = q->cdr)
            if (k == q->car->car)
            {
                q->car->cdr = eval(p->cdr->cdr->car, env);
                return lose(mark, env);
            }
        return lose(mark, cons(replace(cons(p->cdr->car, save(eval(p->cdr->cdr->car, env)))), env));
    }
}

// top level define sets global
sexp defineform(sexp p, sexp env)
{
    sexp e = nesteddefine(p, env);
    if (global == env)
        global = e;
    return voida;
}

// atoms
sexp atomsf(sexp args) { return atoms; }

// quote
sexp quoteform(sexp exp, sexp env) { return exp->cdr->car; }

// unquote
sexp unquoteform(sexp exp, sexp env)
{
    sexp* mark = psp;
    if (!exp || !isCons(exp))
        return exp;
    if (unquote == exp->car && isCons(exp->cdr))
        return eval(exp->cdr->car, env);
    if (exp->car && unquotesplicing == exp->car->car)
        return lose(mark, replace(append(save(eval(exp->car->cdr->car, env)),
                                         save(unquoteform(exp->cdr, env)))));
    return lose(mark, cons(save(unquoteform(exp->car, env)),
                           save(unquoteform(exp->cdr, env))));
}

// quasiquote
sexp quasiquoteform(sexp exp, sexp env) { return unquoteform(exp->cdr->car, env); }

// read
sexp readf(sexp args) { sexp port = inport; if (args) assertInPort(port = args->car); return ((InPort*)port)->s->read(); }

// scan
sexp scanff(sexp args) { sexp port = inport; if (args) assertInPort(port = args->car); return ((InPort*)port)->s->scan(); }

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
    exp = exp->cdr;
    if (!exp->cdr)
        error("if: missing consequent");
    if (f != eval(exp->car, env))
        return eval(exp->cdr->car, env);
    exp = exp->cdr;
    if (exp->cdr)
        return eval(exp->cdr->car, env);
    return voida;
}

// (when predicate form..)
sexp whenform(sexp exp, sexp env)
{
    exp = exp->cdr;
    if (!exp)
        error("when: missing predicate");
    if (!exp->cdr)
        error("when: missing consequents");
    if (f != eval(exp->car, env))
        return tailforms(exp->cdr, env);
    return voida;
}

// (unless predicate form..)
sexp unlessform(sexp exp, sexp env)
{
    exp = exp->cdr;
    if (!exp)
        error("when: missing predicate");
    if (!exp->cdr)
        error("when: missing consequents");
    if (f == eval(exp->car, env))
        return tailforms(exp->cdr, env);
    return voida;
}

// (case key ((k1 k2 ..) v1) ((k5 k6 ..) v2) (else v3))
sexp caseform(sexp exp, sexp env)
{
    sexp* mark = psp;

    exp = exp->cdr;

    if (!exp)
        error("case: missing key");

    sexp key = eval(exp->car, env);

    sexp r = save(voida);

    for (exp = exp->cdr; exp; exp = exp->cdr)
    {
        if (elsea == exp->car->car)
            return tailforms(exp->cdr, env);

        for (sexp p = exp->car->car; p; p = p->cdr)
            if (f != eqvp(key, p->car))
                return tailforms(exp->car->cdr, env);
    }

    return lose(voida);
}

/*
 * (set! name value) alters an existing binding
 */
sexp setform(sexp exp, sexp env)
{
    exp = exp->cdr;
    return lose(set(exp->car, save(eval(exp->cdr->car, env)), env));
}

sexp names(sexp bs)
{
    return bs ? lose(replace(cons(bs->car->car, save(names(bs->cdr))))) : 0;
}

sexp values(sexp bs, sexp env)
{
    return bs ? lose(lose(cons(save(eval(bs->car->cdr->car, env)), save(values(bs->cdr, env))))) : 0;
}

// let
sexp let(sexp exp, sexp env)
{
    sexp* mark = psp;
    save(exp);
    sexp e = save(env);
    exp = exp->cdr;
    if (isAtom(exp->car))
    {
        // (let name ((var val) (var val) ..) body )
        sexp l = replace(cons(lambda, replace(cons(save(names(exp->cdr->car)), exp->cdr->cdr))));
        sexp c = replace(cons(closure, replace(cons(l, save(cons(env, 0))))));
        c->cdr->cdr->car = e = replace(cons(save(cons(exp->car, c)), e));
        return lose(mark, apply(e->car->cdr, save(values(exp->cdr->car, e))));
    }
    // (let ((var val) (var val) ..) body )
    for (sexp v = exp->car; v; v = v->cdr)
        e = save(cons(save(cons(v->car->car, save(eval(v->car->cdr->car, env)))), e));
    return lose(mark, tailforms(exp->cdr, e));
}

// (let* ((var val) (var val) ..) body )
sexp letstar(sexp exp, sexp env)
{
    sexp* mark = psp;
    save(exp);
    sexp e = save(env);
    exp = exp->cdr;
    for (sexp v = exp->car; v; v = v->cdr)
        e = save(cons(save(cons(v->car->car, save(eval(v->car->cdr->car, e)))), e));
    return lose(mark, tailforms(exp->cdr, e));
}

// (letrec ((var val) (var val) ..) body )
sexp letrec(sexp exp, sexp env)
{
    sexp* mark = psp;
    save(exp);
    sexp e = save(env);
    exp = exp->cdr;
    for (sexp v = exp->car; v; v = v->cdr)
        e = save(cons(save(cons(v->car->car, v->car->cdr->car)), e));
    for (sexp v = exp->car; v; v = v->cdr)
        set(v->car->car, eval(v->car->cdr->car, e), e);
    return lose(mark, tailforms(exp->cdr, e));
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
    save(exp);
    sexp e = save(env);
    exp = exp->cdr;
    // bind all the variables to their values
    for (sexp v = exp->car; v; v = v->cdr)
        e = save(cons(save(cons(v->car->car, v->car->cdr->car)), e));
    sexp s = save(voida);
    for (;;)
    {
        // if any test succeeds, return s
        for (sexp t = exp->cdr->car; t; t = t->cdr)
            if (f != eval(t->car, e))
                return lose(mark, s);

        // evaluate each body expression
        s = replace(tailforms(exp->cdr->cdr, e));

        // step each variable
        for (sexp v = exp->car; v; v = v->cdr)
            set(v->car->car, eval(v->car->cdr->cdr->car, e), e);
    }
}

// apply
sexp apply(sexp fun, sexp args)
{
    sexp* mark = psp;
    save(fun, args);

    if (false && f != tracing)
    {
        debug("apply-fun", fun);
        debug("apply-args", args);
    }

    if (isFunct(fun))
    {
        switch (arity(fun))
        {
        default: error("unsupported arity");
        case 0: return lose(mark, (*(Varargp)((Funct*)fun)->funcp)(args));
        case 1: return lose(mark, (*(Oneargp)((Funct*)fun)->funcp)(args ? args->car : voida));
        case 2: return lose(mark, (*(Twoargp)((Funct*)fun)->funcp)(args ? args->car : voida,
                                                                   args && args->cdr ? args->cdr->car : voida));
        case 3: return lose(mark, (*(Threeargp)((Funct*)fun)->funcp)(args ? args->car : voida,
                                                                     args && args->cdr ? args->cdr->car : voida,
                                                                     args && args->cdr && args->cdr->cdr ? args->cdr->cdr->car : voida));
        }
    }

    if (isClosure(fun))
    {
        fun          = fun->cdr;
        sexp env     = fun->cdr->car;
        sexp fcc     = fun->car->cdr;

        if (!fcc->car) {
            // fun->cdr->car = (lambda () foo)
        } else if (isAtom(fcc->car)) {
            // fun->cdr->car = (lambda s foo)
            env = replace(cons(save(cons(fcc->car, args)), env));
        } else {
            // fun->cdr->car = (lambda (n) (car x))
            env = save(assoc(fcc->car, args, env));
        }

        return lose(mark, tailforms(fcc->cdr, env));
    }

    error("apply bad function");

    return voida;
}

// (rational numerator denominator)
sexp rationalform(sexp exp, sexp env) { assertRational(exp); return exp; }

// (complex real imaginary)
sexp complexform(sexp exp, sexp env) { assertComplex(exp); return exp; }

// (promise forced value exp env)
sexp promiseform(sexp exp, sexp env) { assertPromise(exp); return exp; }

/*
 * malformed constructs will fail without grace
 */
sexp eval(sexp p, sexp env)
{
    sexp* mark = psp;
    if (f != tracing)
    {
        ++indent;
        std::stringstream s; Ugly ugly(s); std::set<sexp> seenSet;
        s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
        s << "eval:";
        for (int i = indent; --i >= 0; s << ' ') {}
        if (voida == p)
            s << "void";
        else
            display(s, p, seenSet, ugly, 0, true);
        s << " ==> ";
        if (!p)
            error("invalid: ()");
        if (f == p || t == p || (OTHER & shortType(p)) && shortType(p) > ATOM)
            {}
        else if (isAtom(p))
            p = get(p, env);
        else
        {
            save(p, env);
            sexp fun = save(eval(p->car, env));
            if (isForm(fun))
                p = save((*((Form*)fun)->formp)(p, env));
            else
                p = save(apply(fun, save(evlis(p->cdr, env))));
        }
        if (voida == p)
            s << "void";
        else
            display(s, p, seenSet, ugly, 0, true);
        s << std::endl;
        std::cout.write(s.str().c_str(), s.str().length());
        --indent;
        return lose(mark, p);
    } else {
        if (!p)
            error("invalid: ()");
        if (f == p || t == p || (OTHER & shortType(p)) && shortType(p) > ATOM)
            return p;
        if (isAtom(p))
            return get(p, env);
        save(p, env);
        sexp fun = save(eval(p->car, env));
        if (isForm(fun))
            return lose(mark, (*((Form*)fun)->formp)(p, env));
        return lose(mark, apply(fun, save(evlis(p->cdr, env))));
    }
}

/*
 * read Chunks terminated by some character or eof
 */
sexp readChunks(std::istream& fin, const char *ends)
{
    sexp* mark = psp;
    Chunk* r = (Chunk*) save(newcell(CHUNK));
    sexp p = replace(cons((sexp)r, 0));
    sexp q = p;

    for (int i = 0; ; )
    {
        int c = fin.get();

        if (c < 0 || strchr(ends, c))
        {
            while (i < sizeof(r->text))
                r->text[i++] = 0;
            fin.unget();
            return lose(mark, p);
        }

        if ('\\' == c)
            c = decodeEscape(fin.get());

        r->text[i++] = c;

        if (i == sizeof(r->text))
        {
            i = 0;
            r = (Chunk*) save(newcell(CHUNK));
            q = q->cdr = lose(cons((sexp)r, 0));
        }
    }
}

// ignore white space and comments
int whitespace(std::istream& fin, int c)
{
    if (c > 0)
    {
        while (0 <= c && strchr(" \t\r\n", c))
            c = fin.get();

        while (';' == c)
        {
            while (0 <= c && '\n' != c)
                c = fin.get();
            while (0 <= c && strchr(" \t\r\n", c))
                c = fin.get();
        }
    }

    return c;
}

enum NumStatus { NON_NUMERIC, FIXED, RATIONAL, FLOATING, COMPLEX };

// scan a number from fin, copy it to s, set status, return next character
int scanNumber(std::stringstream& s, std::istream& fin, NumStatus& status)
{
    int c = fin.get();
    status = NON_NUMERIC;
    while (isspace(c))
        c = fin.get();
    if ('-' == c)
        { s.put(c); c = fin.get(); }
    while (isdigit(c))
        { status = FIXED; s.put(c); c = fin.get(); }
    if ('.' == c)
        { status = FLOATING; s.put(c); c = fin.get(); }
    while (isdigit(c))
        { status = FLOATING; s.put(c); c = fin.get(); }

    if (status > NON_NUMERIC && ('e' == c || 'E' == c))
    {
        status = NON_NUMERIC;
        s.put(c);
        c = fin.get();
        if ('-' == c) {
            s.put(c);
            c = fin.get();
        } else if ('+' == c) {
            s.put(c);
            c = fin.get();
        }
        while (isdigit(c))
        {
            status = FLOATING;
            s.put(c);
            c = fin.get();
        }
    }

    if (status == FIXED && '/' == c)
    {
        s.put(c);
        c = fin.get();
        if ('-' == c)
        {
            s.put(c);
            c = fin.get();
        }
        while (isdigit(c))
            { status = RATIONAL; s.put(c); c = fin.get(); }
    }

    fin.unget();
    return c;
}

/*
 * read an atom, number or string from the input stream
 */
sexp scan(std::istream& fin);

sexp scans(std::istream& fin)
{
    sexp* mark = psp;

    std::stringstream s;

    int c = whitespace(fin, fin.get());

    if (c < 0)
        return eof;

    switch (c)
    {
    case '(':  return lparen;
    case '.':  return dot;
    case ')':  return rparen;
    case '\'': return qchar;
    case '`':  return tick;
    case '[':  return lbracket;
    case ']':  return rbracket;
    case ',':  c = fin.get();
               if ('@' != c) {
                    fin.unget();
                    return comma;
               } else
                   return commaat;
    case '#':  c = fin.get();
               switch (c)
               {
               case 'f': return f;
               case 't': return t;
               case '\\':
                    c = fin.get();
                    do
                        { s.put(c); c = fin.get(); }
                    while (0 <= c && !isspace(c) && ')' != c && ']' !=c && ',' != c);
                    fin.unget();
                    const char* buf = s.str().c_str();
                    for (int i = 0; character_table[i]; ++i)
                        if (!strcmp(buf, 1+character_table[i]))
                            return newcharacter(*character_table[i]);
                    return newcharacter(*buf);
                }
    case '-':
        c = fin.get();
        if ('.' == c || isdigit(c))
            s.put('-');
        else
            { fin.unget(); return minus; } 
    }

    fin.unget();

    NumStatus status, rstatus, istatus;

    c = scanNumber(s, fin, rstatus);

    if (NON_NUMERIC < rstatus && ('+' == c || '-' == c))
    {
        s << (char)fin.get();
        c = scanNumber(s, fin, istatus);
        if ('i' == c)
        {
            s << (char)fin.get();
            status = COMPLEX;
        }
    }
    else if (NON_NUMERIC < status && '@' == c)
    {
        s << (char)fin.get();
        c = scanNumber(s, fin, istatus);
        status = COMPLEX;
    } else
        status = rstatus;

    if (COMPLEX == status)
    {
        sexp real, imag;

        if (RATIONAL == rstatus)
        {
            long rnum, rden;
            s >> rnum;
            s.get();    // /
            s >> rden;
            real = save(rational_reduce(rnum, rden));
        } else
            { double re; s >> re; real = save(newflonum(re)); }

        c = s.get();    // +,-,@

        if (RATIONAL == istatus)
        {
            long inum, iden;
            s >> inum;
            s.get();    // /
            s >> iden;
            imag = save(rational_reduce(inum, iden));
        } else
            { double im; s >> im; imag = save(newflonum(im)); }

        switch (c)
        {
        case '+':
            return lose(mark, make_complex(real, imag));
        case '-':
            return lose(mark, make_complex(real, save(unineg(imag))));
        case '@':
            double r = isRational(real) ? rat2real(real) : asFlonum(real);
            double theta = isRational(imag) ? rat2real(imag) : asFlonum(imag);
            return lose(mark, make_complex(save(newflonum(r * cos(theta))), save(newflonum(r * sin(theta)))));
        }
    }

    if (FIXED == status)
        { long num; s >> num; return newfixnum(num); }

    if (FLOATING == status)
        { double re; s >> re; return newflonum(re); }

    if (RATIONAL == status)
        { long num, den; s >> num; s.get(); s >> den; return newrational(num, den); }

    if ('"' != c)
        return lose(mark, intern(save(newcell(ATOM, replace(cons (0, save(readChunks(fin, "( )[,]\t\r\n"))))))));

    c = fin.get();
    sexp r = newcell(STRING, save(readChunks(fin, "\"")));
    (void)fin.get();  // read the " again
    return lose(mark, r);
}

// stub to enable tracing of scans()
sexp scan(std::istream& fin) { sexp r = scans(fin); if (f != tracing) debug("scan", r); return r; }

// finish reading a list
sexp readTail(std::istream& fin, int level)
{
    sexp q = read(fin, level);
    if (rparen == q)
        return 0;
    if (eof == q)
        return 0;
    if (dot == q)
        return readTail(fin, level)->car;
    return lose(cons(q, save(readTail(fin, level))));
}

// finish reading a vector
sexp readVector(std::istream& fin, int level)
{
    sexp q = 0;
    sexp* mark = psp;
    for (;;)
    {
        sexp s = save(read(fin, level));
        if (eof == s)
            return lose(mark, 0);
        if (rbracket == s)
            return lose(mark, list_vector(save(reverse(q))));
        while (unquote == s->car)
            s = s->cdr->car;
        q = replace(cons(s, q));
        s = scan(fin);
        if (rbracket == s)
            return lose(mark, list_vector(save(reverse(q))));
        if (comma != s)
            error("comma expected in vector");
    }
}

/*
 * read an s-expression
 */
sexp read(std::istream& fin, int level)
{
    sexp* mark = psp;
    sexp p = scan(fin);
    if (lparen == p)
        return readTail(fin, level+1);
    if (lbracket == p)
        return readVector(fin, level+1);
    if (qchar == p)
        return lose(mark, cons(quote, save(cons(save(read(fin, level)), 0))));
    if (tick == p)
        return lose(mark, cons(quasiquote, save(cons(save(read(fin, level)), 0))));
    if (comma == p)
        return lose(mark, cons(unquote, save(cons(save(read(fin, level)), 0))));
    if (commaat == p)
        return lose(mark, cons(unquotesplicing, save(cons(save(read(fin, level)), 0))));
    if (level == 0 && (rbracket == p || rparen == p))
        error("error: an s-expression cannot begin with ')' or ']'");
    return p;
}

// construct an atom and keep a unique copy
sexp atomize(const char *s) { return newatom(s, 0); }

// the first interrupt will stop everything. the second will exit.
void intr_handler(int sig, siginfo_t *si, void *ctx)
{
    if (killed++)
        exit(0);
    if (gcstate)
        ++gcstate;
    else if (SIGINT == sig)
        error("SIGINT");
}

// do a traceback upon a segmentation violation
void segv_handler(int sig, siginfo_t *si, void *ctx)
{
    std::cout << std::endl;
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

        std::cout << ++n
                  << " 0x" << std::hex << (void*)ip
                  << " sp=0x" << (void*)sp << ' '
                  << name << " + 0x" << static_cast<uintptr_t>(off)
                  << std::dec << std::endl;

        if ( name != symbol )
          free(name);
    }
#endif
    exit(0);
}

struct FuncTable {
    const char* name;
    short       arity;
    void*       funcp;
} funcTable[] = {
    { "&",                                 0, (void*)andf },
    { "|",                                 0, (void*)orf },
    { "+",                                 0, (void*)uniadd },
    { "/",                                 0, (void*)unidiv },
    { "%",                                 0, (void*)unimod },
    { "*",                                 0, (void*)unimul },
    { "-",                                 0, (void*)unisub },
    { "^",                                 0, (void*)xorf },
    { "~",                                 1, (void*)complement },
    { "=",                                 2, (void*)eqnp },
    { ">=",                                2, (void*)gep },
    { ">",                                 2, (void*)gtp },
    { "<=",                                2, (void*)lep },
    { "<<",                                2, (void*)lsh },
    { "<",                                 2, (void*)ltp },
    { ">>",                                2, (void*)rsh },
    { "acos",                              1, (void*)acosff },
    { "angle",                             1, (void*)angle },
    { "append",                            2, (void*)append },
    { "apply",                             2, (void*)apply },
    { "asin",                              1, (void*)asinff },
    { "atan",                              1, (void*)atanff },
    { "atan2",                             2, (void*)atan2ff },
    { "atom?",                             1, (void*)atomp },
    { "atoms",                             0, (void*)atomsf },
    { "boolean?",                          1, (void*)booleanp },
    { "call-with-input-file",              2, (void*)call_with_input_file },
    { "call-with-output-file",             2, (void*)call_with_output_file },
    { "call-with-output-string",           1, (void*)call_with_output_string },
    { "call-with-truncated-output-string", 2, (void*)call_with_truncated_output_string },
    { "car",                               1, (void*)car },
    { "cdr",                               1, (void*)cdr },
    { "ceiling",                           1, (void*)ceilingff },
    { "char?",                             1, (void*)charp },
    { "char=?",                            2, (void*)char_eqp },
    { "char>=?",                           2, (void*)char_gep },
    { "char>?",                            2, (void*)char_gtp },
    { "char<=?",                           2, (void*)char_lep },
    { "char<?",                            2, (void*)char_ltp },
    { "char-alphabetic?",                  1, (void*)char_alphabeticp },
    { "char-ci=?",                         2, (void*)char_cieqp },
    { "char-ci>=?",                        2, (void*)char_cigep },
    { "char-ci>?",                         2, (void*)char_cigtp },
    { "char-ci<=?",                        2, (void*)char_cilep },
    { "char-ci<?",                         2, (void*)char_ciltp },
    { "char-downcase",                     1, (void*)char_downcase },
    { "char->integer",                     1, (void*)char_integer },
    { "char-lower-case?",                  1, (void*)char_lower_casep },
    { "char-numeric?",                     1, (void*)char_numericp },
    { "char-ready?",                       0, (void*)char_readyp },
    { "char-upcase",                       1, (void*)char_upcase },
    { "char-upper-case?",                  1, (void*)char_upper_casep },
    { "char-whitespace?",                  1, (void*)char_whitespacep },
    { "close-input-port",                  1, (void*)close_input_port },
    { "close-output-port",                 1, (void*)close_output_port },
    { "closure?",                          1, (void*)closurep },
    { "complex?",                          1, (void*)complexp },
    { "cons",                              2, (void*)cons },
    { "cos",                               1, (void*)cosff },
    { "cosh",                              1, (void*)coshff },
    { "current-input-port",                0, (void*)current_input_port },
    { "current-output-port",               0, (void*)current_output_port },
    { "cyclic?",                           1, (void*)cyclicp },
    { "diff",                              2, (void*)diff },
    { "display",                           0, (void*)displayf },
    { "eof-object?",                       1, (void*)eof_objectp },
    { "eq?",                               2, (void*)eqp },
    { "equal?",                            2, (void*)equalp },
    { "eqv?",                              2, (void*)eqvp },
    { "eval",                              2, (void*)eval },
    { "exact?",                            1, (void*)exactp },
    { "exact->inexact",                    1, (void*)exact_inexact },
    { "exp",                               1, (void*)expff },
    { "floor",                             1, (void*)floorff },
    { "force",                             1, (void*)force },
    { "form?",                             1, (void*)formp },
    { "function?",                         1, (void*)functionp },
    { "gc",                                0, (void*)gc },
    { "gcd",                               2, (void*)gcdf },
    { "get-output-string",                 1, (void*)get_output_string },
    { "inexact?",                          1, (void*)inexactp },
    { "inexact->exact",                    1, (void*)inexact_exact },
    { "input-port?",                       1, (void*)input_portp },
    { "integer?",                          1, (void*)integerp },
    { "integer->char",                     1, (void*)integer_char },
    { "isqrt",                             1, (void*)isqrtf },
    { "lcm",                               2, (void*)lcmf },
    { "list?",                             1, (void*)listp },
    { "list->string",                      1, (void*)list_string },
    { "list->vector",                      1, (void*)list_vector },
    { "load",                              1, (void*)load },
    { "log",                               1, (void*)logff },
    { "magnitude",                         1, (void*)magnitude },
    { "make-string",                       0, (void*)make_string },
    { "make-vector",                       0, (void*)make_vector },
    { "neg",                               1, (void*)unineg },
    { "negative?",                         1, (void*)negativep },
    { "newline",                           0, (void*)newline },
    { "not",                               1, (void*)isnot },
    { "null?",                             1, (void*)nullp },
    { "number?",                           1, (void*)numberp },
    { "number->string",                    1, (void*)number_string },
    { "open-input-file",                   1, (void*)open_input_file },
    { "open-input-string",                 0, (void*)open_input_string },
    { "open-output-file",                  1, (void*)open_output_file },
    { "open-output-string",                0, (void*)open_output_string },
    { "output-port?",                      1, (void*)output_portp },
    { "pair?",                             1, (void*)pairp },
    { "peek-char",                         0, (void*)peek_char },
    { "positive?",                         1, (void*)positivep },
    { "pow",                               2, (void*)powff },
    { "procedure?",                        1, (void*)procedurep },
    { "product",                           2, (void*)product },
    { "promise?",                          1, (void*)promisep },
    { "promise-forced?",                   1, (void*)promise_forcedp },
    { "promise-value",                     1, (void*)promise_value },
    { "quotient",                          2, (void*)quotientf },
    { "rational?",                         1, (void*)rationalp },
    { "read",                              0, (void*)readf },
    { "read-char",                         0, (void*)read_char },
    { "real?",                             1, (void*)realp },
    { "remainder",                         2, (void*)remainderff },
    { "reverse",                           1, (void*)reverse },
    { "round",                             1, (void*)roundff },
    { "scan",                              0, (void*)scanff },
    { "set-car!",                          2, (void*)set_car },
    { "set-cdr!",                          2, (void*)set_cdr },
    { "sin",                               1, (void*)sinff },
    { "sinh",                              1, (void*)sinhff },
    { "space",                             0, (void*)space },
    { "sqrt",                              1, (void*)sqrtff },
    { "string",                            0, (void*)string },
    { "string?",                           1, (void*)stringp },
    { "string=?",                          2, (void*)string_eqp },
    { "string>=?",                         2, (void*)string_gep },
    { "string>?",                          2, (void*)string_gtp },
    { "string<=?",                         2, (void*)string_lep },
    { "string<?",                          2, (void*)string_ltp },
    { "string-append",                     2, (void*)string_append },
    { "string-ci=?",                       2, (void*)string_cieqp },
    { "string-ci>=?",                      2, (void*)string_cigep },
    { "string-ci>?",                       2, (void*)string_cigtp },
    { "string-ci<=?",                      2, (void*)string_cilep },
    { "string-ci<?",                       2, (void*)string_ciltp },
    { "string-copy",                       1, (void*)string_copy },
    { "string-fill!",                      2, (void*)string_fill },
    { "string-length",                     1, (void*)string_length },
    { "string->list",                      1, (void*)string_list },
    { "string->number",                    1, (void*)string_number },
    { "string-ref",                        2, (void*)string_ref },
    { "string-set!",                       3, (void*)string_set },
    { "string->symbol",                    1, (void*)string_symbol },
    { "substring",                         0, (void*)substringf },
    { "sum",                               2, (void*)sum },
    { "symbol?",                           1, (void*)symbolp },
    { "symbol->string",                    1, (void*)symbol_string },
    { "tan",                               1, (void*)tanff },
    { "tanh",                              1, (void*)tanhff },
    { "trace",                             1, (void*)trace },
    { "truncate",                          1, (void*)truncateff },
    { "undefine",                          1, (void*)undefine },
    { "vector",                            0, (void*)vector },
    { "vector?",                           1, (void*)vectorp },
    { "vector-fill!",                      2, (void*)vector_fill },
    { "vector-length",                     1, (void*)vector_length },
    { "vector->list",                      1, (void*)vector_list },
    { "vector-ref",                        2, (void*)vector_ref },
    { "vector-set!",                       3, (void*)vector_set },
    { "with-input-from-file",              2, (void*)with_input_from_file },
    { "with-output-to-file",               2, (void*)with_output_to_file },
    { "write",                             0, (void*)writef },
    { "write-char",                        0, (void*)write_char },
    { "write-to-string",                   0, (void*)write_to_string },
    { "zero?",                             1, (void*)zerop },
    { 0,                                   0, 0 }
};

struct FormTable {
    const char* name;
    Formp       formp;
} formTable[] = {
    { "and",         andform },
    { "begin",       begin },
    { "bound?",      boundp },
    { "case",        caseform },
    { "complex",     complexform },
    { "cond",        cond },
    { "define",      defineform },
    { "delay",       delayform },
    { "do",          doform },
    { "environment", environment },
    { "if",          ifform },
    { "lambda",      lambdaform },
    { "let",         let },
    { "let*",        letstar },
    { "letrec",      letrec },
    { "or",          orform },
    { "promise",     promiseform },
    { "quasiquote",  quasiquoteform },
    { "quote",       quoteform },
    { "rational",    rationalform },
    { "set!",        setform },
    { "unless",      unlessform },
    { "when",        whenform },
    { "while",       whileform },
    { 0,             0 }
};

void define_atomize_sexpr(const char* name, sexp value)
{
    define(atomize(name), value);
}

int main(int argc, char **argv, char **envp)
{
    // allocate all the cells we will ever have
    cell = new Cons[CELLS];
    for (int i = CELLS; --i >= 0; )
    {
        cell[i].car = 0;
        cell[i].cdr = freelist;
        freelist = cell+i;
    }

    // allocate the protection stack
    psp   = protect = new sexp[PSIZE];
    psend = protect + PSIZE;

    // allocate ports for cin, cout, cerr
    inport  = newcell(INPORT,  (sexp)&cinStream);
    outport = newcell(OUTPORT, (sexp)&coutStream);
    errport = newcell(OUTPORT, (sexp)&cerrStream);

    // constants
    zero = newfixnum(0);
    one  = newfixnum(1);

    // names
    closure         = atomize("closure");
    commaat         = atomize(",@");
    comma           = atomize(",");
    complex         = atomize("complex");
    definea         = atomize("define");
    dot             = atomize(".");
    elsea           = atomize("else");
    eof             = atomize("#eof");
    f               = atomize("#f");
    lambda          = atomize("lambda");
    lbracket        = atomize("[");
    lparen          = atomize("(");
    minus           = atomize("-");
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

    // streams
    define_atomize_sexpr("cerr",     errport);
    define_atomize_sexpr("cin",      inport);
    define_atomize_sexpr("cout",     outport);

    // metasyntax
    define_atomize_sexpr("comma",    comma);
    define_atomize_sexpr("commaat",  commaat);
    define_atomize_sexpr("dot",      dot);
    define_atomize_sexpr("lbracket", lbracket);
    define_atomize_sexpr("lparen",   lparen);
    define_atomize_sexpr("qchar",    qchar);
    define_atomize_sexpr("rbracket", rbracket);
    define_atomize_sexpr("rparen",   rparen);
    define_atomize_sexpr("tick",     tick);
    define_atomize_sexpr("void",     voida);

    for (FuncTable* p = funcTable; p->name; ++p)
    {
        sexp* mark = psp;
        Funct* f = (Funct*)save(newcell(FUNCT));
        f->tags[2] = p->arity; f->funcp = p->funcp;
        define(save(atomize(p->name)), (sexp)f);
        psp = mark;
    }

    for (FormTable* p = formTable; p->name; ++p)
    {
        sexp* mark = psp;
        Form* f = (Form*)save(newcell(FORM));
        f->formp = p->formp;
        define(save(atomize(p->name)), (sexp)f);
        psp = mark;
    }

    tracing = f;

    char* s;
    struct sigaction intr_action;
    intr_action.sa_flags = SA_SIGINFO;
    intr_action.sa_sigaction = intr_handler;
    struct sigaction segv_action;
    segv_action.sa_flags = SA_SIGINFO;
    segv_action.sa_sigaction = segv_handler;

    s = (char*) sigsetjmp(the_jmpbuf, 1);
    indent = 0; psp = protect;
    if (s)
        std::cout << s << std::endl;

    sigaction(SIGSEGV, &segv_action, NULL);
    sigaction(SIGINT,  &intr_action, NULL);

    load(newstring("init.ss"));

    fixenvs(global);

    if (argc > 1)
    {
        load(newstring(argv[1]));
        return 0;
    }

    killed = 0;

    s = (char*) sigsetjmp(the_jmpbuf, 1);
    indent = 0; psp = protect;
    if (s)
        std::cout << s << std::endl;

    // read evaluate display ...

    gc();

    for (;;)
    {
        if (psp > protect)
            if ((long)(psp-protect) > 1)
                std::cout << (long)(psp-protect) << " items remain on protection stack" << std::endl;
            else
                std::cout << "one item remains on protection stack" << std::endl;

        std::cout << "> ";
        std::cout.flush();
        expr = read(std::cin, 0);
        if (eof == expr)
            break;
        killed = 0;
        valu = eval(expr, global);
        {
            std::stringstream s; Ugly ugly(s); std::set<sexp> seenSet;
            s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
            display(s, valu, seenSet, ugly, 0, false);
            std::cout.write(s.str().c_str(), s.str().length());
            if (voida != valu)
                std::cout << std::endl;
        }
    }
    return 0;
}

