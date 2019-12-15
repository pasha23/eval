/*
 * this aspires to be a scheme interpreter
 * but it lacks tail call optimization, call/cc etc.
 * 
 * Robert Kelley October 2019
 */
#define PSIZE   65536
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
#include <unordered_map>
#include <sstream>
#include <stdint.h>
#include <stdlib.h>
#include <string>
#include <termios.h>
#include <unistd.h>
#include "num.hpp"
#include "rat.hpp"

#ifdef BROKEN
#define error(s) do { std::cout << s << std::endl; assert(false); } while(0)
#else
#define error(s) do { longjmp(the_jmpbuf, (long)s); } while(0)
#endif

/*
 * memory is managed as a freelist of cells, each potentially containing two pointers
 *
 * if bit 0 is 0 it's a Cons
 * otherwise the type is in the second byte
 * if bit 1 is set then it's marked
 *
 * vectors and strings are stored on the regular heap new / delete
 */
enum Tag0 { CONS = 0, OTHER = 1, MARK = 2 };

enum Tag1
{
    ATOM     = 0x0001,
    STRING   = 0x0101,
    FORM     = 0x0201,
    FIXNUM   = 0x0301,
    FUNCT    = 0x0401,
    FLOAT    = 0x0501,
    DOUBLE   = 0x0601,
    CHAR     = 0x0701,
    INPORT   = 0x0801,
    OUTPORT  = 0x0901,
    VECTOR   = 0x0A01,
    BIGNUM   = 0x0B01,
    RATIONAL = 0x0C01
};

typedef struct Cons *sexp;
typedef sexp (*Formp)(sexp, sexp);
typedef sexp (*Varargp)(sexp);
typedef sexp (*Oneargp)(sexp);
typedef sexp (*Twoargp)(sexp, sexp);
typedef sexp (*Threeargp)(sexp, sexp, sexp);

jmp_buf the_jmpbuf;

int killed = 1;             // we might not make it through initialization
int gcstate;           	    // handling break during gc
int indent;                 // handling eval trace indent
sexp expr;              	// the expression read
sexp valu;              	// the value of it
sexp cell;         	    	// all the memory starts here
sexp atoms;         		// all atoms are linked in a list
sexp global;        		// this is the global symbol table (a list)
sexp replenv;        		// this is the repl environment
sexp cinport;               // the port associated with std::cin
sexp inport;        		// the current input port
sexp coutport;              // the port associated with std::cout
sexp outport;       		// the current output port
sexp tracing;       		// trace everything
sexp cerrport;              // the port associated with std::cerr
sexp errport;       		// the stderr port
sexp freelist;      		// available cells are linked in a list
sexp *psp;          		// protection stack pointer
sexp *psend;            	// protection stack end
sexp *protect;      		// protection stack

sexp closure, comma, commaat, complex, definea, dot, elsea, eof, f, lambda;
sexp lbracket, lparen, minus, one, promise, qchar, quasiquote, quote;
sexp rbracket, rparen, t, tick, unquote, unquotesplicing, voida, zero;

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
    int limit;

    StrPortStream(std::stringstream& stringstream, int limit) : PortStream(&stringstream), limit(limit) {}
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
    if (0 == limit || ss->tellp() < limit)
        ((std::stringstream*)streamPointer)->put(ch);
}

void StrPortStream::write(const char *s, int len)
{
    std::stringstream* ss = (std::stringstream*)streamPointer;
    if (limit && (int)ss->tellp() + len > limit)
        len = limit - (int)ss->tellp() - 1;
    ss->write(s, len);
}

/*
 * note that there is just no room for virtual function pointers
 */
struct Cons     { sexp                cdr;                        sexp           car; };
struct Tags     { char tags[sizeof(Cons)];                                            };
struct InPort   { char tags[sizeof(sexp)-2], avail, peek;         PortStream*      s; };
struct Stags    { short stags; char tags[sizeof(sexp)-2];         sexp           car; };
struct Vector   { char tags[sizeof(sexp)-sizeof(short)]; short l; sexp*            e; };
struct Atom     { char tags[sizeof(Cons)-sizeof(sexp)];           sexp          body; };
struct String   { char tags[sizeof(Cons)-sizeof(char*)];          char*         text; };
struct Fixnum   { char tags[sizeof(Cons)-sizeof(int)];            int         fixnum; };
struct Float    { char tags[sizeof(Cons)-sizeof(float)];          float       flonum; };
struct Double   { char tags[sizeof(Cons)-sizeof(double)];         double      flonum; };
struct Funct    { char tags[sizeof(Cons)-sizeof(void*)];          void*        funcp; };
struct Form     { char tags[sizeof(Cons)-sizeof(Formp)];          Formp        formp; };
struct Char     { char tags[sizeof(Cons)-sizeof(uint32_t)];       uint32_t        ch; };
struct OutPort  { char tags[sizeof(Cons)-sizeof(PortStream*)];    PortStream*      s; };
struct Bignum   { char tags[sizeof(Cons)-sizeof(Num*)];           Num*          nump; };
struct Rational { char tags[sizeof(Cons)-sizeof(Rat*)];           Rat*          ratp; };

// supports uglyprinting
struct Context
{
    static const int eol  = 70;
    static const int tabs =  4;

    bool write;
    bool pretty;
    int  label;
    std::streampos pos;
    std::streampos limit;
    std::stringstream s;
    std::unordered_map<sexp,sexp> seenMap;
    Context(int limit, bool write, bool pretty) :
        limit(limit), label(0), write(write), pretty(pretty) { setp(); pos = s.tellp(); }
    void setp() { s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15); }
    void wrap(int level, int length) { if (pretty && s.tellp() - pos + length > eol) newline(level); else space(); }
    void newline(int level) { s << '\n'; pos = s.tellp(); for (int i = level; --i >= 0; s << ' ') {} }
    void space(void) { s << ' '; }
    bool labelCycles(sexp exp, bool last);
};

void mapCycles(Context& context, sexp exp);
void display(Context& context, sexp p, int level);

static inline int  shortType(const sexp p)  { return       (~MARK &  ((Stags*)p)->stags); }
static inline int  arity(const sexp p)      { return                ((Funct*)p)->tags[2]; }
static inline bool isMarked(const sexp p)   { return       ( MARK & ((Tags*)p)->tags[0]); }
static inline bool isCons(const sexp p)     { return p && !(OTHER & ((Tags*)p)->tags[0]); }
static inline bool isAtom(const sexp p)     { return p &&       ATOM     == shortType(p); }
static inline bool isString(const sexp p)   { return p &&       STRING   == shortType(p); }
static inline bool isFunct(const sexp p)    { return p &&       FUNCT    == shortType(p); }
static inline bool isForm(const sexp p)     { return p &&       FORM     == shortType(p); }
static inline bool isFixnum(const sexp p)   { return p &&       FIXNUM   == shortType(p); }
static inline bool isFloat(const sexp p)    { return p &&       FLOAT    == shortType(p); }
static inline bool isDouble(const sexp p)   { return p &&       DOUBLE   == shortType(p); }
static inline bool isChar(const sexp p)     { return p &&       CHAR     == shortType(p); }
static inline bool isInPort(const sexp p)   { return p &&       INPORT   == shortType(p); }
static inline bool isOutPort(const sexp p)  { return p &&       OUTPORT  == shortType(p); }
static inline bool isVector(const sexp p)   { return p &&       VECTOR   == shortType(p); }
static inline bool isBignum(const sexp p)   { return p &&       BIGNUM   == shortType(p); }
static inline bool isRational(const sexp p) { return p &&       RATIONAL == shortType(p); }

bool isFlonum(const sexp p)  { return isFloat(p) || isDouble(p); }

bool isClosure(sexp p)
{
    return isCons(p) &&
           closure == p->car &&                         // (closure
           isCons(p = p->cdr) && p->car &&              //  exp
           isCons(p = p->cdr) && p->car &&              //  env)
           !p->cdr;
}

bool isPromise(sexp p)
{
    return isCons(p) && promise == p->car &&            // (promise
           isCons(p = p->cdr) &&                        //  forced
           isCons(p = p->cdr) &&                        //  value
           isCons(p = p->cdr) &&                        //  exp
           isCons(p = p->cdr) &&                        //  env)
           !p->cdr;
}

bool isComplex(sexp p)
{
    return isCons(p) && complex == p->car &&            // (complex
           isCons(p = p->cdr) && isFlonum(p->car) &&    //  real-part
           isCons(p = p->cdr) && isFlonum(p->car) &&    //  imag-part
           !p->cdr;                                     // )
}

static inline sexp boolwrap(bool x) { return x ? t : f; }

// boolean?
sexp booleanp(sexp x) { return boolwrap(t == x || f == x); }

// form?
sexp formp(sexp p) { return boolwrap(isForm(p)); }

// function?
sexp functionp(sexp p) { return boolwrap(isFunct(p)); }

// closure?
sexp closurep(sexp s) { return boolwrap(isClosure(s)); }

// promise?
sexp promisep(sexp s) { return boolwrap(isPromise(s)); }

// rational?
sexp rationalp(sexp s) { return boolwrap(isRational(s)); }

// exact?
sexp exactp(sexp x) { return boolwrap(isFixnum(x) || isRational(x) || isBignum(x)); }

// inexact?
sexp inexactp(sexp x) { return boolwrap(isFlonum(x)); }

// complex?
sexp complexp(sexp s) { return boolwrap(isComplex(s)); }

// protection stack management

void psoverflow(void) { error("protection stack overflow"); }

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

static inline sexp replace(sexp p) { return *psp = p; }

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

    if (isCons(p)) {
        sexp q = p->cdr;
        sexp r = p->car;
        markCell(p);
        mark(q);
        mark(r);
        return;
    } else if (isAtom(p)) {
        Atom* atom = (Atom*)p;
        mark(atom->body);
    } else if (isVector(p)) {
        Vector* v = (Vector*)p;
        for (int i = v->l; --i >= 0; mark(v->e[i])) {}
    }

    markCell(p);
}

static void deleteinport(sexp v)
{
    PortStream* stream = ((InPort*)v)->s;
    ((InPort*)v)->s = 0;
    if (stream != &cinStream)
        delete stream;
}

static void deleteoutport(sexp v)
{
    PortStream* stream = ((OutPort*)v)->s;
    ((OutPort*)v)->s = 0;
    if (stream != &coutStream && stream != &cerrStream)
        delete stream;
}

static void deletevector(sexp v) { delete ((Vector*)v)->e; }

static void deletebignum(sexp n) { delete ((Bignum*)n)->nump; }

static void deleterational(sexp n) { delete ((Rational*)n)->ratp; }

// String.tags[2] == 0 ==> immutable ascii string
// String.tags[2] == 1 ==> mutable ascii string
// String.tags[2] == 2 ==> mutable uint32_t string
// String.tags[2] == 3 ==> mutable utf8 string

static inline bool isUTF8(String *s)    { return 3 == s->tags[2]; }
static inline bool isWide(String *s)    { return 2 == s->tags[2]; }
static inline bool isMutable(String *s) { return 0 != s->tags[2]; }

static void deletestring(sexp s) { if (isMutable((String*)s)) delete ((String*)s)->text; }

/*
 * mark all reachable cells
 *
 * sweep all memory, putting unmarked cells on the freelist
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
    mark(replenv);
    mark(inport);
    mark(errport);
    mark(outport);

    for (sexp *p = protect; p < psp; ++p)
        mark(*p);

    freelist = 0;

    for (sexp p = cell; p < cell+CELLS; ++p)
    {
        if (!isMarked(p))
        {
            switch (((Stags*)p)->stags)
            {
            case OUTPORT:  deleteoutport(p);  break;
            case INPORT:   deleteinport(p);   break;
            case VECTOR:   deletevector(p);   break;
            case BIGNUM:   deletebignum(p);   break;
            case RATIONAL: deleterational(p); break;
            }
            p->car = 0;
            p->cdr = freelist;
            freelist = p;
        } else 
            unmarkCell(p);
    }

    if (!freelist)
    {
        gcstate = 0;
        error("gc: out of memory");
    }

    if (gcstate > 1)
    {
        killed = 0;
        gcstate = 0;
        error("SIGINT");
    }

    gcstate = 0;
    return voida;
}

void assertCons(sexp s)     { if (!isCons(s))     error("not pair"); }
void assertAtom(sexp s)     { if (!isAtom(s))     error("not symbol"); }
void assertChar(sexp s)     { if (!isChar(s))     error("not a character"); }
void assertFixnum(sexp s)   { if (!isFixnum(s))   error("not an integer"); }
void assertString(sexp s)   { if (!isString(s))   error("not a string"); }
void assertInPort(sexp s)   { if (!isInPort(s))   error("not an input port"); }
void assertOutPort(sexp s)  { if (!isOutPort(s))  error("not an output port"); }
void assertComplex(sexp s)  { if (!isComplex(s))  error("not complex"); }
void assertRational(sexp s) { if (!isRational(s)) error("not rational"); }
void assertPromise(sexp s)  { if (!isPromise(s))  error("not a promise"); }

void assertFlonum(sexp s)   { if (!isFlonum(s) && !isFixnum(s) && !isRational(s)) error("not a real number"); }

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

sexp newfixnum(int number)
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

sexp newbignum(const Num& num)
{
    Bignum* bignum = (Bignum*)newcell(BIGNUM);
    bignum->nump = new Num(num);
    return (sexp)bignum;
}

sexp newrational(const Rat& rat)
{
    Rational* rational = (Rational*)newcell(RATIONAL);
    rational->ratp = new Rat(rat);
    rational->ratp->reduce();
    return (sexp)rational;
}

sexp newrational(const Num& num, const Num& den)
{
    Rational* rational = (Rational*)newcell(RATIONAL);
    rational->ratp = new Rat(num, den);
    rational->ratp->reduce();
    return (sexp)rational;
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

// time
sexp timeff(sexp args)
{
    struct timespec ts;
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts);
    return newflonum(ts.tv_sec + ts.tv_nsec / 1000000000.0);
}

static inline int asFixnum(sexp p) { return ((Fixnum*)p)->fixnum; }

static inline Num asBignum(sexp x) { return *((Bignum*)x)->nump; }

static inline Rat asRational(sexp x) { return *((Rational*)x)->ratp; }

double asFlonum(sexp p)
{
    switch (shortType(p))
    {
    default:       error("asFlonum: not a flonum");
    case FLOAT:    return ((Float*)p)->flonum;
    case DOUBLE:   return ((Double*)p)->flonum;
    case FIXNUM:   return (double) asFixnum(p);
    case BIGNUM:   return ((Bignum*)p)->nump->to_double();
    case RATIONAL: return ((Rational*)p)->ratp->to_double();
    }
}

// supports labeling of cyclic structures
bool Context::labelCycles(sexp exp, bool last)
{
    sexp value = seenMap[exp];
    if (isFixnum(value)) {
        if (last)
            s << ". ";
        s << '#' << asFixnum(value) << '#';
        return true;
    } else if (t == value) {
        s << '#' << label << '=';
        seenMap[exp] = newfixnum(label++);
    }
    return false;
}

// negative?
sexp negativep(sexp x)
{
    return boolwrap(isRational(x) ? (asRational(x).num <  0 ?
                                     asRational(x).den >= 0 :
                                     asRational(x).den <  0) :
                    isBignum(x)   ?  asBignum(x) < 0 :
                                     asFlonum(x) < 0);
}

// positive?
sexp positivep(sexp x)
{
    return boolwrap(isRational(x) ? (asRational(x).den >= 0 ?
                                     asRational(x).num >  0 :
                                     asRational(x).num <  0) :
                    isBignum(x)   ?  asBignum(x) > 0 :
                                     asFlonum(x) > 0);
}

// <
sexp ltp(sexp x, sexp y) { return boolwrap(asFlonum(x) <  asFlonum(y)); }

// <=
sexp lep(sexp x, sexp y) { return boolwrap(asFlonum(x) <= asFlonum(y)); }

// >=
sexp gep(sexp x, sexp y) { return boolwrap(asFlonum(x) >= asFlonum(y)); }

// >
sexp gtp(sexp x, sexp y) { return boolwrap(asFlonum(x) >  asFlonum(y)); }

sexp make_complex(sexp re, sexp im)
{
    sexp* mark = psp;
    return lose(mark, cons(complex, replace(cons(save(re), replace(cons(save(im), 0))))));
}

bool unsafe_add(int a, int x)
{
    return ((x > 0) && (a > INT_MAX - x)) || ((x < 0) && (a < INT_MIN - x));
}

bool unsafe_sub(int a, int x)
{
    return ((x < 0) && (a > INT_MAX + x)) || ((x > 0) && (a < INT_MIN + x));
}

bool unsafe_mul(int a, int x)
{
    return ((a == -1) && (x == INT_MIN)) ||
           ((x == -1) && (a == INT_MIN)) ||
           (x && ((a > INT_MAX / x) || (a < INT_MIN / x)));
}

// magnitude
sexp magnitude(sexp z)
{
    assertComplex(z); z = z->cdr;
    return newflonum(sqrt(asFlonum(z->car)      * asFlonum(z->car) +
                          asFlonum(z->cdr->car) * asFlonum(z->cdr->car)));
}

// angle
sexp angle(sexp z)
{
    assertComplex(z); z = z->cdr;
    return newflonum(atan2(asFlonum(z->cdr->car), asFlonum(z->car)));
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

static inline sexp real_part(sexp x) { return x->cdr->car; }

static inline sexp imag_part(sexp x) { return x->cdr->cdr->car; }

double toDouble(sexp x)
{
    double d;
    if (isFlonum(x))
        d = asFlonum(x);
    else if (isRational(x))
        d = asRational(x).to_double();
    else if (isBignum(x))
        d = asBignum(x).to_double();
    else if (isFixnum(x))
        d = (double)asFixnum(x);
    else
        error("not a number");
    return d;
}

Rat toRational(sexp x)
{
    Rat r;
    if (isRational(x))
        r = asRational(x);
    else if (isBignum(x))
        r = Rat(asBignum(x));
    else if (isFixnum(x))
        r = Rat(asFixnum(x));
    else
        error("not a number");
    return r;
}

Num toBignum(sexp x)
{
    Num b;
    if (isBignum(x))
        b = asBignum(x);
    else if (isFixnum(x))
        b = Num(asFixnum(x));
    else
        error("not an integer");
    return b;
}

sexp bignumResult(Num result)
{
    int r; return result.can_convert_to_int(&r) ? newfixnum(r) : newbignum(result);
}

sexp rationalResult(Rat result)
{
    result.reduce();

    if (result.den == 1)
        return bignumResult(result.num);

    return newrational(result);
}

int igcd(int x, int y)
{
    if (x < 0) x = -x;
    if (y < 0) y = -y;
    for (;;)
    {
        if (0 == x) return y;
        y %= x;
        if (0 == y) return x;
        x %= y;
    }
}

// gcd
sexp gcd(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
        return newfixnum(igcd(asFixnum(x), asFixnum(y)));

    return bignumResult(Num::gcd(toBignum(x), toBignum(y)));
}

// lcm
sexp lcm(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
    {
        int g = igcd(asFixnum(x), asFixnum(y));
        Num l((asFixnum(x) / g) * (asFixnum(y) / g));
        return bignumResult(l);
    }

    Num xb = toBignum(x);
    Num yb = toBignum(y);
    Num g = Num::gcd(xb, yb);
    Num l = (xb / g) * (yb / g);
    return bignumResult(l);
}

// x + y
sexp sum(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
    {
        if (unsafe_add(asFixnum(x), asFixnum(y)))
            return newbignum(Num(asFixnum(x)) + Num(asFixnum(y)));
        else
            return newfixnum(asFixnum(x) + asFixnum(y));
    }

    sexp* mark = psp;

    if (isComplex(x)) {
        if (isComplex(y))
            return lose(mark, make_complex(save(sum(real_part(x), real_part(y))),
                                           save(sum(imag_part(x), imag_part(y)))));
        else
            return lose(mark, make_complex(save(sum(real_part(x), y)), imag_part(x)));
    } else if (isComplex(y))
        return lose(mark, make_complex(save(sum(x, real_part(y))), imag_part(y)));

    if (isFlonum(x))
        return newflonum(asFlonum(x) + toDouble(y));

    if (isFlonum(y))
        return newflonum(toDouble(x) + asFlonum(y));

    if (isRational(x) || isRational(y))
        return rationalResult(toRational(x) + toRational(y));

    return bignumResult(toBignum(x) + toBignum(y));
}

// x - y
sexp diff(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
    {
        if (unsafe_sub(asFixnum(x), asFixnum(y)))
            return newbignum(Num(asFixnum(x)) - Num(asFixnum(y)));
        else
            return newfixnum(asFixnum(x) - asFixnum(y));
    }

    sexp* mark = psp;

    if (isComplex(x)) {
        if (isComplex(y))
            return lose(mark, make_complex(save(diff(real_part(x), real_part(y))),
                                           save(diff(imag_part(x), imag_part(y)))));
        else
            return lose(mark, make_complex(save(diff(real_part(x), y)), imag_part(x)));
    } else if (isComplex(y))
        return lose(mark, make_complex(save(diff(x, real_part(y))), imag_part(y)));

    if (isFlonum(x))
        return newflonum(asFlonum(x) - toDouble(y));

    if (isFlonum(y))
        return newflonum(toDouble(x) - asFlonum(y));

    if (isRational(x) || isRational(y))
        return rationalResult(toRational(x) - toRational(y));

    return bignumResult(toBignum(x) - toBignum(y));
}

// x * y
sexp product(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
    {
        if (unsafe_mul(asFixnum(x), asFixnum(y)))
            return newbignum(Num(asFixnum(x)) * Num(asFixnum(y)));
        else
            return newfixnum(asFixnum(x) * asFixnum(y));
    }

    bool cpx = false;
    sexp xr, xi, yr, yi;

    if (isComplex(x))
        { cpx = true; xr = real_part(x); xi = imag_part(x); }
    else
        { xr = x; xi = zero; }

    if (isComplex(y))
        { cpx = true; yr = real_part(y); yi = imag_part(y); }
    else
        { yr = y; yi = zero; }

    if (cpx)
    {
        sexp* mark = psp;
        return lose(mark, make_complex(save(diff(save(product(xr, yr)), save(product(xi, yi)))),
                                       save( sum(save(product(xr, yi)), save(product(xi, yr))))));
    }

    if (isFlonum(x))
        return newflonum(asFlonum(x) * toDouble(y));

    if (isFlonum(y))
        return newflonum(toDouble(x) * asFlonum(y));

    if (isRational(x) || isRational(y))
        return rationalResult(toRational(x) * toRational(y));

    return bignumResult(toBignum(x) * toBignum(y));
}

// x / y
sexp quotientf(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
    {
        Rat result(Num(asFixnum(x)), Num(asFixnum(y)));
        return rationalResult(result);
    }

    bool cpx = false;
    sexp xr, xi, yr, yi;

    if (isComplex(x))
        { cpx = true; xr = real_part(x); xi = imag_part(x); }
    else
        { xr = x; xi = zero; }

    if (isComplex(y))
        { cpx = true; yr = real_part(y); yi = imag_part(y); }
    else
        { yr = y; yi = zero; }

    if (cpx)
    {
        sexp* mark = psp;
        sexp d = save(sum(save(product(yr, yr)), save(product(yi, yi))));
        return lose(mark, make_complex(save(quotientf(save(sum(save(product(xr, yr)),
                                                               save(product(xi, yi)))), d)),
                                       save(quotientf(save(diff(save(product(xi, yr)),
                                                                save(product(xr, yi)))), d))));
    }

    if (isFlonum(x))
        return newflonum(asFlonum(x) / toDouble(y));

    if (isFlonum(y))
        return newflonum(toDouble(x) / asFlonum(y));

    if (isRational(x) || isRational(y))
        return rationalResult(toRational(x) / toRational(y));

    Rat result(toBignum(x), toBignum(y));

    return rationalResult(result);
}

int mod(int x, int y)
{
    int r = x % y;
    if (r * y < 0)
        r += y;
    return r;
}

// (modulo x y)
sexp moduloff(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
        return newfixnum(mod(asFixnum(x), asFixnum(y)));

    bool cpx = false;
    sexp xr, xi, yr, yi;

    if (isComplex(x))
        { cpx = true; xr = real_part(x); xi = imag_part(x); }
    else
        { xr = x; xi = zero; }

    if (isComplex(y))
        { cpx = true; yr = real_part(y); yi = imag_part(y); }
    else
        { yr = y; yi = zero; }

    if (cpx)
        error("complex modulo not implemented");

    if (isFlonum(x))
        return newflonum(fmod(asFlonum(x), toDouble(y)));

    if (isFlonum(y))
        return newflonum(fmod(toDouble(x), asFlonum(y)));

    if (isRational(x) || isRational(y))
    {
        Rat xrat = toRational(x);
        Rat yrat = toRational(y);
        Rat result(Num::mod(xrat.num * yrat.den,
                            yrat.num * xrat.den),
                   xrat.den * yrat.den);
    }

    return bignumResult(Num::mod(toBignum(x), toBignum(y)));
}

int rem(int x, int y)
{
    int r = x % y;
    if (r > 0)
    {
        if (x < 0)
            r -= abs(y);
    } else if (r < 0) {
        if (x > 0)
            r += abs(y);
    }
    return r;
}

double drem(double xd, double yd)
{
    double rd = fmod(xd, yd);
    if (rd > 0)
    {
        if (xd < 0)
            rd -= abs(yd);
    } else if (rd < 0) {
        if (xd > 0)
            rd += abs(yd);
    }
    return rd;
}

// x % y
sexp remainderff(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
        return newfixnum(rem(asFixnum(x), asFixnum(y)));

    bool cpx = false;
    sexp xr, xi, yr, yi;

    if (isComplex(x))
        { cpx = true; xr = real_part(x); xi = imag_part(x); }
    else
        { xr = x; xi = zero; }

    if (isComplex(y))
        { cpx = true; yr = real_part(y); yi = imag_part(y); }
    else
        { yr = y; yi = zero; }

    if (cpx)
        error("complex remainder not implemented");

    if (isFlonum(x))
        return newflonum(drem(asFlonum(x), toDouble(y)));

    if (isFlonum(y))
        return newflonum(drem(toDouble(x), asFlonum(y)));

    if (isRational(x) || isRational(y))
    {
        Rat xrat = toRational(x);
        Rat yrat = toRational(y);
        Rat result(Num::mod(xrat.num * yrat.den,
                            yrat.num * xrat.den),
                   xrat.den * yrat.den);

        if (result > 0)
        {
            if (xrat < 0)
            {
                if (yrat < 0)
                    result += yrat;
                else
                    result -= yrat;
            }
        } else if (result < 0) {
            if (xrat > 0)
            {
                if (yrat < 0)
                    result -= yrat;
                else
                    result += yrat;
            }
        }

        return rationalResult(result);
    }

    Num xb = toBignum(x);
    Num yb = toBignum(y);

    Num result(Num::mod(xb, yb));

    if (result > 0)
    {
        if (xb < 0)
        {
            if (yb < 0)
                result += yb;
            else
                result -= yb;
        }
    } else if (result < 0) {
        if (xb > 0)
        {
            if (yb < 0)
                result -= yb;
            else
                result += yb;
        }
    }

    return bignumResult(result);
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
    sexp* mark = psp;

    if (isComplex(x))
        return lose(mark, make_complex(save(unineg(x->cdr->car)), save(unineg(x->cdr->cdr->car))));

    switch (shortType(x))
    {
    default:       error("neg: operand");
    case FIXNUM:   return newfixnum(-   ((Fixnum*)x)->fixnum);
    case FLOAT:    return newflonum(-   ((Float*)x)->flonum);
    case DOUBLE:   return newflonum(-   ((Double*)x)->flonum);
    case BIGNUM:   return newbignum(-   *((Bignum*)x)->nump);
    case RATIONAL: return newrational(- *((Rational*)x)->ratp);
    }
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

// 1 / x0
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

sexp randomf(sexp x) { return newflonum(drand48()); }

double truncate(double x) { return x < 0 ? ceil(x) : floor(x); }

sexp floatstub(double (*f)(double), sexp x) { assertFlonum(x); return newflonum((*f)(asFlonum(x))); }

sexp flintstub(double (*f)(double), sexp x)
{
    assertFlonum(x);
    double r = (*f)(asFlonum(x));
    return (r == (int)r) ? newfixnum((int)r) : newflonum(r);
}

// functions on real numbers
sexp acosff(sexp x)     { return floatstub(acos,     x); } // acos
sexp asinff(sexp x)     { return floatstub(asin,     x); } // asin
sexp atanff(sexp x)     { return floatstub(atan,     x); } // atan
sexp cosff(sexp x)      { return floatstub(cos,      x); } // cos
sexp coshff(sexp x)     { return floatstub(cosh,     x); } // cosh
sexp expff(sexp x)      { return floatstub(exp,      x); } // exp
sexp logff(sexp x)      { return floatstub(log,      x); } // log
sexp sinff(sexp x)      { return floatstub(sin,      x); } // sin
sexp sinhff(sexp x)     { return floatstub(sinh,     x); } // sinh
sexp tanff(sexp x)      { return floatstub(tan,      x); } // tan
sexp tanhff(sexp x)     { return floatstub(tanh,     x); } // tanh
sexp truncateff(sexp x) { return flintstub(truncate, x); } // truncate
sexp ceilingff(sexp x)  { return flintstub(ceil,     x); } // ceil
sexp floorff(sexp x)    { return flintstub(floor,    x); } // floor
sexp roundff(sexp x)    { return flintstub(round,    x); } // round

sexp isqrtf(sexp x)
{
    if (isFixnum(x) && 0 <= asFixnum(x))
        return newfixnum(isqrt(asFixnum(x)));
    if (isBignum(x) && asBignum(x) >= 0)
        return newbignum(asBignum(x).sqrt());
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
    sexp* mark = psp;
    return lose(mark, make_complex(save(newflonum(re)), save(newflonum(im))));
}

// pow
sexp powff(sexp x, sexp y) { assertFlonum(x); assertFlonum(y); return newflonum(pow(asFlonum(x), asFlonum(y))); }

// atan2
sexp atan2ff(sexp x, sexp y) { assertFlonum(x); assertFlonum(y); return newflonum(atan2(asFlonum(x), asFlonum(y))); }

// integer?
sexp integerp(sexp x) { return boolwrap(isFixnum(x) || isFlonum(x) && (int)asFlonum(x) == asFlonum(x)); }

// real?
sexp realp(sexp x) { return boolwrap(isFixnum(x) || isFlonum(x) || isRational(x)); }

// inexact->exact
sexp inexact_exact(sexp x) { assertFlonum(x); return newfixnum((int)asFlonum(x)); }

// exact->inexact
sexp exact_inexact(sexp x)
{
    if (isFixnum(x) || isRational(x) || isBignum(x))
        return newflonum((double)asFlonum(x));
    error("exact->inexact: not exact");
}

// <<
sexp lsh(sexp x, sexp y)
{
    assertFixnum(y);
    if (isFixnum(x) || isBignum(x))
        return bignumResult(toBignum(x) << asFixnum(y));
    else
        error("<< non integer arguments");
}

// >>
sexp rsh(sexp x, sexp y)
{
    assertFixnum(y);
    if (isFixnum(x))
        return newfixnum(asFixnum(x) >> asFixnum(y));
    else if (isBignum(x))
        return bignumResult(asBignum(x) >> asFixnum(y));
    else
        error(">> non integer arguments");
}

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

static const u_int32_t offsetsFromUTF8[6] =
{
    0x00000000UL, 0x00003080UL, 0x000E2080UL,
    0x03C82080UL, 0xFA082080UL, 0x82082080UL
};

uint32_t read_utf8(std::istream& fin)
{
    uint32_t ch = 0;
    int ci, sz = 0;

    do {
        ch <<= 6;
        ch += (unsigned char)fin.get();
        ci = fin.get();
        if (ci < 0)
            return -1L;
        ++sz;
    } while ((((unsigned char)ci) & 0xc0) == 0x80);
    ch -= offsetsFromUTF8[sz-1];
    fin.unget();
    return ch;
}

uint32_t read_utf8(char*& p)
{
    uint32_t ch = 0;
    int ci, sz = 0;

    do {
        ch <<= 6;
        ch += (unsigned char)*p++;
        ci = *p++;
        if (ci == 0)
            return 0L;
        ++sz;
    } while ((((unsigned char)ci) & 0xc0) == 0x80);
    ch -= offsetsFromUTF8[sz-1];
    --p;
    return ch;
}

int stringlen(String *s)
{
    if (isWide(s)) {
        int len = 0;
        uint32_t* p = (uint32_t*)s->text;
        while (*p++)
            ++len;
        return len;
    } else if (isUTF8(s)) {
        int len = 0;
        char* p = s->text;
        while (read_utf8(p))
            ++len;
        return len;
    } else
        return strlen(s->text);
}

// string-length
sexp string_length(sexp s)
{
    assertString(s);
    return newfixnum(stringlen((String*)s));
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

// a string with text on the heap
sexp dynstring(const char* s)
{
    String* string = (String*)newcell(STRING);
    string->text = (char*)s;
    string->tags[2] = 1;
    return (sexp) string;
}

// a utf8 string created by displayString()
sexp utfstring(const char* s)
{
    String* string = (String*)newcell(STRING);
    string->text = (char*)s;
    string->tags[2] = 3;
    return (sexp) string;
}

// a string with string constant text
sexp stastring(const char* s)
{
    String* string = (String*)newcell(STRING);
    string->text = (char*)s;
    return (sexp) string;
}

static inline char* strsave(const char *s)
{
    return strcpy(new char[strlen(s)+1], s);
}

static inline char* stringText(sexp s)
{
    return ((String*)s)->text;
}

static inline char* atomText(sexp s)
{
    return stringText((((Atom*)s)->body->cdr->car));
}

// every atom must be unique and saved in the atoms list
sexp dynintern(const char *s)
{
    for (sexp q = atoms; q; q = q->cdr)
        if (0 == strcmp(s, atomText(q->car)))
            return q->car;
    Atom* a = (Atom*)newcell(ATOM, cons(0, cons(dynstring(s), 0)));
    atoms = cons((sexp)a, atoms);
    return (sexp)a;
}

// these atoms are made from a string constant
sexp staintern(const char *s)
{
    for (sexp q = atoms; q; q = q->cdr)
        if (0 == strcmp(s, atomText(q->car)))
            return q->car;
    Atom* a = (Atom*)newcell(ATOM, cons(0, cons(stastring(s), 0)));
    atoms = cons((sexp)a, atoms);
    return (sexp)a;
}

// strcpy for ucs strings
uint32_t* widecpy(uint32_t* dst, const uint32_t* src)
{
    uint32_t* r = dst;
    while (*src)
        *dst++ = *src++;
    return r;
}

// strcmp for ucs strings
int widecmp(const uint32_t* s0, const uint32_t* s1)
{
    int r = 0;
    while (*s0 && *s1 && (r = *s0++ - *s1++)) {}
    return r;
}

// create a ucs string, text on heap
sexp widestring(const uint32_t* text)
{
    String* string = (String*)newcell(STRING);
    string->text = (char*)text;
    string->tags[2] = 2;
    return (sexp) string;
}

// create a ucs string, copying argument to heap
sexp widestring(const std::vector<uint32_t> s)
{
    uint32_t* widetext = new uint32_t[s.size()];
    for (int i = 0; i < s.size(); ++i)
        widetext[i] = s[i];
    String* string = (String*)newcell(STRING);
    string->text = (char*)widetext;
    string->tags[2] = 2;
    return (sexp) string;
}

// number->string
sexp number_string(sexp exp)
{
    Context context(0, true, false);
    mapCycles(context, exp);
    display(context, exp, 0);
    return utfstring(strsave(context.s.str().c_str()));
}

// make-string
sexp make_string(sexp args)
{
    if (!args || !isFixnum(args->car))
        error("make-string: args expected");

    int l = asFixnum(args->car);
    int c = args->cdr && isChar(args->cdr->car) ?
                  ((Char*)(args->cdr->car))->ch : ' ';

    if (c > 0x7f)
    {
        uint32_t *b = new uint32_t[l+1];
        uint32_t *q = b;
        for (int i = 0; i < l; ++i)
            *q++ = c;
        *q++ = 0;
        return widestring(b);
    } else {
        char *b = new char[l+1];
        char *q = b;
        for (int i = 0; i < l; ++i)
            *q++ = c;
        *q++ = 0;
        return dynstring(b);
    }
}

// string-copy
sexp string_copy(sexp s)
{
    assertString(s);
    String* string = (String*)s;
    if (isWide(string)) {
        int l = stringlen(string);
        uint32_t *widetext = new uint32_t[l+1];
        widecpy(widetext, (uint32_t*)string->text);
        return widestring(widetext);
    } else if (isUTF8(string))
        return utfstring(strsave(stringText(s)));
    else
        return dynstring(strsave(stringText(s)));
}

// string-append
sexp string_append(sexp p, sexp q)
{
    assertString(p);
    assertString(q);
    String* ps = (String*)p;
    String* qs = (String*)q;
    int pl = stringlen(ps);
    int ql = stringlen(qs);
    if (isWide(ps) || isWide(qs))
    {
        int i = 0;
        uint32_t* b = new uint32_t[pl+ql+1];
        uint32_t* s = b;
        if (isWide(ps)) {
            widecpy(b, (uint32_t*)ps->text);
        } else if (isUTF8(ps)) {
            char* r = ps->text;
            uint32_t wc;
            while ((wc = read_utf8(r)))
                *s++ = wc;
        } else {
            char* r = ps->text;
            while (*r)
                b[i++] = *r++;
        }
        if (isWide(qs)) {
            widecpy(b+pl, (uint32_t*)qs->text);
        } else if (isUTF8(qs)) {
            char* r = qs->text;
            uint32_t wc;
            while ((wc = read_utf8(r)))
                *s++ = wc;
            *s++ = 0;
        } else {
            char* r = qs->text;
            while (*r)
                b[i++] = *r++;
        }
        b[i++] = 0;
        return widestring(b);
    } else if (isUTF8(ps) && isUTF8(qs)) {
        pl = strlen(ps->text);
        ql = strlen(qs->text);
        char *b = new char[pl+ql+1];
        strcpy(b,    ((String*)p)->text);
        strcpy(b+pl, ((String*)q)->text);
        return utfstring(b);
    } else if (!isUTF8(ps) && !isUTF8(qs)) {
        char *b = new char[pl+ql+1];
        strcpy(b,    ((String*)p)->text);
        strcpy(b+pl, ((String*)q)->text);
        return dynstring(b);
    } else
        error("utf8 not complete");
}

// string-fill
sexp string_fill(sexp s, sexp c)
{
    assertChar(c);
    assertString(s);

    String* string = (String*)s;
    if (!isMutable(string))
        error("string-fill!: immutable string");
    if (isWide(string))
    {
        uint32_t k = ((Char*)c)->ch;
        uint32_t* p = (uint32_t*)string->text;
        while (*p)
            *p++ = k;
    } else {
        string->tags[2] = 1;
        char k = ((Char*)c)->ch;
        char* p = string->text;
        while (*p)
            *p++ = k;
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
    return newinport(stringText(p));
}

// open-output-file
sexp open_output_file(sexp p)
{
    assertString(p);
    return newoutport(stringText(p));
}

// output-port?
sexp output_portp(sexp p) { return boolwrap(isOutPort(p)); }

// with-input-from-file
sexp with_input_from_file(sexp p, sexp thunk)
{
    sexp* mark = psp;
    sexp t = save(inport);
    inport = open_input_file(p);
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
    outport = open_output_file(p);
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
    if (args = args->cdr)
    {
        assertFixnum(args->car);
        i = asFixnum(args->car);
    }

    char* text = ((String*)s)->text;
    int j = strlen(text);
    if (args = args->cdr)
    {
        assertFixnum(args->car);
        j = asFixnum(args->car);
    }

    if (i < 0 || j <= i)
        error("open-input-string: bad arguments");

    std::stringstream* ss = new std::stringstream();
    for (int k = i; k < j; ++k)
        ss->put(text[k]);
    InPort* port = (InPort*)save(newcell(INPORT));
    port->avail = 0;
    port->peek = 0;
    port->s = new StrPortStream(*ss, 0);
    return lose((sexp)port);
}

// get-output-string
sexp get_output_string(sexp port)
{
    assertOutPort(port);
    OutPort* p = (OutPort*)port;
    std::stringstream* ss = (std::stringstream*) p->s->streamPointer;
    return utfstring(strsave(ss->str().c_str()));
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
    sexp exp = args->car;
    int limit = 0;
    if (args = args->cdr)
    {
        assertFixnum(args->car);
        limit = asFixnum(args->car);
    }
    Context context(limit, true, false);
    mapCycles(context, exp);
    display(context, exp, 0);
    if (0 == limit) limit = context.s.str().length();
    return utfstring(strsave(context.s.str().substr(0, limit).c_str()));
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
    if ((args = args->cdr) && args->car)
        fill = args->car;
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
    int i = asFixnum(index);
    Vector* v = (Vector*)vector;
    if (0 <= i && i < v->l)
        return ((Vector*)vector)->e[asFixnum(index)];
    error("vector-ref: bounds check");
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

// these only work on ascii data

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

// save the original termios then modify it for cbreak style input. return success
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

// these only work on ascii data

// string<=?
sexp string_lep(sexp p, sexp q) { return boolwrap(strcmp(stringText(p), stringText(q)) <= 0); }

// string<?
sexp string_ltp(sexp p, sexp q) { return boolwrap(strcmp(stringText(p), stringText(q)) <  0); }

// string=?
sexp string_eqp(sexp p, sexp q) { return boolwrap(strcmp(stringText(p), stringText(q)) == 0); }

// string>=?
sexp string_gep(sexp p, sexp q) { return boolwrap(strcmp(stringText(p), stringText(q)) >= 0); }

// string>?
sexp string_gtp(sexp p, sexp q) { return boolwrap(strcmp(stringText(p), stringText(q)) >  0); }

// string-ci-<=?
sexp string_cilep(sexp p, sexp q) { return boolwrap(strcasecmp(stringText(p), stringText(q)) <= 0); }

// string-ci<?
sexp string_ciltp(sexp p, sexp q) { return boolwrap(strcasecmp(stringText(p), stringText(q)) <  0); }

// string-ci=?
sexp string_cieqp(sexp p, sexp q) { return boolwrap(strcasecmp(stringText(p), stringText(q)) == 0); }

// string-ci>=?
sexp string_cigep(sexp p, sexp q) { return boolwrap(strcasecmp(stringText(p), stringText(q)) >= 0); }

// string-ci>?
sexp string_cigtp(sexp p, sexp q) { return boolwrap(strcasecmp(stringText(p), stringText(q)) >  0); }

// string-ref
sexp string_ref(sexp s, sexp i)
{
    assertString(s);
    assertFixnum(i);

    String* string = (String*)s;
    int len = stringlen(string);
    int ind = asFixnum(i);
    if (0 <= ind && ind < len) {
        if (isWide(string))
            return newcharacter(((uint32_t*)string->text)[ind]);
        else if (isUTF8(string)) {
            int ix = 0;
            uint32_t wc;
            for (char* p = string->text; wc = read_utf8(p); ++ix)
                if (ind == ix)
                    return newcharacter(wc);
        } else
            return newcharacter(string->text[ind]);
    }
    error("string-ref: out of bounds");
}

int encodeUTF8(char *p, uint32_t ch)
{
    char* q = p;
    if (ch < 0x80) {
        *q++ = (char)ch;
    } else if (ch < 0x800) {
        *q++ = (ch>>6) | 0xC0;
        *q++ = (ch & 0x3F) | 0x80;
    } else if (ch < 0x10000) {
        *q++ = (ch>>12) | 0xE0;
        *q++ = ((ch>>6) & 0x3F) | 0x80;
        *q++ = (ch & 0x3F) | 0x80;
    } else if (ch < 0x110000) {
        *q++ = (ch>>18) | 0xF0;
        *q++ = ((ch>>12) & 0x3F) | 0x80;
        *q++ = ((ch>>6) & 0x3F) | 0x80;
        *q++ = (ch & 0x3F) | 0x80;
    }
    *q++ = 0;
    return q-p;
}

int encodedLength(uint32_t ch)
{
    char b[8];
    return encodeUTF8(b, ch);
}

// string-set!
sexp string_set(sexp s, sexp k, sexp c)
{
    assertString(s);
    assertFixnum(k);
    assertChar(c);

    String* string = (String*)s;
    if (!isMutable(string))
        error("string-set!: immutable string");

    int len = stringlen(string);
    int ind = asFixnum(k);
    if (ind < 0 || len <= ind)
        error("string-set!: out of bounds");

    if (isWide(string)) {
        uint32_t* p = (uint32_t*)string->text;
        p[ind] = ((Char*)c)->ch;
    } else if (isUTF8(string)) {
        int ix = 0;
        uint32_t wc;
        int el = encodedLength(((Char*)c)->ch);
        for (char* p = string->text; wc = read_utf8(p); ++ix)
            if (ind == ix)
                if (encodedLength(wc) == el) {
                    unsigned char sp = *p;
                    encodeUTF8(p-el, ((Char*)c)->ch);
                    *p = sp;
                } else
                    error("utf8 not complete");
    } else
        string->text[asFixnum(k)] = ((Char*)c)->ch;

    return s;
}

// substring does not yet work on utf8 strings
sexp substringf(sexp args)
{
    if (!args || !isString(args->car))
        error("substring: no string");

    sexp s = args->car;

    if (!(args = args->cdr) || !isFixnum(args->car))
        error("substring: bad start index");

    int i = asFixnum(args->car);
    String* string = (String*)s;
    int j = stringlen(string);

    if ((args = args->cdr) && isFixnum(args->car))
        j = asFixnum(args->car);

    if (i < 0 || j < i)
        error("substring: start negative or end before start");

    if (isWide(string)) {
        uint32_t* b = new uint32_t[j-i+1];
        uint32_t* t = (uint32_t*)string->text;
        for (int k = 0; k <= j-i; ++k)
            b[k] = t[i+k];
        b[j-i] = 0;
        return widestring(b);
    } else if (isUTF8(string)) {
        int ix = 0;
        uint32_t wc;
        for (char* p = string->text; wc = read_utf8(p); ++ix)
            if (i <= ix && ix < j)
                error("utf8 incomplete");
    } else {
        char* b = new char[j-i+1];
        strncpy(b, string->text+i, j-i);
        b[j-i] = 0;
        return dynstring(b);
    }
}

sexp append(sexp p, sexp q)
{
    sexp* mark = psp;
    save(p, q);
    return lose(mark, p ? cons(p->car, save(append(p->cdr, q))) : q);
}

// reverse!
sexp reverse(sexp x)
{
    sexp t = 0;
    if (x)
        while (x)
            if (isCons(x))
            {
                t = cons(car(x), t);
                x = x->cdr;
            } else
                error("reverse!: not a proper list");
    return t;
}

// eq?
sexp eqp(sexp x, sexp y) { return boolwrap(x == y); }

// = numeric equality
sexp eqnp(sexp x, sexp y)
{
    if (isRational(x) && isRational(y))
        return boolwrap(asRational(x) == asRational(y));
 
    if (isComplex(x) && isComplex(y))
    {
        x = x->cdr; y = y->cdr;
        return boolwrap(asFlonum(x->car) == asFlonum(y->car) &&
                        asFlonum(x->cdr->car) == asFlonum(y->cdr->car));
    }

    return boolwrap(asFlonum(x) == asFlonum(y));
}

// zero?
sexp zerop(sexp x)
{
    return eqnp(zero, x);
}

// odd?
sexp oddp(sexp x)
{
    if (isFixnum(x))
        return boolwrap(asFixnum(x) & 1);
    if (isBignum(x))
        return boolwrap(asBignum(x).get_bit(0));
    error("odd?: not an integer");
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
    int result = ~0;
    for (sexp p = args; p; p = p->cdr)
        result = result & asFixnum(p->car);
    return lose(newfixnum(result));
}

// x0 | x1 | x2 ...
sexp orf(sexp args)
{
    assertAllFixnums(args);
    int result = 0;
    for (sexp p = args; p; p = p->cdr)
        result = result | asFixnum(p->car);
    return lose(newfixnum(result));
}

// x0 ^ x1 ^ x2 ...
sexp xorf(sexp args)
{
    assertAllFixnums(args);
    int result = 0;
    for (sexp p = args; p; p = p->cdr)
        result = result ^ asFixnum(p->car);
    return lose(newfixnum(result));
}

// (define (lfsr-shift r p) (if (odd? r) (>> r 1) (^ (>> r 1) p)))

sexp lfsr_shift(sexp r, sexp p)
{
    if (isFixnum(r) && isFixnum(p))
    {
        int rf = asFixnum(r);

        rf = (1 & rf) ? (rf >> 1) : (rf >> 1) ^ asFixnum(p);

        return newfixnum(rf);
    }

    Num rb(isFixnum(r) ? asFixnum(r) : asBignum(r));
    Num pb(isFixnum(p) ? asFixnum(p) : asBignum(p));

    rb = rb.get_bit(0) ? (rb >> 1) : (rb >> 1) ^ pb;

    return bignumResult(rb);
}

// delay
sexp delayform(sexp exp, sexp env)
{
    return lose(cons(promise,
        replace(cons(0,
        replace(cons(0,
        replace(cons(exp->cdr->car,
           save(cons(env, 0))))))))));
}

// force
sexp force(sexp p)
{
    if (!isPromise(p))
        error("force: not a promise");
    if (!(p = p->cdr)->car)
    {
        p->car = t;
        p->cdr->car = eval(p->cdr->cdr->car,
                           p->cdr->cdr->cdr->car);
    }
    return p->cdr->car;
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
    if (!(p = p->cdr)->car)
        error("promise not forced yet");
    return p->cdr->car;
}

// load
sexp load(sexp s)
{
    assertString(s);

    char *name = stringText(s);

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
            eval(input, replenv);
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
    Context context(0, false, true);
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    mapCycles(context, args->car);
    display(context, args->car, 0);
    ((OutPort*)port)->s->write(context.s.str().c_str(), context.s.str().length());
    return voida;
}

// write
sexp writef(sexp args)
{
    Context context(0, true, true);
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    mapCycles(context, args->car);
    display(context, args->car, 0);
    ((OutPort*)port)->s->write(context.s.str().c_str(), context.s.str().length());
    return voida;
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

// cyclic?
sexp cyclicp(sexp x) { std::set<sexp> seenSet; return boolwrap(cyclic(seenSet, x)); }

// for prettyprinting (we should be counting code points)
int displayLength(sexp exp)
{
    Context context(0, true, false);
    mapCycles(context, exp);
    display(context, exp, 0);
    return context.s.str().length();
}

void displayList(Context& context, sexp exp, int level)
{
    bool first = false;
    if (context.labelCycles(exp, false))
        return;
    context.s << '(';
    sexp p = exp;
    level += displayLength(p->car) + 2;
    while (p)
    {
        if (first && context.labelCycles(p, true))
            break;
        display(context, p->car, level);
        if ((p = p->cdr)) {
            if (isCons(p) && !isClosure(p) && !isPromise(p) && replenv != p && global != p) {
                context.wrap(level, displayLength(p->car));
            } else {
                context.s << " . ";
                display(context, p, level);
                p = 0;
            }
        }
        first = true;
    }
    context.s << ')';
}

void displayVector(Context& context, sexp v, int level)
{
    context.s << '[';
    Vector *vv = (Vector*)v;
    if (vv->l)
        level += displayLength(vv->e[0]) + 3;
    for (int i = 0; i < vv->l; ++i)
    {
        if (!context.labelCycles(vv->e[i], false))
            display(context, vv->e[i], level);
        if (i < vv->l-1)
        {
            context.s << ",";
            context.wrap(level, displayLength(vv->e[i+1]));
        }
    }
    context.s << ']';
}

const char * const character_table[] =
{
    "\000nul",       "\001soh", "\002stx",     "\003etx", "\004eot", "\005enq",    "\006ack", "\007bell",
    "\010backspace", "\011tab", "\012newline", "\013vt",  "\014ff",  "\015return", "\016so",  "\017si",
    "\020dle",       "\021dc1", "\022dc2",     "\023dc3", "\024dc4", "\025nak",    "\026syn", "\027etb",
    "\030can",       "\031em",  "\032sub",     "\033esc", "\034fs",  "\035gs",     "\036rs",  "\037us",
    "\040space",     "\177del", 0
};

void displayChar(Context& context, sexp exp)
{
    char buf[8];
    int c = ((Char*)exp)->ch;
    for (int i = 0; character_table[i]; ++i)
        if (c == *character_table[i]) {
            context.s << "#\\" << 1+character_table[i];
            return;
        }
    encodeUTF8(buf, ((Char*)exp)->ch);
    context.s << "#\\" << buf;
}

void displayString(Context& context, sexp exp)
{
    char buf[8];
    if (context.write)
        context.s << '"';
    String* string = (String*)exp;
    if (isUTF8(string))
        context.s << string->text;
    else if (isWide(string)) {
        for (uint32_t* p = (uint32_t*)string->text; *p; ++p)
            if (context.write && strchr("\007\b\t\n\r\"\\", *p))
                context.s << '\\' << encodeEscape(*p);
            else {
                encodeUTF8(buf, *p);
                context.s << buf;
            }
    } else {
        for (char* p = string->text; *p; ++p)
            if (context.write && strchr("\007\b\t\n\r\"\\", *p))
                context.s << '\\' << encodeEscape(*p);
            else {
                encodeUTF8(buf, *p);
                context.s << buf;
            }
    }
    if (context.write)
        context.s << '"';
}

// atoms are not yet utf8

void displayAtom(Context& context, sexp exp)
{
    if (context.write && voida == exp) {
        context.s << "#void";
    } else {
        for (char* p = atomText(exp); *p; ++p)
            if (context.write && strchr("\007\b\t\n\r\"\\", *p))
                context.s << '\\' << encodeEscape(*p);
            else
                context.s << *p;
    }
}

void displayNamed(Context& context, const char *kind, sexp exp)
{
    context.s << "#<" << kind << '@';
    for (sexp p = replenv; p; p = p->cdr)
        if (exp == p->car->cdr)
        {
            displayAtom(context, p->car->car);
            context.s << '>';
            return;
        }
    context.s << std::hex << (void*)exp << std::dec << '>';
}

void displayBignum(Context& context, sexp exp)
{
    std::vector<char> cs;
    ((Bignum*)exp)->nump->print(cs);
    for (char c : cs)
        if (c)
            context.s.put(c);
}

void displayRational(Context& context, sexp exp)
{
    Rat* ratp = ((Rational*)exp)->ratp;
    std::vector<char> cs;
    ratp->num.print(cs);
    for (char c : cs)
        if (c)
            context.s.put(c);
    context.s.put('/');
    std::vector<char> ds;
    ratp->den.print(ds);
    for (char c : ds)
        if (c)
            context.s.put(c);
}

void mapCycles(Context& context, sexp exp)
{
    if (isCons(exp)) {
        if (0 == context.seenMap[exp]) {
            context.seenMap[exp] = f;
            mapCycles(context, exp->car);
            mapCycles(context, exp->cdr);
        } else
            context.seenMap[exp] = t;
    } else if (isVector(exp)) {
        if (0 == context.seenMap[exp]) {
            context.seenMap[exp] = f;
            Vector* v = (Vector*)exp;
            for (int i = 0; i < v->l; ++i)
                mapCycles(context, v->e[i]);
        } else
            context.seenMap[exp] = t;
    }
}

// ensure there is some way of distinguishing a flonum
void displayFlonum(Context& context, sexp exp)
{
    std::streampos pos = context.s.tellp();
    context.s << asFlonum(exp);
    std::string sstr = context.s.str().substr(pos);
    if (std::string::npos == sstr.find("nan") &&
        std::string::npos == sstr.find("inf") &&
        std::string::npos == sstr.find('e') &&
        std::string::npos == sstr.find('.'))
        context.s << ".0";
}

void display(Context& context, sexp exp, int level)
{
    if (context.limit && context.s.tellp() >= context.limit)
        return;

    if (!exp) { context.s << "()"; return; }

    if (isCons(exp)) {
        bool quoted = false;
        if (isCons(exp->cdr))
        {
            quoted = true;
            sexp p = exp->car;
            if      (quote           == p) context.s << '\'';
            else if (quasiquote      == p) context.s <<  '`';
            else if (unquote         == p) context.s <<  ',';
            else if (unquotesplicing == p) context.s << ",@";
            else quoted = false;
        }
        if (quoted)
            display(context, exp->cdr->car, level);
        else if (replenv == exp)
            context.s << "#<repl environment>";
        else if (global == exp)
            context.s << "#<global environment>";
        else if (isClosure(exp))
            displayNamed(context, "closure", exp);
        else if (isPromise(exp))
            displayNamed(context, "promise", exp);
        else if (isComplex(exp)) {
            if (isRational(exp->cdr->car))
                displayRational(context, exp->cdr->car);
            else
                displayFlonum(context, exp->cdr->car);
            double im = asFlonum(exp->cdr->cdr->car);
            if (im > 0.0)
                context.s << '+';
            if (im)
            {
                if (isRational(exp->cdr->cdr->car))
                    displayRational(context, exp->cdr->cdr->car);
                else
                    displayFlonum(context, exp->cdr->cdr->car);
                context.s << 'i';
            }
        } else
            displayList(context, exp, level);
        return;
    }

    switch (((Stags*)exp)->stags)
    {
    default:       error("display: unknown object");
    case FLOAT: 
    case DOUBLE:   displayFlonum(context, exp);             break;
    case FIXNUM:   context.s << asFixnum(exp);              break;
    case STRING:   displayString(context, exp);             break;
    case ATOM:     displayAtom(context, exp);               break;
    case FUNCT:    displayNamed(context, "function", exp);  break;
    case FORM:     displayNamed(context, "form", exp);      break;
    case INPORT:   displayNamed(context, "input", exp);     break;
    case OUTPORT:  displayNamed(context, "output", exp);    break;
    case CHAR:     displayChar(context, exp);               break;
    case BIGNUM:   displayBignum(context, exp);             break;
    case RATIONAL: displayRational(context, exp);           break;
    case VECTOR:   displayVector(context, exp, level);
    }
}

void debug(const char *what, sexp exp)
{
    Context context(0, true, true);
    mapCycles(context, exp);
    if (what)
        context.s << what << ": ";
    display(context, exp, 0);
    context.s << std::endl;
    std::cout.write(context.s.str().c_str(), context.s.str().length());
}

// call this from gdb
void debug(sexp exp)
{
    debug(0, exp);
}

// string->symbol
sexp string_symbol(sexp x)
{
    assertString(x);
    return dynintern(strsave(stringText(x)));
}

// symbol->string
sexp symbol_string(sexp x)
{
    assertAtom(x);
    return dynstring(strsave(atomText(x)));
}

// string->number
sexp string_number(sexp exp)
{
    Context context(0, false, false);
    context.s << ((String*)exp)->text;
    return read(context.s, 0);
}

// string->list
sexp string_list(sexp x)
{
    sexp* mark = psp;
    assertString(x);
    String* string = (String*)x;
    if (isWide(string))
    {
        uint32_t* q = (uint32_t*)string->text;
        uint32_t* r = q;
        while (*r++) {}
        sexp p = save(0);
        do
            p = replace(cons(save(newcharacter(*--r)), p));
        while (q != r);
        return lose(mark, p);
    } else if (isUTF8(string)) {
        char* r = string->text;
        uint32_t wc;
        sexp p = save(0);
        while ((wc = read_utf8(r)))
            p = replace(cons(save(newcharacter(wc)), p));
        p = reverse(p);
        return lose(mark, reverse(p));
    } else {
        char* q = stringText(x);
        char* r = q + strlen(q);
        sexp p = save(0);
        do
            p = replace(cons(save(newcharacter(*--r)), p));
        while (q != r);
        return lose(mark, p);
    }
}

// list->string
sexp list_string(sexp s)
{
    if (!s)
        return newcell(STRING, 0);

    int i = 0;
    bool ascii = true;
    for (sexp p = s; p; p = p->cdr)
    {
        if (0x7f < ((Char*)(p->car))->ch)
            ascii = false;
        ++i;
    }

    if (ascii) {
        char* b = new char[i+1];
        char* q = b;
        for (sexp p = s; p; p = p->cdr)
            *q++ = ((Char*)(p->car))->ch;
        *q++ = 0;
        return dynstring(b);
    } else {
        uint32_t* b = new uint32_t[i+1];
        uint32_t* q = b;
        for (sexp p = s; p; p = p->cdr)
            *q++ = ((Char*)(p->car))->ch;
        *q++ = 0;
        return widestring(b);
    }
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
    case FLOAT :   return ((Float*)x)->flonum  == ((Float*)y)->flonum;
    case DOUBLE:   return ((Double*)x)->flonum == ((Double*)y)->flonum;
    case STRING:   return 0 == strcmp(stringText(x), stringText(y));    // UTF8
    case FIXNUM:   return ((Fixnum*)x)->fixnum  == ((Fixnum*)y)->fixnum;
    case CHAR:     return ((Char*)x)->ch        == ((Char*)y)->ch;
    case BIGNUM:   return *((Bignum*)x)->nump   == *((Bignum*)y)->nump;
    case RATIONAL: return *((Rational*)x)->ratp == *((Rational*)y)->ratp;
    case VECTOR:   return cmpv(seenx, seeny, x, y);
    default:       return 0;
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

// resets closures like letrec
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
    if (isAtom(p))
    {
        char* text = atomText(p);
        int len = strlen(text);
        if (len > sizeof(errorBuffer)-strlen(msg))
            len = sizeof(errorBuffer)-strlen(msg);
        char *r = errorBuffer+strlen(msg);
        *r++ = '"';
        for (char* q = text; *q; )
            *r++ = *q++;
        *r++ = '"';
        *r++ = 0;
    }
    error(errorBuffer);
}

// bound?
sexp boundp(sexp p, sexp env)
{
    for (sexp q = env; q; q = q->cdr)
        if (p->cdr->car == q->car->car)
            return t;
    return f;
}

// fetch cached value of an atom
static inline sexp value_put(sexp p, sexp v)
{
    return ((Atom*)p)->body->car = v;
}

// cache value of an atom
static inline sexp value_get(sexp p)
{
    return ((Atom*)p)->body->car;
}

// invalidate the cache
void purge_values(void)
{
    for (sexp q = atoms; q; q = q->cdr)
        value_put(q->car, 0);
}

// define
sexp define(sexp p, sexp r)
{
    for (sexp q = replenv; q; q = q->cdr)
        if (p == q->car->car)
        {
            q->car->cdr = r;
            return voida;
        }
    replenv = cons(save(cons(p, r)), replenv);
    return lose(voida);
}

// undefine
sexp undefine(sexp p)
{
    value_put(p, 0);
    if (p == global->car->car)
        global = global->cdr;
    if (p == replenv->car->car)
        replenv = replenv->cdr;
    else
        for (sexp q = replenv; q; q = q->cdr)
            if (q->cdr && p == q->cdr->car)
                q->cdr = q->cdr->cdr;
    return voida;
}

// set!
sexp set(sexp p, sexp r, sexp env)
{
    value_put(p, 0);
    for (sexp q = env; q; q = q->cdr)
        if (p == q->car->car)
        {
            q->car->cdr = r;
            return voida;
        }

    lookup_error("unbound: set ", p);
}

// retrieve the value of a variable in an environment
sexp get(sexp p, sexp env)
{
    sexp g = global;
    sexp v = value_get(p);
    if (v) {
        // the variable is cached
        for (sexp q = env; q; q = q->cdr)
            if (p == q->car->car)
                // but hidden by a local
                return q->car->cdr;
            else if (g == q)
                // we can use the cached value
                return v;
    } else {
        // the variable is not cached
        for (sexp q = env; q; q = q->cdr)
            if (g == q) {
                // but it is global
                for ( ; q; q = q->cdr)
                    if (p == q->car->car)
                        // so set the value cell
                        return value_put(p, q->car->cdr);
                break;
            } else if (p == q->car->car)
                // the variable is local
                return q->car->cdr;
    }

    lookup_error("unbound: get ", p);
}

// evaluate a list of arguments in an environment
sexp evlis(sexp p, sexp env)
{
    sexp* mark = psp;
    save(p, env);
    return p ? lose(mark, cons(save(eval(p->car, env)), save(evlis(p->cdr, env)))) : 0;
}

// associate formal and actual parameters in an environment
sexp assoc(sexp names, sexp values, sexp env)
{
    sexp* mark = psp;
    save(values, names, env);
    if (!isCons(names))
        return lose(mark, cons(save(cons(names, values)), env));
    if (!values)
        return lose(mark, cons(save(cons(names->car, voida)),
                               save(assoc(names->cdr, values, env))));
    return lose(mark, cons(save(cons(names->car, values->car)),
                           save(assoc(names->cdr, values->cdr, env))));
}

// environment
sexp environment(sexp exp, sexp env) { return replenv; }

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

    if (!(p = p->cdr) || !p->cdr)
        error("define: missing operands");

    if (isCons(p->car))
    {
        // (define (foo ...)
        sexp k = p->car->car;
        if (!isAtom(k))
            error("define: variable must be a symbol");
        value_put(k, 0);
        sexp v = replace(cons(lambda, save(cons(p->car->cdr, p->cdr))));
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
        return lose(mark, v->cdr->cdr->car = cons(save(cons(p->car->car, save(v))), env));
    } else {
        sexp k = p->car;
        if (!isAtom(k))
            error("define: variable must be a symbol");
        value_put(k, 0);
        for (sexp q = env; q; q = q->cdr)
            if (k == q->car->car)
            {
                q->car->cdr = eval(p->cdr->car, env);
                return lose(mark, env);
            }
        return lose(mark, cons(replace(cons(p->car, save(eval(p->cdr->car, env)))), env));
    }
}

// top level define sets replenv
sexp defineform(sexp p, sexp env)
{
    sexp e = nesteddefine(p, env);
    if (replenv == env)
        replenv = e;
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
 * if the predicate evaluates not #f
 *    then evaluate the consequent
 *    else evaluate the alternative
 */
sexp ifform(sexp exp, sexp env)
{
    if (!(exp = exp->cdr))
        error("if: missing predicate");
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
    if (!(exp = exp->cdr))
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
    if (!(exp = exp->cdr))
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

    if (!(exp = exp->cdr))
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
    if (!isAtom(exp->car))
        error("set!: variable must be a symbol");
    if (!exp || !exp->cdr)
        error("set!: missing operands");
    return lose(set(exp->car, save(eval(exp->cdr->car, env)), env));
}

// accumulates names from a let expression
sexp names(sexp bs)
{
    return bs ? lose(replace(cons(bs->car->car, save(names(bs->cdr))))) : 0;
}

// accumulates values from a let expression
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
        if (!v->car->cdr || v->car->cdr->cdr)
            error("let: malformed expression");
        else
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
        if (!v->car->cdr || v->car->cdr->cdr)
            error("let*: malformed expression");
        else
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
        e = save(cons(save(cons(v->car->car, 0)), e));
    for (sexp v = exp->car; v; v = v->cdr)
        if (!v->car->cdr || v->car->cdr->cdr)
            error("letrec: malformed expression");
        else
            set(v->car->car, save(eval(v->car->cdr->car, e)), e);
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
    sexp* mark = psp;
    save(exp);
    sexp e = save(env);
    exp = exp->cdr;
    // bind all the variables to their values
    for (sexp v = exp->car; v; v = v->cdr)
        if (!v->car->cdr)
            error("do: missing value");
        else
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
            if (v->car->cdr->cdr)
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
        int a = arity(fun);
        if (0 == a)
            return lose(mark, (*(Varargp)((Funct*)fun)->funcp)(args));
        sexp arg0 = save(args ? args->car : voida);
        if (1 == a)
            return lose(mark, (*(Oneargp)((Funct*)fun)->funcp)(arg0));
        sexp arg1 = save(args && (args = args->cdr) ? args->car : voida);
        if (2 == a)
            return lose(mark, (*(Twoargp)((Funct*)fun)->funcp)(arg0, arg1));
        sexp arg2 = save(args && (args = args->cdr) ? args->car : voida);
        if (3 == a)
            return lose(mark, (*(Threeargp)((Funct*)fun)->funcp)(arg0, arg1, arg2));
        error("apply: unsupported arity");
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
}

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
    if (f != tracing && p && (t != p) && (f != p) && (isAtom(p) || isCons(p)))
    {
        ++indent;
        Context context(0, true, false);
        context.s << "eval:";
        for (int i = indent; --i >= 0; context.s << ' ') {}
        display(context, p, 0);
        context.s << " ==> ";
        if (!p || f == p || t == p || (OTHER & shortType(p)) && shortType(p) > ATOM)
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
        display(context, p, 0);
        context.s << std::endl;
        std::cout.write(context.s.str().c_str(), context.s.str().length());
        --indent;
        return lose(mark, p);

    } else {

        if (!p || f == p || t == p || (OTHER & shortType(p)) && shortType(p) > ATOM)
            return p;

        if (isAtom(p))
            return get(p, env);

        save(p, env);
        sexp fun = save(eval(p->car, env));

        if (isForm(fun))
            return lose(mark, (*((Form*)fun)->formp)(p, env));

        if (isFunct(fun))
        {
            // this is probably better than calling evlis/apply
            int a = arity(fun);
            if (0 == a)
                return lose(mark, (*(Varargp)((Funct*)fun)->funcp)(save(evlis(p->cdr, env))));
            sexp arg0 = save((p = p->cdr) ? eval(p->car, env) : voida);
            if (1 == a)
                return lose(mark, (*(Oneargp)((Funct*)fun)->funcp)(arg0));
            sexp arg1 = save(p && (p = p->cdr) ? eval(p->car, env) : voida);
            if (2 == a)
                return lose(mark, (*(Twoargp)((Funct*)fun)->funcp)(arg0, arg1));
            sexp arg2 = save(p && (p = p->cdr) ? eval(p->car, env) : voida);
            if (3 == a)
                return lose(mark, (*(Threeargp)((Funct*)fun)->funcp)(arg0, arg1, arg2));
            error("eval: unsupported arity");
        }

        return lose(mark, apply(fun, save(evlis(p->cdr, env))));
    }
}

sexp xeval(sexp p, sexp env)
{
    if (!(p && isCons(env) && isCons(env->car)))
        error("eval: bad environment");
    return eval(p, env);
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

enum NumStatus { NON_NUMERIC, FIXED, RATIO, FLOATING, COMPLEX };

int accept(std::stringstream& s, std::istream& f, int c)
{
    s.put(c); return f.get();
}

// scan a number from fin, copy it to s, set status, return next character
int scanNumber(std::stringstream& s, std::istream& fin, NumStatus& status)
{
    int c = fin.get();
    status = NON_NUMERIC;
    while (isspace(c))
        c = fin.get();
    if ('-' == c)
        c = accept(s, fin, c);
    while (isdigit(c))
        { status = FIXED; c = accept(s, fin, c); }
    if ('.' == c)
        { status = FLOATING; c = accept(s, fin, c); }
    while (isdigit(c))
        { status = FLOATING; c = accept(s, fin, c); }
    if (status > NON_NUMERIC && ('e' == c || 'E' == c))
    {
        status = NON_NUMERIC;
        c = accept(s, fin, c);
        if ('-' == c)
            c = accept(s, fin, c);
        else if ('+' == c)
            c = accept(s, fin, c);
        while (isdigit(c))
        {
            status = FLOATING;
            c = accept(s, fin, c);
        }
    }

    if (status == FIXED && '/' == c)
    {
        c = accept(s, fin, c);
        if ('-' == c)
            c = accept(s, fin, c);
        while (isdigit(c))
            { status = RATIO; c = accept(s, fin, c); }
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
    case '#':  switch (c = fin.get())
               {
               case 'f': return f;
               case 't': return t;
               case '\\':
                    c = fin.get();
                    do
                        c = accept(s, fin, c);
                    while (0 <= c && !isspace(c) && ')' != c && ']' !=c && ',' != c);
                    fin.unget();
                    const char* buf = s.str().c_str();
                    for (int i = 0; character_table[i]; ++i)
                        if (!strcmp(buf, 1+character_table[i]))
                            return newcharacter(*character_table[i]);
                    return newcharacter(*buf);
                }
    case '-':   c = fin.get();
                if ('.' == c || isdigit(c))
                    s.put('-');
                else
                    { fin.unget(); return minus; } 
    }

    fin.unget();

    NumStatus status, rstatus, istatus;

    c = scanNumber(s, fin, rstatus);

    size_t split = s.tellp();

    if (NON_NUMERIC < rstatus && ('+' == c || '-' == c)) {
        s << (char)fin.get();
        c = scanNumber(s, fin, istatus);
        if ('i' == c)
        {
            s << (char)fin.get();
            status = COMPLEX;
        }
    } else if (NON_NUMERIC < status && '@' == c) {
        s << (char)fin.get();
        c = scanNumber(s, fin, istatus);
        status = COMPLEX;
    } else
        status = rstatus;

    if (COMPLEX == status)
    {
        std::string cdata = s.str();

        sexp real, imag;

        if (RATIO == rstatus)
        {
            std::string realdata = cdata.substr(0, split);
            int realdiv = realdata.find_first_of('/');
            real = save(newrational(Num(realdata.substr(0,realdiv).c_str()),
                                    Num(realdata.substr(realdiv+1).c_str())));
        } else
            { double re; s >> re; real = save(newflonum(re)); }

        c = cdata.at(split);

        if (RATIO == istatus)
        {
            std::string imagdata = cdata.substr(split+1);
            imagdata = imagdata.substr(0, imagdata.length()-1);
            int imagdiv = imagdata.find_first_of('/');
            imag = save(newrational(Num(imagdata.substr(0,imagdiv).c_str()),
                                    Num(imagdata.substr(imagdiv+1).c_str())));
        } else
            { double im; s >> im; imag = save(newflonum(im)); }

        switch (c)
        {
        case '+':
            return lose(mark, make_complex(real, imag));
        case '-':
            return lose(mark, make_complex(real, save(unineg(imag))));
        case '@':
            double r = isRational(real) ? asRational(real).to_double() : asFlonum(real);
            double theta = isRational(imag) ? asRational(imag).to_double() : asFlonum(imag);
            return lose(mark, make_complex(save(newflonum(r * cos(theta))),
                                           save(newflonum(r * sin(theta)))));
        }
    }

    switch (status)
    {
    case FIXED:
        { std::string n; s >> n; Num num(n.c_str()); return bignumResult(num); }
    case FLOATING:
        { double re; s >> re; return newflonum(re); }
    case RATIO:
        { std::string ratio; s >> ratio; int pos = ratio.find_first_of('/');
          return newrational(Num(ratio.substr(0,pos).c_str()),
                             Num(ratio.substr(pos+1).c_str())); }
    default:
        break;
    }

    (void)fin.get();
    bool ascii = true;
    std::vector<uint32_t> string;
    if ('"' != c) {
        // read an atom (not yet utf8)
        while (0 <= c && !strchr("( )[,]\t\r\n", c))
            c = accept(s, fin, c);
        fin.unget();
        return dynintern(strsave(s.str().c_str()));
    } else {
        // read a string (utf8)
        c = fin.get();
        while (0 <= c && c != '"')
        {
            if ('\\' == c)
            {
                c = read_utf8(fin);
                if ('x' == c)
                {
                    int x = 0;
                    c = fin.get();
                    while (0 <= c && isxdigit(c))
                    {
                        if (isdigit(c))
                            x = x << 4 | (c - '0');
                        else if (islower(c))
                            x = x << 4 | (c - 'a');
                        else
                            x = x << 4 | (c - 'A');
                        c = fin.get();
                    }
                    if (0x7f < x)
                        ascii = false;
                    string.push_back(x);
                    if (';' == c)
                        c = read_utf8(fin);
                    if (0 < c && '"' != c)
                    {
                        string.push_back(c);
                        c = read_utf8(fin);
                    }
                } else if (0 <= c && !strchr("( )[,]\t\r\n", c)) {
                    uint32_t x = decodeEscape(c);
                    if (0x7f < x)
                        ascii = false;
                    string.push_back(x);
                    c = read_utf8(fin);
                } else
                    while (0 <= c && strchr("( )[,]\t\r\n", c))
                        c = read_utf8(fin);
            } else {
                if (0x7f < c)
                    ascii = false;
                string.push_back(c);
                c = read_utf8(fin);
            }
        }
        if (ascii)
        {
            for (uint32_t wc : string)
                s.put(wc);
            return dynstring(strsave(s.str().c_str()));
        } else {
            string.push_back(0);
            return widestring(string);
        }
    }
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
            break;
        while (unquote == s->car)
            s = s->cdr->car;
        q = replace(cons(s, q));
        s = scan(fin);
        if (rbracket == s)
            break;
        if (comma != s)
            error("comma expected in vector");
    }
    return lose(mark, list_vector(save(reverse(q))));
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
    exit(1);
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
    { "eval",                              2, (void*)xeval },
    { "exact?",                            1, (void*)exactp },
    { "exact->inexact",                    1, (void*)exact_inexact },
    { "exp",                               1, (void*)expff },
    { "floor",                             1, (void*)floorff },
    { "force",                             1, (void*)force },
    { "form?",                             1, (void*)formp },
    { "function?",                         1, (void*)functionp },
    { "gc",                                0, (void*)gc },
    { "gcd",                               2, (void*)gcd },
    { "get-output-string",                 1, (void*)get_output_string },
    { "inexact?",                          1, (void*)inexactp },
    { "inexact->exact",                    1, (void*)inexact_exact },
    { "input-port?",                       1, (void*)input_portp },
    { "integer?",                          1, (void*)integerp },
    { "integer->char",                     1, (void*)integer_char },
    { "isqrt",                             1, (void*)isqrtf },
    { "lcm",                               2, (void*)lcm },
    { "lfsr-shift",                        2, (void*)lfsr_shift },
    { "list?",                             1, (void*)listp },
    { "list->string",                      1, (void*)list_string },
    { "list->vector",                      1, (void*)list_vector },
    { "load",                              1, (void*)load },
    { "log",                               1, (void*)logff },
    { "magnitude",                         1, (void*)magnitude },
    { "make-string",                       0, (void*)make_string },
    { "make-vector",                       0, (void*)make_vector },
    { "modulo",                            2, (void*)moduloff },
    { "neg",                               1, (void*)unineg },
    { "negative?",                         1, (void*)negativep },
    { "newline",                           0, (void*)newline },
    { "not",                               1, (void*)isnot },
    { "null?",                             1, (void*)nullp },
    { "number?",                           1, (void*)numberp },
    { "number->string",                    1, (void*)number_string },
    { "odd?",                              1, (void*)oddp },
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
    { "random",                            0, (void*)randomf },
    { "rational?",                         1, (void*)rationalp },
    { "read",                              0, (void*)readf },
    { "read-char",                         0, (void*)read_char },
    { "real?",                             1, (void*)realp },
    { "remainder",                         2, (void*)remainderff },
    { "reverse!",                          1, (void*)reverse },
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
    { "time",                              1, (void*)timeff },
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
    { "set!",        setform },
    { "unless",      unlessform },
    { "when",        whenform },
    { "while",       whileform },
    { 0,             0 }
};

void define_staintern_sexpr(const char* name, sexp value)
{
    define(staintern(name), value);
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
    inport  = cinport  = newcell(INPORT,  (sexp)&cinStream);
    outport = coutport = newcell(OUTPORT, (sexp)&coutStream);
    errport = cerrport = newcell(OUTPORT, (sexp)&cerrStream);

    // constants
    zero = newfixnum(0);
    one  = newfixnum(1);

    // names
    closure         = staintern("closure");
    commaat         = staintern(",@");
    comma           = staintern(",");
    complex         = staintern("complex");
    definea         = staintern("define");
    dot             = staintern(".");
    elsea           = staintern("else");
    eof             = staintern("#eof");
    f               = staintern("#f");
    lambda          = staintern("lambda");
    lbracket        = staintern("[");
    lparen          = staintern("(");
    minus           = staintern("-");
    promise         = staintern("promise");
    qchar           = staintern("'");
    quasiquote      = staintern("quasiquote");
    quote           = staintern("quote");
    rbracket        = staintern("]");
    rparen          = staintern(")");
    t               = staintern("#t");
    tick            = staintern("`");
    unquote         = staintern("unquote");
    unquotesplicing = staintern("unquote-splicing");
    voida           = staintern("");

    // streams
    define_staintern_sexpr("cerr",     errport);
    define_staintern_sexpr("cin",      inport);
    define_staintern_sexpr("cout",     outport);

    // metasyntax
    define_staintern_sexpr("comma",    comma);
    define_staintern_sexpr("commaat",  commaat);
    define_staintern_sexpr("dot",      dot);
    define_staintern_sexpr("lbracket", lbracket);
    define_staintern_sexpr("lparen",   lparen);
    define_staintern_sexpr("qchar",    qchar);
    define_staintern_sexpr("rbracket", rbracket);
    define_staintern_sexpr("rparen",   rparen);
    define_staintern_sexpr("tick",     tick);
    define_staintern_sexpr("void",     voida);

    for (FuncTable* p = funcTable; p->name; ++p)
    {
        sexp* mark = psp;
        Funct* f = (Funct*)save(newcell(FUNCT));
        f->tags[2] = p->arity; f->funcp = p->funcp;
        define_staintern_sexpr(p->name, (sexp)f);
        psp = mark;
    }

    for (FormTable* p = formTable; p->name; ++p)
    {
        sexp* mark = psp;
        Form* f = (Form*)save(newcell(FORM));
        f->formp = p->formp;
        define_staintern_sexpr(p->name, (sexp)f);
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

    load(stastring("init.ss"));

    global = replenv;

    fixenvs(global);

    if (argc > 1)
    {
        load(stastring(argv[1]));
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
            if ((int)(psp-protect) > 1)
                std::cout << (int)(psp-protect) << " items remain on protection stack" << std::endl;
            else
                std::cout << "one item remains on protection stack" << std::endl;

        std::cout << "> ";
        std::cout.flush();
        expr = read(std::cin, 0);
        if (eof == expr)
            break;
        killed = 0;
        valu = eval(expr, replenv);
        {
            Context context(0, false, true);
            mapCycles(context, valu);
            display(context, valu, 0);
            std::cout.write(context.s.str().c_str(), context.s.str().length());
            if (voida != valu)
                std::cout << std::endl;
        }
    }
    return 0;
}

