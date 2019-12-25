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
#include <float.h>
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
#define error(s) do { if (killed) assert(false); longjmp(the_jmpbuf, (long)s); } while(0)
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
    RATIONAL = 0x0C01,
    CLOSURE  = 0x0D01
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
sexp scanahead;             // pushed-back token
sexp *psp;          		// protection stack pointer
sexp *psend;            	// protection stack end
sexp *protect;      		// protection stack
int  argc;                  // from main
char** argv;                // from main
char** envp;                // from main

sexp comma, commaat, complex, definea, dot, elsea, eof, f, lambda, lbracket;
sexp lparen, minus, one, plus, promise, qchar, quasiquote, quote, rbracket;
sexp rparen, t, tick, unquote, unquotesplicing, voida, zero, hash, backslash;
sexp bang, banga, fa, falsea, ta, truea, voidaa;

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
struct Closure  { char tags[sizeof(sexp)];                        sexp        expenv; };

// supports uglyprinting
struct Context
{
    static const int eol  = 70;
    static const int tabs =  4;

    bool write;
    bool pretty;
    bool cyclic;
    int  label;
    int  radix;
    std::streampos pos;
    std::streampos limit;
    std::stringstream s;
    std::unordered_map<sexp,sexp> seenMap;
    Context(int limit, bool write, bool pretty, bool cyclic, int radix) :
        limit(limit), label(0), write(write), pretty(pretty), cyclic(cyclic), radix(radix)
        { setp(); setr(); pos = s.tellp(); }
    void setp() { s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15); }
    void setr() { if (radix ==  8) s << std::oct; else
                  if (radix == 16) s << std::hex; else
                                   s << std::dec; }
    void wrap(int level, int length)
        { if (pretty && s.tellp() - pos + length > eol) newline(level); else space(); }
    void newline(int level)
        { s << '\n'; pos = s.tellp(); for (int i = level; --i >= 0; s << ' ') {} }
    void space(void) { s << ' '; }
    bool labelCycles(sexp exp, bool last);
};

void mapCycles(Context& context, sexp exp);
void display(Context& context, sexp p, int level);

static inline int  shortType(const sexp p)  { return (~MARK &   ((Stags*)p)->stags); }
static inline int  arity(const sexp p)      { return           ((Funct*)p)->tags[2]; }
static inline int  stringtag(const sexp p)  { return          ((String*)p)->tags[2]; }
static inline bool isMarked(const sexp p)   { return ( MARK &  ((Tags*)p)->tags[0]); }
static inline bool isCons(const sexp p)     { return !(OTHER & ((Tags*)p)->tags[0]); }
static inline bool isAtom(const sexp p)     { return ATOM           == shortType(p); }
static inline bool isString(const sexp p)   { return STRING         == shortType(p); }
static inline bool isFunct(const sexp p)    { return FUNCT          == shortType(p); }
static inline bool isForm(const sexp p)     { return FORM           == shortType(p); }
static inline bool isFixnum(const sexp p)   { return FIXNUM         == shortType(p); }
static inline bool isFloat(const sexp p)    { return FLOAT          == shortType(p); }
static inline bool isDouble(const sexp p)   { return DOUBLE         == shortType(p); }
static inline bool isChar(const sexp p)     { return CHAR           == shortType(p); }
static inline bool isInPort(const sexp p)   { return INPORT         == shortType(p); }
static inline bool isOutPort(const sexp p)  { return OUTPORT        == shortType(p); }
static inline bool isVector(const sexp p)   { return VECTOR         == shortType(p); }
static inline bool isBignum(const sexp p)   { return BIGNUM         == shortType(p); }
static inline bool isRational(const sexp p) { return RATIONAL       == shortType(p); }
static inline bool isClosure(const sexp p)  { return CLOSURE        == shortType(p); }
static inline bool isFlonum(const sexp p)   { return isFloat(p) || isDouble(p);      }

bool isPromise(sexp p)
{
    return isCons(p) && promise == p->car &&        // (promise
           (p = p->cdr) && isCons(p) &&             //  forced
           (p = p->cdr) && isCons(p) &&             //  value
           (p = p->cdr) && isCons(p) &&             //  exp
           (p = p->cdr) && isCons(p) &&             //  env)
           !p->cdr;
}

bool isComplex(sexp p)
{
    return isCons(p) && complex == p->car &&   // (complex
           (p = p->cdr) && isCons(p) &&        //  real-part
           (p = p->cdr) && isCons(p) &&        //  imag-part
           !p->cdr;                            // )
}

bool isReal(sexp x)
{
    return isFixnum(x) || isFlonum(x) || isBignum(x) || isRational(x);
}

bool isNumber(sexp x)
{
    return isFixnum(x) || isFlonum(x) || isBignum(x) || isRational(x) || isComplex(x);
}

static inline sexp boolwrap(bool x) { return x ? t : f; }

// boolean?
sexp booleanp(sexp x) { return boolwrap(t == x || f == x); }

// form?
sexp formp(sexp p) { return boolwrap(p && isForm(p)); }

// function?
sexp functionp(sexp p) { return boolwrap(p && isFunct(p)); }

// closure?
sexp closurep(sexp p) { return boolwrap(p && isClosure(p)); }

// promise?
sexp promisep(sexp p) { return boolwrap(p && isPromise(p)); }

// rational?
sexp rationalp(sexp p) { return boolwrap(p && isRational(p)); }

// exact?
sexp exactp(sexp p) { return boolwrap(p && (isFixnum(p) || isRational(p) || isBignum(p))); }

// exact-integer?
sexp exact_integerp(sexp p) { return boolwrap(p && (isFixnum(p) || isBignum(p))); }

// inexact?
sexp inexactp(sexp p) { return boolwrap(p && isFlonum(p)); }

// complex?
sexp complexp(sexp p) { return boolwrap(p && isComplex(p)); }

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
    } else if (isClosure(p)) {
        Closure* clo = (Closure*)p;
        mark(clo->expenv);
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

enum StringTags { STATIC, DYNAMIC };

static inline bool isMutable(String *s) { return STATIC != s->tags[2]; }

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
    mark(scanahead);

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

void assertCons(sexp s)     { if (!s || !isCons(s))     error("not pair"); }
void assertAtom(sexp s)     { if (!s || !isAtom(s))     error("not symbol"); }
void assertChar(sexp s)     { if (!s || !isChar(s))     error("not a character"); }
void assertFixnum(sexp s)   { if (!s || !isFixnum(s))   error("not an integer"); }
void assertString(sexp s)   { if (!s || !isString(s))   error("not a string"); }
void assertInPort(sexp s)   { if (!s || !isInPort(s))   error("not an input port"); }
void assertOutPort(sexp s)  { if (!s || !isOutPort(s))  error("not an output port"); }
void assertComplex(sexp s)  { if (!s || !isComplex(s))  error("not complex"); }
void assertRational(sexp s) { if (!s || !isRational(s)) error("not rational"); }
void assertPromise(sexp s)  { if (!s || !isPromise(s))  error("not a promise"); }

void assertFlonum(sexp s)   { if (!s || !isFlonum(s) && !isFixnum(s) && !isRational(s) && !isBignum(s))
                              error("not a real number"); }

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
sexp car(sexp p) { if (!p || !isCons(p)) error("error: car of non-pair"); return p->car; }

// cdr
sexp cdr(sexp p) { if (!p || !isCons(p)) error("error: cdr of non-pair"); return p->cdr; }

// set-car!
sexp set_car_(sexp p, sexp q)
{
    if (!p || !isCons(p)) error("error: set-car! of non-pair"); p->car = q; return voida;
}

// set-cdr!
sexp set_cdr_(sexp p, sexp q)
{
    if (!p || !isCons(p)) error("error: set-cdr! of non-pair"); p->cdr = q; return voida;
}

// and
sexp andform(sexp p, sexp env)
{
    sexp q = t;
    while ((p = p->cdr) && f != (q = eval(p->car, env))) {}
    return q;
}

// or
sexp orform(sexp p, sexp env)
{
    sexp q = f;
    while ((p = p->cdr) && f == (q = eval(p->car, env))) {}
    return q;
}

// trace
sexp trace(sexp arg)
{
    sexp r = tracing;
    tracing = arg;
    return r;
}

// cputime
sexp cputime(sexp args)
{
    struct timespec ts;
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &ts);
    return newflonum(ts.tv_sec + ts.tv_nsec / 1000000000.0);
}

// current-second
sexp current_second(sexp args)
{
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return newflonum(ts.tv_sec + ts.tv_nsec / 1000000000.0);
}

static inline int asFixnum(sexp p) { return ((Fixnum*)p)->fixnum; }

static inline Num asBignum(sexp x) { return *((Bignum*)x)->nump; }

static inline Rat asRational(sexp x) { return *((Rational*)x)->ratp; }

static inline sexp real_part(sexp x) { return x->cdr->car; }

static inline sexp imag_part(sexp x) { return x->cdr->cdr->car; }

// zero?
sexp zerop(sexp x)
{
    if (x)
    {
        if (isDouble(x))
        {
            double xf = ((Double*)x)->flonum;
            return boolwrap(-DBL_MIN < xf && xf < DBL_MIN);
        }
        if (isFloat(x))
        {
            float xf = ((Float*)x)->flonum;
            return boolwrap(-FLT_MIN < xf && xf < FLT_MIN);
        }
        if (isFixnum(x))
            return boolwrap(0 == ((Fixnum*)x)->fixnum);
        if (isRational(x))
            return boolwrap(asRational(x) == 0);
        if (isBignum(x))
            return boolwrap(asBignum(x) == 0);
    }
    error("zero?: operand");
}

double asFlonum(sexp p)
{
    if (p)
    {
        if (isComplex(p) && f != zerop(imag_part(p)))
            p = real_part(p);
        switch (shortType(p))
        {
        default:       break;
        case FLOAT:    return ((Float*)p)->flonum;
        case DOUBLE:   return ((Double*)p)->flonum;
        case FIXNUM:   return (double) asFixnum(p);
        case BIGNUM:   return ((Bignum*)p)->nump->to_double();
        case RATIONAL: return ((Rational*)p)->ratp->to_double();
        }
    }
    error("asFlonum: not a flonum");
}

// supports labeling of cyclic structures
bool Context::labelCycles(sexp exp, bool last)
{
    if (cyclic)
    {
        sexp value = seenMap[exp];
        if (value && isFixnum(value)) {
            if (last)
                s << ". ";
            s << '#' << asFixnum(value) << '#';
            return true;
        } else if (t == value) {
            s << '#' << label << '=';
            seenMap[exp] = newfixnum(label++);
        }
    }
    return false;
}

// negative?
sexp negativep(sexp x)
{
    return boolwrap(x &&
                    isRational(x) ? (asRational(x).num <  0 ?
                                     asRational(x).den >= 0 :
                                     asRational(x).den <  0) :
                    isBignum(x)   ?  asBignum(x) < 0 :
                                     asFlonum(x) < 0);
}

// positive?
sexp positivep(sexp x)
{
    return boolwrap(x &&
                    isRational(x) ? (asRational(x).den >= 0 ?
                                     asRational(x).num >  0 :
                                     asRational(x).num <  0) :
                    isBignum(x)   ?  asBignum(x) > 0 :
                                     asFlonum(x) > 0);
}

// <
sexp ltp(sexp args)
{
    if (!args)
        error("<: no arguments");
    sexp x = args->car;
    while (args = args->cdr)
    {
        if (asFlonum(x) >= asFlonum(args->car))
            return f;
        x = args->car;
    }
    return t;
}

// <=
sexp lep(sexp args)
{
    if (!args)
        error("<=: no arguments");
    sexp x = args->car;
    while (args = args->cdr)
    {
        if (asFlonum(x) > asFlonum(args->car))
            return f;
        x = args->car;
    }
    return t;
}

// >=
sexp gep(sexp args)
{
    if (!args)
        error(">=: no arguments");
    sexp x = args->car;
    while (args = args->cdr)
    {
        if (asFlonum(x) < asFlonum(args->car))
            return f;
        x = args->car;
    }
    return t;
}

// >
sexp gtp(sexp args)
{
    if (!args)
        error(">: no arguments");
    sexp x = args->car;
    while (args = args->cdr)
    {
        if (asFlonum(x) <= asFlonum(args->car))
            return f;
        x = args->car;
    }
    return t;
}

sexp make_rectangular(sexp re, sexp im)
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

// prepare operands for arithmetic
Rat toRational(sexp x)
{
    if (x)
    {
        if (isRational(x))
            return asRational(x);
        if (isBignum(x))
            return Rat(asBignum(x));
        if (isFixnum(x))
            return Rat(asFixnum(x));
    }
    error("not a number");
}

// prepare operands for arithmetic
Num toBignum(sexp x)
{
    if (x)
    {
        if (isBignum(x))
            return asBignum(x);
        if (isFixnum(x))
            return Num(asFixnum(x));
    }
    error("not an integer");
}

// create appropriate sexp for arithmetic result
sexp bignumResult(Num result)
{
    int r; return result.can_convert_to_int(&r) ? newfixnum(r) : newbignum(result);
}

// create appropriate sexp for arithmetic result
sexp rationalResult(Rat result)
{
    result.reduce();

    if (result.den == 1)
        return bignumResult(result.num);

    return newrational(result);
}

// numerator
sexp numerator(sexp x)
{
    if (x)
    {
        if (isFixnum(x) || isBignum(x))
            return x;
        if (isRational(x))
            return bignumResult(((Rational*)x)->ratp->num);
    }
    error("numerator: not rational");
}

// denominator
sexp denominator(sexp x)
{
    if (x)
    {
        if (isFixnum(x) || isBignum(x))
            return one;
        if (isRational(x))
            return bignumResult(((Rational*)x)->ratp->den);
    }
    error("denominator: not rational");
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
    if (x && y)
    {
        if (isFixnum(x) && isFixnum(y))
            return newfixnum(igcd(asFixnum(x), asFixnum(y)));
        return bignumResult(Num::gcd(toBignum(x), toBignum(y)));
    }
    error("gcd: operands");
}

// lcm
sexp lcm(sexp x, sexp y)
{
    if (x && y)
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

    error("lcm: operands");
}

// x + y
sexp sum(sexp x, sexp y)
{
    if (!x || !y)
        error("sum: operands");

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
            return lose(mark, make_rectangular(save(sum(real_part(x), real_part(y))),
                                               save(sum(imag_part(x), imag_part(y)))));
        else
            return lose(mark, make_rectangular(save(sum(real_part(x), y)), imag_part(x)));
    } else if (isComplex(y))
        return lose(mark, make_rectangular(save(sum(x, real_part(y))), imag_part(y)));

    if (isFlonum(x))
        return newflonum(asFlonum(x) + asFlonum(y));

    if (isFlonum(y))
        return newflonum(asFlonum(x) + asFlonum(y));

    if (isRational(x) || isRational(y))
        return rationalResult(toRational(x) + toRational(y));

    return bignumResult(toBignum(x) + toBignum(y));
}

// x - y
sexp diff(sexp x, sexp y)
{
    if (!x || !y)
        error("diff: operands");

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
            return lose(mark, make_rectangular(save(diff(real_part(x), real_part(y))),
                                               save(diff(imag_part(x), imag_part(y)))));
        else
            return lose(mark, make_rectangular(save(diff(real_part(x), y)), imag_part(x)));
    } else if (isComplex(y))
        return lose(mark, make_rectangular(save(diff(x, real_part(y))), imag_part(y)));

    if (isFlonum(x))
        return newflonum(asFlonum(x) - asFlonum(y));

    if (isFlonum(y))
        return newflonum(asFlonum(x) - asFlonum(y));

    if (isRational(x) || isRational(y))
        return rationalResult(toRational(x) - toRational(y));

    return bignumResult(toBignum(x) - toBignum(y));
}

// x * y
sexp product(sexp x, sexp y)
{
    if (!x || !y)
        error("product: operands");

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
        return lose(mark, make_rectangular(save(diff(save(product(xr, yr)), save(product(xi, yi)))),
                                           save( sum(save(product(xr, yi)), save(product(xi, yr))))));
    }

    if (isFlonum(x))
        return newflonum(asFlonum(x) * asFlonum(y));

    if (isFlonum(y))
        return newflonum(asFlonum(x) * asFlonum(y));

    if (isRational(x) || isRational(y))
        return rationalResult(toRational(x) * toRational(y));

    return bignumResult(toBignum(x) * toBignum(y));
}

// divide
sexp divide(sexp x, sexp y)
{
    if (!x || !y)
        error("divide: operands");

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
        return lose(mark, make_rectangular(save(divide(save(sum(save(product(xr, yr)),
                                                                save(product(xi, yi)))), d)),
                                           save(divide(save(diff(save(product(xi, yr)),
                                                                 save(product(xr, yi)))), d))));
    }

    if (isFlonum(x))
        return newflonum(asFlonum(x) / asFlonum(y));

    if (isFlonum(y))
        return newflonum(asFlonum(x) / asFlonum(y));

    if (isRational(x) || isRational(y))
        return rationalResult(toRational(x) / toRational(y));

    Rat result(toBignum(x), toBignum(y));

    return rationalResult(result);
}

// quotient
sexp quotientf(sexp x, sexp y)
{
    if (x && y)
    {
        if (isFixnum(x)) {
            if (isFixnum(y))
                return newfixnum(asFixnum(x) / asFixnum(y));
            if (isBignum(y))
                return bignumResult(Num::div(toBignum(x), asBignum(y)));
        } else if (isBignum(x)) {
            if (isFixnum(y))
                return bignumResult(Num::div(asBignum(x), toBignum(y)));
            if (isBignum(y))
                return bignumResult(Num::div(asBignum(x), toBignum(y)));
        }
    }
    error("quotient: operands");
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
    if (x && y)
    {
        if (isFixnum(x)) {
            if (isFixnum(y))
                return newfixnum(mod(asFixnum(x), asFixnum(y)));
            if (isBignum(y))
                return bignumResult(Num::mod(toBignum(x), asBignum(y)));
        } else if (isBignum(x)) {
            if (isFixnum(y))
                return bignumResult(Num::mod(asBignum(x), toBignum(y)));
            if (isBignum(y))
                return bignumResult(Num::mod(asBignum(x), toBignum(y)));
        }
    }
    error("modulo: operands");
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

// fix remainder result
sexp remainderNum(const Num& xb, const Num& yb)
{
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

// x % y
sexp remainderff(sexp x, sexp y)
{
    if (x && y)
    {
        if (isFixnum(x)) {
            if (isFixnum(y))
                return newfixnum(rem(asFixnum(x), asFixnum(y)));
            if (isBignum(y))
                return remainderNum(toBignum(x), asBignum(y));
        } else if (isBignum(x)) {
            if (isFixnum(y))
                return remainderNum(asBignum(x), toBignum(y));
            if (isBignum(y))
                return remainderNum(asBignum(x), toBignum(y));
        }
    }
    error("remainder: operands");
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

    if (x)
    {
        if (isComplex(x))
            return lose(mark, make_rectangular(save(unineg(x->cdr->car)),
                                               save(unineg(x->cdr->cdr->car))));

        switch (shortType(x))
        {
        default:       break;
        case FIXNUM:   return newfixnum(- ((Fixnum*)x)->fixnum);
        case FLOAT:    return newflonum(- ((Float*)x)->flonum);
        case DOUBLE:   return newflonum(- ((Double*)x)->flonum);
        case BIGNUM:   return newbignum(- *((Bignum*)x)->nump);
        case RATIONAL: return newrational(- *((Rational*)x)->ratp);
        }
    }
    error("neg: operand");
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
        result = replace(divide(result, l->car));
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
    if (x)
    {
        if (isFixnum(x) && 0 <= asFixnum(x))
            return newfixnum(isqrt(asFixnum(x)));
        if (isBignum(x) && asBignum(x) >= 0)
            return newbignum(asBignum(x).sqrt());
    }
    error("isqrt: not a positive integer");
}

// sqrt
sexp sqrtff(sexp x)
{
    if (x)
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
        return lose(mark, make_rectangular(save(newflonum(re)), save(newflonum(im))));
    }

    error("sqrt: operand");
}

// pow
sexp powff(sexp x, sexp y)
{
    assertFlonum(x); assertFlonum(y);
    return newflonum(pow(asFlonum(x), asFlonum(y)));
}

// atan2
sexp atan2ff(sexp x, sexp y)
{
    assertFlonum(x); assertFlonum(y);
    return newflonum(atan2(asFlonum(x), asFlonum(y)));
}

// bignum?
sexp bignump(sexp x) { return boolwrap(x && isBignum(x)); }

// integer?
sexp integerp(sexp x)
{
    return boolwrap(x && (isFixnum(x) || isFlonum(x) && (int)asFlonum(x) == asFlonum(x)));
}

// real?
sexp realp(sexp x) { return boolwrap(x && isReal(x)); }

// inexact->exact
sexp inexact_exact(sexp x) { assertFlonum(x); return newfixnum((int)asFlonum(x)); }

// exact->inexact
sexp exact_inexact(sexp x)
{
    if (x && (isFixnum(x) || isRational(x) || isBignum(x)))
        return newflonum((double)asFlonum(x));
    error("exact->inexact: not exact");
}

// <<
sexp lsh(sexp x, sexp y)
{
    assertFixnum(y);
    if (x && (isFixnum(x) || isBignum(x)))
        return bignumResult(toBignum(x) << asFixnum(y));
    error("<< non integer arguments");
}

// >>
sexp rsh(sexp x, sexp y)
{
    assertFixnum(y);
    if (x)
    {
        if (isFixnum(x))
            return newfixnum(asFixnum(x) >> asFixnum(y));
        if (isBignum(x))
            return bignumResult(asBignum(x) >> asFixnum(y));
    }
    error(">> non integer arguments");
}

// not
sexp isnot(sexp x) { return boolwrap(f == x); }

// null?
sexp nullp(sexp x) { return boolwrap(0 == x); }

// list?
sexp listp(sexp x) { return boolwrap(x && isCons(x) && f != listp(x->cdr)); }

// atom?
sexp atomp(sexp x) { return boolwrap(x && !isCons(x)); }

// pair?
sexp pairp(sexp x) { return boolwrap(x && isCons(x)); }

// number?
sexp numberp(sexp x) { return boolwrap(x && isNumber(x)); }

// string?
sexp stringp(sexp x) { return boolwrap(x && isString(x)); }

// symbol?
sexp symbolp(sexp x) { return boolwrap(x && isAtom(x)); }

// symbol=?
sexp symbol_eqp(sexp x)
{
    if (!x)
        error("symbol=?: no arguments");
    sexp a = x->car;
    do {
        if (!isAtom(x->car))
            error("symbol=?: not a symbol");
        if (a != x->car)
            return f;
    } while (x = x->cdr);
    return t;
}

// boolean=?
sexp boolean_eqp(sexp x)
{
    if (!x)
        error("boolean=?: no arguments");
    sexp a = x->car;
    do {
        if (f != x->car && t != x->car)
            error("boolean=?: not a boolean");
        if (a != x->car)
            return f;
    } while (x = x->cdr);
    return t;
}

// procedure?
sexp procedurep(sexp p) { return boolwrap(p && (isFunct(p) || isClosure(p))); }

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
        ++sz;
    } while ((((unsigned char)ci) & 0xc0) == 0x80);
    ch -= offsetsFromUTF8[sz-1];
    --p;
    return ch;
}

// length of a String
int stringlen(String *s)
{
    int len = 0;
    char* p = s->text;
    while (*p && read_utf8(p))
        ++len;
    return len;
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
    string->tags[2] = DYNAMIC;
    return (sexp) string;
}

// a string with string constant text
sexp stastring(const char* s)
{
    String* string = (String*)newcell(STRING);
    string->text = (char*)s;
    string->tags[2] = STATIC;
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

// (number->string number [ radix ] )
sexp number_string(sexp args)
{
    int base = 10;
    if (args && args->car && isNumber(args->car))
    {
        sexp number = args->car;
        if ((args = args->cdr) && args->car && isFixnum(args->car))
            base = asFixnum(args->car);
        if (base != 8 && base != 16)
            base = 10;
        Context context(0, true, false, false, base);
        display(context, number, 0);
        return dynstring(strsave(context.s.str().c_str()));
    }
    error("number->string: arguments");
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
    return q-p-1;
}

int encodedLength(uint32_t ch)
{
    char b[5];
    return encodeUTF8(b, ch);
}

// make-string
sexp make_string(sexp args)
{
    if (!args || !args->car || !isFixnum(args->car))
        error("make-string: args expected");

    char cb[5];
    int l = asFixnum(args->car);
    uint32_t cx = args->cdr && args->cdr->car && isChar(args->cdr->car) ? ((Char*)(args->cdr->car))->ch : ' ';
    int cl = encodeUTF8(cb, cx);
    char* b = new char[(l*cl)+1];
    char* q = b;
    for (int i = 0; i < l; ++i)
    {
        strcpy(q, cb);
        q += cl;
    }
    *q++ = 0;
    return dynstring(b);
}

// string-copy
sexp string_copy(sexp args)
{
    if (!args || !args->car || !isString(args->car))
        error("string-copy: no string");

    sexp s = args->car;
    int i = 0;

    if ((args = args->cdr) && args->car && isFixnum(args->car))
        i = asFixnum(args->car);

    String* string = (String*)s;
    int len = stringlen(string);
    int j = len;

    if (args && (args = args->cdr) && args->car && isFixnum(args->car))
        j = asFixnum(args->car);

    if (i < 0 || j < i || j > len)
        error("string-copy: start negative or end before start");

    char* q;
    char* p = string->text;
    for (int k = 0; k < j; ++k)
    {
        if (i == k)
            q = p;
        read_utf8(p);
    }
    char* b = new char[p-q+1];
    memcpy(b, q, p-q);
    b[p-q] = 0;
    return dynstring(b);
}

// (string-copy! to at from [ start [ end ]])
sexp string_copy_(sexp args)
{
    if (!args || !args->car || !isString(args->car) ||
        !args->cdr || !isFixnum(args->cdr->car) ||
        !args->cdr->cdr || !isString(args->cdr->cdr->car))
        error("string-copy!: arguments");

    sexp to = args->car;
    int tolen = stringlen((String*)to);
    args = args->cdr;
    int at = asFixnum(args->car);
    args = args->cdr;
    sexp from = args->car;

    int start = 0;
    int len = stringlen(((String*)from));
    int end = len;
    if ((args = args->cdr) && args->car && isFixnum(args->car)) {
        start = asFixnum(args->car);
        if ((args = args->cdr) && args->car && isFixnum(args->car))
            end = asFixnum(args->car);
    }

    if (!(0 <= start && start <= end && end <= len))
        error("string-copy!: start negative or end before start");

    char* q = ((String*)from)->text;
    char* p = q;
    for (int k = 0; k < end; ++k)
    {
        if (start == k)
            q = p;
        read_utf8(p);
    }

    char* r = ((String*)to)->text;
    char* s = r;
    for (int k = 0; k < at+end-start; ++k)
    {
        if (at == k)
            r = s;
        read_utf8(s);
    }

    if ((p-q) != (s-r) || at+end-start > tolen)
        error("string-copy!: bad parameters or implementation incomplete");

    memmove(r, q, end-start);

    return newfixnum(at+end-start);
}

// write-string
sexp write_string(sexp args)
{
    if (!args || !args->car || !isString(args->car))
        error("write-string: no string");

    sexp s = args->car;
    sexp port = outport;
    if (args && (args = args->cdr) && isOutPort(args->car))
        port = args->car;
    else
        error("write-string: not an output port");

    int i = 0;

    if (args && (args = args->cdr) && args->car && isFixnum(args->car))
        i = asFixnum(args->car);

    String* string = (String*)s;
    int j = stringlen(string);

    if (args && (args = args->cdr) && args->car && isFixnum(args->car))
        j = asFixnum(args->car);

    if (i < 0 || j < i)
        error("write-string: start negative or end before start");

    char* q;
    char* p = string->text;
    for (int k = 0; k < j; ++k)
    {
        if (i == k)
            q = p;
        read_utf8(p);
    }
    char* b = (char*)alloca(p-q+1);
    memcpy(b, q, p-q);
    b[p-q] = 0;

    Context context(0, true, true, true, 10);
    ((OutPort*)port)->s->write(b, p-q);
    return voida;
}

// string->number
sexp string_number(sexp args)
{
    if (args && args->car && isString(args->car))
    {
        Num num(0);
        sexp string = args->car;
        args = args->cdr;
        int base = 10;
        if (args && args->car && isFixnum(args->car))
            base = asFixnum(args->car);
        if (base != 8 && base != 16)
            base = 10;
        char* p = ((String*)string)->text;
        if (*p)
        {
            int scale = 0;
            bool dotseen = false;
            uint32_t c = read_utf8(p);

            if ('+' == c)
                c = read_utf8(p);
            else if ('-' == c) {
                c = read_utf8(p);
                num.neg = true;
            }

            for (;;)
            {
                if (dotseen)
                    ++scale;
                else if ('.' == c && *p) {
                    dotseen = true;
                    c = read_utf8(p);
                }
                Num::word b = num.char_to_word(c);
                if (b >= base)
                    break;
                num.mul_word(base);
                num.add_word(b);
                if (*p)
                    c = read_utf8(p);
                else
                    break;
            }

            if (scale)
                return newflonum(num.to_double() * pow(10.0, -scale));
            else
                return bignumResult(num);
        }
        error("string->number: number syntax");
    }
    error("string->number: arguments");
}

// string-append
sexp string_append(sexp args)
{
    int length = 0;
    for (sexp p = args; p; p = p->cdr)
    {
        if (!p->car || !isString(p->car))
            error("string-append: not a string");
        String* string = (String*)p->car;
        length += strlen(string->text);
    }

    char* b = new char[length+1];
    char* q = b;
    for (sexp p = args; p; p = p->cdr)
    {
        String* string = (String*)p->car;
        for (char* r = string->text; *r; )
            *q++ = *r++;
    }
    *q++ = 0;
    return dynstring(b);
}

// (string-fill! string char begin end)
// but not all chars are the same length
sexp string_fill_(sexp args)
{
    if (args)
    {
        sexp string = args->car;
        if ((args = args->cdr) && args->car && isChar(args->car))
        {
            String* s = (String*)string;
            sexp fill = args->car;
            uint32_t fc = ((Char*)fill)->ch;
            int i = 0;
            int l = stringlen(s);
            int j = l;
            if (args && (args = args->cdr) && args->car && isFixnum(args->car))
            {
                i = asFixnum(args->car);
                if (args && (args = args->cdr) && args->car && isFixnum(args->car))
                    j = asFixnum(args->car);
            }

            if (!string || !isString(string) || !isMutable(s) ||
                !fill || !isChar(fill) || i < 0 || j < i || j > l)
                error("string-fill: arguments");

            int kl = encodedLength(fc);
            char* p = s->text;
            for (int ix = 0; ix < j; ++ix)
                if (i <= ix) {
                    char* q = p;
                    uint32_t cx = read_utf8(p);
                    if (encodedLength(cx) != kl)
                        error("string-fill!: encoded length differs");
                    char c = *p;
                    q += encodeUTF8(q, fc);
                    *p = c;
                } else
                    read_utf8(p);
            return string;
        }
        error("string-fill!: bad fill");
    }
    error("string-fill!: no arguments");
}

// close-input-port
sexp close_input_port(sexp p)
{
    assertInPort(p);
    if (inport == p) inport = 0;
    deleteinport(p);
    return voida;
}

// close-output-port
sexp close_output_port(sexp p)
{
    assertOutPort(p);
    if (outport == p) outport = 0;
    deleteoutport(p);
    return voida;
}

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

    String* string = (String*)s;
    int j = stringlen(string);
    if (args && (args = args->cdr))
    {
        assertFixnum(args->car);
        j = asFixnum(args->car);
    }

    if (i < 0 || j <= i)
        error("open-input-string: bad arguments");

    std::stringstream* ss = new std::stringstream();
    char* p = string->text;
    for (int k = 0; k < j; ++k)
    {
        char* q = p;
        read_utf8(p);
        if (i <= k)
            while (q < p)
                ss->put(*q++);
    }

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
    return dynstring(strsave(ss->str().c_str()));
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
    Context context(limit, true, false, true, 10);
    mapCycles(context, exp);
    display(context, exp, 0);
    if (0 == limit) limit = context.s.str().length();
    return dynstring(strsave(context.s.str().substr(0, limit).c_str()));
}

// vector?
sexp vectorp(sexp v) { return boolwrap(v && isVector(v)); }

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
sexp vector_list(sexp args)
{
    if (args)
    {
        sexp* mark = psp;
        save(args);
        sexp vector = args->car;
        assertVector(vector);
        Vector* v = (Vector*)vector;
        int begin = 0;
        int end = v->l;
        if ((args = args->cdr) && isFixnum(args->car))
        {
            begin = asFixnum(args->car);
            if (args && (args = args->cdr) && isFixnum(args->car))
                end = asFixnum(args->car);
        }
        if (0 <= begin && begin <= end && end <= v->l)
        {
            sexp list = save(0);
            for (int index = end; index > begin; )
                replace(list = cons(v->e[--index], list));
            return lose(mark, list);
        }
    }
    error("vector->list: arguments");
}

// (vector-copy! to at from [ start [ end ]])
sexp vector_copy_(sexp args)
{
    if (args)
    {
        if (args->car && isVector(args->car))
        {
            Vector* to = (Vector*)args->car;
            args = args->cdr;
            if (args && args->car && isFixnum(args->car))
            {
                int at = asFixnum(args->car);
                args = args->cdr;
                if (args && args->car && isVector(args->car))
                {
                    Vector* from = (Vector*)args->car;
                    args = args->cdr;
                    int start = 0;
                    int len = from->l;
                    int end = len;
                    if (args && args->car && isFixnum(args->car))
                    {
                        start = asFixnum(args->car);
                        args = args->cdr;
                        if (args && args->car && isFixnum(args->car))
                            end = asFixnum(args->car);
                    }

                    if (at+end-start <= to->l)
                    {
                        /*
                         * The rule for handling overlap is: Always start copying from the end
                         * of the source toward which the destination is offset.  If the offset is
                         * zero it doesn't matter.
                         */
                        if (at <= start)
                            for (int i = start; i < end; ++i)
                                to->e[at+i-start] = from->e[i];
                        else
                            for (int i = end; --i >= start; )
                                to->e[at+i-start] = from->e[i];

                        return newfixnum(at+end-start);
                    }
                }
            }
        }
    }
    error("vector_copy!: arguments");
}

// vector->string
sexp vector_string(sexp args)
{
    if (args)
    {
        sexp vector = args->car;
        assertVector(vector);
        Vector* v = (Vector*)vector;
        int begin = 0;
        int end = v->l;
        if ((args = args->cdr) && isFixnum(args->car))
        {
            begin = asFixnum(args->car);
            if (args && (args = args->cdr) && isFixnum(args->car))
                end = asFixnum(args->car);
        }
        if (0 <= begin && begin <= end && end <= v->l)
        {
            int len = 0;
            for (int index = begin; index < end; ++index)
            {
                sexp ch = v->e[index];
                assertChar(ch);
                len += encodedLength(((Char*)ch)->ch);
            }
            char* b = new char[len+1];
            char* p = b;
            *p = 0;
            for (int index = begin; index < end; ++index)
                p += encodeUTF8(p, ((Char*)(v->e[index]))->ch);
            return dynstring(b);
        }
    }
    error("vector->string: arguments");
}

// vector-append
sexp vector_append(sexp args)
{
    int j = 0;
    for (sexp p = args; p; p = p->cdr)
    {
        assertVector(p->car);
        j += ((Vector*)(p->car))->l;
    }
    sexp* mark = psp;
    sexp nv = save(newvector(j, 0));
    j = 0;
    for (sexp p = args; p; p = p->cdr)
    {
        Vector* v = (Vector*)p->car;
        for (int i = 0; i < v->l; ++i)
            ((Vector*)nv)->e[j++] = v->e[i];
    }
    return lose(nv);
}

// vector-copy
sexp vector_copy(sexp args)
{
    if (args)
    {
        sexp* mark = psp;
        save(args);
        sexp vector = args->car;
        assertVector(vector);
        Vector* v = (Vector*)vector;
        int begin = 0;
        int end = v->l;
        if ((args = args->cdr) && isFixnum(args->car))
        {
            begin = asFixnum(args->car);
            if (args && (args = args->cdr) && isFixnum(args->car))
                end = asFixnum(args->car);
        }
        if (0 <= begin && begin <= end && end <= v->l)
        {
            sexp nv = save(newvector(end-begin, 0));
            for (int index = begin; index < end; ++index)
                ((Vector*)nv)->e[index-begin] = v->e[index];
            return lose(mark, nv);
        }
    }
    error("vector-copy: arguments");
}

// (vector-fill! vector value begin end)
sexp vector_fill_(sexp args)
{
    if (args)
    {
        sexp* mark = psp;
        save(args);
        sexp vector = args->car;
        assertVector(vector);
        Vector* v = (Vector*)vector;
        if (args = args->cdr)
        {
            int begin = 0;
            int end = v->l;
            sexp fill = args->car;
            if (args && (args = args->cdr) && isFixnum(args->car))
            {
                begin = asFixnum(args->car);
                if (args && (args = args->cdr) && isFixnum(args->car))
                    end = asFixnum(args->car);
            }
            if (0 <= begin && begin <= end && end <= v->l)
            {
                for (int index = begin; index < end; ++index)
                    v->e[index] = fill;
                return lose(mark, vector);
            }
        }
    }
    error("vector-fill!: arguments");
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

// vector-set!
sexp vector_set_(sexp vector, sexp index, sexp value)
{
    assertFixnum(index);
    assertVector(vector);
    Vector* v = (Vector*)vector;
    v->e[asFixnum(index)] = value;
    return voida;
}

// these only work on ascii data

// char-alphabetic?
sexp char_alphabeticp(sexp c) { return boolwrap(c && isChar(c) && isalpha(((Char*)c)->ch)); }

// char->integer
sexp char_integer(sexp c) { assertChar(c); return newfixnum(((Char*)c)->ch); }

// char-ci=?
sexp char_cieqp(sexp args)
{
    if (!args)
        error("char-ci=?: no arguments");
    sexp x = args->car;
    assertChar(x);
    while (args = args->cdr)
    {
        assertChar(args->car);
        if (tolower(((Char*)x)->ch) != tolower(((Char*)(args->car))->ch))
            return f;
        x = args->car;
    }
    return t;
}

// char-ci>=?
sexp char_cigep(sexp args)
{
    if (!args)
        error("char-ci>=?: no arguments");
    sexp x = args->car;
    assertChar(x);
    while (args = args->cdr)
    {
        assertChar(args->car);
        if (tolower(((Char*)x)->ch) < tolower(((Char*)(args->car))->ch))
            return f;
        x = args->car;
    }
    return t;
}

// char-ci>?
sexp char_cigtp(sexp args)
{
    if (!args)
        error("char-ci>?: no arguments");
    sexp x = args->car;
    assertChar(x);
    while (args = args->cdr)
    {
        assertChar(args->car);
        if (tolower(((Char*)x)->ch) <= tolower(((Char*)(args->car))->ch))
            return f;
        x = args->car;
    }
    return t;
}

// char-ci<=?
sexp char_cilep(sexp args)
{
    if (!args)
        error("char-ci<=?: no arguments");
    sexp x = args->car;
    assertChar(x);
    while (args = args->cdr)
    {
        assertChar(args->car);
        if (tolower(((Char*)x)->ch) > tolower(((Char*)(args->car))->ch))
            return f;
        x = args->car;
    }
    return t;
}

// char-ci<?
sexp char_ciltp(sexp args)
{
    if (!args)
        error("char-ci<?: no arguments");
    sexp x = args->car;
    assertChar(x);
    while (args = args->cdr)
    {
        assertChar(args->car);
        if (tolower(((Char*)x)->ch) >= tolower(((Char*)(args->car))->ch))
            return f;
        x = args->car;
    }
    return t;
}

// char=?
sexp char_eqp(sexp args)
{
    if (!args)
        error("char=?: no arguments");
    sexp x = args->car;
    assertChar(x);
    while (args = args->cdr)
    {
        assertChar(args->car);
        if (((Char*)x)->ch != ((Char*)(args->car))->ch)
            return f;
        x = args->car;
    }
    return t;
}

// char>=?
sexp char_gep(sexp args)
{
    if (!args)
        error("char>=?: no arguments");
    sexp x = args->car;
    assertChar(x);
    while (args = args->cdr)
    {
        assertChar(args->car);
        if (((Char*)x)->ch < ((Char*)(args->car))->ch)
            return f;
        x = args->car;
    }
    return t;
}

// char>?
sexp char_gtp(sexp args)
{
    if (!args)
        error("char>?: no arguments");
    sexp x = args->car;
    assertChar(x);
    while (args = args->cdr)
    {
        assertChar(args->car);
        if (((Char*)x)->ch <= ((Char*)(args->car))->ch)
            return f;
        x = args->car;
    }
    return t;
}

// char<=?
sexp char_lep(sexp args)
{
    if (!args)
        error("char<=?: no arguments");
    sexp x = args->car;
    assertChar(x);
    while (args = args->cdr)
    {
        assertChar(args->car);
        if (((Char*)x)->ch > ((Char*)(args->car))->ch)
            return f;
        x = args->car;
    }
    return t;
}

// char<?
sexp char_ltp(sexp args)
{
    if (!args)
        error("char<?: no arguments");
    sexp x = args->car;
    assertChar(x);
    while (args = args->cdr)
    {
        assertChar(args->car);
        if (((Char*)x)->ch >= ((Char*)(args->car))->ch)
            return f;
        x = args->car;
    }
    return t;
}

// character?
sexp charp(sexp c) { return boolwrap(c && isChar(c)); }

// char-downcase
sexp char_downcase(sexp c) { assertChar(c); return newcharacter(tolower(((Char*)c)->ch)); }

// char-foldcase
sexp char_foldcase(sexp c) { assertChar(c); return newcharacter(tolower(((Char*)c)->ch)); }

// integer->char
sexp integer_char(sexp c) { assertFixnum(c); return newcharacter(asFixnum(c)); }

// char-lowercase?
sexp char_lower_casep(sexp c) { return boolwrap(c && isChar(c) && islower(((Char*)c)->ch)); }

// char-numeric?
sexp char_numericp(sexp c) { return boolwrap(c && isChar(c) && isdigit(((Char*)c)->ch)); }

// digit-value
sexp digit_value(sexp c)
{ 
    if (c && isChar(c))
    {
        int ch = ((Char*)c)->ch;
        if ('0' <= ch && ch <= '9')
            return newfixnum(ch-'0');
    }
    return f;
}

// char-upcase
sexp char_upcase(sexp c) { assertChar(c); return newcharacter(toupper(((Char*)c)->ch)); }

// char-uppercase?
sexp char_upper_casep(sexp c) { return boolwrap(c && isChar(c) && isupper(((Char*)c)->ch)); }

// char-whitespace?
sexp char_whitespacep(sexp c) { return boolwrap(c && isChar(c) && isspace(((Char*)c)->ch)); }

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

    char b[5];
    encodeUTF8(b, ((Char*)(args->car))->ch);
    ((OutPort*)port)->s->write(b, strlen(b));

    return voida;
}

// these only work on ascii data

// string<=?
sexp string_lep(sexp args)
{
    if (!args)
        error("string<=?: no arguments");
    sexp x = args->car;
    assertString(x);
    while (args = args->cdr)
    {
        assertString(args->car);
        if (strcmp(((String*)x)->text, ((String*)(args->car))->text) > 0)
            return f;
        x = args->car;
    }
    return t;
}

// string<?
sexp string_ltp(sexp args)
{
    if (!args)
        error("string<?: no arguments");
    sexp x = args->car;
    assertString(x);
    while (args = args->cdr)
    {
        assertString(args->car);
        if (strcmp(((String*)x)->text, ((String*)(args->car))->text) >= 0)
            return f;
        x = args->car;
    }
    return t;
}

// string=?
sexp string_eqp(sexp args)
{
    if (!args)
        error("string=?: no arguments");
    sexp x = args->car;
    assertString(x);
    while (args = args->cdr)
    {
        assertString(args->car);
        if (strcmp(((String*)x)->text, ((String*)(args->car))->text) != 0)
            return f;
        x = args->car;
    }
    return t;
}

// string>=?
sexp string_gep(sexp args)
{
    if (!args)
        error("string>=?: no arguments");
    sexp x = args->car;
    assertString(x);
    while (args = args->cdr)
    {
        assertString(args->car);
        if (strcmp(((String*)x)->text, ((String*)(args->car))->text) < 0)
            return f;
        x = args->car;
    }
    return t;
}

// string>?
sexp string_gtp(sexp args)
{
    if (!args)
        error("string>?: no arguments");
    sexp x = args->car;
    assertString(x);
    while (args = args->cdr)
    {
        assertString(args->car);
        if (strcmp(((String*)x)->text, ((String*)(args->car))->text) <= 0)
            return f;
        x = args->car;
    }
    return t;
}

// string-ci-<=?
sexp string_cilep(sexp args)
{
    if (!args)
        error("string-ci<=?: no arguments");
    sexp x = args->car;
    assertString(x);
    while (args = args->cdr)
    {
        assertString(args->car);
        if (strcasecmp(((String*)x)->text, ((String*)(args->car))->text) > 0)
            return f;
        x = args->car;
    }
    return t;
}

// string-ci<?
sexp string_ciltp(sexp args)
{
    if (!args)
        error("string-ci<?: no arguments");
    sexp x = args->car;
    assertString(x);
    while (args = args->cdr)
    {
        assertString(args->car);
        if (strcasecmp(((String*)x)->text, ((String*)(args->car))->text) >= 0)
            return f;
        x = args->car;
    }
    return t;
}

// string-ci=?
sexp string_cieqp(sexp args)
{
    if (!args)
        error("string-ci=?: no arguments");
    sexp x = args->car;
    assertString(x);
    while (args = args->cdr)
    {
        assertString(args->car);
        if (strcasecmp(((String*)x)->text, ((String*)(args->car))->text) != 0)
            return f;
        x = args->car;
    }
    return t;
}

// string-ci>=?
sexp string_cigep(sexp args)
{
    if (!args)
        error("string-ci>=?: no arguments");
    sexp x = args->car;
    assertString(x);
    while (args = args->cdr)
    {
        assertString(args->car);
        if (strcasecmp(((String*)x)->text, ((String*)(args->car))->text) < 0)
            return f;
        x = args->car;
    }
    return t;
}

// string-ci>?
sexp string_cigtp(sexp args)
{
    if (!args)
        error("string-ci>?: no arguments");
    sexp x = args->car;
    assertString(x);
    while (args = args->cdr)
    {
        assertString(args->car);
        if (strcasecmp(((String*)x)->text, ((String*)(args->car))->text) <= 0)
            return f;
        x = args->car;
    }
    return t;
}

// string-ref
sexp string_ref(sexp s, sexp i)
{
    assertString(s);
    assertFixnum(i);

    String* string = (String*)s;
    int len = stringlen(string);
    int ind = asFixnum(i);
    char* p = string->text;
    for (int k = 0; k < ind; ++k)
        read_utf8(p);
    if (*p)
        return newcharacter(read_utf8(p));
    error("string-ref: out of bounds");
}

// string-set!
sexp string_set_(sexp s, sexp k, sexp c)
{
    assertString(s);
    assertFixnum(k);
    assertChar(c);

    String* string = (String*)s;

    if (!isMutable(string))
        error("string-set!: immutable string");

    uint32_t cx = ((Char*)c)->ch;
    int len = stringlen(string);
    int ind = asFixnum(k);
    char* p = string->text;
    for (int i = 0; i < ind; ++i)
        read_utf8(p);

    if (0 == *p)
        error("string-set!: out of bounds");

    char* q = p;
    read_utf8(p);
    if (q + encodedLength(cx) != p)
        error("string-set!: implementation incomplete");

    char cy = *p;
    encodeUTF8(q, cx);
    *p = cy;

    return s;
}

// substring
sexp substringf(sexp args)
{
    if (!args || !args->car || !isString(args->car))
        error("substring: no string");

    sexp s = args->car;

    if (!(args = args->cdr) || !args->car || !isFixnum(args->car))
        error("substring: bad start index");

    int i = asFixnum(args->car);
    String* string = (String*)s;
    int j = stringlen(string);

    if ((args = args->cdr) && args->car && isFixnum(args->car))
        j = asFixnum(args->car);

    if (i < 0 || j < i)
        error("substring: start negative or end before start");

    char* q;
    char* p = string->text;
    for (int k = 0; k < j; ++k)
    {
        if (i == k)
            q = p;
        read_utf8(p);
    }
    char* b = new char[p-q+1];
    memcpy(b, q, p-q);
    b[p-q] = 0;
    return dynstring(b);
}

// append
sexp append(sexp p, sexp q)
{
    sexp* mark = psp;
    save(p, q);
    return lose(mark, p ? cons(p->car, save(append(p->cdr, q))) : q);
}

// reverse!
sexp reverse_(sexp x)
{
    sexp t = 0;
    while (x)
        if (x && isCons(x))
        {
            t = cons(car(x), t);
            x = x->cdr;
        } else
            error("reverse!: not a proper list");
    return t;
}

bool eqnb(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) == asFixnum(y);

    if (isRational(x) || isRational(y))
    {
        Rat xr = toRational(x); xr.reduce();
        Rat yr = toRational(y); yr.reduce();
        return xr == yr;
    }
    
    if (isBignum(x) || isBignum(y))
    {
        Num xb = toBignum(x);
        Num yb = toBignum(y);
        return xb == yb;
    }

    if (isComplex(x)) {
        if (isComplex(y))
            return eqnb(real_part(x), real_part(y)) && eqnb(imag_part(x), imag_part(y));
        else
            return eqnb(real_part(x), y) && f != zerop(imag_part(x));
    } else if (isComplex(y))
        return eqnb(x, real_part(y)) && f != zerop(imag_part(y));

    return asFlonum(x) == asFlonum(y);
}

bool eqa(sexp x, sexp y)
{
    if (x == y)
        return true;

    if (!x || !y || isAtom(x) || isAtom(y))
        return false;

    if (isComplex(x) && isComplex(y))
        return eqa(real_part(x), real_part(y)) && eqa(imag_part(x), imag_part(y));

    if (isCons(x) || isCons(y))
        return false;

    if (shortType(x) != shortType(y))
        return false;

    switch (shortType(x)) 
    {
    default:       return false;
    case FLOAT :   return ((Float*)x)->flonum  == ((Float*)y)->flonum;
    case DOUBLE:   return ((Double*)x)->flonum == ((Double*)y)->flonum;
    case STRING:   return 0 == strcmp(stringText(x), stringText(y));
    case FIXNUM:   return ((Fixnum*)x)->fixnum  == ((Fixnum*)y)->fixnum;
    case CHAR:     return ((Char*)x)->ch        == ((Char*)y)->ch;
    case BIGNUM:   return *((Bignum*)x)->nump   == *((Bignum*)y)->nump;
    case RATIONAL: { Rat xr = asRational(x); xr.reduce();
                     Rat yr = asRational(y); yr.reduce();
                     return xr == yr; }
    }
}

// = numeric equality
sexp eqnp(sexp args)
{
    if (!args)
        error("=: no arguments");

    sexp x = args->car;

    while (args = args->cdr)
    {
        sexp y = args->car;
        if (!eqnb(x, y))
            return f;
    }
    return t;
}

// odd?
sexp oddp(sexp x)
{
    if (x)
    {
        if (isFixnum(x))
            return boolwrap(asFixnum(x) & 1);
        if (isBignum(x))
            return boolwrap(asBignum(x).get_bit(0));
    }
    error("odd?: not an integer");
}

// ~ x
sexp complement(sexp x) { return x && isFixnum(x) ? newfixnum(~asFixnum(x)) : f; }

// all arguments must be fixnums for these logical operations
void assertAllFixnums(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
        if (!p->car || !isFixnum(p->car))
            error("bitwise ops require fixnum arguments");
}

// x0 & x1 & x2 ...
sexp bit_and(sexp args)
{
    assertAllFixnums(args);
    int result = ~0;
    for (sexp p = args; p; p = p->cdr)
        result = result & asFixnum(p->car);
    return lose(newfixnum(result));
}

// x0 | x1 | x2 ...
sexp bit_or(sexp args)
{
    assertAllFixnums(args);
    int result = 0;
    for (sexp p = args; p; p = p->cdr)
        result = result | asFixnum(p->car);
    return lose(newfixnum(result));
}

// x0 ^ x1 ^ x2 ...
sexp bit_xor(sexp args)
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
    if (r && p && isFixnum(r) && isFixnum(p))
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
    if (!p || !isPromise(p))
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
    if (!p || !isPromise(p))
        error("promise-forced?: not a promise");
    return p->cdr->car;
}

// promise-value
sexp promise_value(sexp p)
{
    if (!p || !isPromise(p))
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
sexp display_shared(sexp args)
{
    Context context(0, false, true, true, 10);
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    mapCycles(context, args->car);
    display(context, args->car, 0);
    ((OutPort*)port)->s->write(context.s.str().c_str(), context.s.str().length());
    return voida;
}

sexp display_simple(sexp args)
{
    Context context(0, false, true, false, 10);
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    mapCycles(context, args->car);
    display(context, args->car, 0);
    ((OutPort*)port)->s->write(context.s.str().c_str(), context.s.str().length());
    return voida;
}

// write
sexp write_shared(sexp args)
{
    Context context(0, true, true, true, 10);
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    mapCycles(context, args->car);
    display(context, args->car, 0);
    ((OutPort*)port)->s->write(context.s.str().c_str(), context.s.str().length());
    return voida;
}

sexp write_simple(sexp args)
{
    Context context(0, true, true, false, 10);
    sexp port = args->cdr ? args->cdr->car : outport;
    assertOutPort(port);
    mapCycles(context, args->car);
    display(context, args->car, 0);
    ((OutPort*)port)->s->write(context.s.str().c_str(), context.s.str().length());
    return voida;
}

bool cyclic(std::set<sexp>& seenSet, sexp exp)
{
    if (!exp || isPromise(exp))
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
    Context context(0, true, false, true, 10);
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
    int dl = displayLength(p->car) + 2;
    if (dl > 9) dl = 1;
    level += dl;
    while (p)
    {
        if (first && context.labelCycles(p, true))
            break;
        display(context, p->car, level);
        if ((p = p->cdr)) {
            if (isCons(p) && !isPromise(p) && replenv != p && global != p) {
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
    context.s << "#(";
    Vector *vv = (Vector*)v;
    if (vv->l)
        level += 2;
    for (int i = 0; i < vv->l; ++i)
    {
        if (!context.labelCycles(vv->e[i], false))
            display(context, vv->e[i], level);
        if (i < vv->l-1)
            context.wrap(level, displayLength(vv->e[i+1]));
    }
    context.s << ')';
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
    char buf[5];
    int c = ((Char*)exp)->ch;
    if (context.write)
    {
        for (int i = 0; character_table[i]; ++i)
            if (c == *character_table[i]) {
                context.s << "#\\" << 1+character_table[i];
                return;
            }
        encodeUTF8(buf, ((Char*)exp)->ch);
        context.s << "#\\" << buf;
    } else {
        encodeUTF8(buf, ((Char*)exp)->ch);
        context.s << buf;
    }
}

void displayString(Context& context, sexp exp)
{
    if (context.write)
        context.s << '"';
    String* string = (String*)exp;
    for (char* p = string->text; *p; )
    {
        uint32_t cx = read_utf8(p);
        if (context.write && cx <= 0x7f && strchr("\007\b\t\n\r\"\\", cx)) {
            context.s << '\\' << encodeEscape(cx);
        } else {
            char buf[5];
            encodeUTF8(buf, cx);
            context.s << buf;
        }
    }
    if (context.write)
        context.s << '"';
}

void displayAtom(Context& context, sexp exp)
{
    if (context.write && voida == exp) {
        context.s << "#void";
    } else {
        for (char* p = atomText(exp); *p; )
        {
            uint32_t cx = read_utf8(p);
            if (context.write && cx <= 0x7f && strchr("\007\b\t\n\r\"\\", cx)) {
                context.s << '\\' << encodeEscape(cx);
            } else {
                char buf[5];
                encodeUTF8(buf, cx);
                context.s << buf;
            }
        }
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
    ((Bignum*)exp)->nump->print(cs, context.radix);
    for (char c : cs)
        if (c)
            context.s.put(c);
}

void displayRational(Context& context, sexp exp)
{
    Rat* ratp = ((Rational*)exp)->ratp;
    std::vector<char> cs;
    ratp->num.print(cs, context.radix);
    for (char c : cs)
        if (c)
            context.s.put(c);
    context.s.put('/');
    std::vector<char> ds;
    ratp->den.print(ds, context.radix);
    for (char c : ds)
        if (c)
            context.s.put(c);
}

void mapCycles(Context& context, sexp p)
{
    if (p && isCons(p)) {
        if (0 == context.seenMap[p]) {
            context.seenMap[p] = f;
            mapCycles(context, p->car);
            mapCycles(context, p->cdr);
        } else
            context.seenMap[p] = t;
    } else if (p && isVector(p)) {
        if (0 == context.seenMap[p]) {
            context.seenMap[p] = f;
            Vector* v = (Vector*)p;
            for (int i = 0; i < v->l; ++i)
                mapCycles(context, v->e[i]);
        } else
            context.seenMap[p] = t;
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
        if (exp->cdr && isCons(exp->cdr))
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
        else if (isPromise(exp))
            displayNamed(context, "promise", exp);
        else if (isComplex(exp)) {
            display(context, exp->cdr->car, level);
            double im = asFlonum(exp->cdr->cdr->car);
            if (im > 0.0)
                context.s << '+';
            if (im)
            {
                if (im == -1)
                    context.s << '-';
                else if (im != 1)
                    display(context, exp->cdr->cdr->car, level);
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
    case VECTOR:   displayVector(context, exp, level);      break;
    case CLOSURE:  displayNamed(context, "closure", exp);   break;
    }
}

void debug(const char *what, sexp exp)
{
    Context context(0, true, true, true, 10);
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

// string->list
sexp string_list(sexp args)
{
    if (args)
    {
        sexp* mark = psp;
        save(args);
        sexp string = args->car;
        assertString(string);
        String* s = (String*)string;
        int begin = 0;
        int len = stringlen(s);
        int end = len;
        if ((args = args->cdr) && isFixnum(args->car))
        {
            begin = asFixnum(args->car);
            if (args && (args = args->cdr) && isFixnum(args->car))
                end = asFixnum(args->car);
        }

        if (0 <= begin && begin <= end && end <= len)
        {
            sexp list = save(0);
            char* q = s->text;
            for (int i = 0; i < end; ++i)
            {
                uint32_t ch = read_utf8(q);
                if (begin <= i && i < end)
                    replace(list = cons(newcharacter(ch), list));
            }
            return lose(mark, reverse_(list));
        }
    }
    error("string->list: arguments");
}

// string->vector
sexp string_vector(sexp args)
{
    if (args)
    {
        sexp* mark = psp;
        save(args);
        sexp string = args->car;
        assertString(string);
        String* s = (String*)string;
        int begin = 0;
        int len = stringlen(s);
        int end = len;
        if ((args = args->cdr) && isFixnum(args->car))
        {
            begin = asFixnum(args->car);
            if (args && (args = args->cdr) && isFixnum(args->car))
                end = asFixnum(args->car);
        }

        if (0 <= begin && begin <= end && end <= len)
        {
            sexp nv = save(newvector(end-begin, 0));
            char* q = s->text;
            for (int i = 0; i < end; ++i)
            {
                uint32_t ch = read_utf8(q);
                if (begin <= i && i < end)
                    ((Vector*)nv)->e[i-begin] = newcharacter(ch);
            }
            return lose(mark, nv);
        }
    }
    error("string->vector: arguments");
}

// list->string
sexp list_string(sexp s)
{
    if (!s)
        return newcell(STRING, 0);

    int size = 1;
    for (sexp p = s; p; p = p->cdr)
    {
        assertChar(p->car);
        size += encodedLength(((Char*)(p->car))->ch);
    }

    char* b = new char[size];
    char* q = b;
    for (sexp p = s; p; p = p->cdr)
        q += encodeUTF8(q, ((Char*)(p->car))->ch);
    *q++ = 0;

    return dynstring(b);
}

// string
sexp string(sexp args) { return list_string(args); }

// eqv?
sexp eqvp(sexp args)
{
    if (!args)
        error("eqv?: no arguments");
    sexp x = args->car;
    while (args = args->cdr)
        if (!eqa(x, args->car))
            return f;
    return t;
}

// eq?
sexp eqp(sexp args)
{
    if (!args)
        error("eq?: no arguments");
    sexp x = args->car;
    while (args = args->cdr)
        if (x != args->car)
            return f;
    return t;
}

bool equalb(std::set<sexp>& seen, sexp x, sexp y)
{
    if (x == y)
        return true;

    if (!x || !y || isAtom(x) || isAtom(y))
        return false;

    if (isCons(x) && isCons(y))
    {
        if (seen.find(x) != seen.end() &&
            seen.find(y) != seen.end())
            return true;

        seen.insert(x);
        seen.insert(y);

        return equalb(seen, x->car, y->car) && equalb(seen, x->cdr, y->cdr);
    }

    if (shortType(x) != shortType(y))
        return false;

    if (isVector(x))
    {
        Vector* xv = (Vector*)x;
        Vector* yv = (Vector*)y;

        if (xv->l != yv->l)
            return false;

        for (int i = xv->l; --i >= 0; )
            if (!equalb(seen, xv->e[i], yv->e[i]))
                return false;

        return true;
    }

    return eqa(x, y);
}

bool equalb(std::set<sexp>& seen, sexp args)
{
    if (!args)
        error("equal?: no arguments");

    sexp x = args->car;

    while (args = args->cdr)
        if (!equalb(seen, x, args->car))
            return false;

    return true;
}

// equal?
sexp equalp(sexp args)
{
    std::set<sexp> seen;
    return boolwrap(equalb(seen, args));
}

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
            ((Closure*)(e->car->cdr))->expenv->cdr = env;
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

// defined?
sexp definedp(sexp p, sexp env)
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
sexp set_(sexp p, sexp r, sexp env)
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
    if (!p)
        return p;
    return lose(mark, cons(save(eval(p->car, env)), save(evlis(p->cdr, env))));
}

// associate names with values in an environment
sexp assoc(sexp names, sexp values, sexp env)
{
    if (!names)
        return env;
    sexp* mark = psp;
    save(values, names, env);
    if (!isCons(names))
        if (values)
            return lose(mark, cons(save(cons(names, values)), env));
        else
            return lose(mark, cons(save(cons(names, voida)), env));
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

sexp unbox(sexp s)
{
    return ((Closure*)s)->expenv;
}

// lambda creates a closure
sexp lambdaform(sexp exp, sexp env)
{
    return lose(newcell(CLOSURE, save(cons(exp, env))));
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
        // v is a closure
        for (sexp q = env; q; q = q->cdr)
            if (k == q->car->car)
            {
                q->car->cdr = v;
                return lose(mark, env);
            }
        // update the closure definition to include the one we just made
        return lose(mark, ((Closure*)v)->expenv->cdr = cons(save(cons(p->car->car, save(v))), env));
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
sexp readf(sexp args)
{
    sexp port = inport;
    if (args) assertInPort(port = args->car);
    return ((InPort*)port)->s->read();
}

// scan
sexp scanff(sexp args)
{
    sexp port = inport;
    if (args) assertInPort(port = args->car);
    return ((InPort*)port)->s->scan();
}

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
            if (eqa(key, p->car))
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
    if (!exp || !isAtom(exp->car))
        error("set!: variable must be a symbol");
    if (!exp->cdr)
        error("set!: missing operands");
    return lose(set_(exp->car, save(eval(exp->cdr->car, env)), env));
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
    if (exp->car && isAtom(exp->car))
    {
        // (let name ((var val) (var val) ..) body )
        sexp l = replace(cons(lambda, replace(cons(save(names(exp->cdr->car)), exp->cdr->cdr))));
        sexp c = replace(newcell(CLOSURE, save(cons(l, env))));
        ((Closure*)c)->expenv->cdr = e = replace(cons(save(cons(exp->car, c)), e));
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
            set_(v->car->car, save(eval(v->car->cdr->car, e)), e);
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
            e = save(cons(replace(cons(v->car->car, save(eval(v->car->cdr->car, env)))), e));

    for (;;)
    {
        sexp u = exp->cdr->car;
        if (f != eval(u->car, e))
            if (u->cdr)
                return lose(mark, tailforms(u->cdr, e));
            else
                return voida;

        // evaluate each body expression
        tailforms(exp->cdr->cdr, e);

        // step each variable
        for (sexp v = exp->car; v; v = v->cdr)
            if (v->car->cdr->cdr)
                set_(v->car->car, eval(v->car->cdr->cdr->car, e), e);
    }
}

// command-line
sexp command_line(sexp x)
{
    sexp* mark = psp;
    sexp args = save(0);
    for (int i = argc; i > 0; )
        args = replace(cons(save(stastring(argv[--i])), args));
    return lose(mark, args);
}

// exit
sexp exitf(sexp args)
{
    exit(args ? 1 : 0);
}

// get-environment-variable
sexp get_environment_variable(sexp name)
{
    return stastring(getenv(((String*)name)->text));
}

// get-environment-variables
sexp get_environment_variables(sexp name)
{
    sexp* mark = psp;
    sexp env = save(0);
    for (char** e = envp; *e; ++e)
    {
        const char* v = *e;
        const char* s = strchr(v, '=');
        char* name = strncpy(new char[s-v+1], v, s-v);
        name[s-v] = '\0';
        char* value = strcpy(new char[strlen(s+1)+1], s+1);
        env = replace(cons(replace(cons(save(dynstring(name)), save(dynstring(value)))), env));
    }
    return lose(mark, env);
}

// apply
sexp apply(sexp fun, sexp args)
{
    if (fun)
    {
        sexp* mark = psp;
        save(fun, args);

        if (false && f != tracing)
            debug("apply", cons(fun, args));

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
            Closure* clo = (Closure*)fun;
            sexp env     = clo->expenv->cdr;
            sexp fcc     = clo->expenv->car->cdr;

            if (!fcc->car) {
                // (lambda () foo)
            } else if (isAtom(fcc->car)) {
                // (lambda s foo)
                env = replace(cons(save(cons(fcc->car, args)), env));
            } else {
                // (lambda (n) (car x))
                env = save(assoc(fcc->car, args, env));
            }

            return lose(mark, tailforms(fcc->cdr, env));
        }
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
        Context context(0, true, false, false, 10);
        context.s << "eval:";
        for (int i = indent; --i >= 0; context.s << ' ') {}
        display(context, p, 0);
        context.s << " ==> ";
        if (!p || f == p || t == p || (OTHER & shortType(p)) && shortType(p) > ATOM)
            {}
        else if (isAtom(p))
            p = get(p, env);
        else {
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

        if (fun)
        {
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
    error("eval: null function");
}

// like eval, with error checking
sexp xeval(sexp p, sexp env)
{
    if (env && isCons(env) && env->car && isCons(env->car))
        return eval(p, env);
    error("eval: bad environment");
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
    if ('-' == c || '+' == c)
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
        if ('-' == c || '+' == c)
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

sexp readTail(std::istream& fin, int level);

sexp scans(std::istream& fin)
{
    sexp* mark = psp;

    std::stringstream s;

    if (scanahead)
    {
        sexp sv = scanahead;
        scanahead = 0;
        return sv;
    }

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
    case '#':  return hash;
    case '\\': return backslash;
    case '!':  return bang;
    case ',':  c = fin.get();
               if ('@' != c) {
                    fin.unget();
                    return comma;
               } else
                   return commaat;
    case '+':   c = fin.get();
                // sloppy parsing +inf.0 +nan.0
                if ('.' == c || 'i' == c || 'n' == c || isdigit(c))
                    s.put('+');
                else
                    { fin.unget(); return plus; }
                break;

    case '-':   c = fin.get();
                // sloppy parsing -inf.0 -nan.0
                if ('.' == c || 'i' == c || 'n' == c || isdigit(c))
                    s.put('-');
                else
                    { fin.unget(); return minus; } 
                break;
    }

    fin.unget();

    NumStatus status, rstatus, istatus;

    c = scanNumber(s, fin, rstatus);

    size_t split = s.tellp();

    if ('+' == c || '-' == c) {
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

        if (NON_NUMERIC == rstatus) {
            real = zero;
        } else if (RATIO == rstatus) {
            std::string realdata = cdata.substr(0, split);
            int realdiv = realdata.find_first_of('/');
            real = save(rationalResult(Rat(Num(realdata.substr(0,realdiv).c_str()),
                                           Num(realdata.substr(realdiv+1).c_str()))));
        } else if (FIXED == rstatus) {
            std::string n = cdata.substr(0, split);
            Num num(n.c_str()); real = save(bignumResult(num));
        } else
            { double re; s >> re; real = save(newflonum(re)); }

        c = cdata.at(split);

        if (NON_NUMERIC == istatus) {
            imag = one;
        } else if (RATIO == istatus) {
            std::string imagdata = cdata.substr(split+1);
            imagdata = imagdata.substr(0, imagdata.length()-1);
            int imagdiv = imagdata.find_first_of('/');
            imag = save(rationalResult(Rat(Num(imagdata.substr(0,imagdiv).c_str()),
                                           Num(imagdata.substr(imagdiv+1).c_str()))));
        } else if (FIXED == istatus) {
            std::string n = cdata.substr(split+1);
            n = n.substr(0, n.length()-1);
            Num num(n.c_str()); imag = save(bignumResult(num));
        } else
            { double im; s >> im; imag = save(newflonum(im)); }

        switch (c)
        {
        case '+':
            return lose(mark, make_rectangular(real, imag));
        case '-':
            return lose(mark, make_rectangular(real, save(unineg(imag))));
        case '@':
            double r = isRational(real) ? asRational(real).to_double() : asFlonum(real);
            double theta = isRational(imag) ? asRational(imag).to_double() : asFlonum(imag);
            return lose(mark, make_rectangular(save(newflonum(r * cos(theta))),
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
          return rationalResult(Rat(Num(ratio.substr(0,pos).c_str()),
                                    Num(ratio.substr(pos+1).c_str()))); }
    default:
        break;
    }

    (void)fin.get();
    if ('|' == c) {
        c = fin.get();
        // read an atom
        while (0 <= c && '|' != c)
        {
            if ('\\' == c)
                c = fin.get();
            c = accept(s, fin, c);
        }
        return dynintern(strsave(s.str().c_str()));
    } else if ('"' != c) {
        // read an atom
        while (0 <= c && !strchr("( )[,]\t\r\n", c))
            c = accept(s, fin, c);
        fin.unget();
        return dynintern(strsave(s.str().c_str()));
    } else {
        char bx[5];
        // read a string
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
                    if (';' == c)
                        c = read_utf8(fin);
                    encodeUTF8(bx, x);
                    s << bx;
                    if (0 < c && '"' != c)
                    {
                        encodeUTF8(bx, c);
                        c = read_utf8(fin);
                    }
                } else if (0 <= c && !strchr("( )[,]\t\r\n", c)) {
                    uint32_t x = decodeEscape(c);
                    encodeUTF8(bx, x);
                    s << bx;
                    c = read_utf8(fin);
                } else
                    while (0 <= c && strchr("( )[,]\t\r\n", c))
                        c = read_utf8(fin);
            } else {
                encodeUTF8(bx, c);
                s << bx;
                c = read_utf8(fin);
            }
        }
        return dynstring(strsave(s.str().c_str()));
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

const int NUMBER_EXACT   = -1;
const int NUMBER_INEXACT = -2;

sexp readNumber(std::istream& fin, int radix)
{
    int c = fin.get();
    Num::word base = radix;
    if (NUMBER_EXACT == radix || NUMBER_INEXACT == radix)
    {
        base = 10;
        if ('#' == c)
            switch (c = fin.get())
            {
            default:  fin.unget();              break;
            case 'b': base =  2; c = fin.get(); break;
            case 'o': base =  8; c = fin.get(); break;
            case 'd': base = 10; c = fin.get(); break;
            case 'x': base = 16; c = fin.get(); break;
        }
    } else if ('#' == c)
        switch (c = fin.get())
        {
        default:  fin.unget();                           break;
        case 'e': radix = NUMBER_EXACT;   c = fin.get(); break;
        case 'i': radix = NUMBER_INEXACT; c = fin.get(); break;
        }

    Num num(0);
    if ('+' == c)
        {}
    else if ('-' == c)
        num.neg = true;
    else
        fin.unget();

    int scale = 0;
    bool dotseen = false;
    while (c = fin.get())
    {
        if (c < 0)
            return eof;
        if (dotseen)
            ++scale;
        else if ('.' == c) {
            dotseen = true;
            c = fin.get();
        }
        Num::word b = num.char_to_word(c);
        if (b >= base)
            break;
        num.mul_word(base);
        num.add_word(b);
    }
    fin.unget();

    if (NUMBER_INEXACT == radix || dotseen && NUMBER_EXACT != radix) {
        if (scale)
            return newflonum(num.to_double() * pow(10.0, -scale));
        else
            return newflonum(num.to_double());
    } else {
        if (scale)
            return rationalResult(Rat(num, Num(10).pow(scale)));
        else
            return bignumResult(num);
    }
}

// finish reading a # token
// #b #o #d #x #e #i prefixes
sexp readHash(std::istream& fin, int level)
{
    std::stringstream s;
    sexp* mark = psp;
    int c = fin.get();
    switch (c)
    {
    default:    break;
    case '(':   return lose(mark, list_vector(save(readTail(fin, level+1))));
    case 'b':   return readNumber(fin, 2);
    case 'o':   return readNumber(fin, 8);
    case 'd':   return readNumber(fin, 10);
    case 'x':   return readNumber(fin, 16);
    case 'e':   return readNumber(fin, NUMBER_EXACT);
    case 'i':   return readNumber(fin, NUMBER_INEXACT);
    case '!':   do
                    c = fin.get();
                while ('\r' != c && '\n' != c);
                return lose(mark, read(fin, level));
    case '\\':  {
                    c = fin.get();
                    do
                        c = accept(s, fin, c);
                    while (0 <= c && !isspace(c) && '(' != c && ')' != c);
                    fin.unget();
                    const char* buf = s.str().c_str();
                    for (int i = 0; character_table[i]; ++i)
                        if (!strcmp(buf, 1+character_table[i]))
                            return lose(mark, newcharacter(*character_table[i]));
                    return lose(mark, newcharacter(*buf));
                }
    }
    fin.unget();
    sexp p = save(scan(fin));
    if (fa == p || falsea == p)
        return lose(mark, f);
    if (ta == p || truea == p)
        return lose(mark, t);
    if (voidaa == p)
        return lose(mark, voida);
    scanahead = p;
    return hash;
}

/*
 * read an s-expression
 */
sexp read(std::istream& fin, int level)
{
    sexp* mark = psp;
    sexp p = save(scan(fin));
    if (lparen == p)
        return lose(mark, readTail(fin, level+1));
    if (hash == p)
        return lose(mark, readHash(fin, level+1));
    if (qchar == p)
        return lose(mark, cons(quote, save(cons(save(read(fin, level)), 0))));
    if (tick == p)
        return lose(mark, cons(quasiquote, save(cons(save(read(fin, level)), 0))));
    if (comma == p)
        return lose(mark, cons(unquote, save(cons(save(read(fin, level)), 0))));
    if (commaat == p)
        return lose(mark, cons(unquotesplicing, save(cons(save(read(fin, level)), 0))));
    if (level == 0 && rparen == p)
        error("error: an s-expression cannot begin with ')'");
    return lose(mark, p);
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

const struct FuncTable {
    const char* name;
    short       arity;
    void*       funcp;
} funcTable[] = {
    { "bit-and",                           0, (void*)bit_and },
    { "bit-or",                            0, (void*)bit_or },
    { "+",                                 0, (void*)uniadd },
    { "/",                                 0, (void*)unidiv },
    { "%",                                 0, (void*)unimod },
    { "*",                                 0, (void*)unimul },
    { "-",                                 0, (void*)unisub },
    { "bit-xor",                           0, (void*)bit_xor },
    { "~",                                 1, (void*)complement },
    { "=",                                 0, (void*)eqnp },
    { ">=",                                0, (void*)gep },
    { ">",                                 0, (void*)gtp },
    { "<=",                                0, (void*)lep },
    { "lsh",                               2, (void*)lsh },
    { "<",                                 0, (void*)ltp },
    { "rsh",                               2, (void*)rsh },
    { "acos",                              1, (void*)acosff },
    { "angle",                             1, (void*)angle },
    { "append",                            2, (void*)append },
    { "apply",                             2, (void*)apply },
    { "asin",                              1, (void*)asinff },
    { "assoc",                             3, (void*)assoc },
    { "atan",                              1, (void*)atanff },
    { "atan2",                             2, (void*)atan2ff },
    { "atom?",                             1, (void*)atomp },
    { "atoms",                             0, (void*)atomsf },
    { "bignum?",                           1, (void*)bignump },
    { "boolean?",                          1, (void*)booleanp },
    { "boolean=?",                         0, (void*)boolean_eqp },
    { "call-with-input-file",              2, (void*)call_with_input_file },
    { "call-with-output-file",             2, (void*)call_with_output_file },
    { "call-with-output-string",           1, (void*)call_with_output_string },
    { "call-with-truncated-output-string", 2, (void*)call_with_truncated_output_string },
    { "car",                               1, (void*)car },
    { "cdr",                               1, (void*)cdr },
    { "ceiling",                           1, (void*)ceilingff },
    { "char?",                             1, (void*)charp },
    { "char=?",                            0, (void*)char_eqp },
    { "char>=?",                           0, (void*)char_gep },
    { "char>?",                            0, (void*)char_gtp },
    { "char<=?",                           0, (void*)char_lep },
    { "char<?",                            0, (void*)char_ltp },
    { "char-alphabetic?",                  1, (void*)char_alphabeticp },
    { "char-ci=?",                         0, (void*)char_cieqp },
    { "char-ci>=?",                        0, (void*)char_cigep },
    { "char-ci>?",                         0, (void*)char_cigtp },
    { "char-ci<=?",                        0, (void*)char_cilep },
    { "char-ci<?",                         0, (void*)char_ciltp },
    { "char-downcase",                     1, (void*)char_downcase },
    { "char-foldcase",                     1, (void*)char_foldcase },
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
    { "command-line",                      0, (void*)command_line },
    { "complex?",                          1, (void*)complexp },
    { "cons",                              2, (void*)cons },
    { "cos",                               1, (void*)cosff },
    { "cosh",                              1, (void*)coshff },
    { "cputime",                           0, (void*)cputime },
    { "current-input-port",                0, (void*)current_input_port },
    { "current-output-port",               0, (void*)current_output_port },
    { "current-second",                    0, (void*)current_second },
    { "cyclic?",                           1, (void*)cyclicp },
    { "denominator",                       1, (void*)denominator },
    { "diff",                              2, (void*)diff },
    { "digit-value",                       1, (void*)digit_value },
    { "display",                           0, (void*)display_shared },
    { "display-shared",                    0, (void*)display_shared },
    { "display-simple",                    0, (void*)display_simple },
    { "divide",                            2, (void*)divide },
    { "emergency-exit",                    0, (void*)exitf },
    { "eof-object?",                       1, (void*)eof_objectp },
    { "eq?",                               0, (void*)eqp },
    { "equal?",                            0, (void*)equalp },
    { "eqv?",                              0, (void*)eqvp },
    { "eval",                              2, (void*)xeval },
    { "evlis",                             2, (void*)evlis },
    { "exact?",                            1, (void*)exactp },
    { "exact-integer?",                    1, (void*)exact_integerp },
    { "exact->inexact",                    1, (void*)exact_inexact },
    { "exp",                               1, (void*)expff },
    { "exit",                              0, (void*)exitf },
    { "floor",                             1, (void*)floorff },
    { "force",                             1, (void*)force },
    { "form?",                             1, (void*)formp },
    { "function?",                         1, (void*)functionp },
    { "gc",                                0, (void*)gc },
    { "gcd",                               2, (void*)gcd },
    { "get-environment-variable",          1, (void*)get_environment_variable },
    { "get-environment-variables",         0, (void*)get_environment_variables },
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
    { "make-rectangular",                  2, (void*)make_rectangular },
    { "make-string",                       0, (void*)make_string },
    { "make-vector",                       0, (void*)make_vector },
    { "modulo",                            2, (void*)moduloff },
    { "neg",                               1, (void*)unineg },
    { "negative?",                         1, (void*)negativep },
    { "newline",                           0, (void*)newline },
    { "not",                               1, (void*)isnot },
    { "null?",                             1, (void*)nullp },
    { "number?",                           1, (void*)numberp },
    { "number->string",                    0, (void*)number_string },
    { "numerator",                         1, (void*)numerator },
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
    { "reverse!",                          1, (void*)reverse_ },
    { "round",                             1, (void*)roundff },
    { "scan",                              0, (void*)scanff },
    { "set-car!",                          2, (void*)set_car_ },
    { "set-cdr!",                          2, (void*)set_cdr_ },
    { "sin",                               1, (void*)sinff },
    { "sinh",                              1, (void*)sinhff },
    { "space",                             0, (void*)space },
    { "sqrt",                              1, (void*)sqrtff },
    { "string",                            0, (void*)string },
    { "string?",                           1, (void*)stringp },
    { "string=?",                          0, (void*)string_eqp },
    { "string>=?",                         0, (void*)string_gep },
    { "string>?",                          0, (void*)string_gtp },
    { "string<=?",                         0, (void*)string_lep },
    { "string<?",                          0, (void*)string_ltp },
    { "string-append",                     0, (void*)string_append },
    { "string-ci=?",                       0, (void*)string_cieqp },
    { "string-ci>=?",                      0, (void*)string_cigep },
    { "string-ci>?",                       0, (void*)string_cigtp },
    { "string-ci<=?",                      0, (void*)string_cilep },
    { "string-ci<?",                       0, (void*)string_ciltp },
    { "string-copy",                       0, (void*)string_copy },
    { "string-copy!",                      0, (void*)string_copy_ },
    { "string-fill!",                      0, (void*)string_fill_ },
    { "string-length",                     1, (void*)string_length },
    { "string->list",                      0, (void*)string_list },
    { "string->number",                    0, (void*)string_number },
    { "string-ref",                        2, (void*)string_ref },
    { "string-set!",                       3, (void*)string_set_ },
    { "string->symbol",                    1, (void*)string_symbol },
    { "string->vector",                    0, (void*)string_vector },
    { "substring",                         0, (void*)substringf },
    { "sum",                               2, (void*)sum },
    { "symbol?",                           1, (void*)symbolp },
    { "symbol=?",                          0, (void*)symbol_eqp },
    { "symbol->string",                    1, (void*)symbol_string },
    { "tan",                               1, (void*)tanff },
    { "tanh",                              1, (void*)tanhff },
    { "trace",                             1, (void*)trace },
    { "truncate",                          1, (void*)truncateff },
    { "unbox",                             1, (void*)unbox },
    { "undefine",                          1, (void*)undefine },
    { "vector",                            0, (void*)vector },
    { "vector?",                           1, (void*)vectorp },
    { "vector-append",                     0, (void*)vector_append },
    { "vector-copy",                       0, (void*)vector_copy },
    { "vector-copy!",                      0, (void*)vector_copy_ },
    { "vector-fill!",                      0, (void*)vector_fill_ },
    { "vector-length",                     1, (void*)vector_length },
    { "vector->list",                      0, (void*)vector_list },
    { "vector->string",                    0, (void*)vector_string },
    { "vector-ref",                        2, (void*)vector_ref },
    { "vector-set!",                       3, (void*)vector_set_ },
    { "with-input-from-file",              2, (void*)with_input_from_file },
    { "with-output-to-file",               2, (void*)with_output_to_file },
    { "write",                             0, (void*)write_shared },
    { "write-shared",                      0, (void*)write_shared },
    { "write-simple",                      0, (void*)write_simple },
    { "write-char",                        0, (void*)write_char },
    { "write-string",                      0, (void*)write_string },
    { "write-to-string",                   0, (void*)write_to_string },
    { "zero?",                             1, (void*)zerop },
    { 0,                                   0, 0 }
};

const struct FormTable {
    const char* name;
    Formp       formp;
} formTable[] = {
    { "and",         andform },
    { "begin",       begin },
    { "defined?",    definedp },
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
    ::argc = argc;
    ::argv = argv;
    ::envp = envp;

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
    bang            = staintern("!");
    commaat         = staintern(",@");
    comma           = staintern(",");
    complex         = staintern("complex");
    definea         = staintern("define");
    dot             = staintern(".");
    elsea           = staintern("else");
    eof             = staintern("#eof");
    f               = staintern("#f");
    fa              = staintern("f");
    falsea          = staintern("false");
    hash            = staintern("#");
    lambda          = staintern("lambda");
    lbracket        = staintern("[");
    lparen          = staintern("(");
    minus           = staintern("-");
    plus            = staintern("+");
    promise         = staintern("promise");
    qchar           = staintern("'");
    quasiquote      = staintern("quasiquote");
    quote           = staintern("quote");
    rbracket        = staintern("]");
    rparen          = staintern(")");
    t               = staintern("#t");
    ta              = staintern("t");
    truea           = staintern("true");
    tick            = staintern("`");
    unquote         = staintern("unquote");
    unquotesplicing = staintern("unquote-splicing");
    voida           = staintern("");
    voidaa          = staintern("void");

    // streams
    define_staintern_sexpr("cerr",     errport);
    define_staintern_sexpr("cin",      inport);
    define_staintern_sexpr("cout",     outport);

    // metasyntax
    define_staintern_sexpr("bang",     bang);
    define_staintern_sexpr("comma",    comma);
    define_staintern_sexpr("commaat",  commaat);
    define_staintern_sexpr("dot",      dot);
    define_staintern_sexpr("hash",     hash);
    define_staintern_sexpr("lbracket", lbracket);
    define_staintern_sexpr("lparen",   lparen);
    define_staintern_sexpr("qchar",    qchar);
    define_staintern_sexpr("rbracket", rbracket);
    define_staintern_sexpr("rparen",   rparen);
    define_staintern_sexpr("tick",     tick);
    define_staintern_sexpr("void",     voida);

    define_staintern_sexpr("+inf.0",   newflonum(INFINITY));
    define_staintern_sexpr("-inf.0",   newflonum(-INFINITY));
    define_staintern_sexpr("+nan.0",   newflonum(NAN));
    define_staintern_sexpr("-nan.0",   newflonum(-NAN));

    for (const FuncTable* p = funcTable; p->name; ++p)
    {
        sexp* mark = psp;
        Funct* f = (Funct*)save(newcell(FUNCT));
        f->tags[2] = p->arity; f->funcp = p->funcp;
        define_staintern_sexpr(p->name, (sexp)f);
        psp = mark;
    }

    for (const FormTable* p = formTable; p->name; ++p)
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
            Context context(0, false, true, true, 10);
            mapCycles(context, valu);
            display(context, valu, 0);
            std::cout.write(context.s.str().c_str(), context.s.str().length());
            if (voida != valu)
                std::cout << std::endl;
        }
    }
    return 0;
}

