/*
 * this aspires to be a scheme interpreter
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

int killed = 1;

#ifdef BROKEN
#define error(s) do { std::cout << s << std::endl; assert(false); } while(0)
#else
#define error(s) do { psp = protect; longjmp(the_jmpbuf, (long)s); } while(0)
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
enum Tag0
{
    CONS   = 0,
    OTHER  = 1,
    MARK   = 2
};

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

sexp closure, comma, commaat, complex, dot, elsea, eof, f, lambda, lbracket, lparen;
sexp minus, nil, one, promise, qchar, quasiquote, quote, rational, rbracket, rparen;
sexp t, tick, unquote, unquotesplicing, voida, zero;

sexp define(sexp p, sexp r);
sexp eval(sexp p, sexp env);
sexp apply(sexp fun, sexp args);
sexp read(std::istream& fin, int level);
sexp scan(std::istream& fin);
void debug(const char* label, sexp exp);

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
    virtual void put(int ch) { ((std::stringstream*)streamPointer)->put(ch); }
    virtual void write(const char *s, int len);
    virtual sexp read(void) { return ::read(*(std::stringstream*)streamPointer, 0); }
    virtual sexp scan(void) { return ::scan(*(std::stringstream*)streamPointer); }
    virtual bool good(void) { return ((std::stringstream*)streamPointer)->good(); }
    virtual ~StrPortStream() { delete (std::stringstream*) streamPointer; }
};

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
struct Atom    { char tags[sizeof(sexp)]; sexp                      chunks; };
struct String  { char tags[sizeof(sexp)]; sexp                      chunks; };
struct Fixnum  { char tags[sizeof(sexp)]; long                      fixnum; };
struct Float   { char tags[sizeof(Cons)-sizeof(float)];  float      flonum; };
struct Double  { char tags[sizeof(Cons)-sizeof(double)]; double     flonum; };
struct Funct   { char tags[sizeof(sexp)]; void*                      funcp; };
struct Form    { char tags[sizeof(sexp)]; Formp                      formp; };
struct Char    { char tags[sizeof(sexp)-sizeof(char)];   char           ch; };
struct InPort  { char tags[sizeof(sexp)-2]; char avail,peek; PortStream* s; };
struct OutPort { char tags[sizeof(sexp)]; PortStream*                    s; };
struct Vector  { char tags[sizeof(sexp)-sizeof(short)]; short l; sexp*   e; };

// supports uglyprinting
class ugly
{
    static const int tabs = 2;
    static const int eol = 60;

    std::ostream& s;
    std::streampos pos;
public:
    ugly(std::ostream& s) : s(s) { pos = s.tellp(); }
    void wrap(int level, int length) { if (s.tellp() - pos + length > eol) newline(level); else space(); }
    void newline(int level) { s << '\n'; pos = s.tellp(); for (int i = level; --i >= 0; s << ' ') {} }
    void space() { s << ' '; }
};

std::ostream& display(std::ostream& s, sexp p, std::set<sexp>& seenSet, ugly& ugly, int level, bool write);

static inline int  shortType(const sexp p) { return                   ((Stags*)p)->stags; }
static inline int  arity(const sexp p)     { return                 ((Funct*)p)->tags[2]; }
static inline bool isMarked(const sexp p)  { return       (MARK  &  ((Tags*)p)->tags[0]); }
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

bool isFlonum(const sexp p)  { return isFloat(p) || isDouble(p) || isRational(p); }

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

int  total = 0;         	// total allocation across gc's
int  marked = 0;        	// how many cells were marked during gc
int  allocated = 0;     	// how many cells have been allocated
int  collected = 0;     	// how many gc's
bool collecting = false;	// collecting garbage now
sexp cell = 0;         	    // all the storage starts here
sexp atoms = 0;         	// all atoms are linked in a list
sexp global = 0;        	// this is the global symbol table (a list)
sexp inport = 0;        	// the current input port
sexp outport = 0;       	// the current output port
sexp tracing = 0;       	// trace everything
sexp errport = 0;       	// the stderr port
sexp freelist = 0;      	// available cells are linked in a list
sexp *psp = 0;          	// protection stack pointer
sexp *psend = 0;            // protection stack end
sexp *protect = 0;      	// protection stack

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

static inline void markCell(sexp p)   { ((Tags*)p)->tags[0] |=  MARK; ++marked; }
static inline void unmarkCell(sexp p) { ((Tags*)p)->tags[0] &= ~MARK; --marked; }

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

    if (isCons(p))
    {
        std::set<sexp> seenSet;
        markCons(p, seenSet);
        return;
    }

    switch (((Stags*)p)->stags)
    {
    case ATOM:
    case STRING:
        mark(((Atom*)p)->chunks);
        break;
    case VECTOR:
        Vector* v = (Vector*)p;
        for (int i = v->l; --i >= 0; mark(v->e[i])) {}
    }

    markCell(p);
}

void deleteinport(sexp v)
{
    PortStream* f = ((InPort*)v)->s;
    ((InPort*)v)->s = 0;
    if (f != &cinStream)
        delete f;
}

void deleteoutport(sexp v)
{
    PortStream* f = ((OutPort*)v)->s;
    ((OutPort*)v)->s = 0;
    if (f != &coutStream && f != &cerrStream)
        delete f;
}

void deletevector(sexp v) { delete ((Vector*)v)->e; }

/*
 * mark all reachable objects
 *
 * sweep all storage, putting unmarked objects on the freelist
 */
sexp gc(sexp args)
{
    collecting = true;
    bool verbose = isCons(args) && args->car;
    int werefree = CELLS-allocated;
    int wereprot = psp-protect;

    marked = 0;
    mark(atoms);
    mark(global);
    mark(inport);
    mark(errport);
    mark(outport);
    mark(zero);
    mark(one);
    for (sexp *p = protect; p < psp; ++p)
        mark(*p);

    freelist = 0;
    int reclaimed = 0;
    int weremark = marked;

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
            ++reclaimed;
        } else 
            unmarkCell(p);
    }

    if (verbose)
        std::cout << "gc: allocated: " << allocated << " protected: "    << wereprot  << " marked: "       << weremark
                  << " reclaimed: "    << reclaimed << " collections: "  << collected << " allocation: "   << total << std::endl;

    allocated -= reclaimed-werefree;
    total += allocated;
    ++collected;
    if (!freelist)
        error("error: storage exhausted");
    collecting = false;
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

void assertFlonum(sexp s) { if (!isFlonum(s) && !isFixnum(s) && !isRational(s)) error("not a real number"); }

/*
 * allocate a cell from the freelist
 */
sexp newcell(void)
{
    if (allocated >= CELLS)
        gc(0);

    ++allocated;
    Cons* p = freelist;
    freelist = freelist->cdr;
    p->cdr = 0; // this is important!
    return p;
}

sexp newcell(short stags, sexp car)
{
    Stags* t = (Stags*)newcell();
    t->stags = stags;
    t->car = car;
    return (sexp)t;
}

sexp newfixnum(long number)
{
    Fixnum* p = (Fixnum*)newcell();
    ((Stags*)p)->stags = FIXNUM;
    p->fixnum = number;
    return (sexp)p;
}

sexp newcharacter(char c)
{
    Char* p = (Char*)newcell();
    ((Stags*)p)->stags = CHAR;
    p->ch = c;
    return (sexp)p;
}

sexp newinport(char* name)
{
    InPort* p = (InPort*)newcell();
    ((Stags*)p)->stags = INPORT;
    p->avail = 0;
    p->peek = 0;
    p->s = new IfsPortStream(name, std::ifstream::ios_base::in);
    return (sexp)p;
}

sexp newoutport(char* name)
{
    OutPort* p = (OutPort*)newcell();
    ((Stags*)p)->stags = OUTPORT;
    p->s = new OfsPortStream(name, std::ofstream::ios_base::out);
    return (sexp)p;
}

sexp newflonum(double number)
{
    if (sizeof(double) > sizeof(void*)) {
        Float* p = (Float*)newcell();
        ((Stags*)p)->stags = FLOAT;
        p->flonum = number;
        return (sexp)p;
    } else {
        Double* p = (Double*)newcell();
        ((Stags*)p)->stags = DOUBLE;
        p->flonum = number;
        return (sexp)p;
    }
}

sexp define_form(sexp name, Formp f)
{
    assert(name);
    Form* p = (Form*)save(newcell());
    ((Stags*)p)->stags = FORM;
    p->formp = f;
    define(name, (sexp)p);
    return lose(name);
}

sexp define_funct(sexp name, int arity, void* f)
{
    assert(name);
    Funct* p = (Funct*)save(newcell());
    ((Stags*)p)->stags = FUNCT;
    p->tags[2] = arity;
    p->funcp = f;
    define(name, (sexp)p);
    return lose(name);
}

// cons
sexp cons(sexp car, sexp cdr)
{
    sexp* mark = psp;
    save(car, cdr);
    if (allocated >= CELLS)
        gc(0);
    ++allocated;
    sexp p = freelist;
    freelist = freelist->cdr;
    p->car = car;
    p->cdr = cdr;
    return lose(mark, p);
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
    sexp q = t;
    while ((p = p->cdr) && (q = eval(p->car, env))) {}
    return q;
}

// or
sexp orform(sexp p, sexp env)
{
    sexp q = 0;
    while ((p = p->cdr) && 0 == (q = eval(p->car, env))) {}
    return q;
}

// trace
sexp trace(sexp arg) { sexp r = tracing; tracing = arg ? t : 0; return r; }

long asFixnum(sexp p) { if (isFixnum(p)) return ((Fixnum*)p)->fixnum; error("asFixnum: not a fixnum"); }

double rat2real(sexp x) { return (double)asFixnum(x->cdr->car) / (double)asFixnum(x->cdr->cdr->car); }

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
        if (asFixnum(x->cdr->car) < 0)
            return asFixnum(x->cdr->cdr->car) < 0 ? 0 : t;
        else
            return asFixnum(x->cdr->cdr->car) < 0 ? t : 0;

    return asFlonum(x) < 0 ? t : 0;
}

// positive?
sexp positivep(sexp x)
{
    if (isRational(x))
        if (asFixnum(x->cdr->car) < 0)
            return asFixnum(x->cdr->cdr->car) < 0 ? t : 0;
        else
            return asFixnum(x->cdr->cdr->car) < 0 ? 0 : t;

    return asFlonum(x) > 0 ? t : 0;
}

// boolean?
sexp booleanp(sexp x) { return t == x || 0 == x ? t : 0; }

// <
sexp ltp(sexp x, sexp y) { return asFlonum(x) < asFlonum(y) ? t : 0; }

// <=
sexp lep(sexp x, sexp y) { return asFlonum(x) <= asFlonum(y) ? t : 0; }

// >=
sexp gep(sexp x, sexp y) { return asFlonum(x) >= asFlonum(y) ? t : 0; }

// >
sexp gtp(sexp x, sexp y) { return asFlonum(x) > asFlonum(y) ? t : 0; }

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
sexp exactp(sexp x) { return (isFixnum(x) || isRational(x)) ? t : 0; }

// inexact?
sexp inexactp(sexp x) { return isFlonum(x) ? t : 0; }

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
        sexp real = save(rational_div(save(rational_add(save(rational_mul(x, u)), save(rational_mul(y, v)))), d));
        sexp imag = save(rational_div(save(rational_sub(save(rational_mul(y, u)), save(rational_mul(x, v)))), d));
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

// x0 + x1 + x2 ...
sexp uniadd(sexp l)
{
    sexp* mark = psp;
    sexp sum = zero;
    save(l, sum);
    while (l)
    {
        sexp x = l->car;
        if (isComplex(sum)) {
            if (isComplex(x))
                sum = replace(complex_add(sum, x));
            else if (isRational(x) || isFixnum(x) || isFlonum(x))
                sum = replace(lose(complex_add(sum, save(make_complex(x, zero)))));
            else
                error("not a number");
        } else if (isRational(sum)) {
            if (isComplex(x))
                sum = replace(lose(complex_add(x, save(make_complex(sum, zero)))));
            else if (isRational(x) || isFixnum(x))
                sum = replace(rational_add(sum, x));
            else if (isFlonum(x))
                sum = replace(newflonum(rat2real(sum) + asFlonum(x)));
            else
                error("not a number");
        } else if (isFixnum(sum)) {
            if (isComplex(x))
                sum = replace(lose(complex_add(x, save(make_complex(sum, zero)))));
            else if (isRational(x))
                sum = replace(lose(rational_add(save(make_rational(sum, one)), x)));
            else if (isFixnum(x))
                sum = replace(newfixnum(asFixnum(sum) + asFixnum(x)));
            else if (isFlonum(x))
                sum = replace(newflonum((double)asFixnum(sum) + asFlonum(x)));
            else
                error("not a number");
        } else if (isFlonum(sum)) {
            if (isComplex(x))
                sum = replace(lose(complex_add(save(make_complex(sum, zero)), x)));
            else if (isRational(x))
                sum = replace(newflonum(asFlonum(sum) + rat2real(x)));
            else if (isFixnum(x))
                sum = replace(newflonum(asFlonum(sum) + (double)asFixnum(x)));
            else if (isFlonum(x))
                sum = replace(newflonum(asFlonum(sum) + asFlonum(x)));
            else
                error("not a number");
        } else
            error("not a number");
        l = l->cdr;
    }
    return lose(mark, sum);
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
    default:     error("neg: not a number");
    case FIXNUM: return newfixnum(-((Fixnum*)x)->fixnum);
    case FLOAT:  return newflonum(-((Float*)x)->flonum);
    case DOUBLE: return newflonum(-((Double*)x)->flonum);
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
    return lose(uniadd(replace(cons(l->car, replace(cons(replace(unineg(save(uniadd(l->cdr)))), 0))))));
}

// x0 * x1 * x2 ...
sexp unimul(sexp l)
{
    sexp* mark = psp;
    sexp product = one;
    save(l, product);
    while (l)
    {
        sexp x = l->car;
        if (isComplex(product)) {
            if (isComplex(x))
                product = replace(complex_mul(product, x));
            else if (isRational(x) || isFixnum(x) || isFlonum(x))
                product = replace(lose(complex_mul(product, save(make_complex(x, zero)))));
            else
                error("not a number");
        } else if (isRational(product)) {
            if (isComplex(x))
                product = replace(lose(complex_mul(x, save(make_complex(product, zero)))));
            else if (isRational(x) || isFixnum(x))
                product = replace(rational_mul(product, x));
            else if (isFlonum(x))
                product = replace(newflonum(rat2real(product) * asFlonum(x)));
            else
                error("not a number");
        } else if (isFixnum(product)) {
            if (isComplex(x))
                product = replace(lose(complex_mul(x, save(make_complex(product, zero)))));
            else if (isRational(x))
                product = replace(lose(rational_mul(save(make_rational(product, one)), x)));
            else if (isFixnum(x))
                product = replace(newfixnum(asFixnum(product) * asFixnum(x)));
            else if (isFlonum(x))
                product = replace(newflonum((double)asFixnum(product) * asFlonum(x)));
            else
                error("not a number");
        } else if (isFlonum(product)) {
            if (isComplex(x))
                product = replace(lose(complex_mul(save(make_complex(product, zero)), x)));
            else if (isRational(x))
                product = replace(newflonum(asFlonum(product) * rat2real(x)));
            else if (isFixnum(x))
                product = replace(newflonum(asFlonum(product) * (double)asFixnum(x)));
            else if (isFlonum(x))
                product = replace(newflonum(asFlonum(product) * asFlonum(x)));
            else
                error("not a number");
        } else
            error("not a number");
        l = l->cdr;
    }
    return lose(mark, product);
}

// x0 / x1 / x2 ...
sexp unidiv(sexp l)
{
    sexp* mark = psp;

    sexp product;
    if (l && l->cdr)
    {
        product = l->car;
        l = l->cdr;
    } else
        product = one;

    save(l, product);
    while (l)
    {
        sexp x = l->car;
        if (isComplex(product)) {
            if (isComplex(x))
                product = replace(complex_div(product, x));
            else if (isRational(x) || isFixnum(x) || isFlonum(x))
                product = replace(lose(complex_div(product, save(make_complex(x, zero)))));
            else
                error("not a number");
        } else if (isRational(product)) {
            if (isComplex(x))
                product = replace(lose(complex_div(x, save(make_complex(product, zero)))));
            else if (isRational(x) || isFixnum(x))
                product = replace(rational_div(product, x));
            else if (isFlonum(x))
                product = replace(newflonum(rat2real(product) / asFlonum(x)));
            else
                error("not a number");
        } else if (isFixnum(product)) {
            if (isComplex(x))
                product = replace(lose(complex_div(x, save(make_complex(product, zero)))));
            else if (isFixnum(x) || isRational(x))
                product = replace(lose(rational_div(save(make_rational(product, one)), x)));
            else if (isFlonum(x))
                product = replace(newflonum((double)asFixnum(product) / asFlonum(x)));
            else
                error("not a number");
        } else if (isFlonum(product)) {
            if (isComplex(x))
                product = replace(lose(complex_div(save(make_complex(product, zero)), x)));
            else if (isRational(x))
                product = replace(newflonum(asFlonum(product) / rat2real(x)));
            else if (isFixnum(x))
                product = replace(newflonum(asFlonum(product) / (double)asFixnum(x)));
            else if (isFlonum(x))
                product = replace(newflonum(asFlonum(product) / asFlonum(x)));
            else
                error("not a number");
        } else
            error("not a number");
        l = l->cdr;
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

sexp complex_mod(sexp x, sexp y) { error("complex_mod: not implemented"); }

// x0 % x1 % x2 ...
sexp unimod(sexp l)
{
    sexp* mark = psp;
    sexp product = l->car;
    save(l, product);
    while (l = l->cdr) {
        sexp x = l->car;
        if (isComplex(product)) {
            if (isComplex(x))
                product = replace(complex_mod(product, x));
            else if (isRational(x) || isFixnum(x) || isFlonum(x))
                product = replace(lose(complex_mod(product, save(make_complex(x, zero)))));
            else
                error("not a number");
        } else if (isRational(product)) {
            if (isComplex(x))
                product = replace(lose(complex_mod(x, save(make_complex(product, zero)))));
            else if (isRational(x) || isFixnum(x))
                product = replace(rational_mod(product, x));
            else if (isFlonum(x))
                product = replace(newflonum(fmod(rat2real(product), asFlonum(x))));
            else
                error("not a number");
        } else if (isFixnum(product)) {
            if (isComplex(x))
                product = replace(lose(complex_mod(x, save(make_complex(product, zero)))));
            else if (isRational(x))
                product = replace(lose(rational_mod(save(make_rational(product, one)), x)));
            else if (isFixnum(x))
                product = replace(newfixnum(asFixnum(product) % asFixnum(x)));
            else if (isFlonum(x))
                product = replace(newflonum(fmod((double)asFixnum(product), asFlonum(x))));
            else
                error("not a number");
        } else if (isFlonum(product)) {
            if (isComplex(x))
                product = replace(lose(complex_mod(save(make_complex(product, zero)), x)));
            else if (isRational(x))
                product = replace(newflonum(fmod(asFlonum(product), rat2real(x))));
            else if (isFixnum(x))
                product = replace(newflonum(fmod(asFlonum(product), (double)asFixnum(x))));
            else if (isFlonum(x))
                product = replace(newflonum(fmod(asFlonum(product), asFlonum(x))));
            else
                error("not a number");
        } else
            error("not a number");
    }
    return lose(mark, product);
}

// functions on real numbers
sexp acosff(sexp x)    { assertFlonum(x); return newflonum(acos(asFlonum(x)));  } // acos
sexp asinff(sexp x)    { assertFlonum(x); return newflonum(asin(asFlonum(x)));  } // asin
sexp atanff(sexp x)    { assertFlonum(x); return newflonum(atan(asFlonum(x)));  } // atan
sexp ceilingff(sexp x) { assertFlonum(x); return newflonum(ceil(asFlonum(x)));  } // ceiling
sexp cosff(sexp x)     { assertFlonum(x); return newflonum(cos(asFlonum(x)));   } // cos
sexp coshff(sexp x)    { assertFlonum(x); return newflonum(cosh(asFlonum(x)));  } // cosh
sexp expff(sexp x)     { assertFlonum(x); return newflonum(exp(asFlonum(x)));   } // exp
sexp floorff(sexp x)   { assertFlonum(x); return newflonum(floor(asFlonum(x))); } // floor
sexp logff(sexp x)     { assertFlonum(x); return newflonum(log(asFlonum(x)));   } // log
sexp roundff(sexp x)   { assertFlonum(x); return newflonum(round(asFlonum(x))); } // round
sexp sinff(sexp x)     { assertFlonum(x); return newflonum(sin(asFlonum(x)));   } // sin
sexp sinhff(sexp x)    { assertFlonum(x); return newflonum(sinh(asFlonum(x)));  } // sinh
sexp tanff(sexp x)     { assertFlonum(x); return newflonum(tan(asFlonum(x)));   } // tan
sexp tanhff(sexp x)    { assertFlonum(x); return newflonum(tanh(asFlonum(x)));  } // tanh

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
    if (isComplex(x))
    {
        re = asFlonum(x->cdr->car);
        im = asFlonum(x->cdr->cdr->car);
    } else if (isFlonum(x)) {
        re = asFlonum(x);
    } else if (isFixnum(x))
        re = (double)asFixnum(x);

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

// truncate
sexp truncateff(sexp x) { assertFlonum(x); return newflonum(asFlonum(x) < 0 ? ceil(asFlonum(x)) : floor(asFlonum(x))); }

// integer?
sexp integerp(sexp x) { return isFixnum(x) ? t : isFlonum(x) && (long)asFlonum(x) == asFlonum(x) ? t : 0; }

// real?
sexp realp(sexp x) { return (isFixnum(x) || isFlonum(x)) ? t : 0; }

// inexact->exact
sexp inexact_exact(sexp x) { assertFlonum(x); return newfixnum((long)asFlonum(x)); }

// exact->inexact
sexp exact_inexact(sexp x) { assertFlonum(x); return newflonum((double)asFlonum(x)); }

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
sexp string_length(sexp s) { assertString(s); return newfixnum(slen(s)); }

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
    ((Stags*)r)->stags = CHUNK;
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
            return lose(p);
        }

        r->text[i++] = c;

        if (i == sizeof(r->text))
        {
            i = 0;
            q = q->cdr = newcell();
            r = (Chunk*) newcell();
            ((Stags*)r)->stags = CHUNK;
            q->car = (sexp) r;
        }
    }
}

// number->string (actually we will convert arbitrary s-expressions)
sexp number_string(sexp exp)
{
    std::stringstream s; ugly ugly(s); std::set<sexp> seenSet;
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    display(s, exp, seenSet, ugly, 0, true);
    return lose(newcell(STRING, save(newchunk(s.str().c_str()))));
}

// make-string
sexp make_string(sexp args)
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
    return lose(newcell(STRING, save(newchunk(b))));
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
sexp string_copy(sexp s)
{
    assertString(s);
    int len = slen(s)+1;
    return lose(newcell(STRING, save(newchunk(sstr((char*)alloca(len), len, s)))));
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
    return lose(newcell(STRING, save(newchunk(b))));
}

// string-fill
sexp string_fill(sexp s, sexp c)
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
sexp close_input_port(sexp p) { assertInPort(p); if (inport == p) inport = 0; deleteinport(p); return 0; }

// close-output-port
sexp close_output_port(sexp p) { assertOutPort(p); if (outport == p) outport = 0; deleteoutport(p); return 0; }

// current-input-port
sexp current_input_port(sexp p) { return inport; }

// current-output-port
sexp current_output_port(sexp p) { return outport; }

// input-port?
sexp input_portp(sexp p) { return isInPort(p) ? t : 0; }

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
sexp output_portp(sexp p) { return isOutPort(p) ? t : 0; }

// with-input-from-file
sexp with_input_from_file(sexp p, sexp f)
{
    sexp* mark = psp;
    sexp t = save(inport);
    inport = save(open_input_file(p));
    sexp q = save(apply(f, 0));
    close_input_port(inport);
    inport = t;
    return lose(mark, q);
}

// with-output-to-file
sexp with_output_to_file(sexp p, sexp f)
{
    sexp* mark = psp;
    sexp t = save(outport);
    outport = save(open_output_file(p));
    sexp q = save(apply(f, 0));
    close_output_port(outport);
    outport = t;
    return lose(mark, q);
}

// call-with-input-file
sexp call_with_input_file(sexp p, sexp f)
{
    sexp* mark = psp;
    sexp inp = save(open_input_file(p));
    sexp q = save(apply(f, save(cons(inp, 0))));
    close_input_port(inp);
    return lose(mark, q);
}

// call-with-output-file
sexp call_with_output_file(sexp p, sexp f)
{
    sexp* mark = psp;
    sexp oup = save(open_output_file(p));
    sexp q = save(apply(f, save(cons(oup, 0))));
    close_output_port(oup);
    return lose(mark, q);
}

// open-input-string
sexp open_input_string(sexp args)
{
    sexp s = args->car;
    int ii = 0;
    if (args->cdr)
        ii = asFixnum(args->cdr->car);
    int jj = slen(s);
    if (args->cdr->cdr)
        jj = asFixnum(args->cdr->cdr->car);
    if (ii < 0 || jj <= ii)
        error("open-input-string: bad arguments");

    std::stringstream* ss = new std::stringstream();
    InPort* port = (InPort*)save(newcell());
    ((Stags*)port)->stags = INPORT;
    port->avail = 0;
    port->peek = 0;
    port->s = new StrPortStream(*ss, 0);

    int k = 0;
    for (sexp p = ((String*)s)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        if (k <= ii && ii < k+sizeof(t->text))
        {
            for (int m = 0; m < sizeof(t->text); ++m)
            {
                int n = k+m;
                if (n == jj)
                    return lose((sexp)port);
                else if (ii <= n && n < jj)
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
    OutPort* p = (OutPort*)port;
    std::stringstream* ss = (std::stringstream*) p->s->streamPointer;
    return lose(newcell(STRING, save(newchunk(ss->str().c_str()))));
}

// open-output-string
sexp open_output_string(sexp args)
{
    std::stringstream* ss = new std::stringstream();
    OutPort* p = (OutPort*)newcell();
    ((Stags*)p)->stags = OUTPORT;
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
    sexp port = save(newcell());
    OutPort* p = (OutPort*)port;
    ((Stags*)p)->stags = OUTPORT;
    p->s = new StrPortStream(*ss, asFixnum(limit));
    apply(proc, save(cons(port, 0)));
    return lose(mark, get_output_string(port));
}

// write-to-string
sexp write_to_string(sexp args)
{
    sexp object = args->car;
    int limit = INT_MAX;
    if (args->cdr)
        limit = asFixnum(args->cdr->car);
    std::stringstream s; ugly ugly(s); std::set<sexp> seenSet;
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    display(s, object, seenSet, ugly, 0, true);
    return lose(newcell(STRING, save(newchunk(s.str().c_str()))));
}

// vector?
sexp vectorp(sexp v) { return isVector(v) ? t : 0; }

sexp newvector(int len, sexp fill)
{
    Vector* v = (Vector*) save(newcell());
    ((Stags*)v)->stags = VECTOR;
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
sexp char_alphabeticp(sexp c) { return isChar(c) && isalpha(((Char*)c)->ch) ? t : 0; }

// char->integer
sexp char_integer(sexp c) { assertChar(c); return  newfixnum(((Char*)c)->ch); }

// char-ci=?
sexp char_cieqp(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) == tolower(((Char*)q)->ch) ? t : 0; }

// char-ci>=?
sexp char_cigep(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) >= tolower(((Char*)q)->ch) ? t : 0; }

// char-ci>?
sexp char_cigtp(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) >  tolower(((Char*)q)->ch) ? t : 0; }

// char-ci<=?
sexp char_cilep(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) <= tolower(((Char*)q)->ch) ? t : 0; }

// char-ci<?
sexp char_ciltp(sexp p, sexp q) { assertChar(p); assertChar(q); return tolower(((Char*)p)->ch) <  tolower(((Char*)q)->ch) ? t : 0; }

// char=?
sexp char_eqp(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch == ((Char*)q)->ch ? t : 0; }

// char>=?
sexp char_gep(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch >= ((Char*)q)->ch ? t : 0; }

// char>?
sexp char_gtp(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch >  ((Char*)q)->ch ? t : 0; }

// char<=?
sexp char_lep(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch <= ((Char*)q)->ch ? t : 0; }

// char<?
sexp char_ltp(sexp p, sexp q) { assertChar(p); assertChar(q); return ((Char*)p)->ch <  ((Char*)q)->ch ? t : 0; }

// character?
sexp charp(sexp c) { return isChar(c) ? t : 0; }

// char-downcase
sexp char_downcase(sexp c) { assertChar(c); return newcharacter(tolower(((Char*)c)->ch)); }

// integer->char
sexp integer_char(sexp c) { assertFixnum(c); return newcharacter(asFixnum(c)); }

// char-lowercase?
sexp char_lower_casep(sexp c) { return isChar(c) && islower(((Char*)c)->ch) ? t : 0; }

// char-numeric?
sexp char_numericp(sexp c) { return isChar(c) && isdigit(((Char*)c)->ch) ? t : 0; }

// char-upcase
sexp char_upcase(sexp c) { assertChar(c); return newcharacter(toupper(((Char*)c)->ch)); }

// char-uppercase?
sexp char_upper_casep(sexp c) { return isChar(c) && isupper(((Char*)c)->ch) ? t : 0; }

// char-whitespace?
sexp char_whitespacep(sexp c) { return isChar(c) && isspace(((Char*)c)->ch) ? t : 0; }

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
sexp char_readyp(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);

    InPort* inPort = (InPort*)port;

    struct termios original;

    if (&cinStream == inPort->s && 0 == tcgetattr(0, &original))
    {
        struct termios working;

        if (inPort->avail)
            return t;

        setTermios(&original, &working, 0);

        if (0 == tcsetattr(0, TCSANOW, &working))
        {
            inPort->avail = read(0, &inPort->peek, 1) > 0;
            tcsetattr(0, TCSANOW, &original);
        }
        return inPort->avail ? t : 0;
    } else
        return t;
}

// read-char
sexp read_char(sexp args)
{
    sexp port = inport;
    if (args)
        assertInPort(port = args->car);

    InPort* inPort = (InPort*)port;

    struct termios original;

    if (&cinStream == inPort->s)
    {
        if (0 == tcgetattr(0, &original))
        {
            if (inPort->avail)
            {
                inPort->avail = false;
                return newcharacter(inPort->peek);
            }

            struct termios working;

            setTermios(&original, &working, 1);

            if (0 == tcsetattr(0, TCSANOW, &working))
            {
                while (0 == read(0, &inPort->peek, 1)) {}
                tcsetattr(0, TCSANOW, &original);
            }
            return newcharacter(inPort->peek);
        }
        return newcharacter(std::cin.get());
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

    struct termios original;

    if (&cinStream == inPort->s)
    {
        if (0 == tcgetattr(0, &original))
        {
            if (inPort->avail)
                return newcharacter(inPort->peek);

            struct termios working;

            setTermios(&original, &working, 1);

            if (0 == tcsetattr(0, TCSANOW, &working))
            {
                while (0 == read(0, &inPort->peek, 1)) {}
                inPort->avail = true;
                tcsetattr(0, TCSANOW, &original);
            }
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

    ((OutPort*)port)->s->put(((Char*)(args->car))->ch);

    return voida;
}

sexp achunk(sexp s) { assertString(s); return ((String*)s)->chunks; }

// string<=?
sexp string_lep(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) <= 0 ? t : 0; }

// string<?
sexp string_ltp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) <  0 ? t : 0; }

// string=?
sexp string_eqp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) == 0 ? t : 0; }

// string>=?
sexp string_gep(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) >= 0 ? t : 0; }

// string>?
sexp string_gtp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmp(p, q) >  0 ? t : 0; }

// string-ci-<=?
sexp string_cilep(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) <= 0 ? t : 0; }

// string-ci<?
sexp string_ciltp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) <  0 ? t : 0; }

// string-ci=?
sexp string_cieqp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) == 0 ? t : 0; }

// string-ci>=?
sexp string_cigep(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) >= 0 ? t : 0; }

// string-ci>?
sexp string_cigtp(sexp p, sexp q) { p=achunk(p); q = achunk(q); return scmpi(p, q) >  0 ? t : 0; }

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
                    return lose(newcell(STRING, save(newchunk(b))));
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
    sexp* mark = psp;
    save(p, q);
    return lose(mark, p ? cons(p->car, save(append(p->cdr, q))) : q);
}

// reverse
sexp reverse(sexp x) { sexp t = 0; while (isCons(x)) { t = cons(car(x), t); x = x->cdr; } return t; }

// eq?
sexp eqp(sexp x, sexp y) { return x == y ? t : 0; }

// =
sexp eqnp(sexp x, sexp y)
{
    if (isRational(x) && isRational(y))
        return (asFixnum(x->cdr->car) == asFixnum(y->cdr->car) &&
                asFixnum(x->cdr->car) == asFixnum(y->cdr->car)) ? t : 0;
 
    if (isComplex(x) && isComplex(y))
        return (asFlonum(x->cdr->car) == asFlonum(y->cdr->car) &&
                asFlonum(x->cdr->cdr->car) == asFlonum(y->cdr->cdr->car)) ? t : 0;

    return asFlonum(x) == asFlonum(y) ? t : 0;
}

// ~ x
sexp complement(sexp x) { return isFixnum(x) ? newfixnum(~asFixnum(x)) : 0; }

// all arguments must be fixnums for these logical operations
sexp allfixnums(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
        if (!isFixnum(p->car))
            return 0;
    return t;
}

// x0 & x1 & x2 ...
sexp andf(sexp args)
{
    if (allfixnums(save(args))) {
        long result = ~0;
        for (sexp p = args; p; p = p->cdr)
            result = result & asFixnum(p->car);
        return lose(newfixnum(result));
    } else
        return lose(0);
}

// x0 | x1 | x2 ...
sexp orf(sexp args)
{
    if (allfixnums(save(args))) {
        long result = 0;
        for (sexp p = args; p; p = p->cdr)
            result = result | asFixnum(p->car);
        return lose(newfixnum(result));
    } else
        return lose(0);
}

// x0 ^ x1 ^ x2 ...
sexp xorf(sexp args)
{
    if (allfixnums(save(args))) {
        long result = 0;
        for (sexp p = args; p; p = p->cdr)
            result = result ^ asFixnum(p->car);
        return lose(newfixnum(result));
    } else
        return lose(0);
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
            if (tracing)
                debug("load", input);
            eval(input, global);
        }
        return t;
    }
    return 0;
}

// space
sexp space(sexp args) { sexp port = args ? args->car : outport; assertOutPort(port); ((OutPort*)port)->s->put(' '); return voida; }

// newline
sexp newline(sexp args) { sexp port = args ? args->car : outport; assertOutPort(port); ((OutPort*)port)->s->put('\n'); return voida; }

// eof-object?
sexp eof_objectp(sexp a) { return eof == a ? t : 0; }

// display
sexp displayf(sexp args)
{
    std::stringstream s; ugly ugly(s); std::set<sexp> seenSet;
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
    std::stringstream s; ugly ugly(s); std::set<sexp> seenSet;
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

bool cyclic(sexp exp) { std::set<sexp> seenSet; return cyclic(seenSet, exp); }

// cyclic?
sexp cyclicp(sexp x) { return cyclic(x) ? t : 0; }

// for prettyprinting
int displayLength(sexp exp)
{
    std::stringstream ss; ugly ugly(ss); std::set<sexp> seenSet;
    ss << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    display(ss, exp, seenSet, ugly, 0, true);
    return ss.str().length();
}

std::ostream& displayList(std::ostream& s, sexp exp, std::set<sexp>& seenSet, ugly& ugly, int level, bool write)
{
    s << '(';
    level += 2;
    while (exp && seenSet.find(exp) == seenSet.end())
    {
        display(s, exp->car, seenSet, ugly, level+2, write);
        seenSet.insert(exp);
        if (exp->cdr) {
            if (isCons(exp->cdr) && !isClosure(exp->cdr) && !isPromise(exp->cdr))
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

std::ostream& displayVector(std::ostream& s, sexp v, std::set<sexp>& seenSet, ugly& ugly, int level, bool write)
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

const char *character_table[] =
{
    "\000nul",       "\001soh", "\002stx",     "\003etx", "\004eot", "\005enq",    "\006ack", "\007bell",
    "\010backspace", "\011tab", "\012newline", "\013vt",  "\014ff",  "\015return", "\016so",  "\017si",
    "\020dle",       "\021dc1", "\022dc2",     "\023dc3", "\024dc4", "\025nak",    "\026syn", "\027etb",
    "\030can",       "\031em",  "\032sub",     "\033esc", "\034fs",  "\035gs",     "\036rs",  "\037us",
    "\040space",     "\177del", 0
};

std::ostream& displayAtom(std::ostream& s, sexp exp, bool write)
{
    return displayChunks(s, ((Atom*)exp)->chunks, true, write);
}

std::ostream& displayString(std::ostream& s, sexp exp, bool write)
{
    return displayChunks(s, ((Atom*)exp)->chunks, false, write);
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
    if (write)
    {
        char c = ((Char*)exp)->ch;
        for (int i = 0; character_table[i]; ++i)
            if (c == *character_table[i]) {
                s << "#\\" << 1+character_table[i];
                return s;
            }
        s << "#\\" << ((Char*)exp)->ch;;
    } else
        s << ((Char*)exp)->ch;
    return s;
}

std::ostream& displayRational(std::ostream& s, sexp exp)
{
    s << asFixnum(exp->cdr->car) << '/' << asFixnum(exp->cdr->cdr->car);
    return s;
}

std::ostream& display(std::ostream& s, sexp exp, std::set<sexp>& seenSet, ugly& ugly, int level, bool write)
{
    if (!exp)
    {
        s << "#f";
        return s;
    } else if (isCons(exp)) {
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
    std::stringstream s; ugly ugly(s); std::set<sexp> seenSet;
    s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
    s << label << ": ";
    if (voida == exp)
        s << "void";
    else
        display(s, exp, seenSet, ugly, 0, true);
    s << '\n';
    std::cout.write(s.str().c_str(), s.str().length());
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
sexp string_symbol(sexp x) { assertString(x); return lose(intern(newcell(ATOM, save((((String*)x)->chunks))))); }

// symbol->string
sexp symbol_string(sexp x) { assertAtom(x); return lose(newcell(STRING, save(((Atom*)x)->chunks))); }

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
    sexp p = save(newcell());
    sexp q = p;
    Chunk* r = (Chunk*) newcell();
    ((Stags*)r)->stags = CHUNK;
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
            ((Stags*)r)->stags = CHUNK;
            q->car = (sexp) r;
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
    if (!x || !y)
        return false;
    if (isAtom(x) || isAtom(y))
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
sexp eqvp(sexp x, sexp y) { std::set<sexp> seenx; std::set<sexp> seeny; return eqvb(seenx, seeny, x, y) ? t : 0; }

// equal?
sexp equalp(sexp x, sexp y) { std::set<sexp> seenx; std::set<sexp> seeny; return eqvb(seenx, seeny, x, y) ? t : 0; }

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
    global = cons(save(cons(p, r)), global);
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
    return voida;
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
    sexp* mark = psp;
    save(p, env);
    return p ? lose(mark, cons(save(eval(p->car, env)), save(evlis(p->cdr, env)))) : 0;
}

// associate a list of formal parameters and actual parameters in an environment
sexp assoc(sexp formals, sexp actuals, sexp env)
{
    if (!actuals || !formals)
        return env;
    sexp* mark = psp;
    save(actuals, formals, env);
    return lose(mark, cons(save(cons(formals->car, actuals->car)),
                           save(assoc(formals->cdr, actuals->cdr, env))));
}

// null-environment
sexp null_environment(sexp exp, sexp env) { return global; }

// interaction-environment
sexp interaction_environment(sexp exp, sexp env) { return env; }

// begin
sexp begin(sexp exp, sexp env)
{
    sexp v = 0;
    for (sexp p = exp->cdr; p; p = p->cdr)
        v = eval(p->car, env);
    return v;
}

// while
sexp whileform(sexp exp, sexp env)
{
    sexp v = 0;
    exp = exp->cdr;
    while (eval(exp->car, env))
        for (sexp p = exp->cdr; p; p = p->cdr)
            v = eval(p->car, env);
    return v;
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
        if (elsea == p->car->car || eval(p->car->car, env))
            return eval(p->car->cdr->car, env);
    return voida;
}

// lambda creates a closure
sexp lambdaform(sexp exp, sexp env)
{
    return lose(cons(closure, replace(cons(exp, save(cons(env, 0))))));
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
            sexp k = p->cdr->car->car;
            sexp v = replace(cons(lambda, save(cons(p->cdr->car->cdr, p->cdr->cdr))));
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
            sexp k = p->cdr->car->car;
            sexp v = replace(cons(lambda, replace(cons(save(cons(p->cdr->car->car, p->cdr->car->cdr)), p->cdr->cdr))));
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
                q->car->cdr = eval(p->cdr->cdr->car, env);
                return lose(mark, voida);
            }
        global = cons(replace(cons(p->cdr->car, save(eval(p->cdr->cdr->car, env)))), global);
        return lose(mark, voida);
    }
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
    else if (unquote == exp->car && isCons(exp->cdr))
        return eval(exp->cdr->car, env);
    else if (exp->car && unquotesplicing == exp->car->car)
        return lose(mark, replace(append(save(eval(exp->car->cdr->car, env)),
                                         save(unquoteform(exp->cdr, env)))));
    else
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
    if (!exp->cdr->cdr)
        error("if: missing consequent");
    if (eval(exp->cdr->car, env))
        return eval(exp->cdr->cdr->car, env);
    if (exp->cdr->cdr->cdr)
        return eval(exp->cdr->cdr->cdr->car, env);
    return voida;
}

sexp whenform(sexp exp, sexp env)
{
    if (!exp->cdr)
        error("when: missing predicate");
    if (!exp->cdr->cdr)
        error("when: missing consequent");
    if (eval(exp->cdr->car, env))
        eval(exp->cdr->cdr->car, env);
    return voida;
}

sexp unlessform(sexp exp, sexp env)
{
    if (!exp->cdr)
        error("unless: missing predicate");
    if (!exp->cdr->cdr)
        error("unless: missing consequent");
    if (!eval(exp->cdr->car, env))
        eval(exp->cdr->cdr->car, env);
    return voida;
}

sexp caseform(sexp exp, sexp env)
{
    sexp* mark = psp;

    if (!exp->cdr)
        error("case: missing key");

    sexp key = exp->cdr->car;

    sexp r = save(voida);
    for (exp = exp->cdr->cdr; exp; exp = exp->cdr)
    {
        if (elsea = exp->car)
        {
            for (sexp p = exp->cdr; p; p = p->cdr)
                r = replace(eval(p->car, env));
            return lose(r);
        }

        for (sexp p = exp->car->car; p; p = p->cdr)
            if (key == p->car)
            {
                for (p = exp->cdr; p; p = p->cdr)
                    r = replace(eval(p->car, env));
                return lose(r);
            }
    }
    return lose(voida);
}

/*
 * (set! name value) alters an existing binding
 */
sexp setform(sexp exp, sexp env)
{
    return lose(set(exp->cdr->car, save(eval(exp->cdr->cdr->car, env)), env));
}

// (let ((var val) (var val) ..) body )
sexp let(sexp exp, sexp env)
{
    sexp* mark = psp;
    sexp e = env;
    for (sexp v = exp->cdr->car; v; v = v->cdr)
        e = replace(cons(replace(cons(v->car->car, save(eval(v->car->cdr->car, env)))), e));
    sexp r = save(voida);
    for (sexp p = exp->cdr->cdr; p; p = p->cdr)
        r = save(eval(p->car, e));
    return lose(mark, r);
}

// (let* ((var val) (var val) ..) body )
sexp letstar(sexp exp, sexp env)
{
    sexp* mark = psp;
    sexp e = env;
    for (sexp v = exp->cdr->car; v; v = v->cdr)
        e = replace(cons(replace(cons(v->car->car, save(eval(v->car->cdr->car, e)))), e));
    sexp r = save(voida);
    for (sexp p = exp->cdr->cdr; p; p = p->cdr)
        r = replace(eval(p->car, e));
    return lose(mark, r);
}

// (letrec ((var val) (var val) ..) body )
sexp letrec(sexp exp, sexp env)
{
    sexp* mark = psp;
    sexp e = env;
    for (sexp v = exp->cdr->car; v; v = v->cdr)
        e = replace(cons(save(cons(v->car->car, v->car->cdr->car)), e));
    for (sexp v = exp->cdr->car; v; v = v->cdr)
        set(v->car->car, eval(v->car->cdr->car, e), e);
    sexp r = save(voida);
    for (sexp p = exp->cdr->cdr; p; p = p->cdr)
        r = replace(eval(p->car, e));
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
    sexp e = env;
    // bind all the variables to their values
    for (sexp v = exp->cdr->car; v; v = v->cdr)
        e = replace(cons(save(cons(v->car->car, v->car->cdr->car)), e));
    sexp s = save(voida);
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

    if (false && tracing)
    {
        debug("apply-fun", fun);
        debug("apply-args", args);
    }

    if (isFunct(fun))
    {
        switch (arity(fun))
        {
        case 0: return (*(Varargp)((Funct*)fun)->funcp)(args);
        case 1: return (*(Oneargp)((Funct*)fun)->funcp)(args ? args->car : 0);
        case 2: return (*(Twoargp)((Funct*)fun)->funcp)(args->car, args->cdr->car);
        case 3: return (*(Threeargp)((Funct*)fun)->funcp)(args->car, args->cdr->car, args->cdr->cdr->car);
        }
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
            return s;
        } else if (isAtom(fun->cdr->car->cdr->car->cdr)) {
            // fun->cdr->car = (lambda (f . s) foo)
            sexp e = replace(cons(save(cons(fun->cdr->car->cdr->car->cdr, args)), cenv));
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

// (rational numerator denominator)
sexp rationalform(sexp exp, sexp env) { assertRational(exp); return exp; }

// (complex real imaginary)
sexp complexform(sexp exp, sexp env) { assertComplex(exp); return exp; }

/*
 * malformed constructs will fail without grace
 */
sexp eval(sexp p, sexp env)
{
    if (tracing)
        debug("eval", p);

    if (!p || f == p || t == p || (OTHER & shortType(p)) && shortType(p) > ATOM)
        return p;

    if (isAtom(p))
    {
        // it pays to inline get() here
        for (sexp q = env; q; q = q->cdr)
            if (q->car && p == q->car->car)
                return q->car->cdr;
        debug("eval: undefined ", p); error("");
    }

    sexp* mark = psp;

    save(p, env);

    sexp fun = save(eval(p->car, env));

    if (isForm(fun))
        return lose(mark, (*((Form*)fun)->formp)(p, env));

    sexp args = save(evlis(p->cdr, env));

    return lose(mark, apply(fun, args));
}

/*
 * read Chunks terminated by some character or eof
 */
sexp readChunks(std::istream& fin, const char *ends)
{
    sexp* mark = psp;
    sexp p = save(newcell());
    sexp q = p;
    Chunk* r = (Chunk*) newcell();
    ((Stags*)r)->stags = CHUNK;
    q->car = (sexp) r;

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
            q = q->cdr = newcell();
            r = (Chunk*) newcell();
            ((Stags*)r)->stags = CHUNK;
            q->car = (sexp) r;
        }
    }
}

// ignore white space and comments
char whitespace(std::istream& fin, char c)
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

    char c = whitespace(fin, fin.get());

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
               case 'f': return 0;
               case 't': return t;
               case '\\':
                    c = fin.get();
                    while (0 <= c && !isspace(c) && ')' != c && ']' != c && ',' != c)
                        { s.put(c); c = fin.get(); }
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

    if ('"' == c)
    {
        c = fin.get();
        sexp r = newcell(STRING, save(readChunks(fin, "\"")));
        (void)fin.get();  // read the " again
        return lose(mark, r);
    }

    return lose(mark, intern(save(newcell(ATOM, save(readChunks(fin, "( )[,]\t\r\n"))))));
}

// stub to enable tracing of scans()
sexp scan(std::istream& fin) { sexp r = scans(fin); if (tracing) debug("scan", r); return r; }

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
    else
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
            return 0;
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
    if (nil == p)
        return 0;
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
sexp atomize(const char *s) { sexp* mark = psp; return lose(mark, intern(save(newcell(ATOM, save(newchunk(s)))))); }

// the first interrupt will stop everything. the second will exit.
void intr_handler(int sig, siginfo_t *si, void *ctx)
{
    if (killed++)
        exit(0);
    if (collecting)
        std::cout << "collecting now" << std::endl;
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

int main(int argc, char **argv, char **envp)
{
    // allocate all the cells we will ever have
    cell = (sexp)new Cons[CELLS];
    for (int i = CELLS; --i >= 0; )
    {
        cell[i].car = 0;
        cell[i].cdr = freelist;
        freelist = cell+i;
    }

    // allocate the protection stack
    psp = protect = (sexp*)new sexp[PSIZE];
    psend = protect + PSIZE;

    // allocate ports for cin, cout, cerr
    inport  = newcell(INPORT,  (sexp)&cinStream);
    outport = newcell(OUTPORT, (sexp)&coutStream);
    errport = newcell(OUTPORT, (sexp)&cerrStream);

    zero = newfixnum(0);
    one  = newfixnum(1);

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

    define(atomize("cerr"), errport);
    define(atomize("cin"),  inport);
    define(atomize("cout"), outport);

    // metasyntax
    define(atomize("comma"),    comma);
    define(atomize("commaat"),  commaat);
    define(atomize("dot"),      dot);
    define(atomize("lbracket"), lbracket);
    define(atomize("lparen"),   lparen);
    define(atomize("qchar"),    qchar);
    define(atomize("rbracket"), rbracket);
    define(atomize("rparen"),   rparen);
    define(atomize("tick"),     tick);
    define(atomize("void"),     voida);

    define_funct(atomize("&"), 0, (void*)andf);
    define_funct(atomize("|"), 0, (void*)orf);
    define_funct(atomize("^"), 0, (void*)xorf);
    define_funct(atomize("~"), 1, (void*)complement);
    define_funct(atomize("<<"), 2, (void*)lsh);
    define_funct(atomize(">>"), 2, (void*)rsh);
    define_funct(atomize("acos"), 1, (void*)acosff);
    define_funct(atomize("angle"), 1, (void*)angle);
    define_funct(atomize("append"), 2, (void*)append);
    define_funct(atomize("apply"), 2, (void*)apply);
    define_funct(atomize("asin"), 1, (void*)asinff);
    define_funct(atomize("atan"), 1, (void*)atanff);
    define_funct(atomize("atan2"), 2, (void*)atan2ff);
    define_funct(atomize("atom?"), 1, (void*)atomp);
    define_funct(atomize("atoms"), 0, (void*)atomsf);
    define_funct(atomize("boolean?"), 1, (void*)booleanp);
    define_funct(atomize("call-with-input-file"), 2, (void*)call_with_input_file);
    define_funct(atomize("call-with-output-file"), 2, (void*)call_with_output_file);
    define_funct(atomize("call-with-output-string"), 1, (void*)call_with_output_string);
    define_funct(atomize("call-with-truncated-output-string"), 2, (void*)call_with_truncated_output_string);
    define_funct(atomize("ceiling"), 1, (void*)ceilingff);
    define_funct(atomize("char?"), 1, (void*)charp);
    define_funct(atomize("char=?"), 2, (void*)char_eqp);
    define_funct(atomize("char>=?"), 2, (void*)char_gep);
    define_funct(atomize("char>?"), 2, (void*)char_gtp);
    define_funct(atomize("char<=?"), 2, (void*)char_lep);
    define_funct(atomize("char<?"), 2, (void*)char_ltp);
    define_funct(atomize("char-alphabetic?"), 1, (void*)char_alphabeticp);
    define_funct(atomize("char-ci=?"), 2, (void*)char_cieqp);
    define_funct(atomize("char-ci>=?"), 2, (void*)char_cigep);
    define_funct(atomize("char-ci>?"), 2, (void*)char_cigtp);
    define_funct(atomize("char-ci<=?"), 2, (void*)char_cilep);
    define_funct(atomize("char-ci<?"), 2, (void*)char_ciltp);
    define_funct(atomize("char-downcase"), 1, (void*)char_downcase);
    define_funct(atomize("char->integer"), 1, (void*)char_integer);
    define_funct(atomize("char-lower-case?"), 1, (void*)char_lower_casep);
    define_funct(atomize("char-numeric?"), 1, (void*)char_numericp);
    define_funct(atomize("char-ready?"), 0, (void*)char_readyp);
    define_funct(atomize("char-upcase"), 1, (void*)char_upcase);
    define_funct(atomize("char-upper-case?"), 1, (void*)char_upper_casep);
    define_funct(atomize("char-whitespace?"), 1, (void*)char_whitespacep);
    define_funct(atomize("close-input-port"), 1, (void*)close_input_port);
    define_funct(atomize("close-output-port"), 1, (void*)close_output_port);
    define_funct(atomize("closure?"), 1, (void*)closurep);
    define_funct(atomize("complex?"), 1, (void*)complexp);
    define_funct(atomize("cos"), 1, (void*)cosff);
    define_funct(atomize("cosh"),  1, (void*)coshff);
    define_funct(atomize("current-input-port"), 0, (void*)current_input_port);
    define_funct(atomize("current-output-port"), 0, (void*)current_output_port);
    define_funct(atomize("cyclic?"), 1, (void*)cyclicp);
    define_funct(atomize("display"), 0, (void*)displayf);
    define_funct(atomize("eof-object?"), 1, (void*)eof_objectp);
    define_funct(atomize("eval"), 2, (void*)eval);
    define_funct(atomize("exact?"), 1, (void*)exactp);
    define_funct(atomize("exact->inexact"), 1, (void*)exact_inexact);
    define_funct(atomize("exp"), 1, (void*)expff);
    define_funct(atomize("floor"), 1, (void*)floorff);
    define_funct(atomize("force"), 1, (void*)force);
    define_funct(atomize("gc"), 0, (void*)gc);
    define_funct(atomize("gcd"), 2, (void*)gcdf);
    define_funct(atomize("get-output-string"),  1, (void*)get_output_string);
    define_funct(atomize("inexact?"), 1, (void*)inexactp);
    define_funct(atomize("inexact->exact"), 1, (void*)inexact_exact);
    define_funct(atomize("input-port?"), 1, (void*)input_portp);
    define_funct(atomize("integer?"), 1, (void*)integerp);
    define_funct(atomize("integer->char"), 1, (void*)integer_char);
    define_funct(atomize("lcm"), 2, (void*)lcmf);
    define_funct(atomize("list?"), 1, (void*)listp);
    define_funct(atomize("list->string"), 1, (void*)list_string);
    define_funct(atomize("list->vector"), 1, (void*)list_vector);
    define_funct(atomize("load"), 1, (void*)load);
    define_funct(atomize("log"), 1, (void*)logff);
    define_funct(atomize("magnitude"), 1, (void*)magnitude);
    define_funct(atomize("make-string"), 0, (void*)make_string);
    define_funct(atomize("make-vector"), 0, (void*)make_vector);
    define_funct(atomize("newline"), 0, (void*)newline);
    define_funct(atomize("number?"), 1, (void*)numberp);
    define_funct(atomize("number->string"), 1, (void*)number_string);
    define_funct(atomize("open-input-file"), 1, (void*)open_input_file);
    define_funct(atomize("open-input-string"), 0, (void*)open_input_string);
    define_funct(atomize("open-output-file"), 1, (void*)open_output_file);
    define_funct(atomize("open-output-string"), 0, (void*)open_output_string);
    define_funct(atomize("output-port?"), 1, (void*)output_portp);
    define_funct(atomize("peek-char"), 0, (void*)peek_char);
    define_funct(atomize("pow"), 2, (void*)powff);
    define_funct(atomize("procedure?"), 1, (void*)procedurep);
    define_funct(atomize("promise?"), 1, (void*)promisep);
    define_funct(atomize("promise-forced?"), 1, (void*)promise_forcedp);
    define_funct(atomize("promise-value"), 1, (void*)promise_value);
    define_funct(atomize("rational?"), 1, (void*)rationalp);
    define_funct(atomize("read"), 0, (void*)readf);
    define_funct(atomize("read-char"), 0, (void*)read_char);
    define_funct(atomize("real?"), 1, (void*)realp);
    define_funct(atomize("reverse"), 1, (void*)reverse);
    define_funct(atomize("round"), 1, (void*)roundff);
    define_funct(atomize("scan"),     0, (void*)scanff);
    define_funct(atomize("set-car!"), 2, (void*)set_car);
    define_funct(atomize("set-cdr!"), 2, (void*)set_cdr);
    define_funct(atomize("sin"), 1, (void*)sinff);
    define_funct(atomize("sinh"),  1, (void*)sinhff);
    define_funct(atomize("space"), 0, (void*)space);
    define_funct(atomize("sqrt"), 1, (void*)sqrtff);
    define_funct(atomize("isqrt"), 1, (void*)isqrtf);
    define_funct(atomize("string"), 0, (void*)string);
    define_funct(atomize("string?"), 1, (void*)stringp);
    define_funct(atomize("string=?"), 2, (void*)string_eqp);
    define_funct(atomize("string>=?"), 2, (void*)string_gep);
    define_funct(atomize("string>?"), 2, (void*)string_gtp);
    define_funct(atomize("string<=?"), 2, (void*)string_lep);
    define_funct(atomize("string<?"), 2, (void*)string_ltp);
    define_funct(atomize("string-append"), 2, (void*)string_append);
    define_funct(atomize("string-ci=?"), 2, (void*)string_cieqp);
    define_funct(atomize("string-ci>=?"), 2, (void*)string_cigep);
    define_funct(atomize("string-ci>?"), 2, (void*)string_cigtp);
    define_funct(atomize("string-ci<=?"), 2, (void*)string_cilep);
    define_funct(atomize("string-ci<?"), 2, (void*)string_ciltp);
    define_funct(atomize("string-copy"), 1, (void*)string_copy);
    define_funct(atomize("string-fill!"), 2, (void*)string_fill);
    define_funct(atomize("string-length"), 1, (void*)string_length);
    define_funct(atomize("string->list"), 1, (void*)string_list);
    define_funct(atomize("string->number"), 1, (void*)string_number);
    define_funct(atomize("string-ref"), 2, (void*)string_ref);
    define_funct(atomize("string-set!"), 3, (void*)string_set);
    define_funct(atomize("string->symbol"), 1, (void*)string_symbol);
    define_funct(atomize("substring"), 0, (void*)substringf);
    define_funct(atomize("symbol?"), 1, (void*)symbolp);
    define_funct(atomize("symbol->string"), 1, (void*)symbol_string);
    define_funct(atomize("tan"), 1, (void*)tanff);
    define_funct(atomize("tanh"),  1, (void*)tanhff);
    define_funct(atomize("trace"), 1, (void*)trace);
    define_funct(atomize("truncate"), 1, (void*)truncateff);
    define_funct(atomize("undefine"), 1, (void*)undefine);
    define_funct(atomize("vector"), 0, (void*)vector);
    define_funct(atomize("vector?"), 1, (void*)vectorp);
    define_funct(atomize("vector-fill!"), 2, (void*)vector_fill);
    define_funct(atomize("vector-length"), 1, (void*)vector_length);
    define_funct(atomize("vector->list"), 1, (void*)vector_list);
    define_funct(atomize("vector-ref"), 2, (void*)vector_ref);
    define_funct(atomize("vector-set!"), 3, (void*)vector_set);
    define_funct(atomize("with-input-from-file"), 2, (void*)with_input_from_file);
    define_funct(atomize("with-output-to-file"), 2, (void*)with_output_to_file);
    define_funct(atomize("write"), 0, (void*)writef);
    define_funct(atomize("write-char"), 0, (void*)write_char);
    define_funct(atomize("write-to-string"), 0, (void*)write_to_string);

    define_funct(atomize("null?"), 1, (void*)nullp);
    define_funct(atomize("pair?"), 1, (void*)pairp);
    define_funct(atomize("negative?"), 1, (void*)negativep);
    define_funct(atomize("positive?"), 1, (void*)positivep);
    define_funct(atomize("%"), 0, (void*)unimod);
    define_funct(atomize("/"), 0, (void*)unidiv);
    define_funct(atomize("not"), 1, (void*)isnot);
    define_funct(atomize("neg"), 1, (void*)unineg);
    define_funct(atomize("<"), 2, (void*)ltp);
    define_funct(atomize("<="), 2, (void*)lep);
    define_funct(atomize(">="), 2, (void*)gep);
    define_funct(atomize(">"), 2, (void*)gtp);
    define_funct(atomize("eq?"), 2, (void*)eqp);
    define_funct(atomize("="), 2, (void*)eqnp);
    define_funct(atomize("equal?"), 2, (void*)equalp);
    define_funct(atomize("eqv?"), 2, (void*)eqvp);
    define_funct(atomize("+"), 0, (void*)uniadd);
    define_funct(atomize("-"), 0, (void*)unisub);
    define_funct(atomize("*"), 0, (void*)unimul);
    define_funct(atomize("car"), 1, (void*)car);
    define_funct(atomize("cdr"), 1, (void*)cdr);
    define_funct(atomize("cons"), 2, (void*)cons);

    define_form(atomize("begin"), begin);
    define_form(atomize("bound?"), boundp);
    define_form(atomize("case"), caseform);
    define_form(atomize("cond"), cond);
    define_form(atomize("define"), defineform);
    define_form(atomize("delay"), delayform);
    define_form(atomize("do"), doform);
    define_form(atomize("interaction-environment"), interaction_environment);
    define_form(atomize("null-environment"), null_environment);
    define_form(atomize("let"), let);
    define_form(atomize("let*"), letstar);
    define_form(atomize("letrec"), letrec);
    define_form(atomize("quasiquote"), quasiquoteform);
    define_form(atomize("set!"), setform);
    define_form(atomize("while"), whileform);
    define_form(atomize("when"), whenform);
    define_form(atomize("unless"), unlessform);
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

    //tracing = t;

    char *s = (char*) sigsetjmp(the_jmpbuf, 1);
    if (s)
        std::cout << s << std::endl;

    sigaction(SIGSEGV, &segv_action, NULL);
    sigaction(SIGINT,  &intr_action, NULL);

    load(newcell(STRING, newchunk("init.ss")));

    fixenvs(global);

    if (argc > 1)
    {
        load(newcell(STRING, newchunk(argv[1])));
        return 0;
    }

    killed = 0;

    s = (char*) sigsetjmp(the_jmpbuf, 1);
    if (s)
        std::cout << s << std::endl;

    // read evaluate display ...

    gc(atoms);

    for (;;)
    {
        if (psp > protect)
            if ((long)(psp-protect) > 1)
                std::cout << (long)(psp-protect) << " items remain on protection stack" << std::endl;
            else
                std::cout << "one item remains on protection stack" << std::endl;
        total = 0;
        collected = 0;
        std::cout << "> ";
        std::cout.flush();
        sexp e = read(std::cin, 0);
        if (eof == e)
            break;
        killed = 0;
        sexp v = eval(e, global);
        {
            std::stringstream s; ugly ugly(s); std::set<sexp> seenSet;
            s << std::setprecision(sizeof(double) > sizeof(void*) ? 8 : 15);
            display(s, v, seenSet, ugly, 0, false);
            std::cout.write(s.str().c_str(), s.str().length());
            if (voida != v)
                std::cout << std::endl;
        }
    }
    return 0;
}

