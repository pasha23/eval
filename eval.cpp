/*
 * this is kind of a lisp interpreter for my own amusement
 * not at all standards compliant or industrial strength
 * dynamically scoped, without tail call optimization
 *
 * there are gc issues at present
 * circular lists cannot be printed
 * syntactic atoms need meta-syntax when printed
 * quasiquote
 * 
 * Robert Kelley October 2019
 */
#define __STDC_FORMAT_MACROS
#include <inttypes.h>
#define UNW_LOCAL_ONLY
#include <libunwind.h>
#include <cxxabi.h>
#include <setjmp.h>
#include <iostream>
#include <fstream>
#include <cstring>
#include <cstdlib>
#include <csignal>
#include <climits>

#define GC
#define MAX 4096
#undef  DEBUG
#define VOLUNTARY_GC
#undef  SIGNALS

/*
 * storage is managed as a freelist of nodes, each potentially containing two pointers
 * the low 4 bits contain a tag that identifies the type of node except usual list cells
 * naturally have a tag of 0.  Chunks contain the text of atoms linked in a list, but
 * the tag is not present unless the Chunk is marked for garbage collection. Bit 3 is
 * used to mark reachable nodes during garbage collection.  There are just enough bits
 * available to implement this plan.
 */
enum Tag
{
    CONS   = 0,
    CHUNK  = 1,
    ATOM   = 2,
    FORM   = 3,
    NUMBER = 4,
    FUNCT  = 5,
    STRING = 6,
    UNUSD7 = 7,
    MARK   = 8
};

const char* nodeTypes[] =
{
	"CONS",
    "CHUNK",
	"ATOM",
	"FORM",
	"NUMBER",
	"FUNCTION",
	"STRING",
	"UNUSD7",
	"MARK"
};

typedef struct Cons *sexp;
typedef sexp (*Formp)(sexp, sexp);
typedef sexp (*Varargp)(sexp);
typedef sexp (*Oneargp)(sexp);
typedef sexp (*Twoargp)(sexp, sexp);

/*
 * setting up union declarations isn't all that fun
 */
struct Cons   { sexp   cdr; sexp    car;                 };
struct Chunk  { Chunk* cdr; char    text[sizeof(void*)]; };
struct Atom   { Tag    tag; Chunk*  chunks;              };
struct String { Tag    tag; Chunk*  chunks;              };
struct Fixnum { Tag    tag; long    fixnum;              };
struct Funct  { long   tag; void*   funcp;               };
struct Form   { Tag    tag; Formp   formp;               };

sexp eval(sexp p, sexp env);
sexp evlis(sexp p, sexp env);
std::ostream& print(std::ostream& output, sexp p);
sexp set(sexp p, sexp r);
sexp assoc(sexp formals, sexp actuals, sexp env);
sexp read(std::istream& input);
sexp scan(std::istream& input);

// these are the built-in atoms

sexp atomsa, begin, cara, cdra, cond, consa, define, divide, dot, elsea;
sexp gea, gta, eqva, globals, ifa, lambda, lparen, lea, let, loada, lta;
sexp max, min, minus, modulo, nil, nota, plus, printa, println, qchar;
sexp quote, reada, rparen, seta, t, times, voida, whilea;

int  marked = 0;            // how many nodes were marked during gc
sexp atoms = 0;             // all atoms are linked in a list
sexp block = 0;             // all the storage starts here
sexp global = 0;            // this is the global symbol table (a list)
sexp protect = 0;           // protects otherwise unreachable objects from gc
sexp freelist = 0;          // available nodes are linked in a list
int allocated = 0;          // how many nodes have been allocated

static inline int  nodeType(const sexp p) { return 15                & (long)p->cdr;  }
static inline int  numArgs(const sexp p)  { return (long)p->cdr >> 4;                 }
static inline bool isMarked(const sexp p) { return p && MARK         & (long)p->cdr;  }
static inline bool isCons(const sexp p)   { return p && CONS   == (7 & (long)p->cdr); }
static inline bool isChunk(const sexp p)  { return p && CHUNK  == (7 & (long)p->cdr); }
static inline bool isAtom(const sexp p)   { return p && ATOM   == (7 & (long)p->cdr); }
static inline bool isString(const sexp p) { return p && STRING == (7 & (long)p->cdr); }
static inline bool isFunct(const sexp p)  { return p && FUNCT  == (7 & (long)p->cdr); }
static inline bool isForm(const sexp p)   { return p && FORM   == (7 & (long)p->cdr); }
static inline bool isFixnum(const sexp p) { return p && NUMBER == (7 & (long)p->cdr); }

jmp_buf the_jmpbuf;

/*
 * mark the node
 */
static void markNode(sexp p)
{
#ifdef DEBUG
    std::cout << std::hex << (long)p << " markNode    " << nodeTypes[nodeType(p)] << std::endl;
#endif
    *(long*)&p->cdr |= MARK;
    ++marked;
}

/*
 * mark the node, identify it as a Chunk
 */
static void markChunk(sexp p)
{
    *(long*)&p->cdr |= CHUNK;
#ifdef DEBUG
    std::cout << std::hex << (long)p << " markChunk   " << nodeTypes[nodeType(p)] << std::endl;
#endif
    *(long*)&p->cdr |= MARK;
    ++marked;
}

/*
 * unmark the node
 */
static void unmarkNode(sexp p)
{
    *(long*)&p->cdr &= ~MARK;
#ifdef DEBUG
    std::cout << std::hex << (long)p << " unmarkNode  " << nodeTypes[nodeType(p)] << std::endl;
#endif
    --marked;
}

/*
 * unmark the Chunk.  It loses its tag, but Chunks are reachable from their Atom
 */
static void unmarkChunk(sexp p)
{
    *(long*)&p->cdr &= ~MARK;
#ifdef DEBUG
    std::cout << std::hex << (long)p << " unmarkChunk " << nodeTypes[nodeType(p)] << std::endl;
#endif
    *(long*)&p->cdr &= ~CHUNK;
    --marked;
}

/*
 * mark a list of Chunks
 */
void markChunks(Chunk *q)
{
    Chunk *r;
    while (q)
    {
        r = q->cdr;
        markChunk((sexp)q);
        q = r;
    }
}

/*
 * visit objects reachable from p, setting their MARK bit
 */
void mark(sexp p)
{
    if (!p || isMarked(p))
        return;
    if (isAtom(p))
        markChunks(((Atom*)p)->chunks);
    else if (isString(p))
        markChunks(((String*)p)->chunks);
    else if (isCons(p))
    {
        mark(p->car);
        mark(p->cdr);
    }
    markNode(p);
}

/*
 * mark all reachable objects
 *
 * sweep all storage, putting unmarked objects on the freelist
 */
void gc(void)
{
#ifdef GC
    int werefree = 0;
    for (sexp p = freelist; p; p = p->cdr)
        ++werefree;

    std::cout << "gc: allocated: " << allocated << " free: " << werefree;

    marked = 0;
    mark(atoms);
    mark(global);
    mark(protect);
    std::cout << " marked: " << std::dec << marked << " expected garbage: " << werefree+allocated-marked;

    freelist = 0;
    int reclaimed = 0;
    for (sexp p = block; p < block+MAX; ++p)
    {
        if (!isMarked(p))
        {
            p->car = 0;
            p->cdr = freelist;
            freelist = p;
            ++reclaimed;
        } else if (isChunk(p))
            unmarkChunk(p);
        else
            unmarkNode(p);
    }
    std::cout << " reclaimed: " << reclaimed << std::endl;
    allocated -= reclaimed-werefree;

    if (!freelist)
    {
        std::cout << "storage exhausted\n";
        exit(0);
    }
#else
    std::cout << "no gc\n";
    exit(0);
#endif
}

/*
 * allocate a node from the freelist
 */
sexp node(void)
{
    if (!freelist)
        gc();

    ++allocated;
    Cons* p = protect = freelist;
    freelist = freelist->cdr;
    p->cdr = 0;
    return p;
}

sexp cons(sexp car, sexp cdr)
{
    sexp p = node();
    p->car = car;
    p->cdr = cdr;
    return p;
}

sexp car(sexp p)
{
    if (!p || !isCons(p))
    {
        std::cout << "longjmp! car of " << nodeTypes[nodeType(p)] << ' '; print(std::cout, p); std::cout << std::endl;
        longjmp(the_jmpbuf, 1);
    }
    return p->car;
}

sexp cdr(sexp p)
{
    if (!p || !isCons(p))
    {
        std::cout << "longjmp! cdr of " << nodeTypes[nodeType(p)] << ' '; print(std::cout, p); std::cout << std::endl;
        longjmp(the_jmpbuf, 1);
    }
    return p->cdr;
}

/*
 * construct an integer
 */
sexp fixnum(long number)
{
    Fixnum* p = (Fixnum*)node();
    p->tag = NUMBER;
    p->fixnum = number;
    return (sexp)p;
}

long asFixnum(sexp p)
{
    return ((Fixnum*)p)->fixnum;
}

/*
 * arithmetic comparisons
 */
sexp lt(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) < asFixnum(y) ? t : 0;
    return 0;
}

sexp le(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) <= asFixnum(y) ? t : 0;
    return 0;
}

sexp ge(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) >= asFixnum(y) ? t : 0;
    return 0;
}

sexp gt(sexp x, sexp y)
{
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) > asFixnum(y) ? t : 0;
    return 0;
}

/*
 * these arithmetic functions take a list of arguments
 */
sexp addfunc(sexp args)
{
    long result = 0;
    for (sexp p = args; p; p = p->cdr)
    {
        sexp q = p->car;
        if (!isFixnum(q))
            return 0;
        result += asFixnum(q);
    }
    return fixnum(result);
}

sexp subfunc(sexp args)
{
    long result = 0;
    for (sexp p = args; p; p = p->cdr)
    {
        sexp q = p->car;
        if (!isFixnum(q))
            return 0;
        long n = asFixnum(q);
        result += (args == p && p->cdr) ? n : -n;
    }
    return fixnum(result);
}

sexp mulfunc(sexp args)
{
    long result = 1;
    for (sexp p = args; p; p = p->cdr)
    {
        sexp q = p->car;
        if (!isFixnum(q))
            return 0;
        result *= asFixnum(q);
    }
    return fixnum(result);
}

sexp divfunc(sexp args)
{
    long result = 1;
    for (sexp p = args; p; p = p->cdr)
    {
        sexp q = p->car;
        if (!isFixnum(q))
            return 0;
        if (args == p)
            result *= asFixnum(q);
        else
            result /= asFixnum(q);
    }
    return fixnum(result);
}

sexp modfunc(sexp args)
{
    long result = 1;
    for (sexp p = args; p; p = p->cdr)
    {
        sexp q = p->car;
        if (!isFixnum(q))
            return 0;
        if (args == p)
            result *= asFixnum(q);
        else
            result %= asFixnum(q);
    }
    return fixnum(result);
}

sexp maxfunc(sexp args)
{
    long result = LONG_MIN;
    for (sexp p = args; p; p = p->cdr)
    {
        sexp q = p->car;
        if (!isFixnum(q))
            return 0;
        long x = asFixnum(q);
        if (x > result)
            result = x;
    }
    return fixnum(result);
}

sexp minfunc(sexp args)
{
    long result = LONG_MAX;
    for (sexp p = args; p; p = p->cdr)
    {
        sexp q = p->car;
        if (!isFixnum(q))
            return 0;
        long x = asFixnum(q);
        if (x < result)
            result = x;
    }
    return fixnum(result);
}

/*
 * logical negation
 */
sexp isnot(sexp x)
{
    return x ? 0 : t;
}

/*
 * read and evaluate s-expressions from a file
 */
sexp load(sexp x)
{
    if (isString(x)) {
        int length = 0;
        for (Chunk* p = ((String*)x)->chunks; p; p = p->cdr)
        {
            int i = 0;
            while (i < sizeof(void*) && p->text[i])
                ++i;
            length += i;
        }
        char *name = (char*) alloca(length+1);
        int j = 0;
        for (Chunk* p = ((String*)x)->chunks; p; p = p->cdr)
            for (int i = 0; i < sizeof(void*) && p->text[i]; name[j++] = p->text[i++]) {}
        name[j++] = 0;
        std::ifstream fin(name);
        while (fin.good())
        {
            sexp input = read(fin);
            if (!input)
                break;
            eval(input, global);
        }
        fin.close();
    } else
        return 0;
}

/*
 * print a sequence of s-expressions, separated by spaces
 */
sexp printfunc(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
    {
        print(std::cout, p->car);
        if (p->cdr)
            std::cout << ' ';
    }
    return voida;
}


/*
 * print a sequence of s-expressions, separated by spaces, then a newline
 */
sexp printlnfunc(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
    {
        print(std::cout, p->car);
        if (p->cdr)
            std::cout << ' ';
    }
    std::cout << std::endl;
    return voida;
}

/*
 * construct a linked list of chunks of sizeof(void*) characters
 */
Chunk* chunk(const char *t)
{
    Chunk* p = (Chunk*)node();
    Chunk *q = p;
    int i = 0;
    for (;;)
    {
        char c = *t++;
        q->text[i++] = c;
        if (!c)
            return p;
        if (i >= sizeof(void*))
        {
            i = 0;
            Chunk* r = (Chunk*)node();
            q->cdr = r;
            protect = (sexp)p;
            q = r;
        }
    }
}

/*
 * construct an Atom
 */
sexp atom(Chunk* chunks)
{
    Atom* p = (Atom*)node();
    p->tag = ATOM;
    p->chunks = chunks;
    return (sexp)p;
}

/*
 * construct a String
 */
sexp string(Chunk* chunks)
{
    String* p = (String*)node();
    p->tag = STRING;
    p->chunks = chunks;
    return (sexp)p;
}

/*
 * print a list
 */
std::ostream& printList(std::ostream& output, sexp expr)
{
    output.put('(');
    while (expr) {
        print(output, expr->car);
        if (expr->cdr) {
            if (isCons(expr->cdr)) {
                output.put(' ');
                expr = expr->cdr;
            } else {
                output.write(" . ", 3);
                print(output, expr->cdr);
                expr = 0;
            }
        } else
            expr = expr->cdr;
    }
    output.put(')');
    return output;
}

std::ostream& printChunks(std::ostream& output, Chunk* p)
{
    while (p)
    {
        for (int i = 0; i < sizeof(void*); ++i)
        {
            char c = p->text[i];
            if (!c)
                break;
            output.put(c);
        }
        p = p->cdr;
    }
    return output;
}

/*
 * print an s-expression
 */
std::ostream& print(std::ostream& output, sexp expr)
{
    if (!expr)
        output.write("#f", 2);
    else if (isCons(expr))
        printList(output, expr);
    else if (isString(expr)) {
        output.put('"');
        printChunks(output, ((String*)expr)->chunks);
        output.put('"');
    } else if (isAtom(expr))
        printChunks(output, ((Atom*)expr)->chunks);
    else if (isFixnum(expr))
        std::cout << ((Fixnum*)expr)->fixnum;
    else if (isFunct(expr))
        std::cout << "#function@" << std::hex << (long)((Funct*)expr)->funcp << std::dec;
    else if (isForm(expr))
        std::cout << "#form@" << std::hex << (long)((Form*)expr)->formp << std::dec;
    return output;
}

/*
 * match chunks, comparing atoms for equality
 */
bool match(Chunk *p, Chunk *q)
{
    for (;;)
    {
        if (p == q)
            return true;
        if (!p || !q)
            return false;
        for (int i = 0; i < sizeof(void*); ++i)
            if (p->text[i] != q->text[i])
                return false;
        p = p->cdr;
        q = q->cdr;
    }
}

/*
 * comparison for equality
 */
sexp eqv(sexp x, sexp y)
{
    if (x == y)
        return t;
    if (isAtom(x) && isAtom(y))
        return x == y ? t : 0;
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) == asFixnum(y) ? t : 0;
    if (isCons(x) && isCons(y))
        return eqv(x->car, y->car) && eqv(x->cdr, y->cdr) ? t : 0;
    if (isString(x) && isString(y))
        return match(((String*)x)->chunks, ((String*)y)->chunks) ? t : 0;
    return 0;
}

/*
 * atoms are made unique so they can be compared by address
 */
sexp intern(sexp p)
{
    Atom* a = (Atom*)p;
    for (sexp q = atoms; q; q = q->cdr)
    {
        Atom* b = (Atom*)(q->car);
        if (match(a->chunks, b->chunks))
        {
            // a is garbage
            return (sexp)b;
        }
    }
    atoms = cons(p, atoms);
    return p;
}

/*
 * the global symbol table is just a linked list
 */
sexp get(sexp p, sexp r)
{
    for (sexp q = r; q; q = q->cdr)
        if (p == q->car->car)
            return q->car->cdr;
    return 0;
}

/*
 * find an existing value or create a new binding
 */
sexp set(sexp p, sexp r)
{
    sexp s = 0;
    for (sexp q = global; q; q = q->cdr)
        if (p == q->car->car)
        {
            s = q->car->cdr;
            q->car->cdr = r;
            return s;
        }
    global = cons(cons(p, r), global);
    return 0;
}

/*
 * evaluate a list of actual arguments in the environment env
 */
sexp evlis(sexp p, sexp env)
{
    if (!p)
        return 0;
    return cons(eval(p->car, env), evlis(p->cdr, env));
}

/*
 * bind formal arguments to actual arguments
 */
sexp assoc(sexp formals, sexp actuals, sexp env)
{
    if (actuals)
        return cons(cons(formals->car, actuals->car),
                    assoc(formals->cdr, actuals->cdr, env));
    else
        return env;
}

/*
 * special form returns the global environment
 */
sexp globalform(sexp expr, sexp env)
{
    return env;
}

/*
 * (begin exp ...) returns evaluation of the last exp
 */
sexp beginform(sexp expr, sexp env)
{
    sexp v = 0;
    for (sexp p = expr->cdr; p; p = p->cdr)
        v = eval(p->car, env);
    return v;
}

/*
 * (while predicate exp..) returns evaluation of the last exp
 */
sexp whileform(sexp expr, sexp env)
{
    sexp v = 0;
    expr = expr->cdr;
    while (eval(expr->car, env))
        for (sexp p = expr->cdr; p; p = p->cdr)
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
sexp condform(sexp expr, sexp env)
{
    for (sexp p = expr->cdr; p; p = p->cdr)
        if (elsea == p->car->car || eval(p->car->car, env))
            return eval(p->car->cdr->car, env);
    return 0;
}

/*
 * rewrite
 *      (define (mycar x) (car x))
 * as
 *      (define mycar (lambda (x) (car x)))
 * 
 */
sexp defineform(sexp p, sexp env)
{
    if (isCons(p->cdr->car))
    {
        sexp v = cons(lambda, cons(p->cdr->car->cdr, p->cdr->cdr));
        for (sexp q = global; q; q = q->cdr)
            if (p->cdr->car->car == q->car->car)
            {
                q->car->cdr = v;
                return p->cdr->car->car;
            }

        global = cons(cons(p->cdr->car->car, v), global);
        return p->cdr->car->car;
    } else {
        for (sexp q = global; q; q = q->cdr)
            if (p->cdr->car == q->car->car)
            {
                q->car->cdr = p->cdr->cdr->car;
                return p->cdr->car;
            }

        global = cons(cons(p->cdr->car, p->cdr->cdr->car), global);
        return p->cdr->car;
    }
}

/*
 * return the atoms list.  any args are unused
 */
sexp atomsfunc(sexp args)
{
    return atoms;
}

/*
 * 'x => (quote x) => x
 */
sexp quoteform(sexp expr, sexp env)
{
    return expr->cdr->car;
}

/*
 * (read) reads a sexpr and returns it, args are ignored
 */
sexp readform(sexp expr, sexp env)
{
    return read(std::cin);
}

/*
 * (if predicate consequent alternative)
 *
 * if the predicate evaluates non-null
 *    then evaluate the consequent
 *    else evaluate the alternative
 */
sexp ifform(sexp expr, sexp env)
{
    return eval(expr->cdr->car, env) ?
      eval(expr->cdr->cdr->car, env) : eval(expr->cdr->cdr->cdr->car, env);
}

/*
 * (set name value) creates a new binding or alters an old one
 */
sexp setform(sexp expr, sexp env)
{
    return set(expr->cdr->car, eval(expr->cdr->cdr->car, env));
}

/*
 * lambda implements user-defined functions
 */
sexp lambdaform(sexp expr, sexp env)
{
    if (!isCons(expr->car))
        expr = cons(eval(expr->car, env), expr->cdr);
    return eval(expr->car->cdr->cdr->car,
                assoc(expr->car->cdr->car,
                      evlis(expr->cdr, env), env));
}

/*
 * associate variables with values, used by letform
 */
sexp augment(sexp a, sexp env)
{
    if (a)
        return cons(cons(a->car->car, eval(a->car->cdr->car, env)), augment(a->cdr, env));
    else
        return env;
}

/*
 * (let ((var value) ..) expr)
 */
sexp letform(sexp expr, sexp env)
{
    return eval(expr->cdr->cdr->car, augment(expr->cdr->car, env));
}

/*
 * malformed constructs will fail without grace
 */
sexp eval(sexp p, sexp env)
{
    if (!p)
        return 0;
    if (isAtom(p))
        return get(p, env);
    if (isFixnum(p))
        return p;
    if (isString(p))
        return p;
    if (isCons(p) && lambda == p->car)
        return p;
    sexp q = eval(p->car, env);
    if (isCons(q) && lambda == q->car)
        return lambdaform(p, env);
    if (isForm(q))
        return (*((Form*)q)->formp)(p, env);
    if (isFunct(q))
    {
        if (0 == numArgs(q))
            return (*(Varargp)((Funct*)q)->funcp)(evlis(p->cdr, env));
        if (1 == numArgs(q))
            return (*(Oneargp)((Funct*)q)->funcp)(eval(p->cdr->car, env));
        if (2 == numArgs(q))
            return (*(Twoargp)((Funct*)q)->funcp)(eval(p->cdr->car, env), eval(p->cdr->cdr->car, env));
        return 0;
    }
    return p;
}

/*
 * an integer is read from the input stream
 */
long readNumber(std::istream& input)
{
    long number = 0;
    for (;;)
    {
        char c = input.get();
        if ('0' <= c && c <= '9')
            number = 10 * number + (c - '0'); 
        else
            break;
    }
    input.unget();
    return number;
}

/*
 * read Chunks terminated by some character
 */
Chunk *readChunks(std::istream& input, const char *ends)
{
    char c = input.get();

    int i = 0;
    Chunk *q = chunk("");
    Chunk *p = q;

    for (;;)
    {
        q->text[i++] = c;
        c = input.get();

        if (strchr(ends, c))
            return p;

        if (i == sizeof(void*)) {
            q->cdr = chunk("");
            q = q->cdr;
            i = 0;
        }
    }
}

/*
 * read an atom, number or string from the input stream
 */
sexp scan(std::istream& input)
{
    char c = input.get();
    while (strchr(" \t\r\n", c))
        c = input.get();
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

    // signed integers
    if ('-' == c) {
        c = input.get();
        if ('0' <= c && c <= '9')
            return fixnum(-readNumber(input));
        input.unget();
        return minus;
    } else if ('0' <= c && c <= '9') {
        input.unget();
        return fixnum(readNumber(input));
    }

    if ('"' == c)
        return string(readChunks(input, "\""));

    input.unget();
    sexp r = intern(atom(readChunks(input, "( )\t\r\n")));
    input.unget();
    return r;
}

/*
 * finish reading a list
 */
sexp readTail(std::istream& input)
{
    sexp q = read(input);
    if (rparen == q)
        return 0;
    sexp p = cons(q, readTail(input));
    return p;
}

/*
 * read an s-expression
 */
sexp read(std::istream& input)
{
    sexp p = scan(input);
    if (nil == p)
        return 0;
    if (lparen == p)
        return readTail(input);
    if (qchar == p)
        return cons(quote, cons(read(input), 0));
    return p;
}

sexp intern_atom_chunk(const char *s)
{
    return intern(atom(chunk(s)));
}

void set_form(sexp name, Formp f)
{
    Form* p = (Form*)node();
    p->tag = FORM;
    p->formp = f;
    set(name, (sexp)p);
}

void set_funct(sexp name, int arity, void* f)
{
    Funct* p = (Funct*)node();
    p->tag = (arity << 4) | FUNCT;
    p->funcp = f;
    set(name, (sexp)p);
}

#ifdef SIGNALS
void signal_handler(int sig)
{
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

        std::cout << std::dec << "#" << ++n
                  << " 0x" << std::hex << static_cast<uintptr_t>(ip)
                  << " sp=0x" << static_cast<uintptr_t>(sp) << " " << name
                  << " + 0x" << static_cast<uintptr_t>(off) << std::endl;

        if ( name != symbol )
          free(name);
    }
    exit(0);
}
#endif

int main(int argc, char **argv, char **envp)
{
#ifdef SIGNALS
    signal(SIGSEGV, signal_handler);
    signal(SIGINT , signal_handler);
#endif

    // allocate all the nodes we will ever have
    block = (sexp)malloc(MAX*sizeof(Cons));
    for (int i = MAX; --i >= 0; )
    {
        block[i].car = 0;
        block[i].cdr = freelist;
        freelist = block+i;
    }

    // set up all predefined atoms

    atomsa  = intern_atom_chunk("atoms");
    begin   = intern_atom_chunk("begin");
    cara	= intern_atom_chunk("car");
    cdra	= intern_atom_chunk("cdr");
    cond    = intern_atom_chunk("cond");
    consa   = intern_atom_chunk("cons");
    define  = intern_atom_chunk("define");
    divide  = intern_atom_chunk("/");
    dot     = intern_atom_chunk(".");
    elsea   = intern_atom_chunk("else");
    eqva    = intern_atom_chunk("eqv?");
    gea     = intern_atom_chunk(">=");
    globals = intern_atom_chunk("globals");
    gta     = intern_atom_chunk(">");
    ifa     = intern_atom_chunk("if");
    lambda  = intern_atom_chunk("lambda");
    lea     = intern_atom_chunk("<=");
    let     = intern_atom_chunk("let");
    loada   = intern_atom_chunk("load");
    lparen  = intern_atom_chunk("(");
    lta     = intern_atom_chunk("<");
    max     = intern_atom_chunk("max");
    min     = intern_atom_chunk("min");
    minus   = intern_atom_chunk("-");
    modulo  = intern_atom_chunk("%");
    nil     = intern_atom_chunk("#f");
    nota    = intern_atom_chunk("not");
    plus    = intern_atom_chunk("+");
    printa  = intern_atom_chunk("print");
    println = intern_atom_chunk("println");
    qchar   = intern_atom_chunk("'");
    quote   = intern_atom_chunk("quote");
    reada   = intern_atom_chunk("read");
    rparen  = intern_atom_chunk(")");
    seta    = intern_atom_chunk("set");
    times   = intern_atom_chunk("*");
    t       = intern_atom_chunk("#t");
    voida   = intern_atom_chunk("");
    whilea  = intern_atom_chunk("while");

    // set the definitions (special forms)
    set_form(begin,   beginform);
    set_form(cond,    condform);
    set_form(define,  defineform);
    set_form(globals, globalform);
    set_form(ifa,     ifform);
    set_form(lambda,  lambdaform);
    set_form(let,     letform);
    set_form(quote,   quoteform);
    set_form(reada,   readform);
    set_form(seta,    setform);
    set_form(whilea,  whileform);

    // set the definitions (functions)
    set_funct(atomsa,  0, (void*)atomsfunc);
    set_funct(cara,    1, (void*)car);
    set_funct(cdra,    1, (void*)cdr);
    set_funct(consa,   2, (void*)cons);
    set_funct(divide,  0, (void*)divfunc);
    set_funct(eqva,    2, (void*)eqv);
    set_funct(gea,     2, (void*)ge);
    set_funct(gta,     2, (void*)gt);
    set_funct(lea,     2, (void*)le);
    set_funct(loada,   1, (void*)load);
    set_funct(lta,     2, (void*)lt);
    set_funct(max,     0, (void*)maxfunc);
    set_funct(min,     0, (void*)minfunc);
    set_funct(minus,   0, (void*)subfunc);
    set_funct(modulo,  0, (void*)modfunc);
    set_funct(nota,    1, (void*)isnot);
    set_funct(plus,    0, (void*)addfunc);
    set_funct(printa,  0, (void*)printfunc);
    set_funct(println, 0, (void*)printlnfunc);
    set_funct(times,   0, (void*)mulfunc);

    load(string(chunk("init.l")));

    setjmp(the_jmpbuf);

    // read evaluate print ...
    while (std::cin.good())
    {
#ifdef VOLUNTARY_GC
        gc();
#endif
        sexp e = read(std::cin);
        if (!e)
            break;
        sexp v = eval(e, global);
        if (voida != v)
            print(std::cout, eval(e, global)) << std::endl;
    }
    return 0;
}

