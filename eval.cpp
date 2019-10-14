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
#include <iostream>
#include <fstream>
#include <cstring>
#include <cstdlib>

#define GC
#define MAX 4096
#undef  DEBUG
#define VOLUNTARY_GC

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
    VARARG = 5,
    ONEARG = 6,
    TWOARG = 7,
    MARK   = 8
};

const char* nodeTypes[] =
{
	"CONS",
    "CHUNK",
	"ATOM",
	"FORM",
	"NUMBER",
	"VARARG",
	"ONEARG",
	"TWOARG",
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
struct Fixnum { Tag    tag; long    fixnum;              };
struct Vararg { Tag    tag; Varargp funcp;               };
struct Onearg { Tag    tag; Oneargp funcp;               };
struct Twoarg { Tag    tag; Twoargp funcp;               };
struct Form   { Tag    tag; Formp   formp;               };

sexp eval(sexp p, sexp env);
sexp evlis(sexp p, sexp env);
std::ostream& print(std::ostream& output, sexp p);
sexp set(sexp p, sexp r);
sexp assoc(sexp formals, sexp actuals, sexp env);
sexp read(std::istream& input);
sexp scan(std::istream& input);

// these are the built-in atoms

sexp atomsa, begin, cara, cdra, cond, consa, define, divide, dot;
sexp elsea, gea, gta, eqa, globals, ifa, lambda, lparen, lea, loada, lta;
sexp minus, nil, nota, plus, printa, println, qchar, quote, reada, rparen;
sexp seta, t, times, voida;

int  marked = 0;            // how many nodes were marked during gc
sexp atoms = 0;             // all atoms are linked in a list
sexp block = 0;             // all the storage starts here
sexp global = 0;            // this is the global symbol table (a list)
sexp protect = 0;           // protects otherwise unreachable objects from gc
sexp freelist = 0;          // available nodes are linked in a list
int allocated = 0;          // how many nodes have been allocated

static inline int  nodeType(const sexp p) { return 15                & (long)p->cdr;  }
static inline bool isMarked(const sexp p) { return p && MARK         & (long)p->cdr;  }
static inline bool isCons(const sexp p)   { return p && CONS   == (7 & (long)p->cdr); }
static inline bool isChunk(const sexp p)  { return p && CHUNK  == (7 & (long)p->cdr); }
static inline bool isAtom(const sexp p)   { return p && ATOM   == (7 & (long)p->cdr); }
static inline bool isVararg(const sexp p) { return p && VARARG == (7 & (long)p->cdr); }
static inline bool isOnearg(const sexp p) { return p && ONEARG == (7 & (long)p->cdr); }
static inline bool isTwoarg(const sexp p) { return p && TWOARG == (7 & (long)p->cdr); }
static inline bool isForm(const sexp p)   { return p && FORM   == (7 & (long)p->cdr); }
static inline bool isFixnum(const sexp p) { return p && NUMBER == (7 & (long)p->cdr); }

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
 * visit objects reachable from p, setting their MARK bit
 */
void mark(sexp p)
{
    if (!p || isMarked(p))
        return;
    if (isCons(p))
    {
        mark(p->car);
        mark(p->cdr);
    } else if (isAtom(p)) {
        Chunk* r = 0;
        for (Chunk *q = ((Atom*)p)->chunks; q; q = r)
        {
            r = q->cdr;          // we have blown up here p->tag == 11 ??
            markChunk((sexp)q);  // tag the Chunk so sweep will find it
        }
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
#ifndef GC
    std::cout << "no gc\n";
    exit(0);
#endif
    int werefree = 0;
    for (sexp p = freelist; p; p = p->cdr)
        ++werefree;
    std::cout << "gc begins, allocated: " << allocated << " free: " << werefree << std::endl;

    marked = 0;
    mark(atoms);
    mark(global);
    mark(protect);
    std::cout << "marked: " << std::dec << marked << " expected garbage: " << werefree+allocated-marked << std::endl;

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
    std::cout << "gc finished " << std::dec << "remaining marks: " << marked << " reclaimed: " << reclaimed << std::endl;
    allocated -= reclaimed-werefree;
}

/*
 * allocate a node from the freelist
 */
sexp node(void)
{
    ++allocated;
    Cons* p = protect = freelist;
    freelist = freelist->cdr;
    p->cdr = 0;

    if (!freelist)
        gc();

    if (!freelist)
    {
        std::cout << "storage exhausted\n";
        exit(0);
    }

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
    return p->car;
}

sexp cdr(sexp p)
{
    return p->cdr;
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
 * comparison for equality
 */
sexp eq(sexp x, sexp y)
{
    if (x == y)
        return t;
    if (isAtom(x) && isAtom(y))
        return x == y ? t : 0;
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) == asFixnum(y) ? t : 0;
    if (isCons(x) && isCons(y))
        return eq(x->car, y->car) && eq(x->cdr, y->cdr) ? t : 0;
    return 0;
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
    if (isAtom(x))
    {
        // filename must fit in the first chunk
        // since we have not yet implemented strings
        std::ifstream fin(((Atom*)x)->chunks->text);
        while (fin.good())
        {
            sexp input = read(fin);
            if (!input)
                break;
            eval(input, global);
        }
        fin.close();
    }

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
 * construct an atom
 */
sexp atom(Chunk* chunks)
{
    Atom* p = (Atom*)node();
    p->tag = ATOM;
    p->chunks = chunks;
    return (sexp)p;
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

/*
 * these arithmetic functions take a list of arguments
 */
sexp addfunc(sexp args)
{
    long result = 0;
    while (args)
        if (isFixnum(args->car)) {
            result += ((Fixnum*)(args->car))->fixnum;
            args = args->cdr;
        } else
            return 0;
    return fixnum(result);
}

sexp subfunc(sexp args)
{
    if (isFixnum(args->car)) {
        long result = ((Fixnum*)(args->car))->fixnum;
        while (args = args->cdr)
            if (isFixnum(args->car))
                result -= ((Fixnum*)(args->car))->fixnum;
            else
                return 0;
        return fixnum(result);
    }
    return 0;
}

sexp mulfunc(sexp args)
{
    if (isFixnum(args->car)) {
        long result = ((Fixnum*)(args->car))->fixnum;
        while (args = args->cdr)
            if (isFixnum(args->car))
                result *= ((Fixnum*)(args->car))->fixnum;
            else
                return 0;
        return fixnum(result);
    }
    return 0;
}

sexp divfunc(sexp args)
{
    if (isFixnum(args->car)) {
        long result = ((Fixnum*)(args->car))->fixnum;
        while (args = args->cdr)
            if (isFixnum(args->car) && ((Fixnum*)(args->car))->fixnum)
                result /= ((Fixnum*)(args->car))->fixnum;
            else
                return 0;
        return fixnum(result);
    }
    return 0;
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
    else if (isAtom(expr))
        for (Chunk* chunk = ((Atom*)expr)->chunks; chunk; chunk = chunk->cdr)
            for (int i = 0; i < sizeof(void*); ++i)
            {
                char c = chunk->text[i];
                if (!c)
                    break;
                output.put(c);
            }
    else if (isFixnum(expr))
        std::cout << ((Fixnum*)expr)->fixnum;
    else if (isVararg(expr))
        std::cout << "#varargs@" << std::hex << (long)((Vararg*)expr)->funcp << std::dec;
    else if (isOnearg(expr))
        std::cout << "#onearg@" << std::hex << (long)((Onearg*)expr)->funcp << std::dec;
    else if (isTwoarg(expr))
        std::cout << "#twoarg@" << std::hex << (long)((Twoarg*)expr)->funcp << std::dec;
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
    if (!actuals)
        return env;
    return cons(cons(formals->car, actuals->car),
                assoc(formals->cdr, actuals->cdr, env));
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
    for (sexp p = expr; p; p = p->cdr)
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
    if (isCons(p) && lambda == p->car)
        return p;
    sexp q = eval(p->car, env);
    if (isCons(q) && lambda == q->car)
        return lambdaform(p, env);
    if (isVararg(q))
        return (*((Vararg*)q)->funcp)(evlis(p->cdr, env));
    if (isOnearg(q))
        return (*((Onearg*)q)->funcp)(eval(p->cdr->car, env));
    if (isTwoarg(q))
        return (*((Twoarg*)q)->funcp)(eval(p->cdr->car, env),
                                      eval(p->cdr->cdr->car, env));
    if (isForm(q))
        return (*((Form*)q)->formp)(p, env);
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
 * read an atom or number from the input stream
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

    int i = 0;
    Chunk *q = chunk("");
    Chunk *p = q;

    for (;;)
    {
        q->text[i++] = c;
        c = input.get();

        if (strchr("( )\t\r\n", c))
        {
            input.unget();
            return intern(atom(p));
        }

        if (i == sizeof(void*)) {
            q->cdr = chunk("");
            q = q->cdr;
            i = 0;
        }
    }
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

void set_onearg(sexp name, Oneargp f)
{
    Onearg* p = (Onearg*)node();
    p->tag = ONEARG;
    p->funcp = f;
    set(name, (sexp)p);
}

void set_twoarg(sexp name, Twoargp f)
{
    Twoarg* p = (Twoarg*)node();
    p->tag = TWOARG;
    p->funcp = f;
    set(name, (sexp)p);
}

void set_vararg(sexp name, Varargp f)
{
    Vararg* p = (Vararg*)node();
    p->tag = VARARG;
    p->funcp = f;
    set(name, (sexp)p);
}

int main(int argc, char **argv, char **envp)
{
    // allocate all the nodes we will ever have
    block = (sexp)calloc(MAX, sizeof(Cons));
    for (int i = MAX; --i >= 0; )
    {
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
    eqa     = intern_atom_chunk("eq");
    gea     = intern_atom_chunk("ge");
    globals = intern_atom_chunk("globals");
    gta     = intern_atom_chunk("gt");
    ifa     = intern_atom_chunk("if");
    lambda  = intern_atom_chunk("lambda");
    lea     = intern_atom_chunk("le");
    loada   = intern_atom_chunk("load");
    lparen  = intern_atom_chunk("(");
    lta     = intern_atom_chunk("lt");
    minus   = intern_atom_chunk("-");
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

    // set the definitions (special forms)
    set_form(begin,   beginform);
    set_form(cond,    condform);
    set_form(define,  defineform);
    set_form(globals, globalform);
    set_form(ifa,     ifform);
    set_form(lambda,  lambdaform);
    set_form(quote,   quoteform);
    set_form(reada,   readform);
    set_form(seta,    setform);

    // set the definitions (one argument functions)
    set_onearg(cara,   car);
    set_onearg(cdra,   cdr);
    set_onearg(loada,  load);
    set_onearg(nota,   isnot);

    // set the definitions (two argument functions)
    set_twoarg(consa, cons);
    set_twoarg(eqa,   eq);
    set_twoarg(gea,   ge);
    set_twoarg(gta,   gt);
    set_twoarg(lea,   le);
    set_twoarg(lta,   lt);

    // set the definitions (varadic functions)
    set_vararg(atomsa,  atomsfunc);
    set_vararg(plus,    addfunc);
    set_vararg(minus,   subfunc);
    set_vararg(times,   mulfunc);
    set_vararg(divide,  divfunc);
    set_vararg(printa,  printfunc);
    set_vararg(println, printlnfunc);

    load(intern_atom_chunk("init.l"));

    // read evaluate print ...
    while (std::cin.good())
    {
        sexp e = read(std::cin);
        if (!e)
            break;
        sexp v = eval(e, global);
        if (voida != v)
            print(std::cout, eval(e, global)) << std::endl;
#ifdef VOLUNTARY_GC
        gc();
#endif
    }
    return 0;
}

