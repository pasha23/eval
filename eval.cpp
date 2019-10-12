/*
 * this is kind of a lisp interpreter for my own amusement
 * not at all standards compliant or industrial strength
 * dynamically scoped, without tail call optimization
 *
 * there are gc issues at present
 * circular lists cannot be printed
 * syntactic atoms need meta-syntax when printed
 * 
 * Robert Kelley October 2019
 */
#include <string>
#include <iostream>
#include <cstdlib>

#define GC
#undef  DEBUG
#define MAX 4096

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
typedef sexp (*Funcp)(sexp);
typedef sexp (*Formp)(sexp, sexp);
typedef sexp (*Oneargp)(sexp);
typedef sexp (*Twoargp)(sexp, sexp);

/*
 * setting up union declarations isn't all that fun
 */
struct Cons   { Cons*  cdr; Cons*   car;                 };
struct Chunk  { Chunk* cdr; char    text[sizeof(void*)]; };
struct Atom   { Tag    tag; Chunk*  chunks;              };
struct Fixnum { Tag    tag; long    fixnum;              };
struct Func   { Tag    tag; Funcp   funcp;               };
struct Onearg { Tag    tag; Oneargp funcp;               };
struct Twoarg { Tag    tag; Twoargp funcp;               };
struct Form   { Tag    tag; Formp   formp;               };

extern sexp eval(sexp p, sexp env);
extern sexp evlis(sexp p, sexp env);
extern std::ostream& print(std::ostream& output, sexp p);
extern sexp set(sexp p, sexp r);
extern sexp assoc(sexp formals, sexp actuals, sexp env);
extern sexp read(std::istream& input);
extern sexp scan(std::istream& input);

// these are the built-in atoms

sexp caaaara, caaadra, caaara, caadara, caaddra, caadra, caara, cadaara;
sexp cadadra, cadara, caddara, cadddra, caddra, cadra, cara, cdaaara;
sexp cdaadra, cdaara, cdadara, cdaddra, cdadra, cdara, cddaara, cddadra;
sexp cddara, cdddara, cddddra, cdddra, cddra, cdra, consa, divide, dot;
sexp atomsa, exp, globals, ifa, lambda, lparen, minus, nil, plus, qchar;
sexp quote, rparen, seta, t, times, val;

int  marked = 0;            // how many nodes were marked during gc
sexp atoms = 0;             // all atoms are linked in a list
sexp global = 0;            // this is the global symbol table (a list)
sexp protect = 0;           // protects otherwise unreachable objects from gc
sexp freelist = 0;          // available nodes are linked in a list
int allocated = 0;          // how many nodes have been allocated
unsigned long lo, hi;       // extent of the node space for sweep phase of gc

static inline int  nodeType(sexp p)       { return 15 & (long)p->cdr; }
static inline bool isMarked(const sexp p) { return p && MARK & (long)p->cdr; }
static inline bool isCons(const sexp p)   { return p && CONS == (7 & (long)p->cdr); }
static inline bool isChunk(const sexp p)  { return p && CHUNK == (7 & (long)p->cdr); }
static inline bool isAtom(const sexp p)   { return p && ATOM == (7 & (long)p->cdr); }
static inline bool isFunc(const sexp p)   { return p && VARARG == (7 & (long)p->cdr); }
static inline bool isOnearg(const sexp p) { return p && ONEARG == (7 & (long)p->cdr); }
static inline bool isTwoarg(const sexp p) { return p && TWOARG == (7 & (long)p->cdr); }
static inline bool isForm(const sexp p)   { return p && FORM == (7 & (long)p->cdr); }
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
    if (0 == p || isMarked(p))
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

void gc(void)
{
    std::cout << "gc entered, allocated: " << allocated << std::endl;

    if (0 == hi) {
        // allocate all the nodes we will ever have
        sexp block = (sexp)calloc(MAX, sizeof(Cons));
        for (int i = MAX; --i >= 0; )
        {
            block[i].cdr = freelist;
            freelist = block+i;
        }
        lo = (unsigned long)block;
        hi = (unsigned long)(block+MAX);
    } else {
#ifndef GC
        std::cout << "no gc\n";
        exit(0);
#endif
        // mark every reachable node
        marked = 0;
        mark(atoms);
        mark(global);
        mark(protect);
        std::cout << "marked: " << std::dec << marked << " expected garbage: " << allocated-marked << std::endl;

        // return all unmarked nodes to the freelist
        int reclaimed = 0;
        //std::cout << "lo=" << std::hex << lo << " hi=" << std::hex << hi << std::dec << std::endl;
        for (unsigned long pp = lo; pp < hi; pp += sizeof(Cons))
        {
            sexp p = (sexp)pp;
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
        std::cout << "gc complete " << std::dec << "remaining marks: " << marked << " reclaimed: " << reclaimed << std::endl;
        allocated -= reclaimed;
    }
}

/*
 * allocate a node from the freelist
 */
sexp node(void)
{
    if (0 == freelist)
        gc();

    if (0 == freelist)
    {
        std::cout << "storage exhausted\n";
        exit(0);
    }

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

sexp car(sexp p)    { return p->car; }
sexp cdr(sexp p)    { return p->cdr; }
sexp caar(sexp x)   { return x->car->car; }
sexp cadr(sexp x)   { return x->cdr->car; }
sexp cdar(sexp x)   { return x->car->cdr; }
sexp cddr(sexp x)   { return x->cdr->cdr; }
sexp caaar(sexp x)  { return x->car->car->car; }
sexp caadr(sexp x)  { return x->cdr->car->car; }
sexp cadar(sexp x)  { return x->car->cdr->car; }
sexp caddr(sexp x)  { return x->cdr->cdr->car; }
sexp cdaar(sexp x)  { return x->car->car->cdr; }
sexp cdadr(sexp x)  { return x->cdr->car->cdr; }
sexp cddar(sexp x)  { return x->car->cdr->cdr; }
sexp cdddr(sexp x)  { return x->cdr->cdr->cdr; }
sexp caaaar(sexp x) { return x->car->car->car->car; }
sexp caaadr(sexp x) { return x->cdr->car->car->car; }
sexp caadar(sexp x) { return x->car->cdr->car->car; }
sexp caaddr(sexp x) { return x->cdr->cdr->car->car; }
sexp cadaar(sexp x) { return x->car->car->cdr->car; }
sexp cadadr(sexp x) { return x->cdr->car->cdr->car; }
sexp caddar(sexp x) { return x->car->cdr->cdr->car; }
sexp cadddr(sexp x) { return x->cdr->cdr->cdr->car; }
sexp cdaaar(sexp x) { return x->car->car->car->cdr; }
sexp cdaadr(sexp x) { return x->cdr->car->car->cdr; }
sexp cdadar(sexp x) { return x->car->cdr->car->cdr; }
sexp cdaddr(sexp x) { return x->cdr->cdr->car->cdr; }
sexp cddaar(sexp x) { return x->car->car->cdr->cdr; }
sexp cddadr(sexp x) { return x->cdr->car->cdr->cdr; }
sexp cdddar(sexp x) { return x->car->cdr->cdr->cdr; }
sexp cddddr(sexp x) { return x->cdr->cdr->cdr->cdr; }

/*
 * create a linked list of chunks of sizeof(void*) characters
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
        if (0 == c)
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

sexp atom(Chunk* chunks)
{
    Atom* p = (Atom*)node();
    p->tag = ATOM;
    p->chunks = chunks;
    return (sexp)p;
}

sexp vararg(Funcp funcp)
{
    Func* p = (Func*)node();
    p->tag = VARARG;
    p->funcp = funcp;
    return (sexp)p;
}

sexp onearg(Oneargp funcp)
{
    Onearg* p = (Onearg*)node();
    p->tag = ONEARG;
    p->funcp = funcp;
    return (sexp)p;
}

sexp twoarg(Twoargp funcp)
{
    Twoarg* p = (Twoarg*)node();
    p->tag = TWOARG;
    p->funcp = funcp;
    return (sexp)p;
}

sexp form(Formp formp)
{
    Form* p = (Form*)node();
    p->tag = FORM;
    p->formp = formp;
    return (sexp)p;
}

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

std::ostream& print(std::ostream& output, Chunk *chunk)
{
    do
        for (int i = 0; i < sizeof(void*); ++i)
        {
            char c = chunk->text[i];
            if (0 == c)
                break;
            output.put(c);
        }
    while (chunk = chunk->cdr);
    return output;
}

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

std::ostream& print(std::ostream& output, sexp expr)
{
    if (0 == expr)
        output.write("#f", 2);
    else if (isCons(expr))
        printList(output, expr);
    else if (isAtom(expr))
        print(output, (Chunk*)expr->car);
    else if (isFixnum(expr))
        std::cout << ((Fixnum*)expr)->fixnum;
    else if (isFunc(expr))
        std::cout << "#varargs@" << std::hex << (long)((Func*)expr)->funcp << std::dec;
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
        if (0 == p || 0 == q)
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
    if (0 == p)
        return 0;
    return cons(eval(p->car, env), evlis(p->cdr, env));
}

/*
 * this is used to bind formal arguments to actual arguments
 */
sexp assoc(sexp formals, sexp actuals, sexp env)
{
    if (0 == actuals)
        return env;
    return cons(cons(formals->car, actuals->car), assoc(formals->cdr, actuals->cdr, env));
}

/*
 * special form returns the global environment
 */
sexp globalform(sexp expr, sexp env)
{
    return env;
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
 * (if predicate consequent alternative)
 *
 * if the predicate is non-null then evaluate the consequent else evaluate the alternative
 */
sexp ifform(sexp expr, sexp env)
{
    return eval(expr->cdr->car, env) ? eval(expr->cdr->cdr->car, env) : eval(expr->cdr->cdr->cdr->car, env);
}

/*
 * (set name value) creates a new binding or alters an old one
 */
sexp setform(sexp expr, sexp env)
{
    return set(expr->cdr->car, eval(expr->cdr->cdr->car, env));
}

/*
 * lambda can be used to define new functions
 */
sexp lambdaform(sexp expr, sexp env)
{
    if (!isCons(expr->car))
        expr = cons(eval(expr->car, env), expr->cdr);
    return eval(expr->car->cdr->cdr->car, assoc(expr->car->cdr->car, evlis(expr->cdr, env), env));
}

/*
 * this evaluator could be improved
 *
 * malformed constructs will fail unpredictably
 */
sexp eval(sexp p, sexp env)
{
    if (0 == p)
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
    if (isFunc(q))
        return (*((Func*)q)->funcp)(evlis(p->cdr, env));
    if (isOnearg(q))
        return (*((Onearg*)q)->funcp)(eval(p->cdr->car, env));
    if (isTwoarg(q))
        return (*((Twoarg*)q)->funcp)(eval(p->cdr->car, env), eval(p->cdr->cdr->car, env));
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
    while (' ' == c || '\n' == c)
        c = input.get();

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

        if ('(' == c || ')' == c || ' ' == c || '\n' == c) {
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

int main(int argc, char **argv, char **envp)
{
    // set up all predefined atoms

    atomsa  = intern_atom_chunk("atoms");
	caaaara	= intern_atom_chunk("caaaar");
	caaadra	= intern_atom_chunk("caaadr");
	caaara	= intern_atom_chunk("caaar");
	caadara	= intern_atom_chunk("caadar");
	caaddra	= intern_atom_chunk("caaddr");
	caadra	= intern_atom_chunk("caadr");
	caara	= intern_atom_chunk("caar");
	cadaara	= intern_atom_chunk("cadaar");
	cadadra	= intern_atom_chunk("cadadr");
	cadara	= intern_atom_chunk("cadar");
	caddara	= intern_atom_chunk("caddar");
	cadddra	= intern_atom_chunk("cadddr");
	caddra	= intern_atom_chunk("caddr");
	cadra	= intern_atom_chunk("cadr");
	cara	= intern_atom_chunk("car");
	cdaaara	= intern_atom_chunk("cdaaar");
	cdaadra	= intern_atom_chunk("cdaadr");
	cdaara	= intern_atom_chunk("cdaar");
	cdadara	= intern_atom_chunk("cdadar");
	cdaddra	= intern_atom_chunk("cdaddr");
	cdadra	= intern_atom_chunk("cdadr");
	cdara	= intern_atom_chunk("cdar");
	cddaara	= intern_atom_chunk("cddaar");
	cddadra	= intern_atom_chunk("cddadr");
	cddara	= intern_atom_chunk("cddar");
	cdddara	= intern_atom_chunk("cdddar");
	cddddra	= intern_atom_chunk("cddddr");
	cdddra	= intern_atom_chunk("cdddr");
	cddra	= intern_atom_chunk("cddr");
	cdra	= intern_atom_chunk("cdr");
    consa   = intern_atom_chunk("cons");
    divide  = intern_atom_chunk("/");
    dot     = intern_atom_chunk(".");
    exp     = intern_atom_chunk("exp");
    globals = intern_atom_chunk("globals");
    ifa     = intern_atom_chunk("if");
    lambda  = intern_atom_chunk("lambda");
    lparen  = intern_atom_chunk("(");
    minus   = intern_atom_chunk("-");
    nil     = intern_atom_chunk("#f");
    plus    = intern_atom_chunk("+");
    qchar   = intern_atom_chunk("'");
    quote   = intern_atom_chunk("quote");
    rparen  = intern_atom_chunk(")");
    seta    = intern_atom_chunk("set");
    times   = intern_atom_chunk("*");
    t       = intern_atom_chunk("#t");
    val     = intern_atom_chunk("val");

    // set the definitions (special forms)
    set(quote,  	form(quoteform));
    set(ifa,    	form(ifform));
    set(seta,   	form(setform));
    set(lambda, 	form(lambdaform));
    set(globals,	form(globalform));

    // set the definitions (one argument functions)
	set(cara,		onearg(car));
	set(cdra,		onearg(cdr));
	set(caara,		onearg(caar));
	set(cadra,		onearg(cadr));
	set(cdara,		onearg(cdar));
	set(cddra,		onearg(cddr));
	set(caaara,		onearg(caaar));
	set(caadra,		onearg(caadr));
	set(cadara,		onearg(cadar));
	set(caddra,		onearg(caddr));
	set(cdaara,		onearg(cdaar));
	set(cdadra,		onearg(cdadr));
	set(cddara,		onearg(cddar));
	set(cdddra,		onearg(cdddr));
	set(caaaara,	onearg(caaaar));
	set(caaadra,	onearg(caaadr));
	set(caadara,	onearg(caadar));
	set(caaddra,	onearg(caaddr));
	set(cadaara,	onearg(cadaar));
	set(cadadra,	onearg(cadadr));
	set(caddara,	onearg(caddar));
	set(cadddra,	onearg(cadddr));
	set(cdaaara,	onearg(cdaaar));
	set(cdaadra,	onearg(cdaadr));
	set(cdadara,	onearg(cdadar));
	set(cdaddra,	onearg(cdaddr));
	set(cddaara,	onearg(cddaar));
	set(cddadra,	onearg(cddadr));
	set(cdddara,	onearg(cdddar));
	set(cddddra,	onearg(cddddr));

    // set the definitions (two argument functions)
    set(consa,  twoarg(cons));

    // set the definitions (varadic functions)
    set(atomsa, vararg(atomsfunc));
    set(plus,   vararg(addfunc));
    set(minus,  vararg(subfunc));
    set(times,  vararg(mulfunc));
    set(divide, vararg(divfunc));

    // run out of memory for testing
    //for (Cons *p = 0; ; p = cons(0, p)) {}

    // read evaluate print ,,,
    while (!std::cin.eof())
    {
        sexp e = read(std::cin);
        set(exp, e); // gc
        sexp v = eval(e, global);
        set(val, v); // gc
        print(std::cout, v) << std::endl;
    }

    return 0;
}

