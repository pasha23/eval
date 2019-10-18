/*
 * this is kind of a lisp interpreter for my own amusement
 * not at all standards compliant or industrial strength
 * dynamically scoped, without tail call optimization
 *
 * there are gc issues at present
 * circular lists cannot be displayed
 * syntactic atoms need meta-syntax when displayed
 * quasiquote
 * 
 * Robert Kelley October 2019
 */
#define UNW_LOCAL_ONLY
#include <libunwind.h>
#include <cxxabi.h>
#include <csetjmp>
#include <cstring>
#include <cstdlib>
#include <csignal>
#include <climits>
#include <cstdio>

#define GC
#define MAX 4096
#undef  DEBUG
#define VOLUNTARY_GC
#undef  SIGNALS

/*
 * storage is managed as a freelist of cells, each potentially containing two pointers
 * the low 4 bits contain a tag that identifies the type of cell except usual list cells
 * naturally have a tag of 0.  Chunks contain the text of atoms linked in a list, but
 * the tag is not present unless the Chunk is marked for garbage collection. Bit 3 is
 * used to mark reachable cells during garbage collection.  There are just enough bits
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

const char* cellTypes[] =
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
struct Cons   { sexp              cdr; sexp                  car; };
struct Chunk  { unsigned char tags[1]; char text[sizeof(Cons)-1]; };
struct Atom   { unsigned char tags[8]; sexp               chunks; };
struct String { unsigned char tags[8]; sexp               chunks; };
struct Fixnum { unsigned char tags[8]; long               fixnum; };
struct Funct  { unsigned char tags[8]; void*               funcp; };
struct Form   { unsigned char tags[8]; Formp               formp; };

sexp read(FILE* fin);
sexp scan(FILE* fin);
sexp set(sexp p, sexp r);
sexp eval(sexp p, sexp env);
sexp evlis(sexp p, sexp env);
void display(FILE* fout, sexp p);
sexp assoc(sexp formals, sexp actuals, sexp env);

// these are the built-in atoms

sexp anda, atoma, atomsa, begin, cara, cdra, cond, consa, define, displaya;
sexp divide, dot, elsea, endl, f, gea, gta, eqva, globals, ifa, lambda, lparen;
sexp lea, let, loada, lta, lista, max, min, minus, modulo, newlinea, nil;
sexp nota, ora, plus, qchar, quote, reada, rparen, seta, setcara, setcdra, t;
sexp times, voida, whilea;

static inline int  arity(const sexp p)    { return                     ((Chunk*)p)->tags[1];  }
static inline int  cellType(const sexp p) { return                (7 & ((Chunk*)p)->tags[0]); }
static inline bool isMarked(const sexp p) { return p &&        (MARK & ((Chunk*)p)->tags[0]); }
static inline bool isCons(const sexp p)   { return p && CONS   == (7 & ((Chunk*)p)->tags[0]); }
static inline bool isChunk(const sexp p)  { return p && CHUNK  == (7 & ((Chunk*)p)->tags[0]); }
static inline bool isAtom(const sexp p)   { return p && ATOM   == (7 & ((Chunk*)p)->tags[0]); }
static inline bool isString(const sexp p) { return p && STRING == (7 & ((Chunk*)p)->tags[0]); }
static inline bool isFunct(const sexp p)  { return p && FUNCT  == (7 & ((Chunk*)p)->tags[0]); }
static inline bool isForm(const sexp p)   { return p && FORM   == (7 & ((Chunk*)p)->tags[0]); }
static inline bool isFixnum(const sexp p) { return p && NUMBER == (7 & ((Chunk*)p)->tags[0]); }

jmp_buf the_jmpbuf;

int  marked = 0;            // how many cells were marked during gc
sexp atoms = 0;             // all atoms are linked in a list
sexp block = 0;             // all the storage starts here
sexp global = 0;            // this is the global symbol table (a list)
sexp freelist = 0;          // available cells are linked in a list
int allocated = 0;          // how many cells have been allocated

const int PSIZE=1024;       // size of protection stack
sexp protect[PSIZE];        // protection stack
sexp *psp = protect+PSIZE;  // protection stack pointer

void prot(sexp p)
{
    if (psp <= protect)
        puts("protection stack overflow!");
#ifdef DEBUG
    printf("push: ");
    display(stdout, p);
    putchar('\n');
#endif
    *--psp = p;
}

void unprot(int n)
{
    if (psp+n > protect+PSIZE)
        puts("protection stack underflow!");
    while (n > 0)
    {
#ifdef DEBUG
        printf("popped: ");
        display(stdout, *psp);
        putchar('\n');
#endif
        --n, *psp++ = 0;
    }
}

static void markCell(sexp p)
{
#ifdef DEBUG
    printf("%lx markCell %s\n", (long)p, cellTypes[cellType(p)]);
#endif
    ((Chunk*)p)->tags[0] |=  MARK;
    ++marked;
}

static void unmarkCell(sexp p)
{
    ((Chunk*)p)->tags[0] &= ~MARK;
#ifdef DEBUG
    printf("%lx unmarkCell %s\n", (long)p, cellTypes[cellType(p)]);
#endif
    --marked;
}

/*
 * visit objects reachable from p, setting their MARK bit
 */
void mark(sexp p)
{
    if (!p || isMarked(p))
        return;
    if (isAtom(p))
        mark(((Atom*)p)->chunks);
    else if (isString(p))
        mark(((String*)p)->chunks);
    else if (isCons(p)) {
        mark(p->car);
        mark(p->cdr);
    }
    markCell(p);
}

/*
 * mark all reachable objects
 *
 * sweep all storage, putting unmarked objects on the freelist
 */
void gc(void)
{
#ifdef GC
    int werefree = MAX-allocated;

    printf("gc: allocated: %d free: %d", allocated, werefree);

    marked = 0;
    mark(atoms);
    mark(global);
    while (psp < protect+PSIZE)
    {
        mark(*psp);
        *psp++ = 0;
    }

    printf(" marked: %d expected garbage: %d", marked, werefree+allocated-marked);

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
        } else 
            unmarkCell(p);
    }

    printf(" reclaimed: %d\n", reclaimed);
    allocated -= reclaimed-werefree;

    if (!freelist)
    {
        printf("storage exhausted!\n");
        exit(0);
    }
#else
    printf("no gc\n");
    exit(0);
#endif
}

sexp cell(void)
{
    if (allocated+16 >= MAX)
        gc();

    ++allocated;
    Cons* p = freelist;
    freelist = freelist->cdr;
    p->cdr = 0;
    return p;
}

sexp atom(sexp chunks)
{
    Atom* p = (Atom*)cell();
    p->tags[0] = ATOM;
    p->chunks = chunks;
    return (sexp)p;
}

sexp string(sexp chunks)
{
    String* p = (String*)cell();
    p->tags[0] = STRING;
    p->chunks = chunks;
    return (sexp)p;
}

sexp fixnum(long number)
{
    Fixnum* p = (Fixnum*)cell();
    p->tags[0] = NUMBER;
    p->fixnum = number;
    return (sexp)p;
}

void set_form(sexp name, Formp f)
{
    Form* p = (Form*)cell();
    p->tags[0] = FORM;
    p->formp = f;
    set(name, (sexp)p);
}

void set_funct(sexp name, int arity, void* f)
{
    Funct* p = (Funct*)cell();
    p->tags[0] = FUNCT;
    p->tags[1] = arity;
    p->funcp = f;
    set(name, (sexp)p);
}

sexp cons(sexp car, sexp cdr)
{
    sexp p = cell();
    p->car = car;
    p->cdr = cdr;
    return p;
}

sexp car(sexp p)
{
    if (!p || !isCons(p))
    {
        printf("longjmp! car of %s ", cellTypes[cellType(p)]);
        display(stdout, p);
        putchar('\n');
        longjmp(the_jmpbuf, 1);
    }
    return p->car;
}

sexp cdr(sexp p)
{
    if (!p || !isCons(p))
    {
        printf("longjmp! cdr of %s ", cellTypes[cellType(p)]);
        display(stdout, p);
        putchar('\n');
        longjmp(the_jmpbuf, 1);
    }
    return p->cdr;
}

sexp setcarfunc(sexp p, sexp q)
{
    if (!isCons(p))
        return 0;
    sexp r = p->car;
    p->car = q;
    return r;
}

sexp setcdrfunc(sexp p, sexp q)
{
    if (!isCons(p))
        return 0;
    sexp r = p->cdr;
    p->cdr = q;
    return r;
}

sexp atomp(sexp p)
{
    return p && isAtom(p) ? t : 0;
}

sexp listp(sexp p)
{
    return p && isCons(p) ? t : 0;
}

sexp andform(sexp p, sexp env)
{
    sexp q = t;
    while (p = p->cdr)
    {
        q = eval(p->car, env);
        if (!q)
            return 0;
    }
    return q;
}

sexp orform(sexp p, sexp env)
{
   while (p = p->cdr)
   {
        sexp q = eval(p->car, env);
        if (q)
            return q;
   }
   return 0;
}

long asFixnum(sexp p)
{
    return ((Fixnum*)p)->fixnum;
}

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

sexp isnot(sexp x)
{
    return x ? 0 : t;
}

sexp load(sexp x)
{
    if (isString(x)) {
        int length = 0;
        for (sexp p = ((String*)x)->chunks; p; p = p->cdr)
        {
            int i = 0;
            while (i < sizeof(Cons)-1 && ((Chunk*)p->car)->text[i])
                ++i;
            length += i;
        }
        char *name = (char*) alloca(length+1);
        int j = 0;
        for (sexp p = ((String*)x)->chunks; p; p = p->cdr)
            for (int i = 0; i < sizeof(Cons)-1 && ((Chunk*)p->car)->text[i]; name[j++] = ((Chunk*)p->car)->text[i++]) {}
        name[j++] = 0;
        FILE* fin = fopen(name, "r");
        while (!feof(fin))
        {
            sexp input = read(fin);
            if (!input)
                break;
            eval(input, global);
        }
        fclose(fin);
    } else
        return 0;
}

sexp newlinefunc(sexp args)
{
    return endl;
}

sexp displayfunc(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
    {
        display(stdout, p->car);
        if (p->cdr)
            putchar(' ');
    }
    return voida;
}

/*
 * construct a linked list of chunks of sizeof(void*) characters
 */
sexp chunk(const char *t)
{
    sexp p = cell();
    sexp q = p;
    Chunk* r = (Chunk*) cell();
    r->tags[0] = CHUNK;
    q->car = (sexp) r;
    int i = 0;
    for (;;)
    {
        char c = *t++;
        r->text[i++] = c;
        if (!c)
            return p;
        if (i >= sizeof(Cons)-1)
        {
            i = 0;
            q = q->cdr = cell();
            r = (Chunk*) cell();
            r->tags[0] = CHUNK;
            q->car = (sexp) r;
        }
    }
}

void displayList(FILE* fout, sexp expr)
{
    putc('(', fout);
    while (expr) {
        display(fout, expr->car);
        if (expr->cdr) {
            if (isCons(expr->cdr)) {
                putc(' ', fout);
                expr = expr->cdr;
            } else {
                fprintf(fout, "%s", " . ");
                display(fout, expr->cdr);
                expr = 0;
            }
        } else
            expr = expr->cdr;
    }
    putc(')', fout);
}

void printChunks(FILE* fout, sexp p)
{
    while (p)
    {
        for (int i = 0; i < sizeof(Cons)-1; ++i)
        {
            char c = ((Chunk*)p->car)->text[i];
            if (!c)
                break;
            putc(c, fout);
        }
        p = p->cdr;
    }
}

void display(FILE* fout, sexp expr)
{
    if (!expr)
        fprintf(fout, "%s", "#f");
    else if (isCons(expr))
        displayList(fout, expr);
    else if (isString(expr)) {
        putc('"', fout);
        printChunks(fout, ((String*)expr)->chunks);
        putc('"', fout);
    } else if (isAtom(expr))
        printChunks(fout, ((Atom*)expr)->chunks);
    else if (isFixnum(expr))
        fprintf(fout, "%ld", ((Fixnum*)expr)->fixnum);
    else if (isFunct(expr))
        fprintf(fout, "#function%d@%lx", arity(expr), (long)((Funct*)expr)->funcp);
    else if (isForm(expr))
        fprintf(fout, "#form@%lx", (long)((Form*)expr)->formp);
}

bool match(sexp p, sexp q)
{
    for (;;)
    {
        if (p == q)
            return true;
        if (!p || !q)
            return false;
        for (int i = 0; i < sizeof(Cons)-1; ++i)
            if (((Chunk*)p->car)->text[i] != ((Chunk*)q->car)->text[i])
                return false;
        p = p->cdr;
        q = q->cdr;
    }
}

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

sexp get(sexp p, sexp env)
{
    for (sexp q = env; q; q = q->cdr)
        if (q->car && p == q->car->car)
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

sexp evlis(sexp p, sexp env)
{
    if (!p)
        return 0;
    return cons(eval(p->car, env), evlis(p->cdr, env));
}

sexp assoc(sexp formals, sexp actuals, sexp env)
{
    if (actuals)
        return cons(cons(formals->car, actuals->car),
                    assoc(formals->cdr, actuals->cdr, env));
    else
        return env;
}

sexp globalform(sexp expr, sexp env)
{
    return env;
}

sexp beginform(sexp expr, sexp env)
{
    sexp v = 0;
    for (sexp p = expr->cdr; p; p = p->cdr)
        v = eval(p->car, env);
    return v;
}

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

sexp atomsfunc(sexp args)
{
    return atoms;
}

sexp quoteform(sexp expr, sexp env)
{
    return expr->cdr->car;
}

sexp readform(sexp expr, sexp env)
{
    return read(stdin);
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
        if (0 == arity(q))
            return (*(Varargp)((Funct*)q)->funcp)(evlis(p->cdr, env));
        if (1 == arity(q))
            return (*(Oneargp)((Funct*)q)->funcp)(eval(p->cdr->car, env));
        if (2 == arity(q))
            return (*(Twoargp)((Funct*)q)->funcp)(eval(p->cdr->car, env), eval(p->cdr->cdr->car, env));
        return 0;
    }
    printf("bad form: ");
    display(stdout, p);
    putchar('\n');
    longjmp(the_jmpbuf,1);
    return p;
}

/*
 * an integer is read from the input stream
 */
long readNumber(FILE* fin)
{
    char c;
    long number = 0;
    for (;;)
    {
        c = getc(fin);
        if ('0' <= c && c <= '9')
            number = 10 * number + (c - '0'); 
        else
            break;
    }
    ungetc(c, fin);
    return number;
}

/*
 * read Chunks terminated by some character
 */
sexp readChunks(FILE* fin, const char *ends)
{
    char c = getc(fin);

    int i = 0;
    sexp p = cell();
    sexp q = p;
    Chunk* r = (Chunk*) cell();
    r->tags[0] = CHUNK;
    q->car = (sexp) r;

    for (;;)
    {
        r->text[i++] = c;
        c = getc(fin);

        if (strchr(ends, c))
        {
            ungetc(c, fin);
            return p;
        }

        if (i == sizeof(Cons)-1) {
            q = q->cdr = cell();
            r = (Chunk*) cell();
            r->tags[0] = CHUNK;
            q->car = (sexp) r;
            i = 0;
        }
    }
}

/*
 * read an atom, number or string from the input stream
 */
sexp scan(FILE* fin)
{
    char c = getc(fin);
    while (strchr(" \t\r\n", c))
        c = getc(fin);
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
        c = getc(fin);
        if ('0' <= c && c <= '9')
            return fixnum(-readNumber(fin));
        ungetc(c, fin);
        return minus;
    } else if ('0' <= c && c <= '9') {
        ungetc(c, fin);
        return fixnum(readNumber(fin));
    }

    if ('"' == c)
    {
        sexp r = string(readChunks(fin, "\""));
        (void)getc(fin);  // read the " again
        return r;
    }

    ungetc(c, fin);
    sexp r = intern(atom(readChunks(fin, "( )\t\r\n")));
    return r;
}

sexp readTail(FILE* fin)
{
    sexp q = read(fin);
    if (rparen == q)
        return 0;
    sexp p = cons(q, readTail(fin));
    return p;
}

/*
 * read an s-expression
 */
sexp read(FILE* fin)
{
    sexp p = scan(fin);
    if (nil == p)
        return 0;
    if (lparen == p)
        return readTail(fin);
    if (qchar == p)
        return cons(quote, cons(read(fin), 0));
    return p;
}

sexp intern_atom_chunk(const char *s)
{
    return intern(atom(chunk(s)));
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

        printf("#%d 0x%016lx sp=0x%016lx %s + 0x%lx\n", ++n,
                static_cast<uintptr_t>(ip), static_cast<uintptr_t>(sp),
                name, static_cast<uintptr_t>(off));

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

    // allocate all the cells we will ever have
    block = (sexp)malloc(MAX*sizeof(Cons));
    for (int i = MAX; --i >= 0; )
    {
        block[i].car = 0;
        block[i].cdr = freelist;
        freelist = block+i;
    }

    // set up all predefined atoms

    anda     = intern_atom_chunk("and");
    atoma    = intern_atom_chunk("atom?");
    atomsa   = intern_atom_chunk("atoms");
    begin    = intern_atom_chunk("begin");
    cara	 = intern_atom_chunk("car");
    cdra	 = intern_atom_chunk("cdr");
    cond     = intern_atom_chunk("cond");
    consa    = intern_atom_chunk("cons");
    define   = intern_atom_chunk("define");
    displaya = intern_atom_chunk("display");
    divide   = intern_atom_chunk("/");
    dot      = intern_atom_chunk(".");
    elsea    = intern_atom_chunk("else");
    endl     = intern_atom_chunk("\n");
    eqva     = intern_atom_chunk("eqv?");
    f        = intern_atom_chunk("#f");
    gea      = intern_atom_chunk(">=");
    globals  = intern_atom_chunk("globals");
    gta      = intern_atom_chunk(">");
    ifa      = intern_atom_chunk("if");
    lambda   = intern_atom_chunk("lambda");
    lea      = intern_atom_chunk("<=");
    let      = intern_atom_chunk("let");
    lista    = intern_atom_chunk("list?");
    loada    = intern_atom_chunk("load");
    lparen   = intern_atom_chunk("(");
    lta      = intern_atom_chunk("<");
    max      = intern_atom_chunk("max");
    min      = intern_atom_chunk("min");
    minus    = intern_atom_chunk("-");
    modulo   = intern_atom_chunk("%");
    newlinea = intern_atom_chunk("newline");
    nil      = intern_atom_chunk("#f");
    nota     = intern_atom_chunk("not");
    ora      = intern_atom_chunk("or");
    plus     = intern_atom_chunk("+");
    qchar    = intern_atom_chunk("'");
    quote    = intern_atom_chunk("quote");
    reada    = intern_atom_chunk("read");
    rparen   = intern_atom_chunk(")");
    seta     = intern_atom_chunk("set");
    setcara  = intern_atom_chunk("set-car");
    setcdra  = intern_atom_chunk("set-cdr");
    seta     = intern_atom_chunk("set");
    t        = intern_atom_chunk("#t");
    times    = intern_atom_chunk("*");
    voida    = intern_atom_chunk("");
    whilea   = intern_atom_chunk("while");

    set(f, f);
    set(t, t);

    // set the definitions (special forms)
    set_form(anda,    andform);
    set_form(begin,   beginform);
    set_form(cond,    condform);
    set_form(define,  defineform);
    set_form(globals, globalform);
    set_form(ifa,     ifform);
    set_form(lambda,  lambdaform);
    set_form(let,     letform);
    set_form(ora,     orform);
    set_form(quote,   quoteform);
    set_form(reada,   readform);
    set_form(seta,    setform);
    set_form(whilea,  whileform);

    // set the definitions (functions)
    set_funct(atoma,    1, (void*)atomp);
    set_funct(atomsa,   0, (void*)atomsfunc);
    set_funct(cara,     1, (void*)car);
    set_funct(cdra,     1, (void*)cdr);
    set_funct(consa,    2, (void*)cons);
    set_funct(displaya, 0, (void*)displayfunc);
    set_funct(divide,   0, (void*)divfunc);
    set_funct(eqva,     2, (void*)eqv);
    set_funct(gea,      2, (void*)ge);
    set_funct(gta,      2, (void*)gt);
    set_funct(lea,      2, (void*)le);
    set_funct(lista,    1, (void*)listp);
    set_funct(loada,    1, (void*)load);
    set_funct(lta,      2, (void*)lt);
    set_funct(max,      0, (void*)maxfunc);
    set_funct(min,      0, (void*)minfunc);
    set_funct(minus,    0, (void*)subfunc);
    set_funct(modulo,   0, (void*)modfunc);
    set_funct(newlinea, 0, (void*)newlinefunc);
    set_funct(nota,     1, (void*)isnot);
    set_funct(plus,     0, (void*)addfunc);
    set_funct(setcara,  2, (void*)setcarfunc);
    set_funct(setcdra,  2, (void*)setcdrfunc);
    set_funct(times,    0, (void*)mulfunc);

    load(string(chunk("init.l")));

    setjmp(the_jmpbuf);

    // read evaluate display ...
    while (!feof(stdin))
    {
#ifdef VOLUNTARY_GC
        gc();
#endif
        sexp e = read(stdin);
        sexp v = eval(e, global);
        if (voida != v)
        {
            display(stdout, v);
            putchar('\n');
        }
    }
    return 0;
}

