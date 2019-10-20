/*
 * this is kind of a lisp interpreter for my own amusement
 * not at all standards compliant or industrial strength
 * dynamically scoped, without tail call optimization
 *
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
#include <assert.h>
#include <cmath>
#include <cfloat>

#define GC
#define PSIZE 8192
#define MAX 262144
#undef  DEBUG
#define SIGNALS

/*
 * storage is managed as a freelist of cells, each potentially containing two pointers
 * the low 4 bits contain a tag that identifies the type of cell except usual list cells
 * naturally have a tag of 0.  Bit 3 is used to mark reachable cells during garbage collection.
 */
enum Tag
{
    CONS   = 0,
    CHUNK  = 1,
    ATOM   = 2,
    FORM   = 3,
    FIXNUM = 4,
    FUNCT  = 5,
    STRING = 6,
    FLONUM = 7,
    MARK   = 8
};

const char* cellTypes[] =
{
	"CONS",
    "CHUNK",
	"ATOM",
	"FORM",
	"FIXNUM",
	"FUNCTION",
	"STRING",
	"FLONUM",
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
struct Flonum { unsigned char tags[8]; double             flonum; };
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

sexp anda, atoma, atomsa, begin, cara, cdra, cond, consa, cosa, define, displaya;
sexp divide, dot, elsea, endl, expa, f, gea, gta, eqva, globals, ifa, lambda, loga;
sexp lparen, lea, let, loada, lta, lista, max, min, minus, modulo, newlinea, nil;
sexp nota, ora, plus, powa, qchar, quote, reada, rparen, seta, setcara, setcdra, sina, t;
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
static inline bool isFixnum(const sexp p) { return p && FIXNUM == (7 & ((Chunk*)p)->tags[0]); }
static inline bool isFlonum(const sexp p) { return p && FLONUM == (7 & ((Chunk*)p)->tags[0]); }

jmp_buf the_jmpbuf;

int  marked = 0;            // how many cells were marked during gc
sexp atoms = 0;             // all atoms are linked in a list
sexp block = 0;             // all the storage starts here
sexp global = 0;            // this is the global symbol table (a list)
sexp freelist = 0;          // available cells are linked in a list
int allocated = 0;          // how many cells have been allocated

sexp protect[PSIZE];        // protection stack
sexp *psp = protect;        // protection stack pointer

/*
 * save the argument on the protection stack, return it
 */
sexp save(sexp p)
{
    *psp++ = p;
#ifdef DEBUG
    printf("push: %ld ", psp-protect);
    display(stdout, p);
    putchar('\n');
#endif
    if (psp >= protect+PSIZE)
        longjmp(the_jmpbuf, (long)"protection stack overflow");
    return p;
}

/*
 * pop n items from the protection stack then return p
 */
sexp lose(int n, sexp p)
{
    if (psp-n < protect)
        longjmp(the_jmpbuf, (long)"protection stack underflow");

    for ( ; n > 0; --n)
    {
        sexp p = *--psp;
        *psp = 0;
#ifdef DEBUG
        printf("popped: ");
        display(stdout, p);
        putchar('\n');
#endif
    }
    return p;
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
    int werefree = MAX-allocated;

    printf("gc: allocated: %d free: %d", allocated, werefree);

    marked = 0;
    mark(atoms);
    mark(global);

    printf(" protected: %lu", psp-protect);

    for (sexp *p = protect; p < psp; ++p)
        mark(*p);

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
}

/*
 * allocate a cell from the freelist
 */
sexp cell(void)
{
    if (allocated >= MAX)
        gc();

    ++allocated;
    Cons* p = freelist;
    freelist = freelist->cdr;
    p->cdr = 0;
    return p;
}

sexp atom(sexp chunks)
{
    save(chunks);
    Atom* p = (Atom*)cell();
    p->tags[0] = ATOM;
    p->chunks = chunks;
    return lose(1, (sexp)p);
}

sexp string(sexp chunks)
{
    save(chunks);
    String* p = (String*)cell();
    p->tags[0] = STRING;
    p->chunks = chunks;
    return lose(1, (sexp)p);
}

sexp fixnum(long number)
{
    Fixnum* p = (Fixnum*)cell();
    p->tags[0] = FIXNUM;
    p->fixnum = number;
    return (sexp)p;
}

sexp flonum(double number)
{
    Flonum* p = (Flonum*)cell();
    p->tags[0] = FLONUM;
    p->flonum = number;
    return (sexp)p;
}

sexp set_form(sexp name, Formp f)
{
    Form* p = (Form*)cell();
    p->tags[0] = FORM;
    p->formp = f;
    return lose(1, set(name, save((sexp)p)));
}

sexp set_funct(sexp name, int arity, void* f)
{
    Funct* p = (Funct*)cell();
    p->tags[0] = FUNCT;
    p->tags[1] = arity;
    p->funcp = f;
    return lose(1, set(name, save((sexp)p)));
}

sexp cons(sexp car, sexp cdr)
{
    save(car);
    save(cdr);
    sexp p = cell();
    p->car = car;
    p->cdr = cdr;
    return lose(2, p);
}

char format_buffer[32];

sexp car(sexp p)
{
    if (!p || !isCons(p))
    {
        sprintf(format_buffer, "car of %s", cellTypes[cellType(p)]);
        display(stdout, p);
        putchar(' ');
        longjmp(the_jmpbuf, (long)format_buffer);
    }
    return p->car;
}

sexp cdr(sexp p)
{
    if (!p || !isCons(p))
    {
        sprintf(format_buffer, "cdr of %s", cellTypes[cellType(p)]);
        display(stdout, p);
        putchar(' ');
        longjmp(the_jmpbuf, (long)format_buffer);
    }
    return p->cdr;
}

sexp setcarfunc(sexp p, sexp q)
{
    if (!isCons(p))
    {
        sprintf(format_buffer, "setcar of %s", cellTypes[cellType(p)]);
        display(stdout, p);
        putchar(' ');
        longjmp(the_jmpbuf, (long)format_buffer);
    }
    sexp r = p->car;
    p->car = q;
    return r;
}

sexp setcdrfunc(sexp p, sexp q)
{
    if (!isCons(p))
    {
        sprintf(format_buffer, "setcdr of %s", cellTypes[cellType(p)]);
        display(stdout, p);
        putchar(' ');
        longjmp(the_jmpbuf, (long)format_buffer);
    }
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

long asFixnum(sexp p)
{
    return isFixnum(p) ? ((Fixnum*)p)->fixnum : (long)((Flonum*)p)->flonum;
}

double asFlonum(sexp p)
{
    return isFlonum(p) ? ((Flonum*)p)->flonum : (double)((Fixnum*)p)->fixnum;
}

sexp lt(sexp x, sexp y)
{
    if (isFlonum(x) || isFlonum(y))
        return asFlonum(x) < asFlonum(y) ? t : 0;
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) < asFixnum(y) ? t : 0;
    return 0;
}

sexp le(sexp x, sexp y)
{
    if (isFlonum(x) || isFlonum(y))
        return asFlonum(x) <= asFlonum(y) ? t : 0;
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) <= asFixnum(y) ? t : 0;
    return 0;
}

sexp ge(sexp x, sexp y)
{
    if (isFlonum(x) || isFlonum(y))
        return asFlonum(x) >= asFlonum(y) ? t : 0;
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) >= asFixnum(y) ? t : 0;
    return 0;
}

sexp gt(sexp x, sexp y)
{
    if (isFlonum(x) || isFlonum(y))
        return asFlonum(x) > asFlonum(y) ? t : 0;
    if (isFixnum(x) && isFixnum(y))
        return asFixnum(x) > asFixnum(y) ? t : 0;
    return 0;
}

sexp allfixnums(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
        if (!isFixnum(p->car))
            return 0;
    return t;
}

sexp allflonums(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
        if (!isFlonum(p->car))
            return 0;
    return t;
}

sexp addfunc(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = 0;
        for (sexp p = args; p; p = p->cdr)
            result += asFixnum(p->car);
        return lose(1, fixnum(result));
    } else if (allflonums(args)) {
        double result = 0;
        for (sexp p = args; p; p = p->cdr)
            result += asFlonum(p->car);
        return lose(1, flonum(result));
    } else {
        double result = 0;
        for (sexp p = args; p; p = p->cdr)
            if (isFlonum(p->car))
                result += asFlonum(p->car);
            else if (isFixnum(p->car))
                result += asFixnum(p->car);
            else
                return lose(1, 0);
        return lose(1, flonum(result));
    }
}

sexp subfunc(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = 0;
        for (sexp p = args; p; p = p->cdr)
        {
            long n = asFixnum(p->car);
            result += (args == p && p->cdr) ? n : -n;
        }
        return lose(1, fixnum(result));
    } else if (allflonums(args)) {
        double result = 0;
        for (sexp p = args; p; p = p->cdr)
        {
            double n = asFlonum(p->car);
            result += (args == p && p->cdr) ? n : -n;
        }
        return lose(1, flonum(result));
    } else {
        double result = 0;
        for (sexp p = args; p; p = p->cdr)
        {
            if (isFlonum(p->car)) {
                double n = asFlonum(p->car);
                result += (args == p && p->cdr) ? n : -n;
            } else if (isFixnum(p->car)) {
                double n = (double)asFixnum(p->car);
                result += (args == p && p->cdr) ? n : -n;
            } else
                return lose(1, 0);
        }
        return lose(1, flonum(result));
    }
}

sexp mulfunc(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = 1;
        for (sexp p = args; p; p = p->cdr)
            result *= asFixnum(p->car);
        return lose(1, fixnum(result));
    } else if (allflonums(args)) {
        double result = 1;
        for (sexp p = args; p; p = p->cdr)
            result *= asFlonum(p->car);
        return lose(1, flonum(result));
    } else {
        double result = 1;
        for (sexp p = args; p; p = p->cdr)
            if (isFixnum(p->car))
                result *= (double)asFixnum(p->car);
            else if (isFlonum(p->car))
                result *= asFlonum(p->car);
            else
                return lose(1, 0);
        return lose(1, flonum(result));
    }
}

sexp divfunc(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = asFixnum(args->car);
        for (sexp p = args->cdr; p; p = p->cdr)
            result = result / asFixnum(p->car);
        return lose(1, fixnum(result));
    } else if (allflonums(args)) {
        double result = asFlonum(args->car);
        for (sexp p = args->cdr; p; p = p->cdr)
            result = result / asFlonum(p->car);
        return lose(1, flonum(result));
    } else {
        double result = asFlonum(args->car);
        for (sexp p = args->cdr; p; p = p->cdr)
            if (isFixnum(p->car))
                result = result / (double)asFixnum(p->car);
            else if (isFlonum(p->car))
                result = result / asFlonum(p->car);
            else
                return lose(1, 0);
        return lose(1, flonum(result));
    }
}

sexp modfunc(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = asFixnum(args->car);
        for (sexp p = args->cdr; p; p = p->cdr)
            result = result % asFixnum(p->car);
        return lose(1, fixnum(result));
    } else if (allflonums(args)) {
        double result = asFlonum(args->car);
        for (sexp p = args->cdr; p; p = p->cdr)
            result = fmod(result, asFlonum(p->car));
        return lose(1, flonum(result));
    } else {
        double result = asFlonum(args->car);
        for (sexp p = args->cdr; p; p = p->cdr)
            if (isFixnum(p->car))
                result = fmod(result, (double)asFixnum(p->car));
            else if (isFlonum(p->car))
                result = fmod(result, asFlonum(p->car));
            else
                return lose(1, 0);
        return lose(1, flonum(result));
    }
}

sexp maxfunc(sexp args)
{
    save(args);
    if (allfixnums(args))
    {
        long result = LONG_MIN;
        for (sexp p = args; p; p = p->cdr)
        {
            long x = asFixnum(p->car);
            if (x > result)
                result = x;
        }
        return lose(1, fixnum(result));
    } else if (allflonums(args)) {
        double result = DBL_MIN;
        for (sexp p = args; p; p = p->cdr)
        {
            long x = asFlonum(p->car);
            if (x > result)
                result = x;
        }
        return lose(1, flonum(result));
    } else
        return lose(1, 0);
}

sexp minfunc(sexp args)
{
    save(args);
    if (allfixnums(args))
    {
        long result = LONG_MAX;
        for (sexp p = args; p; p = p->cdr)
        {
            long x = asFixnum(p->car);
            if (x < result)
                result = x;
        }
        return lose(1, fixnum(result));
    } else if (allflonums(args)) {
        double result = DBL_MAX;
        for (sexp p = args; p; p = p->cdr)
        {
            double x = asFixnum(p->car);
            if (x < result)
                result = x;
        }
        return lose(1, flonum(result));
    } else
        return lose(1, 0);
}

sexp cosfunc(sexp x)
{
    return isFlonum(x) ? flonum(cos(asFlonum(x))) : 0;
}

sexp sinfunc(sexp x)
{
    return isFlonum(x) ? flonum(sin(asFlonum(x))) : 0;
}

sexp logfunc(sexp x)
{
    return isFlonum(x) ? flonum(log(asFlonum(x))) : 0;
}

sexp expfunc(sexp x)
{
    return isFlonum(x) ? flonum(exp(asFlonum(x))) : 0;
}

sexp powfunc(sexp x, sexp y)
{
    return isFlonum(x) && isFlonum(y) ? flonum(pow(asFlonum(x), asFlonum(y))) : 0;
}

sexp isnot(sexp x)
{
    return x ? 0 : t;
}

sexp load(sexp x)
{
    sexp r = 0;
    if (!isString(x))
        return r;
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
        save(input);
        r = lose(1, eval(input, global));
    }
    fclose(fin);
    return r;
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
    save(p);
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
            return lose(1, p);
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
    else if (isFlonum(expr))
        fprintf(fout, "%.12g", ((Flonum*)expr)->flonum);
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
    if (isFlonum(x) && isFlonum(y))
        return asFlonum(x) == asFlonum(y) ? t : 0;
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
    global = cons(save(cons(save(p), save(r))), global);
    return lose(3, 0);
}

sexp evlis(sexp p, sexp env)
{
    if (!p)
        return 0;
    save(p);
    return lose(4, cons(save(eval(p->car, env)), save(evlis(p->cdr, save(env)))));
}

sexp assoc(sexp formals, sexp actuals, sexp env)
{
    if (actuals) {
        save(env);
        save(actuals);
        save(formals);
        return lose(5, cons(save(cons(formals->car, actuals->car)), save(assoc(formals->cdr, actuals->cdr, env))));
    } else
        return env;
}

sexp globalform(sexp expr, sexp env)
{
    return env;
}

sexp beginform(sexp expr, sexp env)
{
    save(env);
    save(expr);
    sexp v = 0;
    for (sexp p = expr->cdr; p; p = p->cdr)
        v = eval(p->car, env);
    return lose(2, v);
}

sexp whileform(sexp expr, sexp env)
{
    save(env);
    save(expr);
    sexp v = 0;
    expr = expr->cdr;
    while (eval(expr->car, env))
        for (sexp p = expr->cdr; p; p = p->cdr)
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
sexp condform(sexp expr, sexp env)
{
    save(env);
    save(expr);
    sexp r = 0;
    for (sexp p = expr->cdr; p; p = p->cdr)
        if (elsea == p->car->car || eval(p->car->car, env)) {
            r = eval(p->car->cdr->car, env);
            break;
        }
    return lose(2, r);
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
        save(p);
        save(env);
        sexp v = save(cons(lambda, save(cons(p->cdr->car->cdr, p->cdr->cdr))));
        for (sexp q = global; q; q = q->cdr)
            if (p->cdr->car->car == q->car->car)
            {
                q->car->cdr = v;
                return lose(4, p->cdr->car->car);
            }
        global = cons(save(cons(p->cdr->car->car, v)), global);
        return lose(5, p->cdr->car->car);
    } else {
        for (sexp q = global; q; q = q->cdr)
            if (p->cdr->car == q->car->car)
            {
                q->car->cdr = p->cdr->cdr->car;
                return p->cdr->car;
            }
        save(p);
        global = cons(save(cons(p->cdr->car, p->cdr->cdr->car)), global);
        return lose(2, p->cdr->car);
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
    save(env);
    save(expr);
    return lose(2,
                  eval(expr->cdr->car, env) ?
             eval(expr->cdr->cdr->car, env) : eval(expr->cdr->cdr->cdr->car, env));
}

/*
 * (set name value) creates a new binding or alters an old one
 */
sexp setform(sexp expr, sexp env)
{
    save(env);
    save(expr);
    return lose(3, set(expr->cdr->car, save(eval(expr->cdr->cdr->car, env))));
}

/*
 * lambda implements user-defined functions
 */
sexp lambdaform(sexp expr, sexp env)
{
    save(env);
    save(expr);
    if (!isCons(expr->car)) {
        expr = save(cons(save(eval(expr->car, env)), expr->cdr));
        return lose(6, eval(expr->car->cdr->cdr->car,
                              save(assoc(expr->car->cdr->car, save(evlis(expr->cdr, env)), env))));
    } else
        return lose(4, eval(expr->car->cdr->cdr->car,
                              save(assoc(expr->car->cdr->car, save(evlis(expr->cdr, env)), env))));
}

/*
 * associate variables with values, used by letform
 */
sexp augment(sexp exp, sexp env)
{
    if (exp) {
        save(exp);
        return lose(5, cons(save(cons(exp->car->car,
                                        save(eval(exp->car->cdr->car, env)))),
                              save(augment(exp->cdr, save(env)))));
    } else
        return env;
}

/*
 * (let ((var value) ..) expr)
 */
sexp letform(sexp expr, sexp env)
{
    save(env);
    save(expr);
    return lose(3, eval(expr->cdr->cdr->car, save(augment(expr->cdr->car, env))));
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
    if (isFlonum(p))
        return p;
    if (isString(p))
        return p;
    if (isCons(p) && lambda == p->car)
        return p;
    sexp q = save(eval(save(p)->car, save(env)));
    if (isCons(q) && lambda == q->car)
        return lose(3, lambdaform(p, env));
    if (isForm(q))
        return lose(3, (*((Form*)q)->formp)(p, env));
    if (isFunct(q) && 0 == arity(q))
            return lose(4, (*(Varargp)((Funct*)q)->funcp)(save(evlis(p->cdr, env))));
    if (isFunct(q) && 1 == arity(q))
            return lose(4, (*(Oneargp)((Funct*)q)->funcp)(save(eval(p->cdr->car, env))));
    if (isFunct(q) && 2 == arity(q))
            return lose(5, (*(Twoargp)((Funct*)q)->funcp)(save(eval(p->cdr->car, env)), save(eval(p->cdr->cdr->car, env))));
    display(stdout, p);
    putchar('\n');
    longjmp(the_jmpbuf, (long)"bad form");
    return p;
}

/*
 * a number is read from the input stream, return true if floating point
 */
bool readNumber(FILE* fin, double& flonum, long& fixnum)
{
    char c;
    flonum = 0;
    fixnum = 0;
    double factor = 0;
    for (;;)
    {
        c = getc(fin);
        if ('0' <= c && c <= '9') {
            flonum = 10 * flonum + (c - '0'); 
            fixnum = 10 * fixnum + (c - '0'); 
            factor *= 0.1;
        } else if ('.' == c)
            factor = 1;
        else
            break;
    }

    if ('e' == c || 'E' == c)
    {
        int exp = 0;
        c = getc(fin);
        if ('-' == c) {
            c = getc(fin);
            while ('0' <= c && c <= '9')
                exp = 10 * exp + (c - '0');
            while (exp++ < 0)
                factor *= 0.1;
        } else if ('+' == c) {
            c = getc(fin);
            while ('0' <= c && c <= '9')
                exp = 10 * exp + (c - '0');
            while (exp-- > 0)
                factor *= 10.0;
        }
    }

    ungetc(c, fin);

    if (factor)
    {
        flonum *= factor;
        return true;
    } else
        return false;
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
    save(p);
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
            return lose(1, p);
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

enum { NON_NUMERIC, INT_NUMERIC, FLO_NUMERIC };

/*
 * read an atom, number or string from the input stream
 */
sexp scan(FILE* fin)
{
    char buffer[32];
    char *p = buffer;
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
    else if ('-' == c) {
        c = getc(fin);
        if ('.' == c || '0' <= c && c <= '9')
            *p++ = '-';
        else {
            ungetc(c, fin);
            return minus;
        } 
    }

    int rc = NON_NUMERIC;

    for (;;)
    {
        while (' ' == c || '\t' == c || '\n' == c)
            c = getc(fin);

        while ('0' <= c && c <= '9')
        {
            rc = INT_NUMERIC;
            *p++ = c;
            c = getc(fin);
        }

        if ('.' == c)
        {
            rc = FLO_NUMERIC;
            *p++ = c;
            c = getc(fin);
        }

        while ('0' <= c && c <= '9')
        {
            *p++ = c;
            c = getc(fin);
        }
        if ((INT_NUMERIC == rc || FLO_NUMERIC == rc) && ('e' == c || 'E' == c))
        {
            rc = NON_NUMERIC;
            *p++ = c;
            c = getc(fin);
            if ('-' == c) {
                *p++ = c;
                c = getc(fin);
            } else if ('+' == c) {
                *p++ = c;
                c = getc(fin);
            }
            while ('0' <= c && c <= '9')
            {
                rc = FLO_NUMERIC;
                *p++ = c;
                c = getc(fin);
            }
        }
        *p++ = 0;
        ungetc(c, fin);
        break;
    }

    if (FLO_NUMERIC == rc)
    {
        char *nptr;
        double floater = strtod(buffer, &nptr);
        if (nptr == strchr(buffer, '\0'))
            return flonum(floater);
    }

    if (INT_NUMERIC == rc)
    {
        char *nptr;
        long fixer = strtol(buffer, &nptr, 10);
        if (nptr == strchr(buffer, '\0'))
            return fixnum(fixer);
    }

    if ('"' == c)
    {
        sexp r = string(readChunks(fin, "\""));
        (void)getc(fin);  // read the " again
        return r;
    }

    return intern(atom(readChunks(fin, "( )\t\r\n")));
}

sexp readTail(FILE* fin)
{
    sexp q = read(fin);
    if (rparen == q)
        return 0;
    save(q);
    return lose(2, cons(q, save(readTail(fin))));
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
        return lose(2, cons(quote, save(cons(save(read(fin)), 0))));
    return p;
}

sexp intern_atom_chunk(const char *s)
{
    return intern(atom(chunk(s)));
}

#ifdef SIGNALS
void signal_handler(int sig)
{
    putchar('\n');

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

        printf("#%2d 0x%016lx sp=0x%016lx %s + 0x%lx\n", ++n,
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
    cosa     = intern_atom_chunk("cos");
    define   = intern_atom_chunk("define");
    displaya = intern_atom_chunk("display");
    divide   = intern_atom_chunk("/");
    dot      = intern_atom_chunk(".");
    elsea    = intern_atom_chunk("else");
    endl     = intern_atom_chunk("\n");
    eqva     = intern_atom_chunk("eqv?");
    expa     = intern_atom_chunk("exp");
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
    loga     = intern_atom_chunk("log");
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
    powa     = intern_atom_chunk("pow");
    qchar    = intern_atom_chunk("'");
    quote    = intern_atom_chunk("quote");
    reada    = intern_atom_chunk("read");
    rparen   = intern_atom_chunk(")");
    seta     = intern_atom_chunk("set");
    setcara  = intern_atom_chunk("set-car");
    setcdra  = intern_atom_chunk("set-cdr");
    seta     = intern_atom_chunk("set");
    sina     = intern_atom_chunk("sin");
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
    set_funct(cosa,     1, (void*)cosfunc);
    set_funct(displaya, 0, (void*)displayfunc);
    set_funct(divide,   0, (void*)divfunc);
    set_funct(eqva,     2, (void*)eqv);
    set_funct(expa,     1, (void*)expfunc);
    set_funct(gea,      2, (void*)ge);
    set_funct(gta,      2, (void*)gt);
    set_funct(lea,      2, (void*)le);
    set_funct(lista,    1, (void*)listp);
    set_funct(loga,     1, (void*)logfunc);
    set_funct(loada,    1, (void*)load);
    set_funct(lta,      2, (void*)lt);
    set_funct(max,      0, (void*)maxfunc);
    set_funct(min,      0, (void*)minfunc);
    set_funct(minus,    0, (void*)subfunc);
    set_funct(modulo,   0, (void*)modfunc);
    set_funct(newlinea, 0, (void*)newlinefunc);
    set_funct(nota,     1, (void*)isnot);
    set_funct(plus,     0, (void*)addfunc);
    set_funct(powa,     2, (void*)powfunc);
    set_funct(setcara,  2, (void*)setcarfunc);
    set_funct(setcdra,  2, (void*)setcdrfunc);
    set_funct(sina,     1, (void*)sinfunc);
    set_funct(times,    0, (void*)mulfunc);

    load(string(chunk("init.l")));

    const char *s = (const char *)setjmp(the_jmpbuf);
    if (s)
        printf("%s!\n", s);

    // read evaluate display ...
    while (!feof(stdin))
    {
#ifdef GC
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

