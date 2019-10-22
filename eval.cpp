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
#define PSIZE   16384
#define MAX     262144

#define UNW_LOCAL_ONLY
#ifdef  UNWIND
#include <libunwind.h>
#include <cxxabi.h>
#endif
#include <assert.h>
#include <cfloat>
#include <climits>
#include <cmath>
#include <csetjmp>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <unistd.h>

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
    ATOM   = 0,
    STRING = 1,
    CHUNK  = 2,
    FORM   = 3,
    FIXNUM = 4,
    FUNCT  = 5,
    FLONUM = 6
};

typedef struct Cons *sexp;
typedef sexp (*Formp)(sexp, sexp);
typedef sexp (*Varargp)(sexp);
typedef sexp (*Oneargp)(sexp);
typedef sexp (*Twoargp)(sexp, sexp);

/*
 * setting up union declarations isn't all that fun
 */
struct Cons   { sexp                cdr; sexp                  car; };
struct Other  { char                          tags[sizeof(Cons)-0]; };
struct Chunk  { char tags[2];            char text[sizeof(Cons)-2]; };
struct Atom   { char tags[sizeof(sexp)]; sexp               chunks; };
struct String { char tags[sizeof(sexp)]; sexp               chunks; };
struct Fixnum { char tags[sizeof(sexp)]; long               fixnum; };
struct Flonum { char tags[sizeof(sexp)]; double             flonum; };
struct Funct  { char tags[sizeof(sexp)]; void*               funcp; };
struct Form   { char tags[sizeof(sexp)]; Formp               formp; };

sexp read(FILE* fin);
sexp scan(FILE* fin);
sexp set(sexp p, sexp r);
sexp eval(sexp p, sexp env);
sexp evlis(sexp p, sexp env);
void display(FILE* fout, sexp p);
sexp assoc(sexp formals, sexp actuals, sexp env);

// these are the built-in atoms

sexp adda, ampera, anda, atoma, atomsa, begin, cara, cdra, cond, consa, cosa;
sexp define, displaya, diva, dot, elsea, endl, expa, f, gea, gta, eqva;
sexp globals, ifa, lambda, loga, lparen, lea, let, loada, lta, lista, minus;
sexp moda, modulo, mula, newlinea, nil, nota, ora, pipea, plus, powa, qchar, quote;
sexp reada, rparen, seta, setcara, setcdra, sina, sqrta, suba, t, times, voida, whilea;
sexp lsha, rsha, tilde, xora;

static inline bool isMarked(const sexp p) { return       (MARK        & ((Other*)p)->tags[0]); }
static inline bool isCons(const sexp p)   { return p && !(OTHER       & ((Other*)p)->tags[0]); }
static inline bool isOther(const sexp p)  { return p &&  (OTHER       & ((Other*)p)->tags[0]); }
static inline int  evalType(const sexp p) { return                      ((Other*)p)->tags[1];  }
static inline int  arity(const sexp p)    { return                      ((Other*)p)->tags[2];  }
static inline bool isAtom(const sexp p)   { return isOther(p) && ATOM   == evalType(p);        }
static inline bool isString(const sexp p) { return isOther(p) && STRING == evalType(p);        }
static inline bool isChunk(const sexp p)  { return isOther(p) && CHUNK  == evalType(p);        }
static inline bool isFunct(const sexp p)  { return isOther(p) && FUNCT  == evalType(p);        }
static inline bool isForm(const sexp p)   { return isOther(p) && FORM   == evalType(p);        }
static inline bool isFixnum(const sexp p) { return isOther(p) && FIXNUM == evalType(p);        }
static inline bool isFlonum(const sexp p) { return isOther(p) && FLONUM == evalType(p);        }

jmp_buf the_jmpbuf;

bool killed = 0;        // to catch consecutive SIGINTs
sexp atoms = 0;         // all atoms are linked in a list
sexp block = 0;         // all the storage starts here
sexp global = 0;        // this is the global symbol table (a list)
sexp freelist = 0;      // available cells are linked in a list
int  marked = 0;        // how many cells were marked during gc
int  allocated = 0;     // how many cells have been allocated
int  total = 0;         // total allocation across gc's
int  collected = 0;     // how many gc's
sexp protect[PSIZE];    // protection stack
sexp *psp = protect;    // protection stack pointer

/*
 * save the argument on the protection stack, return it
 */
sexp save(sexp p)
{
    *psp++ = p;
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
    }
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

/*
 * visit objects reachable from p, setting their MARK bit
 */
void mark(sexp p)
{
    if (!p || isMarked(p))
        return;
    if (isCons(p))
        { mark(p->car); mark(p->cdr); }
    else if (isAtom(p))
        mark(((Atom*)p)->chunks);
    else if (isString(p))
        mark(((String*)p)->chunks);
    markCell(p);
}

/*
 * mark all reachable objects
 *
 * sweep all storage, putting unmarked objects on the freelist
 */
void gc(bool verbose)
{
    int werefree = MAX-allocated;
    int wereprot = psp-protect;
    marked = 0;
    mark(atoms);
    mark(global);
    for (sexp *p = protect; p < psp; ++p)
        mark(*p);
    int weremark = marked;
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
    if (verbose)
        printf("gc: allocated: %d protected: %d marked: %d reclaimed: %d collections: %d allocation: %d\n",
               allocated, wereprot, weremark, reclaimed, collected, total);

    allocated -= reclaimed-werefree;
    total += allocated;
    ++collected;
    if (!freelist)
        longjmp(the_jmpbuf, (long)"storage exhausted");
}

/*
 * allocate a cell from the freelist
 */
sexp cell(void)
{
    if (allocated >= MAX)
        gc(false);

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
    p->tags[0] = OTHER;
    p->tags[1] = ATOM;
    p->chunks = chunks;
    return lose(1, (sexp)p);
}

sexp string(sexp chunks)
{
    save(chunks);
    String* p = (String*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = STRING;
    p->chunks = chunks;
    return lose(1, (sexp)p);
}

sexp fixnum(long number)
{
    Fixnum* p = (Fixnum*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = FIXNUM;
    p->fixnum = number;
    return (sexp)p;
}

sexp flonum(double number)
{
    Flonum* p = (Flonum*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = FLONUM;
    p->flonum = number;
    return (sexp)p;
}

sexp set_form(sexp name, Formp f)
{
    Form* p = (Form*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = FORM;
    p->formp = f;
    return lose(1, set(name, save((sexp)p)));
}

sexp set_funct(sexp name, int arity, void* f)
{
    Funct* p = (Funct*)cell();
    p->tags[0] = OTHER;
    p->tags[1] = FUNCT;
    p->tags[2] = arity;
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

sexp car(sexp p)
{
    if (!isCons(p))
        longjmp(the_jmpbuf, (long)"car: bad argument");
    return p->car;
}

sexp cdr(sexp p)
{
    if (!isCons(p))
        longjmp(the_jmpbuf, (long)"cdr: bad argument");
    return p->cdr;
}

sexp setcarfunc(sexp p, sexp q)
{
    if (!isCons(p))
        longjmp(the_jmpbuf, (long)"setcar: bad argument");
    sexp r = p->car;
    p->car = q;
    return r;
}

sexp setcdrfunc(sexp p, sexp q)
{
    if (!isCons(p))
        longjmp(the_jmpbuf, (long)"setcdr: bad argument");
    sexp r = p->cdr;
    p->cdr = q;
    return r;
}

sexp atomp(sexp p)
{
    return isAtom(p) ? t : 0;
}

sexp listp(sexp p)
{
    return isCons(p) ? t : 0;
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

bool cmplt(sexp x, sexp y)
{
    if (isFlonum(x)) {
        if (isFlonum(y))
            return asFlonum(x) < asFlonum(y);
        if (isFixnum(y))
            return asFlonum(x) < (double)asFixnum(y);
    } else if (isFixnum(x)) {
        if (isFixnum(y))
            return asFixnum(x) < asFixnum(y);
        if (isFlonum(y))
            return (double)asFixnum(x) < asFixnum(y);
    }
    longjmp(the_jmpbuf, (long)"comparison bad argument");
}

bool cmple(sexp x, sexp y)
{
    if (isFlonum(x)) {
        if (isFlonum(y))
            return asFlonum(x) <= asFlonum(y);
        if (isFixnum(y))
            return asFlonum(x) <= (double)asFixnum(y);
    } else if (isFixnum(x)) {
        if (isFixnum(y))
            return asFixnum(x) <= asFixnum(y);
        if (isFlonum(y))
            return (double)asFixnum(x) <= asFixnum(y);
    }
    longjmp(the_jmpbuf, (long)"comparison bad argument");
}

sexp lt(sexp x, sexp y)
{
    return cmplt(x, y) ? t : 0;
}

sexp le(sexp x, sexp y)
{
    return cmple(x, y) ? t : 0;
}

sexp ge(sexp x, sexp y)
{
    return cmplt(x, y) ? 0 : t;
}

sexp gt(sexp x, sexp y)
{
    return cmple(x, y) ? 0 : t;
}

sexp allfixnums(sexp args)
{
    for (sexp p = args; p; p = p->cdr)
        if (!isFixnum(p->car))
            return 0;
    return t;
}

sexp add(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return fixnum(asFixnum(x) + asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFixnum(x) + asFlonum(y));
        else
            return 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return flonum(asFlonum(x) + asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFlonum(x) + asFlonum(y));
        else
            return 0;
    } else
        return 0;
}

sexp sub(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return fixnum(asFixnum(x) - asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFixnum(x) - asFlonum(y));
        else
            return 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return flonum(asFlonum(x) - asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFlonum(x) - asFlonum(y));
        else
            return 0;
    } else
        return 0;
}

sexp mul(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return fixnum(asFixnum(x) * asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFixnum(x) * asFlonum(y));
        else
            return 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return flonum(asFlonum(x) * asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFlonum(x) * asFlonum(y));
        else
            return 0;
    } else
        return 0;
}

sexp divf(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return fixnum(asFixnum(x) / asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFixnum(x) / asFlonum(y));
        else
            return 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return flonum(asFlonum(x) / asFixnum(y));
        else if (isFlonum(y))
            return flonum(asFlonum(x) / asFlonum(y));
        else
            return 0;
    } else
        return 0;
}

sexp mod(sexp x, sexp y)
{
    if (isFixnum(x)) {
        if (isFixnum(y))
            return fixnum(asFixnum(x) % asFixnum(y));
        else if (isFlonum(y))
            return flonum(fmod((double)asFixnum(x), asFlonum(y)));
        else
            return 0;
    } else if (isFlonum(x)) {
        if (isFixnum(y))
            return flonum(fmod(asFlonum(x), (double)asFixnum(y)));
        else if (isFlonum(y))
            return flonum(fmod(asFlonum(x), asFlonum(y)));
        else
            return 0;
    } else
        return 0;
}

sexp cosfunc(sexp x)
{
    return isFlonum(x) ? flonum(cos(asFlonum(x))) : 0;
}

sexp sinfunc(sexp x)
{
    return isFlonum(x) ? flonum(sin(asFlonum(x))) : 0;
}

sexp sqrtfunc(sexp x)
{
    return isFlonum(x) ? flonum(sqrt(asFlonum(x))) : 0;
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

sexp complement(sexp x)
{
    return isFixnum(x) ? fixnum(~asFixnum(x)) : 0;
}

sexp lsh(sexp x, sexp y)
{
    return isFixnum(x) && isFixnum(y) ? fixnum(asFixnum(x) << asFixnum(y)) : 0;
}

sexp rsh(sexp x, sexp y)
{
    return isFixnum(x) && isFixnum(y) ? fixnum(asFixnum(x) >> asFixnum(y)) : 0;
}

sexp andfunc(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = ~0;
        for (sexp p = args; p; p = p->cdr)
            result = result & asFixnum(p->car);
        return lose(1, fixnum(result));
    } else
        return lose(1, 0);
}

sexp orfunc(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = 0;
        for (sexp p = args; p; p = p->cdr)
            result = result | asFixnum(p->car);
        return lose(1, fixnum(result));
    } else
        return lose(1, 0);
}

sexp xorfunc(sexp args)
{
    save(args);
    if (allfixnums(args)) {
        long result = 0;
        for (sexp p = args; p; p = p->cdr)
            result = result ^ asFixnum(p->car);
        return lose(1, fixnum(result));
    } else
        return lose(1, 0);
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
        Chunk* t = (Chunk*)(p->car);
        while (i < sizeof(t->text) && t->text[i])
            ++i;
        length += i;
    }

    int j = 0;
    char *name = (char*) alloca(length+1);
    for (sexp p = ((String*)x)->chunks; p; p = p->cdr)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text) && t->text[i]; name[j++] = t->text[i++]) {}
    }

    name[j++] = 0;
    printf("; load: %s\n", name);
    FILE* fin = fopen(name, "r");
    if (fin)
    {
        while (!feof(fin))
        {
            sexp input = read(fin);
            if (!input)
                break;
            save(input);
            r = lose(1, eval(input, global));
        }
        fclose(fin);
    }
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

void displayChunks(FILE* fout, sexp p)
{
    while (p)
    {
        Chunk* t = (Chunk*)(p->car);
        for (int i = 0; i < sizeof(t->text); ++i)
        {
            char c = t->text[i];
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
        displayChunks(fout, ((String*)expr)->chunks);
        putc('"', fout);
    } else if (isAtom(expr))
        displayChunks(fout, ((Atom*)expr)->chunks);
    else if (isFixnum(expr))
        fprintf(fout, "%ld", ((Fixnum*)expr)->fixnum);
    else if (isFlonum(expr))
        fprintf(fout, "%#.12f", ((Flonum*)expr)->flonum);
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
        Chunk* s = (Chunk*)(p->car);
        Chunk* t = (Chunk*)(q->car);
        for (int i = 0; i < sizeof(s->text); ++i)
        {
            if (0 == s->text[i] && 0 == t->text[i])
                return true;
            if (s->text[i] != t->text[i])
                return false;
        }
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
    for (sexp q = atoms; q; q = q->cdr)
    {
        sexp r = q->car;
        if (match(((Atom*)p)->chunks, ((Atom*)r)->chunks))
            return r;
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
    return lose(4, cons(save(eval(p->car, env)), save(evlis(save(p)->cdr, save(env)))));
}

sexp assoc(sexp formals, sexp actuals, sexp env)
{
    if (!actuals || !formals)
        return env;
    return lose(5, cons(save(cons(formals->car, actuals->car)), save(assoc(save(formals)->cdr, save(actuals)->cdr, save(env)))));
}

sexp globalform(sexp expr, sexp env)
{
    return env;
}

sexp beginform(sexp expr, sexp env)
{
    save(env);
    sexp v = 0;
    for (sexp p = save(expr)->cdr; p; p = p->cdr)
        v = eval(p->car, env);
    return lose(2, v);
}

sexp whileform(sexp expr, sexp env)
{
    save(env);
    sexp v = 0;
    expr = save(expr)->cdr;
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
    sexp r = 0;
    for (sexp p = save(expr)->cdr; p; p = p->cdr)
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
 * or
 *      (define (mycar . x) (car x))
 * as
 *      (define mycar (lambda (mycar . x) (car x)))
 */
sexp defineform(sexp p, sexp env)
{
    if (isCons(p->cdr->car))
    {
        if (isCons(p->cdr->car->cdr))
        {
            save(env);
            sexp v = save(cons(lambda, save(cons(p->cdr->car->cdr, save(p)->cdr->cdr))));
            for (sexp q = global; q; q = q->cdr)
                if (p->cdr->car->car == q->car->car)
                {
                    q->car->cdr = v;
                    return lose(4, p->cdr->car->car);
                }
            global = cons(save(cons(p->cdr->car->car, v)), global);
            return lose(5, p->cdr->car->car);
        } else {
            save(env);
            sexp v = cons(lambda, save(cons(save(cons(p->cdr->car->car, p->cdr->car->cdr)), save(p)->cdr->cdr)));
            for (sexp q = global; q; q = q->cdr)
                if (p->cdr->car->car == q->car->car)
                {
                    q->car->cdr = v;
                    return lose(4, p->cdr->car->car);
                }
            global = cons(save(cons(p->cdr->car->car, v)), global);
            return lose(5, p->cdr->car->car);
        }
    } else {
        for (sexp q = global; q; q = q->cdr)
            if (p->cdr->car == q->car->car)
            {
                q->car->cdr = p->cdr->cdr->car;
                return p->cdr->car;
            }
        global = cons(save(cons(p->cdr->car, save(p)->cdr->cdr->car)), global);
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
    return lose(2, eval(save(expr)->cdr->car, save(env)) ?
                          eval(expr->cdr->cdr->car, env) : eval(expr->cdr->cdr->cdr->car, env));
}

/*
 * (set name value) creates a new binding or alters an old one
 */
sexp setform(sexp expr, sexp env)
{
    return lose(3, set(expr->cdr->car, save(eval(save(expr)->cdr->cdr->car, save(env)))));
}

/*
 * associate variables with values, used by letform
 */
sexp augment(sexp exp, sexp env)
{
    if (!exp)
        return env;
    return lose(5, cons(save(cons(exp->car->car, save(eval(exp->car->cdr->car, env)))), save(augment(save(exp)->cdr, save(env)))));
}

/*
 * (let ((var value) ..) expr)
 */
sexp letform(sexp expr, sexp env)
{
    return lose(3, eval(expr->cdr->cdr->car, save(augment(save(expr)->cdr->car, save(env)))));
}

/*
 * malformed constructs will fail without grace
 */
sexp eval(sexp p, sexp env)
{
    if (!p || f == p || t == p || isOther(p) && ATOM != evalType(p))
        return p;
    if (isAtom(p))
        return get(p, env);
    if (lambda == p->car)
        return p;
    sexp q = save(eval(save(p)->car, save(env)));
    if (isCons(q) && lambda == q->car)
        if (isAtom(q->cdr->car->cdr))
            return lose(6, eval(q->cdr->cdr->car, save(cons(save(cons(q->cdr->car->cdr, save(evlis(p->cdr, env)))), env))));
        else
            return lose(5, eval(q->cdr->cdr->car, save(assoc(q->cdr->car, save(evlis(p->cdr, env)), env))));
    if (isForm(q))
        return lose(3, (*((Form*)q)->formp)(p, env));
    if (isFunct(q))
    {
        if (0 == arity(q))
            return lose(4, (*(Varargp)((Funct*)q)->funcp)(save(evlis(p->cdr, env))));
        if (1 == arity(q) && p->cdr)
            return lose(4, (*(Oneargp)((Funct*)q)->funcp)(save(eval(p->cdr->car, env))));
        if (2 == arity(q) && p->cdr && p->cdr->cdr)
            return lose(5, (*(Twoargp)((Funct*)q)->funcp)(save(eval(p->cdr->car, env)), save(eval(p->cdr->cdr->car, env))));
    }
    printf("bad form: "); display(stdout, q); printf(" in "); display(stdout, p); putchar('\n');
    //longjmp(the_jmpbuf, (long)"bad form");
    return p;
}

/*
 * construct a linked list of chunks of sizeof(void*) characters
 */
sexp chunk(const char *t)
{
    if (0 == *t)
        return 0;

    char c = *t++;

    sexp p = cell();
    save(p);
    sexp q = p;
    Chunk* r = (Chunk*) cell();
    r->tags[0] = OTHER;
    r->tags[1] = CHUNK;
    q->car = (sexp) r;

    int i = 0;
    for (;;)
    {
        r->text[i++] = c;

        c = *t++;

        if (!c) {
            while (i < sizeof(r->text))
                r->text[i++] = 0;
            return lose(1, p);
        }

        if (i == sizeof(r->text))
        {
            i = 0;
            q = q->cdr = cell();
            r = (Chunk*) cell();
            r->tags[0] = OTHER;
            r->tags[1] = CHUNK;
            q->car = (sexp) r;
        }
    }
}

/*
 * read Chunks terminated by some character
 */
sexp readChunks(FILE* fin, const char *ends)
{
    char c = getc(fin);

    sexp p = cell();
    sexp q = p;
    save(p);
    Chunk* r = (Chunk*) cell();
    r->tags[0] = OTHER;
    r->tags[1] = CHUNK;
    q->car = (sexp) r;

    for (int i = 0; ; )
    {
        r->text[i++] = c;

        c = getc(fin);

        if (strchr(ends, c))
        {
            while (i < sizeof(r->text))
                r->text[i++] = 0;
            ungetc(c, fin);
            return lose(1, p);
        }

        if (i == sizeof(r->text)) {
            q = q->cdr = cell();
            r = (Chunk*) cell();
            r->tags[0] = OTHER;
            r->tags[1] = CHUNK;
            q->car = (sexp) r;
            i = 0;
        }
    }
}

char whitespace(FILE* fin, char c)
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

    return c;
}

enum { NON_NUMERIC, INT_NUMERIC, FLO_NUMERIC };

/*
 * read an atom, number or string from the input stream
 */
sexp scan(FILE* fin)
{
    char buffer[32];
    char *p = buffer;
    char *pend = buffer + sizeof(buffer);

    char c = whitespace(fin, getc(fin));

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

        while (p < pend && '0' <= c && c <= '9')
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

        while (p < pend && '0' <= c && c <= '9')
        {
            *p++ = c;
            c = getc(fin);
        }

        if (NON_NUMERIC != rc && ('e' == c || 'E' == c))
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
            while (p < pend && '0' <= c && c <= '9')
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
        c = getc(fin);
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
    sexp r = save(readTail(fin));
    return lose(2, r && dot == r->car ? cons(q, r->cdr->car) : cons(q, r));
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

void intr_handler(int sig, siginfo_t *si, void *ctx)
{
    if (killed++)
        exit(0);
    if (SIGINT == sig)
        longjmp(the_jmpbuf, (long)"SIGINT");
}

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

        printf("#%2d 0x%016lx sp=0x%016lx %s + 0x%lx\n", ++n,
                static_cast<uintptr_t>(ip), static_cast<uintptr_t>(sp),
                name, static_cast<uintptr_t>(off));

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

    // set up all predefined atoms

    endl     = intern_atom_chunk("\n");
    adda     = intern_atom_chunk("add");
    ampera   = intern_atom_chunk("&");
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
    diva     = intern_atom_chunk("div");
    dot      = intern_atom_chunk(".");
    elsea    = intern_atom_chunk("else");
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
    lsha     = intern_atom_chunk("<<");
    lta      = intern_atom_chunk("<");
    minus    = intern_atom_chunk("-");
    moda     = intern_atom_chunk("mod");
    mula     = intern_atom_chunk("mul");
    newlinea = intern_atom_chunk("newline");
    nil      = intern_atom_chunk("#f");
    nota     = intern_atom_chunk("not");
    ora      = intern_atom_chunk("or");
    pipea    = intern_atom_chunk("|");
    powa     = intern_atom_chunk("pow");
    qchar    = intern_atom_chunk("'");
    quote    = intern_atom_chunk("quote");
    reada    = intern_atom_chunk("read");
    rparen   = intern_atom_chunk(")");
    rsha     = intern_atom_chunk(">>");
    seta     = intern_atom_chunk("set");
    setcara  = intern_atom_chunk("set-car");
    setcdra  = intern_atom_chunk("set-cdr");
    sina     = intern_atom_chunk("sin");
    sqrta    = intern_atom_chunk("sqrt");
    suba     = intern_atom_chunk("sub");
    tilde    = intern_atom_chunk("~");
    t        = intern_atom_chunk("#t");
    voida    = intern_atom_chunk("");
    whilea   = intern_atom_chunk("while");
    xora     = intern_atom_chunk("^");

    set(lambda, lambda);

    // set the definitions (special forms)
    set_form(anda,    andform);
    set_form(begin,   beginform);
    set_form(cond,    condform);
    set_form(define,  defineform);
    set_form(globals, globalform);
    set_form(ifa,     ifform);
    set_form(let,     letform);
    set_form(ora,     orform);
    set_form(quote,   quoteform);
    set_form(reada,   readform);
    set_form(seta,    setform);
    set_form(whilea,  whileform);

    // set the definitions (functions)
    set_funct(adda,     2, (void*)add);
    set_funct(ampera,   0, (void*)andfunc);
    set_funct(atoma,    1, (void*)atomp);
    set_funct(atomsa,   0, (void*)atomsfunc);
    set_funct(cara,     1, (void*)car);
    set_funct(cdra,     1, (void*)cdr);
    set_funct(consa,    2, (void*)cons);
    set_funct(cosa,     1, (void*)cosfunc);
    set_funct(displaya, 0, (void*)displayfunc);
    set_funct(diva,     2, (void*)divf);
    set_funct(eqva,     2, (void*)eqv);
    set_funct(expa,     1, (void*)expfunc);
    set_funct(gea,      2, (void*)ge);
    set_funct(gta,      2, (void*)gt);
    set_funct(lea,      2, (void*)le);
    set_funct(lista,    1, (void*)listp);
    set_funct(loada,    1, (void*)load);
    set_funct(loga,     1, (void*)logfunc);
    set_funct(lsha,     2, (void*)lsh);
    set_funct(lta,      2, (void*)lt);
    set_funct(moda,     2, (void*)mod);
    set_funct(mula,     2, (void*)mul);
    set_funct(newlinea, 0, (void*)newlinefunc);
    set_funct(nota,     1, (void*)isnot);
    set_funct(pipea,    0, (void*)orfunc);
    set_funct(powa,     2, (void*)powfunc);
    set_funct(rsha,     2, (void*)rsh);
    set_funct(setcara,  2, (void*)setcarfunc);
    set_funct(setcdra,  2, (void*)setcdrfunc);
    set_funct(sina,     1, (void*)sinfunc);
    set_funct(sqrta,    1, (void*)sqrtfunc);
    set_funct(suba,     2, (void*)sub);
    set_funct(tilde,    1, (void*)complement);
    set_funct(xora,     0, (void*)xorfunc);

    load(string(chunk("init.l")));

    struct sigaction intr_action;
    intr_action.sa_flags = SA_SIGINFO;
    intr_action.sa_sigaction = intr_handler;
    struct sigaction segv_action;
    segv_action.sa_flags = SA_SIGINFO;
    segv_action.sa_sigaction = segv_handler;
    char *s = (char*) sigsetjmp(the_jmpbuf, 1);
    if (s)
        printf(" caught %s!\n", s);

    sigaction(SIGSEGV, &segv_action, NULL);
    sigaction(SIGINT,  &intr_action, NULL);

    // read evaluate display ...
    while (!feof(stdin))
    {
        gc(true);
        total = 0;
        collected = 0;
        psp = protect;
        sexp e = read(stdin);
        killed = 0;
        sexp v = eval(e, global);
        if (voida != v)
        {
            display(stdout, v);
            putchar('\n');
        }
    }
    return 0;
}

