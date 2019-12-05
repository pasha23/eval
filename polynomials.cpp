
#include <iostream>

using namespace std;

#include <stdlib.h>

typedef unsigned long word;

const unsigned word_size = 8 * sizeof(word);

/*
 * construct the identity bit matrix
 */
void identity(unsigned N, word *r)
{
    for (int j = N; --j >= 0; )
        r[j] = (word)1 << j;
}

/*
 * multiply the bit matrix r by the polynomial t in integer representation
 */
void multiply(unsigned N, word *r, word t)
{
    for (unsigned j = 0; j < N; ++j)
    {
        if (j+1 < N)
            r[j] = r[j+1];
        else
            r[j] = 0;
        if (((word)1 << j) & t)
            r[j] ^= 1;
    }
}

/*
 * square the bit matrix r
 */
void square(unsigned N, word *r, word *s)
{
    for (int i = N; --i >= 0; )
    {
        s[i] = 0;
        for (int j = N; --j >= 0; )
            if (r[i] & ((word)1 << j))
                s[i] ^= r[j];
    }
}

/*
 * given the bit matrix representation r of a polynomial and the
 * current contents of the shift register x, shift once and return the result
 */
word shift(unsigned N, word *r, word x)
{
    word y = 0;

    for (unsigned j = 0; j < N; ++j)
        for (unsigned k = 0; k < N; ++k)
            if (x & r[j] & ((word)1 << k))
                y ^= (word)1 << j;

    return y;
}

/*
 * load x into a shift register described by the polynomial t
 * shift the register n times and return the result`
 */
word raise(unsigned N, word n, word x, word t)
{
    word r[N], s[N];

    identity(N, r);

    multiply(N, r, t);

    for (;;)
    {
        if (n > 0)
        {
            if (n & 1)
                x = shift(N, r, x);
            square(N, r, s);
            n >>= 1;
        } else
            return x;

        if (n > 0)
        {
            if (n & 1)
                x = shift(N, s, x);
            square(N, s, r);
            n >>= 1;
        } else
            return x;
    }
}

/*
 * return a zero terminated array of factors of 2^N-1
 */
const word * const factor(unsigned N)
{
    static word factors[12];
    word m = ~(word)0>>(word_size-N); // 2^N-1

    // compute test factors 2^N-1 / p
    // where p is a prime factor of 2^N-1
    word p = 2;
    word *fp = factors;
    for (word a = m; 1 < a; )
    {
        if (a % p == 0) {
            do
                a /= p;
            while (a % p == 0);
            *fp++ = m / p;
        } else if (p * p > a) {
            *fp++ = m / a;
            a = 1;
        } else
            ++p;
    }
    *fp++ = 0;

    return factors;
}

/*
 * construct reciprocal polynomial of t
 */
word reciprocal(unsigned N, word t)
{
    word s = 1;

    for (int i = N-1; --i >= 0; )
    {
        s = (s << 1) | (t & 1); t >>= 1;
    }

    return s;
}

/*
 * each call returns a new irreducible polynomial over GF(2^N) until 0
 * each returned polynomial x has an irreducible reciprocal(x)
 * that generates the same m-sequence backwards
 */
word polynomials(unsigned N, const word * const factors, word t)
{
    if (N == 0)
        return 0;

    if (t == 0)
    {
        if (N <= 2)
            return ((word)1 << N) - 1;
        else
            t = (word)1 << (N-1);
    }

    word m = ~(word)0>>(word_size-N);   // 2^N-1

    for ( ; ++t & ((word)1<<N)-1; )
    {
        if ( ! __builtin_parityl((unsigned long)t) && t < reciprocal(N, t) && m == raise(N, m, m, t))
        {
            // x * t^m == x
            const word *fp = factors;
            while (*fp > 1 && m != raise(N, *fp, m, t))
                ++fp;
            // x * t^f != x
            if (*fp <= 1)
                return t;
        }
    }

    return 0;
}

void sift(unsigned n)
{
    const word * const factors = factor(n);
    for (word t = 0; (t = polynomials(n, factors, t)); )
    {
        if (n > 0)
            cout << ", ";
        cout << t;
        cout.flush();
        return;
    }
}

int main(int argc, char **argv, char **envp)
{
    cout << "(define polynomials [ 0";
    for (unsigned n = 1; n <= word_size; ++n)
        sift(n);
    cout << " ])\n";
    return 0;
}

