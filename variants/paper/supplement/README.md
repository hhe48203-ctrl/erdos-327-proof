# Numerical supplement

`verify_certificate.py` is a self-contained standard-library verifier for the
finite and numerical content of the manuscript. It has no dependencies, uses
exact integer and rational arithmetic throughout, and runs in a few seconds.

It checks, in nine groups:

1. the closed-form universal periodic witness, and the resulting benchmark
   densities (1/2 for odd k, 0 for even k);
2. the conflict criterion `a+b | kab  <=>  x/(x,k) | g`;
3. the two-adic restriction on odd conflicts and the mod-4 splitting at k=2;
4. the generalised source coordinates for an arbitrary modulus, including
   `u >= L`, `x > L`, and the exact L-smooth part;
5. the two-endpoint mixed coordinates for odd k with the dilation
   lambda(k) = least power of two >= max(2,k), their converse, the exclusion
   u >= L of the small-u families, a NEGATIVE CONTROL recording why the naive
   dilation 2 is fatal when 3 | k or 5 | k, and the at-most-one-large-prime
   fact behind flagged item 4 of the manuscript;
6. the root counts `3p-2` for both linear-form triples and the p=2 factor;
7. the complete small- and large-prime Euler factors for both triples,
   including the modified factors at primes dividing the multiplier;
8. the five strict parameter inequalities, with rational logarithm intervals
   of width below 1e-80, plus the symbolic cancellation of the log L
   exponents to -3/2 (source) and -2 (mixed);
9. the largest-prime-factor fibration and its contraction constant log 2 < 1;
10. that the assembled two-layer set really is k-admissible, in a finite box,
    for k = 1, 3, 5, 7, 9. This checks the combinatorics of the assembly only.
    The density gain is asymptotic and requires L and N chosen in the legal
    order, so no box can establish it.

Run from any working directory:

```bash
python3 paper/supplement/verify_certificate.py
```

The reference transcript is in `certificate-output.txt`.

These checks certify arithmetic, local densities and the numerical window.
They are not evidence for the two analytic mean-value inputs.
