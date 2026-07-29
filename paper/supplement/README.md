# Numerical supplement

`verify_certificate.py` runs the repository's canonical standard-library
verifier. It checks the exact mixed-conflict coordinates in finite boxes, the
local root count, the complete mixed Euler factors at sample primes, the
strict parameter window by rational intervals for logarithms, and the exact
logarithmic exponent cancellation.

Run from any working directory:

```bash
python3 paper/supplement/verify_certificate.py
```

The reference transcript is in `certificate-output.txt`.
