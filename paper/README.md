# Manuscript

This directory follows the publication layout of the companion `erdos-883`
repository: a single mathematical manuscript, a small macro file, a BibTeX
database, and a reproducible numerical supplement.

Build with:

```bash
cd paper
make pdf
```

The stable output is written to
`output/pdf/erdos-327-positive-density.pdf`.

The supplement reruns the exact rational certificate used for the strict
parameter inequalities and finite coordinate checks:

```bash
python3 paper/supplement/verify_certificate.py
```

The Lean project formalizes the full proof, including the specialized
analytic estimates. The standalone finite certificate remains a lightweight
independent check of the strict numerical parameter window.
