# Manuscript

This directory follows the layout of the repository's main manuscript in
`../../paper/`: a single mathematical manuscript, a small macro file, a BibTeX
database, and a reproducible numerical supplement.

Build with:

```bash
cd paper
make pdf
```

The stable output is written to `variants/output/pdf/erdos-327-variants.pdf`,
and a committed copy lives at `variants/erdos-327-variants-della-pietra.pdf`.

The supplement reruns the exact rational certificate used for the periodic
benchmark witnesses, the finite coordinate checks, the local Euler factors,
and the strict parameter inequalities:

```bash
python3 paper/supplement/verify_certificate.py
```

There is no Lean development for this companion. Formalization is planned and
has not been done; see the "Flagged items" section of the manuscript. The
repository's Lean project, in `../../lean/`, covers the main manuscript only.
