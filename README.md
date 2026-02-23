# rocq-carve

`rocq-carve` is a Rocq library for mechanizing substructural logics and languages.

## Requirements
- [Rocq 9.1.0](https://rocq-prover.org/)
- [Hammer tool for Rocq](https://rocq-prover.org/p/coq-hammer/), install via:

```bash
opam install coq-hammer
```

## Installation

```bash
$ ./configure
$ make
```

## Repository structure

```bash
rocq-carve/
├── src/          # Core library
│ ├── algebras/   # Resource algebras
│ └── contexts/   # Context representations
├── msl/          # Code originating from MSL (Appel, Dockins & Hobor, 2009–10)
├── autosubst/    # Code originating from Stark (2020)
└── case_studies/ # Sample developments showing library usage
```

## External links

- D. Zackon, C. Sano, A. Momigliano & B. Pientka. 2025. *[Split decisions: Explicit contexts for substructural languages](https://doi.org/10.1145/3703595.3705888)*. Proc. CPP '25. 257–271.
- K. Stark. 2020. *[Mechanising Syntax with Binders in Coq](https://www.ps.uni-saarland.de/~kstark/thesis/)*. PhD thesis. Saarland University.
- A. W. Appel, R. Dockins & A. Hobor. 2009–2010. [Mechanized Semantic Library](https://vst.cs.princeton.edu/msl/).