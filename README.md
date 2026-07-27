# A Proof of Graffiti.pc Conjecture 387

[![Lean proof verification](https://github.com/qscqesze/graffiti-pc-conjecture-387/actions/workflows/lean.yml/badge.svg)](https://github.com/qscqesze/graffiti-pc-conjecture-387/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21621226.svg)](https://doi.org/10.5281/zenodo.21621226)

This repository contains Jun Qing's proof of Graffiti.pc Conjecture 387, a
Chinese translation, and a complete machine-checked formalization in Lean 4.

## Main result

Let `G` be a nonempty finite simple graph of order `n`, and arrange its degree
sequence in nondecreasing order:

$$d_1 \le d_2 \le \cdots \le d_n.$$

Set $m(G)=d_{\lfloor n/2\rfloor+1}$, the upper median degree. If
$\gamma_2(G)$ is the 2-domination number, then

$$\boxed{\gamma_2(G)\le n-m(G)+1}.$$

This proves Graffiti.pc Conjecture 387. The proof actually establishes the
stronger statement for every nonempty finite simple graph; connectivity is not
needed.

## Machine verification

The formalization uses Lean 4.32.1 and mathlib v4.32.1, pinned by
[`lean-toolchain`](./lean-toolchain) and [`lake-manifest.json`](./lake-manifest.json).
It contains no `sorry`, `admit`, or custom axiom declarations.

- [`Graffiti387/Polynomial.lean`](./Graffiti387/Polynomial.lean) proves the
  minimally dependent root-polynomial lemma and the circuit-selection lemma.
- [`Graffiti387/Main.lean`](./Graffiti387/Main.lean) defines 2-domination and
  the upper median degree, proves the graph theorem, and derives the numerical
  bound for $\gamma_2$.
- [`Graffiti387/Verification.lean`](./Graffiti387/Verification.lean) prints the
  foundational dependencies of both final theorems.
- [GitHub Actions](./.github/workflows/lean.yml) rejects proof placeholders and
  rebuilds the formal proof on every push and pull request.

To verify locally:

```bash
lake exe cache get
lake build
```

The two final declarations are:

```lean
Graffiti387.graffiti_pc_387
Graffiti387.twoDominationNumber_le
```

See [Formalization notes](./FORMALIZATION.md) and the
[Chinese verification guide](./formalization_zh.md) for the precise mapping
between the written and Lean proofs.

## Written proof

- [Original proof (PDF)](./output/pdf/graffiti387_Jun_Qing.pdf)
- [Chinese translation](./proof_zh.md)

## Citation

Citation metadata is provided in [`CITATION.cff`](./CITATION.cff). On the
GitHub repository page, select **Cite this repository** to generate a BibTeX or
APA citation.

Suggested citation:

> Qing, Jun. (2026). *The 2-Domination Number and the Upper Median Degree: A
> Proof of Graffiti.pc Conjecture 387* (v1.0.0). Zenodo.
> https://doi.org/10.5281/zenodo.21621226

## Keywords

2-domination, domination number, degree sequence, upper median degree,
Graffiti.pc, graph theory, Lean 4, mathlib.
