# Formalization notes

## Scope

The Lean development proves the theorem for every nonempty finite simple graph.
It does not assume connectivity. The graph is represented by mathlib's
`SimpleGraph V`, where `V` is finite.

The upper median is encoded by its order-statistic threshold characterization:
`upperMedianDegree G` is the greatest integer `m <= |V| - 1` for which at least
`ceil(|V|/2)` vertices have degree at least `m`. This is equivalent to the
degree in position `floor(|V|/2) + 1` after sorting increasingly, but avoids an
irrelevant choice of a sorted list.

## Correspondence with the written proof

| Written argument | Lean declaration |
| --- | --- |
| 2-dominating set | `TwoDominates` |
| 2-domination number | `twoDominationNumber` |
| Complementary nonneighbors | `nonneighbors` |
| Degree/nonneighbor partition | `neighborFinset_card_add_nonneighbors_card` |
| Minimal polynomial dependence | `MinimallyDependent` |
| Common-factor bound | `commonRoots_card_le` |
| Polynomial circuit selection | `polynomialCircuitSelection` |
| Small low-degree case | `exists_twoDominating_of_few_low_degree` |
| Polynomial case | `exists_twoDominating_of_many_low_degree` |
| Upper-median majority | `upperMedianDegree_majority` |
| Final set-valued theorem | `graffiti_pc_387` |
| Numerical corollary | `twoDominationNumber_le` |

The written proof chooses distinct real numbers for the roots. The Lean proof
uses distinct rational numbers obtained from a finite enumeration. This is a
strengthening of the algebraic setup and is sufficient because all required
linear-algebra and polynomial facts hold over `ℚ`.

## Trust and reproducibility

Lean reports that the final declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`, the standard foundational principles used
by mathlib. No project-specific axiom is introduced.

The repository pins the Lean and mathlib versions. The CI workflow additionally
scans every Lean source file for proof placeholders and custom axiom
declarations before compiling the project.

```bash
lake exe cache get
lake build
```
