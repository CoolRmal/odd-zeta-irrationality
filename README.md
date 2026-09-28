# At least one of ζ(7), …, ζ(21) and at least one of ζ(9), …, ζ(33) is irrational

A Lean 4 / Mathlib formalisation (in progress) of the two main theorems of the note
[`higher_derivative_proof.pdf`](higher_derivative_proof.pdf):

* **Theorem 1.1** (`r = 5`): at least one of `ζ(7), ζ(9), …, ζ(21)` is irrational;
* **Theorem 1.2** (`r = 7`): at least one of `ζ(9), ζ(11), …, ζ(33)` is irrational.

The proof follows Zudilin's higher-derivative hypergeometric construction
(W. Zudilin, *Arithmetic of linear forms involving odd zeta values*, J. Théor. Nombres Bordeaux
16 (2004), §8): the linear forms `Fₙ = (1/(r-1)!) ∑ₜ Rₙ^{(r-1)}(t)`, their arithmetic
(Zudilin's Lemma 19 and the Chudnovsky–Rukhadze–Hata asymptotics, which need the prime number
theorem), and a saddle-point analysis of their size with certified numerical constants.

## Statements

`Challenge.lean` states the theorems (for Mathlib's `riemannZeta`, and for the real series
`∑ 1/nˢ`); `Solution.lean` proves them, and `lake comparator` (configured by
`comparator.json`) checks that the proofs prove exactly these statements from the standard
axioms `propext`, `Quot.sound`, `Classical.choice` (no `native_decide`).

## Status

Work in progress — see the commit history and [`BLUEPRINT.md`](BLUEPRINT.md) (the mathematical
plan and the deviations from the note). The development lives in `OddZeta/`; `scripts/` contains
the (untrusted) Python programs used to design the certificates.

| Module | Content | Status |
|---|---|---|
| `PNT/` | prime number theorem `θ(x) ~ x` (ported from PrimeNumberTheoremAnd) | proved |
| `Algebra/PartialFractions` | partial fractions from local expansions | proved |
| `Analysis/Stirling` | complex Stirling formula in sectors | proved |
| `Analysis/Laplace` | Laplace's method on a segment | proved |
| `Analysis/Contour`, `VerticalLine` | polygonal Cauchy theorem on discs, vertical-line integrals | proved |
| `Analysis/CotSeries` | `∑ₘ (t-m)^{-r} sin^r(πt)` = Eulerian trigonometric polynomial | proved |
| `Arith/Valuation`, `Bricks` | p-adic bounds for brick expansions (Zudilin's Lemmas 15–18) | proved |
| `Final/Assembly` | the irrationality criterion | proved |
| `Setup/` | `Rₙ`, partial-fraction coefficients, linear form `Fₙ` (Lemma 2.2) | in progress |
| `Arith/Delta`, `DeltaGrowth` | denominators `Δₙ` (Lemma 3.2) and their growth (Lemma 3.3) | in progress |
| `Phi/` | kernel-checked certificate for `φ` and the constant `C₂` | in progress |
| `Analytic/` | integral representation, contour deformation, Prop. 4.7 | in progress |
| `Numerics/`, `Cert/` | verified interval arithmetic; saddle-point certificates | in progress |

## Building

```bash
lake exe cache get
lake build
lake comparator --config comparator.json
```
