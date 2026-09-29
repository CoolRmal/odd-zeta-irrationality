# At least one of ζ(7), …, ζ(21) and at least one of ζ(9), …, ζ(33) is irrational

A complete Lean 4 / Mathlib formalisation of the two main theorems of the note
[`higher_derivative_proof.pdf`](higher_derivative_proof.pdf) (September 2026):

* **Theorem 1.1** (`r = 5`): at least one of the eight numbers `ζ(7), ζ(9), …, ζ(21)` is
  irrational;
* **Theorem 1.2** (`r = 7`): at least one of the thirteen numbers `ζ(9), ζ(11), …, ζ(33)` is
  irrational.

The proof follows Zudilin's higher-derivative hypergeometric construction (W. Zudilin,
*Arithmetic of linear forms involving odd zeta values*, J. Théor. Nombres Bordeaux 16 (2004), §8)
as completed in the note: the linear forms `Fₙ = (1/(r-1)!) ∑ₜ Rₙ^{(r-1)}(t)`, their arithmetic
(Zudilin's Lemma 19 and the Chudnovsky–Rukhadze–Hata asymptotics, which need the prime number
theorem), and a saddle-point analysis of their size with certified numerical constants.

## Statements

`Challenge.lean` states the theorems, for Mathlib's `riemannZeta` (a value not equal to any
rational number) and for the real series `∑_{n≥1} 1/nˢ` (via `Irrational`):

```lean
theorem OddZeta.exists_zeta_ne_ratCast_of_seven_le_of_le_twentyone :
    ∃ s ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), ∀ q : ℚ, riemannZeta s ≠ q
theorem OddZeta.exists_zeta_ne_ratCast_of_nine_le_of_le_thirtythree :
    ∃ s ∈ ({9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33} : Finset ℕ),
      ∀ q : ℚ, riemannZeta s ≠ q
-- and `exists_irrational_tsum_of_…` : ∃ s ∈ …, Irrational (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s)
```

`Solution.lean` proves them. `lake comparator` (configured by `comparator.json`) checks that the
solution proves exactly these statements using only the axioms `propext`, `Quot.sound`,
`Classical.choice`; it runs in CI (`.github/workflows/ci.yml`, with `--paranoid`, i.e. the Lean
kernel and the bundled external checkers). Every numerical fact is checked by the Lean kernel
(`decide +kernel`); there is no `native_decide`.

## The proof

See [`BLUEPRINT.md`](BLUEPRINT.md) for the mathematical plan and the deviations from the note.
In short, for the direction vectors of the note (cases A and B):

1. **Linear forms** (`Setup/`): `Rₙ` is expanded in partial fractions with coefficients read off
   from power-series expansions at the poles; `Fₙ = ∑_{s} A_{s,n} ζ(s) - A_{0,n}` with `s` odd in
   `[r+2, q-2]` (Lemma 2.2).
2. **Denominators** (`Arith/`): `Δₙ A_{s,n} ∈ ℤ`, proved prime by prime from p-adic bounds for the
   Taylor coefficients of the "bricks" (Zudilin's Lemmas 15–19), with `Δₙ` built from the step
   function `φ' ≤ φ` of `Phi/`; `log Δₙ ≤ n(C₂' + o(1))` by the prime number theorem (`PNT/`, ported
   from PrimeNumberTheoremAnd), with `C₂' = 1616 - 678.6` (A) and `1946 - 774.1` (B).
3. **The function φ** (`Phi/`): a kernel-checked certificate of `φ(x) = min_y φ₀(x,y)` on all 3460
   (A) and 2230 (B) intervals of constancy, and rational lower bounds for the weighted sum `I'`.
4. **Analysis** (`Analysis/`, `Analytic/`): the integral representation
   `Fₙ = (1/π) Re ∫_{y≤0} S(M+iy) Gₙ(M+iy) dy` (Lipschitz formula with Eulerian numbers, reflection
   formula), Cauchy's theorem on discs to move the contour to a path `L` through the saddle point,
   complex Stirling in sectors (`Gₙ(nu) = Aₙ e^{n f(u)} Ĝ(u)(1 + O(1/n))`), Laplace's method on the
   segment through the saddle point, and monotone decay of `Re Fd` off it:
   `Fₙ = Kₙ (Im(e^{inα} B) + o(1))` with `(1/n) log Kₙ → H = -C₀` (Proposition 4.7).
5. **Numerics** (`Numerics/`, `Cert/`): verified interval bounds for `log`, `arctan`, `π`, `arg`
   evaluated by the kernel; existence of the exact saddle point by the contraction principle;
   `H < -939` (A), `H < -1175` (B); `α ∉ πℤ`; sign checks of `Re f'`, `Im f'` on 15–27 boxes along
   the path.
6. **Conclusion** (`Final/`): if all the `ζ(s)` were rational, `A Δₙ Fₙ` would be a nonzero
   integer (for infinitely many `n`) tending to `0`.

| Directory | Content | Lines |
|---|---|---|
| `PNT/` | prime number theorem (Wiener–Ikehara, ported from PrimeNumberTheoremAnd) | 2838 |
| `Algebra/` | partial fractions from local expansions | 193 |
| `Analysis/` | complex Stirling, Laplace's method, contour integrals, Lipschitz formula | 1548 |
| `Setup/` | parameters, `Rₙ`, coefficients `a_{i,k}`, linear form `Fₙ` | 779 |
| `Arith/` | p-adic brick bounds, `Δₙ A ∈ ℤ`, growth of `Δₙ` | 2193 |
| `Phi/` | certificate for `φ` and `I'` | 2549 |
| `Analytic/` | Gamma form, integral representation, deformation, Proposition 4.7 | 3238 |
| `Numerics/` | kernel-evaluable interval arithmetic | 3638 |
| `Cert/` | saddle-point certificates | 2401 |
| `Final/` | irrationality criterion and assembly | 393 |

`scripts/` contains the (untrusted) Python programs that reproduce the constants of the note
(`C₀ = 939.0301751743`, `C₂ = 936.8905456295` for A; `1175.7847344814`, `1171.2347981360` for B)
and generate the certificate data; the kernel re-checks everything.

## Building

```bash
lake exe cache get
lake build
lake comparator --config comparator.json   # Linux (needs bubblewrap)
```
