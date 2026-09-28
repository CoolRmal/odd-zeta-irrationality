import OddZeta.Analytic.Defs
import OddZeta.Analysis.CotSeries
import OddZeta.Analysis.VerticalLine

/-!
# The integral representation of `Fₙ` (Lemma 4.1 and (4.7) of the note)

With `M = 1/2 - h₁` and `S = trigS r` (so that `∑ₘ (t-m)^{-r} = π^r S(t)/sin^r(πt)`):
`Fₙ = (1/2πi) ∫_{Re t = M} S(t) Gₙ(t) dt = (1/π) Re ∫_{-∞}^{0} S(M+iy) Gₙ(M+iy) dy`.

Proof: `∫_{Re t=M} Rₙ(t)(t-m)^{-r} dt = -2πi ρₙ(m)` if `m > M` and `0` if `m < M` (partial fractions
and `integral_vert_partialFractions`); summing over `m ∈ ℤ` (Fubini) and using the Lipschitz
formula and `Rₙ = (-sin πt/π)^r Gₙ` gives the first identity; the second follows from the
symmetry `S(t̄)Gₙ(t̄) = conj(S(t)Gₙ(t))`.
-/

namespace OddZeta

open Complex MeasureTheory

namespace Params

variable (P : Params)

/-- The abscissa `M = 1/2 - h₁` of the line of integration. -/
noncomputable def lineM (n : ℕ) : ℝ := 1 / 2 - (hh P.etaOne n : ℝ)

/-- The integrand `S(M+iy) Gₙ(M+iy)` on the line `Re t = M`. -/
noncomputable def lineIntegrand (n : ℕ) (y : ℝ) : ℂ :=
  trigS P.r (P.lineM n + y * I) * P.G n (P.lineM n + y * I)

variable {P}

/-- **Integral representation** of `Fₙ`. -/
theorem F_eq_integral (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (P.lineIntegrand n) ∧
      P.F n = (∫ y in Set.Iic (0 : ℝ), P.lineIntegrand n y).re / Real.pi := by
  sorry

end Params

end OddZeta
