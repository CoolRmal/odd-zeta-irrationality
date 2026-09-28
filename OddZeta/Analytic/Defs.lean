import OddZeta.Setup.Rational
import OddZeta.Analysis.Stirling

/-!
# Gamma-function form of `Rₙ` and the phase function `f`

Section 4 of the note. `Rₙ(t) = (-sin πt/π)^r Gₙ(t)` with
`Gₙ(t) = Norm · (h₀+2t) Γ(-t)^r Γ(t+h₀)^r ∏_j Γ(t+hⱼ)/Γ(t+h₀-hⱼ+1)` (formula (4.6)), and by
Stirling's formula `Gₙ(nu) = Aₙ e^{n f(u)} Ĝ(u) (1 + O(1/n))` uniformly on suitable sets
(Lemma 4.3), with the phase function `f` of (4.1).
-/

namespace OddZeta

open Complex

namespace Params

variable (P : Params)

/-- The normalisation `Norm = ∏_{j>r} (h₀-2hⱼ)! / ∏_{j≤r} ((hⱼ-1)!)²`. -/
noncomputable def normG (n : ℕ) : ℝ :=
  (P.ps.map fun η => ((P.h0 n - 2 * hh η n).factorial : ℝ)).prod /
    (P.zs.map fun η => ((η * n).factorial : ℝ) ^ 2).prod

/-- `Gₙ(t)`, formula (4.6) of the note. -/
noncomputable def G (n : ℕ) (t : ℂ) : ℂ :=
  P.normG n * (P.h0 n + 2 * t) * Gamma (-t) ^ P.r * Gamma (t + P.h0 n) ^ P.r *
    ((P.zs ++ P.ps).map fun η =>
      Gamma (t + hh η n) / Gamma (t + P.h0 n - hh η n + 1)).prod

/-- `κ₀ = ∑_{j>r} (η₀-2ηⱼ) log(η₀-2ηⱼ) - 2 ∑_{j≤r} ηⱼ log ηⱼ`. -/
noncomputable def kappa0 : ℝ :=
  (P.ps.map fun η => ((P.eta0 - 2 * η : ℕ) : ℝ) * Real.log (P.eta0 - 2 * η : ℕ)).sum -
    2 * (P.zs.map fun η => (η : ℝ) * Real.log η).sum

/-- The phase function (4.1):
`f(u) = r[(-u) log(-u) + (η₀+u) log(η₀+u)] + ∑_j [(ηⱼ+u) log(ηⱼ+u) - (η₀-ηⱼ+u) log(η₀-ηⱼ+u)] + κ₀`
(principal branches). -/
noncomputable def f (u : ℂ) : ℂ :=
  P.r * (-u * log (-u) + (P.eta0 + u) * log (P.eta0 + u)) +
    ((P.zs ++ P.ps).map fun η : ℕ =>
      ((η : ℂ) + u) * log (η + u) - ((P.eta0 : ℂ) - η + u) * log (P.eta0 - η + u)).sum +
    P.kappa0

/-- The derivative `f'(u) = r[log(η₀+u) - log(-u)] + ∑_j [log(ηⱼ+u) - log(η₀-ηⱼ+u)]` (4.2). -/
noncomputable def f' (u : ℂ) : ℂ :=
  P.r * (log (P.eta0 + u) - log (-u)) +
    ((P.zs ++ P.ps).map fun η : ℕ => log (η + u) - log (P.eta0 - η + u)).sum

/-- `f''(u) = r[1/(η₀+u) - 1/u] + ∑_j [1/(ηⱼ+u) - 1/(η₀-ηⱼ+u)]` (4.3). -/
noncomputable def f'' (u : ℂ) : ℂ :=
  P.r * ((P.eta0 + u)⁻¹ - u⁻¹) +
    ((P.zs ++ P.ps).map fun η : ℕ => ((η : ℂ) + u)⁻¹ - ((P.eta0 : ℂ) - η + u)⁻¹).sum

/-- `f'''(u) = -r[1/(η₀+u)² - 1/u²] - ∑_j [1/(ηⱼ+u)² - 1/(η₀-ηⱼ+u)²]`. -/
noncomputable def f''' (u : ℂ) : ℂ :=
  -(P.r * (((P.eta0 + u) ^ 2)⁻¹ - (u ^ 2)⁻¹) +
    ((P.zs ++ P.ps).map fun η : ℕ => (((η : ℂ) + u) ^ 2)⁻¹ - (((P.eta0 : ℂ) - η + u) ^ 2)⁻¹).sum)

/-- The amplitude `Ĝ(u) = (η₀+2u) (-u)^{-r/2} (η₀+u)^{3r/2} ∏_j (ηⱼ+u)^{1/2} (η₀-ηⱼ+u)^{-3/2}`
(principal powers). -/
noncomputable def Ghat (u : ℂ) : ℂ :=
  (P.eta0 + 2 * u) * exp (-(P.r / 2 : ℂ) * log (-u) + (3 * P.r / 2 : ℂ) * log (P.eta0 + u) +
    ((P.zs ++ P.ps).map fun η : ℕ =>
      (1 / 2 : ℂ) * log (η + u) - (3 / 2 : ℂ) * log (P.eta0 - η + u)).sum)

/-- The constant `c₀ = ∏_{j>r} (η₀-2ηⱼ)^{1/2} / ∏_{j≤r} ηⱼ`. -/
noncomputable def c0 : ℝ :=
  (P.ps.map fun η => Real.sqrt (P.eta0 - 2 * η : ℕ)).prod / (P.zs.map fun η => (η : ℝ)).prod

/-- `Aₙ = (2π)^{(q-r)/2} c₀ n^{1-(q+r)/2}`. -/
noncomputable def An (n : ℕ) : ℝ :=
  (2 * Real.pi) ^ ((P.q - P.r) / 2) * P.c0 * (n : ℝ) ^ (1 - ((P.q + P.r) / 2 : ℕ) : ℤ)

variable {P}

/-- `Rₙ(t) = (-sin πt / π)^r Gₙ(t)` off the integers (reflection formula). -/
theorem R_eq_sin_pow_mul_G (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {t : ℂ}
    (ht : ∀ m : ℤ, t ≠ m) :
    P.R n t = (-sin (Real.pi * t) / Real.pi) ^ P.r * P.G n t := by
  sorry

/-- **Lemma 4.3** (Stirling): uniformly on a set `U` staying away from the branch points and the
zero of `η₀ + 2u`, `Gₙ(nu) = Aₙ e^{n f(u)} Ĝ(u) (1 + εₙ(u))` with `|εₙ(u)| ≤ C/n`. -/
theorem G_asymp (hP : P.Valid) {U : Set ℂ} {c ε₀ : ℝ} (hc : 0 < c) (hε₀ : 0 < ε₀)
    (hU₁ : ∀ u ∈ U, c ≤ ‖u‖) (hU₂ : ∀ u ∈ U, |(-u).arg| ≤ Real.pi - ε₀)
    (hU₃ : ∀ u ∈ U, c - P.etaOne ≤ u.re) (hU₄ : ∀ u ∈ U, c ≤ ‖(P.eta0 : ℂ) + 2 * u‖) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ U,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n := by
  sorry

end Params

end OddZeta
