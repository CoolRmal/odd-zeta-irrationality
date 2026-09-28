import OddZeta.Setup.Rational
import OddZeta.Analysis.Stirling
import OddZeta.Analytic.GammaAux

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

open GammaAux

/-! ### Auxiliary lemmas -/

/-- `Gₙ(t) = (h₀+2t) ∏_{j≤r} [zero block] ∏_{j>r} [pole block]`, regrouping the factors of `Gₙ`. -/
private lemma G_eq_prod_blocks (n : ℕ) (t : ℂ) :
    P.G n t = (P.h0 n + 2 * t) *
      (P.zs.map fun η => Gamma (-t) * Gamma (t + P.h0 n) *
        (Gamma (t + hh η n) / Gamma (t + P.h0 n - hh η n + 1)) /
          ((η * n).factorial : ℂ) ^ 2).prod *
      (P.ps.map fun η => ((P.h0 n - 2 * hh η n).factorial : ℂ) *
        (Gamma (t + hh η n) / Gamma (t + P.h0 n - hh η n + 1))).prod := by
  simp only [G, normG, List.map_append, List.prod_append, GammaAux.list_prod_map_div,
    List.prod_map_mul, GammaAux.list_prod_map_const]
  push_cast [GammaAux.ofReal_list_prod]
  simp only [r]
  ring

/-- `c₀ = exp(∑_{j>r} ½ log(η₀-2ηⱼ) - ∑_{j≤r} log ηⱼ)`. -/
private lemma c0_eq_exp (hP : P.Valid) :
    (P.c0 : ℂ) = exp ((P.ps.map fun η => (1 / 2 : ℂ) * log ((P.eta0 - 2 * η : ℕ) : ℂ)).sum -
      (P.zs.map fun η : ℕ => log (η : ℂ)).sum) := by
  rw [c0]
  simp only [bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def]
  rw [Complex.exp_sub, exp_list_sum, exp_list_sum, List.map_map, List.map_map,
    Complex.ofReal_div, GammaAux.ofReal_list_prod, GammaAux.ofReal_list_prod]
  congr 1
  · refine congrArg List.prod (List.map_congr_left fun η hη => ?_)
    have h1 : 0 < P.eta0 - 2 * η := by have := hP.two_mul_lt η hη; omega
    have hpos : (0 : ℝ) < ((P.eta0 - 2 * η : ℕ) : ℝ) := by exact_mod_cast h1
    simp only [Function.comp]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.natCast_log]
    push_cast
    ring_nf
  · refine congrArg List.prod (List.map_congr_left fun η hη => ?_)
    have h1 : 0 < η := by
      have := hP.etaOne_le η hη
      have := hP.etaOne_pos
      omega
    have hη0 : (η : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
    simp only [Function.comp, Complex.exp_log hη0, Complex.ofReal_natCast]


/-- The main term `Aₙ e^{n f(u)} Ĝ(u)` as the product of the Stirling main terms of the Gamma
factors of `Gₙ(nu)`, i.e. `n(η₀+2u) (2π)^{(q-r)/2} exp(∑ stirT)`. -/
private lemma main_term (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) (u : ℂ) :
    (P.An n : ℂ) * exp (n * P.f u) * P.Ghat u =
      n * (P.eta0 + 2 * u) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ P.ps.length *
        exp ((P.zs.map fun η : ℕ => stirT n (-u) 0 + stirT n (P.eta0 + u) 2 + stirT n (η + u) 1 -
            stirT n (P.eta0 - η + u) 2 - 2 * stirT n η 1).sum +
          (P.ps.map fun η : ℕ => stirT n (η + u) 1 - stirT n (P.eta0 - η + u) 2 +
            stirT n (P.eta0 - 2 * η : ℕ) 1).sum) := by
  obtain ⟨m, hm⟩ : ∃ m, P.ps.length = 2 * m := by
    obtain ⟨a, ha⟩ := hP.r_odd
    obtain ⟨b, hb⟩ := hP.q_odd
    simp only [r, q] at ha hb
    exact ⟨P.ps.length / 2, by omega⟩
  have hqr1 : (P.q - P.r) / 2 = m := by simp only [q, r]; omega
  have hqr2 : (P.q + P.r) / 2 = P.r + m := by simp only [q, r]; omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  set L : ℂ := (Real.log n : ℂ) with hL
  have hexpL : exp L = n := by
    rw [hL, ← Complex.ofReal_exp, Real.exp_log hnpos, Complex.ofReal_natCast]
  set A : ℂ := -u * log (-u) + (P.eta0 + u) * log (P.eta0 + u) with hA
  set Ga : ℂ := -(1 / 2 : ℂ) * log (-u) + (3 / 2 : ℂ) * log (P.eta0 + u) with hGa
  have hEz : ∀ η ∈ P.zs, (stirT n (-u) 0 + stirT n (P.eta0 + u) 2 + stirT n (η + u) 1 -
      stirT n (P.eta0 - η + u) 2 - 2 * stirT n η 1) =
      ((n : ℂ) * A + Ga - L) + ((n : ℂ) * (((η : ℂ) + u) * log (η + u) -
          ((P.eta0 : ℂ) - η + u) * log (P.eta0 - η + u)) +
        ((1 / 2 : ℂ) * log (η + u) - (3 / 2 : ℂ) * log (P.eta0 - η + u))) -
      (2 * (n : ℂ) * ((η : ℂ) * log η) + log η) := by
    intro η _
    simp only [stirT, hA, hGa, hL]
    push_cast
    ring
  have hEp : ∀ η ∈ P.ps, (stirT n (η + u) 1 - stirT n (P.eta0 - η + u) 2 +
      stirT n (P.eta0 - 2 * η : ℕ) 1) =
      ((n : ℂ) * (((η : ℂ) + u) * log (η + u) - ((P.eta0 : ℂ) - η + u) * log (P.eta0 - η + u)) +
        ((1 / 2 : ℂ) * log (η + u) - (3 / 2 : ℂ) * log (P.eta0 - η + u))) +
      ((n : ℂ) * (((P.eta0 - 2 * η : ℕ) : ℂ) * log ((P.eta0 - 2 * η : ℕ) : ℂ)) +
        (1 / 2 : ℂ) * log ((P.eta0 - 2 * η : ℕ) : ℂ) - (1 / 2 : ℂ) * L) := by
    intro η hη
    have h2 : 2 * η ≤ P.eta0 := (hP.two_mul_lt η hη).le
    have hζ : ((P.eta0 - 2 * η : ℕ) : ℂ) = P.eta0 - 2 * η := by
      rw [Nat.cast_sub h2]; push_cast; ring
    simp only [stirT, ← hL]
    push_cast
    linear_combination ((n : ℂ) * L - n) * hζ
  have e1 : (P.zs.map fun η : ℕ => stirT n (-u) 0 + stirT n (P.eta0 + u) 2 + stirT n (η + u) 1 -
            stirT n (P.eta0 - η + u) 2 - 2 * stirT n η 1).sum +
          (P.ps.map fun η : ℕ => stirT n (η + u) 1 - stirT n (P.eta0 - η + u) 2 +
            stirT n (P.eta0 - 2 * η : ℕ) 1).sum =
      n * P.f u + (-(P.r / 2 : ℂ) * log (-u) + (3 * P.r / 2 : ℂ) * log (P.eta0 + u) +
        ((P.zs ++ P.ps).map fun η : ℕ =>
          (1 / 2 : ℂ) * log (η + u) - (3 / 2 : ℂ) * log (P.eta0 - η + u)).sum) +
      ((P.ps.map fun η => (1 / 2 : ℂ) * log ((P.eta0 - 2 * η : ℕ) : ℂ)).sum -
        (P.zs.map fun η : ℕ => log (η : ℂ)).sum) - ((P.r + m : ℕ) : ℂ) * L := by
    rw [List.map_congr_left hEz, List.map_congr_left hEp]
    simp only [f, kappa0, bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def,
      List.map_append, List.sum_append, List.sum_map_add, GammaAux.list_sum_map_sub,
      List.sum_map_mul_left, GammaAux.list_sum_map_const, Complex.ofReal_sub, Complex.ofReal_mul,
      GammaAux.ofReal_list_sum, Complex.ofReal_natCast, Complex.natCast_log, Complex.ofReal_ofNat]
    simp only [r, hA, hGa]
    rw [hm]
    push_cast
    ring
  have hAn : (P.An n : ℂ) = (2 * Real.pi : ℂ) ^ m * P.c0 *
      (n : ℂ) ^ ((1 : ℤ) - ((P.r + m : ℕ) : ℤ)) := by
    simp only [An, hqr1, hqr2]
    push_cast
    ring
  have hzpow : (n : ℂ) ^ ((1 : ℤ) - ((P.r + m : ℕ) : ℤ)) =
      n / exp (((P.r + m : ℕ) : ℂ) * L) := by
    rw [zpow_sub₀ hN0, zpow_one, zpow_natCast, Complex.exp_nat_mul, hexpL]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ P.ps.length = (2 * Real.pi : ℂ) ^ m := by
    rw [hm, pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have hG : P.Ghat u = (P.eta0 + 2 * u) * exp (-(P.r / 2 : ℂ) * log (-u) +
      (3 * P.r / 2 : ℂ) * log (P.eta0 + u) + ((P.zs ++ P.ps).map fun η : ℕ =>
        (1 / 2 : ℂ) * log (η + u) - (3 / 2 : ℂ) * log (P.eta0 - η + u)).sum) := rfl
  rw [e1, hG, hAn, hzpow, hs, c0_eq_exp hP]
  simp only [Complex.exp_add, Complex.exp_sub]
  ring

/-- Stirling for a zero block `Γ(-nu)Γ(nu+h₀)Γ(nu+h)/(Γ(nu+h₀-h+1)((h-1)!)²)`. -/
private lemma zero_elem {n : ℕ} {u : ℂ} {B : ℝ} (Q : ℂ → Prop)
    (hS : ∀ b : ℕ, b ≤ 2 → ∀ ζ : ℂ, Q ζ → ∃ μ : ℂ, ‖μ‖ ≤ B ∧
      Gamma (n * ζ + b) = Real.sqrt (2 * Real.pi) * exp (stirT n ζ b + μ))
    {η : ℕ} (h1 : Q (-u)) (h2 : Q (P.eta0 + u)) (h3 : Q (η + u)) (h4 : Q (P.eta0 - η + u))
    (h6 : Q η) :
    ∃ ν : ℂ, ‖ν‖ ≤ 6 * B ∧
      Gamma (-(n * u)) * Gamma (n * u + P.h0 n) *
        (Gamma (n * u + hh η n) / Gamma (n * u + P.h0 n - hh η n + 1)) /
          ((η * n).factorial : ℂ) ^ 2 =
      1 * exp ((stirT n (-u) 0 + stirT n (P.eta0 + u) 2 + stirT n (η + u) 1 -
            stirT n (P.eta0 - η + u) 2 - 2 * stirT n η 1) + ν) := by
  obtain ⟨μ1, hμ1, e1⟩ := hS 0 (by norm_num) _ h1
  obtain ⟨μ2, hμ2, e2⟩ := hS 2 le_rfl _ h2
  obtain ⟨μ3, hμ3, e3⟩ := hS 1 (by norm_num) _ h3
  obtain ⟨μ4, hμ4, e4⟩ := hS 2 le_rfl _ h4
  obtain ⟨μ6, hμ6, e6⟩ := hS 1 (by norm_num) _ h6
  have g1 : Gamma (-(n * u)) = Gamma (n * (-u) + ((0 : ℕ) : ℂ)) := by
    congr 1; push_cast; ring
  have g2 : Gamma (n * u + P.h0 n) = Gamma (n * (P.eta0 + u) + ((2 : ℕ) : ℂ)) := by
    congr 1; simp only [h0]; push_cast; ring
  have g3 : Gamma (n * u + hh η n) = Gamma (n * (η + u) + ((1 : ℕ) : ℂ)) := by
    congr 1; simp only [hh]; push_cast; ring
  have g4 : Gamma (n * u + P.h0 n - hh η n + 1) =
      Gamma (n * (P.eta0 - η + u) + ((2 : ℕ) : ℂ)) := by
    congr 1; simp only [h0, hh]; push_cast; ring
  have g6 : ((η * n).factorial : ℂ) = Gamma (n * η + ((1 : ℕ) : ℂ)) := by
    rw [← Complex.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
  rw [g1, g2, g3, g4, g6, e1, e2, e3, e4, e6]
  refine ⟨μ1 + μ2 + μ3 - μ4 - 2 * μ6, ?_, ?_⟩
  · have ha := norm_sub_le (μ1 + μ2 + μ3 - μ4) (2 * μ6)
    have hb := norm_sub_le (μ1 + μ2 + μ3) μ4
    have hc := norm_add_le (μ1 + μ2) μ3
    have hd := norm_add_le μ1 μ2
    have h2 : ‖(2 : ℂ) * μ6‖ = 2 * ‖μ6‖ := by rw [norm_mul]; norm_num
    linarith
  · have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; positivity
    rw [show stirT n (-u) 0 + stirT n (P.eta0 + u) 2 + stirT n (η + u) 1 -
          stirT n (P.eta0 - η + u) 2 - 2 * stirT n η 1 + (μ1 + μ2 + μ3 - μ4 - 2 * μ6) =
        (stirT n (-u) 0 + μ1) + (stirT n (P.eta0 + u) 2 + μ2) + (stirT n (η + u) 1 + μ3) -
          (stirT n (P.eta0 - η + u) 2 + μ4) - (stirT n η 1 + μ6) - (stirT n η 1 + μ6) by ring]
    simp only [Complex.exp_add, Complex.exp_sub]
    field_simp

/-- Stirling for a pole block `(h₀-2h)! Γ(nu+h)/Γ(nu+h₀-h+1)`. -/
private lemma pole_elem {n : ℕ} {u : ℂ} {B : ℝ} (Q : ℂ → Prop)
    (hS : ∀ b : ℕ, b ≤ 2 → ∀ ζ : ℂ, Q ζ → ∃ μ : ℂ, ‖μ‖ ≤ B ∧
      Gamma (n * ζ + b) = Real.sqrt (2 * Real.pi) * exp (stirT n ζ b + μ))
    {η : ℕ} (h3 : Q (η + u)) (h4 : Q (P.eta0 - η + u)) (h5 : Q ((P.eta0 - 2 * η : ℕ) : ℂ)) :
    ∃ ν : ℂ, ‖ν‖ ≤ 3 * B ∧
      ((P.h0 n - 2 * hh η n).factorial : ℂ) *
        (Gamma (n * u + hh η n) / Gamma (n * u + P.h0 n - hh η n + 1)) =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * exp ((stirT n (η + u) 1 -
          stirT n (P.eta0 - η + u) 2 + stirT n (P.eta0 - 2 * η : ℕ) 1) + ν) := by
  obtain ⟨μ3, hμ3, e3⟩ := hS 1 (by norm_num) _ h3
  obtain ⟨μ4, hμ4, e4⟩ := hS 2 le_rfl _ h4
  obtain ⟨μ5, hμ5, e5⟩ := hS 1 (by norm_num) _ h5
  have g3 : Gamma (n * u + hh η n) = Gamma (n * (η + u) + ((1 : ℕ) : ℂ)) := by
    congr 1; simp only [hh]; push_cast; ring
  have g4 : Gamma (n * u + P.h0 n - hh η n + 1) =
      Gamma (n * (P.eta0 - η + u) + ((2 : ℕ) : ℂ)) := by
    congr 1; simp only [h0, hh]; push_cast; ring
  have g5 : ((P.h0 n - 2 * hh η n).factorial : ℂ) =
      Gamma (n * ((P.eta0 - 2 * η : ℕ) : ℂ) + ((1 : ℕ) : ℂ)) := by
    have hnat : P.h0 n - 2 * hh η n = (P.eta0 - 2 * η) * n := by
      rw [Nat.sub_mul, mul_assoc]; simp only [h0, hh]; omega
    rw [hnat, ← Complex.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
  rw [g3, g4, g5, e3, e4, e5]
  refine ⟨μ3 - μ4 + μ5, ?_, ?_⟩
  · have ha := norm_add_le (μ3 - μ4) μ5
    have hb := norm_sub_le μ3 μ4
    linarith
  · have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; positivity
    rw [show stirT n (η + u) 1 - stirT n (P.eta0 - η + u) 2 + stirT n (P.eta0 - 2 * η : ℕ) 1 +
          (μ3 - μ4 + μ5) = (stirT n (η + u) 1 + μ3) - (stirT n (P.eta0 - η + u) 2 + μ4) +
          (stirT n (P.eta0 - 2 * η : ℕ) 1 + μ5) by ring]
    simp only [Complex.exp_add, Complex.exp_sub]
    field_simp

private lemma ratio_aux {w N s X Y ν₁ ν₂ : ℂ} (k j : ℕ) (hw : w ≠ 0) (hN : N ≠ 0)
    (hs : s ≠ 0) :
    (N * w + 2) * (1 ^ k * exp (X + ν₁)) * (s ^ j * exp (Y + ν₂)) /
        (N * w * s ^ j * exp (X + Y)) = (1 + 2 / (N * w)) * exp (ν₁ + ν₂) := by
  simp only [one_pow, one_mul, Complex.exp_add]
  field_simp

/-- `Rₙ(t) = (-sin πt / π)^r Gₙ(t)` off the integers (reflection formula). -/
theorem R_eq_sin_pow_mul_G (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {t : ℂ}
    (ht : ∀ m : ℤ, t ≠ m) :
    P.R n t = (-sin (Real.pi * t) / Real.pi) ^ P.r * P.G n t := by
  have ht' : ∀ k ∈ P.poleRange n, t + k ≠ 0 := fun k _ h =>
    ht (-k) (by push_cast; linear_combination h)
  have hzs_le : ∀ η ∈ P.zs, hh η n ≤ P.h0 n := by
    intro η hη
    have h1 := hP.zs_le_etaMin η hη
    have h2 := hP.two_mul_lt _ hP.etaMin_mem
    simp only [hh, h0]
    nlinarith
  have hps_le : ∀ η ∈ P.ps, 2 * hh η n ≤ P.h0 n := by
    intro η hη
    have h2 := hP.two_mul_lt _ hη
    simp only [hh, h0]
    nlinarith
  have hz : P.zs.map (fun η => (∏ i ∈ Finset.Ico 1 (hh η n), (t + i)) *
        (∏ i ∈ Finset.Ico (P.h0 n - hh η n + 1) (P.h0 n), (t + i)) /
          ((η * n).factorial : ℂ) ^ 2) =
      P.zs.map (fun η => Gamma (t + hh η n) / Gamma (t + P.h0 n - hh η n + 1) *
        (Gamma (t + P.h0 n) / Gamma (t + 1)) / ((η * n).factorial : ℂ) ^ 2) := by
    refine List.map_congr_left fun η hη => ?_
    have h1 := hzs_le η hη
    have h2 : 1 ≤ hh η n := by simp [hh]
    rw [GammaAux.prod_Ico_eq_Gamma_div ht h2, GammaAux.prod_Ico_eq_Gamma_div ht (by omega)]
    push_cast [Nat.cast_sub h1]
    have := GammaAux.Gamma_add_nat_ne_zero ht 1
    have := GammaAux.Gamma_add_nat_ne_zero ht (P.h0 n - hh η n + 1)
    push_cast [Nat.cast_sub h1] at this
    rw [show t + ((P.h0 n : ℂ) - hh η n + 1) = t + P.h0 n - hh η n + 1 by ring] at *
    field_simp
  have hp : P.ps.map (fun η => ((P.h0 n - 2 * hh η n).factorial : ℂ) /
        ∏ i ∈ Finset.Icc (hh η n) (P.h0 n - hh η n), (t + i)) =
      P.ps.map (fun η => ((P.h0 n - 2 * hh η n).factorial : ℂ) *
        (Gamma (t + hh η n) / Gamma (t + P.h0 n - hh η n + 1))) := by
    refine List.map_congr_left fun η hη => ?_
    have h1 := hps_le η hη
    rw [← Finset.Ico_add_one_right_eq_Icc, GammaAux.prod_Ico_eq_Gamma_div ht (by omega)]
    push_cast [Nat.cast_sub (show hh η n ≤ P.h0 n by omega)]
    rw [show t + ((P.h0 n : ℂ) - hh η n + 1) = t + P.h0 n - hh η n + 1 by ring]
    rw [div_div_eq_mul_div, mul_div_assoc]
  rw [R_eq_prod hP hn ht', hz, hp]
  simp only [G, normG, List.map_append, List.prod_append, GammaAux.list_prod_map_div,
    List.prod_map_mul, GammaAux.list_prod_map_const]
  push_cast [GammaAux.ofReal_list_prod]
  rw [div_eq_mul_inv (Gamma (t + P.h0 n) ^ _), ← inv_pow, ← GammaAux.neg_sin_div_mul_Gamma ht]
  simp only [r]
  ring

/-- **Lemma 4.3** (Stirling): uniformly on a set `U` staying away from the branch points and the
zero of `η₀ + 2u`, `Gₙ(nu) = Aₙ e^{n f(u)} Ĝ(u) (1 + εₙ(u))` with `|εₙ(u)| ≤ C/n`. -/
theorem G_asymp (hP : P.Valid) {U : Set ℂ} {c ε₀ : ℝ} (hc : 0 < c) (hε₀ : 0 < ε₀)
    (hU₁ : ∀ u ∈ U, c ≤ ‖u‖) (hU₂ : ∀ u ∈ U, |(-u).arg| ≤ Real.pi - ε₀)
    (hU₃ : ∀ u ∈ U, c - P.etaOne ≤ u.re) (hU₄ : ∀ u ∈ U, c ≤ ‖(P.eta0 : ℂ) + 2 * u‖) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ U,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n := by
  set ε := min ε₀ (Real.pi / 2) with hε
  have hεpos : 0 < ε := lt_min hε₀ (by positivity)
  have hεle : ε ≤ Real.pi / 2 := min_le_right _ _
  have hεle' : ε ≤ ε₀ := min_le_left _ _
  set c' := min c 1 with hc'
  have hc'pos : 0 < c' := lt_min hc one_pos
  obtain ⟨K, N₀, hK, hN₀, hS⟩ := GammaAux.exists_Gamma_scaled hεpos hc'pos
  set Q : ℂ → Prop := fun ζ => c' ≤ ‖ζ‖ ∧ |ζ.arg| ≤ Real.pi - ε with hQ
  have hQre : ∀ ζ : ℂ, c ≤ ζ.re → Q ζ := by
    intro ζ hζ
    refine ⟨(min_le_left _ _).trans (hζ.trans (Complex.re_le_norm ζ)), ?_⟩
    have := Complex.abs_arg_le_pi_div_two_iff.mpr (by linarith : 0 ≤ ζ.re)
    linarith [Real.pi_pos]
  have hQnat : ∀ m : ℕ, 1 ≤ m → Q (m : ℂ) := by
    intro m hm
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_natCast]
      exact (min_le_right _ _).trans (by exact_mod_cast hm)
    · rw [Complex.natCast_arg, abs_zero]
      linarith [Real.pi_pos]
  have hη1 : ∀ η ∈ P.zs ++ P.ps, P.etaOne ≤ η ∧ η + P.etaOne < P.eta0 := by
    intro η hη
    have h1 := hP.zs_le_etaMin _ hP.etaOne_mem
    have h2 := hP.two_mul_lt _ hP.etaMin_mem
    rcases List.mem_append.mp hη with h | h
    · have := hP.etaOne_le η h
      have := hP.zs_le_etaMin η h
      omega
    · have := hP.etaMin_le η h
      have := hP.two_mul_lt η h
      omega
  have hη0 : P.etaOne ≤ P.eta0 := by
    have := (hη1 _ (List.mem_append_left _ hP.etaOne_mem)).2
    omega
  refine ⟨12 * P.q * K + 6 / c, ⌈max N₀ (6 * P.q * K)⌉₊, ?_⟩
  intro n hn u hu
  have hnN : max N₀ (6 * P.q * K) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hnN₀ : N₀ ≤ n := (le_max_left _ _).trans hnN
  have hnq : 6 * P.q * K ≤ n := (le_max_right _ _).trans hnN
  have hn1' : (1 : ℝ) ≤ n := hN₀.trans hnN₀
  have hn1 : 1 ≤ n := by exact_mod_cast hn1'
  have hnpos : (0 : ℝ) < n := by linarith
  have hSn : ∀ b : ℕ, b ≤ 2 → ∀ ζ : ℂ, Q ζ → ∃ μ : ℂ, ‖μ‖ ≤ K / n ∧
      Gamma (n * ζ + b) = Real.sqrt (2 * Real.pi) * exp (stirT n ζ b + μ) :=
    fun b hb ζ hζ => hS n hnN₀ b hb ζ hζ.1 hζ.2
  have hu3 := hU₃ u hu
  have hQ1 : Q (-u) :=
    ⟨(min_le_left _ _).trans (by rw [norm_neg]; exact hU₁ u hu), (hU₂ u hu).trans (by linarith)⟩
  have hQ2 : Q (P.eta0 + u) := hQre _ (by
    have : (P.etaOne : ℝ) ≤ P.eta0 := by exact_mod_cast hη0
    simp only [Complex.add_re, Complex.natCast_re]
    linarith)
  have hQ3 : ∀ η ∈ P.zs ++ P.ps, Q (η + u) := fun η hη => hQre _ (by
    have : (P.etaOne : ℝ) ≤ η := by exact_mod_cast (hη1 η hη).1
    simp only [Complex.add_re, Complex.natCast_re]
    linarith)
  have hQ4 : ∀ η ∈ P.zs ++ P.ps, Q (P.eta0 - η + u) := fun η hη => hQre _ (by
    have : (η : ℝ) + P.etaOne ≤ P.eta0 := by exact_mod_cast (hη1 η hη).2.le
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re]
    linarith)
  obtain ⟨ν₁, hν₁, hz⟩ := GammaAux.list_prod_eq_exp P.zs _ _ 1 (6 * (K / n)) (fun η hη =>
    zero_elem Q hSn hQ1 hQ2 (hQ3 η (List.mem_append_left _ hη))
      (hQ4 η (List.mem_append_left _ hη))
      (hQnat η (by
        have := (hη1 η (List.mem_append_left _ hη)).1
        have := hP.etaOne_pos
        omega)))
  obtain ⟨ν₂, hν₂, hp⟩ := GammaAux.list_prod_eq_exp P.ps _ _ _ (3 * (K / n)) (fun η hη =>
    pole_elem Q hSn (hQ3 η (List.mem_append_right _ hη)) (hQ4 η (List.mem_append_right _ hη))
      (hQnat _ (by have := hP.two_mul_lt η hη; omega)))
  have hw : (P.eta0 : ℂ) + 2 * u ≠ 0 := by
    intro h
    have := hU₄ u hu
    rw [h, norm_zero] at this
    linarith
  have hN0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have hh0 : (P.h0 n : ℂ) + 2 * (n * u) = n * (P.eta0 + 2 * u) + 2 := by
    simp only [h0]; push_cast; ring
  rw [G_eq_prod_blocks, hz, hp, main_term hP hn1 u, hh0, ratio_aux _ _ hw hN0 hs]
  have hq : (P.q : ℝ) = P.zs.length + P.ps.length := by simp [q]
  have hKn : 0 ≤ K / n := by positivity
  have hν : ‖ν₁ + ν₂‖ ≤ 6 * P.q * K / n := by
    have := norm_add_le ν₁ ν₂
    have e : 6 * P.q * K / n = 6 * P.zs.length * (K / n) + 6 * P.ps.length * (K / n) := by
      rw [hq]; ring
    rw [e]
    have : (P.ps.length : ℝ) * (3 * (K / n)) ≤ 6 * P.ps.length * (K / n) := by
      have : (0 : ℝ) ≤ P.ps.length * (K / n) := by positivity
      nlinarith
    nlinarith
  have hB : 6 * P.q * K / n ≤ 1 := by rw [div_le_one hnpos]; exact hnq
  have ha : ‖(2 : ℂ) / (n * (P.eta0 + 2 * u))‖ ≤ 2 / (n * c) := by
    rw [norm_div, norm_mul, Complex.norm_natCast]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    gcongr
    exact hU₄ u hu
  refine (GammaAux.norm_one_add_mul_exp_sub_one_le ha hν hB).trans (le_of_eq ?_)
  field_simp
  ring

end Params

end OddZeta
