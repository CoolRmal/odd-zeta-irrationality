import Mathlib

/-!
# Laplace's method on a segment

We prove an abstract version of Laplace's method (the saddle-point method) on a segment
`[-s₀, s₀]` with a complex quadratic phase: if `h s = -a s² + O(|s|³)` with `0 < Re a`,
`Re h s ≤ -b s²`, `g` is Lipschitz at `0` and `εₙ = O(1/n)`, then
`√n ∫_{-s₀}^{s₀} e^{n h(s)} g(s) (1 + εₙ(s)) ds → g(0) √(π / a)`.

The proof substitutes `s = x / √n` and applies dominated convergence on `ℝ`, with dominating
function `sup |g| · (1 + |C|) · e^{-b x²}`, and concludes with the complex Gaussian integral.
-/

namespace OddZeta
open Filter Topology MeasureTheory

/-- Laplace's method on `[-s₀, s₀]` with a complex quadratic phase. The square root is the
principal branch `Complex.cpow (π / a) (1/2)`. -/
theorem tendsto_sqrt_mul_integral_laplace
    {s₀ b M L C : ℝ} (hs₀ : 0 < s₀) (hb : 0 < b)
    {a : ℂ} (ha : 0 < a.re)
    {h g : ℝ → ℂ} (hh : ContinuousOn h (Set.Icc (-s₀) s₀)) (hg : ContinuousOn g (Set.Icc (-s₀) s₀))
    (h_taylor : ∀ s ∈ Set.Icc (-s₀) s₀, ‖h s + a * s ^ 2‖ ≤ M * |s| ^ 3)
    (h_re : ∀ s ∈ Set.Icc (-s₀) s₀, (h s).re ≤ -b * s ^ 2)
    (hg_lip : ∀ s ∈ Set.Icc (-s₀) s₀, ‖g s - g 0‖ ≤ L * |s|)
    (ε : ℕ → ℝ → ℂ) (hε_cont : ∀ n, ContinuousOn (ε n) (Set.Icc (-s₀) s₀))
    (hε : ∀ n, ∀ s ∈ Set.Icc (-s₀) s₀, ‖ε n s‖ ≤ C / n) :
    Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) *
        ∫ s in (-s₀)..s₀, Complex.exp (n * h s) * g s * (1 + ε n s))
      atTop (𝓝 (g 0 * (Real.pi / a) ^ (1 / 2 : ℂ))) := by
  -- Uniform bounds for `g` and `1 + εₙ` on the segment.
  set G : ℝ := ‖g 0‖ + |L| * s₀ with hG
  set K : ℝ := 1 + |C| with hK
  have hGnn : 0 ≤ G := by positivity
  have hKnn : 0 ≤ K := by positivity
  have hg_bd : ∀ s ∈ Set.Icc (-s₀) s₀, ‖g s‖ ≤ G := by
    intro s hs
    have h1 := hg_lip s hs
    have h2 : |s| ≤ s₀ := abs_le.2 hs
    have h3 : L * |s| ≤ |L| * s₀ :=
      calc L * |s| ≤ |L| * |s| := mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg s)
        _ ≤ |L| * s₀ := mul_le_mul_of_nonneg_left h2 (abs_nonneg L)
    calc ‖g s‖ = ‖g 0 + (g s - g 0)‖ := by congr 1; ring
      _ ≤ ‖g 0‖ + ‖g s - g 0‖ := norm_add_le _ _
      _ ≤ G := by rw [hG]; linarith
  have hε_bd : ∀ n : ℕ, 1 ≤ n → ∀ s ∈ Set.Icc (-s₀) s₀, ‖1 + ε n s‖ ≤ K := by
    intro n hn s hs
    have h1 := hε n s hs
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : C / n ≤ |C| :=
      calc C / n ≤ |C| / n := div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| := div_le_self (abs_nonneg C) hn'
    calc ‖1 + ε n s‖ ≤ ‖(1 : ℂ)‖ + ‖ε n s‖ := norm_add_le _ _
      _ ≤ K := by rw [hK, norm_one]; linarith
  -- The rescaled integrand, extended by zero to `ℝ`.
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ → ℂ, F = fun n : ℕ =>
      Set.indicator (Set.Ioc (-(s₀ * Real.sqrt n)) (s₀ * Real.sqrt n))
        (fun x => Complex.exp (n * h (x / Real.sqrt n)) * g (x / Real.sqrt n) *
          (1 + ε n (x / Real.sqrt n))) := ⟨_, rfl⟩
  have hmaps : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioc (-(s₀ * Real.sqrt n)) (s₀ * Real.sqrt n),
      x / Real.sqrt n ∈ Set.Icc (-s₀) s₀ := by
    intro n hn x hx
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    constructor
    · rw [le_div_iff₀ hsn]; linarith [hx.1]
    · rw [div_le_iff₀ hsn]; exact hx.2
  -- Step 1: the change of variables `s = x / √n`.
  have key : ∀ n : ℕ, 1 ≤ n → (Real.sqrt n : ℂ) *
      ∫ s in (-s₀)..s₀, Complex.exp (n * h s) * g s * (1 + ε n s) = ∫ x, F n x := by
    intro n hn
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    simp only [hF]
    rw [integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le (by nlinarith),
      intervalIntegral.integral_comp_div
        (fun s => Complex.exp (n * h s) * g s * (1 + ε n s)) hsn.ne',
      neg_div, mul_div_cancel_right₀ _ hsn.ne', Complex.real_smul]
  -- Step 2: dominated convergence.
  have hint : Integrable (fun x : ℝ => G * K * Real.exp (-b * x ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul (G * K)
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (F n) volume := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [hF]
    refine (aestronglyMeasurable_indicator_iff measurableSet_Ioc).2 ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    have hc : ContinuousOn (fun s => Complex.exp (n * h s) * g s * (1 + ε n s))
        (Set.Icc (-s₀) s₀) :=
      ((continuousOn_const.mul hh).cexp.mul hg).mul (continuousOn_const.add (hε_cont n))
    exact hc.comp (continuous_id.div_const _).continuousOn (hmaps n hn)
  have hbound : ∀ᶠ n in atTop, ∀ᵐ x ∂volume, ‖F n x‖ ≤ G * K * Real.exp (-b * x ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine Eventually.of_forall (fun x => ?_)
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    simp only [hF]
    by_cases hx : x ∈ Set.Ioc (-(s₀ * Real.sqrt n)) (s₀ * Real.sqrt n)
    · rw [Set.indicator_of_mem hx]
      have hs := hmaps n hn x hx
      have hns : (n : ℝ) * (x / Real.sqrt n) ^ 2 = x ^ 2 := by
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        field_simp
      have he : Real.exp ((n * h (x / Real.sqrt n) : ℂ).re) ≤ Real.exp (-b * x ^ 2) := by
        apply Real.exp_le_exp.2
        have : ((n : ℂ) * h (x / Real.sqrt n)).re = n * (h (x / Real.sqrt n)).re := by
          simp [Complex.mul_re]
        rw [this]
        calc (n : ℝ) * (h (x / Real.sqrt n)).re ≤ n * (-b * (x / Real.sqrt n) ^ 2) :=
              mul_le_mul_of_nonneg_left (h_re _ hs) (Nat.cast_nonneg n)
          _ = -b * x ^ 2 := by rw [← hns]; ring
      rw [norm_mul, norm_mul, Complex.norm_exp]
      calc Real.exp ((n * h (x / Real.sqrt n) : ℂ).re) * ‖g (x / Real.sqrt n)‖ *
            ‖1 + ε n (x / Real.sqrt n)‖ ≤ Real.exp (-b * x ^ 2) * G * K :=
            mul_le_mul (mul_le_mul he (hg_bd _ hs) (norm_nonneg _) (Real.exp_pos _).le)
              (hε_bd n hn _ hs) (norm_nonneg _) (by positivity)
        _ = G * K * Real.exp (-b * x ^ 2) := by ring
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim_pt : ∀ x : ℝ, Tendsto (fun n => F n x) atTop
      (𝓝 (g 0 * Complex.exp (-a * x ^ 2))) := by
    intro x
    have hev : ∀ᶠ n : ℕ in atTop,
        1 ≤ n ∧ x ∈ Set.Ioc (-(s₀ * Real.sqrt n)) (s₀ * Real.sqrt n) := by
      have h1 : ∀ᶠ n : ℕ in atTop, |x| < s₀ * Real.sqrt n :=
        (hsqrt.const_mul_atTop hs₀).eventually_gt_atTop |x|
      filter_upwards [eventually_ge_atTop 1, h1] with n hn hn1
      refine ⟨hn, ?_, ?_⟩
      · linarith [neg_abs_le x]
      · linarith [le_abs_self x]
    -- the phase
    have hA : Tendsto (fun n : ℕ => (n : ℂ) * h (x / Real.sqrt n)) atTop
        (𝓝 (-a * x ^ 2)) := by
      rw [← tendsto_sub_nhds_zero_iff]
      refine squeeze_zero_norm' ?_
        ((tendsto_const_nhds (x := M * |x| ^ 3)).div_atTop hsqrt)
      filter_upwards [hev] with n ⟨hn, hx⟩
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
      have hs := hmaps n hn x hx
      have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
      have hsqC : ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := by exact_mod_cast hsq
      have hsnC : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsn.ne'
      have eq1 : (n : ℂ) * h (x / Real.sqrt n) - -a * x ^ 2 =
          (n : ℂ) * (h (x / Real.sqrt n) + a * ((x / Real.sqrt n : ℝ) : ℂ) ^ 2) := by
        rw [Complex.ofReal_div, div_pow, hsqC]
        have hnC : (n : ℂ) ≠ 0 := by rw [← hsqC]; exact pow_ne_zero 2 hsnC
        field_simp
        ring
      rw [eq1, norm_mul, Complex.norm_natCast]
      calc (n : ℝ) * ‖h (x / Real.sqrt n) + a * ((x / Real.sqrt n : ℝ) : ℂ) ^ 2‖
          ≤ n * (M * |x / Real.sqrt n| ^ 3) :=
            mul_le_mul_of_nonneg_left (h_taylor _ hs) (Nat.cast_nonneg n)
        _ = M * |x| ^ 3 / Real.sqrt n := by
            rw [abs_div, abs_of_pos hsn]
            generalize Real.sqrt n = t at hsq hsn ⊢
            rw [← hsq]
            field_simp
    -- the amplitude
    have hB : Tendsto (fun n : ℕ => g (x / Real.sqrt n)) atTop (𝓝 (g 0)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
        ((tendsto_const_nhds (x := |L| * |x|)).div_atTop hsqrt)
      filter_upwards [hev] with n ⟨hn, hx⟩
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
      calc ‖g (x / Real.sqrt n) - g 0‖ ≤ L * |x / Real.sqrt n| := hg_lip _ (hmaps n hn x hx)
        _ ≤ |L| * |x / Real.sqrt n| :=
            mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
        _ = |L| * |x| / Real.sqrt n := by rw [abs_div, abs_of_pos hsn, mul_div_assoc]
    -- the error term
    have hC : Tendsto (fun n : ℕ => ε n (x / Real.sqrt n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
      filter_upwards [hev] with n ⟨hn, hx⟩
      exact hε n _ (hmaps n hn x hx)
    have hmain : Tendsto (fun n : ℕ => Complex.exp (n * h (x / Real.sqrt n)) *
        g (x / Real.sqrt n) * (1 + ε n (x / Real.sqrt n))) atTop
        (𝓝 (Complex.exp (-a * x ^ 2) * g 0 * (1 + 0))) :=
      (((Complex.continuous_exp.tendsto _).comp hA).mul hB).mul (tendsto_const_nhds.add hC)
    rw [add_zero, mul_one, mul_comm] at hmain
    refine hmain.congr' ?_
    filter_upwards [hev] with n ⟨hn, hx⟩
    simp only [hF]
    rw [Set.indicator_of_mem hx]
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (fun x : ℝ => G * K * Real.exp (-b * x ^ 2)) hmeas hbound hint
    (Eventually.of_forall hlim_pt)
  rw [integral_const_mul, integral_gaussian_complex ha] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (key n hn).symm

end OddZeta
