import OddZeta.Analytic.SaddleAsymp

/-!
# Path-independent pieces of the saddle-point asymptotics

Versions of `tendsto_piece`, `tendsto_ray` (from `SaddleAux3`) for an arbitrary set `U` on which
Stirling's formula holds uniformly, instead of the set `D.pathSet` of a `PathData`. The ray is
only assumed to satisfy `Re Fd ≤ H - b` and the linear decay `Re Fd(x + iy) ≤ K + c y`.
-/

namespace OddZeta

open Complex MeasureTheory Filter Topology

namespace Params

variable {P : Params}

/-- A piece of a path parametrised over a compact interval, on which `Re Fd ≤ H - κ`, contributes
`O(√n e^{-κn})` relative to `Aₙ e^{nH}`. -/
theorem tendsto_piece_gen (hP : P.Valid) {U : Set ℂ} (hU : ∀ z ∈ U, (P.eta0 : ℂ) + 2 * z ≠ 0)
    {H C : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hE : ∀ n ≥ N, ∀ u ∈ U,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n)
    {γ : ℝ → ℂ} {a₁ a₂ M κ : ℝ} (hκ : 0 < κ)
    (hγ : ∀ t ∈ Set.uIcc a₁ a₂, γ t ∈ U ∧ (γ t).im ≤ 0 ∧
      (P.Fd (γ t)).re ≤ H - κ ∧ ‖P.Ghat (γ t)‖ ≤ M) :
    Tendsto (fun n : ℕ => (P.Qn H n : ℂ) *
      ∫ t in a₁..a₂, trigS P.r (n * γ t) * P.G n (n * γ t)) atTop (𝓝 0) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hγ a₁ Set.left_mem_uIcc).2.2.2
  set K : ℝ := ((P.r - 1).factorial : ℝ) * (2 * (1 + |C|) * M * |a₂ - a₁|)
  refine squeeze_zero_norm' ?_ (tendsto_sqrt_mul_exp_neg hκ K)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn1 : 1 ≤ n := hN.trans hn
  have hA := An_pos hP hn1
  have hbound : ∀ t ∈ Set.uIoc a₁ a₂, ‖trigS P.r (n * γ t) * P.G n (n * γ t)‖ ≤
      2 * (1 + |C|) * M * (P.An n * Real.exp (n * (H - κ))) := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hγ t (Set.uIoc_subset_uIcc ht)
    refine (norm_integrand_le hP hn1 h2 (Ghat_ne_zero (hU _ h1)) (hE n hn _ h1)).trans ?_
    have h5 : Real.exp (n * (P.Fd (γ t)).re) ≤ Real.exp (n * (H - κ)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n))
    calc 2 * (1 + |C|) * P.An n * Real.exp (n * (P.Fd (γ t)).re) * ‖P.Ghat (γ t)‖
        ≤ 2 * (1 + |C|) * P.An n * Real.exp (n * (H - κ)) * M := by gcongr
      _ = _ := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Qn_nonneg hP H hn1)]
  calc P.Qn H n * ‖∫ t in a₁..a₂, trigS P.r (n * γ t) * P.G n (n * γ t)‖
      ≤ P.Qn H n * (2 * (1 + |C|) * M * (P.An n * Real.exp (n * (H - κ))) * |a₂ - a₁|) :=
        mul_le_mul_of_nonneg_left hint (Qn_nonneg hP H hn1)
    _ = 2 * (1 + |C|) * M * |a₂ - a₁| * (P.Qn H n * (P.An n * Real.exp (n * (H - κ)))) := by
        ring
    _ = K * Real.sqrt n * Real.exp (-κ * n) := by rw [Qn_mul hP H κ hn1]; ring

/-- A segment `[A, B]` on which `Re Fd ≤ H - κ` (and all logarithms are holomorphic)
contributes `o(Kₙ)`. -/
theorem tendsto_segInt_gen (hP : P.Valid) {U : Set ℂ} (hU : ∀ z ∈ U, (P.eta0 : ℂ) + 2 * z ≠ 0)
    {H C : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hE : ∀ n ≥ N, ∀ u ∈ U,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n)
    {A B : ℂ} {κ : ℝ} (hκ : 0 < κ)
    (hAB : ∀ z ∈ segment ℝ A B, z ∈ U ∧ z.im ≤ 0 ∧ P.Good z ∧ (P.Fd z).re ≤ H - κ) :
    Tendsto (fun n : ℕ => (P.Qn H n : ℂ) *
      segInt (fun u => trigS P.r (n * u) * P.G n (n * u)) A B) atTop (𝓝 0) := by
  set γ : ℝ → ℂ := fun t => A + (t : ℂ) * (B - A) with hγ
  have hγc : Continuous γ := by rw [hγ]; fun_prop
  have hI : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ segment ℝ A B := fun t ht =>
    add_mul_sub_mem_segment ht
  obtain ⟨M, hM⟩ : ∃ M, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖P.Ghat (γ t)‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn fun t ht =>
      ((continuousAt_Ghat (hAB _ (hmem t ht)).2.2.1).comp hγc.continuousAt).continuousWithinAt
  have key := tendsto_piece_gen hP hU hN hE (γ := γ) (a₁ := 0) (a₂ := 1) (M := M) hκ
    (fun t ht => by
      rw [hI] at ht
      obtain ⟨h1, h2, -, h4⟩ := hAB _ (hmem t ht)
      exact ⟨h1, h2, h4, hM t ht⟩)
  have key2 := key.mul_const (B - A)
  rw [zero_mul] at key2
  refine key2.congr fun n => ?_
  rw [segInt, intervalIntegral.integral_mul_const]
  ring

/-- The vertical ray `{xR + iy : y ≤ yR}`, on which `Re Fd ≤ H - b` and
`Re Fd(xR + iy) ≤ K + c y`, contributes `o(Kₙ)`. -/
theorem tendsto_ray_gen (hP : P.Valid) {U : Set ℂ} (hU : ∀ z ∈ U, (P.eta0 : ℂ) + 2 * z ≠ 0)
    {H C : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hE : ∀ n ≥ N, ∀ u ∈ U,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n)
    {xR yR b c K : ℝ} (hyR : yR < 0) (hb : 0 < b) (hc : 0 < c)
    (hmem : ∀ y ≤ yR, (xR : ℂ) + y * I ∈ U)
    (hH : ∀ y ≤ yR, (P.Fd (xR + y * I)).re ≤ H - b)
    (hK : ∀ y ≤ yR, (P.Fd (xR + y * I)).re ≤ K + c * y) :
    Tendsto (fun n : ℕ => (P.Qn H n : ℂ) * ((∫ y in Set.Iic yR,
      trigS P.r (n * (xR + y * I)) * P.G n (n * (xR + y * I))) * I)) atTop (𝓝 0) := by
  have hβ : 0 < -yR := by linarith
  set PR : ℂ := (xR : ℂ) + yR * I with hPR
  set A : ℝ := 2 * P.r + 2 * (P.zs ++ P.ps).length with hA_def
  have hA0 : 0 ≤ A := by positivity
  set A₁ : ℝ := 2 + A with hA₁_def
  have hA₁ : 0 ≤ A₁ := by positivity
  set A₀ : ℝ := P.eta0 + A * (|Real.log (-yR)| + 2 * P.eta0) + A₁ * ‖PR‖ with hA₀_def
  -- growth of `Ĝ` along the ray
  have hGb : ∀ y ≤ yR, ‖P.Ghat (xR + y * I)‖ ≤ Real.exp (A₀ + A₁ * (yR - y)) := by
    intro y hy
    have him : -yR ≤ |((xR : ℂ) + y * I).im| := by
      have : ((xR : ℂ) + y * I).im = y := by simp
      rw [this, abs_of_neg (by linarith)]
      linarith
    have h1 := norm_Ghat_le hP hβ him
    have hu : ‖(xR : ℂ) + y * I‖ ≤ ‖PR‖ + (yR - y) := by
      have e : (xR : ℂ) + y * I = PR + ((y - yR : ℝ) : ℂ) * I := by
        rw [hPR]; push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      linarith
    refine h1.trans (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_left hu hA₁
    rw [hA₀_def]
    rw [hA₁_def] at this ⊢
    nlinarith
  -- the number of factors `e^{Re Fd}` used for the linear decay
  set m : ℝ := (A₁ + c) / c with hm
  have hm0 : 0 ≤ m := by positivity
  have hmc : m * c = A₁ + c := by rw [hm]; field_simp
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge m
  set Z : ℝ := m * (K - H + b) + A₀ + A₁ * yR with hZ
  set K' : ℝ := ((P.r - 1).factorial : ℝ) * (2 * (1 + |C|) * Real.exp (Z + c * yR) / c) with hK'
  refine squeeze_zero_norm' ?_ (tendsto_sqrt_mul_exp_neg hb K')
  filter_upwards [eventually_ge_atTop (max N n₁)] with n hn
  have hnN : N ≤ n := le_of_max_le_left hn
  have hn1 : 1 ≤ n := hN.trans hnN
  have hnm : m ≤ n := hn₁.trans (by exact_mod_cast le_of_max_le_right hn)
  have hAn := An_pos hP hn1
  set B₀ : ℝ := 2 * (1 + |C|) * (P.An n * Real.exp (n * (H - b))) * Real.exp Z with hB₀
  have hbound : ∀ y ∈ Set.Iic yR,
      ‖trigS P.r (n * (xR + y * I)) * P.G n (n * (xR + y * I))‖ ≤ B₀ * Real.exp (c * y) := by
    intro y hy
    have hy' : y ≤ yR := hy
    have hmem' := hmem y hy'
    have him : ((xR : ℂ) + y * I).im ≤ 0 := by simp; linarith
    refine (norm_integrand_le hP hn1 him (Ghat_ne_zero (hU _ hmem'))
      (hE n hnN _ hmem')).trans ?_
    have h1 : (n : ℝ) * (P.Fd (xR + y * I)).re ≤ (n - m) * (H - b) + m * (K + c * y) := by
      have e1 := mul_le_mul_of_nonneg_left (hH y hy') (sub_nonneg.2 hnm)
      have e2 := mul_le_mul_of_nonneg_left (hK y hy') hm0
      linarith
    have h2 := hGb y hy'
    have e3 : m * (K + c * y) = m * K + (A₁ + c) * y := by rw [mul_add, ← mul_assoc, hmc]
    have h3 : (n : ℝ) * (P.Fd (xR + y * I)).re + (A₀ + A₁ * (yR - y)) ≤
        n * (H - b) + Z + c * y := by
      rw [hZ]; nlinarith
    have h4 : 0 ≤ 2 * (1 + |C|) * P.An n := by positivity
    calc 2 * (1 + |C|) * P.An n * Real.exp (n * (P.Fd (xR + y * I)).re) *
          ‖P.Ghat (xR + y * I)‖
        ≤ 2 * (1 + |C|) * P.An n * Real.exp (n * (P.Fd (xR + y * I)).re) *
          Real.exp (A₀ + A₁ * (yR - y)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * (1 + |C|) * P.An n *
          Real.exp (n * (P.Fd (xR + y * I)).re + (A₀ + A₁ * (yR - y))) := by
          rw [Real.exp_add (n * (P.Fd (xR + y * I)).re) (A₀ + A₁ * (yR - y))]; ring
      _ ≤ 2 * (1 + |C|) * P.An n * Real.exp (n * (H - b) + Z + c * y) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) h4
      _ = B₀ * Real.exp (c * y) := by
          rw [hB₀, Real.exp_add, Real.exp_add]; ring
  have hint : IntegrableOn (fun y => B₀ * Real.exp (c * y)) (Set.Iic yR) :=
    (integrableOn_exp_mul_Iic hc _).const_mul B₀
  have hI := norm_integral_le_of_norm_le hint
    (ae_restrict_of_forall_mem measurableSet_Iic hbound)
  rw [integral_const_mul, integral_exp_mul_Iic hc] at hI
  have hE' : Real.exp Z * Real.exp (c * yR) = Real.exp (Z + c * yR) := by
    rw [← Real.exp_add]
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Qn_nonneg hP H hn1)]
  calc P.Qn H n * ‖∫ y in Set.Iic yR,
        trigS P.r (n * (xR + y * I)) * P.G n (n * (xR + y * I))‖
      ≤ P.Qn H n * (B₀ * (Real.exp (c * yR) / c)) :=
        mul_le_mul_of_nonneg_left hI (Qn_nonneg hP H hn1)
    _ = 2 * (1 + |C|) * Real.exp (Z + c * yR) / c *
          (P.Qn H n * (P.An n * Real.exp (n * (H - b)))) := by
        rw [hB₀, ← hE']; ring
    _ = K' * Real.sqrt n * Real.exp (-b * n) := by
        rw [Qn_mul hP H b hn1, hK']; ring

end Params

end OddZeta
