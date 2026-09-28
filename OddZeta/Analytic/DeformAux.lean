import OddZeta.Analytic.Defs
import OddZeta.Analysis.CotSeries
import OddZeta.Analysis.Contour

/-!
# Auxiliary lemmas for the deformation of the contour (`F_eq_im_pathInt`)

* `Deform.deform_ray`: a vertical ray `{Re t = x₀, Im t ≤ 0}` ending at a real point `x₀` can be
  replaced by a vertical ray below a point `z₀` of the lower half-plane followed by a polygonal path
  from `z₀` to `x₀`, for a function holomorphic off the real axis and on a real interval containing
  `x₀`, decaying exponentially as `Im t → -∞` (Cauchy's theorem on large discs
  `B(c - iR, √(R² + w²))`, whose trace on the real axis is `(c - w, c + w)`).
* Regularity, conjugation symmetry and exponential decay of `t ↦ trigS r t · Gₙ(t)`.
-/

namespace OddZeta

namespace Deform

open Complex MeasureTheory Set Filter Topology ComplexConjugate

/-! ### Discs through a real interval -/

lemma mem_ball_lower_iff {c w R : ℝ} {z : ℂ} :
    z ∈ Metric.ball ((c : ℂ) - R * I) (Real.sqrt (R ^ 2 + w ^ 2)) ↔
      (z.re - c) ^ 2 + (z.im + R) ^ 2 < R ^ 2 + w ^ 2 := by
  rw [Metric.mem_ball, dist_eq_norm, Real.lt_sqrt (norm_nonneg _), Complex.sq_norm,
    Complex.normSq_apply]
  simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    sub_im, mul_im, add_zero, zero_sub, sub_neg_eq_add]
  constructor <;> intro h <;> nlinarith

lemma eventually_mem_ball_lower {c w : ℝ} {z : ℂ}
    (hz : z.im < 0 ∨ (z.im = 0 ∧ |z.re - c| < w)) :
    ∀ᶠ R : ℝ in atTop, z ∈ Metric.ball ((c : ℂ) - R * I) (Real.sqrt (R ^ 2 + w ^ 2)) := by
  rcases hz with hz | ⟨hz, hw⟩
  · filter_upwards [eventually_gt_atTop (((z.re - c) ^ 2 + z.im ^ 2) / (-2 * z.im))] with R hR
    rw [mem_ball_lower_iff]
    rw [div_lt_iff₀ (by linarith)] at hR
    nlinarith [sq_nonneg w]
  · refine Eventually.of_forall fun R => ?_
    rw [mem_ball_lower_iff, hz]
    have := sq_lt_sq' (abs_lt.mp hw).1 (abs_lt.mp hw).2
    nlinarith

lemma abs_re_sub_lt_of_mem_ball_lower {c w R : ℝ} (hw : 0 ≤ w) {z : ℂ}
    (hz : z ∈ Metric.ball ((c : ℂ) - R * I) (Real.sqrt (R ^ 2 + w ^ 2))) (him : z.im = 0) :
    |z.re - c| < w := by
  rw [mem_ball_lower_iff, him] at hz
  have h : (z.re - c) ^ 2 < w ^ 2 := by nlinarith
  exact abs_lt_of_sq_lt_sq h hw

/-- A function continuous on `Iic Y` with exponential decay is integrable on `Iic Y`. -/
lemma integrableOn_Iic_of_decay {φ : ℝ → ℂ} {Y C : ℝ} (hφ : ContinuousOn φ (Iic Y))
    (hdec : ∀ y ≤ -1, y ≤ Y → ‖φ y‖ ≤ C * Real.exp y) : IntegrableOn φ (Iic Y) := by
  set m := min Y (-1)
  have h1 : IntegrableOn φ (Iic m) := by
    refine Integrable.mono' ((integrableOn_exp_Iic m).const_mul C)
      ((hφ.mono (Iic_subset_Iic.mpr (min_le_left _ _))).aestronglyMeasurable measurableSet_Iic)
      ?_
    refine (ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => ?_)
    exact hdec y (le_trans hy (min_le_right _ _)) (le_trans hy (min_le_left _ _))
  have h2 : IntegrableOn φ (Icc m Y) := (hφ.mono Icc_subset_Iic_self).integrableOn_Icc
  refine (h1.union h2).mono_set fun y hy => ?_
  rcases le_total y m with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hy⟩

lemma continuousOn_vertical {g : ℂ → ℂ} {x : ℝ} {s : Set ℝ}
    (hg : ∀ y ∈ s, ContinuousAt g (x + y * I)) :
    ContinuousOn (fun y : ℝ => g (x + y * I)) s := fun y hy =>
  (ContinuousAt.comp (f := fun y : ℝ => (x : ℂ) + y * I) (hg y hy)
    (by fun_prop)).continuousWithinAt

/-- **Deformation of a vertical ray.** Let `g` be holomorphic off the real axis and on the real
interval `(a₁, a₂)`, with `‖g t‖ ≤ C e^{Im t}` for `Im t ≤ -1`. Then for a polygonal path from
`z₀` (in the lower half-plane) to a real point `x₀ ∈ (a₁, a₂)` whose vertices lie in the lower
half-plane or in `(a₁, a₂)`, the integral upward along the vertical ray below `z₀` followed by the
polygonal path equals the integral upward along the vertical ray below `x₀`. -/
theorem deform_ray {g : ℂ → ℂ} {a₁ a₂ : ℝ}
    (hg : ∀ t : ℂ, (t.im ≠ 0 ∨ (a₁ < t.re ∧ t.re < a₂)) → DifferentiableAt ℂ g t)
    {C : ℝ} (hdecay : ∀ t : ℂ, t.im ≤ -1 → ‖g t‖ ≤ C * Real.exp t.im)
    (z₀ : ℂ) (hz₀ : z₀.im < 0) {x₀ : ℝ} (hx₀₁ : a₁ < x₀) (hx₀₂ : x₀ < a₂) (l : List ℂ)
    (hl : ∀ z ∈ l, z.im < 0 ∨ (z.im = 0 ∧ a₁ < z.re ∧ z.re < a₂))
    (hlast : (z₀ :: l).getLast (List.cons_ne_nil _ _) = x₀) :
    I * (∫ y in Iic z₀.im, g (z₀.re + y * I)) + polyInt g (z₀ :: l) =
      I * ∫ y in Iic (0 : ℝ), g (x₀ + y * I) := by
  set c := (a₁ + a₂) / 2 with hc
  set w := (a₂ - a₁) / 2 with hw
  have hw0 : 0 ≤ w := by rw [hw]; linarith
  have hgood : ∀ z : ℂ, z.im < 0 ∨ (z.im = 0 ∧ a₁ < z.re ∧ z.re < a₂) →
      z.im < 0 ∨ (z.im = 0 ∧ |z.re - c| < w) := by
    rintro z (h | ⟨h, h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h, abs_lt.mpr ⟨?_, ?_⟩⟩ <;> rw [hc, hw] <;> linarith
  -- `g` is holomorphic on the discs
  have hdiff : ∀ R : ℝ, 0 ≤ R →
      DifferentiableOn ℂ g (Metric.ball ((c : ℂ) - R * I) (Real.sqrt (R ^ 2 + w ^ 2))) := by
    intro R hR z hz
    refine (hg z ?_).differentiableWithinAt
    by_cases him : z.im = 0
    · have := abs_lt.mp (abs_re_sub_lt_of_mem_ball_lower hw0 hz him)
      refine Or.inr ⟨?_, ?_⟩ <;> rw [hc, hw] at this <;> linarith [this.1, this.2]
    · exact Or.inl him
  -- the identity for the truncated contours
  have key : ∀ T : ℝ, 0 < T →
      I * (∫ y in (-T)..z₀.im, g (z₀.re + y * I)) + polyInt g (z₀ :: l) =
        (∫ x in z₀.re..x₀, g (x + (-T : ℝ) * I)) + I * ∫ y in (-T)..0, g (x₀ + y * I) := by
    intro T hT
    set v : ℂ := (z₀.re : ℂ) + (-T : ℝ) * I
    set v' : ℂ := (x₀ : ℂ) + (-T : ℝ) * I
    have hv : v.im < 0 := by simp [v]; linarith
    have hv' : v'.im < 0 := by simp [v']; linarith
    have hx₀ : (x₀ : ℂ).im = 0 ∧ |(x₀ : ℂ).re - c| < w := by
      refine ⟨by simp, ?_⟩
      simp only [ofReal_re]
      refine abs_lt.mpr ⟨?_, ?_⟩ <;> rw [hc, hw] <;> linarith
    have hall : ∀ z ∈ v :: v' :: (x₀ : ℂ) :: z₀ :: l, z.im < 0 ∨ (z.im = 0 ∧ |z.re - c| < w) := by
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | rfl | rfl | rfl | hz
      · exact Or.inl hv
      · exact Or.inl hv'
      · exact Or.inr hx₀
      · exact Or.inl hz₀
      · exact hgood z (hl z hz)
    have hev : ∀ᶠ R : ℝ in atTop, 0 ≤ R ∧ ∀ z ∈ v :: v' :: (x₀ : ℂ) :: z₀ :: l,
        z ∈ Metric.ball ((c : ℂ) - R * I) (Real.sqrt (R ^ 2 + w ^ 2)) := by
      refine (eventually_ge_atTop 0).and ?_
      exact (Filter.eventually_all_finite (List.finite_toSet _)).mpr fun z hz =>
        eventually_mem_ball_lower (hall z hz)
    obtain ⟨R, hR0, hR⟩ := hev.exists
    have hcauchy := polyInt_eq_of_ball (hdiff R hR0) (l₁ := v :: z₀ :: l) (l₂ := [v, v', x₀])
      (fun z hz => hR z (by simp only [List.mem_cons] at hz ⊢; tauto))
      (fun z hz => hR z (by simp only [List.mem_cons, List.not_mem_nil] at hz ⊢; tauto))
      rfl (by rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _),
        hlast]; rfl)
    rw [polyInt_cons_cons, polyInt_cons_cons, polyInt_cons_cons, polyInt_singleton, add_zero]
      at hcauchy
    have e1 : segInt g v z₀ = I * ∫ y in (-T)..z₀.im, g (z₀.re + y * I) := by
      conv_lhs => rw [← Complex.re_add_im z₀]
      exact segInt_vertical g z₀.re (-T) z₀.im
    have e2 : segInt g v v' = ∫ x in z₀.re..x₀, g (x + (-T : ℝ) * I) :=
      segInt_horizontal g z₀.re x₀ (-T)
    have e3 : segInt g v' x₀ = I * ∫ y in (-T)..0, g (x₀ + y * I) := by
      have := segInt_vertical g x₀ (-T) 0
      rwa [ofReal_zero, zero_mul, add_zero] at this
    rw [e1, e2, e3] at hcauchy
    exact hcauchy
  -- integrability on the two rays
  have hcont : ∀ x y : ℝ, (y < 0 ∨ (a₁ < x ∧ x < a₂)) → ContinuousAt g (x + y * I) := by
    intro x y h
    refine (hg _ ?_).continuousAt
    rcases h with h | h
    · left; simpa using h.ne
    · right; simpa using h
  have hdec' : ∀ x y : ℝ, y ≤ -1 → ‖g (x + y * I)‖ ≤ C * Real.exp y := by
    intro x y hy
    simpa using hdecay (x + y * I) (by simpa using hy)
  have hint₁ : IntegrableOn (fun y : ℝ => g (z₀.re + y * I)) (Iic z₀.im) :=
    integrableOn_Iic_of_decay
      (continuousOn_vertical fun y hy => hcont _ _ (Or.inl (lt_of_le_of_lt hy hz₀)))
      fun y hy _ => hdec' _ y hy
  have hint₂ : IntegrableOn (fun y : ℝ => g (x₀ + y * I)) (Iic 0) :=
    integrableOn_Iic_of_decay
      (continuousOn_vertical fun y _ => hcont _ _ (Or.inr ⟨hx₀₁, hx₀₂⟩))
      fun y hy _ => hdec' _ y hy
  -- the horizontal segment tends to zero
  have hH : Tendsto (fun T : ℝ => ∫ x in z₀.re..x₀, g (x + (-T : ℝ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun T => C * Real.exp (-T) * |x₀ - z₀.re|) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with T hT
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
      exact hdec' x (-T) (by linarith)
    · simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).mul_const |x₀ - z₀.re|
  have hneg : Tendsto (fun T : ℝ => -T) atTop atBot := tendsto_neg_atTop_atBot
  have hL := ((intervalIntegral_tendsto_integral_Iic _ hint₁ hneg).const_mul I).add_const
    (polyInt g (z₀ :: l))
  have hR := hH.add ((intervalIntegral_tendsto_integral_Iic _ hint₂ hneg).const_mul I)
  rw [zero_add] at hR
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with T hT
  exact (key T hT).symm


/-! ### Change of variables on a half-line -/

lemma integral_comp_mul_left_Iic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℝ → E) (b : ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ x in Iic b, φ (a * x) = a⁻¹ • ∫ x in Iic (a * b), φ x := by
  have h1 := integral_comp_neg_Ioi (-b) (fun x => φ (a * x))
  rw [neg_neg] at h1
  rw [← h1]
  have h2 := integral_comp_mul_left_Ioi (fun x => φ (-x)) (-b) ha
  simp only [mul_neg] at h2 ⊢
  rw [h2, integral_comp_neg_Ioi, neg_neg]

/-! ### Regularity of `Gₙ` -/

lemma differentiableAt_Gamma_of {z : ℂ} (hz : z.im ≠ 0 ∨ 0 < z.re) :
    DifferentiableAt ℂ Gamma z := by
  refine Complex.differentiableAt_Gamma z fun m hm => ?_
  rcases hz with h | h
  · rw [hm] at h; simp at h
  · rw [hm] at h
    simp at h
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma differentiableAt_list_prod {ι : Type*} (l : List ι) {F : ι → ℂ → ℂ} {z : ℂ}
    (h : ∀ i ∈ l, DifferentiableAt ℂ (F i) z) :
    DifferentiableAt ℂ (fun u => (l.map fun i => F i u).prod) z := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h a List.mem_cons_self).mul (ih fun i hi => h i (List.mem_cons_of_mem a hi))

lemma differentiable_trigS (r : ℕ) : Differentiable ℂ (trigS r) := by
  unfold trigS
  fun_prop

variable {P : Params}

lemma etaOne_le_of_mem (hP : P.Valid) {η : ℕ} (hη : η ∈ P.zs ++ P.ps) : P.etaOne ≤ η := by
  rcases List.mem_append.mp hη with h | h
  · exact hP.etaOne_le η h
  · exact (hP.zs_le_etaMin _ hP.etaOne_mem).trans (hP.etaMin_le η h)

lemma etaOne_lt_eta0 (hP : P.Valid) : P.etaOne < P.eta0 := by
  have h1 := hP.zs_le_etaMin _ hP.etaOne_mem
  have h2 := hP.two_mul_lt _ hP.etaMin_mem
  omega

/-- `Gₙ` is holomorphic off the real axis and on `(-h₁, 0)`. -/
lemma G_differentiableAt (hP : P.Valid) (n : ℕ) {t : ℂ}
    (ht : t.im ≠ 0 ∨ (-(Params.hh P.etaOne n : ℝ) < t.re ∧ t.re < 0)) :
    DifferentiableAt ℂ (P.G n) t := by
  have hpos : ∀ a : ℝ, (Params.hh P.etaOne n : ℝ) ≤ a → ((t + a).im ≠ 0 ∨ 0 < (t + a).re) := by
    intro a ha
    rcases ht with h | h
    · left; simpa using h
    · right; simp only [add_re, ofReal_re]; linarith [h.1]
  have hΓ1 : DifferentiableAt ℂ (fun t => Gamma (-t)) t := by
    refine (differentiableAt_Gamma_of ?_).comp t differentiableAt_id.neg
    rcases ht with h | h
    · left; simpa using h
    · right; simp only [neg_re]; linarith [h.2]
  have hΓ2 : DifferentiableAt ℂ (fun t => Gamma (t + (P.h0 n : ℂ))) t := by
    refine (differentiableAt_Gamma_of ?_).comp t (differentiableAt_id.add_const _)
    have h := hpos (P.h0 n) (by
      have := etaOne_lt_eta0 hP
      simp only [Params.hh, Params.h0]
      push_cast
      nlinarith [(Nat.cast_le (α := ℝ)).mpr this.le, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    simpa using h
  have hprod : DifferentiableAt ℂ (fun t => ((P.zs ++ P.ps).map fun η =>
      Gamma (t + Params.hh η n) / Gamma (t + P.h0 n - Params.hh η n + 1)).prod) t := by
    refine differentiableAt_list_prod _ fun η hη => ?_
    simp_rw [div_eq_mul_inv]
    refine DifferentiableAt.mul ?_ ?_
    · refine (differentiableAt_Gamma_of ?_).comp t (differentiableAt_id.add_const _)
      have h := hpos (Params.hh η n) (by
        have := etaOne_le_of_mem hP hη
        simp only [Params.hh]
        push_cast
        nlinarith [(Nat.cast_le (α := ℝ)).mpr this, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      simpa using h
    · exact (Complex.differentiable_one_div_Gamma.comp (by fun_prop :
        Differentiable ℂ fun t : ℂ => t + (P.h0 n : ℂ) - (Params.hh η n : ℂ) + 1)) t
  unfold Params.G
  exact ((((differentiableAt_const _).mul ((differentiableAt_const _).add
    ((differentiableAt_const _).mul differentiableAt_id))).mul (hΓ1.pow _)).mul
      (hΓ2.pow _)).mul hprod

/-! ### Conjugation symmetry -/

lemma G_conj (n : ℕ) (t : ℂ) : P.G n (conj t) = conj (P.G n t) := by
  have hΓ : ∀ z : ℂ, Gamma (conj z) = conj (Gamma z) := Gamma_conj
  simp only [Params.G, map_mul, map_pow, map_add, map_natCast, map_ofNat, conj_ofReal,
    map_list_prod, List.map_map, map_neg, map_sub, map_one, map_div₀, ← hΓ, Function.comp_def]

lemma im_trigS_mul_G_ofReal (r n : ℕ) (x : ℝ) : (trigS r x * P.G n x).im = 0 := by
  have h : trigS r (conj (x : ℂ)) * P.G n (conj (x : ℂ)) = conj (trigS r x * P.G n x) := by
    rw [trigS_conj, G_conj, map_mul]
  rw [conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- The integral along a real segment of a function real on the real axis is real. -/
lemma im_segInt_ofReal {g : ℂ → ℂ} (hg : ∀ x : ℝ, (g x).im = 0) (a b : ℝ) :
    (segInt g a b).im = 0 := by
  have h : (fun s : ℝ => g (a + s * (b - a)) * (b - a)) =
      fun s : ℝ => (((g ((a + s * (b - a) : ℝ) : ℂ)).re * (b - a) : ℝ) : ℂ) := by
    funext s
    have hx : ((a : ℂ) + s * (b - a)) = ((a + s * (b - a) : ℝ) : ℂ) := by push_cast; ring
    have hba : ((b : ℂ) - a) = ((b - a : ℝ) : ℂ) := by push_cast; ring
    rw [hx, hba]
    apply Complex.ext
    · simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    · simp only [mul_im, ofReal_re, ofReal_im, hg, mul_zero, zero_mul, add_zero]
  rw [segInt, h, intervalIntegral.integral_ofReal, ofReal_im]

/-! ### Exponential decay in the lower half-plane -/

lemma norm_trigS_le {r : ℕ} (hr : 2 ≤ r) {t : ℂ} (ht : t.im ≤ 0) :
    ‖trigS r t‖ ≤ 2 * Real.exp ((r - 2) * Real.pi * (-t.im)) := by
  set top := ((r - 1).factorial : ℂ)⁻¹ * exp (I * Real.pi * ((r : ℂ) - 2) * t)
  have h1 := norm_trigS_sub_le hr ht
  have h2 : ‖top‖ ≤ Real.exp ((r - 2) * Real.pi * (-t.im)) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_exp]
    have hre : (I * Real.pi * ((r : ℂ) - 2) * t).re = (r - 2) * Real.pi * (-t.im) := by
      rw [show I * Real.pi * ((r : ℂ) - 2) * t = I * (((r - 2) * Real.pi : ℝ) : ℂ) * t by
        push_cast; ring]
      simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]
      ring
    rw [hre]
    have : (1 : ℝ) ≤ (r - 1).factorial := Nat.one_le_cast.mpr (Nat.factorial_pos _)
    calc ((r - 1).factorial : ℝ)⁻¹ * Real.exp ((r - 2) * Real.pi * (-t.im))
        ≤ 1 * Real.exp ((r - 2) * Real.pi * (-t.im)) := by
          gcongr; exact inv_le_one_of_one_le₀ this
      _ = _ := one_mul _
  have h3 : Real.exp ((r - 4) * Real.pi * (-t.im)) ≤ Real.exp ((r - 2) * Real.pi * (-t.im)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  calc ‖trigS r t‖ = ‖(trigS r t - top) + top‖ := by rw [sub_add_cancel]
    _ ≤ ‖trigS r t - top‖ + ‖top‖ := norm_add_le _ _
    _ ≤ _ := by linarith

lemma norm_sin_pi_mul_ge {t : ℂ} (ht : t.im ≤ -1) :
    Real.exp (-(Real.pi * t.im)) / 4 ≤ ‖sin (Real.pi * t)‖ := by
  set E := Real.exp (-(Real.pi * t.im))
  have hE : 2 ≤ E := by
    have : Real.pi ≤ -(Real.pi * t.im) := by nlinarith [Real.pi_pos]
    have h1 := Real.add_one_le_exp (-(Real.pi * t.im))
    linarith [Real.pi_gt_three]
  have h1 : ‖exp ((Real.pi * t) * I)‖ = E := by
    rw [Complex.norm_exp]; simp; rfl
  have h2 : ‖exp (-(Real.pi * t) * I)‖ = E⁻¹ := by
    rw [Complex.norm_exp, ← Real.exp_neg]; simp
  have hsin : sin (Real.pi * t) =
      (exp (-(Real.pi * t) * I) - exp ((Real.pi * t) * I)) * I / 2 := rfl
  rw [hsin, norm_div, norm_mul, norm_I, mul_one, Complex.norm_two]
  have h3 := norm_sub_norm_le (exp ((Real.pi * t) * I)) (exp (-(Real.pi * t) * I))
  rw [norm_sub_rev, h1, h2] at h3
  have h4 : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  linarith

/-- The bound for `Rₙ` from its partial fractions. -/
lemma norm_R_le (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {t : ℂ} (ht : t.im ≤ -1) :
    ‖P.R n t‖ ≤ ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r), ‖(P.coef n i k : ℂ)‖ := by
  have hk : ∀ k : ℕ, 1 ≤ ‖t + k‖ := fun k => by
    have := Complex.abs_im_le_norm (t + k)
    simp only [add_im, natCast_im, add_zero] at this
    rw [abs_of_neg (by linarith)] at this
    linarith
  rw [Params.R_eq_sum hP hn ?_]
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
    rw [norm_div, norm_pow]
    exact div_le_self (norm_nonneg _) (one_le_pow₀ (hk k))
  · intro k _ h
    have := hk k
    rw [h, norm_zero] at this
    linarith

lemma norm_G_le (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {t : ℂ} (ht : t.im ≤ -1) :
    ‖P.G n t‖ ≤ (∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r), ‖(P.coef n i k : ℂ)‖) *
      (4 * Real.pi) ^ P.r * Real.exp (P.r * (Real.pi * t.im)) := by
  set CR := ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r), ‖(P.coef n i k : ℂ)‖
  have hR := Params.R_eq_sin_pow_mul_G hP hn (t := t) (fun m h => by
    have := congrArg Complex.im h
    simp at this
    linarith)
  have hnorm : ‖P.R n t‖ = (‖sin (Real.pi * t)‖ / Real.pi) ^ P.r * ‖P.G n t‖ := by
    rw [hR, norm_mul, norm_pow, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  set E := Real.exp (-(Real.pi * t.im))
  have hs := norm_sin_pi_mul_ge ht
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hkey : (E / (4 * Real.pi)) ^ P.r * ‖P.G n t‖ ≤ CR := by
    have hbase : E / (4 * Real.pi) ≤ ‖sin (Real.pi * t)‖ / Real.pi := by
      rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
      nlinarith [Real.pi_pos]
    calc (E / (4 * Real.pi)) ^ P.r * ‖P.G n t‖
        ≤ (‖sin (Real.pi * t)‖ / Real.pi) ^ P.r * ‖P.G n t‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase _) (norm_nonneg _)
      _ = ‖P.R n t‖ := hnorm.symm
      _ ≤ CR := norm_R_le hP hn ht
  have hone : (E / (4 * Real.pi)) ^ P.r * ((4 * Real.pi) ^ P.r *
      Real.exp (Real.pi * t.im) ^ P.r) = 1 := by
    rw [← mul_pow, ← mul_pow]
    have : E / (4 * Real.pi) * (4 * Real.pi * Real.exp (Real.pi * t.im)) = 1 := by
      rw [div_mul_eq_mul_div, mul_comm (4 * Real.pi), ← mul_assoc, mul_div_assoc,
        div_self (by positivity), mul_one, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [this, one_pow]
  calc ‖P.G n t‖ = ((E / (4 * Real.pi)) ^ P.r * ‖P.G n t‖) *
        ((4 * Real.pi) ^ P.r * Real.exp (Real.pi * t.im) ^ P.r) := by
        rw [mul_comm ((E / (4 * Real.pi)) ^ P.r), mul_assoc, hone, mul_one]
    _ ≤ CR * ((4 * Real.pi) ^ P.r * Real.exp (Real.pi * t.im) ^ P.r) := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; ring

/-- Exponential decay of `S Gₙ` as `Im t → -∞`. -/
lemma norm_trigS_mul_G_le (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, ∀ t : ℂ, t.im ≤ -1 → ‖trigS P.r t * P.G n t‖ ≤ C * Real.exp t.im := by
  set CR := ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r), ‖(P.coef n i k : ℂ)‖
  have hCR : 0 ≤ CR := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨2 * (CR * (4 * Real.pi) ^ P.r), fun t ht => ?_⟩
  have hr : 2 ≤ P.r := by have := hP.three_le_r; omega
  rw [norm_mul]
  have h1 := norm_trigS_le hr (t := t) (by linarith)
  have h2 := norm_G_le hP hn ht
  have hexp : Real.exp ((P.r - 2) * Real.pi * (-t.im)) * Real.exp (P.r * (Real.pi * t.im)) =
      Real.exp (2 * Real.pi * t.im) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖trigS P.r t‖ * ‖P.G n t‖
      ≤ (2 * Real.exp ((P.r - 2) * Real.pi * (-t.im))) *
          (CR * (4 * Real.pi) ^ P.r * Real.exp (P.r * (Real.pi * t.im))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 2 * (CR * (4 * Real.pi) ^ P.r) * Real.exp (2 * Real.pi * t.im) := by
        rw [← hexp]; ring
    _ ≤ 2 * (CR * (4 * Real.pi) ^ P.r) * Real.exp t.im := by
        gcongr
        nlinarith [Real.pi_gt_three]

end Deform

end OddZeta
