import Mathlib

/-!
# Integrals of partial fractions along vertical lines

For `M : ℝ` and a pole `p : ℂ` off the line `Re t = M` we compute

* `∫_ℝ (M + y i - p)^{-j} dy = 0` for `j ≥ 2` (`integral_vert_inv_pow`);
* `lim_{Y → ∞} ∫_{-Y}^{Y} (M + y i - p)^{-1} dy = π sign (M - Re p)`
  (`tendsto_integral_vert_inv`);

and deduce the integral along the line `Re t = M` of a rational function given by its partial
fraction decomposition, whose residues sum to zero (`integral_vert_partialFractions`).
-/

open Complex MeasureTheory Filter Topology Set

namespace OddZeta

/-! ### The parametrisation `y ↦ M + y i - p` -/

lemma vert_ne_zero {M : ℝ} {p : ℂ} (hp : p.re ≠ M) (y : ℝ) : (M : ℂ) + y * I - p ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, sub_re, zero_re] at this
  exact hp (by linarith)

lemma continuous_vert (M : ℝ) (p : ℂ) : Continuous (fun y : ℝ => (M : ℂ) + y * I - p) := by
  fun_prop

lemma hasDerivAt_vert (M : ℝ) (p : ℂ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => (M : ℂ) + y * I - p) I y := by
  simpa using ((((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (M : ℂ)).sub_const p

lemma tendsto_norm_vert {l : Filter ℝ} (hl : Tendsto (fun y : ℝ => |y|) l atTop) (M : ℝ)
    (p : ℂ) : Tendsto (fun y : ℝ => ‖(M : ℂ) + y * I - p‖) l atTop := by
  refine tendsto_atTop_mono (fun y => ?_) (tendsto_atTop_add_const_right l (-|p.im|) hl)
  calc |y| + -|p.im| ≤ |y - p.im| := by have := abs_sub_abs_le_abs_sub y p.im; linarith
    _ = |((M : ℂ) + y * I - p).im| := by simp
    _ ≤ ‖(M : ℂ) + y * I - p‖ := Complex.abs_im_le_norm _

lemma integrable_inv_sq_add_sq {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun x : ℝ => (a ^ 2 + x ^ 2)⁻¹) := by
  refine ((integrable_inv_one_add_sq.comp_div ha).const_mul (a ^ 2)⁻¹).congr
    (ae_of_all _ fun x => ?_)
  simp only
  field_simp

/-! ### Powers `j ≥ 2` -/

theorem integrable_vert_inv_pow {M : ℝ} {p : ℂ} (hp : p.re ≠ M) {j : ℕ} (hj : 2 ≤ j) :
    Integrable (fun y : ℝ => (((M : ℂ) + y * I - p) ^ j)⁻¹) := by
  set a := M - p.re with ha_def
  have ha : a ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have hbound := ((integrable_inv_sq_add_sq ha).comp_sub_right p.im).const_mul (|a| ^ k)⁻¹
  refine hbound.mono' (((continuous_vert M p).pow (k + 2)).inv₀
    (fun y => pow_ne_zero _ (vert_ne_zero hp y))).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  have hz : (M : ℂ) + y * I - p ≠ 0 := vert_ne_zero hp y
  have hre : |a| ≤ ‖(M : ℂ) + y * I - p‖ := by
    have := Complex.abs_re_le_norm ((M : ℂ) + y * I - p)
    simpa [a] using this
  have hsq : ‖(M : ℂ) + y * I - p‖ ^ 2 = a ^ 2 + (y - p.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [a]
    ring
  have hpos : 0 < ‖(M : ℂ) + y * I - p‖ := norm_pos_iff.mpr hz
  simp only [norm_inv, norm_pow]
  rw [← mul_inv, pow_add, ← hsq]
  apply inv_anti₀ (mul_pos (pow_pos (abs_pos.mpr ha) k) (pow_pos hpos 2))
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg a) hre k) (by positivity)

theorem integral_vert_inv_pow {M : ℝ} {p : ℂ} (hp : p.re ≠ M) {j : ℕ} (hj : 2 ≤ j) :
    ∫ y : ℝ, (((M : ℂ) + y * I - p) ^ j)⁻¹ = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hderiv : ∀ y : ℝ, HasDerivAt
      (fun y : ℝ => I / (k + 1) * (((M : ℂ) + y * I - p) ^ (k + 1))⁻¹)
      ((((M : ℂ) + y * I - p) ^ (k + 2))⁻¹) y := by
    intro y
    have hz := vert_ne_zero hp y
    have := (((hasDerivAt_vert M p y).fun_pow (k + 1)).fun_inv
      (pow_ne_zero _ hz)).const_mul (I / (k + 1))
    convert this using 1
    generalize (M : ℂ) + y * I - p = z at hz ⊢
    simp only [Nat.add_sub_cancel]
    calc (z ^ (k + 2))⁻¹ = -(I * I) * (z ^ k / (z ^ (k + 1)) ^ 2) := by
          rw [I_mul_I]; field_simp; ring
      _ = _ := by push_cast; field_simp
  have hF : ∀ l : Filter ℝ, Tendsto (fun y : ℝ => |y|) l atTop →
      Tendsto (fun y : ℝ => I / (k + 1) * (((M : ℂ) + y * I - p) ^ (k + 1))⁻¹) l (𝓝 0) := by
    intro l hl
    have h1 : Tendsto (fun y : ℝ => (((M : ℂ) + y * I - p) ^ (k + 1))⁻¹) l (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv, norm_pow]
      exact ((tendsto_pow_atTop (Nat.succ_ne_zero k)).comp
        (tendsto_norm_vert hl M p)).inv_tendsto_atTop
    simpa using h1.const_mul (I / (k + 1))
  rw [integral_of_hasDerivAt_of_tendsto hderiv (integrable_vert_inv_pow hp (by omega))
    (hF _ tendsto_abs_atBot_atTop) (hF _ tendsto_abs_atTop_atTop)]
  simp

/-! ### The power `j = 1` -/

lemma tendsto_ofReal_div_atTop (w : ℂ) : Tendsto (fun Y : ℝ => w / (Y : ℂ)) atTop (𝓝 0) := by
  have := ((Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).const_mul w
  simpa [div_eq_mul_inv] using this

theorem tendsto_integral_vert_inv_of_re_lt {M : ℝ} {p : ℂ} (hp : p.re < M) :
    Tendsto (fun Y : ℝ => ∫ y in (-Y)..Y, ((M : ℂ) + y * I - p)⁻¹) atTop
      (𝓝 (Real.pi : ℂ)) := by
  have hslit : ∀ y : ℝ, (M : ℂ) + y * I - p ∈ slitPlane := fun y =>
    mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => -I * log ((M : ℂ) + y * I - p))
      (((M : ℂ) + y * I - p)⁻¹) y := by
    intro y
    have := ((hasDerivAt_vert M p y).clog_real (hslit y)).const_mul (-I)
    convert this using 1
    have hz := vert_ne_zero hp.ne y
    generalize (M : ℂ) + y * I - p = z at hz ⊢
    rw [← mul_div_assoc, neg_mul, I_mul_I, neg_neg, one_div]
  have hint : ∀ Y : ℝ, ∫ y in (-Y)..Y, ((M : ℂ) + y * I - p)⁻¹ =
      -I * (log ((M : ℂ) + Y * I - p) - log ((M : ℂ) + ((-Y : ℝ) : ℂ) * I - p)) := by
    intro Y
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (((continuous_vert M p).inv₀ (vert_ne_zero hp.ne)).intervalIntegrable _ _)]
    ring
  set w : ℂ := (M : ℂ) - p with hw_def
  have hw := tendsto_ofReal_div_atTop w
  have h1 : Tendsto (fun Y : ℝ => -I * (log (w / Y + I) - log (w / Y - I))) atTop
      (𝓝 (-I * (log I - log (-I)))) := by
    have hI : Tendsto (fun Y : ℝ => w / Y + I) atTop (𝓝 I) := by simpa using hw.add_const I
    have hmI : Tendsto (fun Y : ℝ => w / Y - I) atTop (𝓝 (-I)) := by
      simpa using hw.sub_const I
    exact (((continuousAt_clog (by simp [mem_slitPlane_iff])).tendsto.comp hI).sub
      ((continuousAt_clog (by simp [mem_slitPlane_iff])).tendsto.comp hmI)).const_mul (-I)
  have hlim : -I * (log I - log (-I)) = (Real.pi : ℂ) := by
    rw [log_I, log_neg_I]
    ring_nf
    rw [I_sq]
    ring
  rw [hlim] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Y hY
  have hY' : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have e1 : (M : ℂ) + Y * I - p = Y * (w / Y + I) := by rw [hw_def]; field_simp; ring
  have e2 : (M : ℂ) + ((-Y : ℝ) : ℂ) * I - p = Y * (w / Y - I) := by
    rw [hw_def]; push_cast; field_simp; ring
  have n1 : w / Y + I ≠ 0 := by
    intro h; apply vert_ne_zero hp.ne Y; rw [e1, h, mul_zero]
  have n2 : w / Y - I ≠ 0 := by
    intro h; apply vert_ne_zero hp.ne (-Y); rw [e2, h, mul_zero]
  rw [hint Y, e1, e2, log_ofReal_mul hY n1, log_ofReal_mul hY n2]
  ring

theorem tendsto_integral_vert_inv_of_lt_re {M : ℝ} {p : ℂ} (hp : M < p.re) :
    Tendsto (fun Y : ℝ => ∫ y in (-Y)..Y, ((M : ℂ) + y * I - p)⁻¹) atTop
      (𝓝 (-(Real.pi : ℂ))) := by
  set p' : ℂ := 2 * M - p with hp'_def
  have hp' : p'.re < M := by simp [p']; linarith
  refine (tendsto_integral_vert_inv_of_re_lt hp').neg.congr (fun Y => ?_)
  have e : ∀ y : ℝ, ((M : ℂ) + y * I - p)⁻¹ =
      (fun u : ℝ => -((M : ℂ) + u * I - p')⁻¹) (-y) := by
    intro y
    simp only [← inv_neg]
    congr 1
    simp only [hp'_def]
    push_cast
    ring
  simp_rw [e]
  have := intervalIntegral.integral_comp_neg (a := -Y) (b := Y)
    (f := fun u : ℝ => -((M : ℂ) + u * I - p')⁻¹)
  simp only [neg_neg] at this
  rw [this, intervalIntegral.integral_neg]

/-- The symmetric integrals of `(t - p)⁻¹` along the line `Re t = M` converge to `π` if `p` lies
to the left of the line and to `-π` if `p` lies to the right. -/
theorem tendsto_integral_vert_inv {M : ℝ} {p : ℂ} (hp : p.re ≠ M) :
    Tendsto (fun Y : ℝ => ∫ y in (-Y)..Y, ((M : ℂ) + y * I - p)⁻¹) atTop
      (𝓝 (Real.pi * SignType.sign (M - p.re))) := by
  rcases hp.lt_or_gt with h | h
  · rw [sign_pos (sub_pos.mpr h)]
    simpa using tendsto_integral_vert_inv_of_re_lt h
  · rw [sign_neg (sub_neg.mpr h)]
    simpa using tendsto_integral_vert_inv_of_lt_re h

/-! ### Partial fractions -/

theorem integrable_vert_inv_mul_inv {M : ℝ} {p q : ℂ} (hp : p.re ≠ M) (hq : q.re ≠ M) :
    Integrable (fun y : ℝ => ((M : ℂ) + y * I - p)⁻¹ * ((M : ℂ) + y * I - q)⁻¹) := by
  refine ((integrable_vert_inv_pow hp le_rfl).norm.add
    (integrable_vert_inv_pow hq le_rfl).norm).mono'
    (((continuous_vert M p).inv₀ (vert_ne_zero hp)).mul
      ((continuous_vert M q).inv₀ (vert_ne_zero hq))).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  simp only [norm_mul, norm_inv, norm_pow, Pi.add_apply, ← inv_pow]
  have h1 := inv_nonneg.mpr (norm_nonneg ((M : ℂ) + y * I - p))
  have h2 := inv_nonneg.mpr (norm_nonneg ((M : ℂ) + y * I - q))
  nlinarith [sq_nonneg (‖(M : ℂ) + y * I - p‖⁻¹ - ‖(M : ℂ) + y * I - q‖⁻¹), mul_nonneg h1 h2]

/-- **Integral of a partial fraction decomposition along a vertical line.** If
`Q t = ∑_{p ∈ P} ∑_{1 ≤ j ≤ J} c p j (t - p)^{-j}` has no pole on the line `Re t = M` and the
residues `c p 1` sum to zero, then `Q` is integrable along the line and
`∫_{Re t = M} Q(t) dt = -2πi ∑_{Re p > M} c p 1`. -/
theorem integral_vert_partialFractions {M : ℝ} {P : Finset ℂ} (hP : ∀ p ∈ P, p.re ≠ M)
    {J : ℕ} (hJ : 1 ≤ J) (c : ℂ → ℕ → ℂ) (hc : ∑ p ∈ P, c p 1 = 0) (Q : ℂ → ℂ)
    (hQ : ∀ t, Q t = ∑ p ∈ P, ∑ j ∈ Finset.Icc 1 J, c p j * ((t - p) ^ j)⁻¹) :
    Integrable (fun y : ℝ => Q (M + y * I)) ∧
      (∫ y : ℝ, Q (M + y * I)) * I = -2 * Real.pi * I * ∑ p ∈ P with M < p.re, c p 1 := by
  set h1 : ℝ → ℂ := fun y => ∑ p ∈ P, c p 1 * ((M : ℂ) + y * I - p)⁻¹ with hh1
  set h2 : ℝ → ℂ := fun y =>
    ∑ p ∈ P, ∑ j ∈ Finset.Ioc 1 J, c p j * (((M : ℂ) + y * I - p) ^ j)⁻¹ with hh2
  have hsplit : ∀ y : ℝ, Q (M + y * I) = h1 y + h2 y := by
    intro y
    rw [hQ, Finset.Icc_eq_cons_Ioc hJ]
    simp only [Finset.sum_cons, pow_one, Finset.sum_add_distrib, h1, h2]
  have hq0 : ((M : ℂ) - 1).re ≠ M := by simp
  have h1eq : h1 = fun y : ℝ => ∑ p ∈ P, (c p 1 * (p - (M - 1))) *
      (((M : ℂ) + y * I - p)⁻¹ * ((M : ℂ) + y * I - (M - 1))⁻¹) := by
    ext y
    have : h1 y = h1 y - (∑ p ∈ P, c p 1) * ((M : ℂ) + y * I - (M - 1))⁻¹ := by
      rw [hc]; ring
    rw [this, Finset.sum_mul, hh1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have := vert_ne_zero (hP p hp) y
    have := vert_ne_zero hq0 y
    field_simp
    ring
  have hi1 : Integrable h1 := by
    rw [h1eq]
    exact integrable_finsetSum _ fun p hp =>
      (integrable_vert_inv_mul_inv (hP p hp) hq0).const_mul _
  have hi2' : ∀ p ∈ P, Integrable (fun y : ℝ =>
      ∑ j ∈ Finset.Ioc 1 J, c p j * (((M : ℂ) + y * I - p) ^ j)⁻¹) := fun p hp =>
    integrable_finsetSum _ fun j hj =>
      (integrable_vert_inv_pow (hP p hp) (by simp at hj; omega)).const_mul _
  have hi2 : Integrable h2 := integrable_finsetSum _ hi2'
  have hQi : Integrable (fun y : ℝ => Q (M + y * I)) :=
    (hi1.add hi2).congr (ae_of_all _ fun y => (hsplit y).symm)
  refine ⟨hQi, ?_⟩
  have hint2 : ∫ y, h2 y = 0 := by
    rw [hh2, integral_finsetSum _ hi2']
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [integral_finsetSum _ fun j hj =>
      (integrable_vert_inv_pow (hP p hp) (by simp at hj; omega)).const_mul _]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [integral_const_mul, integral_vert_inv_pow (hP p hp) (by simp at hj; omega), mul_zero]
  have hint1 : ∫ y, h1 y = ∑ p ∈ P, c p 1 * (Real.pi * SignType.sign (M - p.re)) := by
    have hlim1 := intervalIntegral_tendsto_integral hi1 tendsto_neg_atTop_atBot tendsto_id
    have hY : ∀ Y : ℝ, ∫ y in (-Y)..id Y, h1 y =
        ∑ p ∈ P, c p 1 * ∫ y in (-Y)..Y, ((M : ℂ) + y * I - p)⁻¹ := by
      intro Y
      have hcont : ∀ p ∈ P, Continuous (fun y : ℝ => c p 1 * ((M : ℂ) + y * I - p)⁻¹) :=
        fun p hp => continuous_const.mul ((continuous_vert M p).inv₀ (vert_ne_zero (hP p hp)))
      simp only [hh1, id]
      rw [intervalIntegral.integral_finsetSum fun p hp => (hcont p hp).intervalIntegrable _ _]
      simp_rw [intervalIntegral.integral_const_mul]
    have hlim2 : Tendsto (fun Y : ℝ => ∫ y in (-Y)..id Y, h1 y) atTop
        (𝓝 (∑ p ∈ P, c p 1 * (Real.pi * SignType.sign (M - p.re)))) := by
      simp_rw [hY]
      exact tendsto_finsetSum _ fun p hp => (tendsto_integral_vert_inv (hP p hp)).const_mul _
    exact tendsto_nhds_unique hlim1 hlim2
  rw [integral_congr_ae (ae_of_all _ hsplit), integral_add hi1 hi2, hint2, add_zero, hint1]
  have key : ∀ p ∈ P, c p 1 * (Real.pi * SignType.sign (M - p.re)) =
      Real.pi * c p 1 - 2 * Real.pi * (if M < p.re then c p 1 else 0) := by
    intro p hp
    rcases (hP p hp).lt_or_gt with h | h
    · have h' : ¬ M < p.re := by linarith
      rw [sign_pos (by linarith)]
      simp only [h', ite_false, SignType.coe_one]
      ring
    · rw [sign_neg (by linarith)]
      simp only [h, ite_true, SignType.coe_neg_one]
      ring
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.mul_sum, hc, ← Finset.mul_sum,
    ← Finset.sum_filter]
  ring

end OddZeta
