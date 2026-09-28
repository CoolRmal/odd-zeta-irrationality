import OddZeta.Analysis.VerticalLine

/-!
# Auxiliary lemmas for the integral representation of `Fₙ`

* `integrable_tsum_of_summable_integral_norm`: a series of integrable functions whose `L¹` norms
  are summable has an integrable sum;
* `integral_vert_two_poles`: for `p` to the left of the line `Re t = M` and `m` off the line,
  `∫_ℝ (M+iy-p)^{-i} (M+iy-m)^{-r} dy = -2π · res_m` if `m` is to the right of the line and `0`
  otherwise, where `res_m = (-1)^{r-1} C(i+r-2, r-1) (m-p)^{-(i+r-1)}` (`vertRes`);
* `integral_norm_vert_inv_pow_le`: `∫_ℝ |M+iy-m|^{-r} dy ≤ 2^{r-3} π / (M-m)²` if `|M-m| ≥ 1/2`.
-/

open Complex MeasureTheory Filter Topology Set

namespace OddZeta

/-! ### Series of integrable functions -/

/-- A series of integrable functions whose `L¹` norms are summable has an integrable sum. -/
theorem integrable_tsum_of_summable_integral_norm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} [Countable ι] {F : ι → α → ℂ}
    (hF_int : ∀ i, Integrable (F i) μ) (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a => ∑' i, F i a) μ := by
  refine ⟨(AEMeasurable.tsum fun i => (hF_int i).aemeasurable).aestronglyMeasurable, ?_⟩
  have hf'' (i : ι) : AEMeasurable (fun a => ‖F i a‖ₑ) μ := (hF_int i).1.enorm
  have h1 (i : ι) : ∫⁻ a, ‖F i a‖ₑ ∂μ = ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hF_int i).norm (ae_of_all _ fun a => norm_nonneg _)]
    simp
  have hfin : ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ ≠ ⊤ := by
    simp_rw [h1]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun a => norm_nonneg _) hF_sum]
    exact ENNReal.ofReal_ne_top
  calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ :=
        lintegral_mono fun a => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ := lintegral_tsum hf''
    _ < ⊤ := lt_top_iff_ne_top.2 hfin

/-! ### Two poles -/

/-- The residue at `m` of `(t - p)^{-i} (t - m)^{-r}`, in terms of `D = m - p`:
`(-1)^{r-1} C(i+r-2, r-1) D^{-(i+r-1)}` (and `0` if `r = 0`). -/
noncomputable def vertRes (D : ℂ) (i r : ℕ) : ℂ :=
  if r = 0 then 0 else (-1) ^ (r - 1) * ((i + r - 2).choose (r - 1) : ℂ) / D ^ (i + r - 1)

lemma vertRes_succ (D : ℂ) (i b : ℕ) :
    vertRes D i (b + 1) = (-1) ^ b * ((i + b - 1).choose b : ℂ) / D ^ (i + b) := by
  simp only [vertRes, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  rw [show i + (b + 1) - 2 = i + b - 1 by omega, show i + (b + 1) - 1 = i + b by omega]

lemma vertRes_zero_left (D : ℂ) {r : ℕ} (hr : 2 ≤ r) : vertRes D 0 r = 0 := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  rw [vertRes_succ, Nat.choose_eq_zero_of_lt (by omega)]
  simp

lemma vertRes_succ_succ {D : ℂ} (hD : D ≠ 0) (a b : ℕ) :
    vertRes D (a + 1) (b + 1) = -(vertRes D (a + 1) b - vertRes D a (b + 1)) / D := by
  rcases b with _ | c
  · have h0 : vertRes D (a + 1) 0 = 0 := by simp [vertRes]
    rw [vertRes_succ, vertRes_succ, h0]
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, add_zero]
    field_simp
    ring
  · rw [vertRes_succ, vertRes_succ, vertRes_succ,
      show a + 1 + (c + 1) - 1 = a + c + 1 by omega, show a + 1 + c - 1 = a + c by omega,
      show a + (c + 1) - 1 = a + c by omega, show a + 1 + (c + 1) = a + c + 2 by omega,
      show a + 1 + c = a + c + 1 by omega, show a + (c + 1) = a + c + 1 by omega,
      Nat.choose_succ_succ']
    push_cast
    field_simp
    ring

lemma inv_pow_mul_inv_pow_succ_succ {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u - v ≠ 0)
    (a b : ℕ) :
    (u ^ (a + 1))⁻¹ * (v ^ (b + 1))⁻¹ =
      -((u ^ (a + 1))⁻¹ * (v ^ b)⁻¹ - (u ^ a)⁻¹ * (v ^ (b + 1))⁻¹) / (u - v) := by
  field_simp
  ring

lemma integral_vert_two_poles_aux {M : ℝ} {p m : ℂ} (hp : p.re < M) (hm : m.re ≠ M)
    (hpm : p ≠ m) (n : ℕ) : ∀ i r : ℕ, i + r = n + 2 →
      Integrable (fun y : ℝ => (((M : ℂ) + y * I - p) ^ i)⁻¹ * (((M : ℂ) + y * I - m) ^ r)⁻¹) ∧
      ∫ y : ℝ, (((M : ℂ) + y * I - p) ^ i)⁻¹ * (((M : ℂ) + y * I - m) ^ r)⁻¹ =
        if M < m.re then -2 * Real.pi * vertRes (m - p) i r else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i r hir
  rcases i with _ | a
  · have hr : 2 ≤ r := by omega
    simp only [pow_zero, inv_one, one_mul]
    refine ⟨integrable_vert_inv_pow hm hr, ?_⟩
    rw [integral_vert_inv_pow hm hr, vertRes_zero_left _ hr]
    simp
  rcases r with _ | b
  · simp only [pow_zero, inv_one, mul_one]
    refine ⟨integrable_vert_inv_pow hp.ne (by omega), ?_⟩
    rw [integral_vert_inv_pow hp.ne (by omega)]
    simp [vertRes]
  have hD : m - p ≠ 0 := sub_ne_zero.2 (Ne.symm hpm)
  rcases n with _ | n
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    set c : ℂ → ℕ → ℂ := fun x _ => if x = m then (m - p)⁻¹ else (p - m)⁻¹ with hc_def
    have hPre : ∀ x ∈ ({p, m} : Finset ℂ), x.re ≠ M := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hp.ne
      · rw [Finset.mem_singleton.1 hx]; exact hm
    have hc : ∑ x ∈ ({p, m} : Finset ℂ), c x 1 = 0 := by
      rw [Finset.sum_pair hpm]
      simp only [hc_def, hpm, ite_false, ite_true]
      rw [← neg_sub m p, inv_neg, neg_add_cancel]
    obtain ⟨hint, hval⟩ := integral_vert_partialFractions hPre le_rfl c hc _ (fun t => rfl)
    have hpt : ∀ y : ℝ, (((M : ℂ) + y * I - p) ^ (0 + 1))⁻¹ * (((M : ℂ) + y * I - m) ^ (0 + 1))⁻¹ =
        ∑ x ∈ ({p, m} : Finset ℂ), ∑ j ∈ Finset.Icc 1 1,
          c x j * (((M : ℂ) + y * I - x) ^ j)⁻¹ := by
      intro y
      have h1 := vert_ne_zero hp.ne y
      have h2 := vert_ne_zero hm y
      have h3 : p - m ≠ 0 := sub_ne_zero.2 hpm
      rw [Finset.sum_pair hpm]
      simp only [Finset.Icc_self, Finset.sum_singleton, hc_def, hpm, ite_false, ite_true, pow_one,
        zero_add]
      field_simp
      ring
    refine ⟨hint.congr (ae_of_all _ fun y => (hpt y).symm), ?_⟩
    rw [integral_congr_ae (ae_of_all _ hpt)]
    have hfilt : ({p, m} : Finset ℂ).filter (fun x => M < x.re) =
        if M < m.re then {m} else ∅ := by
      rw [Finset.filter_insert, Finset.filter_singleton]
      simp [not_lt.2 hp.le]
    rw [hfilt] at hval
    refine mul_right_cancel₀ I_ne_zero ?_
    rw [hval]
    split_ifs with h
    · simp [hc_def, vertRes]
      ring
    · simp
  · have h1 := ih n (by omega) (a + 1) b (by omega)
    have h2 := ih n (by omega) a (b + 1) (by omega)
    have hpt : ∀ y : ℝ,
        (((M : ℂ) + y * I - p) ^ (a + 1))⁻¹ * (((M : ℂ) + y * I - m) ^ (b + 1))⁻¹ =
          -((((M : ℂ) + y * I - p) ^ (a + 1))⁻¹ * (((M : ℂ) + y * I - m) ^ b)⁻¹ -
            (((M : ℂ) + y * I - p) ^ a)⁻¹ * (((M : ℂ) + y * I - m) ^ (b + 1))⁻¹) / (m - p) := by
      intro y
      have e : m - p = ((M : ℂ) + y * I - p) - ((M : ℂ) + y * I - m) := by ring
      rw [e]
      exact inv_pow_mul_inv_pow_succ_succ (vert_ne_zero hp.ne y) (vert_ne_zero hm y) (e ▸ hD) a b
    refine ⟨((h1.1.sub h2.1).neg.div_const (m - p)).congr (ae_of_all _ fun y => (hpt y).symm), ?_⟩
    rw [integral_congr_ae (ae_of_all _ hpt), integral_div, integral_neg, integral_sub h1.1 h2.1,
      h1.2, h2.2, vertRes_succ_succ hD]
    split_ifs <;> ring

/-- **Two poles on either side.** For `p` to the left of the line `Re t = M`, `m` off the line and
`i + r ≥ 2`, `∫_ℝ (M+iy-p)^{-i} (M+iy-m)^{-r} dy` is `-2π` times the residue at `m` if `m` lies to
the right of the line, and `0` otherwise. -/
theorem integral_vert_two_poles {M : ℝ} {p m : ℂ} (hp : p.re < M) (hm : m.re ≠ M) {i r : ℕ}
    (hir : 2 ≤ i + r) :
    Integrable (fun y : ℝ => (((M : ℂ) + y * I - p) ^ i)⁻¹ * (((M : ℂ) + y * I - m) ^ r)⁻¹) ∧
      ∫ y : ℝ, (((M : ℂ) + y * I - p) ^ i)⁻¹ * (((M : ℂ) + y * I - m) ^ r)⁻¹ =
        if M < m.re then -2 * Real.pi * vertRes (m - p) i r else 0 := by
  by_cases hpm : p = m
  · subst hpm
    have : ¬ M < p.re := not_lt.2 hp.le
    simp only [this, ite_false, ← mul_inv, ← pow_add]
    exact ⟨integrable_vert_inv_pow hp.ne hir, integral_vert_inv_pow hp.ne hir⟩
  · exact integral_vert_two_poles_aux hp hm hpm (i + r - 2) i r (by omega)

/-! ### Bounds -/

lemma integral_inv_sq_add_sq {a : ℝ} (ha : a ≠ 0) :
    ∫ y : ℝ, (a ^ 2 + y ^ 2)⁻¹ = Real.pi / |a| := by
  have h := integral_univ_inv_one_add_mul_sq a⁻¹
  have e : ∀ y : ℝ, (a ^ 2 + y ^ 2)⁻¹ = (a ^ 2)⁻¹ * (1 + (a⁻¹ * y) ^ 2)⁻¹ := by
    intro y
    field_simp
  simp_rw [e]
  rw [integral_const_mul, h, abs_inv, ← sq_abs a]
  have : |a| ≠ 0 := abs_ne_zero.2 ha
  field_simp

lemma norm_vert_inv_pow_le {M : ℝ} {m : ℤ} (hMm : 1 / 2 ≤ |M - m|) {r : ℕ} (hr : 3 ≤ r)
    (y : ℝ) :
    ‖(((M : ℂ) + y * I - m) ^ r)⁻¹‖ ≤ 2 ^ (r - 3) * |M - m|⁻¹ * ((M - m) ^ 2 + y ^ 2)⁻¹ := by
  set z : ℂ := (M : ℂ) + y * I - m with hz_def
  set a : ℝ := M - m with ha_def
  have ha : 0 < |a| := by linarith
  have hsq : ‖z‖ ^ 2 = a ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z, a]
    ring
  have hre : |a| ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    simpa [z, a] using this
  have hpos : 0 < a ^ 2 + y ^ 2 := by
    have := pow_pos ha 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg y]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
  rw [norm_inv, norm_pow, show s + 3 - 3 = s by omega]
  calc (‖z‖ ^ (s + 3))⁻¹ = (‖z‖ ^ s * ‖z‖ * ‖z‖ ^ 2)⁻¹ := by ring
    _ ≤ ((1 / 2) ^ s * |a| * (a ^ 2 + y ^ 2))⁻¹ := by
        rw [hsq]
        refine inv_anti₀ (mul_pos (mul_pos (by positivity) ha) hpos) ?_
        gcongr
        linarith
    _ = 2 ^ s * |a|⁻¹ * (a ^ 2 + y ^ 2)⁻¹ := by
        rw [mul_inv, mul_inv, one_div, inv_pow, inv_inv]

lemma summable_inv_sub_intCast_sq (M : ℝ) : Summable fun m : ℤ => ((M - m) ^ 2)⁻¹ := by
  have h := (Real.summable_one_div_int_add_rpow (-M) 2).2 one_lt_two
  refine h.congr fun m => ?_
  rw [Real.rpow_two, sq_abs, one_div]
  ring

end OddZeta
