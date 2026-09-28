import OddZeta.Cert.ToolsAux1

/-!
# Analytic tools for the saddle-point certificates, part 4: the sign of `Re f'`

`Re f'(u) = (1/2) log Q(u)` with
`Q(u) = |η₀+u|^{2r} ∏_η |η+u|² / (|u|^{2r} ∏_η |η₀-η+u|²)`, so `Re f'(u) > 0 ↔ Q(u) > 1`
(`re_f'_eq_half_log_Q`, `re_f'_pos_iff`). On a box `[x₁, x₂] × [y₁, y₂]` with `y₂ < 0` and
`x₁ > -η₁`, the positivity of `Re f'` follows from a single inequality between products of
rational numbers built from the corners (`re_f'_pos_box`).
-/

namespace OddZeta.Cert

open Complex

/-! ### List helpers -/

theorem list_prod_nonneg_map {ι : Type*} (L : List ι) {f : ι → ℝ} (h : ∀ i ∈ L, 0 ≤ f i) :
    0 ≤ (L.map f).prod :=
  List.prod_nonneg fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact h i hi

theorem list_prod_pos_map {ι : Type*} (L : List ι) {f : ι → ℝ} (h : ∀ i ∈ L, 0 < f i) :
    0 < (L.map f).prod :=
  List.prod_pos fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact h i hi

theorem list_prod_le_prod_of_nonneg {ι : Type*} (L : List ι) {f g : ι → ℝ}
    (h0 : ∀ i ∈ L, 0 ≤ f i) (h : ∀ i ∈ L, f i ≤ g i) : (L.map f).prod ≤ (L.map g).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_le_mul (h a List.mem_cons_self)
      (ih (fun i hi => h0 i (List.mem_cons_of_mem _ hi))
        fun i hi => h i (List.mem_cons_of_mem _ hi))
      (list_prod_nonneg_map L fun i hi => h0 i (List.mem_cons_of_mem _ hi))
      ((h0 a List.mem_cons_self).trans (h a List.mem_cons_self))

theorem log_list_prod_map {ι : Type*} (L : List ι) {f : ι → ℝ} (h : ∀ i ∈ L, 0 < f i) :
    Real.log (L.map f).prod = (L.map fun i => Real.log (f i)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [Real.log_mul (h a List.mem_cons_self).ne'
      (list_prod_pos_map L fun i hi => h i (List.mem_cons_of_mem _ hi)).ne',
      ih fun i hi => h i (List.mem_cons_of_mem _ hi)]

theorem list_sum_map_sub {ι : Type*} (L : List ι) (f g : ι → ℝ) :
    (L.map fun i => f i - g i).sum = (L.map f).sum - (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem list_sum_map_mul_left {ι : Type*} (L : List ι) (f : ι → ℝ) (c : ℝ) :
    (L.map fun i => c * f i).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-! ### `Re f' = (1/2) log Q` -/

/-- `Q(u) = |η₀+u|^{2r} ∏_η |η+u|² / (|u|^{2r} ∏_η |η₀-η+u|²)`. -/
noncomputable def Qf (P : Params) (u : ℂ) : ℝ :=
  normSq ((P.eta0 : ℂ) + u) ^ P.r * ((P.zs ++ P.ps).map fun η : ℕ => normSq ((η : ℂ) + u)).prod /
    (normSq u ^ P.r * ((P.zs ++ P.ps).map fun η : ℕ => normSq ((P.eta0 : ℂ) - η + u)).prod)

variable {P : Params}

theorem log_normSq (z : ℂ) : Real.log (normSq z) = 2 * Real.log ‖z‖ := by
  rw [normSq_eq_norm_sq, Real.log_pow]
  push_cast
  ring

/-- `Re f'(u) = (1/2) log Q(u)` on `Ω`. -/
theorem re_f'_eq_half_log_Q {u : ℂ} (hu : u ∈ Omega P) :
    (P.f' u).re = Real.log (Qf P u) / 2 := by
  obtain ⟨h0, h1, h2⟩ := hu
  have hu0 : u ≠ 0 := fun h => slitPlane_ne_zero h0 (by rw [h, neg_zero])
  have hA := normSq_pos.2 (slitPlane_ne_zero h1)
  have hB := normSq_pos.2 hu0
  have hC : ∀ η ∈ P.zs ++ P.ps, 0 < normSq ((η : ℂ) + u) := fun η hη =>
    normSq_pos.2 (slitPlane_ne_zero (h2 η hη).1)
  have hD : ∀ η ∈ P.zs ++ P.ps, 0 < normSq ((P.eta0 : ℂ) - η + u) := fun η hη =>
    normSq_pos.2 (slitPlane_ne_zero (h2 η hη).2)
  have hCp := list_prod_pos_map _ hC
  have hDp := list_prod_pos_map _ hD
  unfold Qf
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hCp.ne',
    Real.log_mul (by positivity) hDp.ne', Real.log_pow, Real.log_pow, log_list_prod_map _ hC,
    log_list_prod_map _ hD, log_normSq, log_normSq, re_f']
  have eC : ((P.zs ++ P.ps).map fun η : ℕ => Real.log (normSq ((η : ℂ) + u))) =
      (P.zs ++ P.ps).map fun η : ℕ => 2 * Real.log ‖(η : ℂ) + u‖ :=
    List.map_congr_left fun η _ => log_normSq _
  have eD : ((P.zs ++ P.ps).map fun η : ℕ => Real.log (normSq ((P.eta0 : ℂ) - η + u))) =
      (P.zs ++ P.ps).map fun η : ℕ => 2 * Real.log ‖(P.eta0 : ℂ) - η + u‖ :=
    List.map_congr_left fun η _ => log_normSq _
  rw [eC, eD, list_sum_map_mul_left, list_sum_map_mul_left, list_sum_map_sub]
  ring

/-- `Re f'(u) > 0 ↔ Q(u) > 1` on `Ω`. -/
theorem re_f'_pos_iff {u : ℂ} (hu : u ∈ Omega P) : 0 < (P.f' u).re ↔ 1 < Qf P u := by
  have hQ : 0 < Qf P u := by
    obtain ⟨h0, h1, h2⟩ := hu
    have hu0 : u ≠ 0 := fun h => slitPlane_ne_zero h0 (by rw [h, neg_zero])
    have hA := normSq_pos.2 (slitPlane_ne_zero h1)
    have hB := normSq_pos.2 hu0
    have hCp := list_prod_pos_map (P.zs ++ P.ps) (f := fun η : ℕ => normSq ((η : ℂ) + u))
      fun η hη => normSq_pos.2 (slitPlane_ne_zero (h2 η hη).1)
    have hDp := list_prod_pos_map (P.zs ++ P.ps)
      (f := fun η : ℕ => normSq ((P.eta0 : ℂ) - η + u))
      fun η hη => normSq_pos.2 (slitPlane_ne_zero (h2 η hη).2)
    unfold Qf
    positivity
  rw [re_f'_eq_half_log_Q hu, ← Real.log_pos_iff hQ.le]
  constructor <;> intro h <;> linarith

/-! ### The box criterion -/

/-- **Positivity of `Re f'` on a box** `[x₁, x₂] × [y₁, y₂]` with `-η₁ < x₁` and `y₂ < 0`: it
suffices that the product of the minima over the box of the numerator factors of `Q` exceeds the
product of the maxima of its denominator factors. -/
theorem re_f'_pos_box (hP : P.Valid) {u : ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hx₁ : -(P.etaOne : ℝ) < x₁)
    (hx : x₁ ≤ u.re ∧ u.re ≤ x₂) (hy : y₁ ≤ u.im ∧ u.im ≤ y₂) (hy₂ : y₂ < 0)
    (hQ : (max (x₁ ^ 2) (x₂ ^ 2) + y₁ ^ 2) ^ P.r *
          ((P.zs ++ P.ps).map fun η : ℕ => ((P.eta0 : ℝ) - η + x₂) ^ 2 + y₁ ^ 2).prod <
        (((P.eta0 : ℝ) + x₁) ^ 2 + y₂ ^ 2) ^ P.r *
          ((P.zs ++ P.ps).map fun η : ℕ => ((η : ℝ) + x₁) ^ 2 + y₂ ^ 2).prod) :
    0 < (P.f' u).re := by
  have hu : u ∈ Omega P := mem_Omega_of_im_ne_zero P (by linarith [hy.2])
  obtain ⟨h0, h⟩ := re_pos_of_re hP (u := (x₁ : ℂ)) (by simpa using hx₁)
  simp only [ofReal_re] at h0 h
  rw [re_f'_pos_iff hu]
  have hyy : y₂ ^ 2 ≤ u.im ^ 2 ∧ u.im ^ 2 ≤ y₁ ^ 2 := by
    constructor <;> nlinarith [hy.1, hy.2]
  -- the numerator is at least the product of minima
  have hnum : (((P.eta0 : ℝ) + x₁) ^ 2 + y₂ ^ 2) ^ P.r *
      ((P.zs ++ P.ps).map fun η : ℕ => ((η : ℝ) + x₁) ^ 2 + y₂ ^ 2).prod ≤
      normSq ((P.eta0 : ℂ) + u) ^ P.r *
        ((P.zs ++ P.ps).map fun η : ℕ => normSq ((η : ℂ) + u)).prod := by
    apply mul_le_mul
    · apply pow_le_pow_left₀ (by positivity)
      rw [normSq_apply]
      simp only [add_re, natCast_re, add_im, natCast_im, zero_add]
      nlinarith [hx.1]
    · refine list_prod_le_prod_of_nonneg _ (fun η _ => by positivity) fun η hη => ?_
      rw [normSq_apply]
      simp only [add_re, natCast_re, add_im, natCast_im, zero_add]
      nlinarith [hx.1, (h η hη).1]
    · exact list_prod_nonneg_map _ fun η _ => by positivity
    · exact pow_nonneg (normSq_nonneg _) _
  -- the denominator is at most the product of maxima
  have hden : normSq u ^ P.r *
      ((P.zs ++ P.ps).map fun η : ℕ => normSq ((P.eta0 : ℂ) - η + u)).prod ≤
      (max (x₁ ^ 2) (x₂ ^ 2) + y₁ ^ 2) ^ P.r *
        ((P.zs ++ P.ps).map fun η : ℕ => ((P.eta0 : ℝ) - η + x₂) ^ 2 + y₁ ^ 2).prod := by
    apply mul_le_mul
    · apply pow_le_pow_left₀ (normSq_nonneg _)
      rw [normSq_apply]
      have : u.re ^ 2 ≤ max (x₁ ^ 2) (x₂ ^ 2) := by
        rcases le_total 0 u.re with h1 | h1
        · exact le_max_of_le_right (by nlinarith [hx.2])
        · exact le_max_of_le_left (by nlinarith [hx.1])
      nlinarith
    · refine list_prod_le_prod_of_nonneg _ (fun η _ => normSq_nonneg _) fun η hη => ?_
      rw [normSq_apply]
      simp only [add_re, sub_re, natCast_re, add_im, sub_im, natCast_im, sub_zero, zero_add]
      nlinarith [hx.1, hx.2, (h η hη).2]
    · exact list_prod_nonneg_map _ fun η _ => normSq_nonneg _
    · positivity
  have hden_pos : 0 < normSq u ^ P.r *
      ((P.zs ++ P.ps).map fun η : ℕ => normSq ((P.eta0 : ℂ) - η + u)).prod := by
    obtain ⟨h0', -, h2'⟩ := hu
    have hu0 : u ≠ 0 := fun h => slitPlane_ne_zero h0' (by rw [h, neg_zero])
    have := list_prod_pos_map (P.zs ++ P.ps) (f := fun η : ℕ => normSq ((P.eta0 : ℂ) - η + u))
      fun η hη => normSq_pos.2 (slitPlane_ne_zero (h2' η hη).2)
    have := normSq_pos.2 hu0
    positivity
  unfold Qf
  rw [one_lt_div hden_pos]
  linarith

end OddZeta.Cert
