import OddZeta.Family.Phase
import OddZeta.Cert.Tools

/-!
# Analytic helpers for the asymptotic regime `r ≥ 301` (Section 8.7 of the note)

* derivatives of the `r`-independent functions `g = famG` and `e = famE` on `{Re u > 0}`;
* the bounds `‖g''(u)‖ ≤ S₁(ξ)`, `‖g'''(u)‖ ≤ S₂(ξ)` (and similarly for `e`) for `Re u ≥ ξ > 0`
  (the functions `M_k^{hp}` of the note);
* a first-order Taylor bound with remainder `M ‖v‖² / 2`.
-/

namespace OddZeta

open Complex Metric Set

namespace Large

theorem natCast_add_mem_slitPlane (b : ℕ) {u : ℂ} (hu : 0 < u.re) : (b : ℂ) + u ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inl (by simp; positivity))

theorem add_mem_slitPlane_of {c u : ℂ} (hc : 0 ≤ c.re) (hu : 0 < u.re) : c + u ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inl (by rw [add_re]; linarith))

theorem add74_mem {u : ℂ} (hu : 0 < u.re) : (74 : ℂ) + u ∈ slitPlane :=
  add_mem_slitPlane_of (by norm_num) hu

theorem add76_mem {u : ℂ} (hu : 0 < u.re) : (76 : ℂ) + u ∈ slitPlane :=
  add_mem_slitPlane_of (by norm_num) hu

theorem natCast_add_ne_zero (b : ℕ) {u : ℂ} (hu : 0 < u.re) : (b : ℂ) + u ≠ 0 :=
  slitPlane_ne_zero (natCast_add_mem_slitPlane b hu)

/-! ### Derivatives -/

theorem hasDerivAt_famG {u : ℂ} (hu : 0 < u.re) : HasDerivAt famG (famG1 u) u := by
  have h := Cert.hasDerivAt_list_sum famCB
    (g := fun bc w => (bc.2 : ℂ) * ((bc.1 : ℂ) + w) * log ((bc.1 : ℂ) + w))
    (g' := fun bc => (bc.2 : ℂ) * (log ((bc.1 : ℂ) + u) + 1))
    (fun bc _ => by
      have := (Cert.hasDerivAt_add_mul_log (bc.1 : ℂ) (natCast_add_mem_slitPlane bc.1 hu)).const_mul
        (bc.2 : ℂ)
      simpa only [mul_assoc] using this)
  refine (h.add_const ((famKg : ℝ) : ℂ)).congr_deriv ?_
  simp only [famG1, famCB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem hasDerivAt_famG1 {u : ℂ} (hu : 0 < u.re) : HasDerivAt famG1 (famG2 u) u := by
  have h := Cert.hasDerivAt_list_sum famCB
    (g := fun bc w => (bc.2 : ℂ) * log ((bc.1 : ℂ) + w))
    (g' := fun bc => (bc.2 : ℂ) * ((bc.1 : ℂ) + u)⁻¹)
    (fun bc _ => (Cert.hasDerivAt_log_add (bc.1 : ℂ) (natCast_add_mem_slitPlane bc.1 hu)).const_mul
      (bc.2 : ℂ))
  exact h

theorem hasDerivAt_famG2 {u : ℂ} (hu : 0 < u.re) : HasDerivAt famG2 (famG3 u) u := by
  have h := Cert.hasDerivAt_list_sum famCB
    (g := fun bc w => (bc.2 : ℂ) * ((bc.1 : ℂ) + w)⁻¹)
    (g' := fun bc => -((bc.2 : ℂ) * (((bc.1 : ℂ) + u) ^ 2)⁻¹))
    (fun bc _ => by
      have := (Cert.hasDerivAt_inv_add (bc.1 : ℂ) (natCast_add_ne_zero bc.1 hu)).const_mul
        (bc.2 : ℂ)
      simpa only [mul_neg] using this)
  unfold famG3
  rw [← Cert.list_sum_map_neg]
  exact h

theorem hasDerivAt_famE {u : ℂ} (hu : 0 < u.re) : HasDerivAt famE (famE1 u) u := by
  refine (((Cert.hasDerivAt_add_mul_log (74 : ℂ) (add74_mem hu)).sub
    (Cert.hasDerivAt_add_mul_log (76 : ℂ) (add76_mem hu))).add_const
    ((2 : ℂ) * ((Real.log 2 : ℝ) : ℂ))).congr_deriv ?_
  unfold famE1
  ring

theorem hasDerivAt_famE1 {u : ℂ} (hu : 0 < u.re) : HasDerivAt famE1 (famE2 u) u :=
  (Cert.hasDerivAt_log_add (74 : ℂ) (add74_mem hu)).sub
    (Cert.hasDerivAt_log_add (76 : ℂ) (add76_mem hu))

theorem hasDerivAt_famE2 {u : ℂ} (hu : 0 < u.re) : HasDerivAt famE2 (famE3 u) u := by
  refine ((Cert.hasDerivAt_inv_add (74 : ℂ) (slitPlane_ne_zero (add74_mem hu))).sub
    (Cert.hasDerivAt_inv_add (76 : ℂ) (slitPlane_ne_zero (add76_mem hu)))).congr_deriv ?_
  unfold famE3
  ring

/-! ### Norm bounds for `Re u ≥ ξ > 0` -/

/-- `S₁(ξ) = ∑ |c_b| / (b + ξ)`. -/
noncomputable def S1 (ξ : ℝ) : ℝ := (famCB.map fun bc : ℕ × ℤ => |(bc.2 : ℝ)| / ((bc.1 : ℝ) + ξ)).sum

/-- `S₂(ξ) = ∑ |c_b| / (b + ξ)²`. -/
noncomputable def S2 (ξ : ℝ) : ℝ :=
  (famCB.map fun bc : ℕ × ℤ => |(bc.2 : ℝ)| / ((bc.1 : ℝ) + ξ) ^ 2).sum

theorem le_norm_add {b : ℝ} {u : ℂ} {ξ : ℝ} (hu : ξ ≤ u.re) : b + ξ ≤ ‖(b : ℂ) + u‖ := by
  refine le_trans ?_ (re_le_norm _)
  simp only [add_re, ofReal_re]
  linarith

theorem le_norm_natCast_add (b : ℕ) {u : ℂ} {ξ : ℝ} (hu : ξ ≤ u.re) :
    (b : ℝ) + ξ ≤ ‖(b : ℂ) + u‖ := by
  have := le_norm_add (b := (b : ℝ)) hu
  simpa using this

theorem norm_inv_le_of_le {z : ℂ} {t : ℝ} (ht : 0 < t) (h : t ≤ ‖z‖) : ‖z⁻¹‖ ≤ 1 / t := by
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le ht h

theorem norm_famG2_le {ξ : ℝ} (hξ : 0 < ξ) {u : ℂ} (hu : ξ ≤ u.re) : ‖famG2 u‖ ≤ S1 ξ := by
  unfold famG2 S1
  refine Cert.norm_list_sum_map_le _ fun bc _ => ?_
  rw [norm_mul, Complex.norm_intCast]
  have h0 : 0 < (bc.1 : ℝ) + ξ := by positivity
  have := norm_inv_le_of_le h0 (le_norm_natCast_add bc.1 hu)
  calc |(bc.2 : ℝ)| * ‖((bc.1 : ℂ) + u)⁻¹‖ ≤ |(bc.2 : ℝ)| * (1 / ((bc.1 : ℝ) + ξ)) := by gcongr
    _ = |(bc.2 : ℝ)| / ((bc.1 : ℝ) + ξ) := by ring

theorem norm_famG3_le {ξ : ℝ} (hξ : 0 < ξ) {u : ℂ} (hu : ξ ≤ u.re) : ‖famG3 u‖ ≤ S2 ξ := by
  unfold famG3 S2
  rw [norm_neg]
  refine Cert.norm_list_sum_map_le _ fun bc _ => ?_
  rw [norm_mul, Complex.norm_intCast]
  have h0 : 0 < (bc.1 : ℝ) + ξ := by positivity
  have := Cert.norm_inv_sq_le h0 (le_norm_natCast_add bc.1 hu)
  calc |(bc.2 : ℝ)| * ‖(((bc.1 : ℂ) + u) ^ 2)⁻¹‖ ≤ |(bc.2 : ℝ)| * (1 / ((bc.1 : ℝ) + ξ) ^ 2) := by
        gcongr
    _ = |(bc.2 : ℝ)| / ((bc.1 : ℝ) + ξ) ^ 2 := by ring

theorem le_norm_add74 {u : ℂ} {ξ : ℝ} (hu : ξ ≤ u.re) : (74 : ℝ) + ξ ≤ ‖(74 : ℂ) + u‖ := by
  refine le_trans ?_ (re_le_norm _)
  rw [add_re]
  norm_num
  linarith

theorem le_norm_add76 {u : ℂ} {ξ : ℝ} (hu : ξ ≤ u.re) : (76 : ℝ) + ξ ≤ ‖(76 : ℂ) + u‖ := by
  refine le_trans ?_ (re_le_norm _)
  rw [add_re]
  norm_num
  linarith

theorem norm_famE2_le {ξ : ℝ} (hξ : 0 < ξ) {u : ℂ} (hu : ξ ≤ u.re) :
    ‖famE2 u‖ ≤ 1 / (74 + ξ) + 1 / (76 + ξ) := by
  unfold famE2
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_inv_le_of_le (by positivity) (le_norm_add74 hu)
  · exact norm_inv_le_of_le (by positivity) (le_norm_add76 hu)

theorem norm_famE3_le {ξ : ℝ} (hξ : 0 < ξ) {u : ℂ} (hu : ξ ≤ u.re) :
    ‖famE3 u‖ ≤ 1 / (74 + ξ) ^ 2 + 1 / (76 + ξ) ^ 2 := by
  unfold famE3
  rw [norm_neg]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · exact Cert.norm_inv_sq_le (by positivity) (le_norm_add74 hu)
  · exact Cert.norm_inv_sq_le (by positivity) (le_norm_add76 hu)

/-! ### First-order Taylor bound -/

/-- `‖g(u+v) - g(u) - h(u) v‖ ≤ M ‖v‖² / 2` if `g' = h` and `‖h'‖ ≤ M` on the disc. -/
theorem norm_taylor_one_le {g h k : ℂ → ℂ} {u v : ℂ} {M : ℝ}
    (hg : ∀ w ∈ closedBall u ‖v‖, HasDerivAt g (h w) w)
    (hh : ∀ w ∈ closedBall u ‖v‖, HasDerivAt h (k w) w)
    (hk : ∀ w ∈ closedBall u ‖v‖, ‖k w‖ ≤ M) :
    ‖g (u + v) - g u - h u * v‖ ≤ M * ‖v‖ ^ 2 / 2 := by
  have hu : u ∈ closedBall u ‖v‖ := mem_closedBall_self (norm_nonneg _)
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, u + (t : ℂ) * v ∈ closedBall u ‖v‖ := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have step1 : ∀ w ∈ closedBall u ‖v‖, ‖h w - h u‖ ≤ M * ‖w - u‖ := fun w hw =>
    (convex_closedBall u ‖v‖).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun w hw => (hh w hw).hasDerivWithinAt) hk hu hw
  set φ : ℝ → ℂ := fun t => g (u + (t : ℂ) * v) - g u - h u * v * t with hφ
  have hφd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ (h (u + (t : ℂ) * v) * v - h u * v) t := by
    intro t ht
    have h1 := (hg _ (hmem t ht)).comp t (Cert.hasDerivAt_line u v t)
    have h2 := (Cert.hasDerivAt_ofReal' t).const_mul (h u * v)
    convert (h1.sub_const (g u)).sub h2 using 1
    · rw [hφ]; rfl
    · ring
  have step2 : ∀ t ∈ Icc (0 : ℝ) 1, ‖φ t‖ ≤ M * ‖v‖ ^ 2 * t ^ 2 / 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f' := fun t => h (u + (t : ℂ) * v) * v - h u * v)
      (B' := fun t => M * ‖v‖ ^ 2 * t)
      (fun t ht => (hφd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hφd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) ?_ ?_ ?_
    · simp [hφ]
    · intro t
      convert ((hasDerivAt_pow 2 t).const_mul (M * ‖v‖ ^ 2)).div_const 2 using 1
      push_cast; ring
    · intro t ht
      have ht' := Ico_subset_Icc_self ht
      have e : h (u + (t : ℂ) * v) * v - h u * v = (h (u + (t : ℂ) * v) - h u) * v := by ring
      rw [e, norm_mul]
      have := step1 _ (hmem t ht')
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht.1] at this
      calc ‖h (u + ↑t * v) - h u‖ * ‖v‖ ≤ M * (t * ‖v‖) * ‖v‖ := by gcongr
        _ = M * ‖v‖ ^ 2 * t := by ring
  have := step2 1 ⟨zero_le_one, le_rfl⟩
  simpa [hφ] using this

end Large

end OddZeta
