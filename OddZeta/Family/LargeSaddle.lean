import OddZeta.Family.LargeNum

/-!
# The saddle point for `r ≥ 301` (Lemma 8.5 and Section 8.7 of the note)

Near `a = famA` (`‖z - a‖ ≤ 1/8`, so `Re z ≥ 4`) we have `‖g'''‖ ≤ 0.0651`, `‖e''‖ ≤ 0.0254`,
`‖e'''‖ ≤ 0.00033`, `‖e'‖ ≤ 0.03`. With `ũ = a - (2π/(r D̄)) i` the simplified Newton map
(`Cert.exists_saddle`) gives a zero `u*` of `F' = r g' + e' - 2πi` with `‖u* - ũ‖ ≤ 1.8/r`.
-/

namespace OddZeta

open Complex Metric Set

namespace Large

/-! ### Bounds near `a` -/

theorem near_re {z : ℂ} (hz : ‖z - famA‖ ≤ 1 / 8) : 4 ≤ z.re := by
  have h1 : |(z - famA).re| ≤ ‖z - famA‖ := abs_re_le_norm _
  have h2 := famA_lo
  rw [sub_re, ofReal_re] at h1
  have := (abs_le.1 (h1.trans hz)).1
  linarith

theorem near_re_pos {z : ℂ} (hz : ‖z - famA‖ ≤ 1 / 8) : 0 < z.re := by
  linarith [near_re hz]

theorem S2_four : S2 4 ≤ 0.0651 := by
  norm_num [S2, famCB]

theorem S2_268 : S2 2.68 ≤ 0.142 := by
  norm_num [S2, famCB]

theorem norm_famG3_near {z : ℂ} (hz : ‖z - famA‖ ≤ 1 / 8) : ‖famG3 z‖ ≤ 0.0651 :=
  (norm_famG3_le (by norm_num) (near_re hz)).trans S2_four

theorem norm_famE2_near {z : ℂ} (hz : ‖z - famA‖ ≤ 1 / 8) : ‖famE2 z‖ ≤ 0.0254 :=
  (norm_famE2_le (by norm_num) (near_re hz)).trans (by norm_num)

theorem norm_famE3_near {z : ℂ} (hz : ‖z - famA‖ ≤ 1 / 8) : ‖famE3 z‖ ≤ 0.00033 :=
  (norm_famE3_le (by norm_num) (near_re hz)).trans (by norm_num)

theorem mem_near {z : ℂ} (hz : z ∈ closedBall (famA : ℂ) (1 / 8)) : ‖z - famA‖ ≤ 1 / 8 :=
  mem_closedBall_iff_norm.1 hz

theorem famA_mem_near : (famA : ℂ) ∈ closedBall (famA : ℂ) (1 / 8) :=
  mem_closedBall_self (by norm_num)

theorem norm_famG2_sub_le {z : ℂ} (hz : ‖z - famA‖ ≤ 1 / 8) :
    ‖famG2 z - famG2 famA‖ ≤ 0.0651 * ‖z - famA‖ :=
  (convex_closedBall (famA : ℂ) (1 / 8)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun _ hw => (hasDerivAt_famG2 (near_re_pos (mem_near hw))).hasDerivWithinAt)
    (fun _ hw => norm_famG3_near (mem_near hw)) famA_mem_near (mem_closedBall_iff_norm.2 hz)

theorem norm_famE1_near {z : ℂ} (hz : ‖z - famA‖ ≤ 1 / 8) : ‖famE1 z‖ ≤ 0.03 := by
  have h := (convex_closedBall (famA : ℂ) (1 / 8)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun _ hw => (hasDerivAt_famE1 (near_re_pos (mem_near hw))).hasDerivWithinAt)
    (fun _ hw => norm_famE2_near (mem_near hw)) famA_mem_near (mem_closedBall_iff_norm.2 hz)
  have h1 := norm_famE1_famA
  have h2 : ‖famE1 z‖ ≤ ‖famE1 z - famE1 famA‖ + ‖famE1 famA‖ := norm_le_norm_sub_add _ _
  nlinarith [norm_nonneg (z - famA)]

theorem norm_famE_sub_le {z : ℂ} (hz : ‖z - famA‖ ≤ 1 / 8) :
    ‖famE z - famE famA‖ ≤ 0.03 * ‖z - famA‖ :=
  (convex_closedBall (famA : ℂ) (1 / 8)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun _ hw => (hasDerivAt_famE (near_re_pos (mem_near hw))).hasDerivWithinAt)
    (fun _ hw => norm_famE1_near (mem_near hw)) famA_mem_near (mem_closedBall_iff_norm.2 hz)

theorem near_of_mem_ball {v w : ℂ} (hv : ‖v‖ ≤ 1 / 8) (hw : w ∈ closedBall (famA : ℂ) ‖v‖) :
    ‖w - famA‖ ≤ 1 / 8 :=
  (mem_closedBall_iff_norm.1 hw).trans hv

/-- First-order Taylor bound for `g'` at `a` (where `g'(a) = 0`, `g''(a) = -D̄`). -/
theorem taylor_famG1 {v : ℂ} (hv : ‖v‖ ≤ 1 / 8) :
    ‖famG1 (famA + v) - (-(famD : ℂ)) * v‖ ≤ 0.0651 * ‖v‖ ^ 2 / 2 := by
  have := norm_taylor_one_le (g := famG1) (h := famG2) (k := famG3) (u := famA) (v := v)
    (M := 0.0651)
    (fun w hw => hasDerivAt_famG1 (near_re_pos (near_of_mem_ball hv hw)))
    (fun w hw => hasDerivAt_famG2 (near_re_pos (near_of_mem_ball hv hw)))
    (fun _ hw => norm_famG3_near (near_of_mem_ball hv hw))
  rwa [famG1_famA, famG2_famA, sub_zero] at this

/-- Second-order Taylor bound for `g` at `a`. -/
theorem taylor_famG {v : ℂ} (hv : ‖v‖ ≤ 1 / 8) :
    ‖famG (famA + v) - famG famA - (-(famD : ℂ)) * v ^ 2 / 2‖ ≤ 0.0651 * ‖v‖ ^ 3 / 6 := by
  have := Cert.norm_taylor_two_le (F := famG) (g := famG1) (h := famG2) (k := famG3) (u := famA)
    (v := v) (M := 0.0651)
    (fun w hw => hasDerivAt_famG (near_re_pos (near_of_mem_ball hv hw)))
    (fun w hw => hasDerivAt_famG1 (near_re_pos (near_of_mem_ball hv hw)))
    (fun w hw => hasDerivAt_famG2 (near_re_pos (near_of_mem_ball hv hw)))
    (fun _ hw => norm_famG3_near (near_of_mem_ball hv hw)) famG1_famA
    (s := 1) ⟨by norm_num, le_rfl⟩
  rw [famG2_famA] at this
  simpa using this

theorem norm_famG_sub_le {v : ℂ} (hv : ‖v‖ ≤ 1 / 8) :
    ‖famG (famA + v) - famG famA‖ ≤ famD * ‖v‖ ^ 2 / 2 + 0.0651 * ‖v‖ ^ 3 / 6 := by
  have h := taylor_famG hv
  have e : ‖(-(famD : ℂ)) * v ^ 2 / 2‖ = famD * ‖v‖ ^ 2 / 2 := by
    rw [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos famD_pos, norm_pow]
    norm_num
  have h2 := norm_add_le (famG (famA + v) - famG famA - (-(famD : ℂ)) * v ^ 2 / 2)
    ((-(famD : ℂ)) * v ^ 2 / 2)
  rw [sub_add_cancel, e] at h2
  linarith

/-! ### The phase function of the family in terms of `g` and `e` -/

theorem saddle_expr {r : ℕ} (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    (fam r).f' u + I * (((fam r).r : ℂ) - 2) * Real.pi =
      r * famG1 u + famE1 u - 2 * Real.pi * I := by
  rw [Fam.f'_eq hr hu, Fam.r_eq]
  ring

/-! ### Existence of the saddle point -/

theorem twoPi_div_D : (34.27 : ℝ) ≤ 2 * Real.pi / famD ∧ 2 * Real.pi / famD ≤ 34.3 := by
  obtain ⟨h1, h2⟩ := famD_bounds
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have hD := famD_pos
  constructor
  · rw [le_div_iff₀ hD]; nlinarith
  · rw [div_le_iff₀ hD]; nlinarith

/-- **The saddle point** for `r ≥ 301`: `u* = a + w` with `|Re w| ≤ 1.8/r`,
`-36.1/r ≤ Im w ≤ -32.4/r`, `‖w‖ ≤ 36.1/r`. -/
theorem exists_saddle_large (r : ℕ) (hr : 301 ≤ r) :
    ∃ u : ℂ, (fam r).f' u + I * (((fam r).r : ℂ) - 2) * Real.pi = 0 ∧
      |(u - famA).re| ≤ 1.8 / r ∧ -(36.1 / r) ≤ (u - famA).im ∧ (u - famA).im ≤ -(32.4 / r) ∧
      ‖u - famA‖ ≤ 36.1 / r := by
  have hr1 : 1 ≤ r := by omega
  set R : ℝ := (r : ℝ) with hRdef
  have hR : (301 : ℝ) ≤ R := by rw [hRdef]; exact_mod_cast hr
  have hR0 : 0 < R := by linarith
  obtain ⟨hP2lo, hP2hi⟩ := twoPi_div_D
  set P2 : ℝ := 2 * Real.pi / famD with hP2
  have hD := famD_pos
  set τ : ℝ := P2 / R with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hRτ : R * τ = P2 := by rw [hτ]; field_simp
  have hτle : τ ≤ 34.3 / 301 := by
    rw [hτ, div_le_div_iff₀ hR0 (by norm_num)]; nlinarith
  set vt : ℂ := -((τ : ℝ) : ℂ) * I with hvt
  have hvt_norm : ‖vt‖ = τ := by
    rw [hvt, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0, norm_I,
      mul_one]
  have hvt_re : vt.re = 0 := by simp [hvt]
  have hvt_im : vt.im = -τ := by simp [hvt]
  set ut : ℂ := famA + vt with hut
  have hut_im : ut.im = -τ := by simp [hut, hvt_im]
  set ρ : ℝ := 1.8 / R with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hRρ : R * ρ = 1.8 := by rw [hρ]; field_simp
  have hτρ : τ + ρ ≤ 36.1 / R := by
    rw [hτ, hρ, ← add_div, div_le_div_iff_of_pos_right hR0]; linarith
  have h36 : 36.1 / R ≤ 1 / 8 := by rw [div_le_iff₀ hR0]; linarith
  -- the disc `closedBall ut ρ` is close to `a`
  have hnear : ∀ z ∈ closedBall ut ρ, ‖z - famA‖ ≤ 36.1 / R := by
    intro z hz
    rw [mem_closedBall_iff_norm] at hz
    have : z - famA = (z - ut) + vt := by rw [hut]; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [hvt_norm]
    linarith
  have hut_near : ‖ut - famA‖ ≤ 36.1 / R := hnear ut (mem_closedBall_self hρ0)
  have hut_near' : ‖ut - famA‖ ≤ τ := by rw [hut, add_sub_cancel_left, hvt_norm]
  -- `ut` in the lower half-plane
  have hball : closedBall ut ρ ⊆ Cert.Omega (fam r) := by
    apply Cert.closedBall_subset_Omega
    rw [hut_im]
    have : ρ < τ := by
      rw [hρ, hτ, div_lt_div_iff_of_pos_right hR0]; linarith
    linarith
  have hut_neg : ut.im < 0 := by
    rw [hut_im]
    have : 0 < τ := by rw [hτ]; positivity
    linarith
  -- `f''(ut)`
  have hf2 : 0.1756 * R ≤ ‖(fam r).f'' ut‖ := by
    rw [Fam.f''_eq hr1]
    have hδ := norm_famG2_sub_le (hut_near.trans h36)
    rw [famG2_famA] at hδ
    have he2 := norm_famE2_near (hut_near.trans h36)
    have e : (r : ℂ) * famG2 ut + famE2 ut =
        ((-(R * famD) : ℝ) : ℂ) + ((r : ℂ) * (famG2 ut - -(famD : ℂ)) + famE2 ut) := by
      rw [hRdef]; push_cast; ring
    rw [e]
    have h1 := norm_sub_le (((-(R * famD) : ℝ) : ℂ) + ((r : ℂ) * (famG2 ut - -(famD : ℂ)) +
      famE2 ut)) ((r : ℂ) * (famG2 ut - -(famD : ℂ)) + famE2 ut)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity)] at h1
    have h2 : ‖(r : ℂ) * (famG2 ut - -(famD : ℂ)) + famE2 ut‖ ≤ R * (0.0651 * τ) + 0.0254 := by
      refine (norm_add_le _ _).trans (add_le_add ?_ he2)
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hδ.trans (by nlinarith)) hR0.le
    have h3 : R * (0.0651 * τ) = 0.0651 * P2 := by rw [← hRτ]; ring
    have h4 : 0.1832 * R ≤ R * famD := by nlinarith [famD_bounds.1]
    linarith
  -- `F'(ut)`
  have hf1 : ‖(fam r).f' ut + I * (((fam r).r : ℂ) - 2) * Real.pi‖ ≤ 0.158 := by
    rw [saddle_expr hr1 hut_neg]
    have hv8 : ‖vt‖ ≤ 1 / 8 := by rw [hvt_norm]; linarith
    have hT := taylor_famG1 hv8
    have he1 := norm_famE1_near (hut_near.trans h36)
    have e : (r : ℂ) * famG1 ut + famE1 ut - 2 * Real.pi * I =
        (r : ℂ) * (famG1 (famA + vt) - (-(famD : ℂ)) * vt) + famE1 ut := by
      have hreal : R * famD * τ = 2 * Real.pi := by
        rw [mul_right_comm, hRτ, hP2]; field_simp
      have : (r : ℂ) * (-(famD : ℂ) * vt) = 2 * Real.pi * I := by
        calc (r : ℂ) * (-(famD : ℂ) * vt) = ((R * famD * τ : ℝ) : ℂ) * I := by
              rw [hvt, hRdef]; push_cast; ring
          _ = 2 * Real.pi * I := by rw [hreal]; push_cast; ring
      rw [hut]
      linear_combination this
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_natCast, ← hRdef]
    have h1 : R * ‖famG1 (famA + vt) - -(famD : ℂ) * vt‖ ≤ R * (0.0651 * τ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by rw [← hvt_norm]; exact hT) hR0.le
    have h2 : R * (0.0651 * τ ^ 2 / 2) = 0.0651 / 2 * P2 * τ := by rw [← hRτ]; ring
    have h3 : 0.0651 / 2 * P2 * τ ≤ 0.0651 / 2 * 34.3 * (34.3 / 301) := by
      gcongr
    have h4 : (0.0651 : ℝ) / 2 * 34.3 * (34.3 / 301) + 0.03 ≤ 0.158 := by norm_num
    linarith
  -- `f'''` on the disc
  have hf3 : ∀ z ∈ closedBall ut ρ, ‖(fam r).f''' z‖ ≤ 0.0651 * R + 0.00033 := by
    intro z hz
    have hz' := (hnear z hz).trans h36
    rw [Fam.f'''_eq hr1]
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_famE3_near hz'))
    rw [norm_mul, Complex.norm_natCast, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_famG3_near hz') hR0.le
  obtain ⟨u, hu, hsad⟩ := Cert.exists_saddle (P := fam r) (ut := ut) (ρ := ρ) (m := 0.1756 * R)
    (ε := 0.158) (M := 0.0651 * R + 0.00033) hball (by positivity) hf2 hf1 hf3
    (by
      have : (0.0651 * R + 0.00033) * ρ = 0.0651 * 1.8 + 0.00033 * ρ := by rw [← hRρ]; ring
      rw [this]
      have : ρ ≤ 1 := by rw [hρ, div_le_one hR0]; linarith
      nlinarith)
    (by
      have : 0.1756 * R * ρ / 2 = 0.1756 * 1.8 / 2 := by rw [← hRρ]; ring
      rw [this]; norm_num)
  refine ⟨u, hsad, ?_, ?_, ?_, ?_⟩
  · rw [mem_closedBall_iff_norm] at hu
    have e : (u - famA).re = (u - ut).re := by simp [hut, hvt_re]
    rw [e]
    exact (abs_re_le_norm _).trans hu
  · rw [mem_closedBall_iff_norm] at hu
    have e : (u - famA).im = (u - ut).im - τ := by simp [hut, hvt_im]
    rw [e]
    have := (abs_le.1 ((abs_im_le_norm (u - ut)).trans hu)).1
    have : -(36.1 / R) ≤ -τ - ρ := by linarith
    linarith
  · rw [mem_closedBall_iff_norm] at hu
    have e : (u - famA).im = (u - ut).im - τ := by simp [hut, hvt_im]
    rw [e]
    have := (abs_le.1 ((abs_im_le_norm (u - ut)).trans hu)).2
    have : ρ - τ ≤ -(32.4 / R) := by
      rw [hρ, hτ, div_sub_div_same, neg_div', div_le_div_iff_of_pos_right hR0]; linarith
    linarith
  · exact hnear u hu

end Large

end OddZeta
