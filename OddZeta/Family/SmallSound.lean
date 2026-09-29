import OddZeta.Family.SmallMach

/-!
# Soundness of the per-`r` certificate checker: `famCertOK r d = true → FamCert r`

In three stages: the saddle point (`saddle_stage`: contraction, decay along `σ`, `H_d`, `α`),
the bound `Re Fd ≤ T` on `L \ σ` and the geometry of the path (`path_stage`).
-/

namespace OddZeta.Small

open Complex Metric Set OddZeta.Cert OddZeta.Cert.QI OddZeta.FamNum

theorem ratCast_rho : ((rho : ℚ) : ℝ) = 1 / 10000000000 := by norm_num [rho]

theorem rho_pos : (0 : ℝ) < (rho : ℚ) := by rw [ratCast_rho]; norm_num

/-! ### Pieces of `L \ σ` -/

/-- The ray: `Re Fd(z) ≤ -240.067 r - 9.721 + 2π Im z` for `Re z = 20`, `Im z ≤ -1/4`. -/
theorem ray_re_le {r : ℕ} (hr : 1 ≤ r) {z : ℂ} (h1 : z.re = 20) (h2 : z.im ≤ -1 / 4) :
    ((fam r).Fd z).re ≤ r * (-2400670 / 10000) + -97210 / 10000 + 2 * Real.pi * z.im := by
  have hR0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rw [Fd_eq_Phi hr (by linarith), Phi, add_re, famEs_re, re_natCast_mul' r]
  have e : z = ((20 : ℝ) : ℂ) - ((-z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [h1]
  obtain ⟨b1, b2⟩ := regRay_bound (-z.im) (by linarith)
  rw [← e] at b1 b2
  have : (r : ℝ) * (famG z).re ≤ r * (-2400670 / 10000) := mul_le_mul_of_nonneg_left b1 hR0
  linarith

theorem off_ray {r : ℕ} (hr1 : 1 ≤ r) {yR T : ℚ} (hyR : yR ≤ -1 / 4)
    (hray : (r : ℚ) * (-2400670 / 10000) + -97210 / 10000 + 6 * yR ≤ T) {z : ℂ}
    (h1 : z.re = 20) (h2 : z.im ≤ yR) : ((fam r).Fd z).re ≤ T := by
  have hyR' : (yR : ℝ) ≤ -1 / 4 := by exact_mod_cast hyR
  refine (ray_re_le hr1 h1 (by linarith)).trans ?_
  have k : ((r * (-2400670 / 10000) + -97210 / 10000 + 6 * yR : ℚ) : ℝ) ≤ T := by
    exact_mod_cast hray
  push_cast at k
  have hpi := Real.pi_gt_three
  have : 2 * Real.pi * z.im ≤ 6 * yR := by nlinarith
  linarith

theorem off_seg {r : ℕ} (hr1 : 1 ≤ r) {ax ay ex ey ρ T : ℚ} {ts : List ℚ}
    (hs : chkSegP (fun x y => FPt r x y pG) (F2Box r) okBox ax ay ex ey ρ T 1 ts = true)
    {z : ℂ} {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {δ : ℂ} (hδ : ‖δ‖ ≤ ρ)
    (hz : z = cq ax ay + τ * cq ex ey + δ) (hzim : z.im < 0) : ((fam r).Fd z).re ≤ T := by
  rw [Fd_eq_Phi hr1 hzim, hz]
  exact chkSegP_sound (phiEvOK r pG) (phiBoxOK r) hs τ hτ0 (by exact_mod_cast hτ1) δ hδ

theorem seg_PL_param {plx ply : ℚ} {z : ℂ} (hz : z ∈ segment ℝ (cq plx ply) (-2 : ℂ)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ z = cq plx ply + (θ : ℂ) * cq (-2 - plx) (-ply) := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hzeq⟩ := hz
  refine ⟨θ, hθ0, hθ1, ?_⟩
  rw [← hzeq]
  simp only [Complex.real_smul]
  unfold cq
  push_cast
  ring

theorem off_PL {r : ℕ} (hr1 : 1 ≤ r) {plx ply lam T : ℚ} {gL : List ℚ} (hply : ply < 0)
    (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hsL : chkSegP (fun x y => FPt r x y pG) (F2Box r) okBox plx ply (-2 - plx) (-ply) 0 T lam gL =
      true)
    (hlast : lastOK r pG (plx + lam * (-2 - plx)) (ply + lam * -ply) T = true)
    {z : ℂ} (hz : z ∈ segment ℝ (cq plx ply) (-2 : ℂ)) : ((fam r).Fd z).re ≤ T := by
  obtain ⟨θ, hθ0, hθ1, hz'⟩ := seg_PL_param hz
  obtain ⟨hl1, hl2⟩ := lastOK_sound hlast
  have hply' : (ply : ℝ) < 0 := by exact_mod_cast hply
  rcases eq_or_lt_of_le hθ1 with h1 | h1
  · -- the end point `-2`
    have : z = -2 := by rw [hz', h1]; unfold cq; push_cast; ring
    rw [this, re_Fd_neg_two hr1]
    exact hl2
  · have hzim : z.im < 0 := by
      have e : z.im = ply + θ * (-ply) := by rw [hz']; simp
      rw [e]; nlinarith
    rw [Fd_eq_Phi hr1 hzim]
    have hlam1' : ((lam : ℚ) : ℝ) < 1 := by exact_mod_cast hlam1
    rcases le_total θ lam with h2 | h2
    · have k := chkSegP_sound (phiEvOK r pG) (phiBoxOK r) hsL θ hθ0 h2 0 (by simp)
      rw [add_zero] at k
      rw [hz']
      exact k
    · have k := hl1 ((θ - lam) / (1 - lam)) (div_nonneg (by linarith) (by linarith))
        ((div_lt_one (by linarith)).2 (by linarith))
      have hne : (1 : ℝ) - lam ≠ 0 := by linarith
      have e : cq (plx + lam * (-2 - plx)) (ply + lam * -ply) +
          (((θ - lam) / (1 - lam) : ℝ) : ℂ) *
            cq (-2 - (plx + lam * (-2 - plx))) (-(ply + lam * -ply)) =
          cq plx ply + (θ : ℂ) * cq (-2 - plx) (-ply) := by
        apply Complex.ext <;>
          simp only [add_re, add_im, mul_re, mul_im, cq_re, cq_im, ofReal_re, ofReal_im] <;>
          push_cast <;> field_simp <;> ring
      rw [e] at k
      rw [hz']
      exact k

/-! ### Geometry of the pieces -/

theorem ray_good {yR K c₀ : ℝ} (hyR : yR < 0) (hK : 0 ≤ K) (hKy : 20 + K * yR ≤ 0)
    (hc : c₀ ≤ -yR) {z : ℂ} (h1 : z.re = 20) (h2 : z.im ≤ yR) :
    z.im < 0 ∧ -40 ≤ z.re ∧ z.re + K * z.im ≤ 0 ∧ c₀ ≤ ‖z‖ := by
  refine ⟨by linarith, by rw [h1]; norm_num, ?_, ?_⟩
  · rw [h1]
    have := mul_le_mul_of_nonneg_left h2 hK
    linarith
  · have := abs_im_le_norm z
    rw [abs_of_neg (by linarith)] at this
    linarith

theorem PL_good {plx ply : ℚ} {K c₀ na nb : ℝ} (hply : (ply : ℝ) < 0) (hK : 0 ≤ K)
    (hre : -40 ≤ (plx : ℝ)) (hKp : (plx : ℝ) + K * ply ≤ 0) (hnab : na ^ 2 + nb ^ 2 ≤ 1)
    (hc1 : c₀ ≤ na * plx + nb * ply) (hc2 : c₀ ≤ -2 * na) {z : ℂ}
    (hz : z ∈ segment ℝ (cq plx ply) (-2 : ℂ)) :
    z = -2 ∨ (z.im < 0 ∧ -40 ≤ z.re ∧ z.re + K * z.im ≤ 0 ∧ c₀ ≤ ‖z‖) := by
  obtain ⟨θ, hθ0, hθ1, hz'⟩ := seg_PL_param hz
  rcases eq_or_lt_of_le hθ1 with h1 | h1
  · left; rw [hz', h1]; unfold cq; push_cast; ring
  · right
    have hzre : z.re = plx + θ * (-2 - plx) := by rw [hz']; simp
    have hzim : z.im = ply + θ * (-ply) := by rw [hz']; simp
    refine ⟨by rw [hzim]; nlinarith, by rw [hzre]; nlinarith, ?_, ?_⟩
    · rw [hzre, hzim]
      have k1 : 0 ≤ K * (θ * -ply) := mul_nonneg hK (by nlinarith)
      nlinarith
    · refine le_trans ?_ (lin_le_norm hnab z)
      rw [hzre, hzim]
      nlinarith

/-! ### The decay along `σ` -/

theorem sigma_decay_Phi {r : ℕ} (hr1 : 1 ≤ r) {us v : ℂ} {M b V : ℝ} (hg0 : Phi1 r us = 0)
    (hslit : ∀ w ∈ closedBall us ‖v‖, w ∈ slitPlane)
    (hM : ∀ w ∈ closedBall us ‖v‖, ‖Phi3 r w‖ ≤ M) (hv : ‖v‖ ≤ V)
    (hb : b ≤ (-((fam r).f'' us) * v ^ 2 / 2).re - M * V ^ 3 / 6)
    (hlow : ∀ s ∈ Icc (-1 : ℝ) 1, (us + s * v).im < 0) (husim : us.im < 0) :
    ∀ s ∈ Icc (-1 : ℝ) 1, ((fam r).Fd (us + s * v) - (fam r).Fd us).re ≤ -b * s ^ 2 := by
  intro s hs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM us (mem_closedBall_self (norm_nonneg _)))
  have hT := norm_taylor_two_le (F := Phi r) (g := Phi1 r) (h := Phi2 r) (k := Phi3 r)
    (fun w hw => hasDerivAt_Phi r (hslit w hw)) (fun w hw => hasDerivAt_Phi1 r (hslit w hw))
    (fun w hw => hasDerivAt_Phi2 r (hslit w hw)) hM hg0 hs
  rw [Fd_eq_Phi hr1 (hlow s hs), Fd_eq_Phi hr1 husim]
  rw [← f''_eq_Phi2 hr1] at hT
  set E := Phi r (us + s * v) - Phi r us - (fam r).f'' us * v ^ 2 * s ^ 2 / 2 with hE
  have e : Phi r (us + s * v) - Phi r us = E + (fam r).f'' us * v ^ 2 / 2 * ((s ^ 2 : ℝ) : ℂ) := by
    rw [hE]; push_cast; ring
  have hre2 : ((fam r).f'' us * v ^ 2 / 2 * ((s ^ 2 : ℝ) : ℂ)).re =
      ((fam r).f'' us * v ^ 2 / 2).re * s ^ 2 := re_mul_ofReal _ _
  have hs3 : |s| ^ 3 ≤ s ^ 2 := by
    have h1 : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
    have h2 : |s| ^ 3 = |s| * s ^ 2 := by rw [pow_succ', sq_abs]
    rw [h2]
    exact mul_le_of_le_one_left (sq_nonneg _) h1
  have hv3 : M * ‖v‖ ^ 3 ≤ M * V ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 3) hM0
  have hEre : E.re ≤ M * V ^ 3 * s ^ 2 / 6 := by
    refine (re_le_norm E).trans (hT.trans ?_)
    have h0 : 0 ≤ M * ‖v‖ ^ 3 := by positivity
    have k1 := mul_le_mul_of_nonneg_left hs3 h0
    have k2 := mul_le_mul_of_nonneg_right hv3 (sq_nonneg s)
    linarith
  rw [e, add_re, hre2]
  have e2 : (-((fam r).f'' us) * v ^ 2 / 2).re = -((fam r).f'' us * v ^ 2 / 2).re := by
    rw [← neg_re]; ring_nf
  rw [e2] at hb
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  nlinarith

/-- `Re (-f''(u*) v²/2) ≥ Re (-f''(ũ) v²/2) - M ρ ‖v‖²/2`. -/
theorem re_a_lower {r : ℕ} {ut us v : ℂ} {M ρ : ℝ} (hΩ : closedBall ut ρ ⊆ Omega (fam r))
    (hf''' : ∀ w ∈ closedBall ut ρ, ‖(fam r).f''' w‖ ≤ M) (hus : us ∈ closedBall ut ρ) :
    (-((fam r).f'' ut) * v ^ 2 / 2).re - M * ρ * ‖v‖ ^ 2 / 2 ≤
      (-((fam r).f'' us) * v ^ 2 / 2).re := by
  have hρ : 0 ≤ ρ := dist_nonneg.trans hus
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hf''' ut (mem_closedBall_self hρ))
  have hdf'' : ‖(fam r).f'' us - (fam r).f'' ut‖ ≤ M * ρ := by
    refine (norm_f''_sub_le hΩ hf''' hus (mem_closedBall_self hρ)).trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hus hM0
  have e : -((fam r).f'' us) * v ^ 2 / 2 =
      -((fam r).f'' ut) * v ^ 2 / 2 - ((fam r).f'' us - (fam r).f'' ut) * v ^ 2 / 2 := by ring
  have k : |(((fam r).f'' us - (fam r).f'' ut) * v ^ 2 / 2).re| ≤ M * ρ * ‖v‖ ^ 2 / 2 := by
    refine (abs_re_le_norm _).trans ?_
    rw [norm_div, norm_mul, norm_pow]
    simp only [Complex.norm_ofNat]
    have := mul_le_mul_of_nonneg_right hdf'' (sq_nonneg ‖v‖)
    linarith
  rw [e, sub_re]
  linarith [(abs_le.1 k).2]

/-! ### Stage 1: the saddle point -/

/-- The facts about the saddle point `u*` used by the certificate. -/
structure SaddleFacts (r : ℕ) (d : SmData) (us : ℂ) : Prop where
  near : ‖us - cq d.ur d.ui‖ ≤ (rho : ℝ)
  saddle : (fam r).f' us + I * (((fam r).r : ℂ) - 2) * Real.pi = 0
  re_a_pos : 0 < (-((fam r).f'' us) * cq d.vr d.vi ^ 2 / 2).re
  b_pos : (0 : ℝ) < d.b
  sigma : ∀ s ∈ Icc (-1 : ℝ) 1,
    ((fam r).Fd (us + s * cq d.vr d.vi) - (fam r).Fd us).re ≤ -(d.b : ℝ) * s ^ 2
  lo : (d.T : ℝ) + d.b ≤ ((fam r).Fd us).re
  hi : ((fam r).Fd us).re < -(214.8 * r - 3)
  alpha : ∀ m : ℤ, ((fam r).Fd us).im ≠ m * Real.pi

set_option maxHeartbeats 400000 in
-- The proof decodes the saddle-point checks in one local context.
theorem saddle_stage {r : ℕ} {d : SmData} (hg : geomOK r d = true)
    (hs : saddleOK r d (FPt r d.ur d.ui pS) = true) (hf : fdOK r d (FPt r d.ur d.ui pS) = true) :
    ∃ us, SaddleFacts r d us := by
  simp only [geomOK, decide_eq_true_eq] at hg
  obtain ⟨hr1, hV, hvV, hbi, hti, -⟩ := hg
  simp only [saddleOK, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨hokR, hm, hm2, hposR, h74R, h76R, hM3, hMρ, hres, hb0, hbQ⟩ := hs
  simp only [fdOK, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨hokρ, hTb, hH, hα1, hα2, hα3, hα4⟩ := hf
  have hρ0 := rho_pos
  have hρq : (0 : ℚ) < rho := by norm_num [rho]
  have hV' : (0 : ℝ) ≤ d.V := by exact_mod_cast hV
  have hbi' : (d.ui : ℝ) - d.vi + rho < 0 := by exact_mod_cast hbi
  have hti' : (d.ui : ℝ) + d.vi + rho < 0 := by exact_mod_cast hti
  have hui : d.ui < 0 := by linarith
  have hm' : (0 : ℝ) < d.m := by exact_mod_cast hm
  have hMρ' : (d.M3 : ℝ) * rho ≤ d.m / 2 := by exact_mod_cast hMρ
  set ut : ℂ := cq d.ur d.ui with hut
  set vC : ℂ := cq d.vr d.vi with hvC
  have hΩρ : closedBall ut (rho : ℝ) ⊆ Cert.Omega (fam r) :=
    closedBall_subset_Omega (by rw [hut, cq_im]; linarith)
  have hρR : closedBall ut (rho : ℝ) ⊆ closedBall ut ((d.V + rho : ℚ) : ℝ) :=
    closedBall_subset_closedBall (by push_cast; linarith)
  have hM3' : ∀ w ∈ closedBall ut ((d.V + rho : ℚ) : ℝ), ‖Phi3 r w‖ ≤ d.M3 := fun w hw =>
    (norm_Phi3_le_disc r hw hposR h74R h76R).trans (by exact_mod_cast hM3)
  have hM3nn : (0 : ℝ) ≤ d.M3 :=
    (norm_nonneg _).trans (hM3' ut (mem_closedBall_self (by push_cast; linarith)))
  have hf''' : ∀ w ∈ closedBall ut (rho : ℝ), ‖(fam r).f''' w‖ ≤ d.M3 := fun w hw => by
    rw [f'''_eq_Phi3 hr1]; exact hM3' w (hρR hw)
  have hslit : ∀ w ∈ closedBall ut ((d.V + rho : ℚ) : ℝ), w ∈ slitPlane := by
    intro w hw
    obtain ⟨k1, k2, k3, k4⟩ := re_im_bounds_of_mem_closedBall hw
    refine mem_slitPlane_of_okBox hokR ?_ ?_ <;> push_cast at k1 k2 k3 k4 ⊢ <;>
      constructor <;> linarith
  -- (N1) the saddle point
  have hmf'' : (d.m : ℝ) ≤ ‖(fam r).f'' ut‖ := by
    refine le_norm_of_sq_le_normSq ?_
    rw [hut, ← toC_F2Q hr1 d.ur d.ui, QC.normSq_toC]
    exact_mod_cast hm2
  have hF := mem_FPt_Fd hr1 hui pS (x := d.ur)
  have hε : ‖(fam r).f' ut + I * (((fam r).r : ℂ) - 2) * Real.pi‖ ≤ d.m * rho / 2 := by
    refine norm_le_of_normSq_le (by positivity) ?_
    rw [normSq_apply, ← sq, ← sq]
    have k1 := sq_le_sqB hF.2.2.1
    have k2 := sq_le_sqB hF.2.2.2
    have k3 : (((FPt r d.ur d.ui pS).dre.sqB + (FPt r d.ur d.ui pS).dim.sqB : ℚ) : ℝ) ≤
        (((d.m * rho / 2) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hres
    push_cast at k3
    linarith
  obtain ⟨us, hus, hsad⟩ := exists_saddle (P := fam r) (ut := ut) (ρ := rho) (m := d.m)
    (ε := d.m * rho / 2) (M := d.M3) hΩρ hm' hmf'' hε hf''' hMρ' le_rfl
  obtain ⟨hu1, hu2, hu3, hu4⟩ := re_im_bounds_of_mem_closedBall hus
  have husim : us.im < 0 := by linarith
  have husd : ‖us - ut‖ ≤ rho := by rw [← dist_eq_norm]; exact hus
  -- ‖v‖ ≤ V
  have hnv : ‖vC‖ ^ 2 = ((d.vr ^ 2 + d.vi ^ 2 : ℚ) : ℝ) := by
    rw [← normSq_eq_norm_sq, normSq_apply]; simp [vC]; ring
  have hvnorm : ‖vC‖ ≤ d.V := by
    refine norm_le_of_normSq_le hV' ?_
    rw [normSq_eq_norm_sq, hnv]
    exact_mod_cast hvV
  -- (N2) `Re a` and the decay along `σ`
  have hA := re_a_lower (v := vC) hΩρ hf''' hus
  have e2 : (-((fam r).f'' ut) * vC ^ 2 / 2).re = ((aQ r d : ℚ) : ℝ) := by
    rw [hut, ← toC_F2Q hr1 d.ur d.ui, hvC, re_neg_f''_mul]; rfl
  rw [e2, hnv] at hA
  have hbQ' : (d.b : ℝ) ≤ ((aQ r d - d.M3 * rho * (d.vr ^ 2 + d.vi ^ 2) / 2 -
      d.M3 * d.V ^ 3 / 6 : ℚ) : ℝ) := by exact_mod_cast hbQ
  push_cast at hbQ' hA
  have hV3 : (0 : ℝ) ≤ d.M3 * d.V ^ 3 := by positivity
  have hb0' : (0 : ℝ) < d.b := by exact_mod_cast hb0
  have hball : closedBall us ‖vC‖ ⊆ closedBall ut ((d.V + rho : ℚ) : ℝ) :=
    closedBall_subset_closedBall' (by push_cast; rw [dist_eq_norm]; linarith)
  have hlow : ∀ s ∈ Icc (-1 : ℝ) 1, (us + s * vC).im < 0 := by
    intro s hs
    have e : (us + s * vC).im = us.im + s * d.vi := by simp [vC]
    rw [e]
    have k : s * d.vi ≤ |(d.vi : ℝ)| := by
      have := abs_le.2 ⟨hs.1, hs.2⟩
      calc s * d.vi ≤ |s * d.vi| := le_abs_self _
        _ = |s| * |(d.vi : ℝ)| := abs_mul _ _
        _ ≤ 1 * |(d.vi : ℝ)| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = |(d.vi : ℝ)| := one_mul _
    rcases abs_cases (d.vi : ℝ) with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
  have hg0 : Phi1 r us = 0 := by rw [← Fd'_eq_Phi1 hr1 husim]; exact hsad
  have hsigma := sigma_decay_Phi hr1 (b := d.b) (V := d.V) hg0 (fun w hw => hslit w (hball hw))
    (fun w hw => hM3' w (hball hw)) hvnorm (by linarith) hlow husim
  -- (N3), (N4): `Fd(u*)` versus `Fd(ũ)`
  have hM2 : ∀ w ∈ closedBall ut (rho : ℝ), ‖(fam r).f'' w‖ ≤
      (F2Box r (d.ur - rho) (d.ur + rho) (d.ui - rho) (d.ui + rho) : ℝ) := by
    intro w hw
    obtain ⟨k1, k2, k3, k4⟩ := re_im_bounds_of_mem_closedBall hw
    refine norm_f''_le_box hr1 ?_ ?_ (fun bc _ => lowN_pos_of_okBox hokρ (Nat.cast_nonneg _))
      (lowN_pos_of_okBox hokρ (by norm_num)) (lowN_pos_of_okBox hokρ (by norm_num)) <;>
      push_cast <;> constructor <;> linarith
  have hFd := norm_Fd_sub_le hΩρ hus hsad hM2
  have hδ : 2 * ((F2Box r (d.ur - rho) (d.ur + rho) (d.ui - rho) (d.ui + rho) : ℚ) : ℝ) *
      (rho : ℝ) ^ 2 = ((deltaQ r d : ℚ) : ℝ) := by simp [deltaQ]
  rw [hδ] at hFd
  have hre := (abs_le.1 ((abs_re_le_norm ((fam r).Fd us - (fam r).Fd ut)).trans hFd))
  have him := (abs_le.1 ((abs_im_le_norm ((fam r).Fd us - (fam r).Fd ut)).trans hFd))
  rw [sub_re] at hre
  rw [sub_im] at him
  have kRe := hF.1
  have kIm := hF.2.1
  have hTb' : ((d.T + d.b : ℚ) : ℝ) ≤ (((FPt r d.ur d.ui pS).re.lo - deltaQ r d : ℚ) : ℝ) := by
    exact_mod_cast hTb
  have hH' : (((FPt r d.ur d.ui pS).re.hi + deltaQ r d : ℚ) : ℝ) <
      ((-(2148 / 10 * r - 3) : ℚ) : ℝ) := by exact_mod_cast hH
  push_cast at hTb' hH'
  refine ⟨us, husd, hsad, by linarith, hb0', hsigma, by linarith [kRe.1, hre.1], ?_, ?_⟩
  · have : ((2148 : ℝ) / 10) = 214.8 := by norm_num
    linarith [kRe.2, hre.2]
  · -- `α ∉ πℤ`
    intro k hk
    have hα1' : ((d.m0 : ℚ) : ℝ) * Num.piLo <
        (((FPt r d.ur d.ui pS).im.lo - deltaQ r d : ℚ) : ℝ) := by exact_mod_cast hα1
    have hα2' : ((d.m0 : ℚ) : ℝ) * Num.piHi <
        (((FPt r d.ur d.ui pS).im.lo - deltaQ r d : ℚ) : ℝ) := by exact_mod_cast hα2
    have hα3' : (((FPt r d.ur d.ui pS).im.hi + deltaQ r d : ℚ) : ℝ) <
        (((d.m0 : ℚ) + 1 : ℚ) : ℝ) * Num.piLo := by exact_mod_cast hα3
    have hα4' : (((FPt r d.ur d.ui pS).im.hi + deltaQ r d : ℚ) : ℝ) <
        (((d.m0 : ℚ) + 1 : ℚ) : ℝ) * Num.piHi := by exact_mod_cast hα4
    push_cast at hα1' hα2' hα3' hα4'
    have hlo : (d.m0 : ℝ) * Real.pi < ((fam r).Fd us).im :=
      mul_pi_lt (by linarith [kIm.1, him.1]) (by linarith [kIm.1, him.1])
    have hhi : ((fam r).Fd us).im < ((d.m0 : ℝ) + 1) * Real.pi :=
      lt_mul_pi (by linarith [kIm.2, him.2]) (by linarith [kIm.2, him.2])
    rw [hk] at hlo hhi
    have hpi := Real.pi_pos
    have e1 : (d.m0 : ℝ) < k := lt_of_mul_lt_mul_right hlo hpi.le
    have e2 : (k : ℝ) < d.m0 + 1 := lt_of_mul_lt_mul_right hhi hpi.le
    have e1' : d.m0 < k := by exact_mod_cast e1
    have e2' : k < d.m0 + 1 := by exact_mod_cast e2
    omega

/-! ### Stage 2: the path -/

/-- The path through `u*`. -/
noncomputable def pathOf (d : SmData) (us : ℂ) : PathData2 :=
  ⟨us, cq d.vr d.vi, 20, d.yR, cq d.plx d.ply, -2⟩

section Path

variable {r : ℕ} {d : SmData} {us : ℂ}

theorem pathOf_bot_re : (pathOf d us).bot.re = us.re - d.vr := by
  simp [pathOf, PathData2.bot]

theorem pathOf_bot_im : (pathOf d us).bot.im = us.im - d.vi := by
  simp [pathOf, PathData2.bot]

theorem pathOf_top_re : (pathOf d us).top.re = us.re + d.vr := by
  simp [pathOf, PathData2.top]

theorem pathOf_top_im : (pathOf d us).top.im = us.im + d.vi := by
  simp [pathOf, PathData2.top]

theorem pathOf_PR : (pathOf d us).PR = cq 20 d.yR := by
  apply Complex.ext <;> simp [pathOf, PathData2.PR]

theorem pathOf_PL : (pathOf d us).PL = cq d.plx d.ply := rfl

theorem pathOf_x1 : (((pathOf d us).x1 : ℝ) : ℂ) = (-2 : ℂ) := by simp [pathOf]

/-- `‖(u* ± v) - approximation‖ ≤ rs`. -/
theorem approx_le {us : ℂ} {ur ui a b c e rs : ℚ} (hus : ‖us - cq ur ui‖ ≤ (rho : ℝ))
    (h : |ur + a - c| + |ui + b - e| + rho ≤ rs) :
    ‖us + cq a b - cq c e‖ ≤ rs := by
  have e' : us + cq a b - cq c e = (us - cq ur ui) + cq (ur + a - c) (ui + b - e) := by
    unfold cq; push_cast; ring
  rw [e']
  refine (norm_add_le _ _).trans ?_
  have k2 := Complex.norm_le_abs_re_add_abs_im (cq (ur + a - c) (ui + b - e))
  simp only [cq_re, cq_im] at k2
  have k3 : ((|ur + a - c| + |ui + b - e| + rho : ℚ) : ℝ) ≤ rs := by exact_mod_cast h
  push_cast at k2 k3
  linarith

set_option maxHeartbeats 400000 in
-- The proof decodes the geometric checks in one local context.
theorem path_stage (hg : geomOK r d = true) (hseg : segOK r d = true)
    (hus : ‖us - cq d.ur d.ui‖ ≤ (rho : ℝ)) :
    (∀ z ∈ (pathOf d us).offSet, ((fam r).Fd z).re ≤ d.T) ∧
    (∀ z ∈ (pathOf d us).pathSet, z = (-2 : ℂ) ∨
      (z.im < 0 ∧ -40 ≤ z.re ∧ z.re + d.K * z.im ≤ 0 ∧ (d.c0 : ℝ) ≤ ‖z‖)) ∧
    (pathOf d us).bot.im < 0 ∧ (pathOf d us).top.im < 0 := by
  simp only [geomOK, decide_eq_true_eq] at hg
  obtain ⟨hr1, -, -, hbi, hti, hply, hyR, hray, hbr, htr, hc0, -, hc0y, hc0b, hc0t, hc0p,
    hnab, hc0n1, hc0n2, hK, hKy, hKb, hKt, hKp, hre1, hre2, hre3, hlam0, hlam1⟩ := hg
  simp only [segOK, Bool.and_eq_true] at hseg
  obtain ⟨⟨⟨hsR, hsT⟩, hsL⟩, hlast⟩ := hseg
  have hρ0 := rho_pos
  have hbi' : (d.ui : ℝ) - d.vi + rho < 0 := by exact_mod_cast hbi
  have hti' : (d.ui : ℝ) + d.vi + rho < 0 := by exact_mod_cast hti
  have hply' : (d.ply : ℝ) < 0 := by exact_mod_cast hply
  have hyR' : (d.yR : ℝ) ≤ -1 / 4 := by exact_mod_cast hyR
  have hc0' : (0 : ℝ) < d.c0 := by exact_mod_cast hc0
  have hc0y' : (d.c0 : ℝ) ≤ -d.yR := by exact_mod_cast hc0y
  have hc0b' : (d.c0 : ℝ) ≤ -(d.ui - d.vi + rho) := by exact_mod_cast hc0b
  have hc0t' : (d.c0 : ℝ) ≤ -(d.ui + d.vi + rho) := by exact_mod_cast hc0t
  have hc0p' : (d.c0 : ℝ) ≤ -d.ply := by exact_mod_cast hc0p
  have hnab' : (d.na : ℝ) ^ 2 + d.nb ^ 2 ≤ 1 := by exact_mod_cast hnab
  have hc0n1' : (d.c0 : ℝ) ≤ d.na * d.plx + d.nb * d.ply := by exact_mod_cast hc0n1
  have hc0n2' : (d.c0 : ℝ) ≤ -2 * d.na := by exact_mod_cast hc0n2
  have hK' : (0 : ℝ) ≤ d.K := by exact_mod_cast hK
  have hKy' : 20 + (d.K : ℝ) * d.yR ≤ 0 := by exact_mod_cast hKy
  have hKb' : (d.ur : ℝ) - d.vr + rho + d.K * (d.ui - d.vi + rho) ≤ 0 := by exact_mod_cast hKb
  have hKt' : (d.ur : ℝ) + d.vr + rho + d.K * (d.ui + d.vi + rho) ≤ 0 := by exact_mod_cast hKt
  have hKp' : (d.plx : ℝ) + d.K * d.ply ≤ 0 := by exact_mod_cast hKp
  have hre1' : (-40 : ℝ) ≤ d.ur - d.vr - rho := by exact_mod_cast hre1
  have hre2' : (-40 : ℝ) ≤ d.ur + d.vr - rho := by exact_mod_cast hre2
  have hre3' : (-40 : ℝ) ≤ d.plx := by exact_mod_cast hre3
  have husd : us ∈ closedBall (cq d.ur d.ui) (rho : ℝ) := by
    rw [mem_closedBall, dist_eq_norm]; exact hus
  obtain ⟨hu1, hu2, hu3, hu4⟩ := re_im_bounds_of_mem_closedBall husd
  have hbotre : (pathOf d us).bot.re = us.re - d.vr := pathOf_bot_re
  have hbotim : (pathOf d us).bot.im = us.im - d.vi := pathOf_bot_im
  have htopre : (pathOf d us).top.re = us.re + d.vr := pathOf_top_re
  have htopim : (pathOf d us).top.im = us.im + d.vi := pathOf_top_im
  have hPR : (pathOf d us).PR = cq 20 d.yR := pathOf_PR
  have hPL : (pathOf d us).PL = cq d.plx d.ply := pathOf_PL
  have hx1 : (((pathOf d us).x1 : ℝ) : ℂ) = (-2 : ℂ) := pathOf_x1
  have hbot' : ‖(pathOf d us).bot - cq d.br d.bi‖ ≤ d.rs := by
    have e : (pathOf d us).bot = us + cq (-d.vr) (-d.vi) := by
      simp only [pathOf, PathData2.bot]; unfold cq; push_cast; ring
    rw [e]
    exact approx_le hus (by simpa [sub_eq_add_neg] using hbr)
  have htop' : ‖(pathOf d us).top - cq d.tr d.ti‖ ≤ d.rs := approx_le hus htr
  have hbotneg : (pathOf d us).bot.im < 0 := by rw [hbotim]; linarith
  have htopneg : (pathOf d us).top.im < 0 := by rw [htopim]; linarith
  refine ⟨?_, ?_, hbotneg, htopneg⟩
  · -- `Re Fd ≤ T` on `L \ σ`
    intro z hz
    rcases hz with ((hray' | hPRbot) | htopPL) | hPLx1
    · obtain ⟨h1, h2⟩ := hray'
      exact off_ray hr1 hyR hray (by rw [h1]; simp [pathOf]) h2
    · obtain ⟨τ, hτ0, hτ1, δ, hδ, hzeq⟩ := seg_right_pert hbot' hPRbot
      rw [hPR, cq_sub] at hzeq
      exact off_seg hr1 hsR hτ0 hτ1 hδ hzeq
        (im_neg_of_seg hPRbot (by rw [hPR, cq_im]; linarith) hbotneg)
    · obtain ⟨τ, hτ0, hτ1, δ, hδ, hzeq⟩ := seg_left_pert htop' htopPL
      rw [hPL, cq_sub] at hzeq
      exact off_seg hr1 hsT hτ0 hτ1 hδ hzeq
        (im_neg_of_seg htopPL htopneg (by rw [hPL, cq_im]; exact hply'))
    · rw [hx1, hPL] at hPLx1
      exact off_PL hr1 hply hlam0 hlam1 hsL hlast hPLx1
  · -- the geometry
    have hPR1 : (pathOf d us).PR.im ≤ -d.c0 := by rw [hPR, cq_im]; linarith
    have hPR2 : -40 ≤ (pathOf d us).PR.re := by rw [hPR, cq_re]; norm_num
    have hPR3 : (pathOf d us).PR.re + d.K * (pathOf d us).PR.im ≤ 0 := by
      rw [hPR, cq_re, cq_im]; push_cast; linarith
    have hb1 : (pathOf d us).bot.im ≤ -d.c0 := by rw [hbotim]; linarith
    have hb2 : -40 ≤ (pathOf d us).bot.re := by rw [hbotre]; linarith
    have hb3 : (pathOf d us).bot.re + d.K * (pathOf d us).bot.im ≤ 0 := by
      rw [hbotre, hbotim]
      have := mul_le_mul_of_nonneg_left (show us.im - d.vi ≤ d.ui - d.vi + rho by linarith) hK'
      linarith
    have ht1 : (pathOf d us).top.im ≤ -d.c0 := by rw [htopim]; linarith
    have ht2 : -40 ≤ (pathOf d us).top.re := by rw [htopre]; linarith
    have ht3 : (pathOf d us).top.re + d.K * (pathOf d us).top.im ≤ 0 := by
      rw [htopre, htopim]
      have := mul_le_mul_of_nonneg_left (show us.im + d.vi ≤ d.ui + d.vi + rho by linarith) hK'
      linarith
    have hL1 : (pathOf d us).PL.im ≤ -d.c0 := by rw [hPL, cq_im]; linarith
    have hL2 : -40 ≤ (pathOf d us).PL.re := by rw [hPL, cq_re]; linarith
    have hL3 : (pathOf d us).PL.re + d.K * (pathOf d us).PL.im ≤ 0 := by
      rw [hPL, cq_re, cq_im]; linarith
    intro z hz
    rcases hz with (((hray' | hPRbot) | htopPL) | hPLx1) | hσ
    · obtain ⟨h1, h2⟩ := hray'
      exact Or.inr (ray_good (by linarith) hK' hKy' hc0y' (by rw [h1]; simp [pathOf]) h2)
    · exact Or.inr (seg_good hPRbot hc0' hPR1 hb1 hPR2 hb2 hPR3 hb3)
    · exact Or.inr (seg_good htopPL hc0' ht1 hL1 ht2 hL2 ht3 hL3)
    · rw [hx1, hPL] at hPLx1
      exact PL_good hply' hK' hre3' hKp' hnab' hc0n1' hc0n2' hPLx1
    · exact Or.inr (seg_good hσ hc0' hb1 ht1 hb2 ht2 hb3 ht3)

end Path

/-! ### The certificate -/

/-- **Soundness of the checker.** -/
theorem famCert_of_ok {r : ℕ} {d : SmData} (h : famCertOK r d = true) : FamCert r := by
  simp only [famCertOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hg, hs⟩, hf⟩, hseg⟩ := h
  obtain ⟨us, hU⟩ := saddle_stage hg hs hf
  obtain ⟨hoff, hpath, hbot, htop⟩ := path_stage hg hseg hU.near
  have hg' := hg
  simp only [geomOK, decide_eq_true_eq] at hg'
  obtain ⟨hr1, -, -, -, -, -, hyR, -, -, -, hc0, hc02, -⟩ := hg'
  have hyR' : (d.yR : ℝ) ≤ -1 / 4 := by exact_mod_cast hyR
  have hc0' : (0 : ℝ) < d.c0 := by exact_mod_cast hc0
  have hc02' : (d.c0 : ℝ) ≤ 2 := by exact_mod_cast hc02
  have hetaOne : (fam r).etaOne = 45 := rfl
  have heta0 : (fam r).eta0 = 150 := rfl
  have hx1 : (((pathOf d us).x1 : ℝ) : ℂ) = (-2 : ℂ) := pathOf_x1
  refine ⟨pathOf d us, d.b, 2 * Real.pi, r * (-2400670 / 10000) + -97210 / 10000, d.c0,
    Real.pi / 2 - Real.arctan d.K, ?_, hU.hi, hU.alpha⟩
  exact
    { saddle := hU.saddle
      re_a_pos := hU.re_a_pos
      b_pos := hU.b_pos
      sigma_decay := hU.sigma
      off_sigma := fun z hz => by
        show _ ≤ ((fam r).Fd us).re - d.b
        linarith [hoff z hz, hU.lo]
      c_pos := by positivity
      ray_decay := fun y hy => by
        have hy' : y ≤ d.yR := hy
        have := ray_re_le hr1 (z := (((pathOf d us).xR : ℝ) : ℂ) + y * I) (by simp [pathOf])
          (by simp; linarith)
        simpa [pathOf] using this
      x1_neg := by simp [pathOf]
      x1_gt := by rw [hetaOne]; norm_num [pathOf]
      lower := fun z hz hne => by
        rcases hpath z hz with h | h
        · exact absurd (h.trans hx1.symm) hne
        · exact h.1
      yR_neg := by simp [pathOf]; linarith
      bot_im_neg := hbot
      top_im_neg := htop
      c₀_pos := hc0'
      ε₀_pos := by linarith [Real.arctan_lt_pi_div_two d.K]
      path_norm := fun z hz => by
        rcases hpath z hz with h | h
        · rw [h]; norm_num; linarith
        · exact h.2.2.2
      path_arg := fun z hz => by
        rcases hpath z hz with h | h
        · rw [h, neg_neg]
          have : Complex.arg (2 : ℂ) = 0 := by rw [Complex.arg_eq_zero_iff]; norm_num
          rw [this, abs_zero]
          linarith [Real.pi_pos, Real.arctan_lt_pi_div_two d.K, Real.neg_pi_div_two_lt_arctan d.K]
        · exact abs_arg_neg_le' h.1 (by linarith [h.2.2.1])
      path_re := fun z hz => by
        rw [hetaOne]
        rcases hpath z hz with h | h
        · rw [h]; norm_num; linarith
        · push_cast; linarith [h.2.1]
      path_eta0 := fun z hz => by
        rw [heta0]
        refine le_trans ?_ (re_le_norm _)
        have e : (((150 : ℕ) : ℂ) + 2 * z).re = 150 + 2 * z.re := by simp
        rw [e]
        rcases hpath z hz with h | h
        · rw [h]; norm_num; linarith
        · linarith [h.2.1] }

end OddZeta.Small
