import OddZeta.Family.CertDef
import OddZeta.Family.Regions
import OddZeta.Family.LargePath

/-!
# Certificates for the family: `r ≥ 301`: the asymptotic bounds of Section 8.7, uniformly in `t = 1/r`.

The saddle point `u*` (within `36.1/r` of the zero `a` of `ĝ'`, `LargeSaddle`), the half-length
vector `v = -3/2` (so `σ = [u* + 3/2, u* - 3/2]` is horizontal), and the path
`pathD u* = ⟨u*, -3/2, 20, -1/4, P_L, -2⟩` of Section 8.4, with `b = r/20`, `c = 2π`,
`K = -240.067 r - 9.721`, `c₀ = 1/10`, `ε₀ = π/2 - arctan (20/y₀)`, `y₀ = min (1/10) |Im u*|`.
The bounds on the pieces of the path are the region bounds of `Regions.lean` (Lemma 8.7).
-/

namespace OddZeta

open Complex Set

namespace Large

/-- The path of Section 8.4 through `u`. -/
noncomputable def pathD (u : ℂ) : PathData2 := ⟨u, -(3 / 2 : ℂ), 20, -1 / 4, regPL, -2⟩

variable {u : ℂ}

@[simp] theorem pathD_u : (pathD u).u = u := rfl
@[simp] theorem pathD_v : (pathD u).v = -(3 / 2 : ℂ) := rfl
@[simp] theorem pathD_xR : (pathD u).xR = 20 := rfl
@[simp] theorem pathD_yR : (pathD u).yR = -1 / 4 := rfl
@[simp] theorem pathD_PL : (pathD u).PL = regPL := rfl
@[simp] theorem pathD_x1 : (pathD u).x1 = -2 := rfl

theorem pathD_x1' : (((pathD u).x1 : ℝ) : ℂ) = (-2 : ℂ) := by
  rw [pathD_x1]; push_cast; rfl

theorem pathD_bot_re : (pathD u).bot.re = u.re + 3 / 2 := by
  simp only [PathData2.bot, pathD_u, pathD_v, sub_re, neg_re]; norm_num

theorem pathD_bot_im : (pathD u).bot.im = u.im := by
  simp only [PathData2.bot, pathD_u, pathD_v, sub_im, neg_im]; norm_num

theorem pathD_top_re : (pathD u).top.re = u.re - 3 / 2 := by
  simp only [PathData2.top, pathD_u, pathD_v, add_re, neg_re]; norm_num; ring

theorem pathD_top_im : (pathD u).top.im = u.im := by
  simp only [PathData2.top, pathD_u, pathD_v, add_im, neg_im]; norm_num

theorem pathD_PR_re : (pathD u).PR.re = 20 := by rw [PathData2.PR_re, pathD_xR]

theorem pathD_PR_im : (pathD u).PR.im = -1 / 4 := by rw [PathData2.PR_im, pathD_yR]

theorem regPL_re : regPL.re = 2092953 / 1000000 := by simp [regPL]

theorem regPL_im : regPL.im = -(1 / 4) := by simp [regPL]

theorem pathD_PR_mem : (pathD u).PR ∈ regBR := by
  show _ ∧ _ ∧ _ ∧ _
  rw [pathD_PR_re, pathD_PR_im]
  norm_num

theorem pathD_PL_mem : (pathD u).PL ∈ regBL := by
  show _ ∧ _ ∧ _ ∧ _
  rw [pathD_PL, regPL_re, regPL_im]
  norm_num

/-- `y₀ = min (1/10) |Im u|`. -/
noncomputable def y0 (u : ℂ) : ℝ := min (1 / 10) (-u.im)

theorem y0_le : y0 u ≤ 1 / 10 := min_le_left _ _

theorem y0_le_im : y0 u ≤ -u.im := min_le_right _ _

/-- The ray: `Re Fd(20 + iy) ≤ -240.067 r - 9.721 + 2π y` for `y ≤ -1/4`. -/
theorem ray_bound {r : ℕ} (hr1 : 1 ≤ r) {y : ℝ} (hy : y ≤ -1 / 4) :
    ((fam r).Fd (((20 : ℝ) : ℂ) + y * I)).re ≤
      r * (-2400670 / 10000) + -97210 / 10000 + 2 * Real.pi * y := by
  have hR0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hzim : (((20 : ℝ) : ℂ) + y * I).im = y := by simp
  rw [re_Fd hr1 (by rw [hzim]; linarith), hzim]
  have e : ((20 : ℝ) : ℂ) + y * I = ((20 : ℝ) : ℂ) - ((-y : ℝ) : ℂ) * I := by push_cast; ring
  obtain ⟨b1, b2⟩ := regRay_bound (-y) (by linarith)
  rw [← e] at b1 b2
  have : (r : ℝ) * (famG (((20 : ℝ) : ℂ) + y * I)).re ≤ r * (-2400670 / 10000) :=
    mul_le_mul_of_nonneg_left b1 hR0
  linarith

section

variable {r : ℕ} (hr : 301 ≤ r) (hu : IsSaddleLarge r u)
include hr hu

theorem pathD_bot_mem : (pathD u).bot ∈ regBR := by
  have hre := IsSaddleLarge.re_bounds hr hu
  have him := IsSaddleLarge.im_neg hr hu
  have him2 := IsSaddleLarge.im_ge hr hu
  show _ ∧ _ ∧ _ ∧ _
  rw [pathD_bot_re, pathD_bot_im]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num at hre him2 ⊢ <;> linarith

theorem pathD_top_mem : (pathD u).top ∈ regBL := by
  have hre := IsSaddleLarge.re_bounds hr hu
  have him := IsSaddleLarge.im_neg hr hu
  have him2 := IsSaddleLarge.im_ge hr hu
  show _ ∧ _ ∧ _ ∧ _
  rw [pathD_top_re, pathD_top_im]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num at hre him2 ⊢ <;> linarith

theorem y0_pos : 0 < y0 u := lt_min (by norm_num) (by linarith [IsSaddleLarge.im_neg hr hu])

/-- Every point of the path is `x₁ = -2` or lies in the open lower half-plane, with
`-2 ≤ Re z ≤ 20`, `Re z ≤ 0 ∨ Im z ≤ -y₀`, and `|Re z| ≥ 1/10 ∨ Im z ≤ -1/10`. -/
theorem pathD_good : ∀ z ∈ (pathD u).pathSet, z = (((pathD u).x1 : ℝ) : ℂ) ∨
    (z.im < 0 ∧ -2 ≤ z.re ∧ z.re ≤ 20 ∧ (z.re ≤ 0 ∨ z.im ≤ -y0 u) ∧
      (1 / 10 ≤ |z.re| ∨ z.im ≤ -(1 / 10))) := by
  have hre := IsSaddleLarge.re_bounds hr hu
  have him := IsSaddleLarge.im_neg hr hu
  have hy₀0 := y0_pos hr hu
  have hy₀1 : y0 u ≤ 1 / 10 := y0_le
  have hy₀2 : y0 u ≤ -u.im := y0_le_im
  intro z hz
  rcases hz with (((hray | hPRbot) | htopPL) | hPLx1) | hσ
  · obtain ⟨h1, h2⟩ := hray
    rw [pathD_xR] at h1
    rw [pathD_yR] at h2
    right
    refine ⟨by linarith, by linarith, by linarith, Or.inr (by linarith), Or.inl ?_⟩
    rw [h1]; norm_num
  · have hbox := seg_regBR hPRbot pathD_PR_mem (pathD_bot_mem hr hu)
    have him' := seg_im_le (c := -y0 u) hPRbot (by rw [pathD_PR_im]; linarith)
      (by rw [pathD_bot_im]; linarith)
    obtain ⟨h1, h2, -, -⟩ := hbox
    right
    refine ⟨by linarith, by linarith, h2, Or.inr him', Or.inl ?_⟩
    rw [abs_of_pos (by linarith)]; linarith
  · have hbox := seg_regBL htopPL (pathD_top_mem hr hu) pathD_PL_mem
    have him' := seg_im_le (c := -y0 u) htopPL (by rw [pathD_top_im]; linarith)
      (by rw [pathD_PL, regPL_im]; linarith)
    obtain ⟨h1, h2, -, -⟩ := hbox
    right
    refine ⟨by linarith, by linarith, by linarith, Or.inr him', Or.inl ?_⟩
    rw [abs_of_pos (by linarith)]; linarith
  · rw [pathD_PL, pathD_x1'] at hPLx1
    rcases seg_PL hPLx1 with h | ⟨h1, h2, h3, h4, h5⟩
    · left; rw [h, pathD_x1']
    · right
      refine ⟨h1, h2, h3, ?_, h5⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr (by linarith)
  · obtain ⟨θ, h0, h1, hzr, hzi⟩ := seg_re_im hσ
    rw [pathD_bot_re, pathD_top_re] at hzr
    rw [pathD_bot_im, pathD_top_im] at hzi
    have hzi' : z.im = u.im := by rw [hzi]; ring
    have hz1 : 1 ≤ z.re := by rw [hzr]; nlinarith
    right
    refine ⟨by linarith, by linarith, ?_, Or.inr (by linarith), Or.inl ?_⟩
    · rw [hzr]; nlinarith
    · rw [abs_of_pos (by linarith)]; linarith

/-- The margin (S4) of the note: `r S_g + S_e ≤ H_d - b` whenever `S_g ≤ -232.1627`,
`S_e ≤ -9.1937`. -/
theorem key_bound {A B : ℝ} (hA : A ≤ -2321627 / 10000) (hB : B ≤ -91937 / 10000) :
    r * A + B ≤ ((fam r).Fd u).re - r / 20 := by
  have hR : (301 : ℝ) ≤ r := IsSaddleLarge.R_ge hr hu
  have hHd := (abs_le.1 (IsSaddleLarge.re_Fd_near hr hu)).1
  have hg := gR_famA.1
  have he := eR_famA.1
  have h1 : (r : ℝ) * A ≤ r * (-2321627 / 10000) := mul_le_mul_of_nonneg_left hA (by linarith)
  have h2 : (r : ℝ) * (-232.05) ≤ r * gR famA := mul_le_mul_of_nonneg_left hg (by linarith)
  linarith

/-- **Condition (S4)**: `Re Fd ≤ H_d - b` on `L \ σ`. -/
theorem pathD_off : ∀ z ∈ (pathD u).offSet, ((fam r).Fd z).re ≤ ((fam r).Fd (pathD u).u).re - r / 20 := by
  have hr1 : 1 ≤ r := by omega
  have him := IsSaddleLarge.im_neg hr hu
  have hy₀0 := y0_pos hr hu
  have hy₀2 : y0 u ≤ -u.im := y0_le_im
  have hpi := Real.pi_pos
  rw [pathD_u]
  intro z hz
  rcases hz with ((hray | hPRbot) | htopPL) | hPLx1
  · obtain ⟨h1, h2⟩ := hray
    rw [pathD_xR] at h1
    rw [pathD_yR] at h2
    have hz : z = ((20 : ℝ) : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [h1]
    rw [hz]
    refine (ray_bound hr1 h2).trans ?_
    have h3 : 2 * Real.pi * z.im ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have := key_bound hr hu (A := -2400670 / 10000) (B := -97210 / 10000 + 2 * Real.pi * z.im)
      (by norm_num) (by linarith)
    linarith
  · have hbox := seg_regBR hPRbot pathD_PR_mem (pathD_bot_mem hr hu)
    have him' := seg_im_le (c := -y0 u) hPRbot (by rw [pathD_PR_im]; linarith [y0_le (u := u)])
      (by rw [pathD_bot_im]; linarith)
    obtain ⟨b1, b2⟩ := regBR_bound z hbox
    rw [re_Fd hr1 (by linarith)]
    have := key_bound hr hu (A := (famG z).re) (B := (famE z).re + 2 * Real.pi * z.im) b1
      (by linarith)
    linarith
  · have hbox := seg_regBL htopPL (pathD_top_mem hr hu) pathD_PL_mem
    have him' := seg_im_le (c := -y0 u) htopPL (by rw [pathD_top_im]; linarith)
      (by rw [pathD_PL, regPL_im]; linarith [y0_le (u := u)])
    obtain ⟨b1, b2⟩ := regBL_bound z hbox
    rw [re_Fd hr1 (by linarith)]
    have := key_bound hr hu (A := (famG z).re) (B := (famE z).re + 2 * Real.pi * z.im)
      (by linarith) (by linarith)
    linarith
  · rw [pathD_PL, pathD_x1'] at hPLx1
    obtain ⟨b1, b2⟩ := regPL_bound z hPLx1
    rcases seg_PL hPLx1 with h | ⟨h1, -, -, -, -⟩
    · subst h
      have e : ((fam r).Fd (-2 : ℂ)).re = r * (famG (-2 : ℂ)).re + (famE (-2 : ℂ)).re := by
        have := Fam.re_Fd_real (r := r) hr1 (x := -2) (by norm_num) (by norm_num)
        push_cast at this
        exact this
      rw [e]
      simp only [neg_im, im_ofNat, neg_zero, mul_zero, add_zero] at b2
      have := key_bound hr hu (A := (famG (-2 : ℂ)).re) (B := (famE (-2 : ℂ)).re) (by linarith) b2
      linarith
    · rw [re_Fd hr1 h1]
      have := key_bound hr hu (A := (famG z).re) (B := (famE z).re + 2 * Real.pi * z.im)
        (by linarith) b2
      linarith

theorem pathD_arg : ∀ z ∈ (pathD u).pathSet,
    |(-z).arg| ≤ Real.pi - (Real.pi / 2 - Real.arctan (20 / y0 u)) := by
  have hy₀0 := y0_pos hr hu
  have hK0 : 0 ≤ Real.arctan (20 / y0 u) := by
    rw [← Real.arctan_zero]; exact Real.arctan_strictMono.monotone (by positivity)
  intro z hz
  rcases pathD_good hr hu z hz with h | ⟨h1, -, h3, h4, -⟩
  · rw [h, pathD_x1', neg_neg]
    have : Complex.arg (2 : ℂ) = 0 := by
      rw [Complex.arg_eq_zero_iff]; norm_num
    rw [this, abs_zero]
    linarith [Real.pi_pos]
  · refine abs_arg_neg_le h1 ?_
    have hz0 : 0 < -z.im := by linarith
    rcases h4 with h4 | h4
    · have : 0 ≤ 20 / y0 u * -z.im := by positivity
      linarith
    · have e : 20 / y0 u * y0 u = 20 := by field_simp
      have : 20 / y0 u * y0 u ≤ 20 / y0 u * -z.im :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith

/-- **The certificate** `PathCert2` for `r ≥ 301`. -/
theorem pathD_cert : (fam r).PathCert2 (pathD u) (r / 20) (2 * Real.pi)
    (r * (-2400670 / 10000) + -97210 / 10000) (1 / 10)
    (Real.pi / 2 - Real.arctan (20 / y0 u)) := by
  have hr1 : 1 ≤ r := by omega
  have hR : (301 : ℝ) ≤ r := IsSaddleLarge.R_ge hr hu
  have him := IsSaddleLarge.im_neg hr hu
  exact
    { saddle := by rw [pathD_u]; exact hu.1
      re_a_pos := by
        rw [pathD_u, pathD_v]
        have e : -(fam r).f'' u * (-(3 / 2 : ℂ)) ^ 2 / 2 =
            (-(fam r).f'' u) * ((9 / 8 : ℝ) : ℂ) := by
          push_cast; ring
        rw [e, re_mul_ofReal]
        have := IsSaddleLarge.re_neg_f'' hr hu
        nlinarith
      b_pos := by positivity
      sigma_decay := by
        intro s hs
        rw [pathD_u, pathD_v]
        exact IsSaddleLarge.sigma_decay hr hu hs
      off_sigma := pathD_off hr hu
      c_pos := by positivity
      ray_decay := by
        intro y hy
        rw [pathD_yR] at hy
        rw [pathD_xR]
        exact ray_bound hr1 hy
      x1_neg := by rw [pathD_x1]; norm_num
      x1_gt := by rw [pathD_x1]; norm_num [fam]
      lower := by
        intro z hz hne
        rcases pathD_good hr hu z hz with h | h
        · exact absurd h hne
        · exact h.1
      yR_neg := by rw [pathD_yR]; norm_num
      bot_im_neg := by rw [pathD_bot_im]; exact him
      top_im_neg := by rw [pathD_top_im]; exact him
      c₀_pos := by norm_num
      ε₀_pos := by linarith [Real.arctan_lt_pi_div_two (20 / y0 u)]
      path_norm := by
        intro z hz
        rcases pathD_good hr hu z hz with h | ⟨-, -, -, -, h5⟩
        · rw [h, pathD_x1']; norm_num
        · rcases h5 with h5 | h5
          · exact h5.trans (abs_re_le_norm z)
          · have : 1 / 10 ≤ |z.im| := by rw [abs_of_neg (by linarith)]; linarith
            exact this.trans (abs_im_le_norm z)
      path_arg := pathD_arg hr hu
      path_re := by
        intro z hz
        have : (fam r).etaOne = 45 := rfl
        rw [this]
        rcases pathD_good hr hu z hz with h | ⟨-, h2, -, -, -⟩
        · rw [h, pathD_x1]; norm_num
        · push_cast; linarith
      path_eta0 := by
        intro z hz
        have : (fam r).eta0 = 150 := rfl
        rw [this]
        have h2 : -2 ≤ z.re := by
          rcases pathD_good hr hu z hz with h | ⟨-, h2, -, -, -⟩
          · rw [h, pathD_x1]; norm_num
          · exact h2
        refine le_trans ?_ (re_le_norm _)
        have e : (((150 : ℕ) : ℂ) + 2 * z).re = 150 + 2 * z.re := by simp
        rw [e]
        linarith }

/-- **Condition (S6)**: `H_d < -(214.8 r - 3)`. -/
theorem re_Fd_lt : ((fam r).Fd (pathD u).u).re < -(214.8 * r - 3) := by
  have hR : (301 : ℝ) ≤ r := IsSaddleLarge.R_ge hr hu
  have hHd := (abs_le.1 (IsSaddleLarge.re_Fd_near hr hu)).2
  have hg := gR_famA.2
  have he := eR_famA.2
  have h2 : (r : ℝ) * gR famA ≤ r * (-232) := mul_le_mul_of_nonneg_left hg (by linarith)
  rw [pathD_u]
  linarith

end

end Large

open Large in
theorem famCert_large (r : ℕ) (hr : Odd r) (h301 : 301 ≤ r) : FamCert r := by
  obtain ⟨u, hu⟩ := exists_isSaddleLarge r h301
  refine ⟨pathD u, _, _, _, _, _, pathD_cert h301 hu, re_Fd_lt h301 hu, fun m => ?_⟩
  rw [pathD_u]
  exact IsSaddleLarge.im_Fd_ne h301 hu m

end OddZeta
