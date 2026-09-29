import OddZeta.Family.LargeSaddle

/-!
# Bounds at the saddle point for `r ≥ 301` (formulas (8.5)–(8.7) of the note, simplified)

For a saddle point `u* = a + w` as given by `exists_saddle_large`:
* `Re(-f''(u*)) ≥ 0.1832 r - 2.38`;
* the quadratic decay of `Re Fd` along `σ = [u* + 3/2, u* - 3/2]` with `b = r/20` (condition (S2));
* `|Re Fd(u*) - (r ĝ(a) + e(a))| ≤ 1.2` (formula (8.6));
* `|Im Fd(u*) + 2π a| ≤ 0.46` (formula (8.7)), hence `Im Fd(u*) ∉ πℤ` (condition (S5)).
-/

namespace OddZeta

open Complex Metric Set

namespace Large

/-- The saddle-point data of `exists_saddle_large`. -/
def IsSaddleLarge (r : ℕ) (u : ℂ) : Prop :=
  (fam r).f' u + I * (((fam r).r : ℂ) - 2) * Real.pi = 0 ∧
    |(u - famA).re| ≤ 1.8 / r ∧ -(36.1 / r) ≤ (u - famA).im ∧ (u - famA).im ≤ -(32.4 / r) ∧
    ‖u - famA‖ ≤ 36.1 / r

theorem exists_isSaddleLarge (r : ℕ) (hr : 301 ≤ r) : ∃ u, IsSaddleLarge r u :=
  exists_saddle_large r hr

theorem re_Fd {r : ℕ} (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    ((fam r).Fd u).re = r * (famG u).re + (famE u).re + 2 * Real.pi * u.im := by
  rw [Fam.Fd_eq hr hu]
  simp [mul_re, mul_im]

theorem im_Fd {r : ℕ} (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    ((fam r).Fd u).im = r * (famG u).im + (famE u).im - 2 * Real.pi * u.re := by
  rw [Fam.Fd_eq hr hu]
  simp [mul_re, mul_im]

variable {r : ℕ} {u : ℂ}

section

variable (hr : 301 ≤ r) (hu : IsSaddleLarge r u)
include hr hu

theorem IsSaddleLarge.R_ge : (301 : ℝ) ≤ r := by exact_mod_cast hr

theorem IsSaddleLarge.norm_R : (r : ℝ) * ‖u - famA‖ ≤ 36.1 := by
  have hR := IsSaddleLarge.R_ge hr hu
  have h := hu.2.2.2.2
  rwa [le_div_iff₀ (by linarith), mul_comm] at h

theorem IsSaddleLarge.norm_le : ‖u - famA‖ ≤ 36.1 / 301 := by
  have hR := IsSaddleLarge.R_ge hr hu
  exact hu.2.2.2.2.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR)

theorem IsSaddleLarge.near : ‖u - famA‖ ≤ 1 / 8 :=
  (IsSaddleLarge.norm_le hr hu).trans (by norm_num)

theorem IsSaddleLarge.im_neg : u.im < 0 := by
  have hR := IsSaddleLarge.R_ge hr hu
  have h := hu.2.2.2.1
  rw [sub_im, ofReal_im, sub_zero] at h
  have : 0 < 32.4 / (r : ℝ) := by positivity
  linarith

theorem IsSaddleLarge.im_ge : -(36.1 / 301) ≤ u.im := by
  have hR := IsSaddleLarge.R_ge hr hu
  have h := hu.2.2.1
  rw [sub_im, ofReal_im, sub_zero] at h
  have : 36.1 / (r : ℝ) ≤ 36.1 / 301 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR
  linarith

theorem IsSaddleLarge.re_sub : |u.re - famA| ≤ 1.8 / 301 := by
  have hR := IsSaddleLarge.R_ge hr hu
  have h := hu.2.1
  rw [sub_re, ofReal_re] at h
  exact h.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hR)

theorem IsSaddleLarge.re_bounds : 4.1869 ≤ u.re ∧ u.re ≤ 4.1990 := by
  have h := abs_le.1 (IsSaddleLarge.re_sub hr hu)
  have h1 := famA_lo
  have h2 := famA_hi
  constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]

/-- `f''(u*) = -r D̄ + Δ` with `‖Δ‖ ≤ 2.38`. -/
theorem IsSaddleLarge.f''_near :
    ‖(fam r).f'' u - ((-((r : ℝ) * famD) : ℝ) : ℂ)‖ ≤ 2.38 := by
  have hR := IsSaddleLarge.R_ge hr hu
  have hn := IsSaddleLarge.near hr hu
  rw [Fam.f''_eq (by omega)]
  have hδ := norm_famG2_sub_le hn
  rw [famG2_famA] at hδ
  have he2 := norm_famE2_near hn
  have e : (r : ℂ) * famG2 u + famE2 u - ((-((r : ℝ) * famD) : ℝ) : ℂ) =
      (r : ℂ) * (famG2 u - -(famD : ℂ)) + famE2 u := by push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_natCast]
  have h1 : (r : ℝ) * ‖famG2 u - -(famD : ℂ)‖ ≤ (r : ℝ) * (0.0651 * ‖u - famA‖) :=
    mul_le_mul_of_nonneg_left hδ (by positivity)
  have h2 := IsSaddleLarge.norm_R hr hu
  nlinarith

theorem IsSaddleLarge.re_neg_f'' : 0.1832 * r - 2.38 ≤ (-(fam r).f'' u).re := by
  have hR := IsSaddleLarge.R_ge hr hu
  have h := IsSaddleLarge.f''_near hr hu
  have h1 := (abs_le.1 ((abs_re_le_norm _).trans h)).2
  rw [sub_re, ofReal_re] at h1
  rw [neg_re]
  have hD := famD_bounds.1
  nlinarith

/-- **Condition (S2)**: quadratic decay of `Re Fd` along `σ`. -/
theorem IsSaddleLarge.sigma_decay {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    ((fam r).Fd (u + s * (-(3 / 2) : ℂ)) - (fam r).Fd u).re ≤ -((r : ℝ) / 20) * s ^ 2 := by
  have hr1 : 1 ≤ r := by omega
  have hR := IsSaddleLarge.R_ge hr hu
  have hre := IsSaddleLarge.re_bounds hr hu
  have him := IsSaddleLarge.im_neg hr hu
  set v : ℂ := -(3 / 2 : ℂ) with hv
  have hvn : ‖v‖ = 3 / 2 := by rw [hv, norm_neg]; norm_num
  -- the ball `closedBall u (3/2)` lies in `{Re ≥ 2.68}`
  have hball : ∀ z ∈ closedBall u ‖v‖, 2.68 ≤ z.re := by
    intro z hz
    rw [mem_closedBall_iff_norm, hvn] at hz
    have := (abs_le.1 ((abs_re_le_norm _).trans hz)).1
    rw [sub_re] at this
    linarith
  have hpos : ∀ z ∈ closedBall u ‖v‖, 0 < z.re := fun z hz => by linarith [hball z hz]
  set M : ℝ := (r : ℝ) * 0.142 + 0.00034 with hM
  have hk : ∀ z ∈ closedBall u ‖v‖, ‖(r : ℂ) * famG3 z + famE3 z‖ ≤ M := by
    intro z hz
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left ((norm_famG3_le (by norm_num) (hball z hz)).trans S2_268)
        (by positivity)
    · exact (norm_famE3_le (by norm_num) (hball z hz)).trans (by norm_num)
  have hT := Cert.norm_taylor_two_le
    (F := fun z => (r : ℂ) * famG z + famE z - 2 * Real.pi * I * z)
    (g := fun z => (r : ℂ) * famG1 z + famE1 z - 2 * Real.pi * I)
    (h := fun z => (r : ℂ) * famG2 z + famE2 z)
    (k := fun z => (r : ℂ) * famG3 z + famE3 z) (u := u) (v := v) (M := M)
    (fun z hz => ((((hasDerivAt_famG (hpos z hz)).const_mul (r : ℂ)).fun_add
        (hasDerivAt_famE (hpos z hz))).fun_sub
          ((hasDerivAt_id' z).const_mul (2 * Real.pi * I))).congr_deriv (by ring))
    (fun z hz => (((hasDerivAt_famG1 (hpos z hz)).const_mul (r : ℂ)).fun_add
        (hasDerivAt_famE1 (hpos z hz))).sub_const (2 * Real.pi * I))
    (fun z hz => ((hasDerivAt_famG2 (hpos z hz)).const_mul (r : ℂ)).fun_add
        (hasDerivAt_famE2 (hpos z hz)))
    hk (by rw [← saddle_expr hr1 him]; exact hu.1) hs
  have hsv : (u + s * v).im < 0 := by simp [hv, him]
  rw [← Fam.f''_eq hr1] at hT
  rw [← Fam.Fd_eq hr1 hsv, ← Fam.Fd_eq hr1 him] at hT
  set E := (fam r).Fd (u + s * v) - (fam r).Fd u - (fam r).f'' u * v ^ 2 * s ^ 2 / 2 with hE
  have e : (fam r).Fd (u + s * v) - (fam r).Fd u =
      E + ((-(fam r).f'' u) * ((-(9 / 8) * s ^ 2 : ℝ) : ℂ)) := by
    rw [hE, hv]; push_cast; ring
  rw [e, add_re, re_mul_ofReal]
  have hEre : E.re ≤ M * (3 / 2) ^ 3 * |s| ^ 3 / 6 := (re_le_norm E).trans (by rwa [hvn] at hT)
  have hs3 : |s| ^ 3 ≤ s ^ 2 := by
    have h1 : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
    have h2 : |s| ^ 3 = |s| * s ^ 2 := by rw [pow_succ', sq_abs]
    rw [h2]
    exact mul_le_of_le_one_left (sq_nonneg _) h1
  have hf2 := IsSaddleLarge.re_neg_f'' hr hu
  have hM0 : 0 ≤ M := by positivity
  have h3 : M * (3 / 2) ^ 3 * |s| ^ 3 / 6 ≤ M * (3 / 2) ^ 3 * s ^ 2 / 6 := by gcongr
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  nlinarith

/-- Formula (8.6): `|H_d - (r ĝ(a) + e(a))| ≤ 1.2`. -/
theorem IsSaddleLarge.re_Fd_near :
    |((fam r).Fd u).re - (r * gR famA + eR famA)| ≤ 1.2 := by
  have hr1 : 1 ≤ r := by omega
  have hR := IsSaddleLarge.R_ge hr hu
  have him := IsSaddleLarge.im_neg hr hu
  have him2 := IsSaddleLarge.im_ge hr hu
  have hn := IsSaddleLarge.near hr hu
  have hnR := IsSaddleLarge.norm_R hr hu
  have hn301 := IsSaddleLarge.norm_le hr hu
  rw [re_Fd hr1 him]
  -- `g`
  have hg := norm_famG_sub_le (v := u - famA) hn
  rw [add_sub_cancel] at hg
  have hg' : |(famG u).re - gR famA| ≤ ‖famG u - famG famA‖ := by
    rw [famG_ofReal famA_pos] at hg ⊢
    have := abs_re_le_norm (famG u - (gR famA : ℂ))
    rwa [sub_re, ofReal_re] at this
  -- `e`
  have he := norm_famE_sub_le hn
  have he' : |(famE u).re - eR famA| ≤ ‖famE u - famE famA‖ := by
    rw [famE_ofReal famA_pos]
    have := abs_re_le_norm (famE u - (eR famA : ℂ))
    rwa [sub_re, ofReal_re] at this
  have hD := famD_bounds.2
  have hD0 := famD_pos
  set T := ‖u - famA‖ with hT
  have hT0 : 0 ≤ T := norm_nonneg _
  -- `r ‖g(u) - g(a)‖ ≤ 0.41`
  have hrg : (r : ℝ) * ‖famG u - famG famA‖ ≤ 0.41 := by
    have h1 : (r : ℝ) * ‖famG u - famG famA‖ ≤
        (r : ℝ) * (famD * T ^ 2 / 2 + 0.0651 * T ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    have h2 : (r : ℝ) * T ^ 2 ≤ 36.1 * (36.1 / 301) := by
      rw [sq, ← mul_assoc]; exact mul_le_mul hnR hn301 hT0 (by norm_num)
    have h3 : (r : ℝ) * T ^ 3 ≤ 36.1 * (36.1 / 301) ^ 2 := by
      rw [pow_succ', ← mul_assoc, mul_comm (r : ℝ) T, mul_assoc]
      calc T * ((r : ℝ) * T ^ 2) ≤ (36.1 / 301) * (36.1 * (36.1 / 301)) :=
            mul_le_mul hn301 h2 (by positivity) (by norm_num)
        _ = 36.1 * (36.1 / 301) ^ 2 := by ring
    have h4 : (r : ℝ) * (famD * T ^ 2 / 2 + 0.0651 * T ^ 3 / 6) =
        famD / 2 * ((r : ℝ) * T ^ 2) + 0.0651 / 6 * ((r : ℝ) * T ^ 3) := by ring
    have h5 : famD / 2 * ((r : ℝ) * T ^ 2) ≤ 0.1833 / 2 * (36.1 * (36.1 / 301)) := by
      gcongr
    nlinarith
  have hre : |(famE u).re - eR famA| ≤ 0.0036 := by
    refine he'.trans (he.trans ?_)
    nlinarith
  have hpi := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  have him3 : |2 * Real.pi * u.im| ≤ 0.7536 := by
    rw [abs_le]; constructor <;> nlinarith
  have hg2 : |(r : ℝ) * (famG u).re - r * gR famA| ≤ 0.41 := by
    rw [← mul_sub, abs_mul, Nat.abs_cast]
    exact (mul_le_mul_of_nonneg_left hg' (by positivity)).trans hrg
  rw [abs_le] at hg2 hre him3 ⊢
  constructor <;> linarith [hg2.1, hg2.2, hre.1, hre.2, him3.1, him3.2]

/-- Formula (8.7): `|α + 2π a| ≤ 0.46` for `α = Im Fd(u*)`. -/
theorem IsSaddleLarge.im_Fd_near : |((fam r).Fd u).im + 2 * Real.pi * famA| ≤ 0.46 := by
  have hr1 : 1 ≤ r := by omega
  have hR := IsSaddleLarge.R_ge hr hu
  have him := IsSaddleLarge.im_neg hr hu
  have hn := IsSaddleLarge.near hr hu
  have hnR := IsSaddleLarge.norm_R hr hu
  have hn301 := IsSaddleLarge.norm_le hr hu
  have hres := IsSaddleLarge.re_sub hr hu
  rw [im_Fd hr1 him]
  have hg := norm_famG_sub_le (v := u - famA) hn
  rw [add_sub_cancel] at hg
  have hg' : |(famG u).im| ≤ ‖famG u - famG famA‖ := by
    rw [famG_ofReal famA_pos]
    have := abs_im_le_norm (famG u - (gR famA : ℂ))
    rwa [sub_im, ofReal_im, sub_zero] at this
  have he := norm_famE_sub_le hn
  have he' : |(famE u).im| ≤ ‖famE u - famE famA‖ := by
    rw [famE_ofReal famA_pos]
    have := abs_im_le_norm (famE u - (eR famA : ℂ))
    rwa [sub_im, ofReal_im, sub_zero] at this
  have hD := famD_bounds.2
  have hD0 := famD_pos
  set T := ‖u - famA‖ with hT
  have hT0 : 0 ≤ T := norm_nonneg _
  have hrg : (r : ℝ) * ‖famG u - famG famA‖ ≤ 0.41 := by
    have h1 : (r : ℝ) * ‖famG u - famG famA‖ ≤
        (r : ℝ) * (famD * T ^ 2 / 2 + 0.0651 * T ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    have h2 : (r : ℝ) * T ^ 2 ≤ 36.1 * (36.1 / 301) := by
      rw [sq, ← mul_assoc]; exact mul_le_mul hnR hn301 hT0 (by norm_num)
    have h3 : (r : ℝ) * T ^ 3 ≤ 36.1 * (36.1 / 301) ^ 2 := by
      rw [pow_succ', ← mul_assoc, mul_comm (r : ℝ) T, mul_assoc]
      calc T * ((r : ℝ) * T ^ 2) ≤ (36.1 / 301) * (36.1 * (36.1 / 301)) :=
            mul_le_mul hn301 h2 (by positivity) (by norm_num)
        _ = 36.1 * (36.1 / 301) ^ 2 := by ring
    have h4 : (r : ℝ) * (famD * T ^ 2 / 2 + 0.0651 * T ^ 3 / 6) =
        famD / 2 * ((r : ℝ) * T ^ 2) + 0.0651 / 6 * ((r : ℝ) * T ^ 3) := by ring
    have h5 : famD / 2 * ((r : ℝ) * T ^ 2) ≤ 0.1833 / 2 * (36.1 * (36.1 / 301)) := by
      gcongr
    nlinarith
  have hie : |(famE u).im| ≤ 0.0036 := by
    refine he'.trans (he.trans ?_)
    nlinarith
  have hpi := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  have hre3 : |2 * Real.pi * (u.re - famA)| ≤ 0.0376 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    have : 2 * Real.pi * |u.re - famA| ≤ 2 * 3.141593 * (1.8 / 301) :=
      mul_le_mul (by linarith) hres (abs_nonneg _) (by norm_num)
    linarith
  have hg2 : |(r : ℝ) * (famG u).im| ≤ 0.41 := by
    rw [abs_mul, Nat.abs_cast]
    exact (mul_le_mul_of_nonneg_left hg' (by positivity)).trans hrg
  rw [abs_le] at hg2 hie hre3 ⊢
  constructor <;> nlinarith [hg2.1, hg2.2, hie.1, hie.2, hre3.1, hre3.2]

/-- **Condition (S5)**: `α = Im Fd(u*) ∉ πℤ`. -/
theorem IsSaddleLarge.im_Fd_ne (m : ℤ) : ((fam r).Fd u).im ≠ m * Real.pi := by
  intro h
  have hα := IsSaddleLarge.im_Fd_near hr hu
  rw [h, abs_le] at hα
  have h1 := famA_lo
  have h2 := famA_hi
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  -- `m π ∈ [-2π a - 0.46, -2π a + 0.46]`, so `-9 < m < -8`
  have hm1 : (-9 : ℝ) < m := by
    by_contra hc
    have hc := not_lt.1 hc
    nlinarith
  have hm2 : (m : ℝ) < -8 := by
    by_contra hc
    have hc := not_lt.1 hc
    nlinarith
  have hm1' : (-9 : ℤ) < m := by exact_mod_cast hm1
  have hm2' : m < -8 := by exact_mod_cast hm2
  omega

end

end Large

end OddZeta
