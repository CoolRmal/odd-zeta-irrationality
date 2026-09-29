import OddZeta.Analytic.Saddle2Aux2

/-!
# The saddle-point asymptotics of `Fₙ` along a general path

The path `L` (lower half only) consists of
* the vertical ray `{xR + iy : y ≤ yR}` (upwards), ending at `PR = xR + i yR`,
* the segment `[PR, bot]`,
* the segment `σ = [bot, top]` through the saddle point `u* = D.u`, with `bot = u* - v`,
  `top = u* + v`,
* the segments `[top, PL]` and `[PL, x₁]`, ending at the real point `x₁ ∈ (-η₁, 0)`.

Instead of the monotonicity conditions of `PathCert`, the certificate `PathCert2` asks directly
for `Re Fd ≤ Re Fd(u*) - b` on `L \ σ` (`off_sigma`) and for a linear decay of `Re Fd` along the
ray (`ray_decay`). The conclusions are those of `F_eq_im_pathInt`, `tendsto_F_div_Kn` and
`B_ne_zero`.
-/

namespace OddZeta

open Complex MeasureTheory Filter Topology

/-- The data of the general path `L`. -/
structure PathData2 where
  /-- the saddle point `u*` -/
  u : ℂ
  /-- the half-length vector of `σ` -/
  v : ℂ
  /-- the abscissa of the lower ray -/
  xR : ℝ
  /-- the ray is `{xR + iy : y ≤ yR}`; its top point is `PR = xR + yR i` -/
  yR : ℝ
  /-- the intermediate point between `top` and `x₁` -/
  PL : ℂ
  /-- the path ends at the real point `x₁` -/
  x1 : ℝ

namespace PathData2

variable (D : PathData2)

/-- `bot = u* - v`. -/
def bot : ℂ := D.u - D.v

/-- `top = u* + v`. -/
def top : ℂ := D.u + D.v

/-- The top point `PR = xR + yR i` of the ray. -/
def PR : ℂ := D.xR + D.yR * I

/-- `∫` along `L`: the ray (upwards), `[PR, bot]`, `σ = [bot, top]`, `[top, PL]`, `[PL, x₁]`. -/
noncomputable def pathInt (g : ℂ → ℂ) : ℂ :=
  (∫ y in Set.Iic D.yR, g (D.xR + y * I)) * I + segInt g D.PR D.bot + segInt g D.bot D.top +
    segInt g D.top D.PL + segInt g D.PL D.x1

/-- The points of `L \ σ`. -/
def offSet : Set ℂ :=
  {z | z.re = D.xR ∧ z.im ≤ D.yR} ∪ segment ℝ D.PR D.bot ∪ segment ℝ D.top D.PL ∪
    segment ℝ D.PL (D.x1 : ℂ)

/-- The points of `L`. -/
def pathSet : Set ℂ := D.offSet ∪ segment ℝ D.bot D.top

@[simp] theorem PR_re : D.PR.re = D.xR := by simp [PR]

@[simp] theorem PR_im : D.PR.im = D.yR := by simp [PR]

theorem offSet_subset : D.offSet ⊆ D.pathSet := Set.subset_union_left

theorem mem_offSet_ray {y : ℝ} (hy : y ≤ D.yR) : (D.xR : ℂ) + y * I ∈ D.offSet :=
  Or.inl (Or.inl (Or.inl ⟨by simp, by simpa using hy⟩))

theorem segment_PR_bot_subset : segment ℝ D.PR D.bot ⊆ D.offSet :=
  fun _ hz => Or.inl (Or.inl (Or.inr hz))

theorem segment_top_PL_subset : segment ℝ D.top D.PL ⊆ D.offSet :=
  fun _ hz => Or.inl (Or.inr hz)

theorem segment_PL_x1_subset : segment ℝ D.PL (D.x1 : ℂ) ⊆ D.offSet :=
  fun _ hz => Or.inr hz

theorem PL_mem_pathSet : D.PL ∈ D.pathSet :=
  D.offSet_subset (D.segment_top_PL_subset (right_mem_segment ℝ _ _))

theorem mem_pathSet_sigma {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    D.u + s * D.v ∈ D.pathSet := by
  right
  have ht : (s + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  have := add_mul_sub_mem_segment (a := D.bot) (b := D.top) ht
  convert this using 1
  simp only [bot, top]
  push_cast
  ring

theorem u_mem_pathSet : D.u ∈ D.pathSet := by
  have := D.mem_pathSet_sigma (s := 0) (by constructor <;> norm_num)
  simpa using this

/-- **Deformation of the vertical line** `Re t = M` to the path `n·L` followed by the real
segment `[n x₁, M]` (whose contribution is real), for a general integrand `g` holomorphic off the
real axis and on `(a₁, 0)`, real on the real axis and exponentially decaying as `Im t → -∞`. -/
theorem re_integral_eq_im_pathInt {g : ℂ → ℂ} {a₁ C : ℝ}
    (hg : ∀ t : ℂ, (t.im ≠ 0 ∨ (a₁ < t.re ∧ t.re < 0)) → DifferentiableAt ℂ g t)
    (hdecay : ∀ t : ℂ, t.im ≤ -1 → ‖g t‖ ≤ C * Real.exp t.im)
    (hreal : ∀ x : ℝ, (g x).im = 0) {n : ℕ} (hn : 1 ≤ n) {M : ℝ} (hM₁ : a₁ < M) (hM₂ : M < 0)
    (hx₁ : a₁ < n * D.x1) (hx₁' : D.x1 < 0) (hyR : D.yR < 0) (hbot : D.bot.im < 0)
    (htop : D.top.im < 0) (hPL : D.PL.im < 0 ∨ D.PL = D.x1) :
    (∫ y in Set.Iic (0 : ℝ), g (M + y * I)).re = ((n : ℂ) * D.pathInt fun u => g (n * u)).im := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hreal_x1 : ((n : ℂ) * D.x1).im = 0 ∧ a₁ < ((n : ℂ) * D.x1).re ∧
      ((n : ℂ) * D.x1).re < 0 := by
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, ofReal_im, mul_zero,
      mul_re, ofReal_re, sub_zero]
    exact ⟨trivial, hx₁, by nlinarith⟩
  have hlow : ∀ z : ℂ, z.im < 0 → ((n : ℂ) * z).im < 0 := by
    intro z hz
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero]
    nlinarith
  have hvert : ∀ z ∈ [(n : ℂ) * D.bot, (n : ℂ) * D.top, (n : ℂ) * D.PL, (n : ℂ) * D.x1,
      (M : ℂ)], z.im < 0 ∨ (z.im = 0 ∧ a₁ < z.re ∧ z.re < 0) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (hlow _ hbot)
    · exact Or.inl (hlow _ htop)
    · rcases hPL with h | h
      · exact Or.inl (hlow _ h)
      · rw [h]; exact Or.inr hreal_x1
    · exact Or.inr hreal_x1
    · right; simp only [ofReal_im, ofReal_re]; exact ⟨trivial, hM₁, hM₂⟩
  have hb : ((n : ℂ) * D.PR).im < 0 := hlow _ (by simpa using hyR)
  have key := Deform.deform_ray hg hdecay ((n : ℂ) * D.PR) hb hM₁ hM₂ _ hvert rfl
  have hre : ((n : ℂ) * D.PR).re = n * D.xR := by
    simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero, PR_re]
  have him : ((n : ℂ) * D.PR).im = n * D.yR := by
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, PR_im]
  have e_ray : (∫ y in Set.Iic ((n : ℂ) * D.PR).im, g (((n : ℂ) * D.PR).re + y * I)) =
      (n : ℂ) * ∫ y in Set.Iic D.yR, g (n * (D.xR + y * I)) := by
    rw [hre, him]
    have h := Deform.integral_comp_mul_left_Iic
      (fun y : ℝ => g (((n * D.xR : ℝ) : ℂ) + y * I)) D.yR hn0
    have e1 : (fun x : ℝ => g (((n * D.xR : ℝ) : ℂ) + ((n * x : ℝ) : ℂ) * I)) =
        fun y : ℝ => g (n * (D.xR + y * I)) := by
      funext y; congr 1; push_cast; ring
    rw [e1] at h
    rw [h, Complex.real_smul, ← mul_assoc, ofReal_inv, ofReal_natCast,
      mul_inv_cancel₀ (by exact_mod_cast hn0.ne'), one_mul]
  have hseg : (segInt g ((n : ℂ) * D.x1) M).im = 0 := by
    rw [show (n : ℂ) * D.x1 = ((n * D.x1 : ℝ) : ℂ) by push_cast; rfl]
    exact Deform.im_segInt_ofReal hreal _ _
  rw [show (∫ y in Set.Iic (0 : ℝ), g (M + y * I)).re =
      (I * ∫ y in Set.Iic (0 : ℝ), g (M + y * I)).im by simp, ← key, e_ray]
  simp only [polyInt_cons_cons, polyInt_singleton, add_zero, segInt_mul_mul, pathInt]
  have fin : ∀ a b c d f e : ℂ, e.im = 0 →
      (I * ((n : ℂ) * a) + ((n : ℂ) * b + ((n : ℂ) * c + ((n : ℂ) * d + ((n : ℂ) * f + e))))).im =
        ((n : ℂ) * (a * I + b + c + d + f)).im := by
    intro a b c d f e he
    rw [show I * ((n : ℂ) * a) + ((n : ℂ) * b + ((n : ℂ) * c + ((n : ℂ) * d +
      ((n : ℂ) * f + e)))) = (n : ℂ) * (a * I + b + c + d + f) + e by ring, add_im, he, add_zero]
  exact fin _ _ _ _ _ _ hseg

end PathData2

namespace Params

variable (P : Params)

/-- The conditions on the general path, to be certified numerically. -/
structure PathCert2 (D : PathData2) (b c K c₀ ε₀ : ℝ) : Prop where
  /-- `u*` is a saddle point of `Fd` -/
  saddle : P.f' D.u + I * ((P.r : ℂ) - 2) * Real.pi = 0
  /-- `Re a > 0` for `a = -f''(u*) v²/2` -/
  re_a_pos : 0 < (-(P.f'' D.u) * D.v ^ 2 / 2).re
  b_pos : 0 < b
  /-- quadratic decay of `Re Fd` along `σ` -/
  sigma_decay : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
    (P.Fd (D.u + s * D.v) - P.Fd D.u).re ≤ -b * s ^ 2
  /-- `Re Fd ≤ Re Fd(u*) - b` on `L \ σ` -/
  off_sigma : ∀ z ∈ D.offSet, (P.Fd z).re ≤ (P.Fd D.u).re - b
  c_pos : 0 < c
  /-- linear decay of `Re Fd` along the ray -/
  ray_decay : ∀ y ≤ D.yR, (P.Fd (D.xR + y * I)).re ≤ K + c * y
  /-- geometry -/
  x1_neg : D.x1 < 0
  x1_gt : -(P.etaOne : ℝ) < D.x1
  /-- the whole path except its endpoint lies in the open lower half-plane -/
  lower : ∀ z ∈ D.pathSet, z ≠ (D.x1 : ℂ) → z.im < 0
  /-- the ray and `σ` stay away from the real axis -/
  yR_neg : D.yR < 0
  bot_im_neg : D.bot.im < 0
  top_im_neg : D.top.im < 0
  c₀_pos : 0 < c₀
  ε₀_pos : 0 < ε₀
  path_norm : ∀ z ∈ D.pathSet, c₀ ≤ ‖z‖
  path_arg : ∀ z ∈ D.pathSet, |(-z).arg| ≤ Real.pi - ε₀
  path_re : ∀ z ∈ D.pathSet, c₀ - P.etaOne ≤ z.re
  path_eta0 : ∀ z ∈ D.pathSet, c₀ ≤ ‖(P.eta0 : ℂ) + 2 * z‖

variable {P} {D : PathData2} {b c K c₀ ε₀ : ℝ}

theorem PathCert2.im_nonpos (hD : P.PathCert2 D b c K c₀ ε₀) {z : ℂ} (hz : z ∈ D.pathSet) :
    z.im ≤ 0 := by
  by_cases h : z = D.x1
  · rw [h, ofReal_im]
  · exact (hD.lower z hz h).le

theorem PathCert2.good (hP : P.Valid) (hD : P.PathCert2 D b c K c₀ ε₀) {z : ℂ}
    (hz : z ∈ D.pathSet) : P.Good z := by
  by_cases h : z = D.x1
  · rw [h]; exact good_of_real hP hD.x1_neg hD.x1_gt
  · exact good_of_im_ne_zero (hD.lower z hz h).ne

theorem PathCert2.eta0_ne (hD : P.PathCert2 D b c K c₀ ε₀) {z : ℂ} (hz : z ∈ D.pathSet) :
    (P.eta0 : ℂ) + 2 * z ≠ 0 := by
  intro h
  have := hD.path_eta0 z hz
  rw [h, norm_zero] at this
  linarith [hD.c₀_pos]

theorem PathCert2.PL_cases (hD : P.PathCert2 D b c K c₀ ε₀) : D.PL.im < 0 ∨ D.PL = D.x1 := by
  by_cases h : D.PL = D.x1
  · exact Or.inr h
  · exact Or.inl (hD.lower _ D.PL_mem_pathSet h)

/-- **Deformation of the contour**: `Fₙ = (1/π) Im (n ∫_L S(nu) Gₙ(nu) du)`. -/
theorem F_eq_im_pathInt2 (hP : P.Valid) (hD : P.PathCert2 D b c K c₀ ε₀) {n : ℕ} (hn : 1 ≤ n) :
    P.F n = (n * D.pathInt fun u => trigS P.r (n * u) * P.G n (n * u)).im / Real.pi := by
  obtain ⟨-, hF⟩ := F_eq_integral hP hn
  rw [hF]
  congr 1
  obtain ⟨C, hC⟩ := Deform.norm_trigS_mul_G_le hP hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh1 : (Params.hh P.etaOne n : ℝ) = P.etaOne * n + 1 := by simp [Params.hh]
  refine D.re_integral_eq_im_pathInt (a₁ := -(Params.hh P.etaOne n : ℝ))
    (g := fun t => trigS P.r t * P.G n t)
    (fun t ht => (Deform.differentiable_trigS P.r t).mul (Deform.G_differentiableAt hP n ht))
    hC (Deform.im_trigS_mul_G_ofReal P.r n) hn ?_ ?_ ?_ hD.x1_neg hD.yR_neg hD.bot_im_neg
    hD.top_im_neg hD.PL_cases
  · simp only [lineM]; linarith
  · simp only [lineM]; rw [hh1]; nlinarith [(Nat.cast_nonneg P.etaOne : (0 : ℝ) ≤ P.etaOne)]
  · rw [hh1]; nlinarith [hD.x1_gt]

/-- The constant `B` is nonzero. -/
theorem B_ne_zero2 (_hP : P.Valid) (hD : P.PathCert2 D b c K c₀ ε₀) :
    D.v * P.Ghat D.u * (Real.pi / (-(P.f'' D.u) * D.v ^ 2 / 2)) ^ (1 / 2 : ℂ) ≠ 0 := by
  have ha : -(P.f'' D.u) * D.v ^ 2 / 2 ≠ 0 := by
    intro h
    have := hD.re_a_pos
    rw [h, zero_re] at this
    exact lt_irrefl _ this
  have hv : D.v ≠ 0 := by
    intro h
    apply ha
    rw [h]
    ring
  refine mul_ne_zero (mul_ne_zero hv (Ghat_ne_zero (hD.eta0_ne D.u_mem_pathSet))) ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) ha h.1

/-- **Proposition 4.7** for the general path: the asymptotics of `Fₙ`. -/
theorem tendsto_F_div_Kn2 (hP : P.Valid) (hD : P.PathCert2 D b c K c₀ ε₀) :
    Tendsto (fun n : ℕ => P.F n / P.Kn (P.Fd D.u).re n -
      (cexp (I * (n * (P.Fd D.u).im)) *
        (D.v * P.Ghat D.u * (Real.pi / (-(P.f'' D.u) * D.v ^ 2 / 2)) ^ (1 / 2 : ℂ))).im)
      atTop (𝓝 0) := by
  obtain ⟨C, N₀, hE₀⟩ := G_asymp hP hD.c₀_pos hD.ε₀_pos hD.path_norm hD.path_arg hD.path_re
    hD.path_eta0
  have hN : 1 ≤ max N₀ 1 := le_max_right _ _
  have hE : ∀ n ≥ max N₀ 1, ∀ u ∈ D.pathSet,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n :=
    fun n hn u hu => hE₀ n (le_of_max_le_left hn) u hu
  set H := (P.Fd D.u).re with hH
  set B : ℂ := D.v * P.Ghat D.u * (Real.pi / (-(P.f'' D.u) * D.v ^ 2 / 2)) ^ (1 / 2 : ℂ)
    with hB
  have hU : ∀ z ∈ D.pathSet, (P.eta0 : ℂ) + 2 * z ≠ 0 := fun z hz => hD.eta0_ne hz
  -- the pieces of `L`
  have hseg : ∀ A A' : ℂ, segment ℝ A A' ⊆ D.offSet → Tendsto (fun n : ℕ => (P.Qn H n : ℂ) *
      segInt (fun u => trigS P.r (n * u) * P.G n (n * u)) A A') atTop (𝓝 0) := by
    intro A A' hAA'
    refine tendsto_segInt_gen hP hU hN hE hD.b_pos fun z hz => ?_
    have hz' := D.offSet_subset (hAA' hz)
    exact ⟨hz', hD.im_nonpos hz', hD.good hP hz', hD.off_sigma z (hAA' hz)⟩
  have hray : Tendsto (fun n : ℕ => (P.Qn H n : ℂ) * ((∫ y in Set.Iic D.yR,
      trigS P.r (n * (D.xR + y * I)) * P.G n (n * (D.xR + y * I))) * I)) atTop (𝓝 0) :=
    tendsto_ray_gen hP hU hN hE hD.yR_neg hD.b_pos hD.c_pos
      (fun y hy => D.offSet_subset (D.mem_offSet_ray hy))
      (fun y hy => hD.off_sigma _ (D.mem_offSet_ray hy)) hD.ray_decay
  have hσ : Tendsto (fun n : ℕ => (P.Qn H n : ℂ) *
      segInt (fun u => trigS P.r (n * u) * P.G n (n * u)) D.bot D.top -
        cexp (I * (n * (P.Fd D.u).im)) * B) atTop (𝓝 0) :=
    tendsto_sigma_gen hP hU hN hE (fun s hs => D.mem_pathSet_sigma hs) hD.bot_im_neg
      hD.top_im_neg hD.saddle hD.re_a_pos hD.b_pos hD.sigma_decay
  have hsum := (((hray.add (hseg _ _ D.segment_PR_bot_subset)).add hσ).add
    (hseg _ _ D.segment_top_PL_subset)).add (hseg _ _ D.segment_PL_x1_subset)
  simp only [add_zero] at hsum
  have hmain : Tendsto (fun n : ℕ => (P.Qn H n : ℂ) *
      D.pathInt (fun u => trigS P.r (n * u) * P.G n (n * u)) -
        cexp (I * (n * (P.Fd D.u).im)) * B) atTop (𝓝 0) := by
    refine hsum.congr fun n => ?_
    simp only [PathData2.pathInt]
    ring
  refine squeeze_zero_norm' ?_ (by simpa using hmain.norm)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [F_eq_im_pathInt2 hP hD hn]
  set J := D.pathInt (fun u => trigS P.r (n * u) * P.G n (n * u))
  have hA := An_pos hP hn
  have e : ((n : ℂ) * J).im / Real.pi / P.Kn H n =
      ((P.Qn H n : ℂ) * J).im := by
    rw [im_ofReal_mul, im_natCast_mul]
    unfold Kn Qn
    have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
    field_simp
    linear_combination (-J.im) * hs
  rw [e, ← sub_im, Real.norm_eq_abs]
  exact abs_im_le_norm _

end Params

end OddZeta
