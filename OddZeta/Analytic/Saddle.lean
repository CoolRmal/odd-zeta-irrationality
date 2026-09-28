import OddZeta.Analytic.IntegralRep
import OddZeta.Analysis.Contour
import OddZeta.Analysis.Laplace
import OddZeta.Analytic.DeformAux

/-!
# The saddle-point asymptotics of `Fₙ` (Proposition 4.7 of the note, modified)

The path `L` (lower half-plane only) consists of
* the vertical ray `{bot.re + iy : y ≤ bot.im}`,
* the segment `σ = [bot, top]` through the saddle point `u* = D.u`, with `bot = u* - v`,
  `top = u* + v`,
* the horizontal segment from `top` to `x₁ + i·top.im`,
* the vertical segment from `x₁ + i·top.im` up to the real point `x₁`.

With `Fd(u) = f(u) + i(r-2)πu` (the phase of the dominant Fourier mode `k = r - 2`), the
conditions below say: `u*` is a saddle point, `Re Fd` has a strict quadratic maximum at `u*` along
`σ`, and `Re Fd` decreases monotonically along the three other pieces (going away from `σ`).
Then `Fₙ = Kₙ (Im(e^{inα} B) + o(1))` with `Kₙ = √n Aₙ e^{nH}/(π (r-1)!)`, `H = Re Fd(u*)`,
`α = Im Fd(u*)`, `B = v Ĝ(u*) (π/a)^{1/2}`, `a = -f''(u*) v²/2`.
-/

namespace OddZeta

open Complex MeasureTheory Filter Topology

/-- The data of the path `L`. -/
structure PathData where
  /-- the saddle point `u*` -/
  u : ℂ
  /-- the half-length vector of `σ` -/
  v : ℂ
  /-- the abscissa where `L` meets the real axis -/
  x1 : ℝ

namespace PathData

variable (D : PathData)

/-- `bot = u* - v`. -/
def bot : ℂ := D.u - D.v

/-- `top = u* + v`. -/
def top : ℂ := D.u + D.v

/-- The corner `x₁ + i·top.im`. -/
def corner : ℂ := D.x1 + D.top.im * I

/-- The integral of `g` along `L`, from `-i∞` to `x₁`. -/
noncomputable def pathInt (g : ℂ → ℂ) : ℂ :=
  (∫ y in Set.Iic D.bot.im, g (D.bot.re + y * I)) * I +
    segInt g D.bot D.top + segInt g D.top D.corner + segInt g D.corner D.x1

/-- The points of `L`. -/
def pathSet : Set ℂ :=
  {z | z.re = D.bot.re ∧ z.im ≤ D.bot.im} ∪ segment ℝ D.bot D.top ∪
    segment ℝ D.top D.corner ∪ segment ℝ D.corner (D.x1 : ℂ)

/-- **Deformation of the vertical line** `Re t = M` to the path `n·L` followed by the real
segment `[n x₁, M]` (whose contribution is real), for a general integrand `g` holomorphic off the
real axis and on `(a₁, 0)`, real on the real axis and exponentially decaying as `Im t → -∞`. -/
theorem re_integral_eq_im_pathInt {g : ℂ → ℂ} {a₁ C : ℝ}
    (hg : ∀ t : ℂ, (t.im ≠ 0 ∨ (a₁ < t.re ∧ t.re < 0)) → DifferentiableAt ℂ g t)
    (hdecay : ∀ t : ℂ, t.im ≤ -1 → ‖g t‖ ≤ C * Real.exp t.im)
    (hreal : ∀ x : ℝ, (g x).im = 0) {n : ℕ} (hn : 1 ≤ n) {M : ℝ} (hM₁ : a₁ < M) (hM₂ : M < 0)
    (hx₁ : a₁ < n * D.x1) (hx₁' : D.x1 < 0) (htop : D.top.im < 0) (hbot : D.bot.im < 0) :
    (∫ y in Set.Iic (0 : ℝ), g (M + y * I)).re = ((n : ℂ) * D.pathInt fun u => g (n * u)).im := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hvert : ∀ z ∈ [(n : ℂ) * D.top, (n : ℂ) * D.corner, (n : ℂ) * D.x1, (M : ℂ)],
      z.im < 0 ∨ (z.im = 0 ∧ a₁ < z.re ∧ z.re < 0) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · left; simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero]; nlinarith
    · left; simp only [corner, mul_im, natCast_re, natCast_im, zero_mul, add_zero, add_im,
        ofReal_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add]; nlinarith
    · right
      simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, ofReal_im, mul_zero,
        mul_re, ofReal_re, sub_zero]
      exact ⟨trivial, hx₁, by nlinarith⟩
    · right; simp only [ofReal_im, ofReal_re]; exact ⟨trivial, hM₁, hM₂⟩
  have hb : ((n : ℂ) * D.bot).im < 0 := by
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero]; nlinarith
  have key := Deform.deform_ray hg hdecay ((n : ℂ) * D.bot) hb hM₁ hM₂ _ hvert rfl
  have e_ray : (∫ y in Set.Iic ((n : ℂ) * D.bot).im, g (((n : ℂ) * D.bot).re + y * I)) =
      (n : ℂ) * ∫ y in Set.Iic D.bot.im, g (n * (D.bot.re + y * I)) := by
    have h := Deform.integral_comp_mul_left_Iic
      (fun y : ℝ => g (((n * D.bot.re : ℝ) : ℂ) + y * I)) D.bot.im hn0
    have e1 : (fun x : ℝ => g (((n * D.bot.re : ℝ) : ℂ) + ((n * x : ℝ) : ℂ) * I)) =
        fun y : ℝ => g (n * (D.bot.re + y * I)) := by
      funext y; congr 1; push_cast; ring
    rw [e1] at h
    rw [h, Complex.real_smul, ← mul_assoc, ofReal_inv, ofReal_natCast,
      mul_inv_cancel₀ (by exact_mod_cast hn0.ne'), one_mul]
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, mul_re, sub_zero]
  have hseg : (segInt g ((n : ℂ) * D.x1) M).im = 0 := by
    rw [show (n : ℂ) * D.x1 = ((n * D.x1 : ℝ) : ℂ) by push_cast; rfl]
    exact Deform.im_segInt_ofReal hreal _ _
  rw [show (∫ y in Set.Iic (0 : ℝ), g (M + y * I)).re =
      (I * ∫ y in Set.Iic (0 : ℝ), g (M + y * I)).im by simp, ← key, e_ray]
  simp only [polyInt_cons_cons, polyInt_singleton, add_zero, segInt_mul_mul, pathInt]
  have fin : ∀ a b c d e : ℂ, e.im = 0 →
      (I * ((n : ℂ) * a) + ((n : ℂ) * b + ((n : ℂ) * c + ((n : ℂ) * d + e)))).im =
        ((n : ℂ) * (a * I + b + c + d)).im := by
    intro a b c d e he
    rw [show I * ((n : ℂ) * a) + ((n : ℂ) * b + ((n : ℂ) * c + ((n : ℂ) * d + e))) =
      (n : ℂ) * (a * I + b + c + d) + e by ring, add_im, he, add_zero]
  exact fin _ _ _ _ _ hseg

end PathData

namespace Params

variable (P : Params)

/-- The phase of the dominant mode: `Fd(u) = f(u) + i(r-2)πu`. -/
noncomputable def Fd (u : ℂ) : ℂ := P.f u + I * ((P.r : ℂ) - 2) * Real.pi * u

/-- The conditions on the path, to be certified numerically. -/
structure PathCert (D : PathData) (b c c₀ ε₀ : ℝ) : Prop where
  /-- `u*` is a saddle point of `Fd` -/
  saddle : P.f' D.u + I * ((P.r : ℂ) - 2) * Real.pi = 0
  /-- `Re a > 0` for `a = -f''(u*) v²/2` -/
  re_a_pos : 0 < (-(P.f'' D.u) * D.v ^ 2 / 2).re
  b_pos : 0 < b
  /-- quadratic decay of `Re Fd` along `σ` -/
  sigma_decay : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
    (P.Fd (D.u + s * D.v) - P.Fd D.u).re ≤ -b * s ^ 2
  c_pos : 0 < c
  /-- `Re Fd` increases with rate `≥ c` going up the ray -/
  ray : ∀ y ≤ D.bot.im, (P.f' (D.bot.re + y * I)).im + (P.r - 2) * Real.pi ≤ -c
  /-- `Re Fd` increases going right along the horizontal segment -/
  x1_lt : D.x1 < D.top.re
  horiz : ∀ x ∈ Set.Icc D.x1 D.top.re, 0 < (P.f' (x + D.top.im * I)).re
  /-- `Re Fd` decreases going up the vertical segment -/
  vert : ∀ y ∈ Set.Icc D.top.im 0, 0 < (P.f' (D.x1 + y * I)).im + (P.r - 2) * Real.pi
  /-- geometry -/
  x1_neg : D.x1 < 0
  x1_gt : -(P.etaOne : ℝ) < D.x1
  top_im_neg : D.top.im < 0
  bot_im_neg : D.bot.im < 0
  c₀_pos : 0 < c₀
  ε₀_pos : 0 < ε₀
  path_norm : ∀ z ∈ D.pathSet, c₀ ≤ ‖z‖
  path_arg : ∀ z ∈ D.pathSet, |(-z).arg| ≤ Real.pi - ε₀
  path_re : ∀ z ∈ D.pathSet, c₀ - P.etaOne ≤ z.re
  path_eta0 : ∀ z ∈ D.pathSet, c₀ ≤ ‖(P.eta0 : ℂ) + 2 * z‖

/-- The normalising factor `Kₙ = √n Aₙ e^{nH} / (π (r-1)!)`. -/
noncomputable def Kn (H : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt n * P.An n * Real.exp (n * H) / (Real.pi * (P.r - 1).factorial)

variable {P}

/-- **Deformation of the contour**: `Fₙ = (1/π) Im (n ∫_L S(nu) Gₙ(nu) du)`. -/
theorem F_eq_im_pathInt (hP : P.Valid) {D : PathData} {b c c₀ ε₀ : ℝ}
    (hD : P.PathCert D b c c₀ ε₀) {n : ℕ} (hn : 1 ≤ n) :
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
    hC (Deform.im_trigS_mul_G_ofReal P.r n) hn ?_ ?_ ?_ hD.x1_neg hD.top_im_neg hD.bot_im_neg
  · simp only [lineM]; linarith
  · simp only [lineM]; rw [hh1]; nlinarith [(Nat.cast_nonneg P.etaOne : (0 : ℝ) ≤ P.etaOne)]
  · rw [hh1]; nlinarith [hD.x1_gt]

/-- The constant `B` is nonzero. -/
theorem B_ne_zero (hP : P.Valid) {D : PathData} {b c c₀ ε₀ : ℝ}
    (hD : P.PathCert D b c c₀ ε₀) :
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
  have hu : D.u ∈ D.pathSet := by
    refine Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ?_))
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp only [PathData.bot, PathData.top, Complex.real_smul]
    push_cast
    ring
  have h0 : (P.eta0 : ℂ) + 2 * D.u ≠ 0 := by
    intro h
    have := hD.path_eta0 _ hu
    rw [h, norm_zero] at this
    linarith [hD.c₀_pos]
  refine mul_ne_zero (mul_ne_zero hv ?_) ?_
  · exact mul_ne_zero h0 (Complex.exp_ne_zero _)
  · rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) ha h.1

/-- `c₀ > 0`. -/
theorem c0_pos (hP : P.Valid) : 0 < P.c0 := by
  unfold c0
  apply div_pos
  · refine List.prod_pos fun x hx => ?_
    obtain ⟨η, hη, rfl⟩ := List.mem_map.mp hx
    have := hP.two_mul_lt η hη
    exact Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < P.eta0 - 2 * η))
  · refine List.prod_pos fun x hx => ?_
    obtain ⟨η, hη, rfl⟩ : ∃ η ∈ P.zs, x = η := by simpa using hx
    have := hP.etaOne_le η hη
    have := hP.etaOne_pos
    exact_mod_cast (by omega : 0 < η)

/-- `Aₙ > 0`. -/
theorem An_pos (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) : 0 < P.An n := by
  have := c0_pos hP
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold An
  have := zpow_pos hn0 (1 - ((P.q + P.r) / 2 : ℕ) : ℤ)
  positivity

/-- `Kₙ > 0` and `(1/n) log Kₙ → H`. -/
theorem Kn_pos (hP : P.Valid) (H : ℝ) (n : ℕ) (hn : 1 ≤ n) : 0 < P.Kn H n := by
  have := An_pos hP hn
  have : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  unfold Kn
  positivity

theorem tendsto_log_Kn (hP : P.Valid) (H : ℝ) :
    Tendsto (fun n : ℕ => Real.log (P.Kn H n) / n) atTop (𝓝 H) := by
  set k := (P.q - P.r) / 2
  set m : ℤ := 1 - ((P.q + P.r) / 2 : ℕ)
  set A := k * Real.log (2 * Real.pi) + Real.log P.c0 -
    Real.log (Real.pi * (P.r - 1).factorial)
  set B : ℝ := 1 / 2 + m
  have hc0 := c0_pos hP
  have hlog : ∀ n : ℕ, 1 ≤ n → Real.log (P.Kn H n) / n = A / n + B * (Real.log n / n) + H := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hfac : (0 : ℝ) < (P.r - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    unfold Kn An
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_sqrt hn0.le,
      Real.log_pow, Real.log_zpow]
    field_simp
    ring
  have h1 : Tendsto (fun n : ℕ => A / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat A
  have h2 : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have hlim := (h1.add (h2.const_mul B)).add_const H
  rw [zero_add, mul_zero, zero_add] at hlim
  exact hlim.congr' (eventually_atTop.mpr ⟨1, fun n hn => (hlog n hn).symm⟩)

end Params

end OddZeta
