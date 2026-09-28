import OddZeta.Analytic.Saddle
import OddZeta.Analytic.SaddleAux

/-!
# Auxiliary facts about the path `L` for the saddle-point asymptotics

Membership of the pieces of `L` in `D.pathSet`, monotonicity of `Re Fd` along `L \ σ`, and the
pointwise bounds for the integrand `S(nu) Gₙ(nu)`.
-/

namespace OddZeta

open Complex MeasureTheory Filter Topology

namespace Params

variable {P : Params} {D : PathData} {b c c₀ ε₀ : ℝ}

/-! ### Geometry of the path -/

theorem PathData.bot_im (D : PathData) : D.bot.im = D.u.im - D.v.im := by
  simp [PathData.bot]

theorem PathData.top_im (D : PathData) : D.top.im = D.u.im + D.v.im := by
  simp [PathData.top]

theorem mem_pathSet_ray {y : ℝ} (hy : y ≤ D.bot.im) :
    (D.bot.re : ℂ) + y * I ∈ D.pathSet := by
  left; left; left
  constructor <;> simp [hy]

theorem mem_pathSet_sigma {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    D.u + s * D.v ∈ D.pathSet := by
  left; left; right
  have ht : (s + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  have := add_mul_sub_mem_segment (a := D.bot) (b := D.top) ht
  convert this using 1
  simp only [PathData.bot, PathData.top]
  push_cast
  ring

theorem mem_pathSet_horiz (hD : P.PathCert D b c c₀ ε₀) {x : ℝ}
    (hx : x ∈ Set.Icc D.x1 D.top.re) : (x : ℂ) + D.top.im * I ∈ D.pathSet := by
  left; right
  have hlt := hD.x1_lt
  have hne : D.top.re - D.x1 ≠ 0 := (sub_pos.2 hlt).ne'
  set t := (D.top.re - x) / (D.top.re - D.x1) with ht_def
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hx.2]) (by linarith)
    · rw [div_le_one (by linarith)]; linarith [hx.1]
  have := add_mul_sub_mem_segment (a := D.top) (b := D.corner) ht
  convert this using 1
  apply Complex.ext
  · simp only [PathData.corner, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      mul_one, sub_zero, sub_re, zero_mul, add_zero]
    rw [ht_def]
    field_simp
    ring
  · simp only [PathData.corner, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
      mul_one, zero_add, sub_im, sub_self, add_zero, zero_mul]

theorem mem_pathSet_vert (hD : P.PathCert D b c c₀ ε₀) {y : ℝ}
    (hy : y ∈ Set.Icc D.top.im 0) : (D.x1 : ℂ) + y * I ∈ D.pathSet := by
  right
  have hlt := hD.top_im_neg
  have hne : D.top.im ≠ 0 := hlt.ne
  set t := 1 - y / D.top.im with ht_def
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : y / D.top.im ≤ 1 := by rw [div_le_one_of_neg hlt]; exact hy.1
    have h2 : 0 ≤ y / D.top.im := div_nonneg_of_nonpos hy.2 hlt.le
    constructor <;> linarith
  have := add_mul_sub_mem_segment (a := D.corner) (b := (D.x1 : ℂ)) ht
  convert this using 1
  apply Complex.ext
  · simp only [PathData.corner, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      mul_one, sub_re, zero_mul, add_zero, sub_self]
  · simp only [PathData.corner, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
      mul_one, zero_add, sub_im, zero_sub, add_zero, zero_mul]
    rw [ht_def]
    field_simp
    ring

theorem Ghat_ne_zero_of_mem (hD : P.PathCert D b c c₀ ε₀) {u : ℂ} (hu : u ∈ D.pathSet) :
    P.Ghat u ≠ 0 := by
  refine Ghat_ne_zero fun h => ?_
  have := hD.path_eta0 u hu
  rw [h, norm_zero] at this
  linarith [hD.c₀_pos]

/-! ### The phase `Fd` -/

theorem hasDerivAt_Fd {z : ℂ} (hz : P.Good z) :
    HasDerivAt P.Fd (P.f' z + I * ((P.r : ℂ) - 2) * Real.pi) z := by
  have := (hasDerivAt_f hz).add ((hasDerivAt_id' z).const_mul (I * ((P.r : ℂ) - 2) * Real.pi))
  convert this using 1
  · rfl
  · ring

theorem re_Fd (u : ℂ) : (P.Fd u).re = (P.f u).re - (P.r - 2) * Real.pi * u.im := by
  unfold Fd
  rw [add_re, re_I_mul_sub_two]
  ring

theorem im_Fd' (w : ℂ) : (w + I * ((P.r : ℂ) - 2) * Real.pi).im = w.im + (P.r - 2) * Real.pi := by
  simp only [add_im, mul_im, mul_re, I_re, I_im, ofReal_re, ofReal_im, sub_re, sub_im,
    natCast_re, natCast_im, re_ofNat, im_ofNat]
  ring

theorem re_Fd' (w : ℂ) : (w + I * ((P.r : ℂ) - 2) * Real.pi).re = w.re := by
  simp only [add_re, mul_im, mul_re, I_re, I_im, ofReal_re, ofReal_im, sub_re, sub_im,
    natCast_re, natCast_im, re_ofNat, im_ofNat]
  ring

/-! ### Monotonicity of `Re Fd` along `L \ σ` -/

theorem PathCert.ray_le (hD : P.PathCert D b c c₀ ε₀) {y : ℝ} (hy : y ≤ D.bot.im) :
    (P.Fd (D.bot.re + y * I)).re ≤ (P.Fd D.bot).re - c * (D.bot.im - y) := by
  have hder : ∀ y : ℝ, y ≤ D.bot.im → HasDerivAt (fun y : ℝ => (P.Fd (D.bot.re + y * I)).re)
      (-((P.f' (D.bot.re + y * I)).im + (P.r - 2) * Real.pi)) y := by
    intro y hy
    have hgood : P.Good (D.bot.re + y * I) :=
      good_of_im_ne_zero (by simp; linarith [hD.bot_im_neg])
    have h1 : HasDerivAt (fun w : ℂ => (D.bot.re : ℂ) + w * I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id' (y : ℂ)).mul_const I).const_add (D.bot.re : ℂ)
    have h2 := ((hasDerivAt_Fd hgood).comp (y : ℂ) h1).real_of_complex
    rw [mul_I_re, im_Fd'] at h2
    exact h2
  have hmono : MonotoneOn (fun y : ℝ => (P.Fd (D.bot.re + y * I)).re - c * y)
      (Set.Iic D.bot.im) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic _)
      (f' := fun y => -((P.f' (D.bot.re + y * I)).im + (P.r - 2) * Real.pi) - c)
    · intro y hy
      exact ((hder y hy).continuousAt.sub
        (continuousAt_const.mul continuousAt_id)).continuousWithinAt
    · intro y hy
      rw [interior_Iic] at hy
      exact ((hder y hy.le).sub ((hasDerivAt_id y).const_mul c)).hasDerivWithinAt.congr_deriv
        (by simp)
    · intro y hy
      rw [interior_Iic] at hy
      have := hD.ray y hy.le
      linarith
  have := hmono hy (Set.mem_Iic.2 le_rfl) hy
  simp only at this
  rw [re_add_im] at this
  linarith

theorem PathCert.horiz_le (hD : P.PathCert D b c c₀ ε₀) {x : ℝ}
    (hx : x ∈ Set.Icc D.x1 D.top.re) :
    (P.Fd (x + D.top.im * I)).re ≤ (P.Fd D.top).re := by
  have hder : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (P.Fd (x + D.top.im * I)).re)
      (P.f' (x + D.top.im * I)).re x := by
    intro x
    have hgood : P.Good (x + D.top.im * I) :=
      good_of_im_ne_zero (by simp; linarith [hD.top_im_neg])
    have h1 : HasDerivAt (fun w : ℂ => w + (D.top.im : ℂ) * I) 1 (x : ℂ) :=
      (hasDerivAt_id' (x : ℂ)).add_const _
    have h2 := ((hasDerivAt_Fd hgood).comp (x : ℂ) h1).real_of_complex
    rw [mul_one, re_Fd'] at h2
    exact h2
  have hmono : MonotoneOn (fun x : ℝ => (P.Fd (x + D.top.im * I)).re)
      (Set.Icc D.x1 D.top.re) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (f' := fun x => (P.f' (x + D.top.im * I)).re)
    · intro x _
      exact (hder x).continuousAt.continuousWithinAt
    · intro x _
      exact (hder x).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hD.horiz x (Set.Ioo_subset_Icc_self hx)).le
  have := hmono hx (Set.right_mem_Icc.2 hD.x1_lt.le) hx.2
  simp only at this
  rwa [re_add_im] at this

theorem PathCert.vert_le (hP : P.Valid) (hD : P.PathCert D b c c₀ ε₀) {y : ℝ}
    (hy : y ∈ Set.Icc D.top.im 0) :
    (P.Fd (D.x1 + y * I)).re ≤ (P.Fd D.corner).re := by
  have hgood : ∀ y ∈ Set.Icc D.top.im 0, P.Good (D.x1 + y * I) := by
    intro y hy
    rcases hy.2.lt_or_eq with h | h
    · exact good_of_im_ne_zero (by simp; linarith)
    · rw [h]
      simpa using good_of_real hP hD.x1_neg hD.x1_gt
  have hder : ∀ y ∈ Set.Icc D.top.im 0, HasDerivAt (fun y : ℝ => -(P.Fd (D.x1 + y * I)).re)
      ((P.f' (D.x1 + y * I)).im + (P.r - 2) * Real.pi) y := by
    intro y hy
    have h1 : HasDerivAt (fun w : ℂ => (D.x1 : ℂ) + w * I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id' (y : ℂ)).mul_const I).const_add (D.x1 : ℂ)
    have h2 := ((hasDerivAt_Fd (hgood y hy)).comp (y : ℂ) h1).real_of_complex.neg
    rw [mul_I_re, im_Fd', neg_neg] at h2
    exact h2
  have hmono : MonotoneOn (fun y : ℝ => -(P.Fd (D.x1 + y * I)).re) (Set.Icc D.top.im 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (f' := fun y => (P.f' (D.x1 + y * I)).im + (P.r - 2) * Real.pi)
    · intro y hy
      exact (hder y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hder y (interior_subset hy)).hasDerivWithinAt
    · intro y hy
      exact (hD.vert y (interior_subset hy)).le
  have := hmono (Set.left_mem_Icc.2 hD.top_im_neg.le) hy hy.1
  simp only [neg_le_neg_iff] at this
  exact this

theorem PathCert.top_le (hD : P.PathCert D b c c₀ ε₀) :
    (P.Fd D.top).re ≤ (P.Fd D.u).re - b := by
  have := hD.sigma_decay 1 (by constructor <;> norm_num)
  rw [sub_re] at this
  simp only [ofReal_one, one_mul, one_pow, mul_one] at this
  rw [PathData.top]
  linarith

theorem PathCert.bot_le (hD : P.PathCert D b c c₀ ε₀) :
    (P.Fd D.bot).re ≤ (P.Fd D.u).re - b := by
  have := hD.sigma_decay (-1) (by constructor <;> norm_num)
  rw [sub_re] at this
  simp only [ofReal_neg, ofReal_one, neg_one_mul, even_two, Even.neg_pow, one_pow,
    mul_one] at this
  rw [PathData.bot, sub_eq_add_neg]
  linarith

theorem PathCert.ray_bound (hD : P.PathCert D b c c₀ ε₀) {y : ℝ} (hy : y ≤ D.bot.im) :
    (P.Fd (D.bot.re + y * I)).re ≤ (P.Fd D.u).re - b - c * (D.bot.im - y) := by
  linarith [hD.ray_le hy, hD.bot_le]

theorem PathCert.horiz_bound (hD : P.PathCert D b c c₀ ε₀) {x : ℝ}
    (hx : x ∈ Set.Icc D.x1 D.top.re) :
    (P.Fd (x + D.top.im * I)).re ≤ (P.Fd D.u).re - b := by
  linarith [hD.horiz_le hx, hD.top_le]

theorem PathCert.vert_bound (hP : P.Valid) (hD : P.PathCert D b c c₀ ε₀) {y : ℝ}
    (hy : y ∈ Set.Icc D.top.im 0) :
    (P.Fd (D.x1 + y * I)).re ≤ (P.Fd D.u).re - b := by
  have h1 := hD.vert_le hP hy
  have h2 := hD.horiz_le (x := D.x1) (Set.left_mem_Icc.2 hD.x1_lt.le)
  have h3 := hD.top_le
  rw [PathData.corner] at h1
  linarith

end Params

end OddZeta
