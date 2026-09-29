import OddZeta.Family.LargeBounds
import OddZeta.Family.Regions
import OddZeta.Cert.ToolsAux3

/-!
# Geometry of the path `L_r` for `r ≥ 301` (Section 8.4 of the note)

Elementary facts about segments in `ℂ`, the arguments `arg (-z)` on the path, and the pieces of
the path `-i∞ → P_R → bot → σ → top → P_L → -2`.
-/

namespace OddZeta

open Complex Metric Set

namespace Large

/-- Points of a segment. -/
theorem seg_re_im {x y z : ℂ} (hz : z ∈ segment ℝ x y) : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
    z.re = x.re + θ * (y.re - x.re) ∧ z.im = x.im + θ * (y.im - x.im) := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hz
  exact ⟨θ, h0, h1, by simp, by simp⟩

theorem interp_ge {a b l θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ha : l ≤ a) (hb : l ≤ b) :
    l ≤ a + θ * (b - a) := by nlinarith

theorem interp_le {a b l θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ha : a ≤ l) (hb : b ≤ l) :
    a + θ * (b - a) ≤ l := by nlinarith

/-- A segment between two points of a box lies in the box. -/
theorem seg_box {x y z : ℂ} {a₁ a₂ b₁ b₂ : ℝ} (hz : z ∈ segment ℝ x y)
    (hx : a₁ ≤ x.re ∧ x.re ≤ a₂ ∧ b₁ ≤ x.im ∧ x.im ≤ b₂)
    (hy : a₁ ≤ y.re ∧ y.re ≤ a₂ ∧ b₁ ≤ y.im ∧ y.im ≤ b₂) :
    a₁ ≤ z.re ∧ z.re ≤ a₂ ∧ b₁ ≤ z.im ∧ z.im ≤ b₂ := by
  obtain ⟨θ, h0, h1, hre, him⟩ := seg_re_im hz
  rw [hre, him]
  exact ⟨interp_ge h0 h1 hx.1 hy.1, interp_le h0 h1 hx.2.1 hy.2.1, interp_ge h0 h1 hx.2.2.1 hy.2.2.1,
    interp_le h0 h1 hx.2.2.2 hy.2.2.2⟩

theorem seg_regBL {x y z : ℂ} (hz : z ∈ segment ℝ x y) (hx : x ∈ regBL) (hy : y ∈ regBL) :
    z ∈ regBL :=
  seg_box hz hx hy

theorem seg_regBR {x y z : ℂ} (hz : z ∈ segment ℝ x y) (hx : x ∈ regBR) (hy : y ∈ regBR) :
    z ∈ regBR :=
  seg_box hz hx hy

theorem seg_im_le {x y z : ℂ} {c : ℝ} (hz : z ∈ segment ℝ x y) (hx : x.im ≤ c) (hy : y.im ≤ c) :
    z.im ≤ c := by
  obtain ⟨θ, h0, h1, -, him⟩ := seg_re_im hz
  rw [him]
  exact interp_le h0 h1 hx hy

/-- The last piece `[P_L, -2]`. -/
theorem seg_PL {z : ℂ} (hz : z ∈ segment ℝ regPL (-2 : ℂ)) :
    z = (-2 : ℂ) ∨ (z.im < 0 ∧ -2 ≤ z.re ∧ z.re ≤ 20 ∧ (z.re ≤ 0 ∨ z.im ≤ -(1 / 10)) ∧
      (1 / 10 ≤ |z.re| ∨ z.im ≤ -(1 / 10))) := by
  obtain ⟨θ, h0, h1, hre, him⟩ := seg_re_im hz
  have e1 : regPL.re = 2092953 / 1000000 := by simp [regPL]
  have e2 : regPL.im = -(1 / 4) := by simp [regPL]
  rw [e1] at hre
  rw [e2] at him
  simp only [neg_re, re_ofNat, neg_im, im_ofNat] at hre him
  rcases eq_or_lt_of_le h1 with h | h
  · left
    subst h
    apply Complex.ext <;> simp [hre, him]
  · right
    refine ⟨by rw [him]; nlinarith, by rw [hre]; nlinarith, by rw [hre]; nlinarith, ?_, ?_⟩
    · rcases le_or_gt (3 / 5) θ with h3 | h3
      · left; rw [hre]; nlinarith
      · right; rw [him]; nlinarith
    · rcases le_or_gt (3 / 5) θ with h3 | h3
      · left
        rw [hre, abs_of_neg (by nlinarith)]
        nlinarith
      · right; rw [him]; nlinarith

/-- `|arg (-z)| ≤ π/2 + arctan K` if `Im z < 0` and `Re z ≤ K |Im z|`. -/
theorem abs_arg_neg_le {z : ℂ} {K : ℝ} (hz : z.im < 0) (h : z.re ≤ K * -z.im) :
    |(-z).arg| ≤ Real.pi - (Real.pi / 2 - Real.arctan K) := by
  have him : 0 < (-z).im := by rw [neg_im]; linarith
  have harg := Cert.arg_mk_of_im_pos (-z).re him
  rw [← Cert.arg_eq_mk] at harg
  have hnn : 0 ≤ (-z).arg := Complex.arg_nonneg_iff.2 him.le
  rw [abs_of_nonneg hnn, harg]
  have h1 : -K ≤ (-z).re / (-z).im := by
    rw [le_div_iff₀ him, neg_re, neg_im]
    linarith
  have h2 := Real.arctan_strictMono.monotone h1
  rw [Real.arctan_neg] at h2
  linarith

end Large

end OddZeta
