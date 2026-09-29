import OddZeta.Family.Phase

/-!
# The r-independent regions of Section 8.4 and their bounds (Lemma 8.7 of the note)

For `r ≥ 51` the path `L_r` is `-i∞ → P_R → bot → σ → top → P_L → x₀` with `P_L = x_L - i y_c`,
`P_R = x_R - i y_c`, `x₀ = -2`, `y_c = 1/4`, `x_L = 2.092953`, `x_R = 20`, and `top ∈ B_L`,
`bot ∈ B_R` for the rectangles
`B_L = [2.092953, 2.702953] × [-0.523633, 0]`, `B_R = [5.604839, 20] × [-0.827198, 0]`.
On each piece, `Re Fd = r Re g + (Re e + 2π Im u)` is bounded using the r-independent suprema
`S_g` of `Re g` and `S_e` of `Re e + 2π Im u` below (rectangles: by the maximum principle, from
their boundaries; the ray: up to `Y₁ = 162` by a grid, beyond by monotonicity, Lemma 8.6; on
the ray `Re e` is decreasing, so it is bounded by its value `≈ -9.7214` at `y = 1/4`, and
`Re Fd = r Re g + Re e - 2πy` decays linearly).
-/

namespace OddZeta

open Complex

/-- `B_L`. -/
def regBL : Set ℂ := {z | 2092953 / 1000000 ≤ z.re ∧ z.re ≤ 2702953 / 1000000 ∧
  -(523633 / 1000000 : ℝ) ≤ z.im ∧ z.im ≤ 0}

/-- `B_R`. -/
def regBR : Set ℂ := {z | 5604839 / 1000000 ≤ z.re ∧ z.re ≤ 20 ∧
  -(827198 / 1000000 : ℝ) ≤ z.im ∧ z.im ≤ 0}

/-- `P_L = x_L - i y_c`. -/
noncomputable def regPL : ℂ := (2092953 / 1000000 : ℝ) - (1 / 4 : ℝ) * I

/-- `P_R = x_R - i y_c`. -/
noncomputable def regPR : ℂ := (20 : ℝ) - (1 / 4 : ℝ) * I

/-- **Lemma 8.7**, four of the five rows (the upper ray of the note is not needed here), with the
bounds of the note loosened by about `5·10⁻⁴`. -/
theorem regBL_bound : ∀ z ∈ regBL, (famG z).re ≤ -2322435 / 10000 ∧
    (famE z).re + 2 * Real.pi * z.im ≤ -93025 / 10000 := by
  sorry

theorem regBR_bound : ∀ z ∈ regBR, (famG z).re ≤ -2321627 / 10000 ∧
    (famE z).re + 2 * Real.pi * z.im ≤ -93914 / 10000 := by
  sorry

theorem regPL_bound : ∀ z ∈ segment ℝ regPL (-2 : ℂ), (famG z).re ≤ -2325535 / 10000 ∧
    (famE z).re + 2 * Real.pi * z.im ≤ -91937 / 10000 := by
  sorry

theorem regRay_bound : ∀ y : ℝ, 1 / 4 ≤ y →
    (famG ((20 : ℝ) - y * I)).re ≤ -2400670 / 10000 ∧
      (famE ((20 : ℝ) - y * I)).re ≤ -97210 / 10000 := by
  sorry

end OddZeta
