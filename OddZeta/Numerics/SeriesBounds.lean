/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Truncation bounds for the `artanh` and `arctan` power series

For `|u| < 1` we bound the tail of the series
`artanh u = ∑ u^(2k+1)/(2k+1)` and `arctan u = ∑ (-1)^k u^(2k+1)/(2k+1)`
by the geometric majorant `|u|^(2n+1) / (1 - u^2)`.

Both functions are treated simultaneously through a Boolean flag `neg`
(`neg = true` for `arctan`).
-/

namespace OddZeta.Num

open Real Finset

/-- `serF false u = artanh u = (log (1 + u) - log (1 - u)) / 2` and `serF true u = arctan u`. -/
noncomputable def serF (neg : Bool) (u : ℝ) : ℝ :=
  if neg then Real.arctan u else (Real.log (1 + u) - Real.log (1 - u)) / 2

/-- The sign `(-1)^k` for `arctan`, `1` for `artanh`. -/
def serSign (neg : Bool) : ℝ := if neg then -1 else 1

/-- The `k`-th term of the power series of `serF neg`. -/
noncomputable def serTerm (neg : Bool) (u : ℝ) (k : ℕ) : ℝ :=
  serSign neg ^ k * u ^ (2 * k + 1) / (2 * k + 1)

theorem hasSum_serTerm (neg : Bool) {u : ℝ} (hu : |u| < 1) :
    HasSum (serTerm neg u) (serF neg u) := by
  cases neg
  · have h := (Real.hasSum_log_sub_log_of_abs_lt_one hu).div_const 2
    simp only [serF, Bool.false_eq_true, ↓reduceIte]
    convert h using 1
    funext k
    simp only [serTerm, serSign, Bool.false_eq_true, ↓reduceIte, one_pow, one_mul]
    field_simp
  · have h := Real.hasSum_arctan (x := u) (by simpa [Real.norm_eq_abs] using hu)
    simp only [serF, ↓reduceIte]
    convert h using 1
    funext k
    simp [serTerm, serSign]

theorem abs_serTerm_le (neg : Bool) (u : ℝ) (k : ℕ) :
    |serTerm neg u k| ≤ |u| ^ (2 * k + 1) := by
  have hs : |serSign neg ^ k| = 1 := by cases neg <;> simp [serSign]
  rw [serTerm, abs_div, abs_mul, hs, one_mul, abs_pow]
  have h1 : (1 : ℝ) ≤ |(2 * (k : ℝ) + 1)| := by
    rw [abs_of_pos (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  exact div_le_self (by positivity) h1

/-- Tail bound: `|f u - ∑_{k<n} term_k| ≤ |u|^(2n+1) / (1 - u^2)`. -/
theorem abs_serF_sub_sum_le (neg : Bool) {u : ℝ} (hu : |u| < 1) (n : ℕ) :
    |serF neg u - ∑ k ∈ range n, serTerm neg u k| ≤ |u| ^ (2 * n + 1) / (1 - u ^ 2) := by
  have h := (hasSum_nat_add_iff' n).mpr (hasSum_serTerm neg hu)
  have hu2 : u ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg u]
  have hg : HasSum (fun k : ℕ => |u| ^ (2 * n + 1) * (u ^ 2) ^ k)
      (|u| ^ (2 * n + 1) * (1 - u ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (sq_nonneg u) hu2).mul_left _
  have := h.norm_le_of_bounded hg (fun k => by
    rw [Real.norm_eq_abs]
    refine (abs_serTerm_le neg u (k + n)).trans (le_of_eq ?_)
    rw [← sq_abs u, ← pow_mul, ← pow_add]
    ring_nf)
  simpa [Real.norm_eq_abs, div_eq_mul_inv] using this

theorem serF_nonneg (neg : Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : 0 ≤ serF neg u := by
  cases neg
  · simp only [serF, Bool.false_eq_true, ↓reduceIte]
    have : Real.log (1 - u) ≤ Real.log (1 + u) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  · simp only [serF, ↓reduceIte]
    exact Real.arctan_nonneg.mpr hu0

end OddZeta.Num
