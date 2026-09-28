/-
Copyright (c) 2026. All rights reserved.
-/
import OddZeta.Numerics.Interval

/-!
# Verified bounds for `Complex.arg (x + y i)` and `Real.log ‖x + y i‖`, `x y : ℚ`

* `arg`: with `θ = theta (|y| …) (|x| …) ∈ [0, π/2]` the angle of `(|x|, |y|)`, the argument is
  `θ`, `-θ`, `π - θ` or `θ - π` depending on the quadrant.
* `log ‖x + y i‖ = log (x² + y²) / 2`, computed by `logCore` on the natural numbers
  `(|x.num| y.den)² + (|y.num| x.den)²` and `(x.den y.den)²`.
-/

namespace OddZeta.Num

open Real

/-! ### The argument of a complex number in terms of `arctan` -/

theorem arg_of_re_pos' {X Y : ℝ} (hX : 0 < X) :
    Complex.arg (X + Y * Complex.I) = arctan (Y / X) := by
  set z : ℂ := X + Y * Complex.I with hz
  have hre : z.re = X := by simp [hz]
  have him : z.im = Y := by simp [hz]
  have h1 := Complex.tan_arg z
  have h2 : |Complex.arg z| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact hX))
  rw [abs_lt] at h2
  rw [← hre, ← him, ← h1, arctan_tan h2.1 h2.2]

/-- The angle `T ∈ [0, π/2]` of the vector `(|X|, |Y|)`. -/
noncomputable def angleT (X Y : ℝ) : ℝ := if X = 0 then π / 2 else arctan (|Y| / |X|)

theorem arg_eq_angleT {X Y : ℝ} (h : X ≠ 0 ∨ Y ≠ 0) :
    Complex.arg (X + Y * Complex.I) =
      if 0 ≤ X then (if 0 ≤ Y then angleT X Y else -angleT X Y)
      else (if 0 ≤ Y then π - angleT X Y else angleT X Y - π) := by
  rcases lt_trichotomy X 0 with hX | hX | hX
  · -- `X < 0`
    have hX' : X ≠ 0 := hX.ne
    simp only [angleT, ite_eq_right hX', ite_eq_right (not_le.mpr hX)]
    set z : ℂ := X + Y * Complex.I with hz
    have hneg : -z = ((-X : ℝ) : ℂ) + ((-Y : ℝ) : ℂ) * Complex.I := by
      simp only [hz, Complex.ofReal_neg]; ring
    have hA : Complex.arg (-z) = arctan (Y / X) := by
      rw [hneg, arg_of_re_pos' (neg_pos.mpr hX), neg_div_neg_eq]
    rcases lt_trichotomy Y 0 with hY | hY | hY
    · have h := Complex.arg_neg_eq_arg_add_pi_of_im_neg (x := z) (by simpa [hz] using hY)
      rw [ite_eq_right (not_le.mpr hY), abs_of_neg hY, abs_of_neg hX, neg_div_neg_eq]
      linarith
    · subst hY
      have : z = (X : ℂ) := by simp [hz]
      rw [this, Complex.arg_ofReal_of_neg hX, ite_eq_left le_rfl]
      simp
    · have h := Complex.arg_neg_eq_arg_sub_pi_of_im_pos (x := z) (by simpa [hz] using hY)
      rw [ite_eq_left hY.le, abs_of_pos hY, abs_of_neg hX]
      have : arctan (Y / X) = -arctan (Y / -X) := by rw [div_neg, arctan_neg, neg_neg]
      linarith
  · -- `X = 0`
    subst hX
    have hY : Y ≠ 0 := h.resolve_left (fun h => h rfl)
    simp only [angleT, ite_eq_left le_rfl]
    rcases lt_or_gt_of_ne hY with hY | hY
    · rw [ite_eq_right (not_le.mpr hY)]
      exact Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨by simp, by simpa using hY⟩
    · rw [ite_eq_left hY.le]
      exact Complex.arg_eq_pi_div_two_iff.mpr ⟨by simp, by simpa using hY⟩
  · -- `X > 0`
    simp only [angleT, ite_eq_right hX.ne', ite_eq_left hX.le, abs_of_pos hX]
    rw [arg_of_re_pos' hX]
    split_ifs with hY
    · rw [abs_of_nonneg hY]
    · rw [abs_of_neg (not_le.mp hY), neg_div, arctan_neg, neg_neg]

theorem angleT_nonneg (X Y : ℝ) : 0 ≤ angleT X Y := by
  unfold angleT
  split_ifs
  · positivity
  · exact arctan_nonneg.mpr (by positivity)

theorem angleT_le (X Y : ℝ) : angleT X Y ≤ π / 2 := by
  unfold angleT
  split_ifs
  · exact le_rfl
  · exact (arctan_lt_pi_div_two _).le

/-! ### Rational inputs -/

/-- `true` iff the integer is nonnegative (a cheap test for the kernel). -/
def intNonneg : ℤ → Bool
  | .ofNat _ => true
  | .negSucc _ => false

theorem intNonneg_iff (z : ℤ) : intNonneg z = true ↔ 0 ≤ z := by
  cases z <;> simp [intNonneg]

theorem rat_abs_eq (x : ℚ) : |(x : ℝ)| = (x.num.natAbs : ℝ) / x.den := by
  rw [Rat.cast_def, abs_div, Nat.cast_natAbs, Int.cast_abs]
  simp

theorem angleT_rat (x y : ℚ) :
    angleT x y = theta (y.num.natAbs * x.den) (x.num.natAbs * y.den) := by
  have hxd : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
  have hyd : (0 : ℝ) < y.den := by exact_mod_cast y.den_pos
  unfold angleT theta
  by_cases hx : x = 0
  · have : x.num.natAbs * y.den = 0 := by simp [hx]
    simp [hx]
  · have hxr : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    have hq : x.num.natAbs * y.den ≠ 0 :=
      Nat.mul_ne_zero (by simpa using hx) y.den_pos.ne'
    rw [ite_eq_right hxr, ite_eq_right hq, rat_abs_eq, rat_abs_eq]
    congr 1
    push_cast
    have : (x.num.natAbs : ℝ) ≠ 0 := by
      have : x.num.natAbs ≠ 0 := by simpa using hx
      exact_mod_cast this
    field_simp

/-- Bounds for `2^P arg (x + y i)`. -/
def argCore (x y : ℚ) (P : ℕ) : SB :=
  let r := atanNN (y.num.natAbs * x.den) (x.num.natAbs * y.den) P
  let pl := piT >>> (256 - P)
  let ph := ((piT + 64) >>> (256 - P)) + 1
  bif intNonneg x.num then
    (bif intNonneg y.num then ⟨r.1, 0, r.2, 0⟩ else ⟨0, r.2, 0, r.1⟩)
  else
    (bif intNonneg y.num then ⟨pl - r.2, 0, ph - r.1, 0⟩ else ⟨0, ph - r.1, 0, pl - r.2⟩)

theorem argCore_spec {x y : ℚ} (h : x ≠ 0 ∨ y ≠ 0) {P : ℕ} (hP : P ≤ 256) :
    (argCore x y P).Bounds (2 ^ P * Complex.arg ((x : ℝ) + (y : ℝ) * Complex.I)) := by
  have hne : (x : ℝ) ≠ 0 ∨ (y : ℝ) ≠ 0 := by
    rcases h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  have hpq : 0 < y.num.natAbs * x.den ∨ 0 < x.num.natAbs * y.den := by
    rcases h with h | h
    · exact Or.inr (Nat.mul_pos (by simpa using h) y.den_pos)
    · exact Or.inl (Nat.mul_pos (by simpa using h) x.den_pos)
  obtain ⟨r1, r2⟩ := atanNN_spec hpq hP
  rw [← angleT_rat] at r1 r2
  obtain ⟨p1, p2⟩ := shift_bounds hP piT_bounds.1 piT_bounds.2
  have hT0 := angleT_nonneg (x : ℝ) y
  have hT1 := angleT_le (x : ℝ) y
  have hpi := Real.pi_pos
  rw [arg_eq_angleT hne]
  unfold argCore SB.Bounds
  generalize atanNN (y.num.natAbs * x.den) (x.num.natAbs * y.den) P = r at r1 r2
  generalize angleT (x : ℝ) y = T at r1 r2 hT0 hT1
  have hP0 : (0 : ℝ) < 2 ^ P := by positivity
  cases hx : intNonneg x.num <;> cases hy : intNonneg y.num
  · have hx' : ¬ (0 : ℝ) ≤ x := by
      have := (intNonneg_iff x.num).not.mp (by simp [hx])
      exact_mod_cast fun h' => this (Rat.num_nonneg.mpr (by exact_mod_cast h'))
    have hy' : ¬ (0 : ℝ) ≤ y := by
      have := (intNonneg_iff y.num).not.mp (by simp [hy])
      exact_mod_cast fun h' => this (Rat.num_nonneg.mpr (by exact_mod_cast h'))
    simp only [Bool.cond_false, ite_eq_right hx', ite_eq_right hy', Nat.cast_zero, zero_sub]
    have e1 := natCast_sub_ge (((piT + 64) >>> (256 - P)) + 1) r.1
    have e2 : (((piT >>> (256 - P)) - r.2 : ℕ) : ℝ) ≤ 2 ^ P * (π - T) :=
      natCast_sub_le_of (by nlinarith) (by rw [mul_sub]; linarith)
    constructor <;> nlinarith
  · have hx' : ¬ (0 : ℝ) ≤ x := by
      have := (intNonneg_iff x.num).not.mp (by simp [hx])
      exact_mod_cast fun h' => this (Rat.num_nonneg.mpr (by exact_mod_cast h'))
    have hy' : (0 : ℝ) ≤ y := by
      have := (intNonneg_iff y.num).mp hy
      exact_mod_cast Rat.num_nonneg.mp this
    simp only [Bool.cond_false, Bool.cond_true, ite_eq_right hx', ite_eq_left hy', Nat.cast_zero,
      sub_zero]
    have e1 := natCast_sub_ge (((piT + 64) >>> (256 - P)) + 1) r.1
    have e2 : (((piT >>> (256 - P)) - r.2 : ℕ) : ℝ) ≤ 2 ^ P * (π - T) :=
      natCast_sub_le_of (by nlinarith) (by rw [mul_sub]; linarith)
    constructor <;> nlinarith
  · have hx' : (0 : ℝ) ≤ x := by
      have := (intNonneg_iff x.num).mp hx
      exact_mod_cast Rat.num_nonneg.mp this
    have hy' : ¬ (0 : ℝ) ≤ y := by
      have := (intNonneg_iff y.num).not.mp (by simp [hy])
      exact_mod_cast fun h' => this (Rat.num_nonneg.mpr (by exact_mod_cast h'))
    simp only [Bool.cond_false, Bool.cond_true, ite_eq_left hx', ite_eq_right hy', Nat.cast_zero,
      zero_sub]
    constructor <;> linarith
  · have hx' : (0 : ℝ) ≤ x := by
      have := (intNonneg_iff x.num).mp hx
      exact_mod_cast Rat.num_nonneg.mp this
    have hy' : (0 : ℝ) ≤ y := by
      have := (intNonneg_iff y.num).mp hy
      exact_mod_cast Rat.num_nonneg.mp this
    simp only [Bool.cond_true, ite_eq_left hx', ite_eq_left hy', Nat.cast_zero, sub_zero]
    exact ⟨r1, r2⟩

/-- Lower bound for `Complex.arg (x + y i)`, with denominator `2^min prec 240`. -/
def argLo (x y : ℚ) (prec : ℕ) : ℚ :=
  let P := workPrec prec
  let r := argCore x y P
  subQ r.lp r.ln P

/-- Upper bound for `Complex.arg (x + y i)`, with denominator `2^min prec 240`. -/
def argHi (x y : ℚ) (prec : ℕ) : ℚ :=
  let P := workPrec prec
  let r := argCore x y P
  subQ r.hp r.hn P

theorem ratCast_add_mul_I (x y : ℚ) :
    ((x : ℂ) + (y : ℂ) * Complex.I) = (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I) := by
  simp

theorem argLo_le {x y : ℚ} (h : x ≠ 0 ∨ y ≠ 0) (prec : ℕ) :
    ((argLo x y prec : ℚ) : ℝ) ≤ Complex.arg (x + y * Complex.I) := by
  rw [ratCast_add_mul_I]
  exact SB.lo_le (argCore_spec h (workPrec_le prec))

theorem le_argHi {x y : ℚ} (h : x ≠ 0 ∨ y ≠ 0) (prec : ℕ) :
    Complex.arg (x + y * Complex.I) ≤ ((argHi x y prec : ℚ) : ℝ) := by
  rw [ratCast_add_mul_I]
  exact SB.le_hi (argCore_spec h (workPrec_le prec))

/-! ### `log ‖x + y i‖` -/

/-- Bounds for `2^P log (x² + y²) = 2^(P+1) log ‖x + y i‖`. -/
def logAbsCore (x y : ℚ) (P : ℕ) : SB :=
  let a := x.num.natAbs * y.den
  let c := y.num.natAbs * x.den
  let e := x.den * y.den
  logCore (a * a + c * c) (e * e) P

/-- Lower bound for `Real.log ‖x + y i‖`, with denominator `2^(min prec 240 + 1)`. -/
def logAbsLo (x y : ℚ) (prec : ℕ) : ℚ :=
  let P := workPrec prec
  let r := logAbsCore x y P
  subQ r.lp r.ln (P + 1)

/-- Upper bound for `Real.log ‖x + y i‖`, with denominator `2^(min prec 240 + 1)`. -/
def logAbsHi (x y : ℚ) (prec : ℕ) : ℚ :=
  let P := workPrec prec
  let r := logAbsCore x y P
  subQ r.hp r.hn (P + 1)

theorem logAbsCore_spec {x y : ℚ} (h : x ≠ 0 ∨ y ≠ 0) {P : ℕ} (hP : P ≤ 256) :
    (logAbsCore x y P).Bounds (2 ^ (P + 1) * Real.log ‖(x : ℂ) + y * Complex.I‖) := by
  have hxd : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
  have hyd : (0 : ℝ) < y.den := by exact_mod_cast y.den_pos
  set a := x.num.natAbs * y.den with ha
  set c := y.num.natAbs * x.den with hc
  set e := x.den * y.den with he
  have hpos : 0 < a * a + c * c := by
    rcases h with h | h
    · have : 0 < a := Nat.mul_pos (by simpa using h) y.den_pos
      positivity
    · have : 0 < c := Nat.mul_pos (by simpa using h) x.den_pos
      positivity
  have he0 : 0 < e * e := by positivity
  have hs := logCore_spec hpos he0 hP
  unfold logAbsCore
  convert hs using 1
  have hnorm : ‖(x : ℂ) + y * Complex.I‖ = √((x : ℝ) ^ 2 + (y : ℝ) ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp
  have hsq : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 = ((a * a + c * c : ℕ) : ℝ) / ((e * e : ℕ) : ℝ) := by
    rw [← sq_abs (x : ℝ), ← sq_abs (y : ℝ), rat_abs_eq, rat_abs_eq, ha, hc, he]
    push_cast
    field_simp
  rw [hnorm, Real.log_sqrt (by positivity), hsq, pow_succ]
  ring

theorem logAbsLo_le {x y : ℚ} (h : x ≠ 0 ∨ y ≠ 0) (prec : ℕ) :
    ((logAbsLo x y prec : ℚ) : ℝ) ≤ Real.log ‖(x : ℂ) + y * Complex.I‖ :=
  SB.lo_le (logAbsCore_spec h (workPrec_le prec))

theorem le_logAbsHi {x y : ℚ} (h : x ≠ 0 ∨ y ≠ 0) (prec : ℕ) :
    Real.log ‖(x : ℂ) + y * Complex.I‖ ≤ ((logAbsHi x y prec : ℚ) : ℝ) :=
  SB.le_hi (logAbsCore_spec h (workPrec_le prec))

end OddZeta.Num
