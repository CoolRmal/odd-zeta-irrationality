/-
Copyright (c) 2026. All rights reserved.
-/
import OddZeta.Numerics.Tables
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Verified rational bounds for `log`, `arctan`, `π`, `Complex.arg` and `log ‖·‖`

All bound functions are computable and designed to be evaluated by the Lean *kernel*
(`decide +kernel`): the hot path uses only `ℕ` arithmetic (GMP-accelerated in the kernel),
`ℚ` only appears at the interface.

## Method
* `log x`: `x = (N/D) 2^e` with `N/D ∈ [1,2)`; `N/D = (1 + j/128) · X/Y` with `j` the
  nearest table point, and `log (X/Y) = 2 artanh ((X-Y)/(X+Y))` with `|(X-Y)/(X+Y)| ≤ 2^-9`.
  `log 2` and `log (1 + j/128)` come from certified `2^-256`-accurate tables.
* `arctan x`: odd symmetry, `arctan x = π/2 - arctan (1/x)` for `x > 1`, and for
  `0 ≤ x ≤ 1`: `arctan x = arctan (j/128) + arctan t`, `|t| ≤ 2^-8` (addition formula).
* In both cases the series is summed exactly (single final rounding) and a rigorous tail
  bound computed from the actual argument is added, see `seriesNN`.

The working precision is `min prec 240` bits; results are dyadic rationals with
denominator dividing `2^(min prec 240)` (`2^(min prec 240 + 1)` for `logAbs`).
-/

namespace OddZeta.Num

open Real

/-! ### Elementary helper lemmas -/

theorem natCast_sub_ge (x y : ℕ) : (x : ℝ) - y ≤ ((x - y : ℕ) : ℝ) := by
  rcases le_total y x with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, sub_nonpos]
    exact_mod_cast h

theorem natCast_sub_le_of {x y : ℕ} {v : ℝ} (hv : 0 ≤ v) (h : (x : ℝ) - y ≤ v) :
    ((x - y : ℕ) : ℝ) ≤ v := by
  rcases le_total y x with h' | h'
  · rwa [Nat.cast_sub h']
  · rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero]
    exact hv

theorem natCast_shiftRight_le (v s : ℕ) : ((v >>> s : ℕ) : ℝ) ≤ (v : ℝ) / 2 ^ s := by
  rw [Nat.shiftRight_eq_div_pow]
  exact (Nat.cast_div_le).trans (le_of_eq (by push_cast; ring))

theorem lt_natCast_shiftRight_add_one (v s : ℕ) :
    (v : ℝ) / 2 ^ s < ((v >>> s : ℕ) : ℝ) + 1 := by
  rw [Nat.shiftRight_eq_div_pow]
  have := natCast_div_lt_add_one v (Nat.two_pow_pos s)
  push_cast at this
  exact this

theorem two_pow_split {P : ℕ} (hP : P ≤ 256) : (2 : ℝ) ^ 256 = 2 ^ P * 2 ^ (256 - P) := by
  rw [← pow_add, Nat.add_sub_cancel' hP]

/-- Lower bound after rescaling a `2^256`-scaled lower bound to precision `P`. -/
theorem shift_lo {v P : ℕ} {x : ℝ} (hP : P ≤ 256) (h : (v : ℝ) ≤ 2 ^ 256 * x) :
    ((v >>> (256 - P) : ℕ) : ℝ) ≤ 2 ^ P * x := by
  refine (natCast_shiftRight_le _ _).trans ?_
  rw [div_le_iff₀ (by positivity)]
  calc (v : ℝ) ≤ 2 ^ 256 * x := h
    _ = 2 ^ P * x * 2 ^ (256 - P) := by rw [two_pow_split hP]; ring

/-- Upper bound after rescaling a `2^256`-scaled upper bound to precision `P`. -/
theorem shift_hi {w P : ℕ} {x : ℝ} (hP : P ≤ 256) (h : 2 ^ 256 * x ≤ w) :
    2 ^ P * x ≤ (((w >>> (256 - P)) + 1 : ℕ) : ℝ) := by
  push_cast
  refine le_trans ?_ (lt_natCast_shiftRight_add_one w _).le
  rw [le_div_iff₀ (by positivity)]
  calc 2 ^ P * x * 2 ^ (256 - P) = 2 ^ 256 * x := by rw [two_pow_split hP]; ring
    _ ≤ w := h

/-- Both bounds for a table constant with margin `64`. -/
theorem shift_bounds {v P : ℕ} {x : ℝ} (hP : P ≤ 256) (h1 : (v : ℝ) ≤ 2 ^ 256 * x)
    (h2 : 2 ^ 256 * x ≤ (v : ℝ) + 64) :
    ((v >>> (256 - P) : ℕ) : ℝ) ≤ 2 ^ P * x ∧
      2 ^ P * x ≤ ((((v + 64) >>> (256 - P)) + 1 : ℕ) : ℝ) :=
  ⟨shift_lo hP h1, shift_hi hP (by push_cast; exact h2)⟩

/-! ### Semantics of the tables -/

theorem two_serF_false_eq {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    2 * serF false ((X - Y) / (X + Y)) = Real.log (X / Y) := by
  simp only [serF, Bool.false_eq_true, ↓reduceIte]
  have hXY : 0 < X + Y := by positivity
  have h1 : 1 + (X - Y) / (X + Y) = 2 * X / (X + Y) := by field_simp; ring
  have h2 : 1 - (X - Y) / (X + Y) = 2 * Y / (X + Y) := by field_simp; ring
  rw [h1, h2, ← Real.log_div (by positivity) (by positivity)]
  have h3 : 2 * X / (X + Y) / (2 * Y / (X + Y)) = X / Y := by field_simp
  rw [h3]
  ring

theorem logTab_bounds {j : ℕ} (hj : j ≤ 128) :
    (tabGet logTab j : ℝ) ≤ 2 ^ 256 * Real.log (1 + j / 128) ∧
      2 ^ 256 * Real.log (1 + j / 128) ≤ (tabGet logTab j : ℝ) + 64 := by
  obtain ⟨c1, c2⟩ := logTab_check j (by omega)
  obtain ⟨s1, s2⟩ := seriesNN_spec false (a := j) (b := 256 + j) (by omega) 90 257
  have key : 2 ^ 257 * serF false ((j : ℝ) / ((256 + j : ℕ) : ℝ)) =
      2 ^ 256 * Real.log (1 + j / 128) := by
    have := two_serF_false_eq (X := 128 + j) (Y := 128) (by positivity) (by norm_num)
    have e1 : ((128 : ℝ) + j - 128) / (128 + j + 128) = (j : ℝ) / ((256 + j : ℕ) : ℝ) := by
      push_cast; ring_nf
    have e2 : ((128 : ℝ) + j) / 128 = 1 + j / 128 := by ring
    rw [e1, e2] at this
    rw [pow_succ, ← this]
    ring
  unfold logTabCert at c1 c2
  constructor
  · calc (tabGet logTab j : ℝ) ≤ ((seriesNN false j (256 + j) 90 257).1 : ℝ) := by
          exact_mod_cast c1
      _ ≤ _ := s1
      _ = _ := key
  · calc _ = _ := key.symm
      _ ≤ ((seriesNN false j (256 + j) 90 257).2 : ℝ) := s2
      _ ≤ _ := by exact_mod_cast c2

theorem log2T_bounds :
    (log2T : ℝ) ≤ 2 ^ 256 * Real.log 2 ∧ 2 ^ 256 * Real.log 2 ≤ (log2T : ℝ) + 64 := by
  obtain ⟨⟨c1, c2⟩, -⟩ := consts_check
  obtain ⟨s1, s2⟩ := seriesNN_spec false (a := 128) (b := 256 + 128) (by omega) 90 257
  have key : 2 ^ 257 * serF false (((128 : ℕ) : ℝ) / ((256 + 128 : ℕ) : ℝ)) =
      2 ^ 256 * Real.log 2 := by
    have := two_serF_false_eq (X := 256) (Y := 128) (by positivity) (by norm_num)
    norm_num at this ⊢
    rw [pow_succ, ← this]
    ring
  unfold logTabCert at c1 c2
  constructor
  · calc (log2T : ℝ) ≤ ((seriesNN false 128 (256 + 128) 90 257).1 : ℝ) := by
          exact_mod_cast c1
      _ ≤ _ := s1
      _ = _ := key
  · calc _ = _ := key.symm
      _ ≤ ((seriesNN false 128 (256 + 128) 90 257).2 : ℝ) := s2
      _ ≤ _ := by exact_mod_cast c2

theorem arctan_half_add_third : arctan (1 / 2) + arctan (1 / 3) = π / 4 := by
  rw [arctan_add (by norm_num), ← arctan_one]
  norm_num

theorem quarterPi_bounds :
    (quarterPiCert.1 : ℝ) ≤ 2 ^ 256 * (π / 4) ∧ 2 ^ 256 * (π / 4) ≤ (quarterPiCert.2 : ℝ) := by
  obtain ⟨s1, s2⟩ := seriesNN_spec true (a := 1) (b := 2) (by omega) 130 256
  obtain ⟨t1, t2⟩ := seriesNN_spec true (a := 1) (b := 3) (by omega) 90 256
  simp only [serF, ↓reduceIte, Nat.cast_one, Nat.cast_ofNat] at s1 s2 t1 t2
  rw [← arctan_half_add_third]
  simp only [quarterPiCert, Nat.cast_add]
  constructor <;> nlinarith

theorem arctan_table_reflect {j : ℕ} (hj : j ≤ 128) :
    arctan (j / 128) = π / 4 - arctan (((128 - j : ℕ) : ℝ) / ((128 + j : ℕ) : ℝ)) := by
  have hj' : (j : ℝ) ≤ 128 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [Nat.cast_sub hj]
  push_cast
  have hprod : (j : ℝ) / 128 * ((128 - j) / (128 + j)) < 1 := by
    rw [div_mul_div_comm, div_lt_one (by positivity)]
    nlinarith
  rw [eq_sub_iff_add_eq, arctan_add hprod, ← arctan_one]
  congr 1
  have h1 : (1 : ℝ) - j / 128 * ((128 - j) / (128 + j)) ≠ 0 := by linarith
  rw [div_eq_one_iff_eq h1]
  field_simp
  ring

theorem atanTab_bounds {j : ℕ} (hj : j ≤ 128) :
    (tabGet atanTab j : ℝ) ≤ 2 ^ 256 * arctan (j / 128) ∧
      2 ^ 256 * arctan (j / 128) ≤ (tabGet atanTab j : ℝ) + 64 := by
  obtain ⟨c1, c2⟩ := atanTab_check j (by omega)
  have hval : 0 ≤ arctan ((j : ℝ) / 128) := arctan_nonneg.mpr (by positivity)
  suffices h : ((atanTabCert j).1 : ℝ) ≤ 2 ^ 256 * arctan (j / 128) ∧
      2 ^ 256 * arctan (j / 128) ≤ ((atanTabCert j).2 : ℝ) by
    exact ⟨(by exact_mod_cast c1 : (tabGet atanTab j : ℝ) ≤ _).trans h.1,
      h.2.trans (by exact_mod_cast c2)⟩
  unfold atanTabCert
  split_ifs with h64
  · obtain ⟨s1, s2⟩ := seriesNN_spec true (a := j) (b := 128) (by omega) 130 256
    simp only [serF, ↓reduceIte, Nat.cast_ofNat] at s1 s2
    exact ⟨s1, s2⟩
  · obtain ⟨s1, s2⟩ := seriesNN_spec true (a := 128 - j) (b := 128 + j) (by omega) 90 256
    simp only [serF, ↓reduceIte] at s1 s2
    obtain ⟨q1, q2⟩ := quarterPi_bounds
    rw [arctan_table_reflect hj] at hval ⊢
    constructor
    · exact natCast_sub_le_of (by positivity) (by rw [mul_sub]; linarith)
    · exact le_trans (by rw [mul_sub]; linarith) (natCast_sub_ge _ _)

theorem halfPiT_bounds :
    (halfPiT : ℝ) ≤ 2 ^ 256 * (π / 2) ∧ 2 ^ 256 * (π / 2) ≤ (halfPiT : ℝ) + 64 := by
  obtain ⟨-, ⟨c1, c2⟩, -⟩ := consts_check
  obtain ⟨q1, q2⟩ := quarterPi_bounds
  have c1' : (halfPiT : ℝ) ≤ 2 * quarterPiCert.1 := by exact_mod_cast c1
  have c2' : 2 * (quarterPiCert.2 : ℝ) ≤ halfPiT + 64 := by exact_mod_cast c2
  constructor <;> linarith

theorem piT_bounds :
    (piT : ℝ) ≤ 2 ^ 256 * π ∧ 2 ^ 256 * π ≤ (piT : ℝ) + 64 := by
  obtain ⟨-, -, ⟨c1, c2⟩⟩ := consts_check
  obtain ⟨q1, q2⟩ := quarterPi_bounds
  have c1' : (piT : ℝ) ≤ 4 * quarterPiCert.1 := by exact_mod_cast c1
  have c2' : 4 * (quarterPiCert.2 : ℝ) ≤ piT + 64 := by exact_mod_cast c2
  constructor <;> linarith

/-! ### Signed bounds -/

/-- Signed bounds encoded with natural numbers: lower bound `lp - ln`, upper bound `hp - hn`. -/
structure SB where
  lp : ℕ
  ln : ℕ
  hp : ℕ
  hn : ℕ

/-- `s` encloses `x`. -/
def SB.Bounds (s : SB) (x : ℝ) : Prop := (s.lp : ℝ) - s.ln ≤ x ∧ x ≤ (s.hp : ℝ) - s.hn

/-! ### Logarithm -/

/-- Sum of signed bounds. -/
def SB.add (s t : SB) : SB := ⟨s.lp + t.lp, s.ln + t.ln, s.hp + t.hp, s.hn + t.hn⟩

/-- Signed bounds for `±x` from natural bounds `lo ≤ x ≤ hi`. -/
def SB.ofSign (pos : Bool) (lo hi : ℕ) : SB := bif pos then ⟨lo, 0, hi, 0⟩ else ⟨0, hi, 0, lo⟩

theorem SB.add_bounds {s t : SB} {x y : ℝ} (hs : s.Bounds x) (ht : t.Bounds y) :
    (s.add t).Bounds (x + y) := by
  obtain ⟨h1, h2⟩ := hs
  obtain ⟨h3, h4⟩ := ht
  simp only [SB.Bounds, SB.add, Nat.cast_add]
  constructor <;> linarith

theorem SB.ofSign_bounds (pos : Bool) {lo hi : ℕ} {x : ℝ} (h1 : (lo : ℝ) ≤ x)
    (h2 : x ≤ hi) : (SB.ofSign pos lo hi).Bounds (bif pos then x else -x) := by
  cases pos
  · simp only [SB.Bounds, SB.ofSign, Bool.cond_false, Nat.cast_zero]
    constructor <;> linarith
  · simp only [SB.Bounds, SB.ofSign, Bool.cond_true, Nat.cast_zero]
    constructor <;> linarith

/-- Bounds for `2^P (kn - en) log 2`. -/
def logExpPart (P kn en : ℕ) : SB :=
  let s := 256 - P
  let pos := Nat.ble en kn
  let me := bif pos then kn - en else en - kn
  SB.ofSign pos ((me * log2T) >>> s) (((me * (log2T + 64)) >>> s) + 1)

/-- Bounds for `2^P log (X/Y)` via `log (X/Y) = ± 2 artanh (|X-Y|/(X+Y))`. -/
def logSerPart (P X Y : ℕ) : SB :=
  let tpos := Nat.ble Y X
  let sr := seriesNN false (bif tpos then X - Y else Y - X) (X + Y) ((P + 10) / 18) (P + 1)
  SB.ofSign tpos sr.1 sr.2

/-- Bounds for `2^P log (1 + j/128)` from the table. -/
def logTabPart (P j : ℕ) : SB :=
  let v := tabGet logTab j
  ⟨v >>> (256 - P), 0, ((v + 64) >>> (256 - P)) + 1, 0⟩

/-- Last step of the logarithm: bounds for
`2^P ((kn - en) log 2 + log (1 + j/128) + log (X/Y))`. -/
def logAssemble (P kn en j X Y : ℕ) : SB :=
  ((logExpPart P kn en).add (logTabPart P j)).add (logSerPart P X Y)

theorem logExpPart_spec {P : ℕ} (hP : P ≤ 256) (kn en : ℕ) :
    (logExpPart P kn en).Bounds (2 ^ P * (((kn : ℝ) - en) * Real.log 2)) := by
  obtain ⟨l1, l2⟩ := log2T_bounds
  have hE : ∀ me : ℕ, (((me * log2T) >>> (256 - P) : ℕ) : ℝ) ≤ 2 ^ P * (me * Real.log 2) ∧
      2 ^ P * (me * Real.log 2) ≤ ((((me * (log2T + 64)) >>> (256 - P)) + 1 : ℕ) : ℝ) := by
    intro me
    have hme : (0 : ℝ) ≤ me := Nat.cast_nonneg me
    refine ⟨shift_lo hP ?_, shift_hi hP ?_⟩
    · push_cast
      have := mul_le_mul_of_nonneg_left l1 hme
      linarith
    · push_cast
      have := mul_le_mul_of_nonneg_left l2 hme
      linarith
  unfold logExpPart
  generalize hpos : Nat.ble en kn = pos
  cases pos
  · have hlt : kn < en := Nat.lt_of_not_le fun h => by simp [Nat.ble_eq_true_of_le h] at hpos
    obtain ⟨e1, e2⟩ := hE (en - kn)
    have := SB.ofSign_bounds false e1 e2
    simp only [Bool.cond_false] at this ⊢
    convert this using 1
    rw [Nat.cast_sub hlt.le]
    ring
  · have hle : en ≤ kn := Nat.le_of_ble_eq_true hpos
    obtain ⟨e1, e2⟩ := hE (kn - en)
    have := SB.ofSign_bounds true e1 e2
    simp only [Bool.cond_true] at this ⊢
    convert this using 1
    rw [Nat.cast_sub hle]

theorem logSerPart_spec (P : ℕ) {X Y : ℕ} (hX : 0 < X) (hY : 0 < Y) :
    (logSerPart P X Y).Bounds (2 ^ P * Real.log ((X : ℝ) / Y)) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  unfold logSerPart
  generalize htpos : Nat.ble Y X = tpos
  cases tpos
  · have hlt : X < Y := Nat.lt_of_not_le fun h => by simp [Nat.ble_eq_true_of_le h] at htpos
    obtain ⟨s1, s2⟩ := seriesNN_spec false (a := Y - X) (b := X + Y) (by omega)
      ((P + 10) / 18) (P + 1)
    have key : 2 ^ (P + 1) * serF false (((Y - X : ℕ) : ℝ) / ((X + Y : ℕ) : ℝ)) =
        -(2 ^ P * Real.log ((X : ℝ) / Y)) := by
      have := two_serF_false_eq hYr hXr
      rw [Nat.cast_sub hlt.le, Nat.cast_add, add_comm (X : ℝ)]
      rw [pow_succ, mul_assoc, this, Real.log_div hYr.ne' hXr.ne',
        Real.log_div hXr.ne' hYr.ne']
      ring
    rw [key] at s1 s2
    have := SB.ofSign_bounds false s1 s2
    simp only [Bool.cond_false, neg_neg] at this ⊢
    exact this
  · have hle : Y ≤ X := Nat.le_of_ble_eq_true htpos
    obtain ⟨s1, s2⟩ := seriesNN_spec false (a := X - Y) (b := X + Y) (by omega)
      ((P + 10) / 18) (P + 1)
    have key : 2 ^ (P + 1) * serF false (((X - Y : ℕ) : ℝ) / ((X + Y : ℕ) : ℝ)) =
        2 ^ P * Real.log ((X : ℝ) / Y) := by
      have := two_serF_false_eq hXr hYr
      rw [Nat.cast_sub hle, Nat.cast_add]
      rw [pow_succ, mul_assoc, this]
    rw [key] at s1 s2
    have := SB.ofSign_bounds true s1 s2
    simp only [Bool.cond_true] at this ⊢
    exact this

theorem logTabPart_spec {P j : ℕ} (hP : P ≤ 256) (hj : j ≤ 128) :
    (logTabPart P j).Bounds (2 ^ P * Real.log (1 + j / 128)) := by
  obtain ⟨t1, t2⟩ := shift_bounds hP (logTab_bounds hj).1 (logTab_bounds hj).2
  simp only [logTabPart, SB.Bounds, Nat.cast_zero, sub_zero]
  exact ⟨t1, t2⟩

theorem logAssemble_spec {P kn en j X Y : ℕ} (hP : P ≤ 256) (hj : j ≤ 128) (hX : 0 < X)
    (hY : 0 < Y) :
    (logAssemble P kn en j X Y).Bounds
      (2 ^ P * (((kn : ℝ) - en) * Real.log 2 + Real.log (1 + j / 128) +
        Real.log ((X : ℝ) / Y))) := by
  have h := SB.add_bounds (SB.add_bounds (logExpPart_spec hP kn en) (logTabPart_spec hP hj))
    (logSerPart_spec P hX hY)
  unfold logAssemble
  convert h using 1
  ring

/-- Bounds for `2^P ((kn - en) log 2 + log (N/D))`; accurate for `N/D ∈ [1, 2]`
(the table index is clamped, so the result is correct for all `N, D > 0`). -/
def logFinish (P kn en N D : ℕ) : SB :=
  let j := min ((256 * N - 255 * D) / (2 * D)) 128
  logAssemble P kn en j (128 * N) ((128 + j) * D)

set_option linter.style.longLine false in
/-- Packed table: bits `[4q, 4q+4)` hold `⌊log₂ q⌋` for `1 ≤ q < 256`. -/
def flog2Tab : ℕ :=
  0x7777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777777766666666666666666666666666666666666666666666666666666666666666665555555555555555555555555555555544444444444444443333333322221100

/-- One step of the binary search in `flog2`. -/
def flog2Step (k : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  bif Nat.blt p.1 (1 <<< k) then p else (p.1 >>> k, p.2 + k)

/-- `⌊log₂ q⌋` for `0 < q < 2^1024` (`Nat.log2` is not accelerated in the kernel).
Only used as a heuristic for the argument reduction: correctness never depends on it. -/
def flog2 (q : ℕ) : ℕ :=
  bif Nat.blt q 256 then (flog2Tab >>> (4 * q)) % 16
  else
    let p := flog2Step 8 (flog2Step 16 (flog2Step 32 (flog2Step 64 (flog2Step 128
      (flog2Step 256 (flog2Step 512 (q, 0)))))))
    p.2 + (flog2Tab >>> (4 * p.1)) % 16

/-- Binary normalisation: `(kn, en, N, D)` with `N = n 2^en`, `D = d 2^kn` and
(for `n, d > 0`) `N/D ∈ [1, 2]`. -/
def logReduce (n d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  bif Nat.ble d n then
    let e := flog2 (n / d)
    (e, 0, n, d <<< e)
  else
    let f := flog2 (d / n) + 1
    (0, f, n <<< f, d)

/-- Bounds for `2^P log (n/d)` (valid for `0 < n`, `0 < d`, `P ≤ 256`). -/
def logCore (n d P : ℕ) : SB :=
  let r := logReduce n d
  logFinish P r.1 r.2.1 r.2.2.1 r.2.2.2

theorem logFinish_spec {P kn en N D : ℕ} (hP : P ≤ 256) (hN : 0 < N) (hD : 0 < D) :
    (logFinish P kn en N D).Bounds
      (2 ^ P * (((kn : ℝ) - en) * Real.log 2 + Real.log ((N : ℝ) / D))) := by
  have hj : min ((256 * N - 255 * D) / (2 * D)) 128 ≤ 128 := min_le_right _ _
  set j := min ((256 * N - 255 * D) / (2 * D)) 128 with hjdef
  have h := @logAssemble_spec P kn en j (128 * N) ((128 + j) * D) hP hj
    (Nat.mul_pos (by norm_num) hN) (Nat.mul_pos (by positivity) hD)
  have hid : Real.log (1 + j / 128) + Real.log (((128 * N : ℕ) : ℝ) / ((128 + j) * D : ℕ)) =
      Real.log ((N : ℝ) / D) := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    push_cast
    field_simp
  unfold logFinish
  rw [← hjdef]
  convert h using 2
  rw [add_assoc, hid]

theorem logReduce_spec (n d : ℕ) :
    (logReduce n d).2.2.1 = n * 2 ^ (logReduce n d).2.1 ∧
      (logReduce n d).2.2.2 = d * 2 ^ (logReduce n d).1 := by
  unfold logReduce
  cases Nat.ble d n
  · exact ⟨Nat.shiftLeft_eq _ _, by simp⟩
  · exact ⟨by simp, Nat.shiftLeft_eq _ _⟩

theorem logCore_spec {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {P : ℕ} (hP : P ≤ 256) :
    (logCore n d P).Bounds (2 ^ P * Real.log ((n : ℝ) / d)) := by
  obtain ⟨hN, hD⟩ := logReduce_spec n d
  unfold logCore
  generalize logReduce n d = r at *
  obtain ⟨kn, en, N, D⟩ := r
  simp only at hN hD ⊢
  have h := logFinish_spec (kn := kn) (en := en) (N := N) (D := D) hP
    (by rw [hN]; positivity) (by rw [hD]; positivity)
  convert h using 2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have : ((N : ℝ) / D) = (n / d) * (2 ^ en / 2 ^ kn) := by
    rw [hN, hD]; push_cast; field_simp
  have h2 : Real.log ((2 : ℝ) ^ en / 2 ^ kn) = ((en : ℝ) - kn) * Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  rw [this, Real.log_mul (by positivity) (by positivity), h2]
  ring

/-! ### Arctangent -/

/-- Bounds for `2^P arctan (j/128)` from the table. -/
def atanTabPart (P j : ℕ) : ℕ × ℕ :=
  let v := tabGet atanTab j
  (v >>> (256 - P), ((v + 64) >>> (256 - P)) + 1)

/-- Bounds for `2^P (arctan (j/128) ± arctan (a/b))` (sign `+` iff `pos`), truncated at `0`. -/
def atanCombine (P j a b : ℕ) (pos : Bool) : ℕ × ℕ :=
  let sr := seriesNN true a b ((P + 8) / 16) P
  let t := atanTabPart P j
  bif pos then (t.1 + sr.1, t.2 + sr.2) else (t.1 - sr.2, t.2 - sr.1)

/-- Bounds for `2^P arctan (p/q)`, valid for `p ≤ q`, `0 < q`, `P ≤ 256`. -/
def atan01 (p q P : ℕ) : ℕ × ℕ :=
  let j := (256 * p + q) / (2 * q)
  let X := 128 * p
  let Y := j * q
  let b := 128 * q + j * p
  let pos := Nat.ble Y X
  let a := bif pos then X - Y else Y - X
  bif Nat.blt a b then atanCombine P j a b pos else (0, 2 ^ P)

/-- The angle of the vector `(q, p)`, `p q ≥ 0`: `arctan (p/q)`, or `π/2` if `q = 0`. -/
noncomputable def theta (p q : ℕ) : ℝ := if q = 0 then π / 2 else arctan ((p : ℝ) / q)

/-- Bounds for `2^P theta p q`, valid for `(p, q) ≠ (0, 0)`, `P ≤ 256`. -/
def atanNN (p q P : ℕ) : ℕ × ℕ :=
  bif Nat.ble p q then atan01 p q P
  else
    let r := atan01 q p P
    ((halfPiT >>> (256 - P)) - r.2, (((halfPiT + 64) >>> (256 - P)) + 1) - r.1)

theorem atanTabPart_spec {P j : ℕ} (hP : P ≤ 256) (hj : j ≤ 128) :
    ((atanTabPart P j).1 : ℝ) ≤ 2 ^ P * arctan (j / 128) ∧
      2 ^ P * arctan (j / 128) ≤ ((atanTabPart P j).2 : ℝ) :=
  shift_bounds hP (atanTab_bounds hj).1 (atanTab_bounds hj).2

theorem atanCombine_spec {P j a b : ℕ} (pos : Bool) (hP : P ≤ 256) (hj : j ≤ 128) (hab : a < b)
    (hval : 0 ≤ arctan (j / 128) + (bif pos then 1 else -1) * arctan ((a : ℝ) / b)) :
    ((atanCombine P j a b pos).1 : ℝ) ≤
        2 ^ P * (arctan (j / 128) + (bif pos then 1 else -1) * arctan ((a : ℝ) / b)) ∧
      2 ^ P * (arctan (j / 128) + (bif pos then 1 else -1) * arctan ((a : ℝ) / b)) ≤
        ((atanCombine P j a b pos).2 : ℝ) := by
  obtain ⟨s1, s2⟩ := seriesNN_spec true hab ((P + 8) / 16) P
  simp only [serF, ↓reduceIte] at s1 s2
  obtain ⟨t1, t2⟩ := atanTabPart_spec hP hj
  unfold atanCombine
  generalize seriesNN true a b ((P + 8) / 16) P = sr at s1 s2 ⊢
  generalize atanTabPart P j = t at t1 t2 ⊢
  have hP0 : (0 : ℝ) < 2 ^ P := by positivity
  cases pos
  · simp only [Bool.cond_false] at hval ⊢
    constructor
    · exact natCast_sub_le_of (by positivity) (by nlinarith)
    · exact le_trans (by nlinarith) (natCast_sub_ge _ _)
  · simp only [Bool.cond_true] at hval ⊢
    push_cast
    constructor <;> nlinarith

/-- The addition formula used for the argument reduction. -/
theorem arctan_reduce {p q j X Y b : ℕ} (hq : 0 < q) (hj : j ≤ 128) (hX : X = 128 * p)
    (hY : Y = j * q) (hb : b = 128 * q + j * p) {t : ℝ} (ht : t = ((X : ℝ) - Y) / b)
    (hlt : |t| < 1) :
    arctan ((p : ℝ) / q) = arctan (j / 128) + arctan t := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hbr : (0 : ℝ) < b := by
    have : 0 < b := by rw [hb]; positivity
    exact_mod_cast this
  have hx0 : (0 : ℝ) ≤ j / 128 := by positivity
  have hx1 : (j : ℝ) / 128 ≤ 1 := by
    rw [div_le_one (by norm_num)]; exact_mod_cast hj
  have hprod : (j : ℝ) / 128 * t < 1 := by
    have h1 : (j : ℝ) / 128 * t ≤ (j : ℝ) / 128 * |t| :=
      mul_le_mul_of_nonneg_left (le_abs_self t) hx0
    have h2 : (j : ℝ) / 128 * |t| ≤ |t| := mul_le_of_le_one_left (abs_nonneg t) hx1
    linarith
  rw [arctan_add hprod]
  congr 1
  have hne : (1 : ℝ) - j / 128 * t ≠ 0 := by linarith
  rw [eq_div_iff hne]
  subst ht hX hY hb
  have hb' : (128 : ℝ) * q + j * p ≠ 0 := by push_cast at hbr; linarith
  push_cast
  field_simp
  ring

theorem atan01_spec {p q P : ℕ} (hpq : p ≤ q) (hq : 0 < q) (hP : P ≤ 256) :
    ((atan01 p q P).1 : ℝ) ≤ 2 ^ P * arctan ((p : ℝ) / q) ∧
      2 ^ P * arctan ((p : ℝ) / q) ≤ ((atan01 p q P).2 : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hval : 0 ≤ arctan ((p : ℝ) / q) := arctan_nonneg.mpr (by positivity)
  have hj : (256 * p + q) / (2 * q) ≤ 128 :=
    Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
  dsimp only [atan01]
  generalize (256 * p + q) / (2 * q) = j at hj ⊢
  generalize hpos : Nat.ble (j * q) (128 * p) = pos
  generalize ha : (bif pos then 128 * p - j * q else j * q - 128 * p) = a
  cases hab : Nat.blt a (128 * q + j * p)
  · -- fallback: `0 ≤ arctan (p/q) ≤ p/q ≤ 1`
    simp only [Bool.cond_false, Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat]
    have hP0 : (0 : ℝ) < 2 ^ P := by positivity
    refine ⟨mul_nonneg hP0.le hval, ?_⟩
    have h1 : arctan ((p : ℝ) / q) ≤ (p : ℝ) / q := arctan_le_self (by positivity)
    have h2 : (p : ℝ) / q ≤ 1 := by
      rw [div_le_one hqr]; exact_mod_cast hpq
    exact mul_le_of_le_one_right hP0.le (h1.trans h2)
  · simp only [Bool.cond_true]
    have hab' : a < 128 * q + j * p := by simpa using hab
    -- the reduced argument
    have hred : arctan ((p : ℝ) / q) =
        arctan (j / 128) + (bif pos then 1 else -1) * arctan ((a : ℝ) / (128 * q + j * p : ℕ)) := by
      have ht : |((128 * p : ℕ) : ℝ) - (j * q : ℕ)| / ((128 * q + j * p : ℕ) : ℝ) < 1 := by
        have hb0 : (0 : ℝ) < ((128 * q + j * p : ℕ) : ℝ) := by
          have : 0 < 128 * q + j * p := by positivity
          exact_mod_cast this
        rw [div_lt_one hb0]
        cases pos
        · have hlt : 128 * p < j * q :=
            Nat.lt_of_not_le fun h => by simp [Nat.ble_eq_true_of_le h] at hpos
          simp only [Bool.cond_false] at ha
          rw [abs_sub_comm, abs_of_nonneg (by exact_mod_cast (sub_nonneg.mpr
            (by exact_mod_cast hlt.le : ((128 * p : ℕ) : ℝ) ≤ (j * q : ℕ))))]
          rw [← Nat.cast_sub hlt.le, ha]
          exact_mod_cast hab'
        · have hle : j * q ≤ 128 * p := Nat.le_of_ble_eq_true hpos
          simp only [Bool.cond_true] at ha
          rw [abs_of_nonneg (by exact_mod_cast (sub_nonneg.mpr
            (by exact_mod_cast hle : ((j * q : ℕ) : ℝ) ≤ (128 * p : ℕ))))]
          rw [← Nat.cast_sub hle, ha]
          exact_mod_cast hab'
      have hb0 : (0 : ℝ) < ((128 * q + j * p : ℕ) : ℝ) := by
        have : 0 < 128 * q + j * p := by positivity
        exact_mod_cast this
      have ht' : |(((128 * p : ℕ) : ℝ) - ((j * q : ℕ) : ℝ)) / ((128 * q + j * p : ℕ) : ℝ)| < 1 := by
        rw [abs_div, abs_of_pos hb0]; exact ht
      rw [arctan_reduce hq hj rfl rfl rfl rfl ht']
      congr 1
      cases pos
      · have hlt : 128 * p < j * q :=
          Nat.lt_of_not_le fun h => by simp [Nat.ble_eq_true_of_le h] at hpos
        simp only [Bool.cond_false] at ha ⊢
        rw [← ha, Nat.cast_sub hlt.le, neg_one_mul, ← arctan_neg]
        congr 1
        ring
      · have hle : j * q ≤ 128 * p := Nat.le_of_ble_eq_true hpos
        simp only [Bool.cond_true] at ha ⊢
        rw [← ha, Nat.cast_sub hle, one_mul]
    rw [hred] at hval ⊢
    exact atanCombine_spec pos hP hj hab' hval

theorem theta_nonneg (p q : ℕ) : 0 ≤ theta p q := by
  unfold theta
  split_ifs
  · positivity
  · exact arctan_nonneg.mpr (by positivity)

theorem theta_of_lt {p q : ℕ} (h : q < p) : theta p q = π / 2 - arctan ((q : ℝ) / p) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_le q).trans_lt h
  unfold theta
  split_ifs with hq
  · simp [hq]
  · have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    rw [← arctan_inv_of_pos (by positivity), inv_div]

theorem atanNN_spec {p q P : ℕ} (hpq : 0 < p ∨ 0 < q) (hP : P ≤ 256) :
    ((atanNN p q P).1 : ℝ) ≤ 2 ^ P * theta p q ∧
      2 ^ P * theta p q ≤ ((atanNN p q P).2 : ℝ) := by
  unfold atanNN
  cases hle : Nat.ble p q
  · have hlt : q < p := Nat.lt_of_not_le fun h => by simp [Nat.ble_eq_true_of_le h] at hle
    simp only [Bool.cond_false]
    obtain ⟨r1, r2⟩ := atan01_spec hlt.le (by omega) hP
    obtain ⟨h1, h2⟩ := shift_bounds hP halfPiT_bounds.1 halfPiT_bounds.2
    have hth := theta_nonneg p q
    rw [theta_of_lt hlt] at hth ⊢
    generalize atan01 q p P = r at r1 r2
    constructor
    · exact natCast_sub_le_of (by positivity) (by rw [mul_sub]; linarith)
    · exact le_trans (by rw [mul_sub]; linarith) (natCast_sub_ge _ _)
  · have hle' : p ≤ q := Nat.le_of_ble_eq_true hle
    have hq : 0 < q := by omega
    simp only [Bool.cond_true]
    have : theta p q = arctan ((p : ℝ) / q) := by simp [theta, hq.ne']
    rw [this]
    exact atan01_spec hle' hq hP

/-! ### Output as dyadic rationals -/

/-- The dyadic rational `± m / 2^P` in lowest terms (computed with `ℕ` arithmetic only). -/
def dyadic (neg : Bool) (m P : ℕ) : ℚ :=
  let g := Nat.gcd m (2 ^ P)
  { num := bif neg then -((m / g : ℕ) : ℤ) else ((m / g : ℕ) : ℤ)
    den := 2 ^ P / g
    den_nz := (Nat.div_pos (Nat.gcd_le_right _ (Nat.two_pow_pos P))
      (Nat.gcd_pos_of_pos_right _ (Nat.two_pow_pos P))).ne'
    reduced := by
      have h : (bif neg then -((m / g : ℕ) : ℤ) else ((m / g : ℕ) : ℤ)).natAbs = m / g := by
        cases neg <;> simp only [Bool.cond_false, Bool.cond_true, Int.natAbs_neg,
          Int.natAbs_natCast]
      rw [h]
      exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ (Nat.two_pow_pos P)) }

theorem dyadic_cast (neg : Bool) (m P : ℕ) :
    ((dyadic neg m P : ℚ) : ℝ) = (bif neg then -(m : ℝ) else (m : ℝ)) / 2 ^ P := by
  rw [Rat.cast_def]
  have hg : 0 < Nat.gcd m (2 ^ P) := Nat.gcd_pos_of_pos_right _ (Nat.two_pow_pos P)
  have hgr : ((Nat.gcd m (2 ^ P) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 : ((m / Nat.gcd m (2 ^ P) : ℕ) : ℝ) = m / Nat.gcd m (2 ^ P) :=
    Nat.cast_div (Nat.gcd_dvd_left _ _) hgr
  have h2 : ((2 ^ P / Nat.gcd m (2 ^ P) : ℕ) : ℝ) = 2 ^ P / Nat.gcd m (2 ^ P) := by
    rw [Nat.cast_div (Nat.gcd_dvd_right _ _) hgr]
    push_cast
    ring
  have h2' : (2 : ℝ) ^ P ≠ 0 := by positivity
  cases neg
  · simp only [dyadic, Bool.cond_false, Int.cast_natCast]
    rw [h1, h2]
    field_simp
  · simp only [dyadic, Bool.cond_true, Int.cast_neg, Int.cast_natCast]
    rw [h1, h2]
    field_simp

/-- The dyadic rational `(p - n) / 2^P`. -/
def subQ (p n P : ℕ) : ℚ := bif Nat.ble n p then dyadic false (p - n) P else dyadic true (n - p) P

theorem subQ_cast (p n P : ℕ) : ((subQ p n P : ℚ) : ℝ) = ((p : ℝ) - n) / 2 ^ P := by
  unfold subQ
  cases h : Nat.ble n p
  · have hlt : p < n := Nat.lt_of_not_le fun h' => by simp [Nat.ble_eq_true_of_le h'] at h
    simp only [Bool.cond_false, dyadic_cast, Bool.cond_true]
    rw [Nat.cast_sub hlt.le]
    ring
  · have hle : n ≤ p := Nat.le_of_ble_eq_true h
    simp only [Bool.cond_true, dyadic_cast, Bool.cond_false]
    rw [Nat.cast_sub hle]

theorem SB.lo_le {s : SB} {x : ℝ} {P : ℕ} (h : s.Bounds (2 ^ P * x)) :
    ((subQ s.lp s.ln P : ℚ) : ℝ) ≤ x := by
  rw [subQ_cast, div_le_iff₀ (by positivity)]
  linarith [h.1]

theorem SB.le_hi {s : SB} {x : ℝ} {P : ℕ} (h : s.Bounds (2 ^ P * x)) :
    x ≤ ((subQ s.hp s.hn P : ℚ) : ℝ) := by
  rw [subQ_cast, le_div_iff₀ (by positivity)]
  linarith [h.2]

/-! ### Public API -/

/-- Working precision: tables are accurate to `2^-256`, so we cap the precision at `240`. -/
def workPrec (prec : ℕ) : ℕ := min prec 240

theorem workPrec_le (prec : ℕ) : workPrec prec ≤ 256 := (min_le_right _ _).trans (by norm_num)

theorem rat_cast_eq_natAbs {x : ℚ} (hx : 0 ≤ x) : (x : ℝ) = (x.num.natAbs : ℝ) / x.den := by
  rw [Rat.cast_def, Nat.cast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hx)]

/-- Lower bound for `Real.log x` (meaningful for `0 < x`), with denominator `2^min prec 240`. -/
def logLo (x : ℚ) (prec : ℕ) : ℚ :=
  let P := workPrec prec
  let r := logCore x.num.natAbs x.den P
  subQ r.lp r.ln P

/-- Upper bound for `Real.log x` (meaningful for `0 < x`), with denominator `2^min prec 240`. -/
def logHi (x : ℚ) (prec : ℕ) : ℚ :=
  let P := workPrec prec
  let r := logCore x.num.natAbs x.den P
  subQ r.hp r.hn P

theorem logCore_rat {x : ℚ} (hx : 0 < x) (P : ℕ) (hP : P ≤ 256) :
    (logCore x.num.natAbs x.den P).Bounds (2 ^ P * Real.log x) := by
  rw [rat_cast_eq_natAbs hx.le]
  exact logCore_spec (Int.natAbs_pos.mpr (Rat.num_pos.mpr hx).ne') x.den_pos hP

theorem logLo_le {x : ℚ} (hx : 0 < x) (prec : ℕ) :
    ((logLo x prec : ℚ) : ℝ) ≤ Real.log x :=
  SB.lo_le (logCore_rat hx _ (workPrec_le prec))

theorem le_logHi {x : ℚ} (hx : 0 < x) (prec : ℕ) :
    Real.log x ≤ ((logHi x prec : ℚ) : ℝ) :=
  SB.le_hi (logCore_rat hx _ (workPrec_le prec))

/-- Lower bound for `Real.arctan x`, with denominator `2^min prec 240`. -/
def atanLo (x : ℚ) (prec : ℕ) : ℚ :=
  let P := workPrec prec
  match x.num with
  | .ofNat p => dyadic false (atanNN p x.den P).1 P
  | .negSucc p => dyadic true (atanNN (p + 1) x.den P).2 P

/-- Upper bound for `Real.arctan x`, with denominator `2^min prec 240`. -/
def atanHi (x : ℚ) (prec : ℕ) : ℚ :=
  let P := workPrec prec
  match x.num with
  | .ofNat p => dyadic false (atanNN p x.den P).2 P
  | .negSucc p => dyadic true (atanNN (p + 1) x.den P).1 P

theorem theta_of_pos_den (p : ℕ) {q : ℕ} (hq : 0 < q) : theta p q = arctan ((p : ℝ) / q) := by
  simp [theta, hq.ne']

theorem atanLo_le (x : ℚ) (prec : ℕ) : ((atanLo x prec : ℚ) : ℝ) ≤ Real.arctan x := by
  have hP := workPrec_le prec
  have hd : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
  unfold atanLo
  rw [Rat.cast_def x]
  cases hnum : x.num with
  | ofNat p =>
    obtain ⟨h1, -⟩ := atanNN_spec (p := p) (Or.inr x.den_pos) hP
    rw [theta_of_pos_den p x.den_pos] at h1
    simp only [dyadic_cast, Bool.cond_false, Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [div_le_iff₀ (by positivity)]
    linarith
  | negSucc p =>
    obtain ⟨-, h2⟩ := atanNN_spec (p := p + 1) (Or.inr x.den_pos) hP
    rw [theta_of_pos_den (p + 1) x.den_pos] at h2
    simp only [dyadic_cast, Bool.cond_true, Int.cast_negSucc]
    rw [neg_div (x.den : ℝ), arctan_neg, div_le_iff₀ (by positivity)]
    push_cast at h2 ⊢
    linarith

theorem le_atanHi (x : ℚ) (prec : ℕ) : Real.arctan x ≤ ((atanHi x prec : ℚ) : ℝ) := by
  have hP := workPrec_le prec
  have hd : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
  unfold atanHi
  rw [Rat.cast_def x]
  cases hnum : x.num with
  | ofNat p =>
    obtain ⟨-, h2⟩ := atanNN_spec (p := p) (Or.inr x.den_pos) hP
    rw [theta_of_pos_den p x.den_pos] at h2
    simp only [dyadic_cast, Bool.cond_false, Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [le_div_iff₀ (by positivity)]
    linarith
  | negSucc p =>
    obtain ⟨h1, -⟩ := atanNN_spec (p := p + 1) (Or.inr x.den_pos) hP
    rw [theta_of_pos_den (p + 1) x.den_pos] at h1
    simp only [dyadic_cast, Bool.cond_true, Int.cast_negSucc]
    rw [neg_div (x.den : ℝ), arctan_neg, le_div_iff₀ (by positivity)]
    push_cast at h1 ⊢
    linarith

/-- Lower bound for `π` (`≈ 38` correct digits). -/
def piLo : ℚ := dyadic false ((piT >>> 128) - 1) 128

/-- Upper bound for `π` (`≈ 38` correct digits). -/
def piHi : ℚ := dyadic false (((piT + 64) >>> 128) + 2) 128

theorem piLo_lt_pi : (piLo : ℝ) < Real.pi := by
  have h := shift_lo (P := 128) (by norm_num) piT_bounds.1
  norm_num only at h
  unfold piLo
  rw [dyadic_cast, Bool.cond_false, div_lt_iff₀ (by positivity)]
  generalize piT >>> 128 = m at h
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.zero_sub, Nat.cast_zero]
    positivity
  · rw [Nat.cast_sub hm, Nat.cast_one]
    linarith

theorem pi_lt_piHi : Real.pi < (piHi : ℝ) := by
  have h := shift_hi (P := 128) (by norm_num) (w := piT + 64) (by push_cast; exact piT_bounds.2)
  norm_num only at h
  unfold piHi
  rw [dyadic_cast, Bool.cond_false, lt_div_iff₀ (by positivity)]
  push_cast at h ⊢
  linarith

end OddZeta.Num
