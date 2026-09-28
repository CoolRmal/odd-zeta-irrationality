import OddZeta

/-!
# Challenge: irrationality of odd zeta values via Zudilin's higher-derivative forms

This file contains the statements of record. They are the two main theorems of the note
*Irrationality of at least one of ζ(7), …, ζ(21) and of at least one of ζ(9), …, ζ(33):
a complete proof via Zudilin's higher-derivative construction* (September 2026):

* **Theorem 1.1** (`r = 5`): at least one of the eight numbers `ζ(7), ζ(9), …, ζ(21)` is
  irrational;
* **Theorem 1.2** (`r = 7`): at least one of the thirteen numbers `ζ(9), ζ(11), …, ζ(33)` is
  irrational.

Each theorem is stated twice: once for Mathlib's `riemannZeta` (a complex number that is not
the image of any rational number), and once for the real series `∑_{n ≥ 1} n⁻ˢ` (via
`Irrational`). The proofs are in `Solution.lean`; `lake comparator` checks that they prove
exactly these statements using only the standard axioms.
-/

namespace OddZeta

/-- **Theorem 1.1.** At least one of the eight numbers `ζ(7), ζ(9), …, ζ(21)` is irrational:
for some `s ∈ {7, 9, …, 21}`, the value `ζ(s)` of the Riemann zeta function is not a rational
number. -/
theorem exists_zeta_ne_ratCast_of_seven_le_of_le_twentyone :
    ∃ s ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), ∀ q : ℚ, riemannZeta s ≠ q := by
  sorry

/-- **Theorem 1.2.** At least one of the thirteen numbers `ζ(9), ζ(11), …, ζ(33)` is
irrational: for some `s ∈ {9, 11, …, 33}`, the value `ζ(s)` of the Riemann zeta function is not
a rational number. -/
theorem exists_zeta_ne_ratCast_of_nine_le_of_le_thirtythree :
    ∃ s ∈ ({9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33} : Finset ℕ),
      ∀ q : ℚ, riemannZeta s ≠ q := by
  sorry

/-- **Theorem 1.1**, real form: for some `s ∈ {7, 9, …, 21}` the sum `∑_{n ≥ 1} 1 / nˢ` is
irrational. -/
theorem exists_irrational_tsum_of_seven_le_of_le_twentyone :
    ∃ s ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ),
      Irrational (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s) := by
  sorry

/-- **Theorem 1.2**, real form: for some `s ∈ {9, 11, …, 33}` the sum `∑_{n ≥ 1} 1 / nˢ` is
irrational. -/
theorem exists_irrational_tsum_of_nine_le_of_le_thirtythree :
    ∃ s ∈ ({9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33} : Finset ℕ),
      Irrational (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s) := by
  sorry

end OddZeta
