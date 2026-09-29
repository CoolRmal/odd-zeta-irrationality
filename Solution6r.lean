import OddZeta.Final.Family

/-!
# Challenge: one of `ζ(r+2), ζ(r+4), …, ζ(6r-1)` is irrational, for every odd `r ≥ 3`

Theorem 8.1 of the note *One of ζ(r+2), …, ζ(6r−1) is irrational for every odd r, and complete
proofs for ζ(7), …, ζ(21) and ζ(9), …, ζ(33), via Zudilin's higher-derivative construction*
(September 29, 2026). The list `ζ(r+2), ζ(r+4), …, ζ(6r-1)` consists of the `(5r-1)/2` values of
the Riemann zeta function at the odd integers `s` with `r + 2 ≤ s ≤ 6r - 1`.

The theorem is stated for Mathlib's `riemannZeta` (a value not equal to any rational number) and
for the real series `∑_{n ≥ 1} 1/nˢ` (via `Irrational`). The proofs are in `Solution6r.lean`.
-/

namespace OddZeta

/-- **Theorem 8.1.** For every odd integer `r ≥ 3`, at least one of the numbers
`ζ(r+2), ζ(r+4), …, ζ(6r-1)` is irrational. -/
theorem exists_zeta_ne_ratCast_of_odd (r : ℕ) (hr : Odd r) (h3 : 3 ≤ r) :
    ∃ s ∈ (Finset.Icc (r + 2) (6 * r - 1)).filter Odd, ∀ q : ℚ, riemannZeta s ≠ q := by
  obtain ⟨s, hs, hirr⟩ := fam_exists_irrational r hr h3
  refine ⟨s, hs, riemannZeta_ne_ratCast_of_irrational ?_ hirr⟩
  simp only [Finset.mem_filter, Finset.mem_Icc] at hs
  omega

/-- **Theorem 8.1**, real form: for every odd integer `r ≥ 3`, for some odd `s` with
`r + 2 ≤ s ≤ 6r - 1` the sum `∑_{n ≥ 1} 1 / nˢ` is irrational. -/
theorem exists_irrational_tsum_of_odd (r : ℕ) (hr : Odd r) (h3 : 3 ≤ r) :
    ∃ s ∈ (Finset.Icc (r + 2) (6 * r - 1)).filter Odd,
      Irrational (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s) := by
  exact fam_exists_irrational r hr h3

end OddZeta
