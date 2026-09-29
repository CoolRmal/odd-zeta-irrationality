import OddZeta.Analytic.Saddle2
import OddZeta.Family.Phase

/-!
# The saddle-point certificates for the family `η^(r)`, for every odd `r ≥ 3`

`fam_cert r`: a path `L_r` through the saddle point with `PathCert2`, `H_d < -(214.8 r - 3)` and
`α ∉ πℤ`. Three regimes:
* `3 ≤ r ≤ 49`: one kernel-checked certificate per `r` (paths checked segment by segment);
* `51 ≤ r ≤ 299`: the fixed regions of Section 8.4 of the note (r-independent bounds for `Re g` and
  `Re e + 2π Im u`) and per-`r` scalar checks (Section 8.6);
* `r ≥ 301`: the explicit asymptotic bounds of Section 8.7, uniformly in `t = 1/r`.
-/

namespace OddZeta

/-- The certificate statement for the family. -/
def FamCert (r : ℕ) : Prop :=
  ∃ D : PathData2, ∃ b c K c₀ ε₀ : ℝ, (fam r).PathCert2 D b c K c₀ ε₀ ∧
    ((fam r).Fd D.u).re < -(214.8 * r - 3) ∧ ∀ m : ℤ, ((fam r).Fd D.u).im ≠ m * Real.pi

theorem famCert_small (r : ℕ) (hr : Odd r) (h3 : 3 ≤ r) (h49 : r ≤ 49) : FamCert r := by
  sorry

theorem famCert_mid (r : ℕ) (hr : Odd r) (h51 : 51 ≤ r) (h299 : r ≤ 299) : FamCert r := by
  sorry

theorem famCert_large (r : ℕ) (hr : Odd r) (h301 : 301 ≤ r) : FamCert r := by
  sorry

theorem famCert (r : ℕ) (hr : Odd r) (h3 : 3 ≤ r) : FamCert r := by
  rcases le_or_gt r 49 with h | h
  · exact famCert_small r hr h3 h
  rcases le_or_gt r 299 with h' | h'
  · exact famCert_mid r hr (by obtain ⟨k, rfl⟩ := hr; omega) h'
  · exact famCert_large r hr (by obtain ⟨k, rfl⟩ := hr; omega)

end OddZeta
