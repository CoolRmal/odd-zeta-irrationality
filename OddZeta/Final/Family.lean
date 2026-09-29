import OddZeta.Final.Main2
import OddZeta.Family.Arith
import OddZeta.Family.Cert
import OddZeta.Final.Cases

/-!
# Theorem 8.1: one of `ζ(r+2), …, ζ(6r-1)` is irrational, for every odd `r ≥ 3`
-/

namespace OddZeta

theorem fam_exists_irrational (r : ℕ) (hr : Odd r) (h3 : 3 ≤ r) :
    ∃ s ∈ (Finset.Icc (r + 2) (6 * r - 1)).filter Odd, Irrational (zetaR s) := by
  obtain ⟨D, b, c, K, c₀, ε₀, hD, hH, hα⟩ := famCert r hr h3
  obtain ⟨X, vals, φ', hX0, hX1, hXm, hφ0, hφ, hC, hI⟩ := fam_arith r (by omega)
  rw [← Fam.oddRange_eq]
  exact Params.exists_irrational_zetaR2 (Fam.valid hr h3) Fam.ps_sorted X vals hX0 hX1 hXm φ'
    hφ0 hφ 20 _ hI hD (by linarith) hα

end OddZeta
