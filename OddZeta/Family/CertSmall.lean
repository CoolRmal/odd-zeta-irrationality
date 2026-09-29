import OddZeta.Family.CertDef
import OddZeta.Family.Regions

/-!
# Certificates for the family: `3 ≤ r ≤ 299`, one kernel-checked certificate per `r`

For each odd `r ≤ 299`: the saddle point `u*` (contraction mapping around a rational `ũ`), the path
`-i∞ → P_R = 20 - i/4 → bot → σ → top → P_L → -2` (`P_L` on `[top, -2]`); the ray is covered for all
`r` by `regRay_bound`, the three segments by grid checks (Lemma 4.8 of the note).
-/

namespace OddZeta

theorem famCert_small (r : ℕ) (hr : Odd r) (h3 : 3 ≤ r) (h299 : r ≤ 299) : FamCert r := by
  sorry

end OddZeta
