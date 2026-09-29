import OddZeta.Family.CertSmall
import OddZeta.Family.CertMid
import OddZeta.Family.CertLarge

/-!
# The saddle-point certificates for the family `η^(r)`, for every odd `r ≥ 3`

Three regimes: `3 ≤ r ≤ 49` (`CertSmall`), `51 ≤ r ≤ 299` (`CertMid`), `r ≥ 301` (`CertLarge`).
-/

namespace OddZeta

theorem famCert (r : ℕ) (hr : Odd r) (h3 : 3 ≤ r) : FamCert r := by
  rcases le_or_gt r 49 with h | h
  · exact famCert_small r hr h3 h
  rcases le_or_gt r 299 with h' | h'
  · exact famCert_mid r hr (by obtain ⟨k, rfl⟩ := hr; omega) h'
  · exact famCert_large r hr (by obtain ⟨k, rfl⟩ := hr; omega)

end OddZeta
