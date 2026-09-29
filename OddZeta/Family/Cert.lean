import OddZeta.Family.CertSmall
import OddZeta.Family.CertLarge

/-!
# The saddle-point certificates for the family `η^(r)`, for every odd `r ≥ 3`

Two regimes: `3 ≤ r ≤ 299` (`CertSmall`, one certificate per `r`) and `r ≥ 301` (`CertLarge`,
uniform asymptotic bounds).
-/

namespace OddZeta

theorem famCert (r : ℕ) (hr : Odd r) (h3 : 3 ≤ r) : FamCert r := by
  rcases le_or_gt r 299 with h | h
  · exact famCert_small r hr h3 h
  · exact famCert_large r hr (by obtain ⟨k, rfl⟩ := hr; omega)

end OddZeta
