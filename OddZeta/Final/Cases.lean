import OddZeta.Final.Main
import OddZeta.Cert.Saddle

/-!
# Cases (A) and (B)

Instantiation of `Params.exists_irrational_zetaR` with the certified data of cases (A) and (B).
-/

namespace OddZeta

/-- **Theorem 1.1** (for the real series). -/
theorem caseA_exists_irrational : ∃ s ∈ caseA.oddRange, Irrational (zetaR s) := by
  sorry

/-- **Theorem 1.2** (for the real series). -/
theorem caseB_exists_irrational : ∃ s ∈ caseB.oddRange, Irrational (zetaR s) := by
  sorry

/-- `ζ(s)` for a natural `s ≥ 2` is the real number `zetaR s`. -/
theorem riemannZeta_natCast_eq_zetaR {s : ℕ} (hs : 2 ≤ s) :
    riemannZeta (s : ℂ) = (zetaR s : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; exact_mod_cast hs), zetaR,
    Complex.ofReal_tsum]
  congr 1
  ext m
  push_cast
  rw [Complex.cpow_natCast]

theorem riemannZeta_ne_ratCast_of_irrational {s : ℕ} (hs : 2 ≤ s) (h : Irrational (zetaR s))
    (q : ℚ) : riemannZeta (s : ℂ) ≠ (q : ℂ) := by
  intro hq
  rw [riemannZeta_natCast_eq_zetaR hs] at hq
  apply h
  refine ⟨q, ?_⟩
  exact_mod_cast hq.symm

end OddZeta
