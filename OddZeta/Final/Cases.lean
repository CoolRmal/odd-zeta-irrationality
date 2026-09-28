import OddZeta.Final.Main
import OddZeta.Cert.Saddle
import OddZeta.Phi.Sum

/-!
# Cases (A) and (B)

Instantiation of `Params.exists_irrational_zetaR` with the certified data of cases (A) and (B):
the step function `φ'` of the `Phi` certificate (checked on every interval), the lower bounds
`I' ≥ 678.6` resp. `774.1`, and the saddle-point certificates of `Cert.Saddle`. The arithmetic
constants are `r m̂₁ + ∑_{j≥2} m̂ⱼ = 1616` resp. `1946`, so that `C₂' ≤ 937.4` resp. `1171.9`,
while `H = Re Fd(u*) < -939` resp. `< -1175`.
-/

namespace OddZeta

open PhiCert

theorem weightedSum_eq_phiSum (m K : ℕ) (X : List ℚ) (vals : List ℕ) :
    weightedSum m K X vals = (phiSum m K X vals : ℝ) := by
  unfold weightedSum phiSum intervalWeight
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Rat.cast_mul, Rat.cast_add, Rat.cast_sum, Rat.cast_natCast]
  congr 2
  · refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  · by_cases h : (1 / m : ℚ) ≤ X.getD i 0
    · have h' : 1 / (m : ℝ) ≤ (X.getD i 0 : ℝ) := by
        have := (Rat.cast_le (K := ℝ)).mpr h
        push_cast at this
        exact this
      rw [ite_eq_left h, ite_eq_left h']
      push_cast
      ring
    · have h' : ¬ 1 / (m : ℝ) ≤ (X.getD i 0 : ℝ) := by
        intro h''
        apply h
        have : ((1 / m : ℚ) : ℝ) ≤ ((X.getD i 0 : ℚ) : ℝ) := by
          push_cast
          exact h''
        exact (Rat.cast_le (K := ℝ)).mp this
      rw [ite_eq_right h, ite_eq_right h']
      simp

/-- The step function of a checked certificate is bounded below by the values on the intervals
(the form required by `log_Delta_le`). -/
theorem phiStep_ge {η₀ : ℕ} {zs ps : List ℕ} {X : List ℚ} {vals : List ℕ}
    (h : checkPhiCert η₀ zs ps X vals = true) :
    ∀ i, i + 1 < X.length → ∀ x : ℝ, (X.getD i 0 : ℝ) < Int.fract x →
      Int.fract x < X.getD (i + 1) 0 → vals.getD i 0 ≤ phiStep X vals x := by
  intro i hi x hx₁ hx₂
  rw [List.getD_eq_getElem _ _ (by omega)] at hx₁
  rw [List.getD_eq_getElem _ _ hi] at hx₂
  rw [phiStep_eq h i hi x hx₁ hx₂]

/-- **Theorem 1.1** (for the real series). -/
theorem caseA_exists_irrational : ∃ s ∈ caseA.oddRange, Irrational (zetaR s) := by
  obtain ⟨D, b, c, c₀, ε₀, hD, hH, hα⟩ := caseA_saddle_cert
  have hglob := globalOK_of_checkPhiCert checkA
  have hlen := checkPhiCert_length checkA
  refine Params.exists_irrational_zetaR caseA_valid (by decide) XA valsA hglob.2.2.1
    hglob.2.2.2 hlen.2 (phiStep XA valsA) (fun x y => phiStep_le checkA x y)
    (phiStep_ge checkA) 20 678.6 ?_ hD ?_ hα
  · have hm : caseA.mhat0 = 72 := by decide
    rw [hm, weightedSum_eq_phiSum]
    have h' : ((678.6 : ℚ) : ℝ) ≤ ((phiSum _ 20 XA valsA : ℚ) : ℝ) := Rat.cast_le.mpr phiSumA_ge
    rw [show ((678.6 : ℚ) : ℝ) = 678.6 by norm_num] at h'
    exact h'
  · have h1 : caseA.r = 5 := by decide
    have h2 : caseA.mhat1 = 76 := by decide
    have h3 : caseA.mhats.tail.sum = 1236 := by decide
    rw [h1, h2, h3]
    push_cast
    linarith

/-- **Theorem 1.2** (for the real series). -/
theorem caseB_exists_irrational : ∃ s ∈ caseB.oddRange, Irrational (zetaR s) := by
  obtain ⟨D, b, c, c₀, ε₀, hD, hH, hα⟩ := caseB_saddle_cert
  have hglob := globalOK_of_checkPhiCert checkB
  have hlen := checkPhiCert_length checkB
  refine Params.exists_irrational_zetaR caseB_valid (by decide) XB valsB hglob.2.2.1
    hglob.2.2.2 hlen.2 (phiStep XB valsB) (fun x y => phiStep_le checkB x y)
    (phiStep_ge checkB) 20 774.1 ?_ hD ?_ hα
  · have hm : caseB.mhat0 = 57 := by decide
    rw [hm, weightedSum_eq_phiSum]
    have h' : ((774.1 : ℚ) : ℝ) ≤ ((phiSum _ 20 XB valsB : ℚ) : ℝ) := Rat.cast_le.mpr phiSumB_ge
    rw [show ((774.1 : ℚ) : ℝ) = 774.1 by norm_num] at h'
    exact h'
  · have h1 : caseB.r = 7 := by decide
    have h2 : caseB.mhat1 = 58 := by decide
    have h3 : caseB.mhats.tail.sum = 1540 := by decide
    rw [h1, h2, h3]
    push_cast
    linarith

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
