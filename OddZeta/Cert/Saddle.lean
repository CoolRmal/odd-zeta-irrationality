import OddZeta.Analytic.Saddle
import OddZeta.Cert.CaseA
import OddZeta.Cert.CaseB

/-!
# The numerical certificates for the saddle-point analysis (Section 5 of the note)

For each case we exhibit a path `L` through the exact saddle point `u*` of `Fd = f + i(r-2)π u`
(which exists within `10⁻¹⁰` of an explicit rational point, by the contraction mapping theorem)
satisfying the conditions `PathCert`, and bound `H = Re Fd(u*)` and `α = Im Fd(u*)`.
All inequalities are checked by the Lean kernel with rational interval arithmetic
(`OddZeta.Numerics`).
-/

namespace OddZeta

/-- Case (A): the saddle point near `-0.5907586583 - 9.7226884913 i`, `H = -939.0301751743…`,
`α ≡ 1.7733883 (mod π)`. -/
theorem caseA_saddle_cert :
    ∃ D : PathData, ∃ b c c₀ ε₀ : ℝ, caseA.PathCert D b c c₀ ε₀ ∧
      (caseA.Fd D.u).re < -939 ∧ ∀ m : ℤ, (caseA.Fd D.u).im ≠ m * Real.pi :=
  Cert.caseA_cert

/-- Case (B): the saddle point near `2.4144461602 - 6.6989299743 i`, `H = -1175.7847344814…`,
`α ≡ 0.3571480 (mod π)`. -/
theorem caseB_saddle_cert :
    ∃ D : PathData, ∃ b c c₀ ε₀ : ℝ, caseB.PathCert D b c c₀ ε₀ ∧
      (caseB.Fd D.u).re < -1175 ∧ ∀ m : ℤ, (caseB.Fd D.u).im ≠ m * Real.pi :=
  Cert.caseB_cert

end OddZeta
