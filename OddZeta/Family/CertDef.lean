import OddZeta.Analytic.Saddle2
import OddZeta.Family.Phase

/-!
# The certificate statement for the family

`FamCert r`: a path `L_r` through the saddle point of `Fd` for `η^(r)` satisfying `PathCert2`, with
`H_d = Re Fd(u*) < -(214.8 r - 3)` and `α = Im Fd(u*) ∉ πℤ`.
-/

namespace OddZeta

/-- The certificate statement for the family. -/
def FamCert (r : ℕ) : Prop :=
  ∃ D : PathData2, ∃ b c K c₀ ε₀ : ℝ, (fam r).PathCert2 D b c K c₀ ε₀ ∧
    ((fam r).Fd D.u).re < -(214.8 * r - 3) ∧ ∀ m : ℤ, ((fam r).Fd D.u).im ≠ m * Real.pi

end OddZeta
