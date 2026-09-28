import OddZeta.Final.Assembly
import OddZeta.Analytic.SaddleAsymp
import OddZeta.Arith.DeltaGrowth

/-!
# The main theorem for a general direction vector

For valid parameters `P` (with the pole directions sorted), a step function `φ' ≤ φ₀` described
by breakpoints `X` and values `vals`, a rational lower bound `I'` for the weighted sum of `φ'`, and
a certified path `D` through the saddle point, the inequality `C₂' + H < 0` (with
`C₂' = r m̂₁ + ∑_{j≥2} m̂ⱼ - I'` and `H = Re Fd(u*)`) and `α = Im Fd(u*) ∉ πℤ` imply that one of the
numbers `ζ(s)`, `s ∈ {r+2, r+4, …, q-2}`, is irrational.
-/

namespace OddZeta

open Filter Topology Complex

namespace Params

variable {P : Params}

theorem exists_irrational_zetaR (hP : P.Valid) (hsorted : P.ps.Pairwise (· ≤ ·))
    (X : List ℚ) (vals : List ℕ) (hX0 : X.head? = some 0) (hX1 : X.getLast? = some 1)
    (hXmono : X.Pairwise (· < ·)) (φ' : ℝ → ℕ)
    (hφ0 : ∀ x y : ℝ, (φ' x : ℤ) ≤ phi0 P.eta0 P.zs P.ps x y)
    (hφ : ∀ i, i + 1 < X.length → ∀ x : ℝ, (X.getD i 0 : ℝ) < Int.fract x →
      Int.fract x < X.getD (i + 1) 0 → vals.getD i 0 ≤ φ' x)
    (K : ℕ) (I' : ℝ) (hI : I' ≤ weightedSum P.mhat0 K X vals)
    {D : PathData} {b c c₀ ε₀ : ℝ} (hD : P.PathCert D b c c₀ ε₀)
    (hC : P.r * P.mhat1 + (P.mhats.tail.sum : ℝ) - I' + (P.Fd D.u).re < 0)
    (hα : ∀ m : ℤ, (P.Fd D.u).im ≠ m * Real.pi) :
    ∃ s ∈ P.oddRange, Irrational (zetaR s) := by
  set H := (P.Fd D.u).re with hH
  set B := D.v * P.Ghat D.u * (Real.pi / (-(P.f'' D.u) * D.v ^ 2 / 2)) ^ (1 / 2 : ℂ) with hBdef
  -- the normalising sequence, made positive at `n = 0`
  set K' : ℕ → ℝ := fun n => if n = 0 then 1 else P.Kn H n with hK'
  have hK'pos : ∀ n, 0 < K' n := by
    intro n
    simp only [hK']
    split_ifs with h
    · exact one_pos
    · exact Kn_pos hP H n (Nat.one_le_iff_ne_zero.mpr h)
  have hK'ev : ∀ᶠ n : ℕ in atTop, K' n = P.Kn H n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [hK', Nat.one_le_iff_ne_zero.mp hn]
  refine exists_irrational_of_asymptotics (S := P.oddRange) P.F (fun n s => P.coefZeta n s)
    P.coefConst (P.Delta φ') zetaR ?_ ?_ (P.r * P.mhat1 + (P.mhats.tail.sum : ℝ) - I') H hC ?_
    K' hK'pos ?_ B (B_ne_zero hP hD) (P.Fd D.u).im hα ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact F_eq hP hn
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact ⟨Delta_pos φ' n, (Delta_mul_isInt hP hsorted hφ0 hn).1,
      (Delta_mul_isInt hP hsorted hφ0 hn).2⟩
  · intro ε hε
    have := log_Delta_le hP X vals hX0 hX1 hXmono φ' hφ K I' hI ε hε
    filter_upwards [this] with n hn
    linarith
  · refine (tendsto_log_Kn hP H).congr' ?_
    filter_upwards [hK'ev] with n hn
    rw [hn]
  · refine (tendsto_F_div_Kn hP hD).congr' ?_
    filter_upwards [hK'ev] with n hn
    rw [hn]

end Params

end OddZeta
