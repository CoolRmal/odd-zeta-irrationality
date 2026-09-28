import OddZeta.Arith.Delta
import OddZeta.PNT.Main

/-!
# The growth of `Δₙ` (Lemma 3.3 of the note, with the rational truncation `I'`)

If `φ' ≥ vᵢ` on the intervals `fract x ∈ (Xᵢ, Xᵢ₊₁)`, then by the prime number theorem
`log Δₙ ≤ n (r m̂₁ + ∑_{j≥2} m̂ⱼ - I' + o(1))` for every `I' ≤ ∑ᵢ vᵢ wᵢ`, where
`wᵢ = ∑_{k=1}^{K} (1/(k+Xᵢ) - 1/(k+Xᵢ₊₁)) + [Xᵢ ≥ 1/m̂₀] (1/Xᵢ - 1/Xᵢ₊₁)`
is the density of the primes `p` with `n/p ∈ ⋃_{k} (k + Xᵢ, k + Xᵢ₊₁)` (`0 ≤ k ≤ K`, `k = 0` only when
`p ≤ m̂₀ n` is automatic).
-/

namespace OddZeta

open Filter Topology

/-- The weight `∑_{k=1}^{K} (1/(k+α) - 1/(k+β)) + [α ≥ 1/m] (1/α - 1/β)` of an interval
`(α, β)`. -/
noncomputable def intervalWeight (m K : ℕ) (α β : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 K, (1 / (k + α) - 1 / (k + β))) +
    if 1 / (m : ℝ) ≤ α then 1 / α - 1 / β else 0

/-- `∑ᵢ vᵢ wᵢ` for the step function with breakpoints `X` and values `vals`. -/
noncomputable def weightedSum (m K : ℕ) (X : List ℚ) (vals : List ℕ) : ℝ :=
  ∑ i ∈ Finset.range (X.length - 1),
    (vals.getD i 0 : ℝ) * intervalWeight m K (X.getD i 0) (X.getD (i + 1) 0)

namespace Params

variable {P : Params}

/-- **Lemma 3.3** (upper bound, rational truncation). -/
theorem log_Delta_le (hP : P.Valid) (X : List ℚ) (vals : List ℕ)
    (hX0 : X.head? = some 0) (hX1 : X.getLast? = some 1)
    (hXmono : X.Pairwise (· < ·))
    (φ' : ℝ → ℕ)
    (hφ : ∀ i, i + 1 < X.length → ∀ x : ℝ, (X.getD i 0 : ℝ) < Int.fract x →
      Int.fract x < X.getD (i + 1) 0 → vals.getD i 0 ≤ φ' x)
    (K : ℕ) (I' : ℝ) (hI : I' ≤ weightedSum P.mhat0 K X vals) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Real.log (P.Delta φ' n) ≤
      n * (P.r * P.mhat1 + (P.mhats.tail.sum : ℝ) - I' + ε) := by
  sorry

end Params

end OddZeta
