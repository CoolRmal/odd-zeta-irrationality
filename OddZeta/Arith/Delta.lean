import OddZeta.Setup.Rational
import OddZeta.Arith.Bricks
import OddZeta.Phi.Defs

/-!
# The denominators `Δₙ` (Lemma 3.2 of the note, Lemma 19 of Zudilin)

`Δₙ = ∏_{p ≤ h₀} p^{e_p}` with
* `e_p = 3q ⌊log_p h₀⌋` for `p ≤ √h₀` (crude treatment of small primes);
* `e_p = r[p ≤ m̂₁n] + ∑_{j≥2} [p ≤ m̂ⱼn] - [p ≤ m̂₀n] φ'(n/p)` for `p > √h₀`, where `φ'` is any
  function bounded by `φ₀` (in the application, the certified step function of `OddZeta.Phi`).

Then `Δₙ A_{s,n} ∈ ℤ` and `Δₙ A_{0,n} ∈ ℤ`.
-/

namespace OddZeta

namespace Params

variable (P : Params)

/-- `m̂₀ = max(η_r, η₀ - 2η_{r+1})`. -/
def mhat0 : ℕ := max (P.zs.foldr max 0) (P.eta0 - 2 * P.etaMin)

/-- `m̂ⱼ = max(m̂₀, η₀ - η₁ - η_{r+j})` for `j = 1, …, q-r` (in the order of `ps`, which is
increasing, so that `m̂₁ ≥ m̂₂ ≥ ⋯`). -/
def mhats : List ℕ := P.ps.map fun η => max P.mhat0 (P.eta0 - P.etaOne - η)

/-- `m̂₁`. -/
def mhat1 : ℕ := P.mhats.headD 0

/-- The exponent of a prime `p > √h₀` in `D_{m̂₁n}^r D_{m̂₂n} ⋯ D_{m̂_{q-r}n}`:
`r [p ≤ m̂₁n] + ∑_{j ≥ 2} [p ≤ m̂ⱼn]`. -/
def dExp (n p : ℕ) : ℕ :=
  (P.r - 1) * (if p ≤ P.mhat1 * n then 1 else 0) + (P.mhats.filter fun m => p ≤ m * n).length

/-- The exponent of `p` in `Δₙ`. -/
noncomputable def deltaExp (φ' : ℝ → ℕ) (n p : ℕ) : ℤ :=
  if p * p ≤ P.h0 n then ((3 * P.q * Nat.log p (P.h0 n) : ℕ) : ℤ)
  else (P.dExp n p : ℤ) - (if p ≤ P.mhat0 * n then (φ' ((n : ℝ) / p) : ℤ) else 0)

/-- The denominator `Δₙ` (formula (3.3) of the note, modified at the small primes). -/
noncomputable def Delta (φ' : ℝ → ℕ) (n : ℕ) : ℚ :=
  ∏ p ∈ (Finset.range (P.h0 n + 1)).filter Nat.Prime, (p : ℚ) ^ P.deltaExp φ' n p

variable {P}

theorem Delta_pos (φ' : ℝ → ℕ) (n : ℕ) : 0 < P.Delta φ' n :=
  Finset.prod_pos fun p hp => zpow_pos (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos) _

/-- **Lemma 3.2**: `Δₙ A_{s,n} ∈ ℤ` for the odd `s ∈ [r+2, q-2]`, and `Δₙ A_{0,n} ∈ ℤ`. -/
theorem Delta_mul_isInt (hP : P.Valid) (hsorted : P.ps.Pairwise (· ≤ ·)) {φ' : ℝ → ℕ}
    (hφ : ∀ x y : ℝ, (φ' x : ℤ) ≤ phi0 P.eta0 P.zs P.ps x y) {n : ℕ} (hn : 1 ≤ n) :
    (∀ s ∈ P.oddRange, ∃ z : ℤ, P.Delta φ' n * P.coefZeta n s = z) ∧
      ∃ z : ℤ, P.Delta φ' n * P.coefConst n = z := by
  sorry

end Params

end OddZeta
