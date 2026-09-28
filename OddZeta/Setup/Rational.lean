import OddZeta.Setup.Params
import OddZeta.Algebra.PartialFractions

/-!
# The rational function `Rₙ`, its partial fractions and the linear form `Fₙ`

Section 2 of the note. With `K = [h_{r+1}, h₀ - h_{r+1}]` (`poleRange`),
`Rₙ = numPoly / ∏_{k ∈ K} (X + k)^{q-r}`, where each pole block `(h₀-2h)!/(X+h)_{h₀-2h+1}` is
written as `polePoly / ∏_{k ∈ K} (X + k)`.

The expansion `ε^{q-r} Rₙ(-k+ε)` at a pole is `expan n k`; its coefficients are the
partial-fraction coefficients `a_{i,k} = coef n i k`. The linear form is
`Fₙ = ∑_{m ≥ 1-h₁} ρₙ(m)` with `ρₙ(m) = ∑_{i,k} C(i+r-2, r-1) a_{i,k} (m+k)^{-(i+r-1)}`
(which is `Rₙ^{(r-1)}(m)/(r-1)!`).
-/

namespace OddZeta

open Polynomial

namespace Params

variable (P : Params)

/-- `∏_{i ∈ [a, b)} (X + i)`. -/
noncomputable def pochPoly (a b : ℕ) : ℚ[X] := ∏ i ∈ Finset.Ico a b, (X + C (i : ℚ))

/-- A zero block `(X+1)_{h-1} (X+h₀-h+1)_{h-1} / ((h-1)!)²`, `h = η n + 1`. -/
noncomputable def zeroPoly (n η : ℕ) : ℚ[X] :=
  C (((η * n).factorial : ℚ)⁻¹ ^ 2) * pochPoly 1 (hh η n) *
    pochPoly (P.h0 n - hh η n + 1) (P.h0 n)

/-- A pole block `(h₀-2h)! / (X+h)_{h₀-2h+1}`, multiplied by `∏_{k ∈ K} (X + k)`. -/
noncomputable def polePoly (n η : ℕ) : ℚ[X] :=
  C ((P.h0 n - 2 * hh η n).factorial : ℚ) *
    ∏ k ∈ P.poleRange n \ Finset.Icc (hh η n) (P.h0 n - hh η n), (X + C (k : ℚ))

/-- The polynomial part `(h₀ + 2X) · ∏ zero blocks`. -/
noncomputable def zeroPart (n : ℕ) : ℚ[X] :=
  (C (P.h0 n : ℚ) + 2 * X) * (P.zs.map (P.zeroPoly n)).prod

/-- The numerator: `Rₙ = numPoly / ∏_{k ∈ K} (X + k)^{q-r}`. -/
noncomputable def numPoly (n : ℕ) : ℚ[X] :=
  P.zeroPart n * (P.ps.map (P.polePoly n)).prod

/-- `Rₙ(t)` as a complex function. -/
noncomputable def R (n : ℕ) (t : ℂ) : ℂ :=
  ((P.numPoly n).map (algebraMap ℚ ℂ)).eval t / ∏ k ∈ P.poleRange n, (t + k) ^ (P.q - P.r)

/-- The local factor of a pole block at the pole `-k`: the expansion of
`polePoly / ∏_{k' ∈ K, k' ≠ k} (X + k')` at `-k`, i.e. `ε (h₀-2h)! / (ε - k + h)_{h₀-2h+1}`. -/
noncomputable def poleLocal (n η k : ℕ) : PowerSeries ℚ :=
  ((taylor (-(k : ℚ)) (P.polePoly n η) : ℚ[X]) : PowerSeries ℚ) *
    (∏ k' ∈ (P.poleRange n).erase k, (PowerSeries.C ((k' : ℚ) - k) + PowerSeries.X))⁻¹

/-- The expansion `ε^{q-r} Rₙ(-k+ε)` at the pole `-k`: the product of the local factors of all
the bricks. -/
noncomputable def expan (n k : ℕ) : PowerSeries ℚ :=
  ((taylor (-(k : ℚ)) (P.zeroPart n) : ℚ[X]) : PowerSeries ℚ) *
    (P.ps.map fun η => P.poleLocal n η k).prod

/-- The partial-fraction coefficients `a_{i,k}` (for `1 ≤ i ≤ q - r`, `k ∈ K`). -/
noncomputable def coef (n i k : ℕ) : ℚ := PowerSeries.coeff (P.q - P.r - i) (P.expan n k)

/-- `ρₙ(m) = ∑_{i,k} C(i+r-2, r-1) a_{i,k} (m+k)^{-(i+r-1)}`. -/
noncomputable def rho (n : ℕ) (m : ℤ) : ℚ :=
  ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r),
    ((i + P.r - 2).choose (P.r - 1) : ℚ) * P.coef n i k / ((m : ℚ) + k) ^ (i + P.r - 1)

/-- The linear form `Fₙ = ∑_{m ≥ 1 - h₁} ρₙ(m)`. -/
noncomputable def F (n : ℕ) : ℝ := ∑' j : ℕ, (P.rho n ((j : ℤ) + 1 - hh P.etaOne n) : ℝ)

/-- The coefficient `A_{s,n} = C(s-1, r-1) ∑_k a_{s-r+1,k}` of `ζ(s)`. -/
noncomputable def coefZeta (n s : ℕ) : ℚ :=
  ((s - 1).choose (P.r - 1) : ℚ) * ∑ k ∈ P.poleRange n, P.coef n (s + 1 - P.r) k

/-- The constant term `A_{0,n} = ∑_{i,k} C(i+r-2, r-1) a_{i,k} ∑_{l=1}^{k-h₁} l^{-(i+r-1)}`. -/
noncomputable def coefConst (n : ℕ) : ℚ :=
  ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r),
    ((i + P.r - 2).choose (P.r - 1) : ℚ) * P.coef n i k *
      ∑ l ∈ Finset.Icc 1 (k - hh P.etaOne n), ((l : ℚ) ^ (i + P.r - 1))⁻¹

variable {P}

/-- The product formula for `Rₙ` (formula (1.2) of the note). -/
theorem R_eq_prod (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {t : ℂ}
    (ht : ∀ k ∈ P.poleRange n, t + k ≠ 0) :
    P.R n t = (P.h0 n + 2 * t) *
      (P.zs.map fun η => (∏ i ∈ Finset.Ico 1 (hh η n), (t + i)) *
        (∏ i ∈ Finset.Ico (P.h0 n - hh η n + 1) (P.h0 n), (t + i)) /
          ((η * n).factorial : ℂ) ^ 2).prod *
      (P.ps.map fun η => ((P.h0 n - 2 * hh η n).factorial : ℂ) /
        ∏ i ∈ Finset.Icc (hh η n) (P.h0 n - hh η n), (t + i)).prod := by
  sorry

/-- The partial-fraction decomposition (2.1) of `Rₙ`. -/
theorem R_eq_sum (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {t : ℂ}
    (ht : ∀ k ∈ P.poleRange n, t + k ≠ 0) :
    P.R n t = ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r),
      (P.coef n i k : ℂ) / (t + k) ^ i := by
  sorry

/-- The residues of `Rₙ` sum to zero (`deg Rₙ ≤ -2`). -/
theorem sum_coef_one (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ P.poleRange n, P.coef n 1 k = 0 := by
  sorry

/-- The symmetry `a_{i,k} = (-1)^{i+1} a_{i,h₀-k}` (Lemma 2.2 of the note), from
`Rₙ(-t-h₀) = -Rₙ(t)`. -/
theorem coef_symm (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {i k : ℕ} (hi : i ≤ P.q - P.r)
    (hk : k ∈ P.poleRange n) :
    P.coef n i (P.h0 n - k) = (-1) ^ (i + 1) * P.coef n i k := by
  sorry

/-- **Lemma 2.2**: `Fₙ` is a linear form in `1` and the odd zeta values `ζ(r+2), …, ζ(q-2)`. -/
theorem F_eq (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    P.F n = ∑ s ∈ P.oddRange, (P.coefZeta n s : ℝ) * zetaR s - P.coefConst n := by
  sorry

end Params

end OddZeta
