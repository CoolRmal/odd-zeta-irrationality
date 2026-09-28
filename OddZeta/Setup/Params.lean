import Mathlib

/-!
# Parameters of the construction

A direction vector `η = (η₀; η₁, …, η_q)` is split into the `r` zero-block directions `zs` and the
`q - r` pole-block directions `ps` (Section 1 of the note). For `n ≥ 1` one puts `h₀ = η₀ n + 2`
and `hⱼ = ηⱼ n + 1`.
-/

namespace OddZeta

/-- The data of a direction vector. `etaMin` is the smallest pole-block direction `η_{r+1}` and
`etaOne` the smallest zero-block direction `η₁`. -/
structure Params where
  eta0 : ℕ
  zs : List ℕ
  ps : List ℕ
  etaOne : ℕ
  etaMin : ℕ

namespace Params

variable (P : Params)

/-- The number of zero blocks. -/
def r : ℕ := P.zs.length

/-- The total number of blocks. -/
def q : ℕ := P.zs.length + P.ps.length

/-- The odd integers `r + 2, r + 4, …, q - 2`. -/
def oddRange : Finset ℕ := (Finset.Icc (P.r + 2) (P.q - 2)).filter Odd

/-- `h₀ = η₀ n + 2`. -/
def h0 (n : ℕ) : ℕ := P.eta0 * n + 2

/-- `hⱼ = ηⱼ n + 1` for a direction `η = ηⱼ`. -/
def hh (η n : ℕ) : ℕ := η * n + 1

/-- The poles of `Rₙ` are the points `-k`, `k ∈ poleRange n = [h_{r+1}, h₀ - h_{r+1}]`. -/
def poleRange (n : ℕ) : Finset ℕ := Finset.Icc (hh P.etaMin n) (P.h0 n - hh P.etaMin n)

/-- The conditions (1.1) of the note, and the bookkeeping facts about `etaOne`, `etaMin`. -/
structure Valid : Prop where
  r_odd : Odd P.r
  q_odd : Odd P.q
  three_le_r : 3 ≤ P.r
  r_add_four_le_q : P.r + 4 ≤ P.q
  etaOne_mem : P.etaOne ∈ P.zs
  etaOne_le : ∀ η ∈ P.zs, P.etaOne ≤ η
  etaOne_pos : 0 < P.etaOne
  etaMin_mem : P.etaMin ∈ P.ps
  etaMin_le : ∀ η ∈ P.ps, P.etaMin ≤ η
  zs_le_etaMin : ∀ η ∈ P.zs, η ≤ P.etaMin
  two_mul_lt : ∀ η ∈ P.ps, 2 * η < P.eta0
  sum_lt : 2 * (P.zs.sum + P.ps.sum) < P.eta0 * (P.q - P.r)

end Params

/-- Case (A) of the note: `r = 5`, `q = 23`, `η₀ = 196` (Theorem 1.1). -/
def caseA : Params where
  eta0 := 196
  zs := [58, 58, 58, 59, 60]
  ps := [62, 62, 63, 64, 64, 65, 66, 66, 68, 69, 70, 72, 73, 75, 76, 77, 79, 80]
  etaOne := 58
  etaMin := 62

/-- Case (B) of the note: `r = 7`, `q = 35`, `η₀ = 151` (Theorem 1.2). -/
def caseB : Params where
  eta0 := 151
  zs := [46, 46, 46, 46, 46, 46, 46]
  ps := [47, 47, 48, 49, 49, 49, 50, 51, 51, 51, 52, 53, 53, 53, 54, 55, 55, 55, 56, 57, 57, 57,
    58, 59, 59, 59, 60, 61]
  etaOne := 46
  etaMin := 47

theorem caseA_valid : caseA.Valid where
  r_odd := by decide
  q_odd := by decide
  three_le_r := by decide
  r_add_four_le_q := by decide
  etaOne_mem := by decide
  etaOne_le := by decide
  etaOne_pos := by decide
  etaMin_mem := by decide
  etaMin_le := by decide
  zs_le_etaMin := by decide
  two_mul_lt := by decide
  sum_lt := by decide

theorem caseB_valid : caseB.Valid where
  r_odd := by decide
  q_odd := by decide
  three_le_r := by decide
  r_add_four_le_q := by decide
  etaOne_mem := by decide
  etaOne_le := by decide
  etaOne_pos := by decide
  etaMin_mem := by decide
  etaMin_le := by decide
  zs_le_etaMin := by decide
  two_mul_lt := by decide
  sum_lt := by decide

theorem caseA_oddRange : caseA.oddRange = {7, 9, 11, 13, 15, 17, 19, 21} := by decide

theorem caseB_oddRange :
    caseB.oddRange = {9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33} := by decide

/-- `ζ(s) = ∑_{m ≥ 1} m^{-s}` as a real number. -/
noncomputable def zetaR (s : ℕ) : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ s

end OddZeta
