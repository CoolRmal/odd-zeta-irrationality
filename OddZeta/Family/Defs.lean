import OddZeta.Arith.Delta

/-!
# The uniform family `η^(r)` (Section 8.1 of the note)

`η^(r) = (150; 45^r; 48^r, 50^r, 53^r, 56^r, 60^r, 74)`: `r` zero blocks with direction `45`,
`r` pole blocks with each of the directions `48, 50, 53, 56, 60`, and one pole block with
direction `74`; `q = 6r + 1`, so the linear forms involve `ζ(r+2), ζ(r+4), …, ζ(6r-1)`.
-/

namespace OddZeta

/-- The direction vector `η^(r)`. -/
def fam (r : ℕ) : Params where
  eta0 := 150
  zs := List.replicate r 45
  ps := List.replicate r 48 ++ List.replicate r 50 ++ List.replicate r 53 ++
    List.replicate r 56 ++ List.replicate r 60 ++ [74]
  etaOne := 45
  etaMin := 48

/-- The base vector `(150; 45; 48, 50, 53, 56, 60)` (the family with `r = 1`, without the block
`74`), whose function `φ̄` bounds `φ` for `η^(r)` from below by `φ ≥ r φ̄`. -/
def famBase : Params where
  eta0 := 150
  zs := [45]
  ps := [48, 50, 53, 56, 60]
  etaOne := 45
  etaMin := 48

namespace Fam

variable {r : ℕ}

theorem r_eq : (fam r).r = r := by simp [fam, Params.r]

theorem q_eq : (fam r).q = 6 * r + 1 := by simp [fam, Params.q]; ring

theorem valid (hr : Odd r) (h3 : 3 ≤ r) : (fam r).Valid where
  r_odd := by rw [r_eq]; exact hr
  q_odd := by rw [q_eq]; exact ⟨3 * r, by ring⟩
  three_le_r := by rw [r_eq]; exact h3
  r_add_four_le_q := by rw [r_eq, q_eq]; omega
  etaOne_mem := by simp [fam]; omega
  etaOne_le := by intro η hη; simp [fam, List.mem_replicate] at hη; simp [fam]; omega
  etaOne_pos := by simp [fam]
  etaMin_mem := by simp [fam]; omega
  etaMin_le := by
    intro η hη
    simp only [fam, List.mem_append, List.mem_replicate, List.mem_singleton] at hη
    simp only [fam]
    omega
  zs_le_etaMin := by intro η hη; simp [fam, List.mem_replicate] at hη; simp [fam]; omega
  two_mul_lt := by
    intro η hη
    simp only [fam, List.mem_append, List.mem_replicate, List.mem_singleton] at hη
    simp only [fam]
    omega
  sum_lt := by
    simp only [fam, Params.q, Params.r, List.sum_append, List.sum_replicate, List.length_append,
      List.length_replicate, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
      smul_eq_mul]
    omega

theorem ps_sorted : (fam r).ps.Pairwise (· ≤ ·) := by
  simp only [fam, List.pairwise_append, List.pairwise_replicate, List.mem_append,
    List.mem_replicate, List.mem_singleton, List.pairwise_cons, List.Pairwise.nil]
  refine ⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> (try simp) <;> (try intros) <;> omega

theorem oddRange_eq : (fam r).oddRange = (Finset.Icc (r + 2) (6 * r - 1)).filter Odd := by
  simp only [Params.oddRange, r_eq, q_eq]
  congr 2

theorem mhat0_eq (hr : 1 ≤ r) : (fam r).mhat0 = 54 := by
  simp only [Params.mhat0, fam]
  have : (List.replicate r 45).foldr max 0 = 45 := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    induction k with
    | zero => rfl
    | succ k ih => simp_all [List.replicate_succ]
  rw [this]
  rfl

end Fam

end OddZeta
