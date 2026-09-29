import OddZeta.Family.PhiBase
import OddZeta.Family.Defs
import OddZeta.Arith.DeltaGrowth

/-!
# The arithmetic side for the uniform family (Lemma 8.4 of the note)

For `η^(r) = (150; 45^r; 48^r, 50^r, 53^r, 56^r, 60^r, 74)`:

* `φ₀` of `η^(r)` is `r` times `φ₀` of the base vector `(150; 45; 48, 50, 53, 56, 60)` plus the
  (nonnegative) term of the block `74` (`Fam.phi0_eq`); hence `φ' = r φ̄'` is a lower bound for
  `φ₀`, where `φ̄' = phiStep XBase valsBase` is the certified step function of the base vector
  (`Fam.phiFam_le`), with values `r · valsBase` on the intervals of `XBase` (`Fam.valsFam_le`);
* the weighted sum `I'` of `r φ̄'` is `r` times that of `φ̄'`, hence `≥ 116.2 r`
  (`Fam.weightedSum_ge`, from `phiSumBase_ge`);
* `m̂₀ = 54`, `m̂₁ = 57` and `∑_{j ≥ 2} m̂ⱼ = 274 r - 3`, so `r m̂₁ + ∑_{j≥2} m̂ⱼ = 331 r - 3`
  (`Fam.mhat1_eq`, `Fam.tail_sum_eq`, `Fam.C2_eq`).

`fam_arith` packages these facts in the form required by `Params.exists_irrational_zetaR`
(with `K = 20`, `I' = 116.2 r`), whose hypothesis `hC` then reduces to
`(P.Fd D.u).re < -(214.8 r - 3)`.
-/

namespace OddZeta

open PhiCert

namespace Fam

/-! ## `φ₀` of `η^(r)` -/

/-- `φ₀` of `η^(r)` is `r` times `φ₀` of the base vector plus the term of the block `74`. -/
theorem phi0_eq (r : ℕ) (x y : ℝ) :
    phi0 (fam r).eta0 (fam r).zs (fam r).ps x y =
      r * phi0 150 [45] [48, 50, 53, 56, 60] x y + iota (y - 74 * x) ((150 - 74 : ℝ) * x - y) := by
  simp only [phi0, fam, List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, nsmul_eq_mul]
  push_cast
  ring

theorem phi0_ge (r : ℕ) (x y : ℝ) :
    (r : ℤ) * phi0 150 [45] [48, 50, 53, 56, 60] x y ≤
      phi0 (fam r).eta0 (fam r).zs (fam r).ps x y := by
  rw [phi0_eq]
  linarith [iota_nonneg (y - 74 * x) ((150 - 74 : ℝ) * x - y)]

/-! ## The step function `φ' = r φ̄'` -/

/-- The step function `φ' = r φ̄'` for `η^(r)`. -/
noncomputable def phiFam (r : ℕ) (x : ℝ) : ℕ := r * phiStep XBase valsBase x

/-- The values `r · valsBase` of `φ'` on the intervals of `XBase`. -/
def valsFam (r : ℕ) : List ℕ := valsBase.map (r * ·)

theorem phiFam_le (r : ℕ) (x y : ℝ) :
    (phiFam r x : ℤ) ≤ phi0 (fam r).eta0 (fam r).zs (fam r).ps x y := by
  have h := phiStep_le checkBase x y
  calc (phiFam r x : ℤ) = r * (phiStep XBase valsBase x : ℤ) := by simp [phiFam]
    _ ≤ r * phi0 150 [45] [48, 50, 53, 56, 60] x y :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ _ := phi0_ge r x y

theorem getD_map_mul (r i : ℕ) (l : List ℕ) : (l.map (r * ·)).getD i 0 = r * l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem valsFam_le (r : ℕ) :
    ∀ i, i + 1 < XBase.length → ∀ x : ℝ, (XBase.getD i 0 : ℝ) < Int.fract x →
      Int.fract x < XBase.getD (i + 1) 0 → (valsFam r).getD i 0 ≤ phiFam r x := by
  intro i hi x hx₁ hx₂
  rw [List.getD_eq_getElem _ _ (by omega)] at hx₁
  rw [List.getD_eq_getElem _ _ hi] at hx₂
  rw [valsFam, getD_map_mul, phiFam, phiStep_eq checkBase i hi x hx₁ hx₂]

/-! ## The weighted sum -/

theorem weightedSum_map_mul (m K r : ℕ) (X : List ℚ) (vals : List ℕ) :
    weightedSum m K X (vals.map (r * ·)) = r * weightedSum m K X vals := by
  unfold weightedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_map_mul]
  push_cast
  ring

/-- `weightedSum` is the real cast of the rational `phiSum` (as `weightedSum_eq_phiSum` of
`Final/Cases.lean`, restated here to avoid importing the certificates of cases A and B). -/
theorem weightedSum_eq_ratCast_phiSum (m K : ℕ) (X : List ℚ) (vals : List ℕ) :
    weightedSum m K X vals = (phiSum m K X vals : ℝ) := by
  unfold weightedSum phiSum intervalWeight
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Rat.cast_mul, Rat.cast_add, Rat.cast_sum, Rat.cast_natCast]
  congr 2
  · refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  · have hc : (1 / m : ℚ) ≤ X.getD i 0 ↔ 1 / (m : ℝ) ≤ (X.getD i 0 : ℝ) := by
      rw [← Rat.cast_le (K := ℝ)]
      push_cast
      rfl
    by_cases h : (1 / m : ℚ) ≤ X.getD i 0
    · rw [ite_eq_left h, ite_eq_left (hc.1 h)]
      push_cast
      ring
    · rw [ite_eq_right h, ite_eq_right (mt hc.2 h)]
      simp

theorem weightedSum_base_ge : (116.2 : ℝ) ≤ weightedSum 54 20 XBase valsBase := by
  rw [weightedSum_eq_ratCast_phiSum]
  have h : ((116.2 : ℚ) : ℝ) ≤ ((phiSum 54 20 XBase valsBase : ℚ) : ℝ) :=
    Rat.cast_le.mpr phiSumBase_ge
  rw [show ((116.2 : ℚ) : ℝ) = 116.2 by norm_num] at h
  exact h

theorem weightedSum_ge {r : ℕ} (hr : 1 ≤ r) :
    (116.2 * r : ℝ) ≤ weightedSum (fam r).mhat0 20 XBase (valsFam r) := by
  rw [mhat0_eq hr, valsFam, weightedSum_map_mul]
  have h := weightedSum_base_ge
  have hr' : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  nlinarith

/-! ## The constants `m̂ⱼ` -/

theorem mhats_eq {r : ℕ} (hr : 1 ≤ r) :
    (fam r).mhats = List.replicate r 57 ++ List.replicate r 55 ++ List.replicate r 54 ++
      List.replicate r 54 ++ List.replicate r 54 ++ [54] := by
  have h0 := mhat0_eq hr
  simp only [Params.mhats] at h0 ⊢
  rw [h0]
  simp only [fam, List.map_append, List.map_replicate, List.map_cons, List.map_nil]
  rfl

theorem mhat1_eq {r : ℕ} (hr : 1 ≤ r) : (fam r).mhat1 = 57 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [Params.mhat1, mhats_eq hr, List.replicate_succ]
  rfl

theorem sum_mhats {r : ℕ} (hr : 1 ≤ r) : (fam r).mhats.sum = 274 * r + 54 := by
  rw [mhats_eq hr]
  simp only [List.sum_append, List.sum_replicate, List.sum_cons, List.sum_nil, smul_eq_mul]
  ring

theorem tail_sum_eq {r : ℕ} (hr : 1 ≤ r) : (fam r).mhats.tail.sum = 274 * r - 3 := by
  have h : (fam r).mhats.sum = (fam r).mhat1 + (fam r).mhats.tail.sum := by
    rw [Params.mhat1]
    cases (fam r).mhats <;> simp
  rw [sum_mhats hr, mhat1_eq hr] at h
  omega

/-- `r m̂₁ + ∑_{j ≥ 2} m̂ⱼ = 331 r - 3`. -/
theorem C2_eq {r : ℕ} (hr : 1 ≤ r) :
    ((fam r).r * (fam r).mhat1 + ((fam r).mhats.tail.sum : ℝ)) = 331 * r - 3 := by
  rw [r_eq, mhat1_eq hr, tail_sum_eq hr, Nat.cast_sub (by omega)]
  push_cast
  ring

end Fam

open Fam in
/-- **The arithmetic side of Theorem 8.1** (Lemma 8.4 of the note): for `η^(r)` there are a
step function `φ' ≤ φ₀` with breakpoints `X` and values `vals`, and a weighted sum
`I' = 116.2 r ≤ weightedSum m̂₀ 20 X vals`, with `r m̂₁ + ∑_{j≥2} m̂ⱼ - I' ≤ 214.8 r - 3`. These are
the arithmetic hypotheses of `Params.exists_irrational_zetaR` (with `K = 20`, `I' = 116.2 r`). -/
theorem fam_arith (r : ℕ) (hr : 1 ≤ r) :
    ∃ (X : List ℚ) (vals : List ℕ) (φ' : ℝ → ℕ), X.head? = some 0 ∧ X.getLast? = some 1 ∧
      X.Pairwise (· < ·) ∧ (∀ x y : ℝ, (φ' x : ℤ) ≤ phi0 (fam r).eta0 (fam r).zs (fam r).ps x y) ∧
      (∀ i, i + 1 < X.length → ∀ x : ℝ, (X.getD i 0 : ℝ) < Int.fract x →
        Int.fract x < X.getD (i + 1) 0 → vals.getD i 0 ≤ φ' x) ∧
      (fam r).r * (fam r).mhat1 + ((fam r).mhats.tail.sum : ℝ) - 116.2 * r ≤ 214.8 * r - 3 ∧
      (116.2 * r : ℝ) ≤ weightedSum (fam r).mhat0 20 X vals := by
  obtain ⟨-, -, hX0, hX1⟩ := globalOK_of_checkPhiCert checkBase
  refine ⟨XBase, valsFam r, phiFam r, hX0, hX1, (checkPhiCert_length checkBase).2,
    phiFam_le r, valsFam_le r, ?_, weightedSum_ge hr⟩
  rw [C2_eq hr]
  linarith

end OddZeta
