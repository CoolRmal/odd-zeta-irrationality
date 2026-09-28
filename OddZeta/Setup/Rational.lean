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

/-! ### Bookkeeping -/

lemma q_sub_r : P.q - P.r = P.ps.length := by
  unfold q r; omega

lemma hh_le_hh {η η' n : ℕ} (h : η ≤ η') : hh η n ≤ hh η' n := by
  unfold hh; have := Nat.mul_le_mul_right n h; omega

lemma two_hh_lt (hP : P.Valid) {n η : ℕ} (hn : 1 ≤ n) (hη : η ∈ P.ps) :
    2 * hh η n < P.h0 n := by
  have h1 := hP.two_mul_lt η hη
  have h2 : (2 * η + 1) * n ≤ P.eta0 * n := Nat.mul_le_mul_right n h1
  have h3 : (2 * η + 1) * n = 2 * (η * n) + n := by ring
  unfold hh h0; omega

lemma mem_poleRange {n k : ℕ} :
    k ∈ P.poleRange n ↔ hh P.etaMin n ≤ k ∧ k ≤ P.h0 n - hh P.etaMin n :=
  Finset.mem_Icc

lemma Icc_subset_poleRange (hP : P.Valid) {n η : ℕ} (hη : η ∈ P.ps) :
    Finset.Icc (hh η n) (P.h0 n - hh η n) ⊆ P.poleRange n := by
  intro k hk
  have := hh_le_hh (n := n) (hP.etaMin_le η hη)
  rw [Finset.mem_Icc] at hk
  rw [mem_poleRange]; omega

lemma reflect_mem_poleRange {n k : ℕ} (hk : k ∈ P.poleRange n) :
    k ≤ P.h0 n ∧ P.h0 n - k ∈ P.poleRange n := by
  rw [mem_poleRange] at hk ⊢; omega

lemma list_prod_map_div {α K : Type*} [Field K] (l : List α) (f : α → K) (c : K) :
    (l.map f).prod / c ^ l.length = (l.map fun x => f x / c).prod := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← ih,
      List.length_cons, pow_succ]; ring

/-- The product formula for `Rₙ` (formula (1.2) of the note). -/
theorem R_eq_prod (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {t : ℂ}
    (ht : ∀ k ∈ P.poleRange n, t + k ≠ 0) :
    P.R n t = (P.h0 n + 2 * t) *
      (P.zs.map fun η => (∏ i ∈ Finset.Ico 1 (hh η n), (t + i)) *
        (∏ i ∈ Finset.Ico (P.h0 n - hh η n + 1) (P.h0 n), (t + i)) /
          ((η * n).factorial : ℂ) ^ 2).prod *
      (P.ps.map fun η => ((P.h0 n - 2 * hh η n).factorial : ℂ) /
        ∏ i ∈ Finset.Icc (hh η n) (P.h0 n - hh η n), (t + i)).prod := by
  unfold R numPoly zeroPart
  rw [eval_map_algebraMap, q_sub_r, Finset.prod_pow]
  simp only [map_mul, map_list_prod, List.map_map]
  rw [mul_div_assoc, list_prod_map_div]
  congr 1
  · congr 1
    · simp [map_ofNat]
    · congr 1
      refine List.map_congr_left fun η _ => ?_
      simp [zeroPoly, pochPoly, map_prod]
      ring
  · congr 1
    refine List.map_congr_left fun η hη => ?_
    simp only [Function.comp_apply, polePoly, map_mul, aeval_C, map_prod, map_add, aeval_X]
    rw [← Finset.prod_sdiff (Icc_subset_poleRange hP hη)]
    have hne : ∏ x ∈ P.poleRange n \ Finset.Icc (hh η n) (P.h0 n - hh η n), (t + (x : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k hk => ht k (Finset.mem_sdiff.1 hk).1
    simp only [eq_ratCast, Rat.cast_natCast]
    rw [mul_comm (∏ x ∈ P.poleRange n \ _, _) (∏ x ∈ Finset.Icc _ _, _),
      mul_div_mul_right _ _ hne]

/-! ### The local expansions -/

/-- The product `∏_{k' ∈ K, k' ≠ k} (k' - k + ε)`. -/
noncomputable abbrev locDen (n k : ℕ) : PowerSeries ℚ :=
  ∏ k' ∈ (P.poleRange n).erase k, (PowerSeries.C ((k' : ℚ) - k) + PowerSeries.X)

lemma constantCoeff_locDen_ne_zero (n k : ℕ) :
    PowerSeries.constantCoeff (P.locDen n k) ≠ 0 := by
  rw [locDen, map_prod]
  refine Finset.prod_ne_zero_iff.2 fun k' hk' => ?_
  have : k' ≠ k := (Finset.mem_erase.1 hk').1
  simp only [map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero]
  rw [sub_ne_zero]; exact_mod_cast this

lemma coe_taylor_list_prod {α : Type*} (a : ℚ) (l : List α) (f : α → ℚ[X]) :
    ((taylor a (l.map f).prod : ℚ[X]) : PowerSeries ℚ) =
      (l.map fun x => ((taylor a (f x) : ℚ[X]) : PowerSeries ℚ)).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp [taylor_mul, ih]

/-- The defining identity of `expan`: `expan n k · ∏_{k' ≠ k} (k' - k + ε)^{q-r} = N(-k + ε)`. -/
lemma expan_mul (n k : ℕ) :
    P.expan n k * P.locDen n k ^ (P.q - P.r) =
      ((taylor (-(k : ℚ)) (P.numPoly n) : ℚ[X]) : PowerSeries ℚ) := by
  have hloc : ∀ η, P.poleLocal n η k * P.locDen n k =
      ((taylor (-(k : ℚ)) (P.polePoly n η) : ℚ[X]) : PowerSeries ℚ) := by
    intro η
    rw [poleLocal, mul_assoc, PowerSeries.inv_mul_cancel _ (constantCoeff_locDen_ne_zero n k),
      mul_one]
  rw [q_sub_r, expan, numPoly, taylor_mul, Polynomial.coe_mul, mul_assoc, ← List.prod_replicate,
    ← List.map_const', ← List.prod_map_mul, coe_taylor_list_prod]
  congr 2
  exact List.map_congr_left fun η _ => hloc η

lemma prod_univ_erase_coe {M : Type*} [CommMonoid M] (s : Finset ℕ) (i : s) (f : ℕ → M) :
    ∏ j ∈ Finset.univ.erase i, f j = ∏ j ∈ s.erase i, f j := by
  have : s.erase i = (Finset.univ.erase i).image Subtype.val := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hx, hs⟩
      exact ⟨⟨x, hs⟩, fun h => hx (by rw [← h]), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨fun h => hy (Subtype.ext h), y.2⟩
  rw [this, Finset.prod_image Subtype.val_injective.injOn]

/-- The hypothesis of the partial-fraction theorems, for `ι = K`, `s k = -k`, `μ = q - r`. -/
lemma hg_expan (n : ℕ) (i : P.poleRange n) :
    P.expan n i * ∏ j ∈ Finset.univ.erase i,
        (PowerSeries.C (-((i : ℕ) : ℚ) - -((j : ℕ) : ℚ)) + PowerSeries.X) ^ (P.q - P.r) =
      ((taylor (-((i : ℕ) : ℚ)) (P.numPoly n) : ℚ[X]) : PowerSeries ℚ) := by
  rw [← expan_mul, Finset.prod_pow, prod_univ_erase_coe (P.poleRange n) i
    (fun j => PowerSeries.C (-((i : ℕ) : ℚ) - -(j : ℚ)) + PowerSeries.X)]
  simp only [neg_sub_neg]

lemma injective_neg_coe (n : ℕ) :
    Function.Injective fun i : P.poleRange n => -((i : ℕ) : ℚ) := by
  intro a b h
  exact Subtype.ext (by simpa using h)

/-! ### Degree bound -/

lemma natDegree_pochPoly_le (a b : ℕ) : (pochPoly a b).natDegree ≤ b - a := by
  unfold pochPoly
  refine (natDegree_prod_le _ _).trans ?_
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico, le_refl]

lemma natDegree_zeroPoly_le (n η : ℕ) : (P.zeroPoly n η).natDegree ≤ 2 * (η * n) := by
  unfold zeroPoly
  refine natDegree_mul_le.trans ?_
  have h1 := (natDegree_C_mul_le (((η * n).factorial : ℚ)⁻¹ ^ 2) (pochPoly 1 (hh η n))).trans
    (natDegree_pochPoly_le 1 (hh η n))
  have h2 := natDegree_pochPoly_le (P.h0 n - hh η n + 1) (P.h0 n)
  have : hh η n = η * n + 1 := rfl
  omega

lemma natDegree_polePoly_le (n η : ℕ) :
    (P.polePoly n η).natDegree ≤ (P.poleRange n \ Finset.Icc (hh η n) (P.h0 n - hh η n)).card := by
  unfold polePoly
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one, le_refl]

lemma card_poleRange (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    (P.poleRange n).card + 2 * (P.etaMin * n) = P.eta0 * n + 1 := by
  have := two_hh_lt hP hn hP.etaMin_mem
  rw [poleRange, Nat.card_Icc]
  unfold hh h0 at *
  omega

lemma card_sdiff_add (hP : P.Valid) {n η : ℕ} (hn : 1 ≤ n) (hη : η ∈ P.ps) :
    (P.poleRange n \ Finset.Icc (hh η n) (P.h0 n - hh η n)).card + 2 * (P.etaMin * n) =
      2 * (η * n) := by
  rw [Finset.card_sdiff_of_subset (Icc_subset_poleRange hP hη), Nat.card_Icc]
  have h1 := card_poleRange hP hn
  have h2 := two_hh_lt hP hn hη
  have h3 := hh_le_hh (n := n) (hP.etaMin_le η hη)
  have h4 := Finset.card_le_card (Icc_subset_poleRange (n := n) hP hη)
  rw [Nat.card_Icc] at h4
  unfold hh h0 at *
  omega

lemma list_sum_map_add_const {α : Type*} (l : List α) (f g : α → ℕ) (a : ℕ)
    (h : ∀ x ∈ l, f x + a = g x) : (l.map f).sum + l.length * a = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih fun y hy => h y (by simp [hy])
    rw [Nat.succ_mul]
    omega

lemma list_sum_map_two_mul (l : List ℕ) (n : ℕ) :
    (l.map fun η => 2 * (η * n)).sum = 2 * (l.sum * n) := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `deg numPoly + 1 < |K| (q - r)`, i.e. `deg Rₙ ≤ -2`. -/
lemma natDegree_numPoly_add_one_lt (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    (P.numPoly n).natDegree + 1 < (P.poleRange n).card * (P.q - P.r) := by
  have hZ : (P.zeroPart n).natDegree ≤ 1 + 2 * (P.zs.sum * n) := by
    unfold zeroPart
    refine natDegree_mul_le.trans ?_
    have h1 : (C (P.h0 n : ℚ) + 2 * X).natDegree ≤ 1 := by compute_degree
    have h2 := natDegree_list_prod_le (P.zs.map (P.zeroPoly n))
    rw [List.map_map] at h2
    have h3 := List.sum_le_sum (l := P.zs) (f := natDegree ∘ P.zeroPoly n)
      (g := fun η => 2 * (η * n)) fun η _ => natDegree_zeroPoly_le n η
    rw [list_sum_map_two_mul] at h3
    omega
  have hPp : ((P.ps.map (P.polePoly n)).prod).natDegree + P.ps.length * (2 * (P.etaMin * n)) ≤
      2 * (P.ps.sum * n) := by
    have h2 := natDegree_list_prod_le (P.ps.map (P.polePoly n))
    rw [List.map_map] at h2
    have h2' := List.sum_le_sum (l := P.ps) (f := natDegree ∘ P.polePoly n)
        (g := fun η => (P.poleRange n \ Finset.Icc (hh η n) (P.h0 n - hh η n)).card)
        fun η _ => natDegree_polePoly_le n η
    have h3 := list_sum_map_add_const P.ps
      (fun η => (P.poleRange n \ Finset.Icc (hh η n) (P.h0 n - hh η n)).card)
      (fun η => 2 * (η * n)) (2 * (P.etaMin * n)) fun η hη => card_sdiff_add hP hn hη
    rw [list_sum_map_two_mul] at h3
    omega
  have hD : (P.numPoly n).natDegree ≤
      (P.zeroPart n).natDegree + ((P.ps.map (P.polePoly n)).prod).natDegree :=
    natDegree_mul_le
  have hsum := hP.sum_lt
  rw [q_sub_r] at hsum ⊢
  have hmul : (2 * (P.zs.sum + P.ps.sum) + 1) * n ≤ P.eta0 * P.ps.length * n :=
    Nat.mul_le_mul_right n hsum
  have hK := card_poleRange hP hn
  have hKL : ((P.poleRange n).card + 2 * (P.etaMin * n)) * P.ps.length =
      (P.eta0 * n + 1) * P.ps.length := by rw [hK]
  have hL : 4 ≤ P.ps.length := by
    have := hP.r_add_four_le_q
    unfold q r at this; omega
  nlinarith

lemma natDegree_numPoly_lt_sum (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    (P.numPoly n).natDegree + 1 < ∑ _i : P.poleRange n, (P.q - P.r) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  exact natDegree_numPoly_add_one_lt hP hn

/-! ### Partial fractions -/

/-- The partial-fraction decomposition (2.1) of `Rₙ`. -/
theorem R_eq_sum (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {t : ℂ}
    (ht : ∀ k ∈ P.poleRange n, t + k ≠ 0) :
    P.R n t = ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r),
      (P.coef n i k : ℂ) / (t + k) ^ i := by
  have heq := eq_sum_of_expansions (fun i : P.poleRange n => -((i : ℕ) : ℚ))
    (injective_neg_coe n) (fun _ => P.q - P.r) (P.numPoly n)
    (by have := natDegree_numPoly_lt_sum hP hn; omega) (fun i => P.expan n i) (hg_expan n)
  unfold R
  rw [eval_map_algebraMap, heq, map_sum, Finset.sum_div,
    ← Finset.sum_coe_sort (P.poleRange n)
      (fun k => ∑ i ∈ Finset.Icc 1 (P.q - P.r), (P.coef n i k : ℂ) / (t + k) ^ i),
    ← Finset.prod_coe_sort (P.poleRange n) (fun k => (t + (k : ℂ)) ^ (P.q - P.r))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : t + ((i : ℕ) : ℂ) ≠ 0 := ht i i.2
  have hQ : ∏ j ∈ Finset.univ.erase i, (t + ((j : ℕ) : ℂ)) ^ (P.q - P.r) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (ht j j.2)
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k : P.poleRange n => (t + ((k : ℕ) : ℂ)) ^ (P.q - P.r)) (Finset.mem_univ i)]
  simp only [map_sum, map_mul, map_pow, map_sub, map_prod, aeval_C, aeval_X, eq_ratCast,
    Rat.cast_neg, Rat.cast_natCast, sub_neg_eq_add]
  rw [mul_div_mul_right _ _ hQ, Finset.sum_div]
  refine Finset.sum_nbij' (fun j => P.q - P.r - j) (fun j => P.q - P.r - j) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    simp only [Finset.mem_range]
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    omega
  · intro j hj
    have hj' : j < P.q - P.r := Finset.mem_range.1 hj
    have hp : (t + ((i : ℕ) : ℂ)) ^ (P.q - P.r) =
        (t + ((i : ℕ) : ℂ)) ^ (P.q - P.r - j) * (t + ((i : ℕ) : ℂ)) ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj'.le]
    rw [hp, mul_div_mul_right _ _ (pow_ne_zero _ hx), coef, Nat.sub_sub_self hj'.le]

/-- The residues of `Rₙ` sum to zero (`deg Rₙ ≤ -2`). -/
theorem sum_coef_one (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ P.poleRange n, P.coef n 1 k = 0 := by
  have hμ : 1 ≤ P.q - P.r := by have := hP.r_add_four_le_q; omega
  have h := sum_residues_eq_zero_of_expansions (fun i : P.poleRange n => -((i : ℕ) : ℚ))
    (injective_neg_coe n) (fun _ => P.q - P.r) (fun _ => hμ) (P.numPoly n)
    (natDegree_numPoly_lt_sum hP hn) (fun i => P.expan n i) (hg_expan n)
  rw [← Finset.sum_coe_sort]
  exact h

/-! ### The symmetry `t ↦ -t - h₀` -/

lemma prod_reflect_of_symm {M : Type*} [CommMonoid M] (S : Finset ℕ) (m : ℕ)
    (hS : ∀ k ∈ S, k ≤ m ∧ m - k ∈ S) (f : ℕ → M) : ∏ k ∈ S, f (m - k) = ∏ k ∈ S, f k :=
  Finset.prod_nbij' (fun k => m - k) (fun k => m - k) (fun k hk => (hS k hk).2)
    (fun k hk => (hS k hk).2) (fun k hk => by have := (hS k hk).1; omega)
    (fun k hk => by have := (hS k hk).1; omega) (fun _ _ => rfl)

lemma sum_reflect_of_symm {M : Type*} [AddCommMonoid M] (S : Finset ℕ) (m : ℕ)
    (hS : ∀ k ∈ S, k ≤ m ∧ m - k ∈ S) (f : ℕ → M) : ∑ k ∈ S, f (m - k) = ∑ k ∈ S, f k :=
  Finset.sum_nbij' (fun k => m - k) (fun k => m - k) (fun k hk => (hS k hk).2)
    (fun k hk => (hS k hk).2) (fun k hk => by have := (hS k hk).1; omega)
    (fun k hk => by have := (hS k hk).1; omega) (fun _ _ => rfl)

lemma X_add_C_comp_reflect (i m : ℕ) (h : i ≤ m) :
    (X + C (i : ℚ)).comp (-X - C (m : ℚ)) = -(X + C ((m - i : ℕ) : ℚ)) := by
  simp only [add_comp, X_comp, C_comp, Nat.cast_sub h, map_sub]
  ring

lemma pochPoly_comp (a b m : ℕ) (hb : b ≤ m + 1) :
    (pochPoly a b).comp (-X - C (m : ℚ)) = (-1) ^ (b - a) * pochPoly (m + 1 - b) (m + 1 - a) := by
  unfold pochPoly
  rw [prod_comp, Finset.prod_congr rfl fun i hi => X_add_C_comp_reflect i m
    (by simp only [Finset.mem_Ico] at hi; omega), Finset.prod_neg, Nat.card_Ico]
  rw [Finset.prod_Ico_reflect (fun j => X + C (j : ℚ)) a hb]

lemma zeroPoly_comp {n η : ℕ} (h : hh η n ≤ P.h0 n) :
    (P.zeroPoly n η).comp (-X - C (P.h0 n : ℚ)) = P.zeroPoly n η := by
  have h1 : 1 ≤ hh η n := by unfold hh; omega
  unfold zeroPoly
  rw [mul_comp, mul_comp, C_comp, pochPoly_comp _ _ _ (by omega), pochPoly_comp _ _ _ (by omega),
    show P.h0 n + 1 - hh η n = P.h0 n - hh η n + 1 by omega,
    show P.h0 n + 1 - 1 = P.h0 n by omega, show P.h0 n + 1 - P.h0 n = 1 by omega,
    show P.h0 n + 1 - (P.h0 n - hh η n + 1) = hh η n by omega,
    show P.h0 n - (P.h0 n - hh η n + 1) = hh η n - 1 by omega]
  have hs : ((-1 : ℚ[X])) ^ (hh η n - 1) * (-1) ^ (hh η n - 1) = 1 := by
    rw [← mul_pow]; simp
  linear_combination (C (((η * n).factorial : ℚ)⁻¹ ^ 2) * pochPoly 1 (hh η n) *
    pochPoly (P.h0 n - hh η n + 1) (P.h0 n)) * hs

lemma polePoly_comp (hP : P.Valid) {n η : ℕ} (hn : 1 ≤ n) (hη : η ∈ P.ps) :
    (P.polePoly n η).comp (-X - C (P.h0 n : ℚ)) = P.polePoly n η := by
  set S := P.poleRange n \ Finset.Icc (hh η n) (P.h0 n - hh η n) with hSdef
  have h2 := two_hh_lt hP hn hη
  have hS : ∀ k ∈ S, k ≤ P.h0 n ∧ P.h0 n - k ∈ S := by
    intro k hk
    rw [hSdef, Finset.mem_sdiff, Finset.mem_Icc] at hk ⊢
    obtain ⟨hk1, hk2⟩ := reflect_mem_poleRange hk.1
    refine ⟨hk1, hk2, ?_⟩
    omega
  have hcard : Even S.card := by
    have := card_sdiff_add hP hn hη
    rw [← hSdef] at this
    exact ⟨η * n - P.etaMin * n, by omega⟩
  unfold polePoly
  rw [mul_comp, C_comp, prod_comp, ← hSdef, Finset.prod_congr rfl fun k hk => X_add_C_comp_reflect
    k (P.h0 n) (hS k hk).1, Finset.prod_neg, hcard.neg_one_pow, one_mul,
    prod_reflect_of_symm S (P.h0 n) hS (fun k => X + C (k : ℚ))]

/-- `Rₙ(-t - h₀) = -Rₙ(t)`, numerator version. -/
lemma numPoly_comp (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    (P.numPoly n).comp (-X - C (P.h0 n : ℚ)) = -P.numPoly n := by
  unfold numPoly zeroPart
  simp only [mul_comp, list_prod_comp, List.map_map]
  have hz : P.zs.map ((fun p => p.comp (-X - C (P.h0 n : ℚ))) ∘ P.zeroPoly n) =
      P.zs.map (P.zeroPoly n) := by
    refine List.map_congr_left fun η hη => zeroPoly_comp ?_
    have := hh_le_hh (n := n) (hP.zs_le_etaMin η hη)
    have := two_hh_lt hP hn hP.etaMin_mem
    omega
  have hp : P.ps.map ((fun p => p.comp (-X - C (P.h0 n : ℚ))) ∘ P.polePoly n) =
      P.ps.map (P.polePoly n) :=
    List.map_congr_left fun η hη => polePoly_comp hP hn hη
  have hl : (C (P.h0 n : ℚ) + 2 * X).comp (-X - C (P.h0 n : ℚ)) = -(C (P.h0 n : ℚ) + 2 * X) := by
    simp only [add_comp, C_comp, mul_comp, X_comp, ofNat_comp]
    ring
  rw [hz, hp, hl]
  ring

lemma taylor_numPoly_reflect (hP : P.Valid) {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ P.h0 n) :
    taylor (-((P.h0 n - k : ℕ) : ℚ)) (P.numPoly n) =
      -((taylor (-(k : ℚ)) (P.numPoly n)).comp (-X)) := by
  have h := numPoly_comp hP hn
  rw [taylor_apply, taylor_apply, comp_assoc]
  conv_lhs => rw [← neg_neg (P.numPoly n), ← h]
  rw [neg_comp, comp_assoc]
  congr 2
  simp only [sub_comp, neg_comp, X_comp, C_comp, add_comp, Nat.cast_sub hk, map_neg, map_sub]
  ring

lemma coe_comp_neg_X (p : ℚ[X]) :
    ((p.comp (-X) : ℚ[X]) : PowerSeries ℚ) = PowerSeries.rescale (-1) (p : PowerSeries ℚ) := by
  have : (coeToPowerSeries.ringHom : ℚ[X] →+* PowerSeries ℚ).comp (compRingHom (-X)) =
      (PowerSeries.rescale (-1)).comp coeToPowerSeries.ringHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · ext m
      simp only [RingHom.coe_comp, Function.comp_apply, coeToPowerSeries.ringHom_apply,
        PowerSeries.coeff_rescale, coeff_coe, coe_compRingHom_apply, C_comp, coeff_C]
      split_ifs with hm <;> simp [hm]
    · simp [coeToPowerSeries.ringHom_apply]
  exact RingHom.congr_fun this p

lemma rescale_C_add_X (a : ℚ) :
    PowerSeries.rescale (-1) (PowerSeries.C a + PowerSeries.X) =
      PowerSeries.C a - PowerSeries.X := by
  rw [map_add, PowerSeries.rescale_neg_one_X, sub_eq_add_neg]
  congr 1
  ext m
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with hm <;> simp [hm]

lemma locDen_reflect (hP : P.Valid) {n k : ℕ} (hk : k ∈ P.poleRange n) :
    P.locDen n (P.h0 n - k) ^ (P.q - P.r) =
      PowerSeries.rescale (-1) (P.locDen n k ^ (P.q - P.r)) := by
  obtain ⟨hk0, hk'⟩ := reflect_mem_poleRange hk
  have h1 : P.locDen n (P.h0 n - k) = (-1) ^ ((P.poleRange n).erase k).card *
      PowerSeries.rescale (-1) (P.locDen n k) := by
    rw [locDen, locDen, map_prod, ← Finset.prod_neg]
    refine Finset.prod_nbij' (fun j => P.h0 n - j) (fun j => P.h0 n - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_erase] at hj ⊢
      obtain ⟨hj1, hj2⟩ := reflect_mem_poleRange hj.2
      exact ⟨by omega, hj2⟩
    · intro j hj
      rw [Finset.mem_erase] at hj ⊢
      obtain ⟨hj1, hj2⟩ := reflect_mem_poleRange hj.2
      exact ⟨by omega, hj2⟩
    · intro j hj
      have := (reflect_mem_poleRange (Finset.mem_erase.1 hj).2).1
      omega
    · intro j hj
      have := (reflect_mem_poleRange (Finset.mem_erase.1 hj).2).1
      omega
    · intro j hj
      have hj0 := (reflect_mem_poleRange (Finset.mem_erase.1 hj).2).1
      rw [rescale_C_add_X, Nat.cast_sub hj0, Nat.cast_sub hk0]
      simp only [map_sub]
      ring
  have heven : Even (P.q - P.r) := Nat.Odd.sub_odd hP.q_odd hP.r_odd
  rw [h1, mul_pow, map_pow, ← pow_mul, mul_comm _ (P.q - P.r), pow_mul, heven.neg_one_pow,
    one_pow, one_mul]

/-- The symmetry `a_{i,k} = (-1)^{i+1} a_{i,h₀-k}` (Lemma 2.2 of the note), from
`Rₙ(-t-h₀) = -Rₙ(t)`. -/
theorem coef_symm (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {i k : ℕ} (hi : i ≤ P.q - P.r)
    (hk : k ∈ P.poleRange n) :
    P.coef n i (P.h0 n - k) = (-1) ^ (i + 1) * P.coef n i k := by
  obtain ⟨hk0, _⟩ := reflect_mem_poleRange hk
  have h1 := expan_mul (P := P) n (P.h0 n - k)
  have h2 := expan_mul (P := P) n k
  rw [taylor_numPoly_reflect hP hn hk0, Polynomial.coe_neg, coe_comp_neg_X, ← h2, map_mul,
    locDen_reflect hP hk] at h1
  have hne : PowerSeries.rescale (-1) (P.locDen n k ^ (P.q - P.r)) ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.coeff 0) h
    rw [PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_pow, map_zero] at this
    exact pow_ne_zero _ (constantCoeff_locDen_ne_zero n k) this
  have h3 : P.expan n (P.h0 n - k) = -PowerSeries.rescale (-1) (P.expan n k) := by
    apply mul_right_cancel₀ hne
    rw [h1]; ring
  have heven : Even (P.q - P.r) := Nat.Odd.sub_odd hP.q_odd hP.r_odd
  unfold coef
  rw [h3, map_neg, PowerSeries.coeff_rescale]
  have hsign : ((-1 : ℚ)) ^ (P.q - P.r - i) = (-1) ^ i := by
    obtain ⟨m, hm⟩ := heven
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := i)]
    congr 1; omega
  rw [hsign, pow_succ]
  ring

/-! ### The linear form `Fₙ` -/

lemma summable_one_div_add_one_pow {s : ℕ} (hs : 2 ≤ s) :
    Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ s := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < s))
  simpa [Nat.cast_add, Nat.cast_one] using this

lemma summable_shift {s : ℕ} (d : ℕ) (hs : 2 ≤ s) :
    Summable fun j : ℕ => 1 / (((j + d : ℕ) : ℝ) + 1) ^ s :=
  (summable_nat_add_iff d).mpr (summable_one_div_add_one_pow hs)

/-- `∑_{j ≥ 0} (j + d + 1)^{-s} = ζ(s) - ∑_{l=1}^{d} l^{-s}`. -/
lemma tsum_shift {s : ℕ} (d : ℕ) (hs : 2 ≤ s) :
    ∑' j : ℕ, 1 / (((j + d : ℕ) : ℝ) + 1) ^ s =
      zetaR s - ∑ l ∈ Finset.Icc 1 d, ((l : ℝ) ^ s)⁻¹ := by
  have h2 := (summable_one_div_add_one_pow hs).sum_add_tsum_nat_add d
  have h3 : ∑ i ∈ Finset.range d, 1 / ((i : ℝ) + 1) ^ s =
      ∑ l ∈ Finset.Icc 1 d, ((l : ℝ) ^ s)⁻¹ := by
    refine Finset.sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; simp only [Finset.mem_range]; omega
    · intro i _; simp
    · intro i hi; simp only [Finset.mem_Icc] at hi; omega
    · intro i _; push_cast; rw [one_div]
  unfold zetaR
  rw [← h2, ← h3]
  ring

lemma sum_coef_even (hP : P.Valid) {n i : ℕ} (hn : 1 ≤ n) (hi : i ≤ P.q - P.r) (he : Even i) :
    ∑ k ∈ P.poleRange n, P.coef n i k = 0 := by
  have h := sum_reflect_of_symm (P.poleRange n) (P.h0 n) (fun k hk => reflect_mem_poleRange hk)
    (P.coef n i)
  rw [Finset.sum_congr rfl fun k hk => coef_symm hP hn hi hk, ← Finset.mul_sum, pow_succ,
    he.neg_one_pow] at h
  linarith

/-- **Lemma 2.2**: `Fₙ` is a linear form in `1` and the odd zeta values `ζ(r+2), …, ζ(q-2)`. -/
theorem F_eq (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    P.F n = ∑ s ∈ P.oddRange, (P.coefZeta n s : ℝ) * zetaR s - P.coefConst n := by
  have hr3 := hP.three_le_r
  have hrq := hP.r_add_four_le_q
  have hK1 : ∀ k ∈ P.poleRange n, hh P.etaOne n ≤ k := by
    intro k hk
    have := hh_le_hh (n := n) (hP.zs_le_etaMin _ hP.etaOne_mem)
    rw [mem_poleRange] at hk; omega
  have hrho : ∀ j : ℕ, (P.rho n ((j : ℤ) + 1 - hh P.etaOne n) : ℝ) =
      ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r),
        ((((i + P.r - 2).choose (P.r - 1) : ℚ) * P.coef n i k : ℚ) : ℝ) *
          (1 / (((j + (k - hh P.etaOne n) : ℕ) : ℝ) + 1) ^ (i + P.r - 1)) := by
    intro j
    unfold rho
    push_cast
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (hK1 k hk)]
    ring
  have hF : P.F n = ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r),
      ((((i + P.r - 2).choose (P.r - 1) : ℚ) * P.coef n i k : ℚ) : ℝ) *
        (zetaR (i + P.r - 1) -
          ∑ l ∈ Finset.Icc 1 (k - hh P.etaOne n), ((l : ℝ) ^ (i + P.r - 1))⁻¹) := by
    unfold F
    rw [tsum_congr hrho, Summable.tsum_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Summable.tsum_finsetSum]
      · refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : 2 ≤ i + P.r - 1 := by simp only [Finset.mem_Icc] at hi; omega
        rw [Summable.tsum_mul_left _ (summable_shift _ hi'), tsum_shift _ hi']
      · intro i hi
        have hi' : 2 ≤ i + P.r - 1 := by simp only [Finset.mem_Icc] at hi; omega
        exact (summable_shift _ hi').mul_left _
    · intro k _
      refine summable_sum fun i hi => ?_
      have hi' : 2 ≤ i + P.r - 1 := by simp only [Finset.mem_Icc] at hi; omega
      exact (summable_shift _ hi').mul_left _
  have hB : ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r),
      ((((i + P.r - 2).choose (P.r - 1) : ℚ) * P.coef n i k : ℚ) : ℝ) *
        ∑ l ∈ Finset.Icc 1 (k - hh P.etaOne n), ((l : ℝ) ^ (i + P.r - 1))⁻¹ =
      (P.coefConst n : ℝ) := by
    unfold coefConst
    push_cast
    rfl
  have hodd := Nat.odd_iff.1 hP.r_odd
  have hqodd := Nat.odd_iff.1 hP.q_odd
  have hsub : P.oddRange ⊆ Finset.Icc P.r (P.q - 1) := by
    intro s hs
    simp only [oddRange, Finset.mem_filter, Finset.mem_Icc] at hs
    simp only [Finset.mem_Icc]
    omega
  have hvanish : ∀ s ∈ Finset.Icc P.r (P.q - 1), s ∉ P.oddRange →
      (P.coefZeta n s : ℝ) * zetaR s = 0 := by
    intro s hs hns
    simp only [oddRange, Finset.mem_filter, Finset.mem_Icc, Nat.odd_iff, not_and] at hs hns
    have : ∑ k ∈ P.poleRange n, P.coef n (s + 1 - P.r) k = 0 := by
      rcases em (s = P.r) with h | h
      · rw [h, show P.r + 1 - P.r = 1 by omega]
        exact sum_coef_one hP hn
      · refine sum_coef_even hP hn (by omega) ?_
        rw [Nat.even_iff]
        omega
    rw [coefZeta, this, mul_zero, Rat.cast_zero, zero_mul]
  have hA : ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r),
      ((((i + P.r - 2).choose (P.r - 1) : ℚ) * P.coef n i k : ℚ) : ℝ) * zetaR (i + P.r - 1) =
      ∑ s ∈ P.oddRange, (P.coefZeta n s : ℝ) * zetaR s := by
    rw [Finset.sum_subset hsub hvanish, Finset.sum_comm]
    refine Finset.sum_nbij' (fun i => i + P.r - 1) (fun s => s + 1 - P.r) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
    · intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi; omega
    · intro s hs; simp only [Finset.mem_Icc] at hs; omega
    · intro i hi
      simp only [Finset.mem_Icc] at hi
      rw [coefZeta, show i + P.r - 1 - 1 = i + P.r - 2 by omega,
        show i + P.r - 1 + 1 - P.r = i by omega]
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
  rw [hF]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hA, hB]


end Params

end OddZeta
