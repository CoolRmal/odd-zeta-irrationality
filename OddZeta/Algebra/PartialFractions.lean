import Mathlib

/-!
# Partial fractions with coefficients read off from local expansions

Let `K` be a field, `s : ι → K` injective, `μ : ι → ℕ`, `D = ∏ᵢ (X - sᵢ) ^ μᵢ` and `N : K[X]` with
`deg N < deg D`. Suppose `gᵢ ∈ K⟦ε⟧` is the expansion at `sᵢ` of `N / ∏_{j ≠ i} (X - sⱼ) ^ μⱼ`, i.e.
`gᵢ · ∏_{j ≠ i} (C (sᵢ - sⱼ) + ε) ^ μⱼ = N (sᵢ + ε)`. Then

* `eq_sum_of_expansions`: `N = ∑ᵢ Tᵢ · ∏_{j ≠ i} (X - sⱼ) ^ μⱼ`, where
  `Tᵢ = ∑_{j < μᵢ} coeff_j (gᵢ) (X - sᵢ) ^ j`;
* `eval_div_prod_eq_sum_of_expansions`: the partial-fraction decomposition of `N / D` evaluated at
  any `t` which is not a pole;
* `sum_residues_eq_zero_of_expansions`: if `deg N + 1 < deg D` (and all `μᵢ ≥ 1`), the residues
  `coeff_{μᵢ - 1} (gᵢ)` sum to zero.
-/

namespace OddZeta
open Polynomial

section Aux

variable {K : Type*} [Field K]

/-- If `X ^ n` divides the Taylor expansion of `F` at `a`, then `(X - a) ^ n` divides `F`. -/
lemma X_sub_C_pow_dvd_of_X_pow_dvd_taylor {a : K} {n : ℕ} {F : K[X]}
    (h : (X : K[X]) ^ n ∣ taylor a F) : (X - C a) ^ n ∣ F := by
  obtain ⟨R, hR⟩ := h
  refine ⟨taylor (-a) R, ?_⟩
  have := congrArg (taylor (-a)) hR
  rwa [taylor_taylor, neg_add_cancel, taylor_zero, taylor_mul, taylor_pow, taylor_X, map_neg,
    ← sub_eq_add_neg] at this

/-- The local step: if `g` is the expansion at `a` of `N / Q`, then `N` agrees with `T * Q`
modulo `(X - a) ^ n`, where `T` is the truncation of `g` at order `n`, re-expanded around `a`. -/
lemma X_sub_C_pow_dvd_sub_of_expansion (a : K) (n : ℕ) (g : PowerSeries K) (Q N : K[X])
    (hg : g * (taylor a Q : PowerSeries K) = (taylor a N : PowerSeries K)) :
    (X - C a) ^ n ∣
      N - (∑ j ∈ Finset.range n, C (PowerSeries.coeff j g) * (X - C a) ^ j) * Q := by
  apply X_sub_C_pow_dvd_of_X_pow_dvd_taylor
  rw [X_pow_dvd_iff]
  intro d hd
  have hT : taylor a (∑ j ∈ Finset.range n, C (PowerSeries.coeff j g) * (X - C a) ^ j) =
      ∑ j ∈ Finset.range n, C (PowerSeries.coeff j g) * X ^ j := by
    simp [map_sum]
  rw [map_sub, taylor_mul, hT, coeff_sub, ← Polynomial.coeff_coe (taylor a N), ← hg,
    PowerSeries.coeff_mul, coeff_mul, sub_eq_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp1 : p.1 < n := by
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    omega
  simp [finsetSum_coeff, hp1]

lemma natDegree_sum_C_mul_X_sub_C_pow_le (a : K) (n : ℕ) (c : ℕ → K) :
    (∑ j ∈ Finset.range n, C (c j) * (X - C a) ^ j).natDegree ≤ n - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have hj' : j < n := Finset.mem_range.1 hj
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_pow, natDegree_X_sub_C]
  omega

lemma coeff_sum_C_mul_X_sub_C_pow_pred (a : K) (n : ℕ) (hn : 1 ≤ n) (c : ℕ → K) :
    (∑ j ∈ Finset.range n, C (c j) * (X - C a) ^ j).coeff (n - 1) = c (n - 1) := by
  rw [finsetSum_coeff, Finset.sum_eq_single (n - 1)]
  · have h1 := ((monic_X_sub_C a).pow (n - 1)).coeff_natDegree
    rw [natDegree_pow, natDegree_X_sub_C, mul_one] at h1
    rw [coeff_C_mul, h1, mul_one]
  · intro j hj hne
    have hj' : j < n := Finset.mem_range.1 hj
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [natDegree_pow, natDegree_X_sub_C]
    omega
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

variable {ι : Type*}

lemma monic_prod_X_sub_C_pow (S : Finset ι) (s : ι → K) (μ : ι → ℕ) :
    (∏ j ∈ S, (X - C (s j)) ^ μ j).Monic :=
  monic_prod_of_monic _ _ fun j _ => (monic_X_sub_C (s j)).pow (μ j)

lemma natDegree_prod_X_sub_C_pow (S : Finset ι) (s : ι → K) (μ : ι → ℕ) :
    (∏ j ∈ S, (X - C (s j)) ^ μ j).natDegree = ∑ j ∈ S, μ j := by
  rw [natDegree_prod_of_monic _ _ fun j _ => (monic_X_sub_C (s j)).pow (μ j)]
  simp [natDegree_pow]

end Aux

/-- Partial fractions, polynomial form: if `gᵢ` is the expansion at `sᵢ` of
`N / ∏_{j ≠ i} (X - sⱼ) ^ μⱼ`, then
`N = ∑ᵢ (∑_{j < μᵢ} coeff_j (gᵢ) (X - sᵢ) ^ j) · ∏_{j ≠ i} (X - sⱼ) ^ μⱼ`. -/
theorem eq_sum_of_expansions {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (s : ι → K) (hs : Function.Injective s) (μ : ι → ℕ) (N : K[X])
    (hN : N.natDegree < ∑ i, μ i)
    (g : ι → PowerSeries K)
    (hg : ∀ i, g i * ∏ j ∈ Finset.univ.erase i,
        (PowerSeries.C (s i - s j) + PowerSeries.X) ^ μ j =
          ((Polynomial.taylor (s i) N : K[X]) : PowerSeries K)) :
    N = ∑ i, (∑ j ∈ Finset.range (μ i), C (PowerSeries.coeff j (g i)) * (X - C (s i)) ^ j) *
      ∏ j ∈ Finset.univ.erase i, (X - C (s j)) ^ μ j := by
  set T : ι → K[X] := fun i =>
    ∑ j ∈ Finset.range (μ i), C (PowerSeries.coeff j (g i)) * (X - C (s i)) ^ j with hT
  set Q : ι → K[X] := fun i => ∏ j ∈ Finset.univ.erase i, (X - C (s j)) ^ μ j with hQ
  change N = ∑ i, T i * Q i
  rw [← sub_eq_zero]
  have hdvd : ∏ i, (X - C (s i)) ^ μ i ∣ N - ∑ i, T i * Q i := by
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      exact (pairwise_coprime_X_sub_C hs hij).pow
    · intro i
      have hQt : ((taylor (s i) (Q i) : K[X]) : PowerSeries K) =
          ∏ j ∈ Finset.univ.erase i, (PowerSeries.C (s i - s j) + PowerSeries.X) ^ μ j := by
        have h1 : taylor (s i) (Q i) = ∏ j ∈ Finset.univ.erase i, (C (s i - s j) + X) ^ μ j := by
          change taylorAlgHom (s i) (∏ j ∈ Finset.univ.erase i, (X - C (s j)) ^ μ j) = _
          rw [map_prod]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [map_pow]
          change (taylor (s i) (X - C (s j))) ^ μ j = _
          rw [map_sub, taylor_X, taylor_C, map_sub]
          ring
        rw [h1, ← coeToPowerSeries.ringHom_apply, map_prod]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp [coeToPowerSeries.ringHom_apply]
      have h1 : (X - C (s i)) ^ μ i ∣ N - T i * Q i :=
        X_sub_C_pow_dvd_sub_of_expansion (s i) (μ i) (g i) (Q i) N (by rw [hQt]; exact hg i)
      have h2 : (X - C (s i)) ^ μ i ∣ ∑ k ∈ Finset.univ.erase i, T k * Q k := by
        refine Finset.dvd_sum fun k hk => ?_
        refine Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ ?_) _
        simpa [eq_comm] using (Finset.mem_erase.1 hk).1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      convert dvd_sub h1 h2 using 1
      ring
  refine eq_zero_of_dvd_of_natDegree_lt hdvd ?_
  rw [natDegree_prod_X_sub_C_pow]
  refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hN ?_)
  have hpos : 0 < ∑ i, μ i := lt_of_le_of_lt (Nat.zero_le _) hN
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := ∑ i, μ i - 1) fun i _ => ?_)
    (by omega)
  rcases Nat.eq_zero_or_pos (μ i) with h0 | h0
  · simp [hT, h0]
  refine natDegree_mul_le.trans ?_
  have h1 : (T i).natDegree ≤ μ i - 1 := natDegree_sum_C_mul_X_sub_C_pow_le (s i) (μ i) _
  have h3 : (Q i).natDegree = ∑ j ∈ Finset.univ.erase i, μ j := natDegree_prod_X_sub_C_pow _ s μ
  have h2 := Finset.add_sum_erase Finset.univ μ (Finset.mem_univ i)
  omega

/-- Partial-fraction decomposition of `N / ∏ᵢ (X - sᵢ) ^ μᵢ`, evaluated at a point `t` which is
not a pole, with coefficients read off from the local expansions `gᵢ`. -/
theorem eval_div_prod_eq_sum_of_expansions {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (s : ι → K) (hs : Function.Injective s) (μ : ι → ℕ) (N : K[X])
    (hN : N.natDegree < ∑ i, μ i)
    (g : ι → PowerSeries K)
    (hg : ∀ i, g i * ∏ j ∈ Finset.univ.erase i,
        (PowerSeries.C (s i - s j) + PowerSeries.X) ^ μ j =
          ((Polynomial.taylor (s i) N : K[X]) : PowerSeries K))
    (t : K) (ht : ∀ i, t ≠ s i) :
    N.eval t / ∏ i, (t - s i) ^ μ i =
      ∑ i, ∑ j ∈ Finset.range (μ i), PowerSeries.coeff j (g i) * (t - s i) ^ j / (t - s i) ^ μ i := by
  have hti : ∀ i, t - s i ≠ 0 := fun i => sub_ne_zero.2 (ht i)
  rw [eq_sum_of_expansions s hs μ N hN g hg, eval_finsetSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : ∏ j ∈ Finset.univ.erase i, (t - s j) ^ μ j ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hti j)
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (t - s j) ^ μ j) (Finset.mem_univ i)]
  simp only [eval_mul, eval_prod, eval_finsetSum, eval_pow, eval_sub, eval_X, eval_C]
  rw [mul_div_mul_right _ _ hne, Finset.sum_div]

/-- Sum of residues: if `deg N + 1 < deg D` and all `μᵢ ≥ 1`, then the residues
`coeff_{μᵢ - 1} (gᵢ)` of `N / D` sum to zero. -/
theorem sum_residues_eq_zero_of_expansions {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (s : ι → K) (hs : Function.Injective s) (μ : ι → ℕ) (hμ : ∀ i, 1 ≤ μ i) (N : K[X])
    (hN : N.natDegree + 1 < ∑ i, μ i)
    (g : ι → PowerSeries K)
    (hg : ∀ i, g i * ∏ j ∈ Finset.univ.erase i,
        (PowerSeries.C (s i - s j) + PowerSeries.X) ^ μ j =
          ((Polynomial.taylor (s i) N : K[X]) : PowerSeries K)) :
    ∑ i, PowerSeries.coeff (μ i - 1) (g i) = 0 := by
  have h0 : N.coeff (∑ i, μ i - 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [eq_sum_of_expansions s hs μ N (by omega) g hg, finsetSum_coeff] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 := Finset.add_sum_erase Finset.univ μ (Finset.mem_univ i)
  have hM : ∑ k, μ k - 1 = (μ i - 1) + ∑ k ∈ Finset.univ.erase i, μ k := by
    have := hμ i
    omega
  rw [hM, coeff_mul_add_eq_of_natDegree_le
      (natDegree_sum_C_mul_X_sub_C_pow_le (s i) (μ i) fun j => PowerSeries.coeff j (g i))
      (natDegree_prod_X_sub_C_pow _ s μ).le,
    ← natDegree_prod_X_sub_C_pow (Finset.univ.erase i) s μ,
    (monic_prod_X_sub_C_pow _ s μ).coeff_natDegree, mul_one,
    coeff_sum_C_mul_X_sub_C_pow_pred (s i) (μ i) (hμ i) fun j => PowerSeries.coeff j (g i)]

end OddZeta
