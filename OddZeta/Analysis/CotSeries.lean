import Mathlib

/-!
# The Lipschitz formula for `∑_{m ∈ ℤ} (t - m)^{-r}` as a trigonometric polynomial

For `r ≥ 2` and `Im t ≠ 0` we prove
`(∑_{m ∈ ℤ} (t - m)^{-r}) · sin(πt)^r = π^r · trigS r t`, where
`trigS r t = (1/(r-1)!) ∑_{j=0}^{r-2} A(r-1,j) e^{iπ(2j+2-r)t}` and `A(r-1,j) = eulerCoeff r j`
are the Eulerian numbers.

For `Im t > 0` this follows from the Lipschitz formula
(`EisensteinSeries.qExpansion_identity`) and the generating function identity
`(1-q)^r ∑_{d ≥ 1} d^{r-1} q^d = ∑_{j=0}^{r-2} A(r-1,j) q^{j+1}`; the case `Im t < 0` follows by
complex conjugation, using the symmetry `A(r-1,j) = A(r-1,r-2-j)`. The properties of the
Eulerian numbers (vanishing, symmetry, nonnegativity, sum `(r-1)!`) are all derived from the
recurrence `A(r+1, N+1) = (N+1) A(r, N+1) + (r-N) A(r, N)` for the explicit alternating sums.
-/

namespace OddZeta

open Complex Finset

/-- `eulerCoeff r j = ∑_{i=0}^{j+1} (-1)^i C(r,i) (j+1-i)^(r-1)`, the Eulerian number
`A(r-1, j)`. -/
def eulerCoeff (r j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (j + 2), (-1) ^ i * (r.choose i : ℤ) * ((j + 1 - i : ℕ) : ℤ) ^ (r - 1)

/-- `trigS r t = (1/(r-1)!) ∑_{j=0}^{r-2} A(r-1,j) e^{iπ(2j+2-r)t}`. -/
noncomputable def trigS (r : ℕ) (t : ℂ) : ℂ :=
  ((r - 1).factorial : ℂ)⁻¹ *
    ∑ j ∈ Finset.range (r - 1),
      (eulerCoeff r j : ℂ) * exp (I * Real.pi * ((2 * j + 2 - r : ℤ) : ℂ) * t)

/-! ### Eulerian numbers -/

/-- `eulerNum r N = ∑_{i=0}^{N} (-1)^i C(r,i) (N-i)^(r-1)`, so that
`eulerCoeff r j = eulerNum r (j + 1)`. -/
def eulerNum (r N : ℕ) : ℤ :=
  ∑ i ∈ range (N + 1), (-1) ^ i * (r.choose i : ℤ) * ((N - i : ℕ) : ℤ) ^ (r - 1)

theorem eulerCoeff_eq_eulerNum (r j : ℕ) : eulerCoeff r j = eulerNum r (j + 1) := rfl

/-- `eulerF r N = ∑_{i=0}^{N} (-1)^i C(r,i) (N-i)^r`. -/
private def eulerF (r N : ℕ) : ℤ :=
  ∑ i ∈ range (N + 1), (-1) ^ i * (r.choose i : ℤ) * ((N - i : ℕ) : ℤ) ^ r

/-- `eulerG r N = ∑_{i=0}^{N} (-1)^i i C(r,i) (N-i)^(r-1)`. -/
private def eulerG (r N : ℕ) : ℤ :=
  ∑ i ∈ range (N + 1), (-1) ^ i * (i : ℤ) * (r.choose i : ℤ) * ((N - i : ℕ) : ℤ) ^ (r - 1)

private lemma eulerNum_succ_succ_eq (r M : ℕ) :
    eulerNum (r + 1) (M + 1) = eulerF r (M + 1) - eulerF r M := by
  have h1 : eulerNum (r + 1) (M + 1) = ∑ i ∈ range (M + 1),
      (-1) ^ (i + 1) * ((r.choose i : ℤ) + r.choose (i + 1)) * ((M - i : ℕ) : ℤ) ^ r +
        ((M + 1 : ℕ) : ℤ) ^ r := by
    rw [eulerNum, sum_range_succ']
    simp [Nat.choose_succ_succ']
  have h2 : eulerF r (M + 1) = ∑ i ∈ range (M + 1),
      (-1) ^ (i + 1) * (r.choose (i + 1) : ℤ) * ((M - i : ℕ) : ℤ) ^ r +
        ((M + 1 : ℕ) : ℤ) ^ r := by
    rw [eulerF, sum_range_succ']
    simp
  rw [h1, h2, eulerF, add_sub_right_comm, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  ring

private lemma eulerF_eq (r N : ℕ) (hr : 1 ≤ r) :
    eulerF r N = N * eulerNum r N - eulerG r N := by
  rw [eulerF, eulerNum, eulerG, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi : i ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hi)
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Nat.cast_sub hi]
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

private lemma choose_mul_sub (r i : ℕ) :
    ((r : ℤ) - i) * (r.choose i : ℤ) = (i + 1) * (r.choose (i + 1) : ℤ) := by
  rcases le_or_gt i r with h | h
  · have h' := Nat.choose_succ_right_eq r i
    have h'' : ((r.choose (i + 1) * (i + 1) : ℕ) : ℤ) = ((r.choose i * (r - i) : ℕ) : ℤ) := by
      rw [h']
    push_cast [Nat.cast_sub h] at h''
    linarith
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
    simp

private lemma eulerF_eq' (r M : ℕ) (hr : 1 ≤ r) :
    eulerF r M = -((r : ℤ) - M) * eulerNum r M - eulerG r (M + 1) := by
  have hG : eulerG r (M + 1) = ∑ i ∈ range (M + 1), (-1) ^ (i + 1) * ((i : ℤ) + 1) *
      (r.choose (i + 1) : ℤ) * ((M - i : ℕ) : ℤ) ^ (r - 1) := by
    rw [eulerG, sum_range_succ']
    simp
  rw [hG, eulerF, eulerNum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi : i ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hi)
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hc := choose_mul_sub (s + 1) i
  rw [Nat.cast_sub hi]
  simp only [Nat.add_sub_cancel, pow_succ] at hc ⊢
  linear_combination ((-1 : ℤ) ^ i * ((M : ℤ) - i) ^ s) * hc

/-- The recurrence `A(r+1, N+1) = (N+1) A(r, N+1) + (r - N) A(r, N)` (shifted Eulerian
numbers). -/
theorem eulerNum_succ_succ {r : ℕ} (hr : 1 ≤ r) (M : ℕ) :
    eulerNum (r + 1) (M + 1) =
      (M + 1) * eulerNum r (M + 1) + ((r : ℤ) - M) * eulerNum r M := by
  rw [eulerNum_succ_succ_eq, eulerF_eq _ _ hr, eulerF_eq' _ _ hr]
  push_cast
  ring

theorem eulerNum_zero_left (N : ℕ) : eulerNum 0 N = 1 := by
  simp [eulerNum, sum_range_succ']

theorem eulerNum_zero_right {r : ℕ} (hr : 2 ≤ r) : eulerNum r 0 = 0 := by
  simp [eulerNum, zero_pow (show r - 1 ≠ 0 by omega)]

theorem eulerNum_one_succ (M : ℕ) : eulerNum 1 (M + 1) = 0 := by
  simp [eulerNum, sum_range_succ', Nat.choose_succ_succ']

theorem eulerNum_eq_zero_of_le {r N : ℕ} (hr : 1 ≤ r) (h : r ≤ N) : eulerNum r N = 0 := by
  induction r, hr using Nat.le_induction generalizing N with
  | base =>
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    exact eulerNum_one_succ M
  | succ r hr ih =>
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [eulerNum_succ_succ hr, ih (by omega), ih (by omega)]
    simp

theorem eulerNum_nonneg (r N : ℕ) : 0 ≤ eulerNum r N := by
  rcases r with _ | r
  · simp [eulerNum_zero_left]
  induction r generalizing N with
  | zero =>
    rcases N with _ | M
    · simp [eulerNum]
    · simp [eulerNum_one_succ]
  | succ r ih =>
    rcases N with _ | M
    · rw [eulerNum_zero_right (by omega)]
    by_cases h : r + 2 ≤ M + 1
    · rw [eulerNum_eq_zero_of_le (by omega) h]
    · rw [eulerNum_succ_succ (by omega)]
      have h1 := ih (M + 1)
      have h2 := ih M
      have h3 : (0 : ℤ) ≤ ((r + 1 : ℕ) : ℤ) - M := by push_cast; omega
      positivity

theorem eulerNum_symm {r N : ℕ} (hr : 2 ≤ r) (hN : N ≤ r) : eulerNum r N = eulerNum r (r - N) := by
  induction r, hr using Nat.le_induction generalizing N with
  | base =>
    interval_cases N <;> rfl
  | succ r hr ih =>
    rcases N with _ | M
    · rw [eulerNum_zero_right (by omega), Nat.sub_zero, eulerNum_eq_zero_of_le (by omega) le_rfl]
    rcases Nat.lt_or_ge M r with hM | hM
    · obtain ⟨K, hK⟩ : ∃ K, r + 1 - (M + 1) = K + 1 := ⟨r - M - 1, by omega⟩
      rw [hK, eulerNum_succ_succ (by omega), eulerNum_succ_succ (by omega),
        ih (N := M + 1) (by omega), ih (N := M) (by omega), ih (N := K) (by omega),
        ih (N := K + 1) (by omega)]
      have hK' : K = r - (M + 1) := by omega
      subst hK'
      rw [show r - (r - (M + 1)) = M + 1 by omega, show r - (r - (M + 1) + 1) = M by omega,
        ih (N := M + 1) (by omega), ih (N := M) (by omega)]
      push_cast [Nat.cast_sub (show M + 1 ≤ r by omega)]
      ring
    · obtain rfl : M = r := by omega
      rw [Nat.sub_self, eulerNum_zero_right (by omega),
        eulerNum_eq_zero_of_le (by omega) le_rfl]

theorem sum_eulerNum {r : ℕ} (hr : 1 ≤ r) :
    ∑ N ∈ range r, eulerNum r N = (r - 1).factorial := by
  induction r, hr using Nat.le_induction with
  | base => simp [eulerNum]
  | succ r hr ih =>
    rw [sum_range_succ', eulerNum_zero_right (by omega), add_zero]
    simp_rw [eulerNum_succ_succ hr]
    rw [sum_add_distrib]
    have h1 : ∑ M ∈ range r, ((M : ℤ) + 1) * eulerNum r (M + 1) =
        ∑ N ∈ range r, (N : ℤ) * eulerNum r N := by
      have := sum_range_succ' (fun N => (N : ℤ) * eulerNum r N) r
      rw [sum_range_succ, eulerNum_eq_zero_of_le hr le_rfl] at this
      simp only [mul_zero, add_zero, Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one] at this
      exact this.symm
    rw [h1, ← sum_add_distrib]
    have h2 : ∑ N ∈ range r, ((N : ℤ) * eulerNum r N + ((r : ℤ) - N) * eulerNum r N) =
        r * ∑ N ∈ range r, eulerNum r N := by
      rw [mul_sum]
      exact sum_congr rfl fun N _ => by ring
    rw [h2, ih]
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp [Nat.factorial_succ]

/-! ### The statements about `eulerCoeff` -/

theorem eulerCoeff_symm {r j : ℕ} (hj : j ≤ r - 2) : eulerCoeff r j = eulerCoeff r (r - 2 - j) := by
  rcases lt_or_ge r 2 with hr | hr
  · have : j = 0 := by omega
    subst this
    rw [show r - 2 - 0 = 0 by omega]
  rw [eulerCoeff_eq_eulerNum, eulerCoeff_eq_eulerNum, eulerNum_symm hr (by omega)]
  congr 1
  omega

theorem eulerCoeff_nonneg (r j : ℕ) : 0 ≤ eulerCoeff r j := eulerNum_nonneg r (j + 1)

theorem sum_eulerCoeff {r : ℕ} (hr : 2 ≤ r) :
    ∑ j ∈ Finset.range (r - 1), eulerCoeff r j = (r - 1).factorial := by
  have h := sum_eulerNum (r := r) (by omega)
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [sum_range_succ', eulerNum_zero_right hr, add_zero] at h
  simpa [eulerCoeff_eq_eulerNum] using h

theorem eulerCoeff_zero {r : ℕ} (hr : 2 ≤ r) : eulerCoeff r 0 = 1 := by
  simp [eulerCoeff, sum_range_succ, zero_pow (show r - 1 ≠ 0 by omega)]

theorem eulerCoeff_sub_two {r : ℕ} (hr : 2 ≤ r) : eulerCoeff r (r - 2) = 1 := by
  have h0 := eulerCoeff_zero hr
  rwa [eulerCoeff_symm (r := r) (j := 0) (by omega), Nat.sub_zero] at h0

/-! ### The generating function of the Eulerian numbers -/

/-- `(1 - q)^r ∑_{n ≥ 0} n^(r-1) q^n = ∑_{j=0}^{r-2} A(r-1, j) q^(j+1)` for `‖q‖ < 1`. -/
theorem one_sub_pow_mul_tsum_pow_mul_geometric {r : ℕ} (hr : 2 ≤ r) {q : ℂ} (hq : ‖q‖ < 1) :
    (1 - q) ^ r * ∑' n : ℕ, (n : ℂ) ^ (r - 1) * q ^ n =
      ∑ j ∈ range (r - 1), (eulerCoeff r j : ℂ) * q ^ (j + 1) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℂ, f = fun k => (-1) ^ k * (r.choose k : ℂ) * q ^ k := ⟨_, rfl⟩
  have hf0 : ∀ k ∉ range (r + 1), f k = 0 := fun k hk => by
    simp [hf, Nat.choose_eq_zero_of_lt (show r < k by simpa using hk)]
  have hbin : (1 - q) ^ r = ∑' k, f k := by
    rw [tsum_eq_sum hf0, show (1 - q) = -q + 1 by ring, add_pow]
    refine sum_congr rfl fun k _ => ?_
    rw [hf]
    ring
  have hfs : Summable fun k => ‖f k‖ :=
    summable_of_ne_finset_zero (s := range (r + 1)) fun k hk => by simp [hf0 k hk]
  have hgs := summable_norm_pow_mul_geometric_of_norm_lt_one (r - 1) hq
  rw [hbin, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfs hgs]
  have hterm : ∀ n : ℕ, ∑ k ∈ range (n + 1), f k * (((n - k : ℕ) : ℂ) ^ (r - 1) * q ^ (n - k)) =
      (eulerNum r n : ℂ) * q ^ n := by
    intro n
    rw [eulerNum, Int.cast_sum, sum_mul]
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [hf]
    push_cast
    rw [← pow_mul_pow_sub q hk]
    ring
  simp_rw [hterm]
  rw [tsum_eq_sum (s := range r) fun n hn => by
    rw [eulerNum_eq_zero_of_le (by omega) (by simpa using hn)]; simp]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [sum_range_succ', eulerNum_zero_right hr]
  simp [eulerCoeff_eq_eulerNum]

/-! ### Summability -/

theorem summable_inv_sub_intCast_pow {r : ℕ} (hr : 2 ≤ r) {t : ℂ} (_ht : t.im ≠ 0) :
    Summable (fun m : ℤ => ((t - m) ^ r)⁻¹) := by
  have h := (EisensteinSeries.linear_right_summable t 1 (k := (r : ℤ)) (by omega)).comp_injective
    neg_injective
  refine h.congr fun m => ?_
  simp [sub_eq_add_neg]

theorem summable_norm_inv_sub_intCast_pow {r : ℕ} (hr : 2 ≤ r) {t : ℂ} (ht : t.im ≠ 0) :
    Summable (fun m : ℤ => ‖((t - m) ^ r)⁻¹‖) :=
  summable_norm_iff.mpr (summable_inv_sub_intCast_pow hr ht)

/-! ### Conjugation symmetry of `trigS` -/

theorem trigS_conj (r : ℕ) (t : ℂ) : trigS r (starRingEnd ℂ t) = starRingEnd ℂ (trigS r t) := by
  simp only [trigS, map_mul, map_sum, map_inv₀, map_natCast, map_intCast, ← exp_conj, conj_I,
    conj_ofReal]
  congr 1
  rw [← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj : j < r - 1 := mem_range.mp hj
  rw [eulerCoeff_symm (show r - 1 - 1 - j ≤ r - 2 by omega),
    show r - 2 - (r - 1 - 1 - j) = j by omega]
  congr 2
  push_cast [Nat.cast_sub (show j ≤ r - 1 - 1 by omega), Nat.cast_sub (show 1 ≤ r - 1 by omega),
    Nat.cast_sub (show 1 ≤ r by omega)]
  ring

/-! ### The main identity -/

theorem tsum_inv_sub_intCast_pow_mul_sin_pow_of_im_pos {r : ℕ} (hr : 2 ≤ r) {t : ℂ}
    (ht : 0 < t.im) :
    (∑' m : ℤ, ((t - m) ^ r)⁻¹) * sin (Real.pi * t) ^ r = (Real.pi : ℂ) ^ r * trigS r t := by
  set z : UpperHalfPlane := ⟨t, ht⟩
  set q : ℂ := cexp (2 * Real.pi * I * t) with hq_def
  set e : ℂ := cexp (-(I * Real.pi * t)) with he_def
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  have hid := EisensteinSeries.qExpansion_identity (k := r - 1) (by omega) z
  rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hid
  have hS : ∑' m : ℤ, ((t - m) ^ r)⁻¹ = ∑' n : ℤ, 1 / (t + n) ^ r := by
    rw [← tsum_comp_neg]
    simp [sub_eq_add_neg, one_div]
  have hsin : (-2 * Real.pi * I) * sin (Real.pi * t) = Real.pi * e * (1 - q) := by
    have h1 : e * q = cexp (Real.pi * t * I) := by
      rw [he_def, hq_def, ← exp_add]; ring_nf
    have h2 : e = cexp (-(Real.pi * t) * I) := by rw [he_def]; ring_nf
    rw [Complex.sin]
    linear_combination (-Real.pi * (cexp (-(Real.pi * t) * I) - cexp (Real.pi * t * I))) * I_sq
      - Real.pi * h2 + Real.pi * h1
  have hexp : ∀ j : ℕ,
      cexp (I * Real.pi * ((2 * j + 2 - r : ℤ) : ℂ) * t) = e ^ r * q ^ (j + 1) := by
    intro j
    rw [he_def, hq_def, ← exp_nat_mul, ← exp_nat_mul, ← exp_add]
    congr 1
    push_cast
    ring
  have key := one_sub_pow_mul_tsum_pow_mul_geometric hr hq
  rw [hS, hid, trigS]
  simp_rw [hexp]
  change ((-2 * Real.pi * I) ^ r / ((r - 1).factorial : ℂ) * _) * _ = _
  rw [div_eq_mul_inv]
  calc (-2 * Real.pi * I) ^ r * ((r - 1).factorial : ℂ)⁻¹ *
        (∑' n : ℕ, (n : ℂ) ^ (r - 1) * q ^ n) * sin (Real.pi * t) ^ r
      = ((r - 1).factorial : ℂ)⁻¹ * ((-2 * Real.pi * I) * sin (Real.pi * t)) ^ r *
          ∑' n : ℕ, (n : ℂ) ^ (r - 1) * q ^ n := by ring
    _ = ((r - 1).factorial : ℂ)⁻¹ * (Real.pi ^ r * e ^ r) *
          ((1 - q) ^ r * ∑' n : ℕ, (n : ℂ) ^ (r - 1) * q ^ n) := by
          rw [hsin, mul_pow, mul_pow]; ring
    _ = _ := by
      rw [key, mul_sum, mul_sum, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      ring

theorem tsum_inv_sub_intCast_pow_mul_sin_pow {r : ℕ} (hr : 2 ≤ r) {t : ℂ} (ht : t.im ≠ 0) :
    (∑' m : ℤ, ((t - m) ^ r)⁻¹) * sin (Real.pi * t) ^ r = (Real.pi : ℂ) ^ r * trigS r t := by
  rcases ht.lt_or_gt with h | h
  · have h' : 0 < (starRingEnd ℂ t).im := by simpa using h
    have H := congrArg (starRingEnd ℂ) (tsum_inv_sub_intCast_pow_mul_sin_pow_of_im_pos hr h')
    rw [trigS_conj] at H
    simpa [conj_tsum, ← sin_conj] using H
  · exact tsum_inv_sub_intCast_pow_mul_sin_pow_of_im_pos hr h

/-! ### The dominant mode of `trigS` in the lower half-plane -/

theorem norm_trigS_sub_le {r : ℕ} (hr : 2 ≤ r) {t : ℂ} (ht : t.im ≤ 0) :
    ‖trigS r t - ((r - 1).factorial : ℂ)⁻¹ * exp (I * Real.pi * ((r : ℂ) - 2) * t)‖ ≤
      Real.exp ((r - 4) * Real.pi * (-t.im)) := by
  set X := Real.exp ((r - 4) * Real.pi * (-t.im))
  have hsplit : trigS r t - ((r - 1).factorial : ℂ)⁻¹ * exp (I * Real.pi * ((r : ℂ) - 2) * t) =
      ((r - 1).factorial : ℂ)⁻¹ * ∑ j ∈ range (r - 2),
        (eulerCoeff r j : ℂ) * exp (I * Real.pi * ((2 * j + 2 - r : ℤ) : ℂ) * t) := by
    rw [trigS, show r - 1 = r - 2 + 1 by omega, sum_range_succ, eulerCoeff_sub_two hr]
    push_cast [Nat.cast_sub hr]
    ring_nf
    congr 1
    refine sum_congr rfl fun j _ => ?_
    ring_nf
  have hb : ∀ j ∈ range (r - 2),
      ‖(eulerCoeff r j : ℂ) * exp (I * Real.pi * ((2 * j + 2 - r : ℤ) : ℂ) * t)‖ ≤
        (eulerCoeff r j : ℝ) * X := by
    intro j hj
    have hj : j < r - 2 := mem_range.mp hj
    rw [norm_mul, norm_intCast, abs_of_nonneg (by exact_mod_cast eulerCoeff_nonneg r j),
      norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (by exact_mod_cast eulerCoeff_nonneg r j)
    have hf : (2 * (j : ℝ) + 2 - r) ≤ r - 4 := by
      have : (j : ℝ) + 3 ≤ r := by exact_mod_cast (show j + 3 ≤ r by omega)
      linarith
    simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im, intCast_re, intCast_im, mul_im]
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hf) (mul_nonneg Real.pi_pos.le (neg_nonneg.mpr ht))]
  have hsum : (∑ j ∈ range (r - 2), (eulerCoeff r j : ℝ)) ≤ (r - 1).factorial := by
    have h1 : ∑ j ∈ range (r - 2), eulerCoeff r j ≤ ∑ j ∈ range (r - 1), eulerCoeff r j :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
        fun j _ _ => eulerCoeff_nonneg r j
    rw [sum_eulerCoeff hr] at h1
    exact_mod_cast h1
  rw [hsplit, norm_mul, norm_inv, Complex.norm_natCast]
  have hfac : (0 : ℝ) < (r - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  calc ((r - 1).factorial : ℝ)⁻¹ * ‖∑ j ∈ range (r - 2),
        (eulerCoeff r j : ℂ) * exp (I * Real.pi * ((2 * j + 2 - r : ℤ) : ℂ) * t)‖
      ≤ ((r - 1).factorial : ℝ)⁻¹ * ∑ j ∈ range (r - 2), (eulerCoeff r j : ℝ) * X := by
        gcongr
        exact (norm_sum_le _ _).trans (sum_le_sum hb)
    _ = ((r - 1).factorial : ℝ)⁻¹ * (∑ j ∈ range (r - 2), (eulerCoeff r j : ℝ)) * X := by
        rw [← sum_mul, mul_assoc]
    _ ≤ ((r - 1).factorial : ℝ)⁻¹ * (r - 1).factorial * X := by gcongr
    _ = X := by field_simp


example : (List.range 4).map (eulerCoeff 5) = [1, 11, 11, 1] := by decide
example : (List.range 6).map (eulerCoeff 7) = [1, 57, 302, 302, 57, 1] := by decide

end OddZeta
