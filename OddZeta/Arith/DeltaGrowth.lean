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

section Aux

open Finset

/-! ### Consequences of the prime number theorem -/

/-- If `f x / x → L` then `f (c n + d) / n → c L`. -/
theorem tendsto_comp_mul_add_div {f : ℝ → ℝ} {L : ℝ}
    (hf : Tendsto (fun x => f x / x) atTop (𝓝 L)) {c : ℝ} (hc : 0 < c) (d : ℝ) :
    Tendsto (fun n : ℕ => f (c * n + d) / n) atTop (𝓝 (c * L)) := by
  have h1 : Tendsto (fun n : ℕ => c * (n : ℝ) + d) atTop atTop :=
    tendsto_atTop_add_const_right _ d (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  have h2 : Tendsto (fun n : ℕ => (c * (n : ℝ) + d) / n) atTop (𝓝 c) := by
    have : Tendsto (fun n : ℕ => c + d / (n : ℝ)) atTop (𝓝 (c + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have := (hf.comp h1).mul h2
  rw [mul_comm c L]
  refine this.congr' ?_
  filter_upwards [h1.eventually (eventually_gt_atTop 0), eventually_gt_atTop 0] with n h1n hn
  simp only [Function.comp]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- `θ(c n) / n → c`. -/
theorem tendsto_theta_mul_div {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => Chebyshev.theta (c * n) / n) atTop (𝓝 c) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul, Chebyshev.theta_zero, zero_div]
    exact tendsto_const_nhds
  · simpa only [add_zero, mul_one] using tendsto_comp_mul_add_div tendsto_theta_div_atTop hc 0

/-- `log (c n) / n → 0`. -/
theorem tendsto_log_mul_div {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log (c * n) / n) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [id] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simpa only [add_zero, mul_zero] using tendsto_comp_mul_add_div h hc 0

/-- `(ψ - θ)(c n + d) / n → 0`. -/
theorem tendsto_psi_sub_theta_div {c : ℝ} (hc : 0 < c) (d : ℝ) :
    Tendsto (fun n : ℕ => (Chebyshev.psi (c * n + d) - Chebyshev.theta (c * n + d)) / n)
      atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x) atTop (𝓝 0) := by
    have := tendsto_psi_div_atTop.sub tendsto_theta_div_atTop
    rw [sub_self] at this
    simpa only [sub_div] using this
  simpa only [mul_zero] using tendsto_comp_mul_add_div h hc d

/-- `θ(y) - θ(x) - log y ≤ ∑_{p ∈ S} log p` if `S` contains the primes in `(x, y)`. -/
theorem theta_sub_theta_sub_log_le {x y : ℝ} (hy : 1 ≤ y) {S : Finset ℕ}
    (hS : ∀ p : ℕ, p.Prime → x < p → (p : ℝ) < y → p ∈ S) :
    Chebyshev.theta y - Chebyshev.theta x - Real.log y ≤ ∑ p ∈ S, Real.log p := by
  rw [Chebyshev.theta_eq_sum_primesLE y, Chebyshev.theta_eq_sum_primesLE x]
  set G := Nat.primesLE ⌊y⌋₊
  have key : ∀ p ∈ G, Real.log p ≤ ((if (p : ℝ) ≤ x then Real.log p else 0) +
      (if p ∈ S then Real.log p else 0)) + (if p = ⌊y⌋₊ then Real.log p else 0) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have h0 := Real.log_natCast_nonneg p
    by_cases h1 : (p : ℝ) ≤ x
    · split_ifs <;> linarith
    by_cases h2 : (p : ℝ) < y
    · have h3 := hS p hp.2 (not_le.mp h1) h2
      split_ifs <;> linarith
    · have h3 : p = ⌊y⌋₊ := le_antisymm hp.1 (Nat.floor_le_of_le (not_lt.mp h2))
      split_ifs <;> linarith
  have hy0 : 0 ≤ y := by linarith
  suffices ∑ p ∈ G, Real.log p ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p + ∑ p ∈ S, Real.log p + Real.log y by linarith
  calc ∑ p ∈ G, Real.log p
      ≤ ∑ p ∈ G, (((if ((p : ℕ) : ℝ) ≤ x then Real.log p else 0) +
        (if p ∈ S then Real.log p else 0)) + (if p = ⌊y⌋₊ then Real.log p else 0)) :=
        sum_le_sum key
    _ = ∑ p ∈ G with ((p : ℕ) : ℝ) ≤ x, Real.log p + ∑ p ∈ G with p ∈ S, Real.log p +
        ∑ p ∈ G, (if p = ⌊y⌋₊ then Real.log p else 0) := by
        rw [sum_add_distrib, sum_add_distrib, sum_filter, sum_filter]
    _ ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p + ∑ p ∈ S, Real.log p + Real.log y := by
        gcongr ?_ + ?_ + ?_
        · refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
            (fun p _ _ => Real.log_natCast_nonneg p)
          simp only [mem_filter, Nat.mem_primesLE, G] at hp ⊢
          refine ⟨?_, hp.1.2⟩
          have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg p) hp.2
          exact (Nat.le_floor_iff hx0).mpr hp.2
        · exact sum_le_sum_of_subset_of_nonneg (fun p hp => (mem_filter.mp hp).2)
            (fun p _ _ => Real.log_natCast_nonneg p)
        · rw [sum_ite_eq']
          split_ifs
          · exact Real.log_le_log (by exact_mod_cast Nat.floor_pos.mpr hy) (Nat.floor_le hy0)
          · exact Real.log_nonneg hy

/-- `∑_{p ≤ N, p² ≤ N} ⌊log_p N⌋ log p ≤ 2 (ψ(N) - θ(N))`. -/
theorem sum_log_small_le (N : ℕ) :
    ∑ p ∈ Nat.primesLE N with p * p ≤ N, (Nat.log p N : ℝ) * Real.log p ≤
      2 * (Chebyshev.psi N - Chebyshev.theta N) := by
  rw [Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log, ← sum_sub_distrib,
    mul_sum, sum_filter]
  refine sum_le_sum fun p hp => ?_
  rw [Nat.mem_primesLE] at hp
  have h0 := Real.log_natCast_nonneg p
  have hL1 : (1 : ℝ) ≤ Nat.log p N := by
    exact_mod_cast Nat.log_pos hp.2.one_lt hp.1
  split_ifs with h
  · have hL2 : (2 : ℝ) ≤ Nat.log p N := by
      exact_mod_cast Nat.le_log_of_pow_le hp.2.one_lt (by rw [sq]; exact h)
    nlinarith
  · nlinarith

/-- `∑_{p ≤ N, p ≤ M} log p ≤ θ(M)`. -/
theorem sum_primesLE_filter_le_theta (N M : ℕ) :
    ∑ p ∈ Nat.primesLE N with p ≤ M, Real.log p ≤ Chebyshev.theta M := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => Real.log_natCast_nonneg p)
  simp only [mem_filter, Nat.mem_primesLE] at hp ⊢
  exact ⟨hp.2, hp.1.2⟩

/-- `∑_p #{m ∈ l | Q p m} f p = ∑_{m ∈ l} ∑_{p, Q p m} f p`. -/
theorem sum_length_filter_mul (F : Finset ℕ) (Q : ℕ → ℕ → Prop) [∀ p m, Decidable (Q p m)]
    (f : ℕ → ℝ) (l : List ℕ) :
    ∑ p ∈ F, ((l.filter fun m => Q p m).length : ℝ) * f p =
      (l.map fun m => ∑ p ∈ F with Q p m, f p).sum := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    rw [← ih, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    by_cases h : Q p m <;> simp [h, add_mul, add_comm]

/-- `∑_{k=1}^{K} f k = ∑_{k < K} f (k + 1)`. -/
theorem sum_Icc_one_eq_sum_range (K : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 K, f k = ∑ k ∈ Finset.range K, f (k + 1) := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- Order facts for a strictly increasing list of rationals from `0` to `1`. -/
theorem list_unit_facts {X : List ℚ} (hX0 : X.head? = some 0) (hX1 : X.getLast? = some 1)
    (hXmono : X.Pairwise (· < ·)) :
    (∀ i < X.length, 0 ≤ X.getD i 0 ∧ X.getD i 0 ≤ 1) ∧
      ∀ i j, i < j → j < X.length → X.getD i 0 < X.getD j 0 := by
  have hmono : ∀ i j, i < j → j < X.length → X.getD i 0 < X.getD j 0 := fun i j hij hj => by
    rw [List.getD_eq_getElem _ _ (hij.trans hj), List.getD_eq_getElem _ _ hj]
    exact List.pairwise_iff_getElem.mp hXmono i j _ hj hij
  have h0 : X.getD 0 0 = 0 := by
    cases X with
    | nil => simp at hX0
    | cons a l => simpa using hX0
  have h1 : X.getD (X.length - 1) 0 = 1 := by
    rw [List.getLast?_eq_getElem?] at hX1
    rw [List.getD_eq_getElem?_getD, hX1]
    rfl
  refine ⟨fun i hi => ⟨?_, ?_⟩, hmono⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [h0]
    · exact (h0 ▸ hmono 0 i hi0 hi).le
  · rcases Nat.lt_or_ge i (X.length - 1) with h | h
    · exact h1 ▸ (hmono i _ h (by omega)).le
    · rw [show i = X.length - 1 by omega, h1]

end Aux

/-- The index set `{(i, k) : i < |X| - 1, k ≤ K, k ≠ 0 ∨ Xᵢ ≥ 1/m}` of the intervals
`(k + Xᵢ, k + Xᵢ₊₁)` used in the lower bound for `∑ φ'(n/p) log p`. -/
noncomputable def lowIdx (m K : ℕ) (X : List ℚ) : Finset (ℕ × ℕ) :=
  (Finset.range (X.length - 1) ×ˢ Finset.range (K + 1)).filter
    fun ik => ik.2 ≠ 0 ∨ 1 / (m : ℝ) ≤ (X.getD ik.1 0 : ℝ)

/-- The left end point `k + Xᵢ`. -/
noncomputable def lowL (X : List ℚ) (ik : ℕ × ℕ) : ℝ := ik.2 + (X.getD ik.1 0 : ℝ)

/-- The right end point `k + Xᵢ₊₁`. -/
noncomputable def lowR (X : List ℚ) (ik : ℕ × ℕ) : ℝ := ik.2 + (X.getD (ik.1 + 1) 0 : ℝ)

theorem weightedSum_eq (m K : ℕ) (X : List ℚ) (vals : List ℕ) :
    weightedSum m K X vals =
      ∑ ik ∈ lowIdx m K X, (vals.getD ik.1 0 : ℝ) * (1 / lowL X ik - 1 / lowR X ik) := by
  unfold weightedSum lowIdx
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range_succ', intervalWeight, sum_Icc_one_eq_sum_range, mul_add, Finset.mul_sum]
  refine congr_arg₂ HAdd.hAdd (Finset.sum_congr rfl fun k _ => ?_) ?_
  · have hk : k + 1 ≠ 0 ∨ 1 / (m : ℝ) ≤ (X.getD i 0 : ℝ) := Or.inl (Nat.succ_ne_zero k)
    simp only [hk, ↓reduceIte, lowL, lowR]
  · simp [lowL, lowR]

theorem lowIdx_facts {m K : ℕ} (hm : 1 ≤ m) {X : List ℚ} (hX0 : X.head? = some 0)
    (hX1 : X.getLast? = some 1) (hXmono : X.Pairwise (· < ·)) {ik : ℕ × ℕ}
    (hik : ik ∈ lowIdx m K X) :
    ik.1 + 1 < X.length ∧ ik.2 ≤ K ∧ 0 ≤ (X.getD ik.1 0 : ℝ) ∧
      (X.getD ik.1 0 : ℝ) < X.getD (ik.1 + 1) 0 ∧ (X.getD (ik.1 + 1) 0 : ℝ) ≤ 1 ∧
      0 < lowL X ik ∧ lowL X ik < lowR X ik ∧ lowR X ik ≤ K + 1 ∧ 1 / lowL X ik ≤ m := by
  obtain ⟨hb, hmono⟩ := list_unit_facts hX0 hX1 hXmono
  simp only [lowIdx, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hik
  obtain ⟨⟨hi, hk⟩, hc⟩ := hik
  have hi1 : ik.1 + 1 < X.length := by omega
  have h0 : (0 : ℝ) ≤ X.getD ik.1 0 := by exact_mod_cast (hb _ (by omega)).1
  have h1 : (X.getD ik.1 0 : ℝ) < X.getD (ik.1 + 1) 0 := by
    exact_mod_cast hmono _ _ (by omega) hi1
  have h2 : (X.getD (ik.1 + 1) 0 : ℝ) ≤ 1 := by exact_mod_cast (hb _ hi1).2
  have hK : (ik.2 : ℝ) ≤ K := by exact_mod_cast (show ik.2 ≤ K by omega)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk0 : (0 : ℝ) ≤ ik.2 := Nat.cast_nonneg _
  have hLpos : 0 < lowL X ik ∧ 1 / lowL X ik ≤ m := by
    unfold lowL
    rcases hc with hc | hc
    · have : (1 : ℝ) ≤ ik.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
      refine ⟨by linarith, ?_⟩
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    · rw [div_le_iff₀ (by linarith)] at hc
      have hx : 0 < (X.getD ik.1 0 : ℝ) := by
        by_contra hneg
        nlinarith
      refine ⟨by linarith, ?_⟩
      rw [div_le_iff₀ (by linarith)]
      nlinarith
  refine ⟨hi1, by omega, h0, h1, h2, hLpos.1, ?_, ?_, hLpos.2⟩
  · unfold lowL lowR
    linarith
  · unfold lowR
    linarith

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le {l : List ℕ} {c : ℕ} (h : ∀ a ∈ l, a ≤ c) : l.foldr max 0 ≤ c := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.foldr_cons]
    exact max_le (h b (by simp)) (ih fun a ha => h a (by simp [ha]))

namespace Params

variable {P : Params}

theorem one_le_mhat0 (hP : P.Valid) : 1 ≤ P.mhat0 :=
  hP.etaOne_pos.trans_le ((le_foldr_max hP.etaOne_mem).trans (le_max_left _ _))

theorem mhat0_le_eta0 (hP : P.Valid) : P.mhat0 ≤ P.eta0 := by
  have h2 := hP.two_mul_lt _ hP.etaMin_mem
  exact max_le ((foldr_max_le hP.zs_le_etaMin).trans (by omega)) (Nat.sub_le _ _)

theorem mhats_eq_cons (hP : P.Valid) : P.mhats = P.mhat1 :: P.mhats.tail := by
  unfold mhat1
  cases h : P.mhats with
  | nil =>
    have := hP.etaMin_mem
    simp only [mhats, List.map_eq_nil_iff] at h
    simp [h] at this
  | cons a t => rfl

theorem log_Delta_eq (φ' : ℝ → ℕ) (n : ℕ) :
    Real.log (P.Delta φ' n) =
      ∑ p ∈ Nat.primesLE (P.h0 n), (P.deltaExp φ' n p : ℝ) * Real.log p := by
  unfold Delta
  rw [Rat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Rat.cast_zpow, Rat.cast_natCast, Real.log_zpow]
  · intro p hp
    rw [Rat.cast_zpow, Rat.cast_natCast]
    exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero)

theorem log_Delta_le_aux (φ' : ℝ → ℕ) (n : ℕ) :
    Real.log (P.Delta φ' n) ≤
      6 * P.q * (Chebyshev.psi (P.h0 n) - Chebyshev.theta (P.h0 n)) +
        ((P.r - 1 : ℕ) : ℝ) * Chebyshev.theta ((P.mhat1 : ℝ) * n) +
        (P.mhats.map fun m : ℕ => Chebyshev.theta ((m : ℝ) * n)).sum -
        ∑ p ∈ Nat.primesLE (P.h0 n) with ¬ p * p ≤ P.h0 n ∧ p ≤ P.mhat0 * n,
          (φ' ((n : ℝ) / p) : ℝ) * Real.log p := by
  rw [log_Delta_eq]
  have hpt : ∀ p ∈ Nat.primesLE (P.h0 n), (P.deltaExp φ' n p : ℝ) * Real.log p =
      ((if p * p ≤ P.h0 n then (3 * P.q : ℝ) * ((Nat.log p (P.h0 n) : ℝ) * Real.log p)
        else 0) +
        (if p * p ≤ P.h0 n then 0 else (P.dExp n p : ℝ) * Real.log p)) -
        (if ¬ p * p ≤ P.h0 n ∧ p ≤ P.mhat0 * n then (φ' ((n : ℝ) / p) : ℝ) * Real.log p
          else 0) := by
    intro p _
    unfold deltaExp
    by_cases h1 : p * p ≤ P.h0 n
    · simp only [h1, ↓reduceIte, not_true_eq_false, false_and]
      push_cast
      ring
    · by_cases h2 : p ≤ P.mhat0 * n
      · simp only [h1, h2, ↓reduceIte, not_false_eq_true, and_self]
        push_cast
        ring
      · simp only [h1, h2, ↓reduceIte, not_false_eq_true, and_false]
        push_cast
        ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : ∑ p ∈ Nat.primesLE (P.h0 n), (if p * p ≤ P.h0 n then
      (3 * P.q : ℝ) * ((Nat.log p (P.h0 n) : ℝ) * Real.log p) else 0) ≤
      6 * P.q * (Chebyshev.psi (P.h0 n) - Chebyshev.theta (P.h0 n)) := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have := sum_log_small_le (P.h0 n)
    have hq : (0 : ℝ) ≤ 3 * P.q := by positivity
    calc _ ≤ (3 * P.q : ℝ) * (2 * (Chebyshev.psi (P.h0 n) - Chebyshev.theta (P.h0 n))) :=
          mul_le_mul_of_nonneg_left this hq
      _ = _ := by ring
  have hB : ∑ p ∈ Nat.primesLE (P.h0 n),
      (if p * p ≤ P.h0 n then 0 else (P.dExp n p : ℝ) * Real.log p) ≤
      ((P.r - 1 : ℕ) : ℝ) * Chebyshev.theta ((P.mhat1 : ℝ) * n) +
        (P.mhats.map fun m : ℕ => Chebyshev.theta ((m : ℝ) * n)).sum := by
    calc _ ≤ ∑ p ∈ Nat.primesLE (P.h0 n), (P.dExp n p : ℝ) * Real.log p :=
          Finset.sum_le_sum fun p _ => by
            split_ifs
            · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
            · exact le_rfl
      _ = ((P.r - 1 : ℕ) : ℝ) * ∑ p ∈ Nat.primesLE (P.h0 n) with p ≤ P.mhat1 * n, Real.log p +
          ∑ p ∈ Nat.primesLE (P.h0 n),
            ((P.mhats.filter fun m => p ≤ m * n).length : ℝ) * Real.log p := by
          rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          unfold dExp
          split_ifs <;> push_cast <;> ring
      _ ≤ _ := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) ?_
          · have h := sum_primesLE_filter_le_theta (P.h0 n) (P.mhat1 * n)
            push_cast at h
            exact h
          · have h := sum_length_filter_mul (Nat.primesLE (P.h0 n)) (fun p m => p ≤ m * n)
              (fun p => Real.log p) P.mhats
            rw [h]
            refine List.sum_le_sum fun m _ => ?_
            have h' := sum_primesLE_filter_le_theta (P.h0 n) (m * n)
            push_cast at h'
            exact h'
  have hC := (Finset.sum_filter (s := Nat.primesLE (P.h0 n))
    (fun p => ¬ p * p ≤ P.h0 n ∧ p ≤ P.mhat0 * n)
    (fun p => (φ' ((n : ℝ) / p) : ℝ) * Real.log p)).symm
  linarith

theorem sum_phi_lower (hP : P.Valid) {X : List ℚ} {vals : List ℕ}
    (hX0 : X.head? = some 0) (hX1 : X.getLast? = some 1) (hXmono : X.Pairwise (· < ·))
    {φ' : ℝ → ℕ}
    (hφ : ∀ i, i + 1 < X.length → ∀ x : ℝ, (X.getD i 0 : ℝ) < Int.fract x →
      Int.fract x < X.getD (i + 1) 0 → vals.getD i 0 ≤ φ' x) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∑ ik ∈ lowIdx P.mhat0 K X, (vals.getD ik.1 0 : ℝ) *
          (Chebyshev.theta (1 / lowL X ik * n) - Chebyshev.theta (1 / lowR X ik * n) -
            Real.log (1 / lowL X ik * n)) ≤
        ∑ p ∈ Nat.primesLE (P.h0 n) with ¬ p * p ≤ P.h0 n ∧ p ≤ P.mhat0 * n,
          (φ' ((n : ℝ) / p) : ℝ) * Real.log p := by
  have hm0 := one_le_mhat0 hP
  have hm0le := mhat0_le_eta0 hP
  obtain ⟨_, hmono⟩ := list_unit_facts hX0 hX1 hXmono
  filter_upwards [eventually_ge_atTop ((K + 1) ^ 2 * (P.eta0 + 2) + 1)] with n hn
  have hKsq : K + 1 ≤ (K + 1) ^ 2 * (P.eta0 + 2) := by
    calc K + 1 ≤ (K + 1) * ((K + 1) * (P.eta0 + 2)) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
      _ = (K + 1) ^ 2 * (P.eta0 + 2) := by ring
  have hn1 : 1 ≤ n := by omega
  have hnK : ((K : ℝ) + 1) ≤ n := by exact_mod_cast (show K + 1 ≤ n by omega)
  have hbigN : P.h0 n * (K + 1) ^ 2 < n ^ 2 := by
    unfold h0
    calc (P.eta0 * n + 2) * (K + 1) ^ 2 ≤ ((K + 1) ^ 2 * (P.eta0 + 2)) * n := by
          have : P.eta0 * n + 2 ≤ (P.eta0 + 2) * n := by nlinarith
          calc (P.eta0 * n + 2) * (K + 1) ^ 2 ≤ ((P.eta0 + 2) * n) * (K + 1) ^ 2 :=
                Nat.mul_le_mul_right _ this
            _ = ((K + 1) ^ 2 * (P.eta0 + 2)) * n := by ring
      _ < n * n := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = n ^ 2 := (sq n).symm
  have hbig : (P.h0 n : ℝ) * ((K : ℝ) + 1) ^ 2 < (n : ℝ) ^ 2 := by exact_mod_cast hbigN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN : P.mhat0 * n ≤ P.h0 n := by
    unfold h0
    have := Nat.mul_le_mul_right n hm0le
    omega
  -- Step A: each interval contributes at least `θ(n/α) - θ(n/β) - log(n/α)`.
  have stepA : ∀ ik ∈ lowIdx P.mhat0 K X,
      Chebyshev.theta (1 / lowL X ik * n) - Chebyshev.theta (1 / lowR X ik * n) -
          Real.log (1 / lowL X ik * n) ≤
        ∑ p ∈ (Nat.primesLE (P.h0 n)).filter (fun p => ¬ p * p ≤ P.h0 n ∧ p ≤ P.mhat0 * n)
          with lowL X ik < (n : ℝ) / ((p : ℕ) : ℝ) ∧ (n : ℝ) / ((p : ℕ) : ℝ) < lowR X ik, Real.log p := by
    intro ik hik
    obtain ⟨-, -, -, -, -, hL, hLR, hRK, hLm⟩ := lowIdx_facts hm0 hX0 hX1 hXmono hik
    have hR : 0 < lowR X ik := hL.trans hLR
    apply theta_sub_theta_sub_log_le
    · rw [one_div_mul_eq_div, le_div_iff₀ hL]
      linarith
    · intro p hp hxp hpy
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      rw [one_div_mul_eq_div, div_lt_iff₀ hR] at hxp
      rw [one_div_mul_eq_div, lt_div_iff₀ hL] at hpy
      have hpm : (p : ℝ) ≤ P.mhat0 * n := by
        have h1 : (p : ℝ) < n / lowL X ik := by
          rw [lt_div_iff₀ hL]
          exact hpy
        have h2 : (n : ℝ) / lowL X ik ≤ P.mhat0 * n := by
          rw [div_eq_mul_one_div, mul_comm]
          exact mul_le_mul_of_nonneg_right hLm hn0.le
        linarith
      have hpm' : p ≤ P.mhat0 * n := by exact_mod_cast hpm
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr
        ⟨hpm'.trans hN, hp⟩, ?_, hpm'⟩, ?_, ?_⟩
      · intro hpp
        have hpp' : (p : ℝ) * p ≤ P.h0 n := by exact_mod_cast hpp
        have h3 : (n : ℝ) < p * ((K : ℝ) + 1) := by
          nlinarith [mul_le_mul_of_nonneg_left hRK hp0.le]
        have h4 : (n : ℝ) ^ 2 < (p * ((K : ℝ) + 1)) ^ 2 := by nlinarith
        have h5 : (p : ℝ) * p * ((K : ℝ) + 1) ^ 2 ≤ P.h0 n * ((K : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hpp' (by positivity)
        nlinarith
      · rw [lt_div_iff₀ hp0]
        linarith
      · rw [div_lt_iff₀ hp0]
        linarith
  -- Step B: the intervals are disjoint and `φ'(n/p) ≥ vᵢ` on them.
  have stepB : ∑ ik ∈ lowIdx P.mhat0 K X, (vals.getD ik.1 0 : ℝ) *
      ∑ p ∈ (Nat.primesLE (P.h0 n)).filter (fun p => ¬ p * p ≤ P.h0 n ∧ p ≤ P.mhat0 * n)
          with lowL X ik < (n : ℝ) / ((p : ℕ) : ℝ) ∧ (n : ℝ) / ((p : ℕ) : ℝ) < lowR X ik, Real.log p ≤
      ∑ p ∈ (Nat.primesLE (P.h0 n)).filter (fun p => ¬ p * p ≤ P.h0 n ∧ p ≤ P.mhat0 * n),
        (φ' ((n : ℝ) / p) : ℝ) * Real.log p := by
    calc _ = ∑ ik ∈ lowIdx P.mhat0 K X,
          ∑ p ∈ (Nat.primesLE (P.h0 n)).filter (fun p => ¬ p * p ≤ P.h0 n ∧ p ≤ P.mhat0 * n),
            if lowL X ik < (n : ℝ) / p ∧ (n : ℝ) / p < lowR X ik then
              (vals.getD ik.1 0 : ℝ) * Real.log p else 0 := by
          refine Finset.sum_congr rfl fun ik _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_filter]
      _ = ∑ p ∈ (Nat.primesLE (P.h0 n)).filter (fun p => ¬ p * p ≤ P.h0 n ∧ p ≤ P.mhat0 * n),
          ∑ ik ∈ lowIdx P.mhat0 K X,
            if lowL X ik < (n : ℝ) / p ∧ (n : ℝ) / p < lowR X ik then
              (vals.getD ik.1 0 : ℝ) * Real.log p else 0 := Finset.sum_comm
      _ ≤ _ := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [← Finset.sum_filter, ← Finset.sum_mul]
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
          have hbound : ∀ ik ∈ (lowIdx P.mhat0 K X).filter
              (fun ik => lowL X ik < (n : ℝ) / p ∧ (n : ℝ) / p < lowR X ik),
              (vals.getD ik.1 0 : ℝ) ≤ φ' ((n : ℝ) / p) := by
            intro ik hik
            rw [Finset.mem_filter] at hik
            obtain ⟨hi1, -, h0, h01, h1, -⟩ := lowIdx_facts hm0 hX0 hX1 hXmono hik.1
            obtain ⟨hy1, hy2⟩ := hik.2
            simp only [lowL, lowR] at hy1 hy2
            have hfr : Int.fract ((n : ℝ) / p) = (n : ℝ) / p - ik.2 := by
              rw [Int.fract_eq_iff]
              refine ⟨by linarith, by linarith, ik.2, by push_cast; ring⟩
            exact_mod_cast hφ ik.1 hi1 ((n : ℝ) / p) (by rw [hfr]; linarith) (by rw [hfr]; linarith)
          have hcard : ((lowIdx P.mhat0 K X).filter
              (fun ik => lowL X ik < (n : ℝ) / p ∧ (n : ℝ) / p < lowR X ik)).card ≤ 1 := by
            rw [Finset.card_le_one]
            intro a ha b hb
            rw [Finset.mem_filter] at ha hb
            obtain ⟨ha1, -, ha0, ha01, ha1', -⟩ := lowIdx_facts hm0 hX0 hX1 hXmono ha.1
            obtain ⟨hb1, -, hb0, hb01, hb1', -⟩ := lowIdx_facts hm0 hX0 hX1 hXmono hb.1
            obtain ⟨hay1, hay2⟩ := ha.2
            obtain ⟨hby1, hby2⟩ := hb.2
            simp only [lowL, lowR] at hay1 hay2 hby1 hby2
            have hk : a.2 = b.2 := by
              have e1 : (a.2 : ℝ) < b.2 + 1 := by linarith
              have e2 : (b.2 : ℝ) < a.2 + 1 := by linarith
              have e1' : a.2 < b.2 + 1 := by exact_mod_cast e1
              have e2' : b.2 < a.2 + 1 := by exact_mod_cast e2
              omega
            have hk' : (a.2 : ℝ) = b.2 := by rw [hk]
            have hi : a.1 = b.1 := by
              rcases lt_trichotomy a.1 b.1 with h | h | h
              · exfalso
                have : (X.getD (a.1 + 1) 0 : ℝ) ≤ X.getD b.1 0 := by
                  rcases (show a.1 + 1 ≤ b.1 by omega).lt_or_eq with h' | h'
                  · exact_mod_cast (hmono _ _ h' (by omega)).le
                  · rw [h']
                linarith
              · exact h
              · exfalso
                have : (X.getD (b.1 + 1) 0 : ℝ) ≤ X.getD a.1 0 := by
                  rcases (show b.1 + 1 ≤ a.1 by omega).lt_or_eq with h' | h'
                  · exact_mod_cast (hmono _ _ h' (by omega)).le
                  · rw [h']
                linarith
            exact Prod.ext hi hk
          calc ∑ ik ∈ (lowIdx P.mhat0 K X).filter
                (fun ik => lowL X ik < (n : ℝ) / p ∧ (n : ℝ) / p < lowR X ik),
                (vals.getD ik.1 0 : ℝ)
              ≤ ((lowIdx P.mhat0 K X).filter
                (fun ik => lowL X ik < (n : ℝ) / p ∧ (n : ℝ) / p < lowR X ik)).card •
                  (φ' ((n : ℝ) / p) : ℝ) := Finset.sum_le_card_nsmul _ _ _ hbound
            _ ≤ 1 • (φ' ((n : ℝ) / p) : ℝ) := by
                rw [nsmul_eq_mul, nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
            _ = φ' ((n : ℝ) / p) := one_nsmul _
  calc _ ≤ ∑ ik ∈ lowIdx P.mhat0 K X, (vals.getD ik.1 0 : ℝ) *
      ∑ p ∈ (Nat.primesLE (P.h0 n)).filter (fun p => ¬ p * p ≤ P.h0 n ∧ p ≤ P.mhat0 * n)
          with lowL X ik < (n : ℝ) / ((p : ℕ) : ℝ) ∧ (n : ℝ) / ((p : ℕ) : ℝ) < lowR X ik, Real.log p :=
        Finset.sum_le_sum fun ik hik =>
          mul_le_mul_of_nonneg_left (stepA ik hik) (Nat.cast_nonneg _)
    _ ≤ _ := stepB

end Params

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
  intro ε hε
  have hm0 := one_le_mhat0 hP
  have heta0 : (0 : ℝ) < P.eta0 := by
    have := hP.two_mul_lt _ hP.etaMin_mem
    exact_mod_cast (show 0 < P.eta0 by omega)
  have hr : 1 ≤ P.r := by have := hP.three_le_r; omega
  have hLpos : ∀ ik ∈ lowIdx P.mhat0 K X, 0 < lowL X ik := fun ik hik =>
    (lowIdx_facts hm0 hX0 hX1 hXmono hik).2.2.2.2.2.1
  have hRpos : ∀ ik ∈ lowIdx P.mhat0 K X, 0 < lowR X ik := fun ik hik =>
    (hLpos ik hik).trans (lowIdx_facts hm0 hX0 hX1 hXmono hik).2.2.2.2.2.2.1
  have hU : Tendsto (fun n : ℕ =>
      6 * (P.q : ℝ) * ((Chebyshev.psi (P.eta0 * n + 2) - Chebyshev.theta (P.eta0 * n + 2)) / n) +
        ((P.r - 1 : ℕ) : ℝ) * (Chebyshev.theta (P.mhat1 * n) / n) +
        (P.mhats.map fun m : ℕ => Chebyshev.theta ((m : ℝ) * n) / n).sum -
        ∑ ik ∈ lowIdx P.mhat0 K X, (vals.getD ik.1 0 : ℝ) *
          (Chebyshev.theta (1 / lowL X ik * n) / n - Chebyshev.theta (1 / lowR X ik * n) / n -
            Real.log (1 / lowL X ik * n) / n)) atTop
      (𝓝 (6 * (P.q : ℝ) * 0 + ((P.r - 1 : ℕ) : ℝ) * P.mhat1 +
        (P.mhats.map fun m : ℕ => (m : ℝ)).sum -
        ∑ ik ∈ lowIdx P.mhat0 K X, (vals.getD ik.1 0 : ℝ) *
          (1 / lowL X ik - 1 / lowR X ik - 0))) :=
    (((tendsto_const_nhds.mul (tendsto_psi_sub_theta_div heta0 2)).add
      (tendsto_const_nhds.mul (tendsto_theta_mul_div (Nat.cast_nonneg _)))).add
      (tendsto_list_sum _ fun m _ => tendsto_theta_mul_div (Nat.cast_nonneg _))).sub
      (tendsto_finsetSum _ fun ik hik => tendsto_const_nhds.mul
        (((tendsto_theta_mul_div (one_div_pos.mpr (hLpos ik hik)).le).sub
          (tendsto_theta_mul_div (one_div_pos.mpr (hRpos ik hik)).le)).sub
          (tendsto_log_mul_div (one_div_pos.mpr (hLpos ik hik)))))
  have hLimEq : 6 * (P.q : ℝ) * 0 + ((P.r - 1 : ℕ) : ℝ) * P.mhat1 +
        (P.mhats.map fun m : ℕ => (m : ℝ)).sum -
        ∑ ik ∈ lowIdx P.mhat0 K X, (vals.getD ik.1 0 : ℝ) *
          (1 / lowL X ik - 1 / lowR X ik - 0) =
      P.r * P.mhat1 + (P.mhats.tail.sum : ℝ) - weightedSum P.mhat0 K X vals := by
    rw [weightedSum_eq]
    have e : (P.mhats.map fun m : ℕ => (m : ℝ)).sum = P.mhat1 + (P.mhats.tail.sum : ℝ) := by
      conv_lhs => rw [mhats_eq_cons hP]
      rw [List.map_cons, List.sum_cons, Nat.cast_list_sum]
    rw [e, Nat.cast_sub hr, Nat.cast_one]
    simp only [sub_zero, mul_zero, zero_add]
    ring
  have hev1 := hU.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [hev1, sum_phi_lower hP hX0 hX1 hXmono hφ K, eventually_ge_atTop 1]
    with n h1 h2 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmain := log_Delta_le_aux (P := P) φ' n
  have hN : ((P.h0 n : ℕ) : ℝ) = (P.eta0 : ℝ) * n + 2 := by simp [Params.h0]
  rw [hN] at hmain
  have e1 : (P.mhats.map fun m : ℕ => Chebyshev.theta ((m : ℝ) * n) / n).sum =
      (P.mhats.map fun m : ℕ => Chebyshev.theta ((m : ℝ) * n)).sum / n := by
    rw [div_eq_mul_inv, ← List.sum_map_mul_right]
    simp only [div_eq_mul_inv]
  have e2 : ∑ ik ∈ lowIdx P.mhat0 K X, (vals.getD ik.1 0 : ℝ) *
      (Chebyshev.theta (1 / lowL X ik * n) / n - Chebyshev.theta (1 / lowR X ik * n) / n -
        Real.log (1 / lowL X ik * n) / n) =
      (∑ ik ∈ lowIdx P.mhat0 K X, (vals.getD ik.1 0 : ℝ) *
        (Chebyshev.theta (1 / lowL X ik * n) - Chebyshev.theta (1 / lowR X ik * n) -
          Real.log (1 / lowL X ik * n))) / n := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun ik _ => ?_
    ring
  rw [e1, e2] at h1
  have hUn := mul_lt_mul_of_pos_left h1 hn0
  have hn' : (n : ℝ) ≠ 0 := hn0.ne'
  have key : ∀ a b c d q' r' : ℝ,
      (n : ℝ) * (q' * (a / n) + r' * (b / n) + c / n - d / n) = q' * a + r' * b + c - d := by
    intro a b c d q' r'
    field_simp
  rw [key, hLimEq] at hUn
  have hfin : (n : ℝ) * (P.r * P.mhat1 + (P.mhats.tail.sum : ℝ) - weightedSum P.mhat0 K X vals + ε)
      ≤ n * (P.r * P.mhat1 + (P.mhats.tail.sum : ℝ) - I' + ε) :=
    mul_le_mul_of_nonneg_left (by linarith) hn0.le
  linarith

end Params

end OddZeta
