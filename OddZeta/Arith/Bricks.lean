import OddZeta.Arith.Valuation

/-!
# Bricks and the `p`-adic valuations of their Taylor coefficients

For `s : ℤ` and `m : ℕ` we consider the power series (in `X = ε`, over `ℚ`)

* `polyBrick s m = ∏_{c ∈ [s, s+m-1]} (c + X) / m!`;
* `poleBrick s m = m! X / ∏_{c ∈ [s, s+m]} (c + X)`, where the factor `X` cancels the linear
  factor `c = 0` if it is present (`poleBrick_mul_prod` / `eq_poleBrick_iff`).

We bound the `p`-adic valuations of their coefficients (arithmetic core of Zudilin's
Lemmas 15–18), and express the counts of multiples of `p` in the ranges through floor
divisions.
-/

open Finset PowerSeries

namespace OddZeta

/-! ### Linear factors and their inverses -/

theorem C_add_X_ne_zero (c : ℚ) : (C c + X : PowerSeries ℚ) ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  simp [coeff_X] at this

theorem coeff_inv_C_add_X {c : ℚ} (hc : c ≠ 0) (j : ℕ) :
    coeff j (C c + X)⁻¹ = (-1) ^ j * c⁻¹ ^ (j + 1) := by
  have h : (C c + X)⁻¹ = mk fun j => (-1 : ℚ) ^ j * c⁻¹ ^ (j + 1) := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by simpa using hc)]
    ext n
    rw [mul_add, map_add, coeff_mul_C, coeff_one]
    rcases n with _ | n
    · simp [hc]
    · rw [coeff_succ_mul_X]
      simp only [coeff_mk, Nat.add_one_ne_zero, ite_false]
      have hc' : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
      linear_combination (-(-1 : ℚ) ^ n * c⁻¹ ^ (n + 1)) * hc'
  rw [h, coeff_mk]

/-- The inverse of a product of power series over `ℚ` is the product of the inverses. -/
theorem inv_prod {ι : Type*} (S : Finset ι) (f : ι → PowerSeries ℚ) :
    (∏ i ∈ S, f i)⁻¹ = ∏ i ∈ S, (f i)⁻¹ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [prod_empty, prod_empty, PowerSeries.inv_eq_iff_mul_eq_one (by simp), one_mul]
  | insert a S ha ih =>
    rw [prod_insert ha, prod_insert ha, PowerSeries.mul_inv_rev, ih, mul_comm]

theorem prod_C_add_X_ne_zero (S : Finset ℤ) : ∏ c ∈ S, (C (c : ℚ) + X) ≠ 0 :=
  prod_ne_zero_iff.2 fun _ _ => C_add_X_ne_zero _

theorem constantCoeff_prod_C_add_X_ne_zero {S : Finset ℤ} (h : (0 : ℤ) ∉ S) :
    constantCoeff (∏ c ∈ S, (C (c : ℚ) + X)) ≠ 0 := by
  rw [map_prod]
  refine prod_ne_zero_iff.2 fun c hc => ?_
  have : c ≠ 0 := fun h' => h (h' ▸ hc)
  simpa using this

/-- Reindexing a product over an integer interval. -/
theorem prod_Ico_int_eq_prod_range {M : Type*} [CommMonoid M] (f : ℤ → M) (s : ℤ) (m : ℕ) :
    ∏ c ∈ Ico s (s + m), f c = ∏ i ∈ range m, f (s + i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ← ih, Nat.cast_succ, ← add_assoc,
      ← insert_Ico_right_eq_Ico_add_one (by omega), prod_insert (by simp), mul_comm]

/-- A product of `m` consecutive integers is divisible by `m!`. -/
theorem factorial_dvd_prod_Ico (s : ℤ) (m : ℕ) : (m.factorial : ℤ) ∣ ∏ c ∈ Ico s (s + m), c := by
  rw [prod_Ico_int_eq_prod_range (fun c => c)]
  exact Nat.factorial_coe_dvd_prod m s

section Valuation

variable {p : ℕ} [Fact p.Prime]

/-- Coefficients of `(c + X)⁻¹ = ∑ (-1)^j c^{-(j+1)} X^j`. -/
theorem vge_coeff_inv_C_add_X {c : ℤ} (hc : c ≠ 0) {κ : ℤ} (hκ : (padicValInt p c : ℤ) ≤ κ)
    (j : ℕ) : VGe p (-(padicValInt p c : ℤ) - κ * j) (coeff j (C (c : ℚ) + X)⁻¹) := by
  rw [coeff_inv_C_add_X (by exact_mod_cast hc)]
  have := ((vge_one p).neg.pow j).mul (vge_inv_intCast_pow (p := p) c (j + 1))
  refine this.mono ?_
  have hj : (0 : ℤ) ≤ j := by positivity
  push_cast
  nlinarith

theorem sum_padicValInt_eq {S : Finset ℤ} (h : ∀ c ∈ S, c ≠ 0) :
    ∑ c ∈ S, (padicValInt p c : ℤ) = padicValInt p (∏ c ∈ S, c) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [sum_insert ha, prod_insert ha, padicValInt.mul (h a (mem_insert_self a S))
      (prod_ne_zero_iff.2 fun c hc => h c (mem_insert_of_mem hc)),
      ih fun c hc => h c (mem_insert_of_mem hc)]
    push_cast; rfl

end Valuation

/-! ### Polynomial bricks -/

/-- The polynomial brick `∏_{c ∈ [s, s+m-1]} (c + X) / m!`. -/
noncomputable def polyBrick (s : ℤ) (m : ℕ) : PowerSeries ℚ :=
  (∏ c ∈ Ico s (s + m), (C (c : ℚ) + X)) * C ((m.factorial : ℚ)⁻¹)

section PolyBrick

variable {p : ℕ} [Fact p.Prime]

/-- General bound for polynomial bricks: if `v_p(c) ≥ ν c` and `ν c ≤ κ` for each `c` in the
range, then `v_p(coeff l) ≥ ∑ ν c - v_p(m!) - κ l`. -/
theorem polyBrick_vge_of (s : ℤ) (m : ℕ) (ν : ℤ → ℤ) (κ : ℤ)
    (h0 : ∀ c ∈ Ico s (s + m), VGe p (ν c) (c : ℚ)) (h1 : ∀ c ∈ Ico s (s + m), ν c ≤ κ)
    (l : ℕ) :
    VGe p ((∑ c ∈ Ico s (s + m), ν c) - padicValNat p m.factorial - κ * l)
      (coeff l (polyBrick s m)) := by
  have hf := vge_coeff_prod (p := p) (Ico s (s + m)) (fun c => C (c : ℚ) + X) ν κ
    (fun c hc j => vge_coeff_C_add_X (h0 c hc) (h1 c hc) j)
  have ha : VGe p (-(padicValNat p m.factorial : ℤ)) ((m.factorial : ℚ)⁻¹) := by
    simpa using vge_one_div_natCast (p := p) m.factorial
  refine (vge_coeff_mul_C ha hf l).mono (le_of_eq ?_)
  ring

/-- **Bound 1** (polynomial brick): `v_p(coeff l) ≥ μ - v_p(m!) - l`, where `μ` is the number of
multiples of `p` in `[s, s+m-1]`. (No hypothesis on `p` or on the range is needed.) -/
theorem polyBrick_vge_count (s : ℤ) (m : ℕ) (l : ℕ) :
    VGe p ((#{c ∈ Ico s (s + m) | (p : ℤ) ∣ c} : ℤ) - padicValNat p m.factorial - l)
      (coeff l (polyBrick s m)) := by
  have h := polyBrick_vge_of (p := p) s m (fun c => if (p : ℤ) ∣ c then 1 else 0) 1
    (fun c _ => by
      split_ifs with hc
      · by_cases hc0 : c = 0
        · subst hc0; simpa using vge_zero p 1
        · refine (vge_intCast' p c).mono ?_
          have := ((padicValInt_dvd_iff (p := p) 1 c).1 (by simpa using hc)).resolve_left hc0
          exact_mod_cast this
      · exact vge_intCast p c)
    (fun c _ => by split_ifs <;> norm_num) l
  simpa [sum_boole] using h

/-- **Bound 2a** (polynomial brick): `v_p(coeff l) ≥ -v_p(m!)`. -/
theorem polyBrick_vge_neg_factorial (s : ℤ) (m : ℕ) (l : ℕ) :
    VGe p (-(padicValNat p m.factorial : ℤ)) (coeff l (polyBrick s m)) := by
  simpa using polyBrick_vge_of (p := p) s m (fun _ => 0) 0 (fun c _ => vge_intCast p c)
    (fun _ _ => le_rfl) l

/-- **Bound 2b** (polynomial brick): if `0 ∉ [s, s+m-1]` and `v_p(c) ≤ L` on the range, then
`v_p(coeff l) ≥ -L l`. -/
theorem polyBrick_vge_neg_mul (s : ℤ) (m : ℕ) (L : ℕ) (h0 : (0 : ℤ) ∉ Ico s (s + m))
    (hL : ∀ c ∈ Ico s (s + m), padicValInt p c ≤ L) (l : ℕ) :
    VGe p (-((L : ℤ) * l)) (coeff l (polyBrick s m)) := by
  have hne : ∀ c ∈ Ico s (s + m), c ≠ 0 := fun c hc h => h0 (h ▸ hc)
  have h := polyBrick_vge_of (p := p) s m (fun c => (padicValInt p c : ℤ)) L
    (fun c _ => vge_intCast' p c) (fun c hc => by exact_mod_cast hL c hc) l
  refine h.mono ?_
  rw [sum_padicValInt_eq hne]
  have hprod : ∏ c ∈ Ico s (s + m), c ≠ 0 := prod_ne_zero_iff.2 hne
  have hdvd : (p : ℤ) ^ padicValNat p m.factorial ∣ ∏ c ∈ Ico s (s + m), c := by
    have h' : ((p ^ padicValNat p m.factorial : ℕ) : ℤ) ∣ (m.factorial : ℤ) :=
      Int.natCast_dvd_natCast.2 pow_padicValNat_dvd
    push_cast at h'
    exact h'.trans (factorial_dvd_prod_Ico s m)
  have := ((padicValInt_dvd_iff (p := p) _ _).1 hdvd).resolve_left hprod
  have : (padicValNat p m.factorial : ℤ) ≤ padicValInt p (∏ c ∈ Ico s (s + m), c) := by
    exact_mod_cast this
  linarith

end PolyBrick

/-! ### Pole bricks -/

/-- The pole brick `m! X / ∏_{c ∈ [s, s+m]} (c + X)`; when `0 ∈ [s, s+m]` the factor `X`
cancels against the linear factor `c = 0`. It is characterised by `poleBrick_mul_prod`. -/
noncomputable def poleBrick (s : ℤ) (m : ℕ) : PowerSeries ℚ :=
  if (0 : ℤ) ∈ Icc s (s + m) then
    C (m.factorial : ℚ) * (∏ c ∈ Icc s (s + m) with c ≠ 0, (C (c : ℚ) + X))⁻¹
  else
    C (m.factorial : ℚ) * X * (∏ c ∈ Icc s (s + m), (C (c : ℚ) + X))⁻¹

theorem prod_C_add_X_eq_X_mul {S : Finset ℤ} (h0 : (0 : ℤ) ∈ S) :
    ∏ c ∈ S, (C (c : ℚ) + X) = X * ∏ c ∈ S with c ≠ 0, (C (c : ℚ) + X) := by
  rw [filter_ne', ← mul_prod_erase S _ h0]
  simp

/-- The characterising identity: `poleBrick s m · ∏_{c ∈ [s, s+m]} (c + X) = m! X`. -/
theorem poleBrick_mul_prod (s : ℤ) (m : ℕ) :
    poleBrick s m * ∏ c ∈ Icc s (s + m), (C (c : ℚ) + X) = C (m.factorial : ℚ) * X := by
  unfold poleBrick
  split_ifs with h0
  · rw [prod_C_add_X_eq_X_mul h0,
      show ∀ a b c d : PowerSeries ℚ, a * b * (c * d) = a * c * (b * d) by intros; ring,
      PowerSeries.inv_mul_cancel _ (constantCoeff_prod_C_add_X_ne_zero (by simp)), mul_one]
  · rw [mul_assoc, PowerSeries.inv_mul_cancel _ (constantCoeff_prod_C_add_X_ne_zero h0),
      mul_one]

/-- `poleBrick s m` is the unique power series satisfying `poleBrick_mul_prod`. -/
theorem eq_poleBrick_iff {F : PowerSeries ℚ} {s : ℤ} {m : ℕ} :
    F = poleBrick s m ↔ F * ∏ c ∈ Icc s (s + m), (C (c : ℚ) + X) = C (m.factorial : ℚ) * X := by
  constructor
  · rintro rfl; exact poleBrick_mul_prod s m
  · intro h
    exact mul_right_cancel₀ (prod_C_add_X_ne_zero _) (h.trans (poleBrick_mul_prod s m).symm)

/-- Explicit product form: `poleBrick s m = m! X^{[0 ∉ [s,s+m]]} ∏_{c ≠ 0} (c + X)⁻¹`. -/
theorem poleBrick_eq_prod_inv (s : ℤ) (m : ℕ) :
    poleBrick s m = C (m.factorial : ℚ) * X ^ (if (0 : ℤ) ∈ Icc s (s + m) then 0 else 1) *
      ∏ c ∈ Icc s (s + m) with c ≠ 0, (C (c : ℚ) + X)⁻¹ := by
  unfold poleBrick
  split_ifs with h0
  · rw [inv_prod, pow_zero, mul_one]
  · have hne : ∀ c ∈ Icc s (s + m), c ≠ 0 := fun c hc h => h0 (h ▸ hc)
    rw [inv_prod, pow_one, filter_true_of_mem hne]

/-- The difference recursion `poleBrick s (m+1) = poleBrick s m - poleBrick (s+1) m`. -/
theorem poleBrick_succ (s : ℤ) (m : ℕ) :
    poleBrick s (m + 1) = poleBrick s m - poleBrick (s + 1) m := by
  symm
  rw [eq_poleBrick_iff]
  have e1 : ∏ c ∈ Icc s (s + ((m + 1 : ℕ) : ℤ)), (C (c : ℚ) + X) =
      (∏ c ∈ Icc s (s + m), (C (c : ℚ) + X)) * (C (((s + m + 1 : ℤ)) : ℚ) + X) := by
    rw [show s + ((m + 1 : ℕ) : ℤ) = s + m + 1 by push_cast; ring,
      ← insert_Icc_right_eq_Icc_add_one (by omega), prod_insert (by simp), mul_comm]
  have e2 : ∏ c ∈ Icc s (s + ((m + 1 : ℕ) : ℤ)), (C (c : ℚ) + X) =
      (C (s : ℚ) + X) * ∏ c ∈ Icc (s + 1) (s + 1 + m), (C (c : ℚ) + X) := by
    rw [show s + ((m + 1 : ℕ) : ℤ) = s + 1 + m by push_cast; ring,
      ← insert_Icc_add_one_left_eq_Icc (by omega), prod_insert (by simp)]
  rw [sub_mul]
  nth_rw 1 [e1]
  rw [e2, ← mul_assoc, poleBrick_mul_prod, mul_left_comm, poleBrick_mul_prod,
    Nat.factorial_succ]
  push_cast
  simp only [map_add, map_mul, map_natCast, map_one]
  ring

section PoleBrick

variable {p : ℕ} [Fact p.Prime]

/-- General bound for pole bricks: if `v_p(c) ≤ κ` for every nonzero `c` in the
range, then `v_p(coeff l) ≥ v_p(m!) + κ [0 ∉ [s,s+m]] - ∑_{c ≠ 0} v_p(c) - κ l`. -/
theorem poleBrick_vge_of (s : ℤ) (m : ℕ) (κ : ℤ)
    (h : ∀ c ∈ Icc s (s + m), c ≠ 0 → (padicValInt p c : ℤ) ≤ κ) (l : ℕ) :
    VGe p ((padicValNat p m.factorial : ℤ) + (if (0 : ℤ) ∈ Icc s (s + m) then 0 else κ) -
        (∑ c ∈ Icc s (s + m) with c ≠ 0, (padicValInt p c : ℤ)) - κ * l)
      (coeff l (poleBrick s m)) := by
  rw [poleBrick_eq_prod_inv, mul_assoc]
  have hP := vge_coeff_prod (p := p) ({c ∈ Icc s (s + m) | c ≠ 0})
    (fun c => (C (c : ℚ) + X)⁻¹) (fun c => -(padicValInt p c : ℤ)) κ
    (fun c hc j => by
      rw [mem_filter] at hc
      exact vge_coeff_inv_C_add_X hc.2 (h c hc.1 hc.2) j)
  have hXP := vge_coeff_mul (vge_coeff_X_pow (p := p) κ
    (if (0 : ℤ) ∈ Icc s (s + m) then 0 else 1)) hP
  refine (vge_coeff_C_mul (vge_natCast' p m.factorial) hXP l).mono (le_of_eq ?_)
  rw [sum_neg_distrib]
  split_ifs <;> push_cast <;> ring

/-- **Bound 3** (pole brick, large prime): if `v_p(c) ≤ 1` for every nonzero `c ∈ [s, s+m]`,
then `v_p(coeff l) ≥ v_p(m!) - μ' - l`, where `μ'` counts the nonzero multiples of `p` in
`[s, s+m]`. -/
theorem poleBrick_vge_count (s : ℤ) (m : ℕ)
    (h1 : ∀ c ∈ Icc s (s + m), c ≠ 0 → padicValInt p c ≤ 1) (l : ℕ) :
    VGe p ((padicValNat p m.factorial : ℤ) - #{c ∈ Icc s (s + m) | c ≠ 0 ∧ (p : ℤ) ∣ c} - l)
      (coeff l (poleBrick s m)) := by
  have h := poleBrick_vge_of (p := p) s m 1
    (fun c hc hc0 => by exact_mod_cast h1 c hc hc0) l
  have hsum : ∑ c ∈ Icc s (s + m) with c ≠ 0, (padicValInt p c : ℤ) =
      #{c ∈ Icc s (s + m) | c ≠ 0 ∧ (p : ℤ) ∣ c} := by
    rw [← filter_filter, ← sum_boole]
    refine sum_congr rfl fun c hc => ?_
    rw [mem_filter] at hc
    split_ifs with hpc
    · have := ((padicValInt_dvd_iff (p := p) 1 c).1 (by simpa using hpc)).resolve_left hc.2
      have := h1 c hc.1 hc.2
      omega
    · simp [padicValInt.eq_zero_of_not_dvd hpc]
  rw [hsum] at h
  refine h.mono ?_
  split_ifs <;> omega

/-- **Bound 3'** (pole brick, large prime, `0 ∉ [s, s+m]`): one better than bound 3. -/
theorem poleBrick_vge_count_of_not_mem (s : ℤ) (m : ℕ) (h0 : (0 : ℤ) ∉ Icc s (s + m))
    (h1 : ∀ c ∈ Icc s (s + m), padicValInt p c ≤ 1) (l : ℕ) :
    VGe p ((padicValNat p m.factorial : ℤ) + 1 - #{c ∈ Icc s (s + m) | (p : ℤ) ∣ c} - l)
      (coeff l (poleBrick s m)) := by
  have h := poleBrick_vge_of (p := p) s m 1
    (fun c hc _ => by exact_mod_cast h1 c hc) l
  have hne : ∀ c ∈ Icc s (s + m), c ≠ 0 := fun c hc h => h0 (h ▸ hc)
  have hsum : ∑ c ∈ Icc s (s + m) with c ≠ 0, (padicValInt p c : ℤ) =
      #{c ∈ Icc s (s + m) | (p : ℤ) ∣ c} := by
    rw [filter_true_of_mem hne, ← sum_boole]
    refine sum_congr rfl fun c hc => ?_
    split_ifs with hpc
    · have := ((padicValInt_dvd_iff (p := p) 1 c).1 (by simpa using hpc)).resolve_left
        (hne c hc)
      have := h1 c hc
      omega
    · simp [padicValInt.eq_zero_of_not_dvd hpc]
  rw [hsum, ite_eq_right h0] at h
  simpa using h

/-- **Bound 4** (pole brick, very large prime): if no nonzero `c ∈ [s, s+m]` is divisible by `p`,
all coefficients are `p`-integral. -/
theorem poleBrick_vge_zero (s : ℤ) (m : ℕ)
    (h : ∀ c ∈ Icc s (s + m), c ≠ 0 → ¬ (p : ℤ) ∣ c) (l : ℕ) :
    VGe p 0 (coeff l (poleBrick s m)) := by
  have hv : ∀ c ∈ Icc s (s + m), c ≠ 0 → padicValInt p c = 0 :=
    fun c hc hc0 => padicValInt.eq_zero_of_not_dvd (h c hc hc0)
  have h' := poleBrick_vge_of (p := p) s m 0
    (fun c hc hc0 => by simp [hv c hc hc0]) l
  have hsum : ∑ c ∈ Icc s (s + m) with c ≠ 0, (padicValInt p c : ℤ) = 0 :=
    sum_eq_zero fun c hc => by
      rw [mem_filter] at hc
      simp [hv c hc.1 hc.2]
  rw [hsum] at h'
  refine h'.mono ?_
  split_ifs <;> simp

/-- **Bound 5** (pole brick, any prime): if `v_p(c) ≤ L` for every nonzero `c ∈ [s, s+m]`, then
`v_p(coeff l) ≥ -L l`. -/
theorem poleBrick_vge_neg_mul (L : ℕ) (m : ℕ) (s : ℤ)
    (h : ∀ c ∈ Icc s (s + m), c ≠ 0 → padicValInt p c ≤ L) (l : ℕ) :
    VGe p (-((L : ℤ) * l)) (coeff l (poleBrick s m)) := by
  induction m generalizing s with
  | zero =>
    have h' := poleBrick_vge_of (p := p) s 0 L
      (fun c hc hc0 => by exact_mod_cast h c hc hc0) l
    refine h'.mono ?_
    simp only [add_zero, Icc_self, mem_singleton, Nat.factorial_zero,
      padicValNat_one_right, CharP.cast_eq_zero, zero_add]
    by_cases hs : (0 : ℤ) = s
    · subst hs; simp [filter_singleton]
    · have hs' : s ≠ 0 := Ne.symm hs
      have hsL := h s (by simp) hs'
      rw [ite_eq_right hs, filter_singleton, ite_eq_left hs', sum_singleton]
      linarith
  | succ m ih =>
    rw [poleBrick_succ, map_sub]
    refine VGe.sub (ih s fun c hc hc0 => h c ?_ hc0) (ih (s + 1) fun c hc hc0 => h c ?_ hc0)
    · simp only [mem_Icc] at hc ⊢; push_cast; omega
    · simp only [mem_Icc] at hc ⊢; push_cast; omega

/-- **Bound 5**, in the weaker form `v_p(coeff l) ≥ -L (l + 1)`. -/
theorem poleBrick_vge_neg_mul_succ (L : ℕ) (m : ℕ) (s : ℤ)
    (h : ∀ c ∈ Icc s (s + m), c ≠ 0 → padicValInt p c ≤ L) (l : ℕ) :
    VGe p (-((L : ℤ) * (l + 1))) (coeff l (poleBrick s m)) :=
  (poleBrick_vge_neg_mul L m s h l).mono (by nlinarith [(L.cast_nonneg : (0 : ℤ) ≤ L)])

end PoleBrick

/-! ### Legendre's formula for `m < p²` and counting multiples of `p` -/

theorem padicValNat_factorial_of_lt_sq {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : m < p ^ 2) :
    padicValNat p m.factorial = m / p := by
  have hlog : Nat.log p m < 2 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · exact Nat.log_lt_of_lt_pow hm0.ne' hm
  rw [padicValNat_factorial hlog]
  simp

/-- The indicator `ι(u, v) = ⌊(u+v)/p⌋ - ⌊u/p⌋ - ⌊v/p⌋` (integer floor division). -/
def iotaZ (p : ℕ) (u v : ℤ) : ℤ := (u + v) / p - u / p - v / p

theorem iotaZ_eq_emod {p : ℕ} (hp : 0 < p) (u v : ℤ) :
    iotaZ p u v = (u % p + v % p) / p := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have : u + v = (u % p + v % p) + (u / p + v / p) * p := by
    have h1 := Int.emod_add_mul_ediv u p
    have h2 := Int.emod_add_mul_ediv v p
    linarith
  unfold iotaZ
  rw [this, Int.add_mul_ediv_right _ _ hp']
  ring

theorem iotaZ_nonneg {p : ℕ} (hp : 0 < p) (u v : ℤ) : 0 ≤ iotaZ p u v := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  rw [iotaZ_eq_emod hp]
  exact Int.ediv_nonneg (add_nonneg (Int.emod_nonneg _ hp'.ne') (Int.emod_nonneg _ hp'.ne'))
    hp'.le

theorem iotaZ_le_one {p : ℕ} (hp : 0 < p) (u v : ℤ) : iotaZ p u v ≤ 1 := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  rw [iotaZ_eq_emod hp]
  have := Int.ediv_lt_of_lt_mul hp' (show u % p + v % p < 2 * p by
    have := Int.emod_lt_of_pos u hp'
    have := Int.emod_lt_of_pos v hp'
    linarith)
  omega

/-- Number of multiples of `p` in `[s, s+m-1]`. -/
theorem card_Ico_filter_dvd {p : ℕ} (hp : 0 < p) (s : ℤ) (m : ℕ) :
    (#{c ∈ Ico s (s + m) | (p : ℤ) ∣ c} : ℤ) = (s + m - 1) / p - (s - 1) / p := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hI : Ico s (s + m) = Ioc (s - 1) (s + m - 1) := by
    ext c; simp only [mem_Ico, mem_Ioc]; omega
  rw [hI, Int.Ioc_filter_dvd_card _ _ hp']
  have e1 : ⌊((s + m - 1 : ℤ) : ℚ) / ((p : ℤ) : ℚ)⌋ = (s + m - 1) / p := by
    rw [Int.cast_natCast, Rat.floor_intCast_div_natCast]
  have e2 : ⌊((s - 1 : ℤ) : ℚ) / ((p : ℤ) : ℚ)⌋ = (s - 1) / p := by
    rw [Int.cast_natCast, Rat.floor_intCast_div_natCast]
  rw [e1, e2]
  have : (s - 1) / (p : ℤ) ≤ (s + m - 1) / p := Int.ediv_le_ediv hp' (by omega)
  omega

/-- Number of multiples of `p` in `[s, s+m]`. -/
theorem card_Icc_filter_dvd {p : ℕ} (hp : 0 < p) (s : ℤ) (m : ℕ) :
    (#{c ∈ Icc s (s + m) | (p : ℤ) ∣ c} : ℤ) = (s + m) / p - (s - 1) / p := by
  have hI : Icc s (s + m) = Ico s (s + ((m + 1 : ℕ) : ℤ)) := by
    ext c; simp only [mem_Icc, mem_Ico]; push_cast; omega
  rw [hI, card_Ico_filter_dvd hp]
  congr 2
  push_cast; ring

/-- Number of nonzero multiples of `p` in `[s, s+m]`. -/
theorem card_Icc_filter_ne_zero_dvd {p : ℕ} (hp : 0 < p) (s : ℤ) (m : ℕ) :
    (#{c ∈ Icc s (s + m) | c ≠ 0 ∧ (p : ℤ) ∣ c} : ℤ) =
      (s + m) / p - (s - 1) / p - (if (0 : ℤ) ∈ Icc s (s + m) then 1 else 0) := by
  rw [← card_Icc_filter_dvd hp]
  have hF : ({c ∈ Icc s (s + m) | c ≠ 0 ∧ (p : ℤ) ∣ c} : Finset ℤ) =
      ({c ∈ Icc s (s + m) | (p : ℤ) ∣ c} : Finset ℤ).erase 0 := by
    ext c; simp only [mem_filter, mem_erase]; tauto
  rw [hF]
  split_ifs with h0
  · have hmem : (0 : ℤ) ∈ ({c ∈ Icc s (s + m) | (p : ℤ) ∣ c} : Finset ℤ) :=
      mem_filter.2 ⟨h0, dvd_zero _⟩
    rw [card_erase_of_mem hmem, Nat.cast_sub (card_pos.2 ⟨0, hmem⟩), Nat.cast_one]
  · rw [erase_eq_of_notMem (fun h => h0 (mem_filter.1 h).1)]
    simp

theorem neg_sub_one_ediv {p : ℕ} (hp : 0 < p) (a : ℤ) :
    (-a - 1) / (p : ℤ) = -(a / p) - 1 := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have h := (Int.ediv_emod_unique (a := -a - 1) (r := p - 1 - a % p) (q := -(a / p) - 1)
    hp').2
    ⟨by have := Int.emod_add_mul_ediv a p; linarith,
     by have := Int.emod_lt_of_pos a hp'; omega,
     by have := Int.emod_nonneg a hp'.ne'; omega⟩
  exact h.1

/-- Number of nonzero multiples of `p` in `[s, s+m]` when `s ≤ 0 ≤ s + m`. -/
theorem card_Icc_filter_ne_zero_dvd_of_mem {p : ℕ} (hp : 0 < p) {s : ℤ} {m : ℕ} (hs : s ≤ 0)
    (hsm : 0 ≤ s + m) :
    (#{c ∈ Icc s (s + m) | c ≠ 0 ∧ (p : ℤ) ∣ c} : ℤ) = (-s) / p + (s + m) / p := by
  rw [card_Icc_filter_ne_zero_dvd hp, ite_eq_left (mem_Icc.2 ⟨hs, hsm⟩),
    show s - 1 = -(-s) - 1 by ring, neg_sub_one_ediv hp]
  ring

/-- Bound 1 in terms of `ι`: `μ - ⌊m/p⌋ = ι(s-1, m)`. -/
theorem card_Ico_filter_dvd_sub_eq_iota {p : ℕ} (hp : 0 < p) (s : ℤ) (m : ℕ) :
    (#{c ∈ Ico s (s + m) | (p : ℤ) ∣ c} : ℤ) - ((m / p : ℕ) : ℤ) = iotaZ p (s - 1) m := by
  rw [card_Ico_filter_dvd hp, iotaZ, Int.natCast_div]
  ring_nf

/-- Bound 3 in terms of `ι` (when `0 ∈ [s, s+m]`): `⌊m/p⌋ - μ' = ι(-s, s+m)`. -/
theorem sub_card_Icc_filter_ne_zero_dvd_eq_iota {p : ℕ} (hp : 0 < p) {s : ℤ} {m : ℕ}
    (hs : s ≤ 0) (hsm : 0 ≤ s + m) :
    ((m / p : ℕ) : ℤ) - #{c ∈ Icc s (s + m) | c ≠ 0 ∧ (p : ℤ) ∣ c} = iotaZ p (-s) (s + m) := by
  rw [card_Icc_filter_ne_zero_dvd_of_mem hp hs hsm, iotaZ, Int.natCast_div]
  ring_nf

end OddZeta
