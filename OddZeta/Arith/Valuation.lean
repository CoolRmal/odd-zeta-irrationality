import Mathlib

/-!
# Lower bounds for `p`-adic valuations

We write `VGe p e x` for "`v_p(x) ≥ e`", with the convention `v_p(0) = +∞`. This file develops
the calculus of this predicate (monotonicity, sums, products, integers, inverses) and the
**product lemma** for power series: if the `j`-th coefficient of each factor `f i` has valuation
at least `ν i - κ j`, then the `l`-th coefficient of `∏ i, f i` has valuation at least
`∑ i, ν i - κ l`.

Finally, a rational number whose valuation is nonnegative at every prime is an integer.
-/

open Finset PowerSeries

namespace OddZeta

/-- `x` has `p`-adic valuation at least `e` (with `v_p(0) = +∞`). -/
def VGe (p : ℕ) (e : ℤ) (x : ℚ) : Prop := x = 0 ∨ e ≤ padicValRat p x

section Basic

variable {p : ℕ} {e e' : ℤ} {x y : ℚ}

theorem vge_iff : VGe p e x ↔ (x ≠ 0 → e ≤ padicValRat p x) := by
  unfold VGe; tauto

theorem vge_zero (p : ℕ) (e : ℤ) : VGe p e 0 := Or.inl rfl

theorem vge_of_le (h : e ≤ padicValRat p x) : VGe p e x := Or.inr h

/-- Every rational has valuation at least its own valuation. -/
theorem vge_padicValRat (p : ℕ) (x : ℚ) : VGe p (padicValRat p x) x := Or.inr le_rfl

theorem VGe.mono (h : VGe p e x) (he : e' ≤ e) : VGe p e' x :=
  h.imp_right fun h' => he.trans h'

theorem VGe.neg (h : VGe p e x) : VGe p e (-x) := by
  rcases h with h | h
  · exact Or.inl (by simp [h])
  · exact Or.inr (by rwa [padicValRat.neg])

@[simp]
theorem vge_neg_iff : VGe p e (-x) ↔ VGe p e x :=
  ⟨fun h => by simpa using h.neg, VGe.neg⟩

theorem vge_one (p : ℕ) : VGe p 0 1 := Or.inr (by simp)

theorem vge_intCast' (p : ℕ) (z : ℤ) : VGe p (padicValInt p z) (z : ℚ) :=
  Or.inr (by rw [padicValRat.of_int])

theorem vge_intCast (p : ℕ) (z : ℤ) : VGe p 0 (z : ℚ) :=
  (vge_intCast' p z).mono (by positivity)

theorem vge_natCast' (p : ℕ) (n : ℕ) : VGe p (padicValNat p n) (n : ℚ) :=
  Or.inr (by rw [padicValRat.of_nat])

theorem vge_natCast (p : ℕ) (n : ℕ) : VGe p 0 (n : ℚ) :=
  (vge_natCast' p n).mono (by positivity)

theorem vge_ite {P : Prop} [Decidable P] {a b : ℚ} (ha : VGe p e a) (hb : VGe p e b) :
    VGe p e (if P then a else b) := by
  split_ifs <;> assumption

end Basic

section Prime

variable {p : ℕ} [Fact p.Prime] {e e' : ℤ} {x y : ℚ}

/-- `v_p(x⁻¹) = -v_p(x)`. -/
theorem vge_inv_self (x : ℚ) : VGe p (-padicValRat p x) x⁻¹ :=
  Or.inr (by rw [padicValRat.inv])

theorem vge_inv_intCast (z : ℤ) : VGe p (-(padicValInt p z : ℤ)) (z : ℚ)⁻¹ := by
  simpa [padicValRat.of_int] using vge_inv_self (z : ℚ)

theorem vge_one_div_natCast (c : ℕ) : VGe p (-(padicValNat p c : ℤ)) (1 / (c : ℚ)) := by
  simpa [padicValRat.of_nat] using vge_inv_self (c : ℚ)

theorem VGe.add (hx : VGe p e x) (hy : VGe p e y) : VGe p e (x + y) := by
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · rw [add_zero]; exact Or.inr hx
  exact Or.inr ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))

theorem VGe.sub (hx : VGe p e x) (hy : VGe p e y) : VGe p e (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem VGe.sum {ι : Type*} {s : Finset ι} {f : ι → ℚ} (h : ∀ i ∈ s, VGe p e (f i)) :
    VGe p e (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => exact vge_zero p e
  | cons a s ha ih =>
    rw [sum_cons]
    exact (h a (mem_cons_self a s)).add (ih fun i hi => h i (mem_cons_of_mem hi))

theorem VGe.mul (hx : VGe p e x) (hy : VGe p e' y) : VGe p (e + e') (x * y) := by
  by_cases hx0 : x = 0
  · exact Or.inl (by simp [hx0])
  by_cases hy0 : y = 0
  · exact Or.inl (by simp [hy0])
  have hx' := (vge_iff.1 hx) hx0
  have hy' := (vge_iff.1 hy) hy0
  exact Or.inr (by rw [padicValRat.mul hx0 hy0]; omega)

theorem VGe.prod {ι : Type*} {s : Finset ι} {f : ι → ℚ} {ν : ι → ℤ}
    (h : ∀ i ∈ s, VGe p (ν i) (f i)) : VGe p (∑ i ∈ s, ν i) (∏ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using vge_one p
  | cons a s ha ih =>
    rw [sum_cons, prod_cons]
    exact (h a (mem_cons_self a s)).mul (ih fun i hi => h i (mem_cons_of_mem hi))

theorem VGe.pow (hx : VGe p e x) (n : ℕ) : VGe p (n * e) (x ^ n) := by
  simpa using VGe.prod (s := range n) (f := fun _ => x) (ν := fun _ => e) (fun _ _ => hx)

theorem VGe.intCast_mul (z : ℤ) (hx : VGe p e x) : VGe p e (z * x) := by
  simpa using (vge_intCast p z).mul hx

theorem VGe.mul_intCast (z : ℤ) (hx : VGe p e x) : VGe p e (x * z) := by
  simpa using hx.mul (vge_intCast p z)

theorem VGe.natCast_mul (n : ℕ) (hx : VGe p e x) : VGe p e (n * x) := by
  simpa using (vge_natCast p n).mul hx

/-- Valuation bound for the inverse of a nonzero integer power. -/
theorem vge_inv_intCast_pow (z : ℤ) (n : ℕ) :
    VGe p (-(n * (padicValInt p z : ℤ))) ((z : ℚ)⁻¹ ^ n) := by
  simpa using (vge_inv_intCast z).pow n

/-- A rational has nonnegative valuation iff `p` does not divide its denominator. -/
theorem vge_zero_iff_not_dvd_den : VGe p 0 x ↔ ¬ p ∣ x.den := by
  have hp := (Fact.out : p.Prime)
  by_cases hx : x = 0
  · subst hx; simp [vge_zero, hp.one_lt.ne']
  rw [vge_iff, padicValRat_def]
  have hnum : x.num ≠ 0 := Rat.num_ne_zero.2 hx
  constructor
  · intro h hd
    have h1 : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_nz hd
    have h2 : padicValInt p x.num = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro hn
      have : (p : ℤ) ∣ (x.den : ℤ) := Int.natCast_dvd_natCast.2 hd
      have hc := x.reduced
      have : p ∣ Nat.gcd x.num.natAbs x.den :=
        Nat.dvd_gcd (Int.natCast_dvd.1 hn) hd
      rw [hc] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    have := h hx
    omega
  · intro hd _
    rw [padicValNat.eq_zero_of_not_dvd hd]
    simp

end Prime

/-- A rational number with nonnegative valuation at every prime is an integer. -/
theorem exists_int_eq_of_forall_vge {x : ℚ} (h : ∀ p : ℕ, p.Prime → VGe p 0 x) :
    ∃ z : ℤ, x = z := by
  refine ⟨x.num, (Rat.coe_int_num_of_den_eq_one ?_).symm⟩
  refine Nat.eq_one_iff_not_exists_prime_dvd.2 fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  exact vge_zero_iff_not_dvd_den.1 (h p hp)

/-! ### Power series -/

section PowerSeries

variable {p : ℕ}

/-- Constants: only the constant coefficient matters. -/
theorem vge_coeff_C {a : ℚ} {ν : ℤ} (κ : ℤ) (ha : VGe p ν a) (j : ℕ) :
    VGe p (ν - κ * j) (coeff j (C a)) := by
  rw [coeff_C]
  split_ifs with hj
  · subst hj; simpa using ha
  · exact vge_zero p _

theorem vge_coeff_X_pow (κ : ℤ) (n j : ℕ) :
    VGe p (κ * n - κ * j) (coeff j ((X : PowerSeries ℚ) ^ n)) := by
  rw [coeff_X_pow]
  split_ifs with hj
  · subst hj; simpa using vge_one p
  · exact vge_zero p _

theorem vge_coeff_X (κ : ℤ) (j : ℕ) : VGe p (κ - κ * j) (coeff j (X : PowerSeries ℚ)) := by
  simpa using vge_coeff_X_pow (p := p) κ 1 j

/-- The linear factor `c + X`: coefficient `0` is `c`, coefficient `1` is `1`. -/
theorem vge_coeff_C_add_X {c : ℚ} {ν κ : ℤ} (hc : VGe p ν c) (hνκ : ν ≤ κ) (j : ℕ) :
    VGe p (ν - κ * j) (coeff j (C c + X)) := by
  rw [map_add, coeff_C, coeff_X]
  rcases j with _ | _ | j
  · simpa using hc
  · simpa using (vge_one p).mono (by omega)
  · simpa using vge_zero p _

end PowerSeries

section PowerSeriesPrime

variable {p : ℕ} [Fact p.Prime]

/-- Product lemma for two power series. -/
theorem vge_coeff_mul {f g : PowerSeries ℚ} {a b κ : ℤ}
    (hf : ∀ j : ℕ, VGe p (a - κ * j) (coeff j f)) (hg : ∀ j : ℕ, VGe p (b - κ * j) (coeff j g))
    (l : ℕ) : VGe p (a + b - κ * l) (coeff l (f * g)) := by
  rw [coeff_mul]
  refine VGe.sum fun ij hij => ?_
  have hl : ij.1 + ij.2 = l := mem_antidiagonal.1 hij
  have := (hf ij.1).mul (hg ij.2)
  refine this.mono (le_of_eq ?_)
  rw [← hl]; push_cast; ring

/-- **Product lemma**: if the `j`-th coefficient of `f i` has valuation at least `ν i - κ j` for
all `i ∈ s` and all `j`, then the `l`-th coefficient of `∏ i ∈ s, f i` has valuation at least
`∑ i ∈ s, ν i - κ l`. -/
theorem vge_coeff_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (ν : ι → ℤ) (κ : ℤ)
    (h : ∀ i ∈ s, ∀ j : ℕ, VGe p (ν i - κ * j) (coeff j (f i))) (l : ℕ) :
    VGe p ((∑ i ∈ s, ν i) - κ * l) (coeff l (∏ i ∈ s, f i)) := by
  induction s using Finset.cons_induction generalizing l with
  | empty =>
    rw [prod_empty, coeff_one]
    split_ifs with hl
    · subst hl; simpa using vge_one p
    · exact vge_zero p _
  | cons a s ha ih =>
    rw [sum_cons, prod_cons]
    exact vge_coeff_mul (h a (mem_cons_self a s))
      (ih fun i hi => h i (mem_cons_of_mem hi)) l

theorem vge_coeff_C_mul {a : ℚ} {f : PowerSeries ℚ} {ν b κ : ℤ} (ha : VGe p ν a)
    (hf : ∀ j : ℕ, VGe p (b - κ * j) (coeff j f)) (l : ℕ) :
    VGe p (ν + b - κ * l) (coeff l (C a * f)) := by
  rw [coeff_C_mul]
  simpa [add_sub_assoc] using ha.mul (hf l)

theorem vge_coeff_mul_C {a : ℚ} {f : PowerSeries ℚ} {ν b κ : ℤ} (ha : VGe p ν a)
    (hf : ∀ j : ℕ, VGe p (b - κ * j) (coeff j f)) (l : ℕ) :
    VGe p (b + ν - κ * l) (coeff l (f * C a)) := by
  rw [mul_comm f, add_comm b]
  exact vge_coeff_C_mul ha hf l

end PowerSeriesPrime

end OddZeta
