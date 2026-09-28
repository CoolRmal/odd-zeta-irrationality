import OddZeta.Setup.Rational
import OddZeta.Arith.Bricks
import OddZeta.Phi.Defs
import OddZeta.Arith.DeltaAux

/-!
# The denominators `Δₙ` (Lemma 3.2 of the note, Lemma 19 of Zudilin)

`Δₙ = ∏_{p ≤ h₀} p^{e_p}` with
* `e_p = 3q ⌊log_p h₀⌋` for `p ≤ √h₀` (crude treatment of small primes);
* `e_p = r[p ≤ m̂₁n] + ∑_{j≥2} [p ≤ m̂ⱼn] - [p ≤ m̂₀n] φ'(n/p)` for `p > √h₀`, where `φ'` is any
  function bounded by `φ₀` (in the application, the certified step function of `OddZeta.Phi`).

Then `Δₙ A_{s,n} ∈ ℤ` and `Δₙ A_{0,n} ∈ ℤ`.
-/

namespace OddZeta

namespace Params

variable (P : Params)

/-- `m̂₀ = max(η_r, η₀ - 2η_{r+1})`. -/
def mhat0 : ℕ := max (P.zs.foldr max 0) (P.eta0 - 2 * P.etaMin)

/-- `m̂ⱼ = max(m̂₀, η₀ - η₁ - η_{r+j})` for `j = 1, …, q-r` (in the order of `ps`, which is
increasing, so that `m̂₁ ≥ m̂₂ ≥ ⋯`). -/
def mhats : List ℕ := P.ps.map fun η => max P.mhat0 (P.eta0 - P.etaOne - η)

/-- `m̂₁`. -/
def mhat1 : ℕ := P.mhats.headD 0

/-- The exponent of a prime `p > √h₀` in `D_{m̂₁n}^r D_{m̂₂n} ⋯ D_{m̂_{q-r}n}`:
`r [p ≤ m̂₁n] + ∑_{j ≥ 2} [p ≤ m̂ⱼn]`. -/
def dExp (n p : ℕ) : ℕ :=
  (P.r - 1) * (if p ≤ P.mhat1 * n then 1 else 0) + (P.mhats.filter fun m => p ≤ m * n).length

/-- The exponent of `p` in `Δₙ`. -/
noncomputable def deltaExp (φ' : ℝ → ℕ) (n p : ℕ) : ℤ :=
  if p * p ≤ P.h0 n then ((3 * P.q * Nat.log p (P.h0 n) : ℕ) : ℤ)
  else (P.dExp n p : ℤ) - (if p ≤ P.mhat0 * n then (φ' ((n : ℝ) / p) : ℤ) else 0)

/-- The denominator `Δₙ` (formula (3.3) of the note, modified at the small primes). -/
noncomputable def Delta (φ' : ℝ → ℕ) (n : ℕ) : ℚ :=
  ∏ p ∈ (Finset.range (P.h0 n + 1)).filter Nat.Prime, (p : ℚ) ^ P.deltaExp φ' n p

variable {P}

theorem Delta_pos (φ' : ℝ → ℕ) (n : ℕ) : 0 < P.Delta φ' n :=
  Finset.prod_pos fun p hp => zpow_pos (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos) _

namespace DeltaAux

open Finset PowerSeries

theorem le_foldr_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) : l.foldr max 0 ≤ b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem le_mhat0 {η : ℕ} (hη : η ∈ P.zs) : η ≤ P.mhat0 :=
  (le_foldr_max hη).trans (le_max_left _ _)

theorem mhat0_le_eta0 (hP : P.Valid) : P.mhat0 ≤ P.eta0 := by
  have h2 := hP.two_mul_lt _ hP.etaMin_mem
  refine max_le (foldr_max_le fun x hx => ?_) (Nat.sub_le _ _)
  have := hP.zs_le_etaMin x hx
  omega

theorem mhat0_le_of_mem_mhats {m : ℕ} (hm : m ∈ P.mhats) : P.mhat0 ≤ m := by
  unfold mhats at hm
  obtain ⟨η, _, rfl⟩ := List.mem_map.1 hm
  exact le_max_left _ _

theorem mhat1_eq {a : ℕ} {t : List ℕ} (ht : P.ps = a :: t) :
    P.mhat1 = max P.mhat0 (P.eta0 - P.etaOne - a) := by
  simp [mhat1, mhats, ht]

theorem mhat0_le_mhat1 (hP : P.Valid) : P.mhat0 ≤ P.mhat1 := by
  obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hP.etaMin_mem)
  rw [mhat1_eq ht]
  exact le_max_left _ _

/-- For `p ≤ m̂₀ n` every factor of the `D`-product contains `p`. -/
theorem dExp_eq (hP : P.Valid) {n p : ℕ} (hp : p ≤ P.mhat0 * n) : P.dExp n p = P.q - 1 := by
  unfold dExp
  have h1 : p ≤ P.mhat1 * n := hp.trans (Nat.mul_le_mul_right n (mhat0_le_mhat1 hP))
  rw [ite_eq_left h1, List.filter_eq_self.2 fun m hm => by
    simpa using hp.trans (Nat.mul_le_mul_right n (mhat0_le_of_mem_mhats hm))]
  have : P.mhats.length = P.ps.length := by simp [mhats]
  have hr := hP.three_le_r
  simp only [q, r] at hr ⊢
  omega

/-- If `p ≤ k - h₁` then each pole block containing `k` contributes to `dExp`. -/
theorem dExp_ge (hsorted : P.ps.Pairwise (· ≤ ·)) {n k p : ℕ}
    (hpk : p ≤ k - hh P.etaOne n) (hord : 1 ≤ poleCount P n k) :
    P.r - 1 + poleCount P n k ≤ P.dExp n p := by
  have key : ∀ η, hh η n ≤ k ∧ k ≤ P.h0 n - hh η n → p ≤ (P.eta0 - P.etaOne - η) * n := by
    intro η hb
    rw [Nat.sub_mul, Nat.sub_mul]
    simp only [hh, h0] at hb hpk
    omega
  obtain ⟨η, hη, hb⟩ : ∃ η ∈ P.ps, hh η n ≤ k ∧ k ≤ P.h0 n - hh η n := by
    unfold poleCount at hord
    obtain ⟨η, hη, hq⟩ := List.countP_pos_iff.1 hord
    exact ⟨η, hη, by simpa using hq⟩
  have hm1 : p ≤ P.mhat1 * n := by
    obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hη)
    have ha : a ≤ η := by
      rw [ht] at hsorted hη
      rcases List.mem_cons.1 hη with rfl | h
      · exact le_rfl
      · exact List.rel_of_pairwise_cons hsorted h
    rw [mhat1_eq ht]
    exact (key η hb).trans (Nat.mul_le_mul_right n
      ((Nat.sub_le_sub_left ha _).trans (le_max_right _ _)))
  unfold dExp
  rw [ite_eq_left hm1, mul_one]
  have : poleCount P n k ≤ (P.mhats.filter fun m => p ≤ m * n).length := by
    unfold poleCount mhats
    rw [← List.countP_eq_length_filter, List.countP_map]
    refine List.countP_mono_left fun η _ hb => ?_
    simp only [Function.comp, decide_eq_true_eq] at hb ⊢
    exact (key η hb).trans (Nat.mul_le_mul_right n (le_max_right _ _))
  omega

/-- The valuation of `Δₙ`. -/
theorem vge_Delta {p : ℕ} [hp : Fact p.Prime] (φ' : ℝ → ℕ) (n : ℕ) :
    VGe p (if p ≤ P.h0 n then P.deltaExp φ' n p else 0) (P.Delta φ' n) := by
  unfold Delta
  have h := VGe.prod (p := p) (s := (range (P.h0 n + 1)).filter Nat.Prime)
    (f := fun p' => (p' : ℚ) ^ P.deltaExp φ' n p')
    (ν := fun p' => if p' = p then P.deltaExp φ' n p' else 0) (fun p' hp' => by
      refine vge_of_le (le_of_eq ?_)
      rw [padicValRat.zpow]
      split_ifs with h
      · subst h
        rw [padicValRat.self hp.out.one_lt, mul_one]
      · have := Fact.mk (mem_filter.1 hp').2
        rw [padicValRat.of_nat, padicValNat_primes (Ne.symm h)]
        simp)
  refine h.mono (le_of_eq ?_)
  rw [sum_ite_eq']
  simp [mem_filter, hp.out]

/-- The summand of `A_{0,n}`. -/
noncomputable def cterm (P : Params) (n i k : ℕ) : ℚ :=
  ((i + P.r - 2).choose (P.r - 1) : ℚ) * P.coef n i k *
    ∑ l ∈ Finset.Icc 1 (k - hh P.etaOne n), ((l : ℚ) ^ (i + P.r - 1))⁻¹

theorem vge_cterm {p : ℕ} [Fact p.Prime] {n i k : ℕ} {a b : ℤ} (hc : VGe p a (P.coef n i k))
    (hh : VGe p b (∑ l ∈ Finset.Icc 1 (k - hh P.etaOne n), ((l : ℚ) ^ (i + P.r - 1))⁻¹)) :
    VGe p (a + b) (cterm P n i k) := by
  unfold cterm
  exact (((vge_natCast p _).mul hc).mul hh).mono (le_of_eq (by ring))

theorem k_le_h0 {n k : ℕ} (hk : k ∈ P.poleRange n) : k ≤ P.h0 n := by
  rw [mem_poleRange_iff] at hk
  omega

/-- Small primes `p² ≤ h₀`. -/
theorem small_case (hP : P.Valid) {p : ℕ} [Fact p.Prime] {n k : ℕ} (hk : k ∈ P.poleRange n) :
    (∀ i, VGe p (-((3 * P.q * Nat.log p (P.h0 n) : ℕ) : ℤ)) (P.coef n i k)) ∧
    ∀ i ∈ Icc 1 (P.q - P.r), VGe p (-((3 * P.q * Nat.log p (P.h0 n) : ℕ) : ℤ)) (cterm P n i k) := by
  set L := Nat.log p (P.h0 n) with hL
  have hkh := k_le_h0 hk
  have hc : ∀ i, VGe p (-((L : ℤ) * ((P.q - P.r - i : ℕ) : ℤ))) (P.coef n i k) :=
    fun i => vge_coeff_expan_small hP hk _
  refine ⟨fun i => (hc i).mono ?_, fun i hi => ?_⟩
  · have : L * (P.q - P.r - i) ≤ 3 * P.q * L := by
      calc L * (P.q - P.r - i) ≤ L * (3 * P.q) := Nat.mul_le_mul_left _ (by omega)
        _ = 3 * P.q * L := by ring
    have : ((L * (P.q - P.r - i) : ℕ) : ℤ) ≤ ((3 * P.q * L : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at this ⊢
    linarith
  · have hharm := vge_harm (p := p) (k - hh P.etaOne n) (i + P.r - 1) L fun l hl =>
      (padicValNat_le_nat_log l).trans (Nat.log_mono_right (by rw [mem_Icc] at hl; omega))
    refine (vge_cterm (hc i) hharm).mono ?_
    rw [mem_Icc] at hi
    have : L * (P.q - P.r - i) + (i + P.r - 1) * L ≤ 3 * P.q * L := by
      calc L * (P.q - P.r - i) + (i + P.r - 1) * L = L * ((P.q - P.r - i) + (i + P.r - 1)) := by
            ring
        _ ≤ L * (3 * P.q) := Nat.mul_le_mul_left _ (by omega)
        _ = 3 * P.q * L := by ring
    have : ((L * (P.q - P.r - i) + (i + P.r - 1) * L : ℕ) : ℤ) ≤ ((3 * P.q * L : ℕ) : ℤ) := by
      exact_mod_cast this
    push_cast at this ⊢
    linarith

/-- Medium primes `√h₀ < p ≤ m̂₀ n`. -/
theorem medium_case (hP : P.Valid) {φ' : ℝ → ℕ}
    (hφ : ∀ x y : ℝ, (φ' x : ℤ) ≤ phi0 P.eta0 P.zs P.ps x y) {p : ℕ} [Fact p.Prime] {n k : ℕ}
    (hk : k ∈ P.poleRange n) (hs : P.h0 n < p ^ 2) :
    (∀ i, VGe p ((φ' ((n : ℝ) / p) : ℤ) - ((P.q - 1 : ℕ) : ℤ)) (P.coef n i k)) ∧
    ∀ i ∈ Icc 1 (P.q - P.r),
      VGe p ((φ' ((n : ℝ) / p) : ℤ) - ((P.q - 1 : ℕ) : ℤ)) (cterm P n i k) := by
  have hkh := k_le_h0 hk
  have hr := hP.three_le_r
  have hc : ∀ i, VGe p ((φ' ((n : ℝ) / p) : ℤ) - ((P.q - P.r - i : ℕ) : ℤ)) (P.coef n i k) :=
    fun i => (vge_coeff_expan_medium hP hk hs _).mono (by
      have := hφ ((n : ℝ) / p) (((k : ℝ) - 1) / p)
      linarith)
  refine ⟨fun i => (hc i).mono ?_, fun i hi => ?_⟩
  · have : P.q - P.r - i ≤ P.q - 1 := by omega
    have : ((P.q - P.r - i : ℕ) : ℤ) ≤ ((P.q - 1 : ℕ) : ℤ) := by exact_mod_cast this
    linarith
  · have hharm := vge_harm (p := p) (k - hh P.etaOne n) (i + P.r - 1) 1 fun l hl =>
      (padicValNat_le_nat_log l).trans ((Nat.log_mono_right (by rw [mem_Icc] at hl; omega)).trans
        (log_le_one_of_lt_sq hs))
    refine (vge_cterm (hc i) hharm).mono ?_
    rw [mem_Icc] at hi
    have : (P.q - P.r - i) + (i + P.r - 1) = P.q - 1 := by omega
    have : ((P.q - P.r - i : ℕ) : ℤ) + ((i + P.r - 1 : ℕ) : ℤ) = ((P.q - 1 : ℕ) : ℤ) := by
      exact_mod_cast this
    push_cast
    linarith

/-- Large primes `p > m̂₀ n`, `p² > h₀`. -/
theorem large_case (hP : P.Valid) (hsorted : P.ps.Pairwise (· ≤ ·)) {p : ℕ} [Fact p.Prime]
    {n k : ℕ} (hk : k ∈ P.poleRange n) (hs : P.h0 n < p ^ 2) (hm : P.mhat0 * n < p) :
    (∀ i, VGe p (-(if p ≤ P.h0 n then (P.dExp n p : ℤ) else 0)) (P.coef n i k)) ∧
    ∀ i ∈ Icc 1 (P.q - P.r),
      VGe p (-(if p ≤ P.h0 n then (P.dExp n p : ℤ) else 0)) (cterm P n i k) := by
  have hkh := k_le_h0 hk
  have hr := hP.three_le_r
  have hD : 0 ≤ (if p ≤ P.h0 n then (P.dExp n p : ℤ) else 0) := by split_ifs <;> positivity
  have hz : ∀ η ∈ P.zs, η * n < p := fun η hη =>
    lt_of_le_of_lt (Nat.mul_le_mul_right n (le_mhat0 hη)) hm
  have hpole : P.h0 n - 2 * hh P.etaMin n < p := by
    have h1 : P.eta0 - 2 * P.etaMin ≤ P.mhat0 := le_max_right _ _
    have := Nat.mul_le_mul_right n h1
    rw [Nat.sub_mul, mul_assoc] at this
    simp only [h0, hh]
    omega
  have hc : ∀ i, VGe p 0 (P.coef n i k) := fun i => vge_coeff_expan_large hP hk hz hpole _
  refine ⟨fun i => (hc i).mono (by linarith), fun i hi => ?_⟩
  rw [mem_Icc] at hi
  by_cases hc0 : P.coef n i k = 0
  · unfold cterm
    rw [hc0, mul_zero, zero_mul]
    exact vge_zero p _
  have hord := le_poleCount_of_coef_ne_zero hP hk hi.2 hc0
  by_cases hkp : k - hh P.etaOne n < p
  · have hharm := vge_harm (p := p) (k - hh P.etaOne n) (i + P.r - 1) 0 fun l hl => by
      rw [mem_Icc] at hl
      exact (padicValNat_eq_zero_of_lt hl.1 (by omega)).le
    refine (vge_cterm (hc i) hharm).mono ?_
    simp only [Nat.cast_zero, mul_zero, neg_zero, add_zero]
    linarith
  · rw [not_lt] at hkp
    have hph : p ≤ P.h0 n := by omega
    have hdExp := dExp_ge hsorted hkp (by omega)
    have hharm := vge_harm (p := p) (k - hh P.etaOne n) (i + P.r - 1) 1 fun l hl =>
      (padicValNat_le_nat_log l).trans ((Nat.log_mono_right (by rw [mem_Icc] at hl; omega)).trans
        (log_le_one_of_lt_sq hs))
    refine (vge_cterm (hc i) hharm).mono ?_
    rw [ite_eq_left hph]
    have : i + P.r - 1 ≤ P.dExp n p := by omega
    have : ((i + P.r - 1 : ℕ) : ℤ) ≤ (P.dExp n p : ℤ) := by exact_mod_cast this
    push_cast at this ⊢
    linarith

end DeltaAux

/-- **Lemma 3.2**: `Δₙ A_{s,n} ∈ ℤ` for the odd `s ∈ [r+2, q-2]`, and `Δₙ A_{0,n} ∈ ℤ`. -/
theorem Delta_mul_isInt (hP : P.Valid) (hsorted : P.ps.Pairwise (· ≤ ·)) {φ' : ℝ → ℕ}
    (hφ : ∀ x y : ℝ, (φ' x : ℤ) ≤ phi0 P.eta0 P.zs P.ps x y) {n : ℕ} (hn : 1 ≤ n) :
    (∀ s ∈ P.oddRange, ∃ z : ℤ, P.Delta φ' n * P.coefZeta n s = z) ∧
      ∃ z : ℤ, P.Delta φ' n * P.coefConst n = z := by
  classical
  have key : ∀ p : ℕ, p.Prime →
      (∀ s ∈ P.oddRange, VGe p 0 (P.Delta φ' n * P.coefZeta n s)) ∧
        VGe p 0 (P.Delta φ' n * P.coefConst n) := by
    intro p hp
    have := Fact.mk hp
    set D : ℤ := if p ≤ P.h0 n then P.deltaExp φ' n p else 0 with hD
    have hDel : VGe p D (P.Delta φ' n) := DeltaAux.vge_Delta φ' n
    obtain ⟨hcoef, hterm⟩ : (∀ k ∈ P.poleRange n, ∀ i, VGe p (-D) (P.coef n i k)) ∧
        ∀ k ∈ P.poleRange n, ∀ i ∈ Finset.Icc 1 (P.q - P.r),
          VGe p (-D) (DeltaAux.cterm P n i k) := by
      by_cases hs : p * p ≤ P.h0 n
      · have hD' : D = ((3 * P.q * Nat.log p (P.h0 n) : ℕ) : ℤ) := by
          rw [hD, ite_eq_left (le_trans (Nat.le_mul_self p) hs), deltaExp, ite_eq_left hs]
        rw [hD']
        exact ⟨fun k hk => (DeltaAux.small_case hP hk).1,
          fun k hk => (DeltaAux.small_case hP hk).2⟩
      have hs' : P.h0 n < p ^ 2 := by rw [sq]; omega
      by_cases hm : p ≤ P.mhat0 * n
      · have hph : p ≤ P.h0 n := by
          have := Nat.mul_le_mul_right n (DeltaAux.mhat0_le_eta0 hP)
          simp only [h0]
          omega
        have hD' : -D = (φ' ((n : ℝ) / p) : ℤ) - ((P.q - 1 : ℕ) : ℤ) := by
          rw [hD, ite_eq_left hph, deltaExp, ite_eq_right hs, ite_eq_left hm,
            DeltaAux.dExp_eq hP hm]
          ring
        rw [hD']
        exact ⟨fun k hk => (DeltaAux.medium_case hP hφ hk hs').1,
          fun k hk => (DeltaAux.medium_case hP hφ hk hs').2⟩
      · have hD' : D = if p ≤ P.h0 n then (P.dExp n p : ℤ) else 0 := by
          rw [hD, deltaExp, ite_eq_right hs, ite_eq_right hm, sub_zero]
        rw [hD']
        exact ⟨fun k hk => (DeltaAux.large_case hP hsorted hk hs' (by omega)).1,
          fun k hk => (DeltaAux.large_case hP hsorted hk hs' (by omega)).2⟩
    have hZ : ∀ s ∈ P.oddRange, VGe p (-D) (P.coefZeta n s) := fun s _ => by
      unfold coefZeta
      exact ((vge_natCast p _).mul (VGe.sum fun k hk => hcoef k hk _)).mono
        (le_of_eq (zero_add _).symm)
    have hC : VGe p (-D) (P.coefConst n) :=
      VGe.sum fun k hk => VGe.sum fun i hi => hterm k hk i hi
    exact ⟨fun s hs => (hDel.mul (hZ s hs)).mono (add_neg_cancel D).ge,
      (hDel.mul hC).mono (add_neg_cancel D).ge⟩
  exact ⟨fun s hs => exists_int_eq_of_forall_vge fun p hp => (key p hp).1 s hs,
    exists_int_eq_of_forall_vge fun p hp => (key p hp).2⟩

end Params

end OddZeta
