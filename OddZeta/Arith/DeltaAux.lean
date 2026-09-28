import OddZeta.Setup.Rational
import OddZeta.Arith.Bricks
import OddZeta.Phi.Defs

/-!
# Auxiliary results for Lemma 3.2 (the denominators `Δₙ`)

* `Params.expan_eq`: the expansion `ε^{q-r} Rₙ(-k+ε)` at a pole is the product of the linear
  factor `(h₀ - 2k) + 2ε`, the polynomial bricks `polyBrick (1-k) (ηn)`,
  `polyBrick (h₀-h+1-k) (ηn)` of the zero blocks and the pole bricks `poleBrick (h-k) (h₀-2h)`
  of the pole blocks.
* Valuation bounds for its coefficients for small primes (`vge_coeff_expan_small`), medium primes
  (`vge_coeff_expan_medium`, in terms of `φ₀`) and large primes (`vge_coeff_expan_large`).
* `le_poleCount_of_coef_ne_zero`: `a_{i,k} ≠ 0` forces `-k` to be a pole of order `≥ i`.
* `vge_harm`: valuation of the harmonic sums `∑_{l ≤ N} l^{-e}`.
-/

open Finset PowerSeries

namespace OddZeta.Params.DeltaAux

variable {P : Params}

/-- Taylor shift followed by the coercion to power series, as a ring homomorphism. -/
noncomputable def tayl (a : ℚ) : Polynomial ℚ →+* PowerSeries ℚ :=
  Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.taylorAlgHom a).toRingHom

theorem tayl_apply (a : ℚ) (f : Polynomial ℚ) :
    tayl a f = ((Polynomial.taylor a f : Polynomial ℚ) : PowerSeries ℚ) := rfl

theorem tayl_X_add_C (a b : ℚ) :
    tayl a (Polynomial.X + Polynomial.C b) = C (b + a) + X := by
  rw [tayl_apply, Polynomial.taylor_apply, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.C_comp]
  simp only [Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C, map_add]
  ring

theorem tayl_pochPoly (k a b : ℕ) :
    tayl (-(k : ℚ)) (pochPoly a b) =
      ∏ c ∈ Ico ((a : ℤ) - k) ((a : ℤ) - k + ((b - a : ℕ) : ℤ)), (C (c : ℚ) + X) := by
  rw [pochPoly, map_prod, prod_Ico_eq_prod_range, prod_Ico_int_eq_prod_range]
  refine prod_congr rfl fun j _ => ?_
  rw [tayl_X_add_C]
  push_cast
  ring_nf

theorem tayl_zeroPoly {n η k : ℕ} (h : hh η n ≤ P.h0 n) :
    tayl (-(k : ℚ)) (P.zeroPoly n η) =
      polyBrick (1 - k) (η * n) * polyBrick ((P.h0 n : ℤ) - hh η n + 1 - k) (η * n) := by
  rw [zeroPoly, map_mul, map_mul, tayl_pochPoly, tayl_pochPoly]
  have e1 : hh η n - 1 = η * n := by simp [hh]
  have e2 : P.h0 n - (P.h0 n - hh η n + 1) = η * n := by
    have : hh η n = η * n + 1 := rfl
    omega
  have e3 : ((P.h0 n - hh η n + 1 : ℕ) : ℤ) = (P.h0 n : ℤ) - hh η n + 1 := by
    push_cast [h]; ring
  rw [e1, e2, e3, polyBrick, polyBrick]
  simp only [tayl_apply, Polynomial.taylor_C, Polynomial.coe_C]
  push_cast
  rw [map_pow]
  ring


theorem two_mul_hh_le_h0 {n η : ℕ} (h : 2 * η < P.eta0) : 2 * hh η n ≤ P.h0 n := by
  have : 2 * η * n ≤ P.eta0 * n := Nat.mul_le_mul_right n h.le
  simp only [hh, h0]
  nlinarith

theorem hh_le_hh_of_le {n η η' : ℕ} (h : η ≤ η') : hh η n ≤ hh η' n := by
  simp only [hh]
  have := Nat.mul_le_mul_right n h
  omega

theorem poleLocal_eq {n η k : ℕ} (hk : k ∈ P.poleRange n) (hη : P.etaMin ≤ η)
    (h2 : 2 * hh η n ≤ P.h0 n) :
    P.poleLocal n η k = poleBrick ((hh η n : ℤ) - k) (P.h0 n - 2 * hh η n) := by
  set K := P.poleRange n with hK
  set B := Icc (hh η n) (P.h0 n - hh η n) with hB
  set g : ℕ → PowerSeries ℚ := fun k' => C ((k' : ℚ) - k) + X with hg
  have hmin : hh P.etaMin n ≤ hh η n := hh_le_hh_of_le hη
  have hBK : B ⊆ K := by
    intro x hx
    simp only [hB, hK, poleRange, mem_Icc] at hx ⊢
    omega
  have e1 : ∏ c ∈ Icc ((hh η n : ℤ) - k) ((hh η n : ℤ) - k + ((P.h0 n - 2 * hh η n : ℕ) : ℤ)),
      (C (c : ℚ) + X) = ∏ k' ∈ B, g k' := by
    rw [show Icc ((hh η n : ℤ) - k) ((hh η n : ℤ) - k + ((P.h0 n - 2 * hh η n : ℕ) : ℤ)) =
        Ico ((hh η n : ℤ) - k) ((hh η n : ℤ) - k + ((P.h0 n - 2 * hh η n + 1 : ℕ) : ℤ)) by
      ext c; simp only [mem_Icc, mem_Ico]; push_cast; omega]
    rw [prod_Ico_int_eq_prod_range, hB, ← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
    have : P.h0 n - hh η n + 1 - hh η n = P.h0 n - 2 * hh η n + 1 := by omega
    rw [this]
    refine prod_congr rfl fun j _ => ?_
    simp only [hg]
    push_cast
    ring_nf
  have e2 : tayl (-(k : ℚ)) (P.polePoly n η) =
      C ((P.h0 n - 2 * hh η n).factorial : ℚ) * ∏ k' ∈ K \ B, g k' := by
    rw [polePoly, map_mul, map_prod]
    congr 1
    · rw [tayl_apply, Polynomial.taylor_C, Polynomial.coe_C]
    · refine prod_congr rfl fun k' _ => ?_
      rw [tayl_X_add_C]
      simp only [hg, sub_eq_add_neg]
  have hprod : (∏ k' ∈ K \ B, g k') * ∏ k' ∈ B, g k' = g k * ∏ k' ∈ K.erase k, g k' := by
    rw [prod_sdiff hBK, mul_prod_erase K g hk]
  have hgk : g k = X := by simp [hg]
  have hinv : (∏ k' ∈ K.erase k, g k') * (∏ k' ∈ K.erase k, g k')⁻¹ = 1 := by
    refine PowerSeries.mul_inv_cancel _ ?_
    rw [map_prod]
    refine prod_ne_zero_iff.2 fun k' hk' => ?_
    have hne : k' ≠ k := ne_of_mem_erase hk'
    have : (k' : ℚ) - k ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
    simpa [hg] using this
  rw [eq_poleBrick_iff, e1]
  unfold poleLocal
  rw [← tayl_apply, e2]
  calc C ((P.h0 n - 2 * hh η n).factorial : ℚ) * (∏ k' ∈ K \ B, g k') *
        (∏ k' ∈ K.erase k, g k')⁻¹ * ∏ k' ∈ B, g k'
      = C ((P.h0 n - 2 * hh η n).factorial : ℚ) * ((∏ k' ∈ K \ B, g k') * ∏ k' ∈ B, g k') *
        (∏ k' ∈ K.erase k, g k')⁻¹ := by ring
    _ = C ((P.h0 n - 2 * hh η n).factorial : ℚ) * X *
        ((∏ k' ∈ K.erase k, g k') * (∏ k' ∈ K.erase k, g k')⁻¹) := by
      rw [hprod, hgk]; ring
    _ = C ((P.h0 n - 2 * hh η n).factorial : ℚ) * X := by rw [hinv, mul_one]

theorem tayl_linear (k h : ℕ) :
    tayl (-(k : ℚ)) (Polynomial.C (h : ℚ) + 2 * Polynomial.X) = C ((h : ℚ) - 2 * k) + C 2 * X := by
  rw [map_add, map_mul, map_ofNat, tayl_apply, tayl_apply, Polynomial.taylor_C,
    Polynomial.taylor_X, Polynomial.coe_C, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C]
  simp only [map_sub, map_mul, map_neg, map_natCast, map_ofNat]
  ring

/-- The expansion at a pole as a product of bricks. -/
theorem expan_eq (hP : P.Valid) {n k : ℕ} (hk : k ∈ P.poleRange n) :
    P.expan n k = (C ((P.h0 n : ℚ) - 2 * k) + C 2 * X) *
      (P.zs.map fun η => polyBrick (1 - k) (η * n) *
        polyBrick ((P.h0 n : ℤ) - hh η n + 1 - k) (η * n)).prod *
      (P.ps.map fun η => poleBrick ((hh η n : ℤ) - k) (P.h0 n - 2 * hh η n)).prod := by
  have hmin := hP.two_mul_lt _ hP.etaMin_mem
  have hZ : P.zs.map (⇑(tayl (-(k : ℚ))) ∘ P.zeroPoly n) = P.zs.map fun η =>
      polyBrick (1 - k) (η * n) * polyBrick ((P.h0 n : ℤ) - hh η n + 1 - k) (η * n) := by
    refine List.map_congr_left fun η hη => ?_
    have h1 := hP.zs_le_etaMin η hη
    have : 2 * hh η n ≤ P.h0 n := two_mul_hh_le_h0 (by omega)
    exact tayl_zeroPoly (by omega)
  have hPl : P.ps.map (fun η => P.poleLocal n η k) = P.ps.map fun η =>
      poleBrick ((hh η n : ℤ) - k) (P.h0 n - 2 * hh η n) :=
    List.map_congr_left fun η hη =>
      poleLocal_eq hk (hP.etaMin_le η hη) (two_mul_hh_le_h0 (hP.two_mul_lt η hη))
  unfold expan zeroPart
  rw [← tayl_apply, map_mul, tayl_linear, map_list_prod, List.map_map, hZ, hPl]

section Generic

variable {p : ℕ}

theorem padicValInt_le_log {c : ℤ} {N : ℕ} (h : c.natAbs ≤ N) :
    padicValInt p c ≤ Nat.log p N :=
  (padicValNat_le_nat_log _).trans (Nat.log_mono_right h)

theorem log_le_one_of_lt_sq {N : ℕ} (hN : N < p ^ 2) : Nat.log p N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp
  · have := Nat.log_lt_of_lt_pow hN0.ne' hN
    omega

/-- `ι` of two fractions with denominator `p` is the integer `ι`. -/
theorem iota_intCast_div (a b : ℤ) :
    iota ((a : ℝ) / p) ((b : ℝ) / p) = iotaZ p a b := by
  have e : (a : ℝ) / p + (b : ℝ) / p = ((a + b : ℤ) : ℝ) / p := by push_cast; ring
  have hf : ∀ z : ℤ, ⌊(z : ℝ) / (p : ℝ)⌋ = z / (p : ℤ) := fun z => by
    rw [Int.floor_div_natCast, Int.floor_intCast]
  unfold iota iotaZ
  rw [e, hf, hf, hf]

/-- Reflection: `ι(u, v) = ι(-(u+v)-1, v)`. -/
theorem iotaZ_reflect (hp : 0 < p) (u v : ℤ) : iotaZ p u v = iotaZ p (-(u + v) - 1) v := by
  unfold iotaZ
  have h1 := neg_sub_one_ediv hp u
  have h2 := neg_sub_one_ediv hp (u + v)
  have e : -(u + v) - 1 + v = -u - 1 := by ring
  rw [e, h1, h2]
  ring

variable [Fact p.Prime]

/-- Product lemma for a product over a list. -/
theorem vge_coeff_list_prod {α : Type*} (l : List α) (f : α → PowerSeries ℚ) (ν : α → ℤ)
    (κ : ℤ) (h : ∀ a ∈ l, ∀ j : ℕ, VGe p (ν a - κ * j) (coeff j (f a))) (j : ℕ) :
    VGe p ((l.map ν).sum - κ * j) (coeff j (l.map f).prod) := by
  induction l generalizing j with
  | nil =>
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil, coeff_one]
    split_ifs with hj
    · subst hj; simpa using vge_one p
    · exact vge_zero p _
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact vge_coeff_mul (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb))) j

theorem vge_coeff_linear (z : ℤ) (j : ℕ) : VGe p 0 (coeff j (C (z : ℚ) + C 2 * X)) := by
  rw [map_add, coeff_C, coeff_C_mul, coeff_X]
  refine VGe.add (vge_ite (vge_intCast p z) (vge_zero p 0)) ?_
  split_ifs
  · simpa using vge_natCast p 2
  · simpa using vge_zero p 0

/-- Medium primes, polynomial brick. -/
theorem polyBrick_vge_iota (s : ℤ) (m : ℕ) (hm : m < p ^ 2) (l : ℕ) :
    VGe p (iotaZ p (s - 1) m - l) (coeff l (polyBrick s m)) := by
  have h := polyBrick_vge_count (p := p) s m l
  rw [padicValNat_factorial_of_lt_sq hm] at h
  have := card_Ico_filter_dvd_sub_eq_iota (Fact.out : p.Prime).pos s m
  exact h.mono (by rw [← this])

/-- Medium primes, pole brick. -/
theorem poleBrick_vge_iota (s : ℤ) (m : ℕ) (hm : m < p ^ 2)
    (h1 : ∀ c ∈ Icc s (s + m), c ≠ 0 → padicValInt p c ≤ 1) (l : ℕ) :
    VGe p (iotaZ p (-s) (s + m) - l) (coeff l (poleBrick s m)) := by
  have hp := (Fact.out : p.Prime).pos
  have hcount := card_Icc_filter_dvd hp s m
  have hneg := neg_sub_one_ediv hp (s - 1)
  have hmp : ((m / p : ℕ) : ℤ) = (m : ℤ) / p := Int.natCast_div m p
  have key : iotaZ p (-s) (s + m) = (m : ℤ) / p + 1 - ((s + m) / p - (s - 1) / p) := by
    unfold iotaZ
    have e1 : -s + (s + m) = (m : ℤ) := by ring
    have e2 : (-s) / (p : ℤ) = -((s - 1) / p) - 1 := by
      rw [← hneg]; congr 1; ring
    rw [e1, e2]; ring
  rw [key]
  by_cases h0 : (0 : ℤ) ∈ Icc s (s + m)
  · have h := poleBrick_vge_count s m h1 l
    rw [padicValNat_factorial_of_lt_sq hm] at h
    have hc := card_Icc_filter_ne_zero_dvd hp s m
    rw [ite_eq_left h0] at hc
    refine h.mono ?_
    rw [hc, hmp]
    omega
  · have h := poleBrick_vge_count_of_not_mem s m h0
      (fun c hc => h1 c hc (fun h' => h0 (h' ▸ hc))) l
    rw [padicValNat_factorial_of_lt_sq hm] at h
    refine h.mono ?_
    rw [hcount, hmp]

/-- Large primes, polynomial brick. -/
theorem polyBrick_vge_zero (s : ℤ) (m : ℕ) (hm : m < p) (l : ℕ) :
    VGe p 0 (coeff l (polyBrick s m)) := by
  have h := polyBrick_vge_neg_factorial (p := p) s m l
  have hp2 : m < p ^ 2 := lt_of_lt_of_le hm (Nat.le_self_pow two_ne_zero p)
  rwa [padicValNat_factorial_of_lt_sq hp2, Nat.div_eq_of_lt hm, Nat.cast_zero, neg_zero] at h

/-- Large primes, pole brick. -/
theorem poleBrick_vge_zero_of_lt (s : ℤ) (m : ℕ) (h : ∀ c ∈ Icc s (s + m), c.natAbs < p)
    (l : ℕ) : VGe p 0 (coeff l (poleBrick s m)) := by
  refine poleBrick_vge_zero s m (fun c hc hc0 hdvd => ?_) l
  have h1 : p ∣ c.natAbs := Int.natCast_dvd.1 hdvd
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hc0) h1
  exact absurd (h c hc) (not_lt.2 h2)

end Generic

section Ranges

theorem mem_poleRange_iff {n k : ℕ} :
    k ∈ P.poleRange n ↔ hh P.etaMin n ≤ k ∧ k ≤ P.h0 n - hh P.etaMin n := by
  simp [poleRange]

theorem zs_facts (hP : P.Valid) {n η : ℕ} (hη : η ∈ P.zs) :
    2 * hh η n ≤ P.h0 n ∧ hh η n ≤ hh P.etaMin n := by
  have h1 := hP.zs_le_etaMin η hη
  have h2 := hP.two_mul_lt _ hP.etaMin_mem
  exact ⟨two_mul_hh_le_h0 (by omega), hh_le_hh_of_le h1⟩

theorem ps_facts (hP : P.Valid) {n η : ℕ} (hη : η ∈ P.ps) :
    2 * hh η n ≤ P.h0 n ∧ hh P.etaMin n ≤ hh η n :=
  ⟨two_mul_hh_le_h0 (hP.two_mul_lt η hη), hh_le_hh_of_le (hP.etaMin_le η hη)⟩

theorem natAbs_le_of {c : ℤ} {N : ℕ} (h1 : -(N : ℤ) ≤ c) (h2 : c ≤ N) : c.natAbs ≤ N := by
  omega

theorem zeroBrick1_range (hP : P.Valid) {n η k : ℕ} (hη : η ∈ P.zs) (hk : k ∈ P.poleRange n) :
    ∀ c ∈ Ico (1 - (k : ℤ)) (1 - k + ((η * n : ℕ) : ℤ)), c ≠ 0 ∧ c.natAbs ≤ P.h0 n := by
  intro c hc
  have := zs_facts hP (n := n) hη
  rw [mem_poleRange_iff] at hk
  rw [mem_Ico] at hc
  have e : hh η n = η * n + 1 := rfl
  constructor <;> omega

theorem zeroBrick2_range (hP : P.Valid) {n η k : ℕ} (hη : η ∈ P.zs) (hk : k ∈ P.poleRange n) :
    ∀ c ∈ Ico ((P.h0 n : ℤ) - hh η n + 1 - k) ((P.h0 n : ℤ) - hh η n + 1 - k + ((η * n : ℕ) : ℤ)),
      c ≠ 0 ∧ c.natAbs ≤ P.h0 n := by
  intro c hc
  have := zs_facts hP (n := n) hη
  rw [mem_poleRange_iff] at hk
  rw [mem_Ico] at hc
  have e : hh η n = η * n + 1 := rfl
  constructor <;> omega

theorem poleBrick_range (hP : P.Valid) {n η k : ℕ} (hη : η ∈ P.ps) (hk : k ∈ P.poleRange n) :
    ∀ c ∈ Icc ((hh η n : ℤ) - k) ((hh η n : ℤ) - k + ((P.h0 n - 2 * hh η n : ℕ) : ℤ)),
      c.natAbs ≤ P.h0 n - 2 * hh P.etaMin n := by
  intro c hc
  have := ps_facts hP (n := n) hη
  rw [mem_poleRange_iff] at hk
  rw [mem_Icc] at hc
  omega

end Ranges

section Expan

variable {p : ℕ} [Fact p.Prime]

/-- Generic bound for the coefficients of the expansion from bounds for its bricks. -/
theorem vge_coeff_expan_of (hP : P.Valid) {n k : ℕ} (hk : k ∈ P.poleRange n) (κ : ℤ)
    (hκ : 0 ≤ κ) (ν₁ ν₂ ν₃ : ℕ → ℤ)
    (h1 : ∀ η ∈ P.zs, ∀ j : ℕ, VGe p (ν₁ η - κ * j) (coeff j (polyBrick (1 - k) (η * n))))
    (h2 : ∀ η ∈ P.zs, ∀ j : ℕ, VGe p (ν₂ η - κ * j)
      (coeff j (polyBrick ((P.h0 n : ℤ) - hh η n + 1 - k) (η * n))))
    (h3 : ∀ η ∈ P.ps, ∀ j : ℕ, VGe p (ν₃ η - κ * j)
      (coeff j (poleBrick ((hh η n : ℤ) - k) (P.h0 n - 2 * hh η n))))
    (l : ℕ) :
    VGe p ((P.zs.map fun η => ν₁ η + ν₂ η).sum + (P.ps.map ν₃).sum - κ * l)
      (coeff l (P.expan n k)) := by
  rw [expan_eq hP hk]
  have hlin : ∀ j : ℕ, VGe p (0 - κ * j) (coeff j (C ((P.h0 n : ℚ) - 2 * k) + C 2 * X)) := by
    intro j
    have := vge_coeff_linear (p := p) ((P.h0 n : ℤ) - 2 * k) j
    push_cast at this
    exact this.mono (by nlinarith [(j.cast_nonneg : (0 : ℤ) ≤ j)])
  have hZ := vge_coeff_list_prod (p := p) P.zs
    (fun η => polyBrick (1 - k) (η * n) * polyBrick ((P.h0 n : ℤ) - hh η n + 1 - k) (η * n))
    (fun η => ν₁ η + ν₂ η) κ (fun η hη j => vge_coeff_mul (h1 η hη) (h2 η hη) j)
  have hPl := vge_coeff_list_prod (p := p) P.ps
    (fun η => poleBrick ((hh η n : ℤ) - k) (P.h0 n - 2 * hh η n)) ν₃ κ h3
  exact (vge_coeff_mul (vge_coeff_mul hlin hZ) hPl l).mono (le_of_eq (by ring))

/-- Small primes: the crude bound. -/
theorem vge_coeff_expan_small (hP : P.Valid) {n k : ℕ} (hk : k ∈ P.poleRange n) (l : ℕ) :
    VGe p (-((Nat.log p (P.h0 n) : ℤ) * l)) (coeff l (P.expan n k)) := by
  have h := vge_coeff_expan_of (p := p) hP hk (Nat.log p (P.h0 n)) (by positivity)
    (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun η hη j => by
      have := polyBrick_vge_neg_mul (p := p) (1 - k) (η * n) (Nat.log p (P.h0 n))
        (fun h0 => (zeroBrick1_range hP hη hk 0 h0).1 rfl)
        (fun c hc => padicValInt_le_log (zeroBrick1_range hP hη hk c hc).2) j
      simpa using this)
    (fun η hη j => by
      have := polyBrick_vge_neg_mul (p := p) _ (η * n) (Nat.log p (P.h0 n))
        (fun h0 => (zeroBrick2_range hP hη hk 0 h0).1 rfl)
        (fun c hc => padicValInt_le_log (zeroBrick2_range hP hη hk c hc).2) j
      simpa using this)
    (fun η hη j => by
      have := poleBrick_vge_neg_mul (p := p) (Nat.log p (P.h0 n)) _ _
        (fun c hc _ => padicValInt_le_log
          ((poleBrick_range hP hη hk c hc).trans (Nat.sub_le _ _))) j
      simpa using this) l
  simpa using h

/-- Large primes: all coefficients are `p`-integral. -/
theorem vge_coeff_expan_large (hP : P.Valid) {n k : ℕ} (hk : k ∈ P.poleRange n)
    (hz : ∀ η ∈ P.zs, η * n < p) (hpole : P.h0 n - 2 * hh P.etaMin n < p) (l : ℕ) :
    VGe p 0 (coeff l (P.expan n k)) := by
  have h := vge_coeff_expan_of (p := p) hP hk 0 le_rfl
    (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun η hη j => by simpa using polyBrick_vge_zero (p := p) _ _ (hz η hη) j)
    (fun η hη j => by simpa using polyBrick_vge_zero (p := p) _ _ (hz η hη) j)
    (fun η hη j => by
      simpa using poleBrick_vge_zero_of_lt (p := p) _ _
        (fun c hc => lt_of_le_of_lt (poleBrick_range hP hη hk c hc) hpole) j) l
  simpa using h

end Expan

section Medium

variable {p : ℕ}

theorem iota_zs1 (hp : 0 < p) (η n k : ℕ) :
    iota (((k : ℝ) - 1) / p - η * ((n : ℝ) / p)) (η * ((n : ℝ) / p)) =
      iotaZ p (1 - k - 1) ((η * n : ℕ) : ℤ) := by
  rw [show ((k : ℝ) - 1) / p - η * ((n : ℝ) / p) = (((k : ℤ) - 1 - ((η * n : ℕ) : ℤ) : ℤ) : ℝ) / p
      by push_cast; ring,
    show (η : ℝ) * ((n : ℝ) / p) = (((η * n : ℕ) : ℤ) : ℝ) / p by push_cast; ring,
    iota_intCast_div, iotaZ_reflect hp (1 - k - 1)]
  congr 1
  ring

theorem iota_zs2 (η n k : ℕ) :
    iota ((P.eta0 - η : ℝ) * ((n : ℝ) / p) - ((k : ℝ) - 1) / p) (η * ((n : ℝ) / p)) =
      iotaZ p ((P.h0 n : ℤ) - hh η n + 1 - k - 1) ((η * n : ℕ) : ℤ) := by
  rw [show (P.eta0 - η : ℝ) * ((n : ℝ) / p) - ((k : ℝ) - 1) / p =
      (((P.h0 n : ℤ) - hh η n + 1 - k - 1 : ℤ) : ℝ) / p by
        simp only [h0, hh]; push_cast; ring,
    show (η : ℝ) * ((n : ℝ) / p) = (((η * n : ℕ) : ℤ) : ℝ) / p by push_cast; ring,
    iota_intCast_div]

theorem iota_ps {η n k : ℕ} (h2 : 2 * hh η n ≤ P.h0 n) :
    iota (((k : ℝ) - 1) / p - η * ((n : ℝ) / p))
        ((P.eta0 - η : ℝ) * ((n : ℝ) / p) - ((k : ℝ) - 1) / p) =
      iotaZ p (-((hh η n : ℤ) - k)) ((hh η n : ℤ) - k + ((P.h0 n - 2 * hh η n : ℕ) : ℤ)) := by
  have e : ((P.h0 n - 2 * hh η n : ℕ) : ℤ) = (P.h0 n : ℤ) - 2 * hh η n := by push_cast [h2]; ring
  rw [show ((k : ℝ) - 1) / p - η * ((n : ℝ) / p) = ((-((hh η n : ℤ) - k) : ℤ) : ℝ) / p by
        simp only [hh]; push_cast; ring,
    show (P.eta0 - η : ℝ) * ((n : ℝ) / p) - ((k : ℝ) - 1) / p =
      (((hh η n : ℤ) - k + ((P.h0 n - 2 * hh η n : ℕ) : ℤ) : ℤ) : ℝ) / p by
        rw [e]; simp only [h0, hh]; push_cast; ring,
    iota_intCast_div]

variable [Fact p.Prime]

/-- Medium primes (`h₀ < p²`): `v_p(coeff_l) ≥ φ₀(n/p, (k-1)/p) - l`. -/
theorem vge_coeff_expan_medium (hP : P.Valid) {n k : ℕ} (hk : k ∈ P.poleRange n)
    (hp : P.h0 n < p ^ 2) (l : ℕ) :
    VGe p (phi0 P.eta0 P.zs P.ps ((n : ℝ) / p) (((k : ℝ) - 1) / p) - l)
      (coeff l (P.expan n k)) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hzm : ∀ η ∈ P.zs, η * n < p ^ 2 := fun η hη => by
    have := zs_facts hP (n := n) hη
    have e : hh η n = η * n + 1 := rfl
    omega
  have h := vge_coeff_expan_of (p := p) hP hk 1 zero_le_one
    (fun η => iotaZ p (1 - k - 1) ((η * n : ℕ) : ℤ))
    (fun η => iotaZ p ((P.h0 n : ℤ) - hh η n + 1 - k - 1) ((η * n : ℕ) : ℤ))
    (fun η => iotaZ p (-((hh η n : ℤ) - k)) ((hh η n : ℤ) - k + ((P.h0 n - 2 * hh η n : ℕ) : ℤ)))
    (fun η hη j => (polyBrick_vge_iota (p := p) (1 - k) (η * n) (hzm η hη) j).mono (by simp))
    (fun η hη j => (polyBrick_vge_iota (p := p) _ (η * n) (hzm η hη) j).mono (by simp))
    (fun η hη j => (poleBrick_vge_iota (p := p) _ _ (by omega)
      (fun c hc _ => (padicValInt_le_log ((poleBrick_range hP hη hk c hc).trans
        (Nat.sub_le _ _))).trans (log_le_one_of_lt_sq hp)) j).mono (by simp)) l
  refine h.mono (le_of_eq ?_)
  have hsum : (P.zs.map fun η => iotaZ p (1 - k - 1) ((η * n : ℕ) : ℤ) +
      iotaZ p ((P.h0 n : ℤ) - hh η n + 1 - k - 1) ((η * n : ℕ) : ℤ)).sum +
      (P.ps.map fun η => iotaZ p (-((hh η n : ℤ) - k))
        ((hh η n : ℤ) - k + ((P.h0 n - 2 * hh η n : ℕ) : ℤ))).sum =
      phi0 P.eta0 P.zs P.ps ((n : ℝ) / p) (((k : ℝ) - 1) / p) := by
    unfold phi0
    congr 1
    · refine congrArg List.sum (List.map_congr_left fun η _ => ?_)
      rw [iota_zs1 hp0, iota_zs2]
    · refine congrArg List.sum (List.map_congr_left fun η hη => ?_)
      rw [iota_ps (ps_facts hP hη).1]
  rw [← hsum]
  ring

end Medium

section Order

theorem X_dvd_poleBrick {s : ℤ} {m : ℕ} (h : (0 : ℤ) ∉ Icc s (s + m)) :
    (X : PowerSeries ℚ) ∣ poleBrick s m := by
  unfold poleBrick
  rw [ite_eq_right h]
  exact ⟨C (m.factorial : ℚ) * (∏ c ∈ Icc s (s + m), (C (c : ℚ) + X))⁻¹, by ring⟩

theorem X_pow_dvd_list_prod {α : Type*} (l : List α) (f : α → PowerSeries ℚ) (q : α → Bool)
    (h : ∀ a ∈ l, q a → X ∣ f a) : X ^ (l.countP q) ∣ (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [List.countP_cons, List.map_cons, List.prod_cons]
    split_ifs with ha
    · rw [pow_succ']
      exact mul_dvd_mul (h a List.mem_cons_self ha) ih'
    · simpa using dvd_mul_of_dvd_right ih' _

/-- The pole blocks containing `k`. -/
def poleCount (P : Params) (n k : ℕ) : ℕ :=
  P.ps.countP fun η => decide (hh η n ≤ k ∧ k ≤ P.h0 n - hh η n)

/-- If `a_{i,k} ≠ 0` then `-k` is a pole of order at least `i`. -/
theorem le_poleCount_of_coef_ne_zero (hP : P.Valid) {n k i : ℕ} (hk : k ∈ P.poleRange n)
    (hi : i ≤ P.q - P.r) (hc : P.coef n i k ≠ 0) : i ≤ poleCount P n k := by
  by_contra hlt
  rw [not_le] at hlt
  apply hc
  have hlen := List.length_eq_countP_add_countP
    (fun η => decide (hh η n ≤ k ∧ k ≤ P.h0 n - hh η n)) (l := P.ps)
  have hdvd := X_pow_dvd_list_prod P.ps
    (fun η => poleBrick ((hh η n : ℤ) - k) (P.h0 n - 2 * hh η n))
    (fun η => ¬ decide (hh η n ≤ k ∧ k ≤ P.h0 n - hh η n)) (fun η hη hq => by
      refine X_dvd_poleBrick fun h0 => ?_
      have := (ps_facts hP (n := n) hη).1
      simp only [decide_eq_true_eq] at hq
      rw [mem_Icc] at h0
      push_cast [this] at h0
      omega)
  have hX : (X : PowerSeries ℚ) ^ (P.ps.countP
      fun η => ¬ decide (hh η n ≤ k ∧ k ≤ P.h0 n - hh η n)) ∣ P.expan n k := by
    rw [expan_eq hP hk]
    exact dvd_mul_of_dvd_right hdvd _
  unfold coef
  refine PowerSeries.X_pow_dvd_iff.1 hX _ ?_
  have hq : P.q - P.r = P.ps.length := by simp [q, r]
  unfold poleCount at hlt
  omega

end Order

section Harmonic

variable {p : ℕ} [Fact p.Prime]

theorem vge_harm (N e L : ℕ) (hL : ∀ l ∈ Icc 1 N, padicValNat p l ≤ L) :
    VGe p (-((e : ℤ) * L)) (∑ l ∈ Icc 1 N, ((l : ℚ) ^ e)⁻¹) := by
  refine VGe.sum fun l hl => ?_
  have h := vge_inv_intCast_pow (p := p) (l : ℤ) e
  rw [padicValInt.of_nat, Int.cast_natCast, inv_pow] at h
  refine h.mono ?_
  have := hL l hl
  have : (padicValNat p l : ℤ) ≤ L := by exact_mod_cast this
  nlinarith [(e.cast_nonneg : (0 : ℤ) ≤ e)]

omit [Fact p.Prime] in
theorem padicValNat_eq_zero_of_lt {l : ℕ} (h1 : 1 ≤ l) (h2 : l < p) : padicValNat p l = 0 :=
  padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt h1 h2)

end Harmonic

end OddZeta.Params.DeltaAux
