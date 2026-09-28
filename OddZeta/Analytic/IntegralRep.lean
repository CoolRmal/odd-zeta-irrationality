import OddZeta.Analytic.Defs
import OddZeta.Analysis.CotSeries
import OddZeta.Analysis.VerticalLine
import OddZeta.Analytic.IntegralRepAux

/-!
# The integral representation of `Fₙ` (Lemma 4.1 and (4.7) of the note)

With `M = 1/2 - h₁` and `S = trigS r` (so that `∑ₘ (t-m)^{-r} = π^r S(t)/sin^r(πt)`):
`Fₙ = (1/2πi) ∫_{Re t = M} S(t) Gₙ(t) dt = (1/π) Re ∫_{-∞}^{0} S(M+iy) Gₙ(M+iy) dy`.

Proof: `∫_{Re t=M} Rₙ(t)(t-m)^{-r} dt = -2πi ρₙ(m)` if `m > M` and `0` if `m < M` (partial fractions
and `integral_vert_partialFractions`); summing over `m ∈ ℤ` (Fubini) and using the Lipschitz
formula and `Rₙ = (-sin πt/π)^r Gₙ` gives the first identity; the second follows from the
symmetry `S(t̄)Gₙ(t̄) = conj(S(t)Gₙ(t))`.
-/

namespace OddZeta

open Complex MeasureTheory ComplexConjugate

namespace Params

variable (P : Params)

/-- The abscissa `M = 1/2 - h₁` of the line of integration. -/
noncomputable def lineM (n : ℕ) : ℝ := 1 / 2 - (hh P.etaOne n : ℝ)

/-- The integrand `S(M+iy) Gₙ(M+iy)` on the line `Re t = M`. -/
noncomputable def lineIntegrand (n : ℕ) (y : ℝ) : ℂ :=
  trigS P.r (P.lineM n + y * I) * P.G n (P.lineM n + y * I)

variable {P}

/-! ### The line `Re t = M` -/

lemma half_le_abs_lineM_sub (n : ℕ) (j : ℤ) : 1 / 2 ≤ |P.lineM n - j| := by
  set w : ℤ := (hh P.etaOne n : ℤ) + j with hw
  have e : P.lineM n - j = 1 / 2 - w := by
    simp only [lineM, hw]
    push_cast
    ring
  rw [e]
  rcases le_or_gt w 0 with h | h
  · have : (w : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith
  · have : (1 : ℝ) ≤ w := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    linarith

lemma lineM_ne_intCast (n : ℕ) (j : ℤ) : P.lineM n ≠ j := by
  intro h
  have := half_le_abs_lineM_sub (P := P) n j
  rw [h, sub_self, abs_zero] at this
  linarith

lemma line_ne_intCast (n : ℕ) (y : ℝ) (j : ℤ) : (P.lineM n : ℂ) + y * I ≠ j := by
  intro h
  have := congrArg Complex.re h
  simp at this
  exact lineM_ne_intCast n j this

lemma line_add_natCast_ne_zero (n : ℕ) (y : ℝ) (k : ℕ) : (P.lineM n : ℂ) + y * I + k ≠ 0 := by
  intro h
  apply line_ne_intCast (P := P) n y (-(k : ℤ))
  push_cast
  linear_combination h

lemma half_le_norm_line_add_natCast (n : ℕ) (y : ℝ) (k : ℕ) :
    1 / 2 ≤ ‖(P.lineM n : ℂ) + y * I + k‖ := by
  calc (1 : ℝ) / 2 ≤ |P.lineM n - ((-(k : ℤ) : ℤ) : ℝ)| := half_le_abs_lineM_sub n _
    _ = |((P.lineM n : ℂ) + y * I + k).re| := by simp
    _ ≤ _ := abs_re_le_norm _

lemma hh_etaOne_le (hP : P.Valid) {n k : ℕ} (hk : k ∈ P.poleRange n) : hh P.etaOne n ≤ k := by
  have h1 := hP.zs_le_etaMin _ hP.etaOne_mem
  have h2 := (Finset.mem_Icc.1 hk).1
  have := Nat.mul_le_mul_right n h1
  simp only [hh] at *
  omega

lemma neg_re_lt_lineM (hP : P.Valid) {n k : ℕ} (hk : k ∈ P.poleRange n) :
    (-(k : ℂ)).re < P.lineM n := by
  have : (hh P.etaOne n : ℝ) ≤ k := by exact_mod_cast hh_etaOne_le hP hk
  simp only [neg_re, natCast_re, lineM]
  linarith

/-! ### `Rₙ` on the line -/

lemma norm_R_line_le (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    ‖P.R n (P.lineM n + y * I)‖ ≤
      ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r), ‖(P.coef n i k : ℂ)‖ * 2 ^ i := by
  rw [R_eq_sum hP hn fun k _ => line_add_natCast_ne_zero n y k]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  rw [norm_div, norm_pow, div_eq_mul_inv]
  gcongr
  have h := half_le_norm_line_add_natCast (P := P) n y k
  calc (‖(P.lineM n : ℂ) + y * I + k‖ ^ i)⁻¹ ≤ ((1 / 2 : ℝ) ^ i)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h i)
    _ = 2 ^ i := by rw [one_div, inv_pow, inv_inv]

/-- `∫_{Re t = M} Rₙ(t) (t-m)^{-r} dt = -2πi ρₙ(m)` if `m > M`, and `0` if `m < M`. -/
theorem integral_R_mul_inv_pow (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) (m : ℤ) :
    Integrable (fun y : ℝ => P.R n (P.lineM n + y * I) * (((P.lineM n : ℂ) + y * I - m) ^ P.r)⁻¹) ∧
      ∫ y : ℝ, P.R n (P.lineM n + y * I) * (((P.lineM n : ℂ) + y * I - m) ^ P.r)⁻¹ =
        if P.lineM n < m then -2 * Real.pi * (P.rho n m : ℂ) else 0 := by
  set M := P.lineM n with hM
  have hr3 := hP.three_le_r
  have hpt : ∀ y : ℝ, P.R n (M + y * I) * (((M : ℂ) + y * I - m) ^ P.r)⁻¹ =
      ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r), (P.coef n i k : ℂ) *
        ((((M : ℂ) + y * I - (-(k : ℂ))) ^ i)⁻¹ * (((M : ℂ) + y * I - m) ^ P.r)⁻¹) := by
    intro y
    rw [R_eq_sum hP hn fun k _ => line_add_natCast_ne_zero n y k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_neg_eq_add, div_eq_mul_inv, mul_assoc]
  have hterm : ∀ k ∈ P.poleRange n, ∀ i ∈ Finset.Icc 1 (P.q - P.r),
      Integrable (fun y : ℝ =>
        (((M : ℂ) + y * I - (-(k : ℂ))) ^ i)⁻¹ * (((M : ℂ) + y * I - m) ^ P.r)⁻¹) ∧
      ∫ y : ℝ, (((M : ℂ) + y * I - (-(k : ℂ))) ^ i)⁻¹ * (((M : ℂ) + y * I - m) ^ P.r)⁻¹ =
        if M < m then -2 * Real.pi * vertRes ((m : ℂ) - -(k : ℂ)) i P.r else 0 := by
    intro k hk i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have hm : ((m : ℂ)).re ≠ M := by
      simpa using (lineM_ne_intCast (P := P) n m).symm
    simpa using integral_vert_two_poles (neg_re_lt_lineM hP hk) hm (i := i) (r := P.r) (by omega)
  refine ⟨(integrable_finsetSum _ fun k hk => integrable_finsetSum _ fun i hi =>
    (hterm k hk i hi).1.const_mul _).congr (ae_of_all _ fun y => (hpt y).symm), ?_⟩
  rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun k hk =>
    integrable_finsetSum _ fun i hi => (hterm k hk i hi).1.const_mul _]
  have hsum_eq : ∀ k ∈ P.poleRange n,
      ∫ y : ℝ, ∑ i ∈ Finset.Icc 1 (P.q - P.r), (P.coef n i k : ℂ) *
        ((((M : ℂ) + y * I - (-(k : ℂ))) ^ i)⁻¹ * (((M : ℂ) + y * I - m) ^ P.r)⁻¹) =
      ∑ i ∈ Finset.Icc 1 (P.q - P.r), (P.coef n i k : ℂ) *
        (if M < m then -2 * Real.pi * vertRes ((m : ℂ) - -(k : ℂ)) i P.r else 0) := by
    intro k hk
    rw [integral_finsetSum _ fun i hi => (hterm k hk i hi).1.const_mul _]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_const_mul, (hterm k hk i hi).2]
  rw [Finset.sum_congr rfl hsum_eq]
  split_ifs with h
  · have hr1 : (-1 : ℂ) ^ (P.r - 1) = 1 := by
      obtain ⟨s, hs⟩ := hP.r_odd
      rw [show P.r - 1 = 2 * s by omega, pow_mul]
      simp
    have hr0 : P.r ≠ 0 := by omega
    simp only [vertRes, hr0, ite_false, hr1, one_mul, rho]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_neg_eq_add]
    ring
  · simp

lemma summable_integral_norm_R_mul (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    Summable fun m : ℤ =>
      ∫ y : ℝ, ‖P.R n (P.lineM n + y * I) * (((P.lineM n : ℂ) + y * I - m) ^ P.r)⁻¹‖ := by
  set M := P.lineM n with hM
  set B := ∑ k ∈ P.poleRange n, ∑ i ∈ Finset.Icc 1 (P.q - P.r), ‖(P.coef n i k : ℂ)‖ * 2 ^ i
    with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => by positivity
  have hr3 := hP.three_le_r
  refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun y => norm_nonneg _) (fun m => ?_)
    ((summable_inv_sub_intCast_sq M).mul_left (B * 2 ^ (P.r - 3) * Real.pi))
  have hMm := half_le_abs_lineM_sub (P := P) n m
  have ha : M - m ≠ 0 := by
    intro h
    rw [← hM, h, abs_zero] at hMm
    linarith
  have hbound : ∀ y : ℝ, ‖P.R n (M + y * I) * (((M : ℂ) + y * I - m) ^ P.r)⁻¹‖ ≤
      B * 2 ^ (P.r - 3) * |M - m|⁻¹ * ((M - m) ^ 2 + y ^ 2)⁻¹ := by
    intro y
    rw [norm_mul]
    calc ‖P.R n (M + y * I)‖ * ‖(((M : ℂ) + y * I - m) ^ P.r)⁻¹‖
        ≤ B * (2 ^ (P.r - 3) * |M - m|⁻¹ * ((M - m) ^ 2 + y ^ 2)⁻¹) :=
          mul_le_mul (norm_R_line_le hP hn y) (norm_vert_inv_pow_le hMm hr3 y) (norm_nonneg _)
            hB0
      _ = _ := by ring
  calc ∫ y : ℝ, ‖P.R n (M + y * I) * (((M : ℂ) + y * I - m) ^ P.r)⁻¹‖
      ≤ ∫ y : ℝ, B * 2 ^ (P.r - 3) * |M - m|⁻¹ * ((M - m) ^ 2 + y ^ 2)⁻¹ :=
        integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
          ((integrable_inv_sq_add_sq ha).const_mul _) (ae_of_all _ hbound)
    _ = B * 2 ^ (P.r - 3) * |M - m|⁻¹ * (Real.pi / |M - m|) := by
        rw [integral_const_mul, integral_inv_sq_add_sq ha]
    _ = B * 2 ^ (P.r - 3) * Real.pi * ((M - m) ^ 2)⁻¹ := by
        rw [← sq_abs (M - m)]
        have : |M - m| ≠ 0 := abs_ne_zero.2 ha
        field_simp

/-! ### Conjugation symmetry -/

lemma G_conj (n : ℕ) (t : ℂ) : P.G n (conj t) = conj (P.G n t) := by
  simp only [G, map_mul, map_pow, map_add, map_natCast, conj_ofReal, map_ofNat, map_list_prod,
    List.map_map, ← Gamma_conj, map_neg]
  congr 2
  refine List.map_congr_left fun η _ => ?_
  simp [map_div₀, ← Gamma_conj]

lemma lineIntegrand_neg (n : ℕ) (y : ℝ) :
    P.lineIntegrand n (-y) = conj (P.lineIntegrand n y) := by
  have e : (P.lineM n : ℂ) + ((-y : ℝ) : ℂ) * I = conj ((P.lineM n : ℂ) + (y : ℂ) * I) := by
    simp only [map_add, map_mul, conj_ofReal, conj_I, ofReal_neg]
    ring
  simp only [lineIntegrand, e, trigS_conj, G_conj, map_mul]

/-! ### The Lipschitz formula on the line -/

lemma tsum_R_mul_inv_pow (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : y ≠ 0) :
    ∑' m : ℤ, P.R n (P.lineM n + y * I) * (((P.lineM n : ℂ) + y * I - m) ^ P.r)⁻¹ =
      -P.lineIntegrand n y := by
  set t : ℂ := (P.lineM n : ℂ) + y * I with ht
  have ht_im : t.im ≠ 0 := by simpa [t] using hy
  have hlip := tsum_inv_sub_intCast_pow_mul_sin_pow (by linarith [hP.three_le_r] : 2 ≤ P.r)
    ht_im
  have hRG := R_eq_sin_pow_mul_G hP hn (t := t) fun j => line_ne_intCast n y j
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [tsum_mul_left, hRG, lineIntegrand, ← ht]
  calc (-sin (Real.pi * t) / Real.pi) ^ P.r * P.G n t * ∑' m : ℤ, ((t - m) ^ P.r)⁻¹
      = (-1) ^ P.r * ((∑' m : ℤ, ((t - m) ^ P.r)⁻¹) * sin (Real.pi * t) ^ P.r) * P.G n t /
          (Real.pi : ℂ) ^ P.r := by ring
    _ = (-1) ^ P.r * ((Real.pi : ℂ) ^ P.r * trigS P.r t) * P.G n t / (Real.pi : ℂ) ^ P.r := by
        rw [hlip]
    _ = -(trigS P.r t * P.G n t) := by
        rw [hP.r_odd.neg_one_pow]
        field_simp

/-! ### Summation over `m` -/

lemma tsum_ite_rho (n : ℕ) :
    ∑' m : ℤ, (if P.lineM n < m then -2 * (Real.pi : ℂ) * (P.rho n m : ℂ) else 0) =
      -2 * Real.pi * (P.F n : ℂ) := by
  set g : ℕ → ℤ := fun j => (j : ℤ) + 1 - hh P.etaOne n with hg_def
  have hg : Function.Injective g := fun a b h => by
    simp only [hg_def] at h
    omega
  have hlt : ∀ j : ℕ, P.lineM n < (g j : ℝ) := by
    intro j
    simp only [hg_def, lineM]
    push_cast
    have : (0 : ℝ) ≤ j := j.cast_nonneg
    linarith
  have hsupp : Function.support
      (fun m : ℤ => if P.lineM n < m then -2 * (Real.pi : ℂ) * (P.rho n m : ℂ) else 0) ⊆
        Set.range g := by
    intro m hm
    have hlt' : P.lineM n < m := by
      by_contra h
      simp [h] at hm
    have h1 : (1 : ℤ) ≤ m + hh P.etaOne n := by
      by_contra h'
      have h'' : ((m + hh P.etaOne n : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (by omega :
        m + hh P.etaOne n ≤ 0)
      push_cast at h''
      simp only [lineM] at hlt'
      linarith
    refine ⟨(m - 1 + hh P.etaOne n).toNat, ?_⟩
    simp only [hg_def]
    omega
  rw [← hg.tsum_eq hsupp]
  simp only [hlt, ite_true]
  rw [tsum_mul_left, F, ofReal_tsum]
  simp only [hg_def, ofReal_ratCast]

/-- **Integral representation** of `Fₙ`. -/
theorem F_eq_integral (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (P.lineIntegrand n) ∧
      P.F n = (∫ y in Set.Iic (0 : ℝ), P.lineIntegrand n y).re / Real.pi := by
  set Fm : ℤ → ℝ → ℂ := fun m y =>
    P.R n (P.lineM n + y * I) * (((P.lineM n : ℂ) + y * I - m) ^ P.r)⁻¹ with hFm_def
  have hFm := integral_R_mul_inv_pow hP hn
  have hsum := summable_integral_norm_R_mul hP hn
  have hae : ∀ᵐ y : ℝ, ∑' m, Fm m y = -P.lineIntegrand n y := by
    have h0 : ∀ᵐ y : ℝ, y ∉ ({0} : Set ℝ) := measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
    filter_upwards [h0] with y hy
    exact tsum_R_mul_inv_pow hP hn (by simpa using hy)
  have hint : Integrable (P.lineIntegrand n) := by
    have := (integrable_tsum_of_summable_integral_norm (fun m => (hFm m).1) hsum).neg
    refine this.congr (hae.mono fun y hy => ?_)
    change -(∑' m, Fm m y) = _
    rw [hy, neg_neg]
  have htot : ∫ y, P.lineIntegrand n y = 2 * Real.pi * (P.F n : ℂ) := by
    have h1 := integral_tsum_of_summable_integral_norm (fun m => (hFm m).1) hsum
    rw [integral_congr_ae hae, integral_neg] at h1
    rw [tsum_congr fun m => (hFm m).2, tsum_ite_rho] at h1
    linear_combination h1
  have hsymm : ∫ y in Set.Ioi (0 : ℝ), P.lineIntegrand n y =
      conj (∫ y in Set.Iic (0 : ℝ), P.lineIntegrand n y) := by
    have e : ∀ y, P.lineIntegrand n y = conj (P.lineIntegrand n (-y)) := by
      intro y
      rw [lineIntegrand_neg, conj_conj]
    calc ∫ y in Set.Ioi (0 : ℝ), P.lineIntegrand n y
        = ∫ y in Set.Ioi (0 : ℝ), conj (P.lineIntegrand n (-y)) :=
          integral_congr_ae (ae_of_all _ e)
      _ = conj (∫ y in Set.Ioi (0 : ℝ), P.lineIntegrand n (-y)) := integral_conj
      _ = conj (∫ y in Set.Iic (0 : ℝ), P.lineIntegrand n y) := by
          rw [integral_comp_neg_Ioi, neg_zero]
  have hsplit : ∫ y, P.lineIntegrand n y =
      ((2 * (∫ y in Set.Iic (0 : ℝ), P.lineIntegrand n y).re : ℝ) : ℂ) := by
    rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := 0),
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
        hint.integrableOn, hsymm, add_conj]
  refine ⟨hint, ?_⟩
  rw [htot] at hsplit
  have hreal : 2 * Real.pi * P.F n = 2 * (∫ y in Set.Iic (0 : ℝ), P.lineIntegrand n y).re := by
    exact_mod_cast hsplit
  field_simp
  linarith

end Params

end OddZeta
