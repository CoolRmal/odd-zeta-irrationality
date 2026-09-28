import OddZeta.Analysis.Stirling

/-!
# Auxiliary lemmas for the Gamma-function form of `Rₙ`

* Products of Gamma quotients: `Γ(t+b)/Γ(t+a) = ∏_{a ≤ i < b} (t+i)` off the integers, and the
  reflection formula in the form `(-sin πt/π) Γ(-t) = 1/Γ(t+1)`.
* A scaled form of Stirling's formula: `Γ(nζ+b) = √(2π) exp(T + μ)` with
  `T = (nζ+b-1/2)(log n + log ζ) - nζ` and `‖μ‖ ≤ K/n`, uniformly for `b ≤ 2` and `ζ` in a sector
  with `‖ζ‖ ≥ c`.
* Small list lemmas.
-/

namespace OddZeta

namespace GammaAux

open Complex

section Lists

variable {α : Type*}

lemma list_prod_map_div (l : List α) (f g : α → ℂ) :
    (l.map fun i => f i / g i).prod = (l.map f).prod / (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, div_mul_div_comm]

lemma list_prod_map_const (l : List α) (c : ℂ) : (l.map fun _ => c).prod = c ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [pow_succ, mul_comm]

lemma list_sum_map_const (l : List α) (c : ℂ) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

lemma list_sum_map_sub (l : List α) (f g : α → ℂ) :
    (l.map fun i => f i - g i).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma ofReal_list_prod (l : List α) (f : α → ℝ) :
    (((l.map f).prod : ℝ) : ℂ) = (l.map fun i => (f i : ℂ)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma ofReal_list_sum (l : List α) (f : α → ℝ) :
    (((l.map f).sum : ℝ) : ℂ) = (l.map fun i => (f i : ℂ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Accumulating Stirling remainders along a list. -/
lemma list_prod_eq_exp (l : List α) (x e : α → ℂ) (c : ℂ) (B : ℝ)
    (h : ∀ a ∈ l, ∃ ν : ℂ, ‖ν‖ ≤ B ∧ x a = c * exp (e a + ν)) :
    ∃ ν : ℂ, ‖ν‖ ≤ l.length * B ∧ (l.map x).prod = c ^ l.length * exp ((l.map e).sum + ν) := by
  induction l with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons a l ih =>
    obtain ⟨ν₁, hν₁, hx⟩ := h a (by simp)
    obtain ⟨ν₂, hν₂, hl⟩ := ih fun b hb => h b (by simp [hb])
    refine ⟨ν₁ + ν₂, ?_, ?_⟩
    · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      calc ‖ν₁ + ν₂‖ ≤ ‖ν₁‖ + ‖ν₂‖ := norm_add_le _ _
        _ ≤ B + l.length * B := add_le_add hν₁ hν₂
        _ = (l.length + 1) * B := by ring
    · simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons, hx, hl]
      have : exp (e a + (List.map e l).sum + (ν₁ + ν₂)) =
          exp (e a + ν₁) * exp ((List.map e l).sum + ν₂) := by
        rw [← Complex.exp_add]; ring_nf
      rw [this, pow_succ]
      ring

end Lists

section GammaProducts

lemma Gamma_add_nat_eq_mul {t : ℂ} (ht : ∀ m : ℤ, t ≠ m) {a b : ℕ} (hab : a ≤ b) :
    Gamma (t + b) = Gamma (t + a) * ∏ i ∈ Finset.Ico a b, (t + i) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.prod_Ico_succ_top hab, ← mul_assoc, ← ih]
    push_cast
    rw [← add_assoc, Complex.Gamma_add_one]
    · ring
    · intro h
      exact ht (-b) (by push_cast; linear_combination h)

lemma Gamma_add_nat_ne_zero {t : ℂ} (ht : ∀ m : ℤ, t ≠ m) (a : ℕ) : Gamma (t + a) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h
  exact ht (-(m + a : ℕ)) (by push_cast; linear_combination h)

lemma prod_Ico_eq_Gamma_div {t : ℂ} (ht : ∀ m : ℤ, t ≠ m) {a b : ℕ} (hab : a ≤ b) :
    ∏ i ∈ Finset.Ico a b, (t + i) = Gamma (t + b) / Gamma (t + a) := by
  rw [Gamma_add_nat_eq_mul ht hab, mul_div_cancel_left₀ _ (Gamma_add_nat_ne_zero ht a)]

/-- The reflection formula in the form `(-sin πt/π) Γ(-t) = 1/Γ(t+1)`. -/
lemma neg_sin_div_mul_Gamma {t : ℂ} (ht : ∀ m : ℤ, t ≠ m) :
    -sin (Real.pi * t) / Real.pi * Gamma (-t) = (Gamma (t + 1))⁻¹ := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : sin (Real.pi * t) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff]
    rintro ⟨k, hk⟩
    apply ht k
    field_simp at hk
    linear_combination hk
  have h := Complex.Gamma_mul_Gamma_one_sub (-t)
  rw [mul_neg, Complex.sin_neg, sub_neg_eq_add, add_comm 1 t] at h
  apply eq_inv_of_mul_eq_one_left
  rw [mul_assoc, h]
  field_simp

end GammaProducts

section Stirling

/-- The main term `(nζ + b - 1/2)(log n + log ζ) - nζ` of Stirling's formula for `Γ(nζ + b)`. -/
noncomputable def stirT (n : ℕ) (ζ : ℂ) (b : ℕ) : ℂ :=
  (n * ζ + b - 1 / 2) * (Real.log n + log ζ) - n * ζ

/-- Scaled Stirling formula: `Γ(nζ + b) = √(2π) exp(stirT n ζ b + μ)`, `‖μ‖ ≤ K/n`, uniformly
for `b ≤ 2` and `ζ` in the sector `|arg ζ| ≤ π - ε` with `‖ζ‖ ≥ c`. -/
theorem exists_Gamma_scaled {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ K N₀ : ℝ, 0 < K ∧ 1 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → ∀ b : ℕ, b ≤ 2 → ∀ ζ : ℂ, c ≤ ‖ζ‖ →
      |ζ.arg| ≤ Real.pi - ε → ∃ μ : ℂ, ‖μ‖ ≤ K / n ∧
        Gamma (n * ζ + b) = Real.sqrt (2 * Real.pi) * exp (stirT n ζ b + μ) := by
  choose C R hC h using fun b : ℕ => exists_Gamma_add_nat_eq_stirling hε b
  have hCs : 0 < ∑ b ∈ Finset.range 3, C b :=
    Finset.sum_pos (fun b _ => hC b) ⟨0, by simp⟩
  refine ⟨(∑ b ∈ Finset.range 3, C b) / c, max 1 ((∑ b ∈ Finset.range 3, |R b|) / c),
    by positivity, le_max_left _ _, ?_⟩
  intro n hn b hb ζ hζ harg
  have hn1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hζpos : 0 < ‖ζ‖ := hc.trans_le hζ
  have hζ0 : ζ ≠ 0 := norm_pos_iff.mp hζpos
  have hb3 : b ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
  have hCb : C b ≤ ∑ b ∈ Finset.range 3, C b :=
    Finset.single_le_sum (fun b _ => (hC b).le) hb3
  have hRb : R b ≤ ∑ b ∈ Finset.range 3, |R b| :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun b => |R b|) (fun b _ => abs_nonneg _) hb3)
  have hnorm : ‖(n : ℂ) * ζ‖ = n * ‖ζ‖ := by simp
  have hRn : R b ≤ ‖(n : ℂ) * ζ‖ := by
    rw [hnorm]
    have h1 : (∑ b ∈ Finset.range 3, |R b|) / c ≤ n := (le_max_right _ _).trans hn
    rw [div_le_iff₀ hc] at h1
    nlinarith
  have harg' : |((n : ℂ) * ζ).arg| ≤ Real.pi - ε := by
    have := Complex.arg_real_mul ζ hnpos
    rw [Complex.ofReal_natCast] at this
    rwa [this]
  obtain ⟨μ, hμ, hΓ⟩ := h b _ hRn harg'
  have hlog : log ((n : ℂ) * ζ) = Real.log n + log ζ := by
    have := Complex.log_ofReal_mul hnpos hζ0
    rwa [Complex.ofReal_natCast] at this
  refine ⟨μ, hμ.trans ?_, ?_⟩
  · rw [hnorm, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := hCs.le
    calc C b * (c * n) ≤ (∑ b ∈ Finset.range 3, C b) * (c * n) := by gcongr
      _ ≤ (∑ b ∈ Finset.range 3, C b) * (‖ζ‖ * n) := by gcongr
      _ = _ := by ring
  · rw [hΓ, hlog, stirT]

end Stirling

/-- `‖(1 + a) e^ν - 1‖ ≤ 2B + 3A` for `‖a‖ ≤ A`, `‖ν‖ ≤ B ≤ 1`. -/
lemma norm_one_add_mul_exp_sub_one_le {a ν : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hν : ‖ν‖ ≤ B)
    (hB : B ≤ 1) : ‖(1 + a) * exp ν - 1‖ ≤ 2 * B + 3 * A := by
  have h1 : ‖exp ν - 1‖ ≤ 2 * B := (Complex.norm_exp_sub_one_le (hν.trans hB)).trans (by linarith)
  have h2 : ‖exp ν‖ ≤ 3 := by
    calc ‖exp ν‖ = ‖(exp ν - 1) + 1‖ := by ring_nf
      _ ≤ ‖exp ν - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 := by rw [norm_one]; linarith
  have hA : 0 ≤ A := (norm_nonneg _).trans ha
  calc ‖(1 + a) * exp ν - 1‖ = ‖(exp ν - 1) + a * exp ν‖ := by ring_nf
    _ ≤ ‖exp ν - 1‖ + ‖a‖ * ‖exp ν‖ := by rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ 2 * B + A * 3 := by gcongr
    _ = 2 * B + 3 * A := by ring

end GammaAux

end OddZeta
