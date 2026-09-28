import OddZeta.Analytic.Saddle

/-!
# Analytic tools for the saddle-point certificates, part 1: the domain `Ω` and derivatives

`Ω = Omega P` is the open set on which all the logarithms occurring in the phase function `f` are
holomorphic. On `Ω` we have `f' = (f)'`, `f'' = (f')'`, `f''' = (f'')'` and
`(Fd)' = f' + i(r-2)π`. We also record `Re f'` and `Im f'` in terms of `log ‖·‖` and `arg`.
-/

namespace OddZeta.Cert

open Complex

/-- The domain on which all the logarithms in `f` are holomorphic. -/
def Omega (P : Params) : Set ℂ :=
  {u | -u ∈ slitPlane ∧ (P.eta0 : ℂ) + u ∈ slitPlane ∧
    ∀ η ∈ P.zs ++ P.ps, (η : ℂ) + u ∈ slitPlane ∧ (P.eta0 : ℂ) - η + u ∈ slitPlane}

theorem isOpen_Omega (P : Params) : IsOpen (Omega P) := by
  have h1 : ∀ a : ℂ, IsOpen {u : ℂ | a + u ∈ slitPlane} := fun a =>
    isOpen_slitPlane.preimage (continuous_const.add continuous_id)
  have h2 : IsOpen {u : ℂ | -u ∈ slitPlane} := isOpen_slitPlane.preimage continuous_neg
  have h3 : IsOpen {u : ℂ | ∀ η ∈ P.zs ++ P.ps,
      (η : ℂ) + u ∈ slitPlane ∧ (P.eta0 : ℂ) - η + u ∈ slitPlane} := by
    have e : {u : ℂ | ∀ η ∈ P.zs ++ P.ps,
        (η : ℂ) + u ∈ slitPlane ∧ (P.eta0 : ℂ) - η + u ∈ slitPlane} =
        ⋂ η ∈ {η | η ∈ P.zs ++ P.ps},
          ({u : ℂ | (η : ℂ) + u ∈ slitPlane} ∩ {u : ℂ | (P.eta0 : ℂ) - η + u ∈ slitPlane}) := by
      ext u; simp
    rw [e]
    exact (List.finite_toSet _).isOpen_biInter fun η _ => (h1 _).inter (h1 _)
  exact h2.inter ((h1 _).inter h3)

/-- Every point off the real axis lies in `Ω`. -/
theorem mem_Omega_of_im_ne_zero (P : Params) {u : ℂ} (hu : u.im ≠ 0) : u ∈ Omega P := by
  refine ⟨mem_slitPlane_iff.2 (Or.inr (by simpa using hu)),
    mem_slitPlane_iff.2 (Or.inr (by simpa using hu)), fun η _ => ⟨?_, ?_⟩⟩
  · exact mem_slitPlane_iff.2 (Or.inr (by simpa using hu))
  · exact mem_slitPlane_iff.2 (Or.inr (by simpa using hu))

/-- Every `η ∈ zs ++ ps` satisfies `η₁ ≤ η` and `2η < η₀`. -/
theorem valid_bounds {P : Params} (hP : P.Valid) {η : ℕ} (hη : η ∈ P.zs ++ P.ps) :
    P.etaOne ≤ η ∧ 2 * η < P.eta0 := by
  rcases List.mem_append.1 hη with h | h
  · refine ⟨hP.etaOne_le η h, ?_⟩
    have := hP.zs_le_etaMin η h
    have := hP.two_mul_lt _ hP.etaMin_mem
    omega
  · exact ⟨(hP.zs_le_etaMin _ hP.etaOne_mem).trans (hP.etaMin_le η h), hP.two_mul_lt η h⟩

theorem etaOne_lt_eta0 {P : Params} (hP : P.Valid) : 2 * P.etaOne < P.eta0 :=
  (valid_bounds hP (List.mem_append_left _ hP.etaOne_mem)).2

/-- Real parts: for `-η₁ < Re u < 0`, all the arguments of the logarithms have positive real
part. -/
theorem re_pos_of_re {P : Params} (hP : P.Valid) {u : ℂ} (h1 : -(P.etaOne : ℝ) < u.re) :
    0 < (P.eta0 : ℝ) + u.re ∧ ∀ η ∈ P.zs ++ P.ps,
      0 < (η : ℝ) + u.re ∧ 0 < (P.eta0 : ℝ) - η + u.re := by
  have h0 : ((2 * P.etaOne : ℕ) : ℝ) < P.eta0 := by exact_mod_cast etaOne_lt_eta0 hP
  push_cast at h0
  have hpos : (0 : ℝ) ≤ P.etaOne := Nat.cast_nonneg _
  refine ⟨by linarith, fun η hη => ?_⟩
  obtain ⟨h2, h3⟩ := valid_bounds hP hη
  have h2' : (P.etaOne : ℝ) ≤ η := by exact_mod_cast h2
  have h3' : ((2 * η : ℕ) : ℝ) < P.eta0 := by exact_mod_cast h3
  push_cast at h3'
  constructor <;> linarith

/-- Points with `-η₁ < Re u < 0` lie in `Ω`. -/
theorem mem_Omega_of_re {P : Params} (hP : P.Valid) {u : ℂ} (h1 : -(P.etaOne : ℝ) < u.re)
    (h2 : u.re < 0) : u ∈ Omega P := by
  obtain ⟨h0, h⟩ := re_pos_of_re hP h1
  refine ⟨mem_slitPlane_iff.2 (Or.inl (by simpa using h2)),
    mem_slitPlane_iff.2 (Or.inl (by simpa using h0)), fun η hη => ⟨?_, ?_⟩⟩
  · exact mem_slitPlane_iff.2 (Or.inl (by simpa using (h η hη).1))
  · exact mem_slitPlane_iff.2 (Or.inl (by simpa using (h η hη).2))

theorem ne_zero_of_mem_Omega {P : Params} {u : ℂ} (hu : u ∈ Omega P) : u ≠ 0 := by
  intro h
  have := slitPlane_ne_zero hu.1
  rw [h, neg_zero] at this
  exact this rfl

/-! ### List helpers -/

theorem hasDerivAt_list_sum {ι : Type*} (L : List ι) {g : ι → ℂ → ℂ} {g' : ι → ℂ} {u : ℂ}
    (h : ∀ i ∈ L, HasDerivAt (g i) (g' i) u) :
    HasDerivAt (fun w => (L.map fun i => g i w).sum) (L.map g').sum u := by
  induction L with
  | nil => simpa using hasDerivAt_const u (0 : ℂ)
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem list_sum_map_neg {ι : Type*} (L : List ι) (g : ι → ℂ) :
    (L.map fun i => -g i).sum = -(L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem im_list_sum {ι : Type*} (L : List ι) (g : ι → ℂ) :
    (L.map g).sum.im = (L.map fun i => (g i).im).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem re_list_sum {ι : Type*} (L : List ι) (g : ι → ℂ) :
    (L.map g).sum.re = (L.map fun i => (g i).re).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

/-! ### Elementary derivatives -/

theorem hasDerivAt_add_mul_log (a : ℂ) {u : ℂ} (h : a + u ∈ slitPlane) :
    HasDerivAt (fun w => (a + w) * log (a + w)) (log (a + u) + 1) u := by
  have h1 : HasDerivAt (fun w => a + w) 1 u := (hasDerivAt_id' u).const_add a
  have h2 := h1.clog h
  convert h1.mul h2 using 1
  rw [one_mul, mul_one_div_cancel (slitPlane_ne_zero h)]

theorem hasDerivAt_neg_mul_log {u : ℂ} (h : -u ∈ slitPlane) :
    HasDerivAt (fun w => -w * log (-w)) (-log (-u) - 1) u := by
  have h1 : HasDerivAt (fun w : ℂ => -w) (-1) u := (hasDerivAt_id' u).neg
  have h2 := h1.clog h
  convert h1.mul h2 using 1
  rw [mul_div_cancel₀ _ (slitPlane_ne_zero h)]
  ring

theorem hasDerivAt_log_add (a : ℂ) {u : ℂ} (h : a + u ∈ slitPlane) :
    HasDerivAt (fun w => log (a + w)) (a + u)⁻¹ u := by
  have := ((hasDerivAt_id' u).const_add a).clog h
  rwa [one_div] at this

theorem hasDerivAt_log_neg {u : ℂ} (h : -u ∈ slitPlane) :
    HasDerivAt (fun w => log (-w)) u⁻¹ u := by
  have h1 : HasDerivAt (fun w : ℂ => -w) (-1) u := (hasDerivAt_id' u).neg
  have := h1.clog h
  convert this using 1
  rw [neg_div_neg_eq, one_div]

theorem hasDerivAt_inv_add (a : ℂ) {u : ℂ} (h : a + u ≠ 0) :
    HasDerivAt (fun w => (a + w)⁻¹) (-((a + u) ^ 2)⁻¹) u := by
  have := ((hasDerivAt_id' u).const_add a).fun_inv h
  convert this using 1
  rw [neg_div, one_div]

/-! ### The derivatives of `f`, `f'`, `f''`, `Fd` -/

variable {P : Params}

theorem hasDerivAt_f {u : ℂ} (hu : u ∈ Omega P) : HasDerivAt P.f (P.f' u) u := by
  obtain ⟨h0, h1, h2⟩ := hu
  have hA := ((hasDerivAt_neg_mul_log h0).add (hasDerivAt_add_mul_log _ h1)).const_mul
    (P.r : ℂ)
  have hB := hasDerivAt_list_sum (P.zs ++ P.ps)
    (g := fun η w => ((η : ℂ) + w) * log (η + w) - ((P.eta0 : ℂ) - η + w) * log (P.eta0 - η + w))
    (g' := fun η => (log ((η : ℂ) + u) + 1) - (log ((P.eta0 : ℂ) - η + u) + 1))
    (fun η hη => (hasDerivAt_add_mul_log _ (h2 η hη).1).sub
      (hasDerivAt_add_mul_log _ (h2 η hη).2))
  have := (hA.add hB).add_const (P.kappa0 : ℂ)
  unfold Params.f
  convert this using 1
  simp only [Params.f']
  congr 1
  · ring
  · congr 1
    apply List.map_congr_left
    intro η _
    ring

theorem hasDerivAt_f' {u : ℂ} (hu : u ∈ Omega P) : HasDerivAt P.f' (P.f'' u) u := by
  obtain ⟨h0, h1, h2⟩ := hu
  have hA := ((hasDerivAt_log_add _ h1).sub (hasDerivAt_log_neg h0)).const_mul (P.r : ℂ)
  have hB := hasDerivAt_list_sum (P.zs ++ P.ps)
    (g := fun η w => log ((η : ℂ) + w) - log ((P.eta0 : ℂ) - η + w))
    (g' := fun η => ((η : ℂ) + u)⁻¹ - ((P.eta0 : ℂ) - η + u)⁻¹)
    (fun η hη => (hasDerivAt_log_add _ (h2 η hη).1).sub (hasDerivAt_log_add _ (h2 η hη).2))
  have := hA.add hB
  unfold Params.f'
  convert this using 1
  simp only [Params.f'']

theorem hasDerivAt_f'' {u : ℂ} (hu : u ∈ Omega P) : HasDerivAt P.f'' (P.f''' u) u := by
  obtain ⟨h0, h1, h2⟩ := hu
  have hu0 : u ≠ 0 := fun h => slitPlane_ne_zero h0 (by rw [h, neg_zero])
  have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-(u ^ 2)⁻¹) u := by
    simpa using hasDerivAt_inv_add 0 (u := u) (by simpa using hu0)
  have hA := ((hasDerivAt_inv_add _ (slitPlane_ne_zero h1)).sub hinv).const_mul (P.r : ℂ)
  have hB := hasDerivAt_list_sum (P.zs ++ P.ps)
    (g := fun η w => ((η : ℂ) + w)⁻¹ - ((P.eta0 : ℂ) - η + w)⁻¹)
    (g' := fun η => -((((η : ℂ) + u) ^ 2)⁻¹ - (((P.eta0 : ℂ) - η + u) ^ 2)⁻¹))
    (fun η hη => by
      convert (hasDerivAt_inv_add _ (slitPlane_ne_zero (h2 η hη).1)).sub
        (hasDerivAt_inv_add _ (slitPlane_ne_zero (h2 η hη).2)) using 1
      ring)
  have := hA.add hB
  unfold Params.f''
  convert this using 1
  simp only [Params.f''']
  rw [list_sum_map_neg]
  ring

theorem hasDerivAt_Fd {u : ℂ} (hu : u ∈ Omega P) :
    HasDerivAt P.Fd (P.f' u + I * ((P.r : ℂ) - 2) * Real.pi) u := by
  have := (hasDerivAt_f hu).add ((hasDerivAt_id' u).const_mul (I * ((P.r : ℂ) - 2) * Real.pi))
  rw [mul_one] at this
  exact this

theorem differentiableOn_f' : DifferentiableOn ℂ P.f' (Omega P) := fun _ hu =>
  (hasDerivAt_f' hu).differentiableAt.differentiableWithinAt

theorem differentiableOn_f'' : DifferentiableOn ℂ P.f'' (Omega P) := fun _ hu =>
  (hasDerivAt_f'' hu).differentiableAt.differentiableWithinAt

/-! ### Real and imaginary parts of `f'` -/

/-- `Im f'(u) = r[arg(η₀+u) - arg(-u)] + ∑_η [arg(η+u) - arg(η₀-η+u)]` (for every `u`). -/
theorem im_f' (P : Params) (u : ℂ) : (P.f' u).im =
    P.r * (arg (P.eta0 + u) - arg (-u)) +
      ((P.zs ++ P.ps).map fun η : ℕ => arg (η + u) - arg (P.eta0 - η + u)).sum := by
  simp only [Params.f', add_im, mul_im, natCast_re, natCast_im, zero_mul, add_zero, sub_im,
    log_im, im_list_sum]

/-- `Re f'(u) = r[log|η₀+u| - log|u|] + ∑_η [log|η+u| - log|η₀-η+u|]` (for every `u`). -/
theorem re_f' (P : Params) (u : ℂ) : (P.f' u).re =
    P.r * (Real.log ‖(P.eta0 : ℂ) + u‖ - Real.log ‖u‖) +
      ((P.zs ++ P.ps).map fun η : ℕ =>
        Real.log ‖(η : ℂ) + u‖ - Real.log ‖(P.eta0 : ℂ) - η + u‖).sum := by
  simp only [Params.f', add_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, sub_re,
    log_re, re_list_sum, norm_neg]

end OddZeta.Cert
