import OddZeta.Analytic.SaddleAux2

/-!
# The contribution of `L \ σ` to the saddle-point asymptotics

Pointwise bounds for the integrand `S(nu) Gₙ(nu)` on `L`, and the proof that the pieces of `L`
other than `σ` contribute `o(Kₙ)`.
-/

namespace OddZeta

open Complex MeasureTheory Filter Topology

namespace Params

variable {P : Params} {D : PathData} {b c c₀ ε₀ : ℝ}

/-- The normalisation `(r-1)! √n / (Aₙ e^{nH})`. -/
noncomputable def Qn (P : Params) (H : ℝ) (n : ℕ) : ℝ :=
  ((P.r - 1).factorial : ℝ) * Real.sqrt n / (P.An n * Real.exp (n * H))

theorem Qn_nonneg (hP : P.Valid) (H : ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ P.Qn H n := by
  have := An_pos hP hn
  unfold Qn
  positivity

/-- `Qₙ · Aₙ e^{n(H - κ)} = (r-1)! √n e^{-κn}`. -/
theorem Qn_mul (hP : P.Valid) (H κ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    P.Qn H n * (P.An n * Real.exp (n * (H - κ))) =
      ((P.r - 1).factorial : ℝ) * Real.sqrt n * Real.exp (-κ * n) := by
  have hA := An_pos hP hn
  have he : Real.exp (n * (H - κ)) = Real.exp (n * H) * Real.exp (-κ * n) := by
    rw [← Real.exp_add]; ring_nf
  unfold Qn
  rw [he]
  field_simp

theorem im_natCast_mul (n : ℕ) (u : ℂ) : ((n : ℂ) * u).im = n * u.im := by
  simp

/-- The dominant bound for the integrand on `L`. -/
theorem norm_integrand_le (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {u : ℂ} (hu : u.im ≤ 0) {C : ℝ}
    (hGh : P.Ghat u ≠ 0)
    (hE : ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n) :
    ‖trigS P.r (n * u) * P.G n (n * u)‖ ≤
      2 * (1 + |C|) * P.An n * Real.exp (n * (P.Fd u).re) * ‖P.Ghat u‖ := by
  have hA := An_pos hP hn
  have hr : 2 ≤ P.r := by have := hP.three_le_r; omega
  have him : ((n : ℂ) * u).im ≤ 0 := by
    rw [im_natCast_mul]; exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hu
  have h1 := norm_trigS_le hr him
  have h2 := norm_G_le hn hA hGh hE
  have hexp : Real.exp ((P.r - 2) * Real.pi * (-((n : ℂ) * u).im)) *
      Real.exp (n * (P.f u).re) = Real.exp (n * (P.Fd u).re) := by
    rw [← Real.exp_add, re_Fd, im_natCast_mul]; ring_nf
  calc ‖trigS P.r (n * u) * P.G n (n * u)‖
      = ‖trigS P.r (n * u)‖ * ‖P.G n (n * u)‖ := norm_mul _ _
    _ ≤ (2 * Real.exp ((P.r - 2) * Real.pi * (-((n : ℂ) * u).im))) *
        ((1 + |C|) * (P.An n * Real.exp (n * (P.f u).re) * ‖P.Ghat u‖)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 2 * (1 + |C|) * P.An n * (Real.exp ((P.r - 2) * Real.pi * (-((n : ℂ) * u).im)) *
        Real.exp (n * (P.f u).re)) * ‖P.Ghat u‖ := by ring
    _ = _ := by rw [hexp]

/-- The bound for the subdominant modes. -/
theorem norm_sub_integrand_le (hP : P.Valid) {n : ℕ} (hn : 1 ≤ n) {u : ℂ} (hu : u.im ≤ 0)
    {C : ℝ} (hGh : P.Ghat u ≠ 0)
    (hE : ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n) :
    ‖(trigS P.r (n * u) - ((P.r - 1).factorial : ℂ)⁻¹ *
        exp (I * Real.pi * ((P.r : ℂ) - 2) * (n * u))) * P.G n (n * u)‖ ≤
      (1 + |C|) * P.An n * Real.exp (n * ((P.Fd u).re + 2 * Real.pi * u.im)) *
        ‖P.Ghat u‖ := by
  have hA := An_pos hP hn
  have hr : 2 ≤ P.r := by have := hP.three_le_r; omega
  have him : ((n : ℂ) * u).im ≤ 0 := by
    rw [im_natCast_mul]; exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hu
  have h1 := norm_trigS_sub_le hr him
  have h2 := norm_G_le hn hA hGh hE
  have hexp : Real.exp ((P.r - 4) * Real.pi * (-((n : ℂ) * u).im)) *
      Real.exp (n * (P.f u).re) = Real.exp (n * ((P.Fd u).re + 2 * Real.pi * u.im)) := by
    rw [← Real.exp_add, re_Fd, im_natCast_mul]; ring_nf
  calc _ = ‖trigS P.r (n * u) - ((P.r - 1).factorial : ℂ)⁻¹ *
        exp (I * Real.pi * ((P.r : ℂ) - 2) * (n * u))‖ * ‖P.G n (n * u)‖ := norm_mul _ _
    _ ≤ Real.exp ((P.r - 4) * Real.pi * (-((n : ℂ) * u).im)) *
        ((1 + |C|) * (P.An n * Real.exp (n * (P.f u).re) * ‖P.Ghat u‖)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (1 + |C|) * P.An n * (Real.exp ((P.r - 4) * Real.pi * (-((n : ℂ) * u).im)) *
        Real.exp (n * (P.f u).re)) * ‖P.Ghat u‖ := by ring
    _ = _ := by rw [hexp]

/-- A piece of `L` parametrised over a compact interval, on which `Re Fd ≤ H - κ`, contributes
`O(√n e^{-κn})` relative to `Aₙ e^{nH}`. -/
theorem tendsto_piece (hP : P.Valid) (hD : P.PathCert D b c c₀ ε₀) {C : ℝ} {N : ℕ}
    (hN : 1 ≤ N)
    (hE : ∀ n ≥ N, ∀ u ∈ D.pathSet,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n)
    {γ : ℝ → ℂ} {a₁ a₂ M κ : ℝ} (hκ : 0 < κ)
    (hγ : ∀ t ∈ Set.uIcc a₁ a₂, γ t ∈ D.pathSet ∧ (γ t).im ≤ 0 ∧
      (P.Fd (γ t)).re ≤ (P.Fd D.u).re - κ ∧ ‖P.Ghat (γ t)‖ ≤ M) :
    Tendsto (fun n : ℕ => (P.Qn (P.Fd D.u).re n : ℂ) *
      ∫ t in a₁..a₂, trigS P.r (n * γ t) * P.G n (n * γ t)) atTop (𝓝 0) := by
  set H := (P.Fd D.u).re
  have hM : 0 ≤ M := (norm_nonneg _).trans (hγ a₁ Set.left_mem_uIcc).2.2.2
  set K : ℝ := ((P.r - 1).factorial : ℝ) * (2 * (1 + |C|) * M * |a₂ - a₁|)
  refine squeeze_zero_norm' ?_ (tendsto_sqrt_mul_exp_neg hκ K)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn1 : 1 ≤ n := hN.trans hn
  have hA := An_pos hP hn1
  have hbound : ∀ t ∈ Set.uIoc a₁ a₂, ‖trigS P.r (n * γ t) * P.G n (n * γ t)‖ ≤
      2 * (1 + |C|) * M * (P.An n * Real.exp (n * (H - κ))) := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hγ t (Set.uIoc_subset_uIcc ht)
    refine (norm_integrand_le hP hn1 h2 (Ghat_ne_zero_of_mem hD h1) (hE n hn _ h1)).trans ?_
    have h5 : Real.exp (n * (P.Fd (γ t)).re) ≤ Real.exp (n * (H - κ)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n))
    calc 2 * (1 + |C|) * P.An n * Real.exp (n * (P.Fd (γ t)).re) * ‖P.Ghat (γ t)‖
        ≤ 2 * (1 + |C|) * P.An n * Real.exp (n * (H - κ)) * M := by gcongr
      _ = _ := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Qn_nonneg hP H hn1)]
  calc P.Qn H n * ‖∫ t in a₁..a₂, trigS P.r (n * γ t) * P.G n (n * γ t)‖
      ≤ P.Qn H n * (2 * (1 + |C|) * M * (P.An n * Real.exp (n * (H - κ))) * |a₂ - a₁|) :=
        mul_le_mul_of_nonneg_left hint (Qn_nonneg hP H hn1)
    _ = 2 * (1 + |C|) * M * |a₂ - a₁| * (P.Qn H n * (P.An n * Real.exp (n * (H - κ)))) := by
        ring
    _ = K * Real.sqrt n * Real.exp (-κ * n) := by rw [Qn_mul hP H κ hn1]; ring

/-- The horizontal segment. -/
theorem tendsto_horiz (hP : P.Valid) (hD : P.PathCert D b c c₀ ε₀) {C : ℝ} {N : ℕ}
    (hN : 1 ≤ N)
    (hE : ∀ n ≥ N, ∀ u ∈ D.pathSet,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n) :
    Tendsto (fun n : ℕ => (P.Qn (P.Fd D.u).re n : ℂ) *
      segInt (fun u => trigS P.r (n * u) * P.G n (n * u)) D.top D.corner) atTop (𝓝 0) := by
  have huI : Set.uIcc D.top.re D.x1 = Set.Icc D.x1 D.top.re := Set.uIcc_of_ge hD.x1_lt.le
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Set.Icc D.x1 D.top.re, ‖P.Ghat (x + D.top.im * I)‖ ≤ M := by
    refine isCompact_Icc.exists_bound_of_continuousOn fun x _ => ?_
    have hg : P.Good ((x : ℂ) + D.top.im * I) :=
      good_of_im_ne_zero (by simp; linarith [hD.top_im_neg])
    exact ((continuousAt_Ghat hg).comp (f := fun x : ℝ => (x : ℂ) + D.top.im * I)
      (by fun_prop)).continuousWithinAt
  have key := tendsto_piece hP hD hN hE (γ := fun x : ℝ => (x : ℂ) + D.top.im * I)
    (a₁ := D.top.re) (a₂ := D.x1) (M := M) hD.b_pos (fun t ht => by
      rw [huI] at ht
      refine ⟨mem_pathSet_horiz hD ht, ?_, hD.horiz_bound ht, hM t ht⟩
      simp [hD.top_im_neg.le])
  refine key.congr fun n => ?_
  congr 1
  have := segInt_horizontal (fun u => trigS P.r (n * u) * P.G n (n * u)) D.top.re D.x1 D.top.im
  rw [re_add_im] at this
  exact this.symm

/-- The vertical segment. -/
theorem tendsto_vert (hP : P.Valid) (hD : P.PathCert D b c c₀ ε₀) {C : ℝ} {N : ℕ}
    (hN : 1 ≤ N)
    (hE : ∀ n ≥ N, ∀ u ∈ D.pathSet,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n) :
    Tendsto (fun n : ℕ => (P.Qn (P.Fd D.u).re n : ℂ) *
      segInt (fun u => trigS P.r (n * u) * P.G n (n * u)) D.corner D.x1) atTop (𝓝 0) := by
  have huI : Set.uIcc D.top.im 0 = Set.Icc D.top.im 0 := Set.uIcc_of_le hD.top_im_neg.le
  obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ Set.Icc D.top.im 0, ‖P.Ghat (D.x1 + y * I)‖ ≤ M := by
    refine isCompact_Icc.exists_bound_of_continuousOn fun y hy => ?_
    have hg : P.Good ((D.x1 : ℂ) + y * I) := by
      rcases hy.2.lt_or_eq with h | h
      · exact good_of_im_ne_zero (by simp; linarith)
      · rw [h]
        simpa using good_of_real hP hD.x1_neg hD.x1_gt
    exact ((continuousAt_Ghat hg).comp (f := fun y : ℝ => (D.x1 : ℂ) + y * I)
      (by fun_prop)).continuousWithinAt
  have key := tendsto_piece hP hD hN hE (γ := fun y : ℝ => (D.x1 : ℂ) + y * I)
    (a₁ := D.top.im) (a₂ := 0) (M := M) hD.b_pos (fun t ht => by
      rw [huI] at ht
      refine ⟨mem_pathSet_vert hD ht, ?_, hD.vert_bound hP ht, hM t ht⟩
      simp [ht.2])
  have key2 := key.const_mul I
  rw [mul_zero] at key2
  refine key2.congr fun n => ?_
  have := segInt_vertical (fun u => trigS P.r (n * u) * P.G n (n * u)) D.x1 D.top.im 0
  simp only [ofReal_zero, zero_mul, add_zero] at this
  change _ = _ * segInt _ (D.x1 + D.top.im * I) _
  rw [this]
  ring

/-- The vertical ray. -/
theorem tendsto_ray (hP : P.Valid) (hD : P.PathCert D b c c₀ ε₀) {C : ℝ} {N : ℕ}
    (hN : 1 ≤ N)
    (hE : ∀ n ≥ N, ∀ u ∈ D.pathSet,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n) :
    Tendsto (fun n : ℕ => (P.Qn (P.Fd D.u).re n : ℂ) * ((∫ y in Set.Iic D.bot.im,
      trigS P.r (n * (D.bot.re + y * I)) * P.G n (n * (D.bot.re + y * I))) * I))
      atTop (𝓝 0) := by
  set H := (P.Fd D.u).re with hH
  have hbot := hD.bot_im_neg
  have hc := hD.c_pos
  have hβ : 0 < -D.bot.im := by linarith
  set A : ℝ := 2 * P.r + 2 * (P.zs ++ P.ps).length with hA_def
  have hA0 : 0 ≤ A := by positivity
  set A₁ : ℝ := 2 + A with hA₁_def
  have hA₁ : 0 ≤ A₁ := by positivity
  set A₀ : ℝ := P.eta0 + A * (|Real.log (-D.bot.im)| + 2 * P.eta0) + A₁ * ‖D.bot‖ with hA₀_def
  -- growth of `Ĝ` along the ray
  have hGb : ∀ y ≤ D.bot.im,
      ‖P.Ghat (D.bot.re + y * I)‖ ≤ Real.exp (A₀ + A₁ * (D.bot.im - y)) := by
    intro y hy
    have him : -D.bot.im ≤ |((D.bot.re : ℂ) + y * I).im| := by
      have : ((D.bot.re : ℂ) + y * I).im = y := by simp
      rw [this, abs_of_neg (by linarith)]
      linarith
    have h1 := norm_Ghat_le hP hβ him
    have hu : ‖(D.bot.re : ℂ) + y * I‖ ≤ ‖D.bot‖ + (D.bot.im - y) := by
      have e : (D.bot.re : ℂ) + y * I = D.bot + ((y - D.bot.im : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      linarith
    refine h1.trans (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_left hu hA₁
    rw [hA₀_def]
    rw [hA₁_def] at this ⊢
    nlinarith
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge ((A₁ + c) / c)
  set K : ℝ := ((P.r - 1).factorial : ℝ) * (2 * (1 + |C|) * Real.exp A₀ / c) with hK
  refine squeeze_zero_norm' ?_ (tendsto_sqrt_mul_exp_neg hD.b_pos K)
  filter_upwards [eventually_ge_atTop (max N n₁)] with n hn
  have hnN : N ≤ n := le_of_max_le_left hn
  have hn1 : 1 ≤ n := hN.trans hnN
  have hnc : A₁ + c ≤ n * c := by
    have : (A₁ + c) / c ≤ n := hn₁.trans (by exact_mod_cast le_of_max_le_right hn)
    rwa [div_le_iff₀ hc] at this
  have hA := An_pos hP hn1
  set B₀ : ℝ := 2 * (1 + |C|) * (P.An n * Real.exp (n * (H - b))) *
    Real.exp (A₀ - c * D.bot.im) with hB₀
  have hbound : ∀ y ∈ Set.Iic D.bot.im,
      ‖trigS P.r (n * (D.bot.re + y * I)) * P.G n (n * (D.bot.re + y * I))‖ ≤
        B₀ * Real.exp (c * y) := by
    intro y hy
    have hy' : y ≤ D.bot.im := hy
    have hmem := mem_pathSet_ray (D := D) hy'
    have him : ((D.bot.re : ℂ) + y * I).im ≤ 0 := by simp; linarith
    refine (norm_integrand_le hP hn1 him (Ghat_ne_zero_of_mem hD hmem)
      (hE n hnN _ hmem)).trans ?_
    have h1 : (n : ℝ) * (P.Fd (D.bot.re + y * I)).re ≤ n * (H - b - c * (D.bot.im - y)) :=
      mul_le_mul_of_nonneg_left (hD.ray_bound hy') (Nat.cast_nonneg n)
    have h2 := hGb y hy'
    have h3 : (n : ℝ) * (H - b - c * (D.bot.im - y)) + (A₀ + A₁ * (D.bot.im - y)) ≤
        n * (H - b) + (A₀ - c * D.bot.im) + c * y := by
      nlinarith [mul_nonneg (sub_nonneg.2 hnc) (sub_nonneg.2 hy')]
    have h4 : 0 ≤ 2 * (1 + |C|) * P.An n := by positivity
    calc 2 * (1 + |C|) * P.An n * Real.exp (n * (P.Fd (D.bot.re + y * I)).re) *
          ‖P.Ghat (D.bot.re + y * I)‖
        ≤ 2 * (1 + |C|) * P.An n * Real.exp (n * (H - b - c * (D.bot.im - y))) *
          Real.exp (A₀ + A₁ * (D.bot.im - y)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) h4) h2 (norm_nonneg _)
            (by positivity)
      _ = 2 * (1 + |C|) * P.An n *
          Real.exp (n * (H - b - c * (D.bot.im - y)) + (A₀ + A₁ * (D.bot.im - y))) := by
          rw [Real.exp_add (n * (H - b - c * (D.bot.im - y))) (A₀ + A₁ * (D.bot.im - y))]; ring
      _ ≤ 2 * (1 + |C|) * P.An n * Real.exp (n * (H - b) + (A₀ - c * D.bot.im) + c * y) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) h4
      _ = B₀ * Real.exp (c * y) := by
          rw [hB₀, Real.exp_add, Real.exp_add]; ring
  have hint : IntegrableOn (fun y => B₀ * Real.exp (c * y)) (Set.Iic D.bot.im) :=
    (integrableOn_exp_mul_Iic hc _).const_mul B₀
  have hI := norm_integral_le_of_norm_le hint
    (ae_restrict_of_forall_mem measurableSet_Iic hbound)
  rw [integral_const_mul, integral_exp_mul_Iic hc] at hI
  have hE' : Real.exp (A₀ - c * D.bot.im) * Real.exp (c * D.bot.im) = Real.exp A₀ := by
    rw [← Real.exp_add]; ring_nf
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Qn_nonneg hP H hn1)]
  calc P.Qn H n * ‖∫ y in Set.Iic D.bot.im,
        trigS P.r (n * (D.bot.re + y * I)) * P.G n (n * (D.bot.re + y * I))‖
      ≤ P.Qn H n * (B₀ * (Real.exp (c * D.bot.im) / c)) :=
        mul_le_mul_of_nonneg_left hI (Qn_nonneg hP H hn1)
    _ = 2 * (1 + |C|) * Real.exp A₀ / c * (P.Qn H n * (P.An n * Real.exp (n * (H - b)))) := by
        rw [hB₀, ← hE']; ring
    _ = K * Real.sqrt n * Real.exp (-b * n) := by
        rw [Qn_mul hP H b hn1, hK]; ring

end Params

end OddZeta
