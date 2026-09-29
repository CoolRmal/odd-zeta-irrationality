import OddZeta.Analytic.Saddle2Aux

/-!
# The contribution of the segment `σ` for a general path

A version of `tendsto_sigma` (from `SaddleAux4`) for the segment `σ = [u - v, u + v]` of an
arbitrary path: Stirling's formula is only assumed uniformly on a set `U` containing `σ`.
-/

namespace OddZeta

open Complex MeasureTheory Filter Topology

namespace Params

variable {P : Params}

/-- The segment `σ = [u - v, u + v]` through the saddle point `u` (Laplace's method). -/
theorem tendsto_sigma_gen (hP : P.Valid) {U : Set ℂ} (hU : ∀ z ∈ U, (P.eta0 : ℂ) + 2 * z ≠ 0)
    {C : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hE : ∀ n ≥ N, ∀ u ∈ U,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n)
    {u v : ℂ} {b : ℝ} (hmemσ : ∀ s ∈ Set.Icc (-1 : ℝ) 1, u + s * v ∈ U)
    (hbot : (u - v).im < 0) (htop : (u + v).im < 0)
    (hsaddle : P.f' u + I * ((P.r : ℂ) - 2) * Real.pi = 0)
    (hre_a : 0 < (-(P.f'' u) * v ^ 2 / 2).re) (hb : 0 < b)
    (hdecay : ∀ s ∈ Set.Icc (-1 : ℝ) 1, (P.Fd (u + s * v) - P.Fd u).re ≤ -b * s ^ 2) :
    Tendsto (fun n : ℕ => (P.Qn (P.Fd u).re n : ℂ) *
      segInt (fun u => trigS P.r (n * u) * P.G n (n * u)) (u - v) (u + v) -
        cexp (I * (n * (P.Fd u).im)) *
          (v * P.Ghat u * (Real.pi / (-(P.f'' u) * v ^ 2 / 2)) ^ (1 / 2 : ℂ)))
      atTop (𝓝 0) := by
  set H := (P.Fd u).re with hH
  set α := (P.Fd u).im with hα
  set a : ℂ := -(P.f'' u) * v ^ 2 / 2 with ha
  set B : ℂ := v * P.Ghat u * (Real.pi / a) ^ (1 / 2 : ℂ) with hB
  -- the parametrisation of `σ`
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℂ, w = fun s : ℝ => u + (s : ℂ) * v := ⟨_, rfl⟩
  have hw_cont : Continuous w := by rw [hw]; fun_prop
  have hw_der : ∀ s : ℝ, HasDerivAt w v s := fun s => by
    rw [hw]; simpa using ((hasDerivAt_id s).ofReal_comp.mul_const v).const_add u
  have hw0 : w 0 = u := by rw [hw]; simp
  have hws : ∀ s : ℝ, w s = u + s * v := fun s => by rw [hw]
  set δ := min (-(u - v).im) (-(u + v).im) with hδ
  have hδpos : 0 < δ := lt_min (by linarith [hbot]) (by linarith [htop])
  have hw_im : ∀ s ∈ Set.Icc (-1 : ℝ) 1, (w s).im ≤ -δ := by
    intro s hs
    have h1 : u.im - v.im ≤ -δ := by
      have h := min_le_left (-(u - v).im) (-(u + v).im)
      have e : (u - v).im = u.im - v.im := sub_im u v
      rw [← hδ] at h
      linarith
    have h2 : u.im + v.im ≤ -δ := by
      have h := min_le_right (-(u - v).im) (-(u + v).im)
      have e : (u + v).im = u.im + v.im := add_im u v
      rw [← hδ] at h
      linarith
    have e : (w s).im = u.im + s * v.im := by rw [hws]; simp
    rw [e]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s)
        (by linarith : u.im - v.im + δ ≤ 0),
      mul_nonpos_of_nonneg_of_nonpos (by linarith [hs.1] : (0 : ℝ) ≤ 1 + s)
        (by linarith : u.im + v.im + δ ≤ 0)]
  have hw_neg : ∀ s ∈ Set.Icc (-1 : ℝ) 1, (w s).im < 0 := fun s hs => by
    linarith [hw_im s hs]
  have hw_lower : ∀ s ∈ Set.Icc (-1 : ℝ) 1, w s ∈ lowerHalf := hw_neg
  have hw_good : ∀ s ∈ Set.Icc (-1 : ℝ) 1, P.Good (w s) := fun s hs =>
    good_of_im_ne_zero (hw_neg s hs).ne
  have hw_mem : ∀ s ∈ Set.Icc (-1 : ℝ) 1, w s ∈ U := fun s hs => by
    rw [hws]; exact hmemσ s hs
  -- the data for Laplace's method
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ → ℂ, h = fun s => P.Fd (w s) - P.Fd u := ⟨_, rfl⟩
  obtain ⟨g, hg_def⟩ : ∃ g : ℝ → ℂ, g = fun s => v * P.Ghat (w s) := ⟨_, rfl⟩
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℕ → ℝ → ℂ, ε = fun n s => if N ≤ n then
      P.G n (n * w s) / (P.An n * exp (n * P.f (w s)) * P.Ghat (w s)) - 1 else 0 :=
    ⟨_, rfl⟩
  have hε_eq : ∀ n ≥ N, ∀ s, ε n s =
      P.G n (n * w s) / (P.An n * exp (n * P.f (w s)) * P.Ghat (w s)) - 1 := by
    intro n hn s; rw [hε_def]; simp only [hn, ↓reduceIte]
  -- continuity
  have hh_cont : ContinuousOn h (Set.Icc (-1) 1) := by
    intro s hs; rw [hh_def]
    exact (((hasDerivAt_Fd (hw_good s hs)).continuousAt.comp hw_cont.continuousAt).sub
      continuousAt_const).continuousWithinAt
  have hg_cont : ContinuousOn g (Set.Icc (-1) 1) := by
    intro s hs; rw [hg_def]
    exact (continuousAt_const.mul ((continuousAt_Ghat (hw_good s hs)).comp
      hw_cont.continuousAt)).continuousWithinAt
  have hnw_im : ∀ n : ℕ, 1 ≤ n → ∀ s ∈ Set.Icc (-1 : ℝ) 1, ((n : ℂ) * w s).im ≠ 0 := by
    intro n hn s hs
    rw [im_natCast_mul]
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact (mul_neg_of_pos_of_neg this (hw_neg s hs)).ne
  have hG_cont : ∀ n : ℕ, 1 ≤ n →
      ContinuousOn (fun s => P.G n (n * w s)) (Set.Icc (-1) 1) := by
    intro n hn s hs
    exact ((continuousAt_G n (hnw_im n hn s hs)).comp (f := fun s : ℝ => (n : ℂ) * w s)
      (by fun_prop)).continuousWithinAt
  have hden_cont : ∀ n : ℕ, ContinuousOn
      (fun s => (P.An n : ℂ) * exp (n * P.f (w s)) * P.Ghat (w s)) (Set.Icc (-1) 1) := by
    intro n s hs
    exact ((continuousAt_const.mul ((continuousAt_const.mul ((continuousAt_f (hw_good s hs)).comp
      hw_cont.continuousAt)).cexp)).mul ((continuousAt_Ghat (hw_good s hs)).comp
        hw_cont.continuousAt)).continuousWithinAt
  have hden_ne : ∀ n : ℕ, 1 ≤ n → ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      (P.An n : ℂ) * exp (n * P.f (w s)) * P.Ghat (w s) ≠ 0 := by
    intro n hn s hs
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast (An_pos hP hn).ne') (exp_ne_zero _))
      (Ghat_ne_zero (hU _ (hw_mem s hs)))
  have hε_cont : ∀ n, ContinuousOn (ε n) (Set.Icc (-1) 1) := by
    intro n
    by_cases hn : N ≤ n
    · have hn1 : 1 ≤ n := hN.trans hn
      have := ((hG_cont n hn1).div (hden_cont n) (hden_ne n hn1)).sub
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℂ)) _)
      exact this.congr fun s _ => hε_eq n hn s
    · rw [hε_def]; simp only [hn, ↓reduceIte]; exact continuousOn_const
  -- the Taylor bound for `h`
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖deriv P.f'' (w s)‖ ≤ M₀ :=
    isCompact_Icc.exists_bound_of_continuousOn
      (continuousOn_deriv_f''.comp hw_cont.continuousOn hw_lower)
  have h_taylor : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖h s + a * s ^ 2‖ ≤ (M₀ * ‖v‖ ^ 3) * |s| ^ 3 := by
    have key := norm_sub_taylor2_le (φ := h)
      (φ1 := fun s => (P.f' (w s) + I * ((P.r : ℂ) - 2) * Real.pi) * v)
      (φ2 := fun s => P.f'' (w s) * v * v)
      (φ3 := fun s => deriv P.f'' (w s) * v * v * v) (M := M₀ * ‖v‖ ^ 3)
      (fun s hs => by
        rw [hh_def]
        exact ((hasDerivAt_Fd (hw_good s hs)).comp s (hw_der s)).sub_const _)
      (fun s hs => (((hasDerivAt_f' (hw_good s hs)).comp s (hw_der s)).add_const _).mul_const v)
      (fun s hs => (((differentiableAt_f'' (hw_good s hs)).hasDerivAt.comp s
        (hw_der s)).mul_const v).mul_const v)
      (fun s hs => by
        simp only [norm_mul]
        calc ‖deriv P.f'' (w s)‖ * ‖v‖ * ‖v‖ * ‖v‖
            ≤ M₀ * ‖v‖ * ‖v‖ * ‖v‖ := by gcongr; exact hM₀ s hs
          _ = M₀ * ‖v‖ ^ 3 := by ring)
    intro s hs
    have e : h s + a * s ^ 2 = h s - h 0 -
        (P.f' (w 0) + I * ((P.r : ℂ) - 2) * Real.pi) * v * s -
          P.f'' (w 0) * v * v * s ^ 2 / 2 := by
      rw [hw0, hsaddle]
      have : h 0 = 0 := by rw [hh_def]; simp only [hw0, sub_self]
      rw [this, ha]
      ring
    rw [e]
    exact key s hs
  -- the Lipschitz bound for `g`
  obtain ⟨M₁, hM₁⟩ : ∃ M₁, ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖deriv P.Ghat (w s)‖ ≤ M₁ :=
    isCompact_Icc.exists_bound_of_continuousOn
      (continuousOn_deriv_Ghat.comp hw_cont.continuousOn hw_lower)
  have hg_lip : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖g s - g 0‖ ≤ (M₁ * ‖v‖ ^ 2) * |s| := by
    refine norm_sub_le_of_hasDerivAt (φ1 := fun s => v * (deriv P.Ghat (w s) * v))
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [hg_def]
      exact ((differentiableAt_Ghat (hw_good s hs)).hasDerivAt.comp s (hw_der s)).const_mul v
    · simp only [norm_mul]
      calc ‖v‖ * (‖deriv P.Ghat (w s)‖ * ‖v‖) ≤ ‖v‖ * (M₁ * ‖v‖) := by
            gcongr; exact hM₁ s hs
        _ = M₁ * ‖v‖ ^ 2 := by ring
  -- the error term
  have hε_bd : ∀ n : ℕ, ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖ε n s‖ ≤ |C| / n := by
    intro n s hs
    by_cases hn : N ≤ n
    · rw [hε_eq n hn s]
      exact (hE n hn _ (hw_mem s hs)).trans
        (div_le_div_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg n))
    · rw [hε_def]; simp only [hn, ↓reduceIte, norm_zero]; positivity
  -- Laplace's method
  have hlap := tendsto_sqrt_mul_integral_laplace (s₀ := 1) zero_lt_one hb hre_a
    hh_cont hg_cont h_taylor (fun s hs => by simp only [hh_def, hws]; exact hdecay s hs)
    hg_lip ε hε_cont hε_bd
  have hg0 : g 0 * (Real.pi / a) ^ (1 / 2 : ℂ) = B := by
    rw [hg_def]; simp only [hw0, hB]
  rw [hg0] at hlap
  -- the segment integral as a real integral
  have hseg : ∀ n : ℕ, segInt (fun u => trigS P.r (n * u) * P.G n (n * u)) (u - v) (u + v) =
      v * ∫ s in (-1 : ℝ)..1, trigS P.r (n * w s) * P.G n (n * w s) := by
    intro n
    have e1 : u - v = u + ((-1 : ℝ) : ℂ) * v := by push_cast; ring
    have e2 : u + v = u + ((1 : ℝ) : ℂ) * v := by push_cast; ring
    rw [e1, e2, segInt_line]
    simp only [hws]
  -- the pointwise decomposition into dominant and subdominant modes
  have hpt : ∀ n ≥ N, ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      (P.Qn H n : ℂ) * (v * (trigS P.r (n * w s) * P.G n (n * w s))) =
        cexp (I * (n * α)) * (Real.sqrt n * (exp (n * h s) * g s * (1 + ε n s))) +
        (P.Qn H n : ℂ) * v * ((trigS P.r (n * w s) - ((P.r - 1).factorial : ℂ)⁻¹ *
          exp (I * Real.pi * ((P.r : ℂ) - 2) * (n * w s))) * P.G n (n * w s)) := by
    intro n hn s hs
    have hn1 : 1 ≤ n := hN.trans hn
    have hA := An_pos hP hn1
    have hexp : exp (I * Real.pi * ((P.r : ℂ) - 2) * (n * w s)) * exp (n * P.f (w s)) =
        cexp (I * (n * α)) * exp (n * h s) * (Real.exp (n * H) : ℂ) := by
      rw [ofReal_exp, ← exp_add, ← exp_add, ← exp_add]
      congr 1
      have hFu : P.Fd u = H + α * I := (re_add_im _).symm
      rw [hh_def]
      simp only
      rw [hFu]
      unfold Fd
      push_cast
      ring
    have := key_identity (Q := (P.Qn H n : ℂ)) (v := v) (T := trigS P.r (n * w s))
      (E := exp (I * Real.pi * ((P.r : ℂ) - 2) * (n * w s))) (G := P.G n (n * w s))
      (c := ((P.r - 1).factorial : ℂ)) (sq := (Real.sqrt n : ℂ)) (e1 := cexp (I * (n * α)))
      (eh := exp (n * h s)) (EH := (Real.exp (n * H) : ℂ)) (AA := (P.An n : ℂ))
      (fe := exp (n * P.f (w s))) (Gh := P.Ghat (w s)) (ε := ε n s)
      (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)) (by exact_mod_cast hA.ne')
      (by exact_mod_cast (Real.exp_pos _).ne') (exp_ne_zero _)
      (Ghat_ne_zero (hU _ (hw_mem s hs))) (by unfold Qn; push_cast; ring) (hε_eq n hn s) hexp
    rw [hg_def]
    exact this
  -- integration of the decomposition
  have hint_eq : ∀ n ≥ N, (P.Qn H n : ℂ) *
      segInt (fun u => trigS P.r (n * u) * P.G n (n * u)) (u - v) (u + v) =
      cexp (I * (n * α)) *
        ((Real.sqrt n : ℂ) * ∫ s in (-1 : ℝ)..1, exp (n * h s) * g s * (1 + ε n s)) +
      (P.Qn H n : ℂ) * v * ∫ s in (-1 : ℝ)..1,
        (trigS P.r (n * w s) - ((P.r - 1).factorial : ℂ)⁻¹ *
          exp (I * Real.pi * ((P.r : ℂ) - 2) * (n * w s))) * P.G n (n * w s) := by
    intro n hn
    have hn1 : 1 ≤ n := hN.trans hn
    have hIcc : Set.uIcc (-1 : ℝ) 1 = Set.Icc (-1) 1 := Set.uIcc_of_le (by norm_num)
    have hL : IntervalIntegrable (fun s => exp (n * h s) * g s * (1 + ε n s)) volume (-1) 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [hIcc]
      exact (((continuousOn_const.mul hh_cont).cexp).mul hg_cont).mul
        (continuousOn_const.add (hε_cont n))
    have hR : IntervalIntegrable (fun s => (trigS P.r (n * w s) -
        ((P.r - 1).factorial : ℂ)⁻¹ * exp (I * Real.pi * ((P.r : ℂ) - 2) * (n * w s))) *
          P.G n (n * w s)) volume (-1) 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [hIcc]
      refine ContinuousOn.mul (Continuous.continuousOn ?_) (hG_cont n hn1)
      exact ((continuous_trigS P.r).comp (continuous_const.mul hw_cont)).sub
        (continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul (continuous_const.mul hw_cont))))
    have lhs : (P.Qn H n : ℂ) * (v * ∫ s in (-1 : ℝ)..1, trigS P.r (n * w s) * P.G n (n * w s)) =
        ∫ s in (-1 : ℝ)..1, (P.Qn H n : ℂ) * (v * (trigS P.r (n * w s) * P.G n (n * w s))) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [hseg n, lhs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hL.const_mul _).const_mul _) (hR.const_mul _)]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [hIcc] at hs
    exact hpt n hn s hs
  -- the subdominant modes
  obtain ⟨Mσ, hMσ⟩ : ∃ M, ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖P.Ghat (w s)‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn fun s hs =>
      ((continuousAt_Ghat (hw_good s hs)).comp hw_cont.continuousAt).continuousWithinAt
  have hsub : Tendsto (fun n : ℕ => (P.Qn H n : ℂ) * v * ∫ s in (-1 : ℝ)..1,
      (trigS P.r (n * w s) - ((P.r - 1).factorial : ℂ)⁻¹ *
        exp (I * Real.pi * ((P.r : ℂ) - 2) * (n * w s))) * P.G n (n * w s)) atTop (𝓝 0) := by
    have hκ : 0 < 2 * Real.pi * δ := by positivity
    set K : ℝ := ((P.r - 1).factorial : ℝ) * (‖v‖ * ((1 + |C|) * Mσ * 2)) with hK
    refine squeeze_zero_norm' ?_ (tendsto_sqrt_mul_exp_neg hκ K)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn1 : 1 ≤ n := hN.trans hn
    have hA := An_pos hP hn1
    have hbd : ∀ s ∈ Set.uIoc (-1 : ℝ) 1, ‖(trigS P.r (n * w s) - ((P.r - 1).factorial : ℂ)⁻¹ *
        exp (I * Real.pi * ((P.r : ℂ) - 2) * (n * w s))) * P.G n (n * w s)‖ ≤
          (1 + |C|) * Mσ * (P.An n * Real.exp (n * (H - 2 * Real.pi * δ))) := by
      intro s hs
      have hs' : s ∈ Set.Icc (-1 : ℝ) 1 := by
        have := Set.uIoc_subset_uIcc hs; rwa [Set.uIcc_of_le (by norm_num)] at this
      refine (norm_sub_integrand_le hP hn1 (hw_neg s hs').le
        (Ghat_ne_zero (hU _ (hw_mem s hs'))) (hE n hn _ (hw_mem s hs'))).trans ?_
      have h1 : (P.Fd (w s)).re ≤ H := by
        have := hdecay s hs'
        rw [sub_re, ← hws] at this
        nlinarith [mul_nonneg hb.le (sq_nonneg s)]
      have h2 := hw_im s hs'
      have h3 : (n : ℝ) * ((P.Fd (w s)).re + 2 * Real.pi * (w s).im) ≤
          n * (H - 2 * Real.pi * δ) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
        nlinarith [Real.pi_pos]
      calc (1 + |C|) * P.An n * Real.exp (n * ((P.Fd (w s)).re + 2 * Real.pi * (w s).im)) *
            ‖P.Ghat (w s)‖
          ≤ (1 + |C|) * P.An n * Real.exp (n * (H - 2 * Real.pi * δ)) * Mσ := by
            gcongr
            exact hMσ s hs'
        _ = _ := by ring
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Qn_nonneg hP H hn1)]
    calc P.Qn H n * ‖v‖ * ‖∫ s in (-1 : ℝ)..1, (trigS P.r (n * w s) -
          ((P.r - 1).factorial : ℂ)⁻¹ * exp (I * Real.pi * ((P.r : ℂ) - 2) * (n * w s))) *
            P.G n (n * w s)‖
        ≤ P.Qn H n * ‖v‖ * ((1 + |C|) * Mσ * (P.An n * Real.exp (n * (H - 2 * Real.pi * δ))) *
            |1 - (-1 : ℝ)|) :=
          mul_le_mul_of_nonneg_left hI (mul_nonneg (Qn_nonneg hP H hn1) (norm_nonneg _))
      _ = ‖v‖ * ((1 + |C|) * Mσ * 2) *
          (P.Qn H n * (P.An n * Real.exp (n * (H - 2 * Real.pi * δ)))) := by
          norm_num; ring
      _ = K * Real.sqrt n * Real.exp (-(2 * Real.pi * δ) * n) := by
          rw [Qn_mul hP H _ hn1, hK]; ring
  -- the dominant mode
  have hdom : Tendsto (fun n : ℕ => cexp (I * (n * α)) *
      ((Real.sqrt n : ℂ) * ∫ s in (-1 : ℝ)..1, exp (n * h s) * g s * (1 + ε n s)) -
        cexp (I * (n * α)) * B) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) *
        (∫ s in (-1 : ℝ)..1, exp (n * h s) * g s * (1 + ε n s)) - B) atTop (𝓝 0) := by
      have := hlap.sub_const B
      rwa [sub_self] at this
    refine squeeze_zero_norm (fun n => ?_) (by simpa using h1.norm)
    rw [← mul_sub, norm_mul, norm_cexp_I_mul, one_mul]
  have htot := hdom.add hsub
  rw [add_zero] at htot
  refine htot.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [hint_eq n hn]
  ring

end Params

end OddZeta
