import OddZeta.Cert.ToolsAux1

/-!
# Analytic tools for the saddle-point certificates, part 2: existence of the saddle point and
the cubic Taylor bound

* `exists_zero_of_deriv`: a zero of a holomorphic function near an approximate zero
  (contraction mapping for the simplified Newton map `u ↦ u - g(u)/g'(z₀)`);
* `exists_saddle`: its specialisation to `g = f' + i(r-2)π`;
* `norm_taylor_two_le`, `Fd_taylor`, `re_Fd_sub_le`: the cubic Taylor bound for `Fd` at a
  saddle point, giving the condition `sigma_decay` of `PathCert`.
-/

namespace OddZeta.Cert

open Complex Metric Set

/-- **A zero near an approximate zero.** If `‖g(z₀)‖ ≤ ε`, `‖g'(z₀)‖ ≥ m > 0`, `‖g''‖ ≤ M` on the
closed disc of radius `ρ` around `z₀`, `Mρ ≤ m/2` and `ε ≤ mρ/2`, then `g` has a zero in this
disc. -/
theorem exists_zero_of_deriv {g g' g'' : ℂ → ℂ} {z₀ : ℂ} {ρ m ε M : ℝ}
    (hg : ∀ u ∈ closedBall z₀ ρ, HasDerivAt g (g' u) u)
    (hg' : ∀ u ∈ closedBall z₀ ρ, HasDerivAt g' (g'' u) u)
    (hm : 0 < m) (hm' : m ≤ ‖g' z₀‖) (hε : ‖g z₀‖ ≤ ε)
    (hM : ∀ u ∈ closedBall z₀ ρ, ‖g'' u‖ ≤ M) (hMρ : M * ρ ≤ m / 2) (hερ : ε ≤ m * ρ / 2) :
    ∃ u ∈ closedBall z₀ ρ, g u = 0 := by
  set c := g' z₀ with hc
  have hc0 : 0 < ‖c‖ := hm.trans_le hm'
  have hcne : c ≠ 0 := norm_pos_iff.1 hc0
  have hρ0 : 0 ≤ ρ := by
    have := (norm_nonneg _).trans hε
    nlinarith
  have hz₀ : z₀ ∈ closedBall z₀ ρ := mem_closedBall_self hρ0
  have hconv := convex_closedBall z₀ ρ
  -- `g'` is close to `c` on the disc
  have hg'c : ∀ u ∈ closedBall z₀ ρ, ‖g' u - c‖ ≤ m / 2 := by
    intro u hu
    have h1 := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun w hw => (hg' w hw).hasDerivWithinAt) hM hz₀ hu
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₀ hz₀)
    have h2 : ‖u - z₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact hu
    calc ‖g' u - c‖ ≤ M * ‖u - z₀‖ := h1
      _ ≤ M * ρ := by gcongr
      _ ≤ m / 2 := hMρ
  -- the simplified Newton map
  set Φ : ℂ → ℂ := fun u => u - g u / c with hΦ
  have hΦd : ∀ u ∈ closedBall z₀ ρ, HasDerivAt Φ (1 - g' u / c) u := fun u hu =>
    (hasDerivAt_id' u).sub ((hg u hu).div_const c)
  have hΦb : ∀ u ∈ closedBall z₀ ρ, ‖1 - g' u / c‖ ≤ 1 / 2 := by
    intro u hu
    have e : 1 - g' u / c = -(g' u - c) / c := by field_simp; ring
    rw [e, norm_div, norm_neg, div_le_iff₀ hc0]
    have := hg'c u hu
    nlinarith
  have hlip : LipschitzOnWith (1 / 2) Φ (closedBall z₀ ρ) := by
    refine hconv.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun w hw => (hΦd w hw).hasDerivWithinAt) fun w hw => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    simpa using hΦb w hw
  have hΦz : ‖Φ z₀ - z₀‖ ≤ ρ / 2 := by
    have e : Φ z₀ - z₀ = -(g z₀ / c) := by simp only [hΦ]; ring
    rw [e, norm_neg, norm_div, div_le_iff₀ hc0]
    nlinarith
  have hmaps : MapsTo Φ (closedBall z₀ ρ) (closedBall z₀ ρ) := by
    intro u hu
    have h1 := hlip.dist_le_mul u hu z₀ hz₀
    rw [mem_closedBall, dist_eq_norm] at hu ⊢
    rw [dist_eq_norm, dist_eq_norm] at h1
    have e : Φ u - z₀ = (Φ u - Φ z₀) + (Φ z₀ - z₀) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    push_cast at h1
    linarith
  have hcontr : ContractingWith (1 / 2) (hmaps.restrict Φ (closedBall z₀ ρ) (closedBall z₀ ρ)) :=
    ⟨by rw [← NNReal.coe_lt_coe]; norm_num, hmaps.lipschitzOnWith_iff_restrict.1 hlip⟩
  obtain ⟨y, hy, hfix, -⟩ := hcontr.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hz₀
    (edist_ne_top _ _)
  refine ⟨y, hy, ?_⟩
  have : g y / c = 0 := by
    have h := hfix.eq
    simp only [hΦ] at h
    linear_combination -h
  exact (div_eq_zero_iff.1 this).resolve_right hcne

variable {P : Params}

/-- **Existence of the saddle point (N1).** If `‖f''(ũ)‖ ≥ m > 0`, `‖f'(ũ) + i(r-2)π‖ ≤ ε`,
`‖f'''‖ ≤ M` on the closed disc of radius `ρ` around `ũ` (contained in `Ω`), `Mρ ≤ m/2` and
`ε ≤ mρ/2`, then there is a saddle point of `Fd` in this disc. -/
theorem exists_saddle {ut : ℂ} {ρ m ε M : ℝ} (hball : closedBall ut ρ ⊆ Omega P) (hm : 0 < m)
    (hm' : m ≤ ‖P.f'' ut‖) (hε : ‖P.f' ut + I * ((P.r : ℂ) - 2) * Real.pi‖ ≤ ε)
    (hM : ∀ u ∈ closedBall ut ρ, ‖P.f''' u‖ ≤ M) (hMρ : M * ρ ≤ m / 2) (hερ : ε ≤ m * ρ / 2) :
    ∃ u ∈ closedBall ut ρ, P.f' u + I * ((P.r : ℂ) - 2) * Real.pi = 0 :=
  exists_zero_of_deriv (g := fun u => P.f' u + I * ((P.r : ℂ) - 2) * Real.pi)
    (fun _ hu => (hasDerivAt_f' (hball hu)).add_const _)
    (fun _ hu => hasDerivAt_f'' (hball hu)) hm hm' hε hM hMρ hερ

/-! ### The cubic Taylor bound -/

theorem hasDerivAt_ofReal' (t : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
  simpa using (hasDerivAt_id t).ofReal_comp

/-- The path `t ↦ z + t v` has derivative `v`. -/
theorem hasDerivAt_line (z v : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => z + (t : ℂ) * v) v t := by
  simpa using ((hasDerivAt_ofReal' t).mul_const v).const_add z

/-- Second-order Taylor bound with a cubic remainder, for `t ∈ [0, 1]`. -/
theorem norm_taylor_two_le_of_nonneg {F g h k : ℂ → ℂ} {u v : ℂ} {M : ℝ}
    (hF : ∀ w ∈ closedBall u ‖v‖, HasDerivAt F (g w) w)
    (hg : ∀ w ∈ closedBall u ‖v‖, HasDerivAt g (h w) w)
    (hh : ∀ w ∈ closedBall u ‖v‖, HasDerivAt h (k w) w)
    (hk : ∀ w ∈ closedBall u ‖v‖, ‖k w‖ ≤ M) (hg0 : g u = 0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖F (u + s * v) - F u - h u * v ^ 2 * s ^ 2 / 2‖ ≤ M * ‖v‖ ^ 3 * s ^ 3 / 6 := by
  have hu : u ∈ closedBall u ‖v‖ := mem_closedBall_self (norm_nonneg _)
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, u + (t : ℂ) * v ∈ closedBall u ‖v‖ := by
    intro t ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  -- step 1: `‖h w - h u‖ ≤ M ‖w - u‖`
  have step1 : ∀ w ∈ closedBall u ‖v‖, ‖h w - h u‖ ≤ M * ‖w - u‖ := fun w hw =>
    (convex_closedBall u ‖v‖).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun w hw => (hh w hw).hasDerivWithinAt) hk hu hw
  -- step 2: `φ(t) = g(u + t v) - h(u) v t` satisfies `‖φ(t)‖ ≤ M ‖v‖² t² / 2`
  set φ : ℝ → ℂ := fun t => g (u + (t : ℂ) * v) - h u * v * t with hφ
  have hφd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ (h (u + (t : ℂ) * v) * v - h u * v) t := by
    intro t ht
    have h1 := (hg _ (hmem t ht)).comp t (hasDerivAt_line u v t)
    have h2 := (hasDerivAt_ofReal' t).const_mul (h u * v)
    convert h1.sub h2 using 1
    · rw [hφ]; rfl
    · ring
  have step2 : ∀ t ∈ Icc (0 : ℝ) 1, ‖φ t‖ ≤ M * ‖v‖ ^ 2 * t ^ 2 / 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f' := fun t => h (u + (t : ℂ) * v) * v - h u * v)
      (B' := fun t => M * ‖v‖ ^ 2 * t)
      (fun t ht => (hφd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hφd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) ?_ ?_ ?_
    · simp [hφ, hg0]
    · intro t
      convert ((hasDerivAt_pow 2 t).const_mul (M * ‖v‖ ^ 2)).div_const 2 using 1
      push_cast; ring
    · intro t ht
      have ht' := Ico_subset_Icc_self ht
      have e : h (u + (t : ℂ) * v) * v - h u * v = (h (u + (t : ℂ) * v) - h u) * v := by ring
      rw [e, norm_mul]
      have := step1 _ (hmem t ht')
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht.1] at this
      calc ‖h (u + ↑t * v) - h u‖ * ‖v‖ ≤ M * (t * ‖v‖) * ‖v‖ := by gcongr
        _ = M * ‖v‖ ^ 2 * t := by ring
  -- step 3: `ψ(t) = F(u + t v) - F(u) - h(u) v² t²/2`
  set ψ : ℝ → ℂ := fun t => F (u + (t : ℂ) * v) - F u - h u * v ^ 2 * (t : ℂ) ^ 2 / 2 with hψ
  have hψd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt ψ (v * φ t) t := by
    intro t ht
    have h1 := (hF _ (hmem t ht)).comp t (hasDerivAt_line u v t)
    have h2 := ((hasDerivAt_ofReal' t).fun_pow 2).const_mul (h u * v ^ 2) |>.div_const 2
    convert (h1.sub_const (F u)).sub h2 using 1
    · rw [hψ]; rfl
    · simp only [hφ]
      push_cast
      ring
  have step3 := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := ψ) (a := 0) (b := 1) (f' := fun t => v * φ t)
      (B := fun t => M * ‖v‖ ^ 3 * t ^ 3 / 6) (B' := fun t => M * ‖v‖ ^ 3 * t ^ 2 / 2)
      (fun t ht => (hψd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hψd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (by simp [hψ])
      (fun t => by
        convert ((hasDerivAt_pow 3 t).const_mul (M * ‖v‖ ^ 3)).div_const 6 using 1
        push_cast; ring)
      (fun t ht => by
        rw [norm_mul]
        have := step2 t (Ico_subset_Icc_self ht)
        calc ‖v‖ * ‖φ t‖ ≤ ‖v‖ * (M * ‖v‖ ^ 2 * t ^ 2 / 2) := by gcongr
          _ = M * ‖v‖ ^ 3 * t ^ 2 / 2 := by ring) hs
  simpa [hψ] using step3

/-- Second-order Taylor bound with a cubic remainder, for `s ∈ [-1, 1]`. -/
theorem norm_taylor_two_le {F g h k : ℂ → ℂ} {u v : ℂ} {M : ℝ}
    (hF : ∀ w ∈ closedBall u ‖v‖, HasDerivAt F (g w) w)
    (hg : ∀ w ∈ closedBall u ‖v‖, HasDerivAt g (h w) w)
    (hh : ∀ w ∈ closedBall u ‖v‖, HasDerivAt h (k w) w)
    (hk : ∀ w ∈ closedBall u ‖v‖, ‖k w‖ ≤ M) (hg0 : g u = 0) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    ‖F (u + s * v) - F u - h u * v ^ 2 * s ^ 2 / 2‖ ≤ M * ‖v‖ ^ 3 * |s| ^ 3 / 6 := by
  rcases le_total 0 s with h0 | h0
  · rw [abs_of_nonneg h0]
    exact norm_taylor_two_le_of_nonneg hF hg hh hk hg0 ⟨h0, hs.2⟩
  · have hv : ‖-v‖ = ‖v‖ := norm_neg v
    have := norm_taylor_two_le_of_nonneg (v := -v) (s := -s) (hv ▸ hF) (hv ▸ hg) (hv ▸ hh)
      (hv ▸ hk) hg0 ⟨by linarith, by linarith [hs.1]⟩
    rw [hv, show u + ((-s : ℝ) : ℂ) * -v = u + s * v by push_cast; ring,
      show h u * (-v) ^ 2 * ((-s : ℝ) : ℂ) ^ 2 / 2 = h u * v ^ 2 * (s : ℂ) ^ 2 / 2 by
        push_cast; ring] at this
    rw [abs_of_nonpos h0]
    exact this

/-- **Cubic Taylor bound for `Fd` at a saddle point.** -/
theorem Fd_taylor {u v : ℂ} {M : ℝ} (hball : closedBall u ‖v‖ ⊆ Omega P)
    (hsad : P.f' u + I * ((P.r : ℂ) - 2) * Real.pi = 0)
    (hM : ∀ w ∈ closedBall u ‖v‖, ‖P.f''' w‖ ≤ M) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    ‖P.Fd (u + s * v) - P.Fd u - P.f'' u * v ^ 2 * s ^ 2 / 2‖ ≤ M * ‖v‖ ^ 3 * |s| ^ 3 / 6 :=
  norm_taylor_two_le (g := fun w => P.f' w + I * ((P.r : ℂ) - 2) * Real.pi)
    (fun _ hw => hasDerivAt_Fd (hball hw))
    (fun _ hw => (hasDerivAt_f' (hball hw)).add_const _)
    (fun _ hw => hasDerivAt_f'' (hball hw)) hM hsad hs

/-- **Quadratic decay of `Re Fd` along `σ`** (the condition `sigma_decay` of `PathCert`, with
`b = Re a - M‖v‖³/6`, `a = -f''(u)v²/2`). -/
theorem re_Fd_sub_le {u v : ℂ} {M : ℝ} (hball : closedBall u ‖v‖ ⊆ Omega P)
    (hsad : P.f' u + I * ((P.r : ℂ) - 2) * Real.pi = 0)
    (hM : ∀ w ∈ closedBall u ‖v‖, ‖P.f''' w‖ ≤ M) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    (P.Fd (u + s * v) - P.Fd u).re ≤ -((-(P.f'' u) * v ^ 2 / 2).re - M * ‖v‖ ^ 3 / 6) * s ^ 2 := by
  have hT := Fd_taylor hball hsad hM hs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM u (mem_closedBall_self (norm_nonneg _)))
  set E := P.Fd (u + s * v) - P.Fd u - P.f'' u * v ^ 2 * s ^ 2 / 2 with hE
  have e : P.Fd (u + s * v) - P.Fd u = E + P.f'' u * v ^ 2 / 2 * ((s ^ 2 : ℝ) : ℂ) := by
    rw [hE]; push_cast; ring
  have hre : (P.f'' u * v ^ 2 / 2 * ((s ^ 2 : ℝ) : ℂ)).re = (P.f'' u * v ^ 2 / 2).re * s ^ 2 :=
    re_mul_ofReal _ _
  have hs3 : |s| ^ 3 ≤ s ^ 2 := by
    have h1 : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
    have h2 : |s| ^ 3 = |s| * s ^ 2 := by rw [pow_succ', sq_abs]
    rw [h2]
    exact mul_le_of_le_one_left (sq_nonneg _) h1
  have hEre : E.re ≤ M * ‖v‖ ^ 3 * s ^ 2 / 6 := by
    refine (re_le_norm E).trans (hT.trans ?_)
    have : 0 ≤ M * ‖v‖ ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left hs3 this
    linarith
  rw [e, add_re, hre]
  have e2 : (-(P.f'' u) * v ^ 2 / 2).re = -(P.f'' u * v ^ 2 / 2).re := by
    rw [← neg_re]; ring_nf
  rw [e2]
  nlinarith

end OddZeta.Cert
