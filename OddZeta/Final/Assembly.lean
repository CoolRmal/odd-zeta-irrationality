import Mathlib

/-!
# The irrationality criterion

The abstract final step of the proof (Section 5.3 of the note): if a sequence of linear forms
`Fₙ = ∑_{s ∈ S} A_{s,n} ζ(s) - A_{0,n}` has denominators `Δₙ` with `log Δₙ ≤ n (C₂ + o(1))`, and
`Fₙ = Kₙ (Im(e^{i n α} B) + o(1))` with `log Kₙ ~ n H`, `B ≠ 0`, `α ∉ π ℤ` and `C₂ + H < 0`, then
one of the numbers `ζ(s)`, `s ∈ S`, is irrational.
-/

namespace OddZeta

open Filter Topology Complex

/-- If `Im(e^{i n α} B) → 0` then `B = 0` or `α ∈ π ℤ`. -/
theorem eq_zero_or_mem_of_tendsto_im {α : ℝ} {B : ℂ}
    (h : Tendsto (fun n : ℕ => (cexp (I * (n * α)) * B).im) atTop (𝓝 0)) :
    B = 0 ∨ ∃ m : ℤ, α = m * Real.pi := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hB, hα⟩ := hcon
  have hsin : Real.sin α ≠ 0 := by
    intro hs
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hs
    exact hα m hm.symm
  set w : ℕ → ℂ := fun n => cexp (I * (n * α)) * B with hw
  have h' : Tendsto (fun n => (w n).im) atTop (𝓝 0) := h
  have hcos : (cexp (I * α)).re = Real.cos α := by
    rw [mul_comm]; exact Complex.exp_ofReal_mul_I_re α
  have hsin' : (cexp (I * α)).im = Real.sin α := by
    rw [mul_comm]; exact Complex.exp_ofReal_mul_I_im α
  have hstep : ∀ n, (w (n + 1)).im = Real.sin α * (w n).re + Real.cos α * (w n).im := by
    intro n
    have : w (n + 1) = cexp (I * α) * w n := by
      simp only [hw]
      rw [show cexp (I * α) * (cexp (I * (n * α)) * B) = cexp (I * α + I * (n * α)) * B by
        rw [Complex.exp_add]; ring]
      congr 2
      push_cast
      ring
    rw [this, mul_im, hcos, hsin']
    ring
  have h1 : Tendsto (fun n => (w (n + 1)).im) atTop (𝓝 0) :=
    h'.comp (tendsto_add_atTop_nat 1)
  have hre : Tendsto (fun n => (w n).re) atTop (𝓝 0) := by
    have h2 := h1.sub (h'.const_mul (Real.cos α))
    rw [mul_zero, sub_zero] at h2
    have h3 := h2.const_mul (Real.sin α)⁻¹
    rw [mul_zero] at h3
    refine h3.congr fun n => ?_
    rw [hstep]
    field_simp
    ring
  have hnorm : ∀ n, ‖w n‖ = ‖B‖ := by
    intro n
    simp only [hw, norm_mul, Complex.norm_exp]
    simp [Complex.mul_re]
  have hsq : Tendsto (fun n => (w n).re ^ 2 + (w n).im ^ 2) atTop (𝓝 0) := by
    have := (hre.pow 2).add (h'.pow 2)
    rwa [zero_pow two_ne_zero, add_zero] at this
  have hconst : ∀ n, (w n).re ^ 2 + (w n).im ^ 2 = ‖B‖ ^ 2 := by
    intro n
    rw [← hnorm n, Complex.sq_norm, Complex.normSq_apply]
    ring
  have : ‖B‖ ^ 2 = 0 := by
    have := hsq.congr hconst
    exact tendsto_nhds_unique tendsto_const_nhds this
  exact hB (by simpa using this)

/-- **The irrationality criterion.** -/
theorem exists_irrational_of_asymptotics {S : Finset ℕ} (F : ℕ → ℝ) (A : ℕ → ℕ → ℚ)
    (A₀ : ℕ → ℚ) (Δ : ℕ → ℚ) (ζ : ℕ → ℝ)
    (hLF : ∀ᶠ n in atTop, F n = ∑ s ∈ S, (A n s : ℝ) * ζ s - A₀ n)
    (hInt : ∀ᶠ n in atTop,
      0 < Δ n ∧ (∀ s ∈ S, ∃ z : ℤ, Δ n * A n s = z) ∧ ∃ z : ℤ, Δ n * A₀ n = z)
    (C₂ H : ℝ) (hC : C₂ + H < 0)
    (hΔ : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Real.log (Δ n) ≤ n * (C₂ + ε))
    (K : ℕ → ℝ) (hK : ∀ n, 0 < K n)
    (hKlog : Tendsto (fun n : ℕ => Real.log (K n) / n) atTop (𝓝 H))
    (B : ℂ) (hB : B ≠ 0) (α : ℝ) (hα : ∀ m : ℤ, α ≠ m * Real.pi)
    (hasymp : Tendsto (fun n : ℕ => F n / K n - (cexp (I * (n * α)) * B).im) atTop (𝓝 0)) :
    ∃ s ∈ S, Irrational (ζ s) := by
  by_contra hcon
  push Not at hcon
  -- all `ζ s` are rational; clear denominators
  have hrat : ∀ s ∈ S, ∃ q : ℚ, (q : ℝ) = ζ s := fun s hs => by
    have := hcon s hs
    unfold Irrational at this
    push Not at this
    simpa [eq_comm] using this
  choose! q hq using hrat
  set D : ℕ := ∏ s ∈ S, (q s).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun s _ => (q s).den_pos
  have hDq : ∀ s ∈ S, ∃ z : ℤ, (D : ℚ) * q s = z := by
    intro s hs
    obtain ⟨c, hc⟩ : (q s).den ∣ D := Finset.dvd_prod_of_mem _ hs
    refine ⟨c * (q s).num, ?_⟩
    rw [hc]
    push_cast
    rw [mul_comm ((q s).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
  -- the integers `Nₙ = D Δₙ Fₙ`
  have hN : ∀ᶠ n in atTop, ∃ z : ℤ, (D : ℝ) * Δ n * F n = z := by
    filter_upwards [hLF, hInt] with n hLFn ⟨_, hAs, hA0⟩
    obtain ⟨z0, hz0⟩ := hA0
    choose! zs hzs using hAs
    choose! ds hds using hDq
    refine ⟨∑ s ∈ S, zs s * ds s - D * z0, ?_⟩
    rw [hLFn]
    have : ∀ s ∈ S, (D : ℝ) * Δ n * ((A n s : ℝ) * ζ s) = (zs s * ds s : ℤ) := by
      intro s hs
      rw [← hq s hs]
      have h1 := congrArg (fun x : ℚ => (x : ℝ)) (hzs s hs)
      have h2 := congrArg (fun x : ℚ => (x : ℝ)) (hds s hs)
      push_cast at h1 h2 ⊢
      calc (D : ℝ) * Δ n * ((A n s : ℝ) * q s) = ((Δ n : ℝ) * A n s) * ((D : ℝ) * q s) := by ring
        _ = _ := by rw [h1, h2]
    rw [mul_sub, Finset.mul_sum, Finset.sum_congr rfl this]
    have h0 := congrArg (fun x : ℚ => (x : ℝ)) hz0
    push_cast at h0 ⊢
    rw [← h0]
    ring
  -- `D Δₙ Kₙ → 0`
  set ε := -(C₂ + H) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hsmall : Tendsto (fun n : ℕ => (D : ℝ) * Δ n * K n) atTop (𝓝 0) := by
    have hK' : ∀ᶠ n : ℕ in atTop, Real.log (K n) ≤ n * (H + ε) := by
      have : ∀ᶠ n : ℕ in atTop, Real.log (K n) / n < H + ε :=
        hKlog.eventually (gt_mem_nhds (by linarith))
      filter_upwards [this, eventually_gt_atTop 0] with n hn hn0
      have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
      rw [div_lt_iff₀ hn0'] at hn
      linarith
    have hlog : Tendsto (fun n : ℕ => Real.log D + n * (C₂ + H + 2 * ε)) atTop atBot := by
      have hneg : C₂ + H + 2 * ε < 0 := by rw [hε]; linarith
      exact tendsto_atBot_add_const_left _ _
        (tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hneg)
    have hbound : ∀ᶠ n : ℕ in atTop,
        Real.log ((D : ℝ) * Δ n * K n) ≤ Real.log D + n * (C₂ + H + 2 * ε) := by
      filter_upwards [hΔ ε hεpos, hK', hInt] with n h1 h2 ⟨hΔpos, _⟩
      have hΔ' : (0 : ℝ) < Δ n := by exact_mod_cast hΔpos
      rw [Real.log_mul (by positivity) (hK n).ne', Real.log_mul (by positivity) hΔ'.ne']
      nlinarith
    have hlog' : Tendsto (fun n : ℕ => Real.log ((D : ℝ) * Δ n * K n)) atTop atBot :=
      tendsto_atBot_mono' _ hbound hlog
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < (D : ℝ) * Δ n * K n := by
      filter_upwards [hInt] with n ⟨hΔpos, _⟩
      have hΔ' : (0 : ℝ) < Δ n := by exact_mod_cast hΔpos
      have : (0 : ℝ) < D := by exact_mod_cast hDpos
      exact mul_pos (mul_pos this hΔ') (hK n)
    have := (Real.tendsto_exp_atBot.comp hlog')
    refine this.congr' ?_
    filter_upwards [hpos] with n hn
    simp [Function.comp, Real.exp_log hn]
  -- hence `Fₙ = 0` eventually
  have hbdd : ∀ᶠ n : ℕ in atTop, |F n / K n| ≤ ‖B‖ + 1 := by
    have : ∀ᶠ n : ℕ in atTop, |F n / K n - (cexp (I * (n * α)) * B).im| < 1 :=
      (Metric.tendsto_nhds.mp hasymp) 1 one_pos |>.mono fun n hn => by simpa using hn
    filter_upwards [this] with n hn
    have him : |(cexp (I * (n * α)) * B).im| ≤ ‖B‖ := by
      calc |(cexp (I * (n * α)) * B).im| ≤ ‖cexp (I * (n * α)) * B‖ := Complex.abs_im_le_norm _
        _ = ‖B‖ := by
          rw [norm_mul, Complex.norm_exp]
          simp [Complex.mul_re]
    calc |F n / K n| = |(F n / K n - (cexp (I * (n * α)) * B).im) +
          (cexp (I * (n * α)) * B).im| := by ring_nf
      _ ≤ |F n / K n - (cexp (I * (n * α)) * B).im| + |(cexp (I * (n * α)) * B).im| :=
          abs_add_le _ _
      _ ≤ ‖B‖ + 1 := by linarith
  have hF0 : ∀ᶠ n : ℕ in atTop, F n = 0 := by
    have hlt : ∀ᶠ n : ℕ in atTop, (D : ℝ) * Δ n * K n * (‖B‖ + 1) < 1 := by
      have := hsmall.mul_const (‖B‖ + 1)
      rw [zero_mul] at this
      exact this.eventually (gt_mem_nhds one_pos)
    filter_upwards [hN, hlt, hbdd, hInt] with n ⟨z, hz⟩ hlt hbdd ⟨hΔpos, _⟩
    have hΔ' : (0 : ℝ) < Δ n := by exact_mod_cast hΔpos
    have hD' : (0 : ℝ) < D := by exact_mod_cast hDpos
    have habs : |(z : ℝ)| < 1 := by
      rw [← hz]
      have hFK : |F n| ≤ K n * (‖B‖ + 1) := by
        have := hbdd
        rw [abs_div, abs_of_pos (hK n), div_le_iff₀ (hK n)] at this
        linarith
      calc |(D : ℝ) * Δ n * F n| = D * Δ n * |F n| := by
            rw [abs_mul, abs_of_pos (mul_pos hD' hΔ')]
        _ ≤ D * Δ n * (K n * (‖B‖ + 1)) := by gcongr
        _ = D * Δ n * K n * (‖B‖ + 1) := by ring
        _ < 1 := hlt
    have hz0 : z = 0 := by
      have : |z| < 1 := by exact_mod_cast habs
      have := abs_lt.mp this
      omega
    rw [hz0, Int.cast_zero] at hz
    have := mul_eq_zero.mp hz
    rcases this with h | h
    · exact absurd h (mul_pos hD' hΔ').ne'
    · exact h
  -- contradiction with the oscillation of `Im(e^{inα} B)`
  have him : Tendsto (fun n : ℕ => (cexp (I * (n * α)) * B).im) atTop (𝓝 0) := by
    have := hasymp.neg
    rw [neg_zero] at this
    refine this.congr' ?_
    filter_upwards [hF0] with n hn
    simp [hn]
  rcases eq_zero_or_mem_of_tendsto_im him with h | ⟨m, hm⟩
  · exact hB h
  · exact hα m hm

end OddZeta
