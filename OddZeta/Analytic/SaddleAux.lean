import OddZeta.Analytic.Defs
import OddZeta.Analysis.CotSeries

/-!
# Auxiliary analytic facts for the saddle-point asymptotics

Regularity of the phase `f`, its derivatives, the amplitude `Ĝ` and `Gₙ` away from the branch
cuts; growth of `Ĝ`; bounds for `trigS` in the lower half-plane; a second-order Taylor bound for
functions of a real variable.
-/

namespace OddZeta

open Complex Filter Topology

/-! ### List sums -/

theorem hasDerivAt_list_sum {ι : Type*} (l : List ι) {F : ι → ℂ → ℂ} {F' : ι → ℂ} {z : ℂ}
    (h : ∀ i ∈ l, HasDerivAt (F i) (F' i) z) :
    HasDerivAt (fun u => (l.map fun i => F i u).sum) ((l.map F').sum) z := by
  induction l with
  | nil => simpa using hasDerivAt_const z (0 : ℂ)
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun i hi => h i (List.mem_cons_of_mem a hi))

theorem differentiableAt_list_sum {ι : Type*} (l : List ι) {F : ι → ℂ → ℂ} {z : ℂ}
    (h : ∀ i ∈ l, DifferentiableAt ℂ (F i) z) :
    DifferentiableAt ℂ (fun u => (l.map fun i => F i u).sum) z := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun i hi => h i (List.mem_cons_of_mem a hi))

namespace Params

variable (P : Params)

/-- The points where all the logarithms occurring in `f` and `Ĝ` are holomorphic. -/
def Good (z : ℂ) : Prop :=
  -z ∈ slitPlane ∧ (P.eta0 : ℂ) + z ∈ slitPlane ∧
    ∀ η ∈ P.zs ++ P.ps, (η : ℂ) + z ∈ slitPlane ∧ (P.eta0 : ℂ) - η + z ∈ slitPlane

variable {P}

theorem good_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : P.Good z := by
  refine ⟨?_, ?_, fun η _ => ⟨?_, ?_⟩⟩ <;> rw [mem_slitPlane_iff] <;> right <;> simpa using hz

theorem Valid.eta_bounds (hP : P.Valid) :
    ∀ η ∈ P.zs ++ P.ps, P.etaOne ≤ η ∧ P.etaOne + η < P.eta0 := by
  intro η hη
  have h1 := hP.zs_le_etaMin _ hP.etaOne_mem
  have h2 := hP.two_mul_lt _ hP.etaMin_mem
  rcases List.mem_append.1 hη with h | h
  · have := hP.etaOne_le η h
    have := hP.zs_le_etaMin η h
    omega
  · have := hP.etaMin_le η h
    have := hP.two_mul_lt η h
    omega

theorem good_of_real (hP : P.Valid) {x : ℝ} (hx0 : x < 0) (hx1 : -(P.etaOne : ℝ) < x) :
    P.Good x := by
  have hb := hP.eta_bounds
  have h1 : P.etaOne + P.etaOne < P.eta0 := (hb _ (List.mem_append_left _ hP.etaOne_mem)).2
  have h1' : (P.etaOne : ℝ) + P.etaOne < P.eta0 := by exact_mod_cast h1
  refine ⟨?_, ?_, fun η hη => ⟨?_, ?_⟩⟩ <;> rw [mem_slitPlane_iff] <;> left
  · simpa using hx0
  · simp only [add_re, natCast_re, ofReal_re]; linarith
  · have := (hb η hη).1
    have : (P.etaOne : ℝ) ≤ η := by exact_mod_cast this
    simp only [add_re, natCast_re, ofReal_re]; linarith
  · have := (hb η hη).2
    have : (P.etaOne : ℝ) + η < P.eta0 := by exact_mod_cast this
    simp only [add_re, sub_re, natCast_re, ofReal_re]; linarith

/-! ### Derivatives of the phase -/

private theorem hasDerivAt_mul_log {c z : ℂ} (hc : c + z ∈ slitPlane) :
    HasDerivAt (fun u => (c + u) * log (c + u)) (log (c + z) + 1) z := by
  have e1 : HasDerivAt (fun u => c + u) 1 z := (hasDerivAt_id' z).const_add c
  have e2 := e1.clog hc
  have hne : c + z ≠ 0 := slitPlane_ne_zero hc
  convert e1.mul e2 using 1
  field_simp

private theorem hasDerivAt_neg_mul_log {z : ℂ} (hz : -z ∈ slitPlane) :
    HasDerivAt (fun u => -u * log (-u)) (-(log (-z) + 1)) z := by
  have e1 : HasDerivAt (fun u : ℂ => -u) (-1) z := (hasDerivAt_id' z).neg
  have e2 := e1.clog hz
  have hne : z ≠ 0 := by
    intro h; rw [h, neg_zero] at hz; exact slitPlane_ne_zero hz rfl
  convert e1.mul e2 using 1
  field_simp
  ring

theorem hasDerivAt_f {z : ℂ} (hz : P.Good z) : HasDerivAt P.f (P.f' z) z := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hl := hasDerivAt_list_sum (P.zs ++ P.ps)
    (F := fun (η : ℕ) u =>
      ((η : ℂ) + u) * log (η + u) - ((P.eta0 : ℂ) - η + u) * log (P.eta0 - η + u))
    (F' := fun η : ℕ => log ((η : ℂ) + z) - log ((P.eta0 : ℂ) - η + z)) (z := z)
    (fun η hη => by
      have := (hasDerivAt_mul_log (h3 η hη).1).sub (hasDerivAt_mul_log (h3 η hη).2)
      convert this using 1
      ring)
  have := (((hasDerivAt_neg_mul_log h1).add (hasDerivAt_mul_log h2)).const_mul
    (P.r : ℂ)).add hl |>.add_const (P.kappa0 : ℂ)
  convert this using 1
  · rfl
  · simp only [Params.f']
    ring

theorem hasDerivAt_f' {z : ℂ} (hz : P.Good z) : HasDerivAt P.f' (P.f'' z) z := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hlog : ∀ c : ℂ, c + z ∈ slitPlane → HasDerivAt (fun u => log (c + u)) (c + z)⁻¹ z := by
    intro c hc
    have := ((hasDerivAt_id' z).const_add c).clog hc
    simpa [one_div] using this
  have hlogneg : HasDerivAt (fun u : ℂ => log (-u)) z⁻¹ z := by
    have := (hasDerivAt_neg' z).clog h1
    have hne : z ≠ 0 := by
      intro h; rw [h, neg_zero] at h1; exact slitPlane_ne_zero h1 rfl
    convert this using 1
    field_simp
  have hl := hasDerivAt_list_sum (P.zs ++ P.ps)
    (F := fun (η : ℕ) u => log ((η : ℂ) + u) - log ((P.eta0 : ℂ) - η + u))
    (F' := fun η : ℕ => ((η : ℂ) + z)⁻¹ - ((P.eta0 : ℂ) - η + z)⁻¹) (z := z)
    (fun η hη => (hlog _ (h3 η hη).1).sub (hlog _ (h3 η hη).2))
  have := (((hlog _ h2).sub hlogneg).const_mul (P.r : ℂ)).add hl
  convert this using 1
  · rfl
  · rfl

theorem differentiableAt_f'' {z : ℂ} (hz : P.Good z) : DifferentiableAt ℂ P.f'' z := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hinv : ∀ c : ℂ, c + z ∈ slitPlane → DifferentiableAt ℂ (fun u => (c + u)⁻¹) z :=
    fun c hc => ((differentiableAt_id.const_add c).inv (slitPlane_ne_zero hc))
  have hne : z ≠ 0 := by
    intro h; rw [h, neg_zero] at h1; exact slitPlane_ne_zero h1 rfl
  have hl := differentiableAt_list_sum (P.zs ++ P.ps)
    (F := fun (η : ℕ) u => ((η : ℂ) + u)⁻¹ - ((P.eta0 : ℂ) - η + u)⁻¹) (z := z)
    (fun η hη => (hinv _ (h3 η hη).1).sub (hinv _ (h3 η hη).2))
  have := (((hinv _ h2).sub (differentiableAt_id.inv hne)).const_mul (P.r : ℂ)).add hl
  exact this

theorem differentiableAt_Ghat {z : ℂ} (hz : P.Good z) : DifferentiableAt ℂ P.Ghat z := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hlog : ∀ c : ℂ, c + z ∈ slitPlane → DifferentiableAt ℂ (fun u => log (c + u)) z :=
    fun c hc => (differentiableAt_id.const_add c).clog hc
  have hl := differentiableAt_list_sum (P.zs ++ P.ps)
    (F := fun (η : ℕ) u =>
      (1 / 2 : ℂ) * log ((η : ℂ) + u) - (3 / 2 : ℂ) * log ((P.eta0 : ℂ) - η + u))
    (z := z)
    (fun η hη => ((hlog _ (h3 η hη).1).const_mul _).sub ((hlog _ (h3 η hη).2).const_mul _))
  have hneg : DifferentiableAt ℂ (fun u : ℂ => log (-u)) z := differentiableAt_id.neg.clog h1
  have := ((differentiableAt_id.const_mul (2 : ℂ)).const_add (P.eta0 : ℂ)).mul
    ((((hneg.const_mul (-(P.r / 2 : ℂ))).add ((hlog _ h2).const_mul (3 * P.r / 2 : ℂ))).add
      hl).cexp)
  exact this

theorem continuousAt_f {z : ℂ} (hz : P.Good z) : ContinuousAt P.f z :=
  (hasDerivAt_f hz).continuousAt

theorem continuousAt_Ghat {z : ℂ} (hz : P.Good z) : ContinuousAt P.Ghat z :=
  (differentiableAt_Ghat hz).continuousAt

/-- The lower half-plane. -/
def lowerHalf : Set ℂ := {z | z.im < 0}

theorem isOpen_lowerHalf : IsOpen lowerHalf :=
  isOpen_lt Complex.continuous_im continuous_const

theorem continuousOn_deriv_f'' : ContinuousOn (deriv P.f'') lowerHalf :=
  ((DifferentiableOn.deriv (fun _ hz => (differentiableAt_f'' (good_of_im_ne_zero
    (ne_of_lt hz))).differentiableWithinAt) isOpen_lowerHalf)).continuousOn

theorem continuousOn_deriv_Ghat : ContinuousOn (deriv P.Ghat) lowerHalf :=
  ((DifferentiableOn.deriv (fun _ hz => (differentiableAt_Ghat (good_of_im_ne_zero
    (ne_of_lt hz))).differentiableWithinAt) isOpen_lowerHalf)).continuousOn

/-! ### Continuity of `Gₙ` off the real axis -/

theorem continuousAt_G (n : ℕ) {t : ℂ} (ht : t.im ≠ 0) : ContinuousAt (P.G n) t := by
  have hs : ∀ w : ℂ, w.im ≠ 0 → ∀ m : ℕ, w ≠ -m := fun w hw m hm => hw (by simp [hm])
  have hG : ∀ c : ℂ, c.im = 0 → ContinuousAt (fun t => Gamma (t + c)) t := by
    intro c hc
    have h1 : (t + c).im ≠ 0 := by simpa [hc] using ht
    exact ContinuousAt.comp (g := Gamma) (f := fun t : ℂ => t + c)
      (differentiableAt_Gamma _ (hs _ h1)).continuousAt (continuousAt_id.add continuousAt_const)
  have hGne : ∀ c : ℂ, c.im = 0 → Gamma (t + c) ≠ 0 := by
    intro c hc
    have h1 : (t + c).im ≠ 0 := by simpa [hc] using ht
    exact Gamma_ne_zero (hs _ h1)
  have hneg : ContinuousAt (fun t : ℂ => Gamma (-t)) t := by
    have h1 : (-t).im ≠ 0 := by simpa using ht
    exact ContinuousAt.comp (g := Gamma) (f := fun t : ℂ => -t)
      (differentiableAt_Gamma _ (hs _ h1)).continuousAt continuousAt_id.neg
  have hl : ContinuousAt (fun t : ℂ => ((P.zs ++ P.ps).map fun η =>
      Gamma (t + hh η n) / Gamma (t + P.h0 n - hh η n + 1)).prod) t := by
    refine tendsto_list_prod (P.zs ++ P.ps) fun η _ => ?_
    have e1 := hG (hh η n : ℂ) (by simp)
    have e2 := hG ((P.h0 n : ℂ) - hh η n + 1) (by simp)
    have e3 := hGne ((P.h0 n : ℂ) - hh η n + 1) (by simp)
    simp only [← add_assoc, add_sub_assoc'] at e2 e3 ⊢
    exact e1.div e2 e3
  have h0 := hG (P.h0 n : ℂ) (by simp)
  unfold Params.G
  exact (((continuousAt_const.mul (continuousAt_const.add (continuousAt_const.mul
    continuousAt_id))).mul (hneg.pow _)).mul (h0.pow _)).mul hl

/-! ### Bounds for `Ĝ` and `Gₙ` -/

theorem Ghat_ne_zero {u : ℂ} (h : (P.eta0 : ℂ) + 2 * u ≠ 0) : P.Ghat u ≠ 0 :=
  mul_ne_zero h (exp_ne_zero _)

private theorem list_sum_re_le {ι : Type*} (l : List ι) (F : ι → ℂ) (K : ℝ)
    (h : ∀ i ∈ l, (F i).re ≤ K) : ((l.map F).sum).re ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, add_re, List.length_cons, Nat.cast_succ]
    have := h a List.mem_cons_self
    have := ih fun i hi => h i (List.mem_cons_of_mem a hi)
    linarith

private theorem mul_log_le {β Λ : ℝ} (hβ : 0 < β) {w : ℂ} (hw₁ : β ≤ ‖w‖)
    (hw₂ : |Real.log β| + ‖w‖ ≤ Λ) (c : ℝ) : c * Real.log ‖w‖ ≤ |c| * Λ := by
  have hw : 0 < ‖w‖ := hβ.trans_le hw₁
  have habs : |Real.log ‖w‖| ≤ |Real.log β| + ‖w‖ := by
    rcases le_or_gt 1 ‖w‖ with h | h
    · rw [abs_of_nonneg (Real.log_nonneg h)]
      have := Real.log_le_sub_one_of_pos hw
      have := abs_nonneg (Real.log β)
      linarith
    · have h1 : Real.log ‖w‖ < 0 := Real.log_neg hw h
      have h2 : Real.log β ≤ Real.log ‖w‖ := Real.log_le_log hβ hw₁
      rw [abs_of_neg h1, abs_of_neg (h2.trans_lt h1)]
      linarith
  calc c * Real.log ‖w‖ ≤ |c| * |Real.log ‖w‖| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |c| * Λ := mul_le_mul_of_nonneg_left (habs.trans hw₂) (abs_nonneg c)

/-- Growth of `Ĝ` at distance `≥ β` from the real axis. -/
theorem norm_Ghat_le (hP : P.Valid) {β : ℝ} (hβ : 0 < β) {u : ℂ} (hu : β ≤ |u.im|) :
    ‖P.Ghat u‖ ≤ Real.exp ((P.eta0 + 2 * ‖u‖) +
      (2 * P.r + 2 * (P.zs ++ P.ps).length) * (|Real.log β| + 2 * P.eta0 + ‖u‖)) := by
  set Λ := |Real.log β| + 2 * (P.eta0 : ℝ) + ‖u‖ with hΛ
  have hb := hP.eta_bounds
  have hη0 : (0 : ℝ) ≤ P.eta0 := Nat.cast_nonneg _
  have hβw : ∀ c : ℝ, β ≤ ‖(c : ℂ) + u‖ := fun c =>
    hu.trans ((by simp : |u.im| = |((c : ℂ) + u).im|) ▸ abs_im_le_norm _)
  have hup : ∀ c : ℝ, |c| ≤ 2 * P.eta0 → |Real.log β| + ‖(c : ℂ) + u‖ ≤ Λ := by
    intro c hc
    have := norm_add_le (c : ℂ) u
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    rw [hΛ]; linarith
  have key : ∀ c : ℝ, |c| ≤ 2 * P.eta0 → ∀ a : ℝ,
      a * Real.log ‖(c : ℂ) + u‖ ≤ |a| * Λ := fun c hc a =>
    mul_log_le hβ (hβw c) (hup c hc) a
  -- the terms of the exponent
  have e1 : (-(P.r / 2 : ℂ) * log (-u)).re ≤ (P.r / 2 : ℝ) * Λ := by
    have := key 0 (by simp) (-(P.r / 2 : ℝ))
    rw [abs_neg, abs_of_nonneg (by positivity)] at this
    simpa [mul_re, log_re, norm_neg] using this
  have e2 : ((3 * P.r / 2 : ℂ) * log (P.eta0 + u)).re ≤ (3 * P.r / 2 : ℝ) * Λ := by
    have := key (P.eta0 : ℝ) (by rw [abs_of_nonneg hη0]; linarith) (3 * P.r / 2 : ℝ)
    rw [abs_of_nonneg (by positivity)] at this
    simpa [mul_re, log_re] using this
  have e3 : (((P.zs ++ P.ps).map fun η : ℕ =>
      (1 / 2 : ℂ) * log (η + u) - (3 / 2 : ℂ) * log (P.eta0 - η + u)).sum).re ≤
      (P.zs ++ P.ps).length * (2 * Λ) := by
    refine list_sum_re_le _ _ _ fun η hη => ?_
    have hη1 : η < P.eta0 := by have := (hb η hη).2; omega
    have hη1' : (η : ℝ) < P.eta0 := by exact_mod_cast hη1
    have f1 := key (η : ℝ) (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; linarith) (1 / 2 : ℝ)
    have f2 := key ((P.eta0 : ℝ) - η) (by rw [abs_of_nonneg (by linarith)]; linarith)
      (-(3 / 2) : ℝ)
    rw [abs_of_nonneg (by norm_num)] at f1
    rw [abs_neg, abs_of_nonneg (by norm_num)] at f2
    have : ((1 / 2 : ℂ) * log (η + u) - (3 / 2 : ℂ) * log (P.eta0 - η + u)).re =
        (1 / 2 : ℝ) * Real.log ‖((η : ℝ) : ℂ) + u‖ +
          (-(3 / 2) : ℝ) * Real.log ‖(((P.eta0 : ℝ) - η : ℝ) : ℂ) + u‖ := by
      simp [mul_re, log_re]
      ring
    rw [this]
    linarith
  have hlen : (0 : ℝ) ≤ (P.zs ++ P.ps).length := Nat.cast_nonneg _
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  -- the prefactor
  have e0 : ‖(P.eta0 : ℂ) + 2 * u‖ ≤ Real.exp (P.eta0 + 2 * ‖u‖) := by
    have h1 := norm_add_le (P.eta0 : ℂ) (2 * u)
    rw [norm_mul, Complex.norm_natCast, Complex.norm_ofNat] at h1
    have h2 := Real.add_one_le_exp ((P.eta0 : ℝ) + 2 * ‖u‖)
    linarith
  unfold Params.Ghat
  rw [norm_mul, Complex.norm_exp, Real.exp_add]
  refine mul_le_mul e0 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (Real.exp_pos _).le
  simp only [add_re]
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  nlinarith

/-- `‖Gₙ(nu)‖ ≤ (1 + |C|) Aₙ e^{n Re f(u)} ‖Ĝ(u)‖` from the Stirling estimate at `u`. -/
theorem norm_G_le {n : ℕ} (hn : 1 ≤ n) {u : ℂ} {C : ℝ} (hA : 0 < P.An n)
    (hGh : P.Ghat u ≠ 0)
    (hE : ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n) :
    ‖P.G n (n * u)‖ ≤ (1 + |C|) * (P.An n * Real.exp (n * (P.f u).re) * ‖P.Ghat u‖) := by
  set X : ℂ := P.An n * exp (n * P.f u) * P.Ghat u with hX
  have hX0 : X ≠ 0 := mul_ne_zero (mul_ne_zero (by exact_mod_cast hA.ne') (exp_ne_zero _)) hGh
  have hXn : ‖X‖ = P.An n * Real.exp (n * (P.f u).re) * ‖P.Ghat u‖ := by
    rw [hX, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA,
      Complex.norm_exp]
    simp
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hCn : C / n ≤ |C| :=
    (div_le_div_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (div_le_self (abs_nonneg C) hn')
  have h1 : ‖P.G n (n * u) / X‖ ≤ 1 + |C| := by
    calc ‖P.G n (n * u) / X‖ = ‖(P.G n (n * u) / X - 1) + 1‖ := by ring_nf
      _ ≤ ‖P.G n (n * u) / X - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + |C| := by rw [norm_one]; linarith
  rw [← hXn]
  calc ‖P.G n (n * u)‖ = ‖P.G n (n * u) / X‖ * ‖X‖ := by
        rw [← norm_mul, div_mul_cancel₀ _ hX0]
    _ ≤ (1 + |C|) * ‖X‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

theorem re_I_mul_sub_two (r : ℕ) (u : ℂ) :
    (I * ((r : ℂ) - 2) * Real.pi * u).re = -((r - 2) * Real.pi * u.im) := by
  simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, sub_re, sub_im, natCast_re,
    natCast_im, re_ofNat, im_ofNat]
  ring

end Params

/-! ### Bounds for `trigS` in the lower half-plane -/

theorem norm_trigS_le {r : ℕ} (hr : 2 ≤ r) {t : ℂ} (ht : t.im ≤ 0) :
    ‖trigS r t‖ ≤ 2 * Real.exp ((r - 2) * Real.pi * (-t.im)) := by
  set X := ((r - 1).factorial : ℂ)⁻¹ * exp (I * Real.pi * ((r : ℂ) - 2) * t) with hX
  have h1 := norm_trigS_sub_le hr ht
  have h2 : ‖X‖ ≤ Real.exp ((r - 2) * Real.pi * (-t.im)) := by
    rw [hX, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_exp]
    have hf : (1 : ℝ) ≤ (r - 1).factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    have : (I * Real.pi * ((r : ℂ) - 2) * t).re = (r - 2) * Real.pi * (-t.im) := by
      simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, sub_re, sub_im, natCast_re,
        natCast_im, re_ofNat, im_ofNat]
      ring
    rw [this]
    calc ((r - 1).factorial : ℝ)⁻¹ * Real.exp ((r - 2) * Real.pi * (-t.im))
        ≤ 1 * Real.exp ((r - 2) * Real.pi * (-t.im)) := by
          gcongr; exact inv_le_one_of_one_le₀ hf
      _ = _ := one_mul _
  have h3 : Real.exp ((r - 4) * Real.pi * (-t.im)) ≤ Real.exp ((r - 2) * Real.pi * (-t.im)) := by
    apply Real.exp_le_exp.2
    have := Real.pi_pos
    nlinarith
  calc ‖trigS r t‖ = ‖(trigS r t - X) + X‖ := by ring_nf
    _ ≤ ‖trigS r t - X‖ + ‖X‖ := norm_add_le _ _
    _ ≤ 2 * Real.exp ((r - 2) * Real.pi * (-t.im)) := by linarith

theorem continuous_trigS (r : ℕ) : Continuous (trigS r) := by
  unfold trigS
  fun_prop

/-! ### Calculus of one real variable -/

/-- Second-order Taylor bound on `[-1, 1]`, by iterating the mean value inequality. -/
theorem norm_sub_taylor2_le {φ φ1 φ2 φ3 : ℝ → ℂ} {M : ℝ}
    (h0 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt φ (φ1 s) s)
    (h1 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt φ1 (φ2 s) s)
    (h2 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt φ2 (φ3 s) s)
    (h3 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ3 s‖ ≤ M) :
    ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ s - φ 0 - φ1 0 * s - φ2 0 * s ^ 2 / 2‖ ≤ M * |s| ^ 3 := by
  have h00 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have hM : 0 ≤ M := (norm_nonneg _).trans (h3 0 h00)
  have hsub : ∀ s ∈ Set.Icc (-1 : ℝ) 1, Set.uIcc 0 s ⊆ Set.Icc (-1 : ℝ) 1 :=
    fun s hs => Set.uIcc_subset_Icc h00 hs
  have habs : ∀ s t : ℝ, t ∈ Set.uIcc 0 s → |t| ≤ |s| := by
    intro s t ht
    rcases le_total 0 s with h | h
    · rw [Set.uIcc_of_le h] at ht; rw [abs_of_nonneg ht.1, abs_of_nonneg h]; exact ht.2
    · rw [Set.uIcc_of_ge h] at ht; rw [abs_of_nonpos ht.2, abs_of_nonpos h]; linarith [ht.1]
  have e1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t => by
    simpa using (hasDerivAt_id t).ofReal_comp
  have e2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 / 2) (t : ℂ) t := fun t => by
    convert ((e1 t).pow 2).div_const 2 using 1
    push_cast; ring
  -- step A
  have hA : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ2 s - φ2 0‖ ≤ M * |s| := by
    intro s hs
    have := (convex_uIcc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := φ2) (f' := φ3) (C := M)
      (fun t ht => (h2 t (hsub s hs ht)).hasDerivWithinAt)
      (fun t ht => h3 t (hsub s hs ht)) Set.left_mem_uIcc Set.right_mem_uIcc
    simpa [Real.norm_eq_abs] using this
  -- step B
  have hB : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ1 s - φ1 0 - φ2 0 * s‖ ≤ M * |s| ^ 2 := by
    intro s hs
    have := (convex_uIcc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t : ℝ => φ1 t - φ1 0 - φ2 0 * t) (f' := fun t => φ2 t - φ2 0) (C := M * |s|)
      (fun t ht => by
        have := ((h1 t (hsub s hs ht)).sub_const (φ1 0)).sub ((e1 t).const_mul (φ2 0))
        convert this.hasDerivWithinAt using 1
        ring)
      (fun t ht => (hA t (hsub s hs ht)).trans
        (mul_le_mul_of_nonneg_left (habs s t ht) hM)) Set.left_mem_uIcc Set.right_mem_uIcc
    simp only [ofReal_zero, mul_zero, sub_zero, sub_self, Real.norm_eq_abs] at this
    calc _ ≤ M * |s| * |s| := this
      _ = M * |s| ^ 2 := by ring
  -- step C
  intro s hs
  have := (convex_uIcc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => φ t - φ 0 - φ1 0 * t - φ2 0 * (t ^ 2 / 2))
    (f' := fun t => φ1 t - φ1 0 - φ2 0 * t) (C := M * |s| ^ 2)
    (fun t ht => by
      have := (((h0 t (hsub s hs ht)).sub_const (φ 0)).sub ((e1 t).const_mul (φ1 0))).sub
        ((e2 t).const_mul (φ2 0))
      convert this.hasDerivWithinAt using 1
      ring)
    (fun t ht => (hB t (hsub s hs ht)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) (habs s t ht) 2) hM))
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [ofReal_zero, mul_zero, sub_zero, sub_self, Real.norm_eq_abs, zero_pow two_ne_zero,
    zero_div] at this
  calc ‖φ s - φ 0 - φ1 0 * s - φ2 0 * s ^ 2 / 2‖
      = ‖φ s - φ 0 - φ1 0 * s - φ2 0 * (s ^ 2 / 2)‖ := by ring_nf
    _ ≤ M * |s| ^ 2 * |s| := this
    _ = M * |s| ^ 3 := by ring

/-- Lipschitz bound on `[-1, 1]` from a derivative bound. -/
theorem norm_sub_le_of_hasDerivAt {φ φ1 : ℝ → ℂ} {L : ℝ}
    (h0 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt φ (φ1 s) s)
    (h1 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ1 s‖ ≤ L) :
    ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ s - φ 0‖ ≤ L * |s| := by
  intro s hs
  have h00 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (h0 t ht).hasDerivWithinAt) h1 h00 hs
  simpa [Real.norm_eq_abs] using this

theorem tendsto_sqrt_mul_exp_neg {κ : ℝ} (hκ : 0 < κ) (K : ℝ) :
    Tendsto (fun n : ℕ => K * Real.sqrt n * Real.exp (-κ * n)) atTop (𝓝 0) := by
  have := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) κ hκ).comp
    tendsto_natCast_atTop_atTop).const_mul K
  rw [mul_zero] at this
  refine this.congr fun n => ?_
  simp only [Function.comp, Real.sqrt_eq_rpow, mul_assoc]

end OddZeta
