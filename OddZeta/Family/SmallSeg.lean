import OddZeta.Family.Num
import OddZeta.Cert.Machinery

/-!
# Segment checks for the per-`r` certificates of the family (`3 ≤ r ≤ 299`)

* `Phi r = r g + e - 2πi u` (`= Fd` of `η^(r)` on the lower half plane) and its derivatives, with
  the enclosure oracle `FPt r` (`phiEvOK`) and the box bound `F2Box r` (`phiBoxOK`);
* the **perturbed segment check** `chkSegP`: `Re Φ ≤ T` on the `ρ`-neighbourhood
  `{A + τ e + δ : τ ∈ [0, t_E], ‖δ‖ ≤ ρ}` of a rational segment (the variant of `chkSeg` of
  `Num.lean` whose second-order Taylor bounds also absorb a perturbation `δ`); it covers the
  segments `[P_R, bot]`, `[top, P_L]` whose endpoints `bot = u* - v`, `top = u* + v` are only known
  up to a small error;
* the **last piece** `lastOK` of the segment `[P_L, -2]`: a one-sided Taylor bound from a point
  `Q` up to the real end point `-2` (where `Φ` is not holomorphic), and the end point itself.
-/

namespace OddZeta.Small

open Complex Metric Set OddZeta.Cert OddZeta.Cert.QI OddZeta.FamNum

/-! ### The function `Φ_r = r g + e - 2πi u` -/

/-- `Φ_r(u) = r g(u) + e(u) - 2πi u`. -/
noncomputable def Phi (r : ℕ) (u : ℂ) : ℂ := r * famG u + famEs u

/-- `Φ_r'`. -/
noncomputable def Phi1 (r : ℕ) (u : ℂ) : ℂ := r * famG1 u + famEs1 u

/-- `Φ_r''`. -/
noncomputable def Phi2 (r : ℕ) (u : ℂ) : ℂ := r * famG2 u + famE2 u

/-- `Φ_r'''`. -/
noncomputable def Phi3 (r : ℕ) (u : ℂ) : ℂ := r * famG3 u + famE3 u

theorem add74_slit {z : ℂ} (hz : z ∈ slitPlane) : (74 : ℂ) + z ∈ slitPlane := by
  have := add_mem_slitPlane hz (a := 74) (by norm_num)
  simpa using this

theorem add76_slit {z : ℂ} (hz : z ∈ slitPlane) : (76 : ℂ) + z ∈ slitPlane := by
  have := add_mem_slitPlane hz (a := 76) (by norm_num)
  simpa using this

theorem hasDerivAt_Phi (r : ℕ) {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt (Phi r) (Phi1 r z) z :=
  ((hasDerivAt_famG hz).const_mul (r : ℂ)).add (hasDerivAt_famEs (add74_slit hz) (add76_slit hz))

theorem hasDerivAt_Phi1 (r : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (Phi1 r) (Phi2 r z) z :=
  ((hasDerivAt_famG1 hz).const_mul (r : ℂ)).add (hasDerivAt_famEs1 (add74_slit hz) (add76_slit hz))

theorem hasDerivAt_Phi2 (r : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (Phi2 r) (Phi3 r z) z :=
  ((hasDerivAt_famG2 hz).const_mul (r : ℂ)).add
    (hasDerivAt_famE2 (slitPlane_ne_zero (add74_slit hz)) (slitPlane_ne_zero (add76_slit hz)))

theorem phiEvOK (r p : ℕ) : EvOK (Phi r) (Phi1 r) (fun x y => FPt r x y p) :=
  fun x y => mem_FPt r x y p

theorem norm_Phi2_le_box (r : ℕ) {z : ℂ} {xl xh yl yh : ℚ} (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh)
    (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh)
    (hpos : ∀ bc ∈ famCB, 0 < lowN (bc.1 + xl) (bc.1 + xh) yl yh)
    (h4 : 0 < lowN (74 + xl) (74 + xh) yl yh) (h6 : 0 < lowN (76 + xl) (76 + xh) yl yh) :
    ‖Phi2 r z‖ ≤ F2Box r xl xh yl yh := by
  unfold Phi2
  refine (norm_add_le _ _).trans ?_
  simp only [F2Box, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
  rw [norm_mul, Complex.norm_natCast]
  exact add_le_add (mul_le_mul_of_nonneg_left (norm_famG2_le_box hx hy hpos) (Nat.cast_nonneg _))
    (norm_famE2_le_box hx hy h4 h6)

theorem phiBoxOK (r : ℕ) : BoxOK (Phi r) (Phi1 r) (Phi2 r) (F2Box r) okBox := by
  intro xl xh yl yh hok z h1 h2 h3 h4
  have hz := mem_slitPlane_of_okBox hok ⟨h1, h2⟩ ⟨h3, h4⟩
  refine ⟨hasDerivAt_Phi r hz, hasDerivAt_Phi1 r hz, norm_Phi2_le_box r ⟨h1, h2⟩ ⟨h3, h4⟩ ?_
    (lowN_pos_of_okBox hok (by norm_num)) (lowN_pos_of_okBox hok (by norm_num))⟩
  intro bc _
  exact lowN_pos_of_okBox hok (Nat.cast_nonneg _)

theorem Fd_eq_Phi {r : ℕ} (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) : (fam r).Fd u = Phi r u :=
  Fd_eq_famEs hr hu

theorem Fd'_eq_Phi1 {r : ℕ} (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    (fam r).f' u + I * (((fam r).r : ℂ) - 2) * Real.pi = Phi1 r u :=
  Fd'_eq_famEs1 hr hu

theorem f''_eq_Phi2 {r : ℕ} (hr : 1 ≤ r) (u : ℂ) : (fam r).f'' u = Phi2 r u := Fam.f''_eq hr u

theorem f'''_eq_Phi3 {r : ℕ} (hr : 1 ≤ r) (u : ℂ) : (fam r).f''' u = Phi3 r u := Fam.f'''_eq hr u

/-- At the real end point `-2`: `Re Fd(-2) = Re Φ(-2)`. -/
theorem re_Fd_neg_two {r : ℕ} (hr : 1 ≤ r) : ((fam r).Fd (-2 : ℂ)).re = (Phi r (-2 : ℂ)).re := by
  have h := Fam.re_Fd_real (r := r) hr (x := -2) (by norm_num) (by norm_num)
  push_cast at h
  rw [h, Phi, add_re, famEs_re, re_natCast_mul' r]
  simp

/-! ### A perturbed second-order Taylor bound -/

/-- `max |lo| |hi|`. -/
def absB (J : QI) : ℚ := max |J.lo| |J.hi|

theorem abs_le_absB {J : QI} {x : ℝ} (h : J.Mem x) : |x| ≤ (absB J : ℝ) := by
  simp only [absB, Rat.cast_max, Rat.cast_abs]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact (h.2.trans (le_abs_self _)).trans (le_max_right _ _)
  · rw [abs_of_nonpos hx]
    exact ((neg_le_neg h.1).trans (neg_le_abs _)).trans (le_max_left _ _)

theorem norm_le_absB {J K : QI} {z : ℂ} (h1 : J.Mem z.re) (h2 : K.Mem z.im) :
    ‖z‖ ≤ ((absB J + absB K : ℚ) : ℝ) := by
  push_cast
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add (abs_le_absB h1) (abs_le_absB h2))

/-- **Taylor bound with a perturbation**: from `u` to `u + σ e + δ`, `0 ≤ σ ≤ l`, `‖δ‖ ≤ ρ`. -/
theorem re_le_quad_pert {Φ Φ' Φ'' : ℂ → ℂ} {u e δ : ℂ} {B R D G l σ ρ E : ℝ} (hσ : 0 ≤ σ)
    (hσl : σ ≤ l) (hδ : ‖δ‖ ≤ ρ) (hE : ‖e‖ ≤ E) (hR : (Φ u).re ≤ R) (hD : (Φ' u * e).re ≤ D)
    (hG : ‖Φ' u‖ ≤ G)
    (h : ∀ z ∈ segment ℝ u (u + σ * e + δ),
      HasDerivAt Φ (Φ' z) z ∧ HasDerivAt Φ' (Φ'' z) z ∧ ‖Φ'' z‖ ≤ B) :
    (Φ (u + σ * e + δ)).re ≤
      R + max 0 (l * D + B * ‖e‖ ^ 2 / 2 * l ^ 2) + ρ * G + B * ρ * (l * E + ρ / 2) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (h u (left_mem_segment ℝ _ _)).2.2
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hδ
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have ht := re_le_taylor h
  rw [show u + σ * e + δ - u = (σ : ℂ) * e + δ by ring] at ht
  have e1 : (Φ' u * ((σ : ℂ) * e + δ)).re = σ * (Φ' u * e).re + (Φ' u * δ).re := by
    rw [mul_add, add_re, mul_left_comm, re_ofReal_mul]
  have e2 : (Φ' u * δ).re ≤ ρ * G := by
    refine (re_le_norm _).trans ?_
    rw [norm_mul, mul_comm ρ]
    exact mul_le_mul hG hδ (norm_nonneg _) hG0
  have e3 : ‖(σ : ℂ) * e + δ‖ ≤ σ * ‖e‖ + ρ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ]
    linarith
  have e4 : ‖(σ : ℂ) * e + δ‖ ^ 2 ≤ (σ * ‖e‖ + ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e3 2
  have hq := quad_le_max (D := D) (K := B * ‖e‖ ^ 2 / 2) hσ hσl (by positivity)
  have h3 : σ * (Φ' u * e).re ≤ σ * D := mul_le_mul_of_nonneg_left hD hσ
  have h4 : σ * ‖e‖ ≤ l * E := mul_le_mul hσl hE (norm_nonneg _) (hσ.trans hσl)
  have h5 : B * (σ * ‖e‖ + ρ) ^ 2 / 2 ≤
      B * ‖e‖ ^ 2 / 2 * σ ^ 2 + B * ρ * (l * E + ρ / 2) := by
    have h6 : B * ρ * (σ * ‖e‖) ≤ B * ρ * (l * E) := mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith
  have h7 : B * ‖(σ : ℂ) * e + δ‖ ^ 2 / 2 ≤ B * (σ * ‖e‖ + ρ) ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left e4 hB
    linarith
  rw [e1] at ht
  linarith

/-! ### The perturbed segment check -/

/-- One piece `[t, s]` of a grid on `A + [0, t_E] e`, with the perturbation radius `ρ`. -/
def pieceP (bnd : ℚ → ℚ → ℚ → ℚ → ℚ) (ok : ℚ → ℚ → ℚ → ℚ → Bool) (ax ay ex ey ρ T t : ℚ)
    (P : Pt) (s : ℚ) (Q : Pt) : Bool :=
  let xu := ax + t * ex
  let yu := ay + t * ey
  let xv := ax + s * ex
  let yv := ay + s * ey
  let xl := min xu xv - ρ
  let xh := max xu xv + ρ
  let yl := min yu yv - ρ
  let yh := max yu yv + ρ
  let h := s - t
  let B := bnd xl xh yl yh
  let K := B * (ex ^ 2 + ey ^ 2) / 2
  let W := B * ρ * (h / 2 * (|ex| + |ey|) + ρ / 2)
  ok xl xh yl yh && decide (0 < h ∧ 0 ≤ ρ ∧
    P.re.hi + max 0 (h / 2 * (dirI P ex ey).hi + K * (h / 2) ^ 2) +
      ρ * (absB P.dre + absB P.dim) + W ≤ T ∧
    Q.re.hi + max 0 (h / 2 * -(dirI Q ex ey).lo + K * (h / 2) ^ 2) +
      ρ * (absB Q.dre + absB Q.dim) + W ≤ T)

/-- The points of a segment `[u, u + σ e + δ]`. -/
theorem mem_segment_pert {u e δ z : ℂ} {σ : ℝ} (hz : z ∈ segment ℝ u (u + σ * e + δ)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ z = u + ((θ * σ : ℝ) : ℂ) * e + (θ : ℂ) * δ := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hz
  refine ⟨θ, h0, h1, ?_⟩
  simp only [Complex.real_smul]
  push_cast
  ring

variable {Φ Φ' Φ'' : ℂ → ℂ} {ev : ℚ → ℚ → Pt} {bnd : ℚ → ℚ → ℚ → ℚ → ℚ}
  {ok : ℚ → ℚ → ℚ → ℚ → Bool}

theorem pieceP_sound (hbox : BoxOK Φ Φ' Φ'' bnd ok) {ax ay ex ey ρ T t s : ℚ} {P Q : Pt}
    (hP : P.Mem (Φ (cq (ax + t * ex) (ay + t * ey))) (Φ' (cq (ax + t * ex) (ay + t * ey))))
    (hQ : Q.Mem (Φ (cq (ax + s * ex) (ay + s * ey))) (Φ' (cq (ax + s * ex) (ay + s * ey))))
    (h : pieceP bnd ok ax ay ex ey ρ T t P s Q = true) :
    ∀ τ : ℝ, (t : ℝ) ≤ τ → τ ≤ s → ∀ δ : ℂ, ‖δ‖ ≤ ρ →
      (Φ (cq ax ay + τ * cq ex ey + δ)).re ≤ T := by
  simp only [pieceP, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hh, hρ, hl, hr⟩ := h
  set A := cq ax ay
  set e := cq ex ey
  set B : ℚ := bnd (min (ax + t * ex) (ax + s * ex) - ρ) (max (ax + t * ex) (ax + s * ex) + ρ)
    (min (ay + t * ey) (ay + s * ey) - ρ) (max (ay + t * ey) (ay + s * ey) + ρ) with hB
  have hts : (t : ℝ) < s := by
    have : (0 : ℚ) < s - t := hh
    exact_mod_cast (show t < s by linarith)
  -- every point `A + τ' e + δ'` of the piece lies in the box
  have hin : ∀ τ' : ℝ, (t : ℝ) ≤ τ' → τ' ≤ s → ∀ δ' : ℂ, ‖δ'‖ ≤ ρ →
      ∀ z : ℂ, z = A + τ' * e + δ' →
        HasDerivAt Φ (Φ' z) z ∧ HasDerivAt Φ' (Φ'' z) z ∧ ‖Φ'' z‖ ≤ (B : ℝ) := by
    intro τ' h1 h2 δ' hδ' z hz
    have hre : z.re = ax + τ' * ex + δ'.re := by rw [hz]; simp [A, e]
    have him : z.im = ay + τ' * ey + δ'.im := by rw [hz]; simp [A, e]
    have k1 := (abs_le.1 ((abs_re_le_norm δ').trans hδ'))
    have k2 := (abs_le.1 ((abs_im_le_norm δ').trans hδ'))
    obtain ⟨x1, x2⟩ := between_of_le (a := (ax : ℝ)) (b := ex) h1 h2
    obtain ⟨y1, y2⟩ := between_of_le (a := (ay : ℝ)) (b := ey) h1 h2
    refine hbox _ _ _ _ hok z ?_ ?_ ?_ ?_
    · push_cast; rw [hre]; linarith [k1.1]
    · push_cast; rw [hre]; linarith [k1.2]
    · push_cast; rw [him]; linarith [k2.1]
    · push_cast; rw [him]; linarith [k2.2]
  have hnorm : ‖e‖ ^ 2 = ((ex ^ 2 + ey ^ 2 : ℚ) : ℝ) := by
    rw [← normSq_eq_norm_sq, normSq_apply]; simp [e]; ring
  have hE : ‖e‖ ≤ ((|ex| + |ey| : ℚ) : ℝ) := by
    push_cast
    simpa [e] using Complex.norm_le_abs_re_add_abs_im e
  intro τ h1 h2 δ hδ
  rcases le_total τ (((t : ℝ) + s) / 2) with hτ | hτ
  · -- left half: from `u = A + t e`
    have hu : cq (ax + t * ex) (ay + t * ey) = A + ((t : ℝ) : ℂ) * e := cq_line _ _ _ _ _
    have hw : A + (τ : ℂ) * e + δ = (A + ((t : ℝ) : ℂ) * e) + ((τ - t : ℝ) : ℂ) * e + δ := by
      push_cast; ring
    rw [hw]
    have hR : (Φ (A + ((t : ℝ) : ℂ) * e)).re ≤ (P.re.hi : ℝ) := by rw [← hu]; exact hP.1.2
    have hD : (Φ' (A + ((t : ℝ) : ℂ) * e) * e).re ≤ ((dirI P ex ey).hi : ℝ) := by
      rw [← hu]; exact (mem_dirI hP ex ey).2
    have hG : ‖Φ' (A + ((t : ℝ) : ℂ) * e)‖ ≤ ((absB P.dre + absB P.dim : ℚ) : ℝ) := by
      rw [← hu]; exact norm_le_absB hP.2.2.1 hP.2.2.2
    have k := re_le_quad_pert (Φ'' := Φ'') (B := (B : ℝ)) (l := ((s - t : ℚ) : ℝ) / 2)
      (sub_nonneg.2 h1) (by push_cast; linarith) hδ hE hR hD hG (by
        intro z hz
        obtain ⟨θ, θ0, θ1, rfl⟩ := mem_segment_pert hz
        refine hin (t + θ * (τ - t)) (by nlinarith) (by nlinarith) ((θ : ℂ) * δ) ?_ _ ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg θ0]
          nlinarith [norm_nonneg δ]
        · push_cast; ring)
    refine k.trans ?_
    have hl' := (Rat.cast_le (K := ℝ)).2 hl
    rw [hnorm]
    push_cast at hl' ⊢
    linarith
  · -- right half: from `v = A + s e`, direction `-e`
    have hv : cq (ax + s * ex) (ay + s * ey) = A + ((s : ℝ) : ℂ) * e := cq_line _ _ _ _ _
    have hw : A + (τ : ℂ) * e + δ = (A + ((s : ℝ) : ℂ) * e) + ((s - τ : ℝ) : ℂ) * (-e) + δ := by
      push_cast; ring
    rw [hw]
    have hR : (Φ (A + ((s : ℝ) : ℂ) * e)).re ≤ (Q.re.hi : ℝ) := by rw [← hv]; exact hQ.1.2
    have hD : (Φ' (A + ((s : ℝ) : ℂ) * e) * -e).re ≤ -((dirI Q ex ey).lo : ℝ) := by
      rw [mul_neg, neg_re, neg_le_neg_iff, ← hv]; exact (mem_dirI hQ ex ey).1
    have hG : ‖Φ' (A + ((s : ℝ) : ℂ) * e)‖ ≤ ((absB Q.dre + absB Q.dim : ℚ) : ℝ) := by
      rw [← hv]; exact norm_le_absB hQ.2.2.1 hQ.2.2.2
    have hE' : ‖-e‖ ≤ ((|ex| + |ey| : ℚ) : ℝ) := by rw [norm_neg]; exact hE
    have k := re_le_quad_pert (Φ'' := Φ'') (B := (B : ℝ)) (l := ((s - t : ℚ) : ℝ) / 2)
      (sub_nonneg.2 h2) (by push_cast; linarith) hδ hE' hR hD hG (by
        intro z hz
        obtain ⟨θ, θ0, θ1, rfl⟩ := mem_segment_pert hz
        refine hin (s - θ * (s - τ)) (by nlinarith) (by nlinarith) ((θ : ℂ) * δ) ?_ _ ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg θ0]
          nlinarith [norm_nonneg δ]
        · push_cast; ring)
    rw [norm_neg] at k
    refine k.trans ?_
    have hr' := (Rat.cast_le (K := ℝ)).2 hr
    rw [hnorm]
    push_cast at hr' ⊢
    linarith

/-- The grid `0 = t₀ < t < t₁ < ⋯ < t_E` of the segment, evaluated from the point `t`. -/
def segGoP (ev : ℚ → ℚ → Pt) (bnd : ℚ → ℚ → ℚ → ℚ → ℚ) (ok : ℚ → ℚ → ℚ → ℚ → Bool)
    (ax ay ex ey ρ T tE : ℚ) : ℚ → Pt → List ℚ → Bool
  | t, P, [] => pieceP bnd ok ax ay ex ey ρ T t P tE (ev (ax + tE * ex) (ay + tE * ey))
  | t, P, s :: l =>
    pieceP bnd ok ax ay ex ey ρ T t P s (ev (ax + s * ex) (ay + s * ey)) &&
      segGoP ev bnd ok ax ay ex ey ρ T tE s (ev (ax + s * ex) (ay + s * ey)) l

/-- **The perturbed segment check**: `Re Φ ≤ T` on `{A + τ e + δ : τ ∈ [0, t_E], ‖δ‖ ≤ ρ}`. -/
def chkSegP (ev : ℚ → ℚ → Pt) (bnd : ℚ → ℚ → ℚ → ℚ → ℚ) (ok : ℚ → ℚ → ℚ → ℚ → Bool)
    (ax ay ex ey ρ T tE : ℚ) (ts : List ℚ) : Bool :=
  segGoP ev bnd ok ax ay ex ey ρ T tE 0 (ev (ax + 0 * ex) (ay + 0 * ey)) ts

theorem segGoP_sound (hev : EvOK Φ Φ' ev) (hbox : BoxOK Φ Φ' Φ'' bnd ok)
    {ax ay ex ey ρ T tE : ℚ} :
    ∀ (l : List ℚ) (t : ℚ),
      segGoP ev bnd ok ax ay ex ey ρ T tE t (ev (ax + t * ex) (ay + t * ey)) l = true →
        ∀ τ : ℝ, (t : ℝ) ≤ τ → τ ≤ tE → ∀ δ : ℂ, ‖δ‖ ≤ ρ →
          (Φ (cq ax ay + τ * cq ex ey + δ)).re ≤ T
  | [], t, h => by
    intro τ h1 h2
    exact pieceP_sound hbox (hev _ _) (hev _ _) h τ h1 h2
  | s :: l, t, h => by
    intro τ h1 h2
    simp only [segGoP, Bool.and_eq_true] at h
    rcases le_total τ s with hτ | hτ
    · exact pieceP_sound hbox (hev _ _) (hev _ _) h.1 τ h1 hτ
    · exact segGoP_sound hev hbox l s h.2 τ hτ h2

theorem chkSegP_sound (hev : EvOK Φ Φ' ev) (hbox : BoxOK Φ Φ' Φ'' bnd ok)
    {ax ay ex ey ρ T tE : ℚ} {ts : List ℚ} (h : chkSegP ev bnd ok ax ay ex ey ρ T tE ts = true) :
    ∀ τ : ℝ, 0 ≤ τ → τ ≤ tE → ∀ δ : ℂ, ‖δ‖ ≤ ρ → (Φ (cq ax ay + τ * cq ex ey + δ)).re ≤ T := by
  intro τ h1 h2
  exact segGoP_sound hev hbox ts 0 h τ (by simpa using h1) h2

/-! ### The last piece `[Q, -2]` of the segment `[P_L, -2]` -/

/-- One-sided bound from `Q = qx + qy i` up to the real end point `-2`, and the end point. -/
def lastOK (r p : ℕ) (qx qy T : ℚ) : Bool :=
  let P := FPt r qx qy p
  let ex := -2 - qx
  let ey := -qy
  let xl := min qx (-2)
  let xh := max qx (-2)
  decide (qy < 0 ∧ qx < 0 ∧
    (∀ bc ∈ famCB, 0 < lowN (bc.1 + xl) (bc.1 + xh) qy 0) ∧
    0 < lowN (74 + xl) (74 + xh) qy 0 ∧ 0 < lowN (76 + xl) (76 + xh) qy 0 ∧
    P.re.hi + max 0 ((dirI P ex ey).hi + F2Box r xl xh qy 0 * (ex ^ 2 + ey ^ 2) / 2) ≤ T ∧
    (FPt r (-2) 0 p).re.hi ≤ T)

theorem lastOK_sound {r p : ℕ} {qx qy T : ℚ} (h : lastOK r p qx qy T = true) :
    (∀ σ : ℝ, 0 ≤ σ → σ < 1 → (Phi r (cq qx qy + σ * cq (-2 - qx) (-qy))).re ≤ T) ∧
      (Phi r (-2 : ℂ)).re ≤ T := by
  simp only [lastOK, decide_eq_true_eq] at h
  obtain ⟨hqy, hqx, hpos, h4, h6, hP, hend⟩ := h
  have hqy' : (qy : ℝ) < 0 := by exact_mod_cast hqy
  constructor
  · intro σ hσ0 hσ1
    set u := cq qx qy
    set e := cq (-2 - qx) (-qy)
    have hseg : ∀ z ∈ segment ℝ u (u + σ * e), HasDerivAt (Phi r) (Phi1 r z) z ∧
        HasDerivAt (Phi1 r) (Phi2 r z) z ∧
          ‖Phi2 r z‖ ≤ (F2Box r (min qx (-2)) (max qx (-2)) qy 0 : ℝ) := by
      intro z hz
      obtain ⟨θ, θ0, θ1, hz⟩ := mem_segment_pert (δ := 0) (by simpa using hz)
      simp only [mul_zero, add_zero] at hz
      have hre : z.re = qx + θ * σ * (-2 - qx) := by rw [hz]; simp [u, e]
      have him : z.im = qy + θ * σ * (-qy) := by rw [hz]; simp [u, e]
      have hθσ0 : 0 ≤ θ * σ := mul_nonneg θ0 hσ0
      have hθσ1 : θ * σ < 1 := by nlinarith
      have hzim : z.im < 0 := by rw [him]; nlinarith
      have hslit : z ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr hzim.ne)
      refine ⟨hasDerivAt_Phi r hslit, hasDerivAt_Phi1 r hslit, norm_Phi2_le_box r ?_ ?_ hpos h4 h6⟩
      · rw [hre]
        push_cast
        constructor
        · rcases le_total (qx : ℝ) (-2) with k | k
          · rw [min_eq_left k]; nlinarith
          · rw [min_eq_right k]; nlinarith
        · rcases le_total (qx : ℝ) (-2) with k | k
          · rw [max_eq_right k]; nlinarith
          · rw [max_eq_left k]; nlinarith
      · rw [him]
        push_cast
        constructor <;> nlinarith
    have k := re_le_quad (Φ := Phi r) (Φ' := Phi1 r) (Φ'' := Phi2 r) (u := u) (e := e) (l := 1)
      hσ0 hσ1.le (mem_FPt r qx qy p).1.2 (mem_dirI (mem_FPt r qx qy p) _ _).2 hseg
    have hnorm : ‖e‖ ^ 2 = (((-2 - qx) ^ 2 + (-qy) ^ 2 : ℚ) : ℝ) := by
      rw [← normSq_eq_norm_sq, normSq_apply]; simp [e]; ring
    rw [hnorm] at k
    simp only [one_mul, one_pow, mul_one] at k
    have hP' := (Rat.cast_le (K := ℝ)).2 hP
    push_cast at hP' k ⊢
    linarith
  · have k := (mem_FPt r (-2) 0 p).1.2
    have e : cq (-2) 0 = (-2 : ℂ) := by apply Complex.ext <;> simp
    rw [e] at k
    have hend' := (Rat.cast_le (K := ℝ)).2 hend
    exact k.trans hend'

end OddZeta.Small
