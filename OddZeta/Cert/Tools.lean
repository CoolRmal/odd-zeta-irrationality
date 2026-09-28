import OddZeta.Cert.ToolsAux2
import OddZeta.Cert.ToolsAux3
import OddZeta.Cert.ToolsAux4

/-!
# Analytic tools for the numerical saddle-point certificates

This module collects generic (parameter-independent) analytic facts used to reduce the conditions
of `Params.PathCert` to finitely many rational inequalities and log/arctan enclosures:

* `ToolsAux1`: the domain `Omega P` (open; contains every non-real point and every point with
  `-η₁ < Re u < 0`), `hasDerivAt_f`, `hasDerivAt_f'`, `hasDerivAt_f''`, `hasDerivAt_Fd`, and the
  formulas `re_f'`, `im_f'`.
* `ToolsAux2`: `exists_saddle` (contraction mapping) and the cubic Taylor bound `Fd_taylor`,
  `re_Fd_sub_le` (the condition `sigma_decay`).
* `ToolsAux3`: `arg ⟨a, b⟩` via `arctan`, corner bounds `im_f'_le_box`, `le_im_f'_box` for
  `Im f'` on boxes, and the tail bound `im_f'_add_le_tail` / `ray_of_tail`.
* `ToolsAux4`: `Re f' = (1/2) log Q` and the box criterion `re_f'_pos_box`.
* this file: discs in `Ω`, bounds for `‖f'''‖`, `‖f'' w₁ - f'' w₂‖`, `‖Fd u* - Fd ũ‖`, norm
  helpers and interval chaining.
-/

namespace OddZeta.Cert

open Complex Metric Set

/-! ### Norm helpers -/

theorem le_norm_of_sq_le_normSq {z : ℂ} {t : ℝ} (h : t ^ 2 ≤ normSq z) : t ≤ ‖z‖ := by
  rw [normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg z]

theorem norm_le_of_normSq_le {z : ℂ} {t : ℝ} (ht : 0 ≤ t) (h : normSq z ≤ t ^ 2) : ‖z‖ ≤ t := by
  rw [normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg z]

/-- On the closed disc of radius `ρ` around `c`, `‖a + w‖ ≥ ‖a + c‖ - ρ`. -/
theorem norm_add_ge_of_mem_closedBall {a c w : ℂ} {ρ : ℝ} (hw : w ∈ closedBall c ρ) :
    ‖a + c‖ - ρ ≤ ‖a + w‖ := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have := norm_sub_norm_le (a + c) (a + w)
  rw [show a + c - (a + w) = -(w - c) by ring, norm_neg] at this
  linarith

theorem norm_list_sum_map_le {ι : Type*} (L : List ι) {g : ι → ℂ} {b : ι → ℝ}
    (h : ∀ i ∈ L, ‖g i‖ ≤ b i) : ‖(L.map g).sum‖ ≤ (L.map b).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (h a List.mem_cons_self)
      (ih fun i hi => h i (List.mem_cons_of_mem _ hi)))

theorem norm_inv_sq_le {z : ℂ} {t : ℝ} (ht : 0 < t) (h : t ≤ ‖z‖) : ‖(z ^ 2)⁻¹‖ ≤ 1 / t ^ 2 := by
  rw [norm_inv, norm_pow, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ht.le h 2)

/-! ### Discs in `Ω` -/

variable {P : Params}

/-- Closed discs in the open lower half-plane lie in `Ω`. -/
theorem closedBall_subset_Omega {c : ℂ} {R : ℝ} (h : c.im + R < 0) : closedBall c R ⊆ Omega P := by
  intro w hw
  apply mem_Omega_of_im_ne_zero
  rw [mem_closedBall, dist_eq_norm] at hw
  have h1 : |w.im - c.im| ≤ ‖w - c‖ := by rw [← sub_im]; exact abs_im_le_norm _
  have := (abs_le.1 (h1.trans hw)).2
  exact (show w.im < 0 by linarith).ne

/-! ### Bounds for `f'''`, `f''` and `Fd` -/

/-- A bound for `‖f'''(u)‖` from lower bounds for the distances of `u` to the singularities. -/
theorem norm_f'''_le {u : ℂ} {d₀ d : ℝ} {e e' : ℕ → ℝ} (hd₀ : 0 < d₀)
    (h₀ : d₀ ≤ ‖(P.eta0 : ℂ) + u‖) (hd : 0 < d) (h₁ : d ≤ ‖u‖)
    (he : ∀ η ∈ P.zs ++ P.ps, 0 < e η ∧ e η ≤ ‖(η : ℂ) + u‖ ∧
      0 < e' η ∧ e' η ≤ ‖(P.eta0 : ℂ) - η + u‖) :
    ‖P.f''' u‖ ≤ P.r * (1 / d₀ ^ 2 + 1 / d ^ 2) +
      ((P.zs ++ P.ps).map fun η : ℕ => 1 / e η ^ 2 + 1 / e' η ^ 2).sum := by
  unfold Params.f'''
  rw [norm_neg]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_natCast]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add (norm_inv_sq_le hd₀ h₀) (norm_inv_sq_le hd h₁))
  · refine norm_list_sum_map_le _ fun η hη => ?_
    obtain ⟨h1, h2, h3, h4⟩ := he η hη
    exact (norm_sub_le _ _).trans (add_le_add (norm_inv_sq_le h1 h2) (norm_inv_sq_le h3 h4))

/-- Lipschitz bound for `f''` on a disc in `Ω` on which `‖f'''‖ ≤ M`. -/
theorem norm_f''_sub_le {c w₁ w₂ : ℂ} {R M : ℝ} (hball : closedBall c R ⊆ Omega P)
    (hM : ∀ w ∈ closedBall c R, ‖P.f''' w‖ ≤ M) (h₁ : w₁ ∈ closedBall c R)
    (h₂ : w₂ ∈ closedBall c R) : ‖P.f'' w₁ - P.f'' w₂‖ ≤ M * ‖w₁ - w₂‖ :=
  (convex_closedBall c R).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun _ hw => (hasDerivAt_f'' (hball hw)).hasDerivWithinAt) hM h₂ h₁

/-- `Fd` at the saddle point `u*` versus `Fd` at a nearby point `ũ`: if `u*` lies in the closed
disc of radius `ρ` around `ũ` (contained in `Ω`) and `‖f''‖ ≤ M₂` there, then
`‖Fd(u*) - Fd(ũ)‖ ≤ 2 M₂ ρ²`. -/
theorem norm_Fd_sub_le {ut us : ℂ} {ρ M₂ : ℝ} (hball : closedBall ut ρ ⊆ Omega P)
    (hus : us ∈ closedBall ut ρ) (hsad : P.f' us + I * ((P.r : ℂ) - 2) * Real.pi = 0)
    (hM₂ : ∀ w ∈ closedBall ut ρ, ‖P.f'' w‖ ≤ M₂) :
    ‖P.Fd us - P.Fd ut‖ ≤ 2 * M₂ * ρ ^ 2 := by
  have hρ : 0 ≤ ρ := dist_nonneg.trans hus
  have hut : ut ∈ closedBall ut ρ := mem_closedBall_self hρ
  have hM0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ ut hut)
  have hconv := convex_closedBall ut ρ
  have hg : ∀ w ∈ closedBall ut ρ, ‖P.f' w + I * ((P.r : ℂ) - 2) * Real.pi‖ ≤ 2 * M₂ * ρ := by
    intro w hw
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun w => P.f' w + I * ((P.r : ℂ) - 2) * Real.pi)
      (fun w hw => ((hasDerivAt_f' (hball hw)).add_const _).hasDerivWithinAt) hM₂ hus hw
    simp only [hsad, sub_zero] at this
    refine this.trans ?_
    have h1 : ‖w - us‖ ≤ 2 * ρ := by
      rw [mem_closedBall, dist_eq_norm] at hw hus
      calc ‖w - us‖ = ‖(w - ut) - (us - ut)‖ := by ring_nf
        _ ≤ ‖w - ut‖ + ‖us - ut‖ := norm_sub_le _ _
        _ ≤ 2 * ρ := by linarith
    calc M₂ * ‖w - us‖ ≤ M₂ * (2 * ρ) := by gcongr
      _ = 2 * M₂ * ρ := by ring
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w hw => (hasDerivAt_Fd (hball hw)).hasDerivWithinAt) hg hut hus
  refine this.trans ?_
  have : ‖us - ut‖ ≤ ρ := by rw [← dist_eq_norm]; exact hus
  calc 2 * M₂ * ρ * ‖us - ut‖ ≤ 2 * M₂ * ρ * ρ := by gcongr
    _ = 2 * M₂ * ρ ^ 2 := by ring

/-! ### Chaining intervals -/

theorem forall_Icc_trans {p : ℝ → Prop} {a b c : ℝ} (h₁ : ∀ x ∈ Icc a b, p x)
    (h₂ : ∀ x ∈ Icc b c, p x) : ∀ x ∈ Icc a c, p x := by
  intro x hx
  rcases le_total x b with h | h
  · exact h₁ x ⟨hx.1, h⟩
  · exact h₂ x ⟨h, hx.2⟩

/-- `Steps q a [t₁, …, tₙ] b` means `q a t₁ ∧ q t₁ t₂ ∧ … ∧ q tₙ b`. -/
def Steps (q : ℝ → ℝ → Prop) : ℝ → List ℝ → ℝ → Prop
  | a, [], b => q a b
  | a, t :: l, b => q a t ∧ Steps q t l b

/-- A property holding on each of the consecutive intervals `[a, t₁], [t₁, t₂], …, [tₙ, b]`
holds on `[a, b]`. -/
theorem forall_Icc_of_steps {p : ℝ → Prop} {l : List ℝ} :
    ∀ {a b : ℝ}, Steps (fun s t => ∀ x ∈ Icc s t, p x) a l b → ∀ x ∈ Icc a b, p x := by
  induction l with
  | nil => intro a b h; exact h
  | cons t l ih => intro a b h; exact forall_Icc_trans h.1 (ih h.2)

end OddZeta.Cert
