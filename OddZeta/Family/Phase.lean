import OddZeta.Family.Defs
import OddZeta.Analytic.Saddle

/-!
# The structure of the phase function of the family (Section 8.1, Lemma 8.2 of the note)

For `η^(r)` the phase function of Section 4 decomposes, on the lower half plane, as
`f(u) = r g(u) + e(u) - i r π u`, hence `Fd(u) = f(u) + i(r-2)πu = r g(u) + e(u) - 2πi u`, with
the `r`-independent functions (principal logarithms)
* `g(u) = -u log u + (150+u) log(150+u) + Z(u) + ∑_{p ∈ {48,50,53,56,60}} Πₚ(u)`,
  `Z(u) = (45+u) log(45+u) - (105+u) log(105+u) - 90 log 45`,
  `Πₚ(u) = (p+u) log(p+u) - (150-p+u) log(150-p+u) + (150-2p) log(150-2p)`;
* `e(u) = Π₇₄(u)`.
We write `g(u) = ∑_b c_b (b+u) log(b+u) + κ_g` with the coefficient list `famCB` (formula (8.2)).
-/

namespace OddZeta

open Complex

/-- The coefficient list `(b, c_b)` of `g' = ∑ c_b log(b + u)` (formula (8.2)). -/
def famCB : List (ℕ × ℤ) :=
  [(0, -1), (150, 1), (45, 1), (105, -1), (48, 1), (102, -1), (50, 1), (100, -1), (53, 1), (97, -1),
    (56, 1), (94, -1), (60, 1), (90, -1)]

/-- The constant `κ_g = -90 log 45 + ∑ₚ (150-2p) log(150-2p)`. -/
noncomputable def famKg : ℝ :=
  -90 * Real.log 45 + 54 * Real.log 54 + 50 * Real.log 50 + 44 * Real.log 44 + 38 * Real.log 38 +
    30 * Real.log 30

/-- `g(u) = ∑_b c_b (b+u) log(b+u) + κ_g`. -/
noncomputable def famG (u : ℂ) : ℂ :=
  (famCB.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * ((bc.1 : ℂ) + u) * log ((bc.1 : ℂ) + u)).sum + famKg

/-- `g'(u) = ∑_b c_b log(b+u)`. -/
noncomputable def famG1 (u : ℂ) : ℂ :=
  (famCB.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * log ((bc.1 : ℂ) + u)).sum

/-- `g''(u) = ∑_b c_b / (b+u)`. -/
noncomputable def famG2 (u : ℂ) : ℂ :=
  (famCB.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * ((bc.1 : ℂ) + u)⁻¹).sum

/-- `g'''(u) = -∑_b c_b / (b+u)²`. -/
noncomputable def famG3 (u : ℂ) : ℂ :=
  -(famCB.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * (((bc.1 : ℂ) + u) ^ 2)⁻¹).sum

/-- `e(u) = (74+u) log(74+u) - (76+u) log(76+u) + 2 log 2`. -/
noncomputable def famE (u : ℂ) : ℂ :=
  (74 + u) * log (74 + u) - (76 + u) * log (76 + u) + 2 * Real.log 2

noncomputable def famE1 (u : ℂ) : ℂ := log (74 + u) - log (76 + u)

noncomputable def famE2 (u : ℂ) : ℂ := (74 + u)⁻¹ - (76 + u)⁻¹

noncomputable def famE3 (u : ℂ) : ℂ := -(((74 + u) ^ 2)⁻¹ - ((76 + u) ^ 2)⁻¹)

/-- `log (-u) = log u + π i` on the open lower half plane. -/
theorem log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) : log (-u) = log u + Real.pi * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hu]

namespace Fam

variable {r : ℕ}

/-- Sums over the directions of `η^(r)`. -/
theorem sum_map_zs_ps {M : Type*} [CommSemiring M] (φ : ℕ → M) :
    (((fam r).zs ++ (fam r).ps).map φ).sum =
      r * (φ 45 + φ 48 + φ 50 + φ 53 + φ 56 + φ 60) + φ 74 := by
  simp only [fam, List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
    nsmul_eq_mul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem kappa0_eq : (fam r).kappa0 = r * famKg + 2 * Real.log 2 := by
  simp only [Params.kappa0, fam, List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate, nsmul_eq_mul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [famKg, List.flatMap_replicate, List.flatten_replicate_singleton, List.map_replicate,
    List.sum_replicate]
  ring

/-- The structure identity, valid on all of `ℂ`. -/
theorem f_eq_aux (u : ℂ) :
    (fam r).f u = r * famG u + famE u - r * u * (log (-u) - log u) := by
  rw [Params.f, sum_map_zs_ps, kappa0_eq, r_eq]
  simp only [famG, famE, famCB, famKg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [fam]
  ring

theorem f'_eq_aux (u : ℂ) :
    (fam r).f' u = r * famG1 u + famE1 u - r * (log (-u) - log u) := by
  rw [Params.f', sum_map_zs_ps, r_eq]
  simp only [famG1, famE1, famCB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [fam]
  ring

/-- **Lemma 8.2** (structure): on the lower half plane `f = r g + e - i r π u`. -/
theorem f_eq (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    (fam r).f u = r * famG u + famE u - I * r * Real.pi * u := by
  rw [f_eq_aux, log_neg_of_im_neg hu]
  ring

theorem Fd_eq (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    (fam r).Fd u = r * famG u + famE u - 2 * Real.pi * I * u := by
  rw [Params.Fd, f_eq hr hu, r_eq]
  ring

theorem f'_eq (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    (fam r).f' u = r * famG1 u + famE1 u - I * r * Real.pi := by
  rw [f'_eq_aux, log_neg_of_im_neg hu]
  ring

theorem f''_eq (hr : 1 ≤ r) (u : ℂ) : (fam r).f'' u = r * famG2 u + famE2 u := by
  rw [Params.f'', sum_map_zs_ps, r_eq]
  simp only [famG2, famE2, famCB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [fam]
  ring

theorem f'''_eq (hr : 1 ≤ r) (u : ℂ) : (fam r).f''' u = r * famG3 u + famE3 u := by
  rw [Params.f''', sum_map_zs_ps, r_eq]
  simp only [famG3, famE3, famCB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [fam]
  ring

/-- On the real segment `(-45, 0)`: `Re Fd(x) = r Re g(x) + Re e(x)` (Lemma 8.2(c)). -/
theorem re_Fd_real (hr : 1 ≤ r) {x : ℝ} (hx : -45 < x) (hx' : x < 0) :
    ((fam r).Fd x).re = r * (famG x).re + (famE x).re := by
  rw [Params.Fd, f_eq_aux, r_eq]
  simp [Complex.log_re]

end Fam

end OddZeta
