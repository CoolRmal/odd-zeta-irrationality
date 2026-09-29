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

namespace Fam

variable {r : ℕ}

/-- **Lemma 8.2** (structure): on the lower half plane `f = r g + e - i r π u`. -/
theorem f_eq (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    (fam r).f u = r * famG u + famE u - I * r * Real.pi * u := by
  sorry

theorem Fd_eq (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    (fam r).Fd u = r * famG u + famE u - 2 * Real.pi * I * u := by
  sorry

theorem f'_eq (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    (fam r).f' u = r * famG1 u + famE1 u - I * r * Real.pi := by
  sorry

theorem f''_eq (hr : 1 ≤ r) (u : ℂ) : (fam r).f'' u = r * famG2 u + famE2 u := by
  sorry

theorem f'''_eq (hr : 1 ≤ r) (u : ℂ) : (fam r).f''' u = r * famG3 u + famE3 u := by
  sorry

/-- On the real segment `(-45, 0)`: `Re Fd(x) = r Re g(x) + Re e(x)` (Lemma 8.2(c)). -/
theorem re_Fd_real (hr : 1 ≤ r) {x : ℝ} (hx : -45 < x) (hx' : x < 0) :
    ((fam r).Fd x).re = r * (famG x).re + (famE x).re := by
  sorry

end Fam

end OddZeta
