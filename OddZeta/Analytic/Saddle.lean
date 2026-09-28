import OddZeta.Analytic.IntegralRep
import OddZeta.Analysis.Contour
import OddZeta.Analysis.Laplace

/-!
# The saddle-point asymptotics of `Fₙ` (Proposition 4.7 of the note, modified)

The path `L` (lower half-plane only) consists of
* the vertical ray `{bot.re + iy : y ≤ bot.im}`,
* the segment `σ = [bot, top]` through the saddle point `u* = D.u`, with `bot = u* - v`,
  `top = u* + v`,
* the horizontal segment from `top` to `x₁ + i·top.im`,
* the vertical segment from `x₁ + i·top.im` up to the real point `x₁`.

With `Fd(u) = f(u) + i(r-2)πu` (the phase of the dominant Fourier mode `k = r - 2`), the
conditions below say: `u*` is a saddle point, `Re Fd` has a strict quadratic maximum at `u*` along
`σ`, and `Re Fd` decreases monotonically along the three other pieces (going away from `σ`).
Then `Fₙ = Kₙ (Im(e^{inα} B) + o(1))` with `Kₙ = √n Aₙ e^{nH}/(π (r-1)!)`, `H = Re Fd(u*)`,
`α = Im Fd(u*)`, `B = v Ĝ(u*) (π/a)^{1/2}`, `a = -f''(u*) v²/2`.
-/

namespace OddZeta

open Complex MeasureTheory Filter Topology

/-- The data of the path `L`. -/
structure PathData where
  /-- the saddle point `u*` -/
  u : ℂ
  /-- the half-length vector of `σ` -/
  v : ℂ
  /-- the abscissa where `L` meets the real axis -/
  x1 : ℝ

namespace PathData

variable (D : PathData)

/-- `bot = u* - v`. -/
def bot : ℂ := D.u - D.v

/-- `top = u* + v`. -/
def top : ℂ := D.u + D.v

/-- The corner `x₁ + i·top.im`. -/
def corner : ℂ := D.x1 + D.top.im * I

/-- The integral of `g` along `L`, from `-i∞` to `x₁`. -/
noncomputable def pathInt (g : ℂ → ℂ) : ℂ :=
  (∫ y in Set.Iic D.bot.im, g (D.bot.re + y * I)) * I +
    segInt g D.bot D.top + segInt g D.top D.corner + segInt g D.corner D.x1

/-- The points of `L`. -/
def pathSet : Set ℂ :=
  {z | z.re = D.bot.re ∧ z.im ≤ D.bot.im} ∪ segment ℝ D.bot D.top ∪
    segment ℝ D.top D.corner ∪ segment ℝ D.corner (D.x1 : ℂ)

end PathData

namespace Params

variable (P : Params)

/-- The phase of the dominant mode: `Fd(u) = f(u) + i(r-2)πu`. -/
noncomputable def Fd (u : ℂ) : ℂ := P.f u + I * ((P.r : ℂ) - 2) * Real.pi * u

/-- The conditions on the path, to be certified numerically. -/
structure PathCert (D : PathData) (b c c₀ ε₀ : ℝ) : Prop where
  /-- `u*` is a saddle point of `Fd` -/
  saddle : P.f' D.u + I * ((P.r : ℂ) - 2) * Real.pi = 0
  /-- `Re a > 0` for `a = -f''(u*) v²/2` -/
  re_a_pos : 0 < (-(P.f'' D.u) * D.v ^ 2 / 2).re
  b_pos : 0 < b
  /-- quadratic decay of `Re Fd` along `σ` -/
  sigma_decay : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
    (P.Fd (D.u + s * D.v) - P.Fd D.u).re ≤ -b * s ^ 2
  c_pos : 0 < c
  /-- `Re Fd` increases with rate `≥ c` going up the ray -/
  ray : ∀ y ≤ D.bot.im, (P.f' (D.bot.re + y * I)).im + (P.r - 2) * Real.pi ≤ -c
  /-- `Re Fd` increases going right along the horizontal segment -/
  x1_lt : D.x1 < D.top.re
  horiz : ∀ x ∈ Set.Icc D.x1 D.top.re, 0 < (P.f' (x + D.top.im * I)).re
  /-- `Re Fd` decreases going up the vertical segment -/
  vert : ∀ y ∈ Set.Icc D.top.im 0, 0 < (P.f' (D.x1 + y * I)).im + (P.r - 2) * Real.pi
  /-- geometry -/
  x1_neg : D.x1 < 0
  x1_gt : -(P.etaOne : ℝ) < D.x1
  top_im_neg : D.top.im < 0
  bot_im_neg : D.bot.im < 0
  c₀_pos : 0 < c₀
  ε₀_pos : 0 < ε₀
  path_norm : ∀ z ∈ D.pathSet, c₀ ≤ ‖z‖
  path_arg : ∀ z ∈ D.pathSet, |(-z).arg| ≤ Real.pi - ε₀
  path_re : ∀ z ∈ D.pathSet, c₀ - P.etaOne ≤ z.re
  path_eta0 : ∀ z ∈ D.pathSet, c₀ ≤ ‖(P.eta0 : ℂ) + 2 * z‖

/-- The normalising factor `Kₙ = √n Aₙ e^{nH} / (π (r-1)!)`. -/
noncomputable def Kn (H : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt n * P.An n * Real.exp (n * H) / (Real.pi * (P.r - 1).factorial)

variable {P}

/-- **Deformation of the contour**: `Fₙ = (1/π) Im (n ∫_L S(nu) Gₙ(nu) du)`. -/
theorem F_eq_im_pathInt (hP : P.Valid) {D : PathData} {b c c₀ ε₀ : ℝ}
    (hD : P.PathCert D b c c₀ ε₀) {n : ℕ} (hn : 1 ≤ n) :
    P.F n = (n * D.pathInt fun u => trigS P.r (n * u) * P.G n (n * u)).im / Real.pi := by
  sorry

/-- The constant `B` is nonzero. -/
theorem B_ne_zero (hP : P.Valid) {D : PathData} {b c c₀ ε₀ : ℝ}
    (hD : P.PathCert D b c c₀ ε₀) :
    D.v * P.Ghat D.u * (Real.pi / (-(P.f'' D.u) * D.v ^ 2 / 2)) ^ (1 / 2 : ℂ) ≠ 0 := by
  sorry

/-- `Kₙ > 0` and `(1/n) log Kₙ → H`. -/
theorem Kn_pos (hP : P.Valid) (H : ℝ) (n : ℕ) (hn : 1 ≤ n) : 0 < P.Kn H n := by
  sorry

theorem tendsto_log_Kn (hP : P.Valid) (H : ℝ) :
    Tendsto (fun n : ℕ => Real.log (P.Kn H n) / n) atTop (𝓝 H) := by
  sorry

end Params

end OddZeta
