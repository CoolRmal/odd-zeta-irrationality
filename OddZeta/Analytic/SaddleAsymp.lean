import OddZeta.Analytic.Saddle
import OddZeta.Analytic.SaddleAux4

/-!
# Proposition 4.7: the asymptotics of `Fₙ`

From the deformed integral `Fₙ = (1/π) Im(n ∫_L S(nu) Gₙ(nu) du)` (`F_eq_im_pathInt`), Stirling's
formula on `L` (`G_asymp`), the Fourier expansion of `S` (dominant mode `k = r-2`), Laplace's method
on `σ` (`tendsto_sqrt_mul_integral_laplace`) and the monotonicity of `Re Fd` on `L \ σ`.
-/

namespace OddZeta

open Complex MeasureTheory Filter Topology

namespace Params

variable {P : Params}

/-- **Proposition 4.7**: the asymptotics of `Fₙ`. -/
theorem tendsto_F_div_Kn (hP : P.Valid) {D : PathData} {b c c₀ ε₀ : ℝ}
    (hD : P.PathCert D b c c₀ ε₀) :
    Tendsto (fun n : ℕ => P.F n / P.Kn (P.Fd D.u).re n -
        (cexp (I * (n * (P.Fd D.u).im)) *
          (D.v * P.Ghat D.u * (Real.pi / (-(P.f'' D.u) * D.v ^ 2 / 2)) ^ (1 / 2 : ℂ))).im)
      atTop (𝓝 0) := by
  obtain ⟨C, N₀, hE₀⟩ := G_asymp hP hD.c₀_pos hD.ε₀_pos hD.path_norm hD.path_arg hD.path_re
    hD.path_eta0
  have hN : 1 ≤ max N₀ 1 := le_max_right _ _
  have hE : ∀ n ≥ max N₀ 1, ∀ u ∈ D.pathSet,
      ‖P.G n (n * u) / (P.An n * exp (n * P.f u) * P.Ghat u) - 1‖ ≤ C / n :=
    fun n hn u hu => hE₀ n (le_of_max_le_left hn) u hu
  set H := (P.Fd D.u).re with hH
  set B : ℂ := D.v * P.Ghat D.u * (Real.pi / (-(P.f'' D.u) * D.v ^ 2 / 2)) ^ (1 / 2 : ℂ)
    with hB
  -- the four pieces of `L`
  have hsum := (((tendsto_ray hP hD hN hE).add (tendsto_sigma hP hD hN hE)).add
    (tendsto_horiz hP hD hN hE)).add (tendsto_vert hP hD hN hE)
  simp only [add_zero] at hsum
  have hmain : Tendsto (fun n : ℕ => (P.Qn H n : ℂ) *
      D.pathInt (fun u => trigS P.r (n * u) * P.G n (n * u)) -
        cexp (I * (n * (P.Fd D.u).im)) * B) atTop (𝓝 0) := by
    refine hsum.congr fun n => ?_
    simp only [PathData.pathInt]
    ring
  refine squeeze_zero_norm' ?_ (by simpa using hmain.norm)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [F_eq_im_pathInt hP hD hn]
  set J := D.pathInt (fun u => trigS P.r (n * u) * P.G n (n * u))
  have hA := An_pos hP hn
  have e : ((n : ℂ) * J).im / Real.pi / P.Kn H n =
      ((P.Qn H n : ℂ) * J).im := by
    rw [im_ofReal_mul, im_natCast_mul]
    unfold Kn Qn
    have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
    field_simp
    linear_combination (-J.im) * hs
  rw [e, ← sub_im, Real.norm_eq_abs]
  exact abs_im_le_norm _

end Params

end OddZeta
