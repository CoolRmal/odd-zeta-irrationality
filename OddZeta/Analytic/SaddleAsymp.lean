import OddZeta.Analytic.Saddle

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
  sorry

end Params

end OddZeta
