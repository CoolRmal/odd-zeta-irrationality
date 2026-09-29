import OddZeta.Cert.SaddleData

/-!
# The saddle-point certificate for case (A)

The seven checks of `cert_of_checks` for `dataA`, evaluated by the kernel.
-/

namespace OddZeta.Cert

theorem caseA_chkBasic : chkBasic caseA dataA = true := by decide +kernel

theorem caseA_chkSaddle : chkSaddle caseA dataA = true := by decide +kernel

theorem caseA_chkSigma : chkSigma caseA dataA = true := by decide +kernel

theorem caseA_chkRay : chkRay caseA dataA = true := by decide +kernel

theorem caseA_chkHor : chkHor caseA dataA = true := by decide +kernel

theorem caseA_chkVer : chkVer caseA dataA = true := by decide +kernel

theorem caseA_chkFd : chkFd caseA dataA = true := by decide +kernel

theorem caseA_cert :
    ∃ D : PathData, ∃ b c c₀ ε₀ : ℝ, caseA.PathCert D b c c₀ ε₀ ∧
      (caseA.Fd D.u).re < -939 ∧ ∀ m : ℤ, (caseA.Fd D.u).im ≠ m * Real.pi := by
  obtain ⟨D, b, c, c₀, ε₀, h1, h2, h3⟩ := cert_of_checks caseA_valid caseA_chkBasic
    caseA_chkSaddle caseA_chkSigma caseA_chkRay caseA_chkHor caseA_chkVer
    caseA_chkFd
  refine ⟨D, b, c, c₀, ε₀, h1, ?_, h3⟩
  have e : ((dataA.H : ℚ) : ℝ) = -939 := by simp [dataA]
  rwa [e] at h2

end OddZeta.Cert
