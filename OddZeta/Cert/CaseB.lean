import OddZeta.Cert.SaddleData

/-!
# The saddle-point certificate for case (B)

The seven checks of `cert_of_checks` for `dataB`, evaluated by the kernel.
-/

namespace OddZeta.Cert

theorem caseB_chkBasic : chkBasic caseB dataB = true := by decide +kernel

theorem caseB_chkSaddle : chkSaddle caseB dataB = true := by decide +kernel

theorem caseB_chkSigma : chkSigma caseB dataB = true := by decide +kernel

theorem caseB_chkRay : chkRay caseB dataB = true := by decide +kernel

theorem caseB_chkHor : chkHor caseB dataB = true := by decide +kernel

theorem caseB_chkVer : chkVer caseB dataB = true := by decide +kernel

theorem caseB_chkFd : chkFd caseB dataB = true := by decide +kernel

theorem caseB_cert :
    ∃ D : PathData, ∃ b c c₀ ε₀ : ℝ, caseB.PathCert D b c c₀ ε₀ ∧
      (caseB.Fd D.u).re < -1175 ∧ ∀ m : ℤ, (caseB.Fd D.u).im ≠ m * Real.pi := by
  obtain ⟨D, b, c, c₀, ε₀, h1, h2, h3⟩ := cert_of_checks caseB_valid caseB_chkBasic
    caseB_chkSaddle caseB_chkSigma caseB_chkRay caseB_chkHor caseB_chkVer
    caseB_chkFd
  refine ⟨D, b, c, c₀, ε₀, h1, ?_, h3⟩
  have e : ((dataB.H : ℚ) : ℝ) = -1175 := by simp [dataB]
  rwa [e] at h2

end OddZeta.Cert
