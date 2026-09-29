import OddZeta.Cert.SaddleNum

/-!
# The saddle-point certificate from finitely many kernel checks

`cert_of_checks` reduces the statement of `caseA_saddle_cert` / `caseB_saddle_cert` (for a general
valid parameter set `P`) to seven Boolean checks on a data record `SData` (a rational approximation
`ut` of the saddle point, the half-length vector `v` of `σ`, the abscissa `x₁`, and interval covers
of the three pieces of `L \ σ`). The checks are evaluated by the kernel (`decide +kernel`).
-/

namespace OddZeta.Cert

open Complex Metric Set QI

/-- The data of a saddle-point certificate. -/
structure SData where
  /-- `ut = ur + i ui` approximates the saddle point -/
  ur : ℚ
  ui : ℚ
  /-- `v = vr + i vi` -/
  vr : ℚ
  vi : ℚ
  x1 : ℚ
  /-- radius for the contraction argument -/
  rho : ℚ
  /-- tail threshold for the ray -/
  Y : ℚ
  /-- `‖v‖ ≤ V` -/
  V : ℚ
  /-- `m ≤ ‖f''(ut)‖` -/
  m : ℚ
  /-- `‖f'''‖ ≤ M3` on the closed disc of radius `V + ρ` around `ut` -/
  M3 : ℚ
  /-- the rate on the ray -/
  c : ℚ
  /-- the target bound `Re Fd(u*) < H` -/
  H : ℚ
  /-- `Im Fd(u*) ∈ (m0 π, (m0 + 1) π)` -/
  m0 : ℤ
  /-- precision of the log / arctan evaluations -/
  prec : ℕ
  /-- the ray is covered by `[-Y, t₁], [t₁, t₂], …, [tₙ, rayB]`, `rayL = [t₁, …, tₙ]` -/
  rayL : List ℚ
  rayB : ℚ
  /-- the horizontal segment is covered by `[x1, …, horB]` -/
  horL : List ℚ
  horB : ℚ
  /-- the vertical segment is covered by `[verA, …, 0]` -/
  verA : ℚ
  verL : List ℚ

namespace SData

variable (d : SData)

/-- `‖v‖²`. -/
def nsqv : ℚ := d.vr ^ 2 + d.vi ^ 2

end SData

/-! ### Chains of intervals -/

/-- `allSteps chk a [t₁, …, tₙ] b = chk a t₁ && chk t₁ t₂ && … && chk tₙ b`. -/
def allSteps (chk : ℚ → ℚ → Bool) : ℚ → List ℚ → ℚ → Bool
  | a, [], b => chk a b
  | a, t :: l, b => chk a t && allSteps chk t l b

theorem forall_of_allSteps {p : ℝ → Prop} {chk : ℚ → ℚ → Bool}
    (hchk : ∀ s t : ℚ, chk s t = true → ∀ x ∈ Icc (s : ℝ) t, p x) :
    ∀ {l : List ℚ} {a b : ℚ}, allSteps chk a l b = true → ∀ x ∈ Icc (a : ℝ) b, p x
  | [], a, b, h => hchk a b h
  | t :: l, a, b, h => by
    simp only [allSteps, Bool.and_eq_true] at h
    exact forall_Icc_trans (hchk a t h.1) (forall_of_allSteps hchk h.2)

/-! ### The checks -/

variable (P : Params) (d : SData)

/-- Rational side conditions (geometry of the path, covers, tail of the ray). -/
def chkBasic : Bool :=
  decide (0 < d.rho ∧ 0 ≤ d.V ∧ d.vr ^ 2 + d.vi ^ 2 ≤ d.V ^ 2 ∧ d.ui + (d.V + d.rho) < 0 ∧
    0 < d.c ∧ 0 < d.Y ∧ d.x1 ≤ -1 / 2 ∧ 1 / 2 - (P.etaOne : ℚ) ≤ d.x1 ∧
    1 / 2 ≤ (P.eta0 : ℚ) + 2 * d.x1 ∧ d.x1 < d.ur + d.vr - d.rho ∧ d.x1 ≤ d.ur - d.vr - d.rho ∧
    d.ui + d.vi + d.rho ≤ -1 / 2 ∧ d.ui - d.vi + d.rho ≤ -1 / 2 ∧
    d.ur - d.vr + d.rho + (d.ui - d.vi + d.rho) ≤ 0 ∧
    d.ur + d.vr + d.rho + (d.ui + d.vi + d.rho) ≤ 0 ∧ d.x1 + (d.ui + d.vi + d.rho) ≤ 0 ∧
    -2 * Num.piLo + P.r * (P.eta0 + 2 * max (-(d.ur - d.vr - d.rho)) (d.ur - d.vr + d.rho)) / d.Y
      ≤ -d.c ∧
    d.ui - d.vi + d.rho ≤ d.rayB ∧ d.ur + d.vr + d.rho ≤ d.horB ∧
    d.verA ≤ d.ui + d.vi - d.rho)

/-- The contraction argument (N1). -/
def chkSaddle : Bool :=
  decide (0 < d.m ∧ d.m ^ 2 ≤ (f''Q P d.ur d.ui).nsq ∧
    f'''Box P (d.ur - (d.V + d.rho)) (d.ur + (d.V + d.rho)) (d.ui - (d.V + d.rho))
      (d.ui + (d.V + d.rho)) ≤ d.M3 ∧
    d.M3 * d.rho ≤ d.m / 2 ∧
    (f'ReI P d.ur d.ui d.prec).sqB + (f'ImShI P d.ur d.ui d.prec).sqB ≤ (d.m * d.rho / 2) ^ 2)

/-- `Re (-f''(ut) v² / 2)`. -/
def aQ : ℚ :=
  -((f''Q P d.ur d.ui).re * (d.vr ^ 2 - d.vi ^ 2) - (f''Q P d.ur d.ui).im * (2 * d.vr * d.vi)) / 2

/-- The decay constant `b` of `σ`. -/
def bQ : ℚ := aQ P d - d.M3 * d.rho * (d.vr ^ 2 + d.vi ^ 2) / 2 - d.M3 * d.V ^ 3 / 6

/-- Quadratic decay along `σ` (N2). -/
def chkSigma : Bool := decide (0 < bQ P d)

/-- One box of the ray. -/
def rayBox (s t : ℚ) : Bool :=
  decide (t < 0 ∧ imUpperQ P (d.ur - d.vr - d.rho) (d.ur - d.vr + d.rho) s t d.prec +
    ((P.r : ℚ) - 2) * Num.piHi ≤ -d.c)

/-- One box of the horizontal segment. -/
def horBox (s t : ℚ) : Bool :=
  decide (-(P.etaOne : ℚ) < s) && reBoxQ P s t (d.ui + d.vi - d.rho) (d.ui + d.vi + d.rho)

/-- One box of the vertical segment. -/
def verBox (s t : ℚ) : Bool :=
  decide (t ≤ 0 ∧ 0 < imLowerQ P d.x1 d.x1 s t d.prec + ((P.r : ℚ) - 2) * Num.piLo)

/-- The ray (N5). -/
def chkRay : Bool := allSteps (rayBox P d) (-d.Y) d.rayL d.rayB

/-- The horizontal segment (N5). -/
def chkHor : Bool := allSteps (horBox P d) d.x1 d.horL d.horB

/-- The vertical segment (N5). -/
def chkVer : Bool := allSteps (verBox P d) d.verA d.verL 0

/-- A bound for `‖f''‖` on the disc of radius `ρ` around `ut`. -/
def M2Q : ℚ := (2 * P.r + 2 * (P.zs ++ P.ps).length) / (-(d.ui + d.rho))

/-- The perturbation bound `‖Fd u* - Fd ut‖ ≤ δ`. -/
def deltaQ : ℚ := 2 * M2Q P d * d.rho ^ 2

/-- `H` and `α` (N3, N4). -/
def chkFd : Bool :=
  decide ((FdReI P d.ur d.ui d.prec).hi + deltaQ P d < d.H ∧
    (d.m0 : ℚ) * Num.piLo < (FdImI P d.ur d.ui d.prec).lo - deltaQ P d ∧
    (d.m0 : ℚ) * Num.piHi < (FdImI P d.ur d.ui d.prec).lo - deltaQ P d ∧
    (FdImI P d.ur d.ui d.prec).hi + deltaQ P d < ((d.m0 : ℚ) + 1) * Num.piLo ∧
    (FdImI P d.ur d.ui d.prec).hi + deltaQ P d < ((d.m0 : ℚ) + 1) * Num.piHi)

variable {P d}

/-! ### Soundness of the box checks -/

theorem two_le_r (hP : P.Valid) : (2 : ℝ) ≤ P.r := by
  have := hP.three_le_r
  exact_mod_cast (by omega : 2 ≤ P.r)

theorem ray_box (hP : P.Valid) {x1 x2 s t c : ℚ} {p : ℕ} (hx1 : -(P.etaOne : ℝ) < x1)
    (ht : t < 0) (hchk : imUpperQ P x1 x2 s t p + ((P.r : ℚ) - 2) * Num.piHi ≤ -c) {x : ℝ}
    (hx : (x1 : ℝ) ≤ x ∧ x ≤ x2) :
    ∀ y ∈ Icc (s : ℝ) t, (P.f' (x + y * I)).im + ((P.r : ℝ) - 2) * Real.pi ≤ -c := by
  intro y hy
  have ht' : (t : ℝ) < 0 := by exact_mod_cast ht
  have h1 := (im_f'_le_box hP (u := x + y * I) hx1 (by simpa using hx) (by simpa using hy)
    ht'.le (Or.inl ht')).trans (le_imUpperQ (P := P) x1 x2 s t p)
  have h3 : ((imUpperQ P x1 x2 s t p + ((P.r : ℚ) - 2) * Num.piHi : ℚ) : ℝ) ≤ ((-c : ℚ) : ℝ) := by
    exact_mod_cast hchk
  push_cast at h3
  have h4 : ((P.r : ℝ) - 2) * Real.pi ≤ ((P.r : ℝ) - 2) * Num.piHi :=
    mul_le_mul_of_nonneg_left Num.pi_lt_piHi.le (by linarith [two_le_r hP])
  linarith

theorem ver_box (hP : P.Valid) {x1 s t : ℚ} {p : ℕ} (hx1 : -(P.etaOne : ℝ) < x1)
    (hx1n : x1 < 0) (ht : t ≤ 0)
    (hchk : 0 < imLowerQ P x1 x1 s t p + ((P.r : ℚ) - 2) * Num.piLo) :
    ∀ y ∈ Icc (s : ℝ) t, 0 < (P.f' ((x1 : ℝ) + y * I)).im + ((P.r : ℝ) - 2) * Real.pi := by
  intro y hy
  have ht' : (t : ℝ) ≤ 0 := by exact_mod_cast ht
  have hx1n' : (x1 : ℝ) < 0 := by exact_mod_cast hx1n
  have h1 := (imLowerQ_le (P := P) x1 x1 s t p).trans
    (le_im_f'_box hP (u := (x1 : ℝ) + y * I) hx1 (by simp) (by simpa using hy) ht' (Or.inr hx1n'))
  have h3 : ((0 : ℚ) : ℝ) < ((imLowerQ P x1 x1 s t p + ((P.r : ℚ) - 2) * Num.piLo : ℚ) : ℝ) := by
    exact_mod_cast hchk
  push_cast at h3
  have h4 : ((P.r : ℝ) - 2) * Num.piLo ≤ ((P.r : ℝ) - 2) * Real.pi :=
    mul_le_mul_of_nonneg_left Num.piLo_lt_pi.le (by linarith [two_le_r hP])
  linarith

theorem hor_box (hP : P.Valid) {s t y1 y2 : ℚ} (hs : -(P.etaOne : ℚ) < s) (hy2 : y2 < 0)
    (hchk : reBoxQ P s t y1 y2 = true) {y : ℝ} (hy : (y1 : ℝ) ≤ y ∧ y ≤ y2) :
    ∀ x ∈ Icc (s : ℝ) t, 0 < (P.f' (x + y * I)).re := by
  intro x hx
  exact re_f'_pos_box hP (by exact_mod_cast hs) (by simpa using hx) (by simpa using hy)
    (by exact_mod_cast hy2) (reBoxQ_spec hchk)

/-! ### Geometry of the path -/

theorem re_im_bounds_of_mem_closedBall {w : ℂ} {x y : ℚ} {R : ℝ} (hw : w ∈ closedBall (cq x y) R) :
    (x : ℝ) - R ≤ w.re ∧ w.re ≤ x + R ∧ (y : ℝ) - R ≤ w.im ∧ w.im ≤ y + R := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have h1 := (abs_re_le_norm (w - cq x y)).trans hw
  have h2 := (abs_im_le_norm (w - cq x y)).trans hw
  simp only [sub_re, sub_im, cq_re, cq_im] at h1 h2
  rw [abs_le] at h1 h2
  exact ⟨by linarith [h1.1], by linarith [h1.2], by linarith [h2.1], by linarith [h2.2]⟩

theorem lin_of_mem_segment {a b z : ℂ} (hz : z ∈ segment ℝ a b) {α β γ : ℝ}
    (ha : α * a.re + β * a.im ≤ γ) (hb : α * b.re + β * b.im ≤ γ) :
    α * z.re + β * z.im ≤ γ := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul]
  have e : s * γ + t * γ = γ := by rw [← add_mul, hst, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left ha hs, mul_le_mul_of_nonneg_left hb ht]

theorem abs_arg_neg_le {z : ℂ} (_h1 : z.im ≤ 0) (h2 : z.re + z.im ≤ 0) :
    |(-z).arg| ≤ Real.pi - 1 / 2 := by
  have hpi := Real.pi_gt_three
  rcases le_or_gt z.re 0 with h | h
  · have := Complex.abs_arg_le_pi_div_two_iff.2 (by simp; linarith : 0 ≤ (-z).re)
    linarith
  · have him : 0 < (-z).im := by simp; linarith
    have h0 : 0 ≤ (-z).arg := Complex.arg_nonneg_iff.2 him.le
    rw [abs_of_nonneg h0, arg_eq_mk, arg_mk_of_im_pos _ him]
    have h3 : -1 ≤ (-z).re / (-z).im := by
      rw [le_div_iff₀ him]; simp; linarith
    have h4 := Real.arctan_strictMono.monotone h3
    rw [Real.arctan_neg, Real.arctan_one] at h4
    linarith

/-- The four geometric conditions of `PathCert` (with `c₀ = ε₀ = 1/2`) at a point `z`. -/
theorem path_props {z : ℂ} {x1 : ℝ} (hre : x1 ≤ z.re) (him : z.im ≤ 0) (hsum : z.re + z.im ≤ 0)
    (hn : z.im ≤ -1 / 2 ∨ z.re ≤ -1 / 2) (hx1 : 1 / 2 - P.etaOne ≤ x1)
    (hx1' : 1 / 2 ≤ P.eta0 + 2 * x1) :
    1 / 2 ≤ ‖z‖ ∧ |(-z).arg| ≤ Real.pi - 1 / 2 ∧ 1 / 2 - P.etaOne ≤ z.re ∧
      1 / 2 ≤ ‖(P.eta0 : ℂ) + 2 * z‖ := by
  refine ⟨?_, abs_arg_neg_le him hsum, by linarith, ?_⟩
  · rcases hn with h | h
    · have := abs_im_le_norm z
      rw [abs_of_nonpos him] at this
      linarith
    · have := abs_re_le_norm z
      rw [abs_of_nonpos (by linarith)] at this
      linarith
  · refine le_trans ?_ (re_le_norm _)
    simp only [add_re, natCast_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith

/-! ### Small real lemmas -/

theorem mul_pi_lt {k : ℤ} {X : ℝ} (h1 : (k : ℝ) * Num.piLo < X) (h2 : (k : ℝ) * Num.piHi < X) :
    (k : ℝ) * Real.pi < X := by
  rcases le_total 0 (k : ℝ) with hk | hk
  · exact (mul_le_mul_of_nonneg_left Num.pi_lt_piHi.le hk).trans_lt h2
  · exact (mul_le_mul_of_nonpos_left Num.piLo_lt_pi.le hk).trans_lt h1

theorem lt_mul_pi {k : ℝ} {X : ℝ} (h1 : X < k * Num.piLo) (h2 : X < k * Num.piHi) :
    X < k * Real.pi := by
  rcases le_total 0 k with hk | hk
  · exact h1.trans_le (mul_le_mul_of_nonneg_left Num.piLo_lt_pi.le hk)
  · exact h2.trans_le (mul_le_mul_of_nonpos_left Num.pi_lt_piHi.le hk)

theorem re_neg_f''_mul (F : QC) (vr vi : ℚ) :
    (-F.toC * cq vr vi ^ 2 / 2).re =
      ((-(F.re * (vr ^ 2 - vi ^ 2) - F.im * (2 * vr * vi)) / 2 : ℚ) : ℝ) := by
  simp [QC.toC, cq, sq, mul_re, mul_im]
  ring

/-! ### The main theorem -/

set_option maxHeartbeats 400000 in
-- The proof elaborates the whole certificate in one (large) local context.
/-- **The saddle-point certificate from the kernel checks.** -/
theorem cert_of_checks (hP : P.Valid) (h1 : chkBasic P d = true) (h2 : chkSaddle P d = true)
    (h3 : chkSigma P d = true) (h4 : chkRay P d = true) (h5 : chkHor P d = true)
    (h6 : chkVer P d = true) (h7 : chkFd P d = true) :
    ∃ D : PathData, ∃ b c c₀ ε₀ : ℝ, P.PathCert D b c c₀ ε₀ ∧
      (P.Fd D.u).re < d.H ∧ ∀ m : ℤ, (P.Fd D.u).im ≠ m * Real.pi := by
  -- decode the rational checks
  obtain ⟨hρ, hV, hnsqv, hball, hc, hY, hx1, hx1η, hx1η0, hx1t, hx1b, hty2, hby2, hbsum, htsum,
    hcsum, htail, hrayB, hhorB, hverA⟩ := of_decide_eq_true h1
  obtain ⟨hm, hm2, hM3, hMρ, hres⟩ := of_decide_eq_true h2
  have h3' := of_decide_eq_true h3
  obtain ⟨hH, hα1, hα2, hα3, hα4⟩ := of_decide_eq_true h7
  -- real versions
  have hρ' : (0 : ℝ) < d.rho := by exact_mod_cast hρ
  have hV' : (0 : ℝ) ≤ d.V := by exact_mod_cast hV
  have hball' : (d.ui : ℝ) + (d.V + d.rho) < 0 := by exact_mod_cast hball
  have hc' : (0 : ℝ) < d.c := by exact_mod_cast hc
  have hY' : (0 : ℝ) < d.Y := by exact_mod_cast hY
  have hx1' : (d.x1 : ℝ) ≤ -1 / 2 := by exact_mod_cast hx1
  have hx1η' : 1 / 2 - (P.etaOne : ℝ) ≤ d.x1 := by
    have := (Rat.cast_le (K := ℝ)).2 hx1η; push_cast at this; linarith
  have hx1η0' : 1 / 2 ≤ (P.eta0 : ℝ) + 2 * d.x1 := by
    have := (Rat.cast_le (K := ℝ)).2 hx1η0; push_cast at this; linarith
  have hx1t' : (d.x1 : ℝ) < d.ur + d.vr - d.rho := by exact_mod_cast hx1t
  have hx1b' : (d.x1 : ℝ) ≤ d.ur - d.vr - d.rho := by exact_mod_cast hx1b
  have hty2' : (d.ui : ℝ) + d.vi + d.rho ≤ -1 / 2 := by exact_mod_cast hty2
  have hby2' : (d.ui : ℝ) - d.vi + d.rho ≤ -1 / 2 := by exact_mod_cast hby2
  have hbsum' : (d.ur : ℝ) - d.vr + d.rho + (d.ui - d.vi + d.rho) ≤ 0 := by exact_mod_cast hbsum
  have htsum' : (d.ur : ℝ) + d.vr + d.rho + (d.ui + d.vi + d.rho) ≤ 0 := by exact_mod_cast htsum
  have hcsum' : (d.x1 : ℝ) + (d.ui + d.vi + d.rho) ≤ 0 := by exact_mod_cast hcsum
  have hrayB' : (d.ui : ℝ) - d.vi + d.rho ≤ d.rayB := by exact_mod_cast hrayB
  have hhorB' : (d.ur : ℝ) + d.vr + d.rho ≤ d.horB := by exact_mod_cast hhorB
  have hverA' : (d.verA : ℝ) ≤ d.ui + d.vi - d.rho := by exact_mod_cast hverA
  have hm' : (0 : ℝ) < d.m := by exact_mod_cast hm
  have hMρ' : (d.M3 : ℝ) * d.rho ≤ d.m / 2 := by exact_mod_cast hMρ
  -- the discs
  set ut : ℂ := cq d.ur d.ui with hut
  set vC : ℂ := cq d.vr d.vi with hvC
  set R : ℝ := (d.V : ℝ) + d.rho with hR
  have hRΩ : closedBall ut R ⊆ Omega P := closedBall_subset_Omega (by rw [hut, cq_im]; linarith)
  have hρR : closedBall ut d.rho ⊆ closedBall ut R :=
    closedBall_subset_closedBall (by rw [hR]; linarith)
  have hM3' : ∀ w ∈ closedBall ut R, ‖P.f''' w‖ ≤ d.M3 := by
    intro w hw
    obtain ⟨hw1, hw2, hw3, hw4⟩ := re_im_bounds_of_mem_closedBall hw
    have hM3r : ((f'''Box P (d.ur - (d.V + d.rho)) (d.ur + (d.V + d.rho)) (d.ui - (d.V + d.rho))
        (d.ui + (d.V + d.rho)) : ℚ) : ℝ) ≤ d.M3 := by exact_mod_cast hM3
    refine (norm_f'''_le_box ?_ ?_ ?_).trans hM3r
    · push_cast; exact ⟨hw1, hw2⟩
    · push_cast; exact ⟨hw3, hw4⟩
    · exact_mod_cast hball
  have hM3nn : (0 : ℝ) ≤ d.M3 :=
    (norm_nonneg _).trans (hM3' ut (mem_closedBall_self (by rw [hR]; linarith)))
  -- (N1) the saddle point
  have hf''ut : P.f'' ut = (f''Q P d.ur d.ui).toC := (toC_f''Q d.ur d.ui).symm
  have hmf'' : (d.m : ℝ) ≤ ‖P.f'' ut‖ := by
    refine le_norm_of_sq_le_normSq ?_
    rw [hf''ut, QC.normSq_toC]
    exact_mod_cast hm2
  have hε : ‖P.f' ut + I * ((P.r : ℂ) - 2) * Real.pi‖ ≤ d.m * d.rho / 2 := by
    refine norm_le_of_normSq_le (by positivity) ?_
    have e1 : (P.f' ut + I * ((P.r : ℂ) - 2) * Real.pi).re = (P.f' ut).re := by simp
    have e2 : (P.f' ut + I * ((P.r : ℂ) - 2) * Real.pi).im =
        (P.f' ut).im + ((P.r : ℝ) - 2) * Real.pi := by simp
    rw [normSq_apply, e1, e2, ← sq, ← sq]
    have k1 := sq_le_sqB (mem_f'ReI (P := P) d.ur d.ui d.prec)
    have k2 := sq_le_sqB (mem_f'ImShI (P := P) d.ur d.ui d.prec)
    have k3 : (((f'ReI P d.ur d.ui d.prec).sqB + (f'ImShI P d.ur d.ui d.prec).sqB : ℚ) : ℝ) ≤
        (((d.m * d.rho / 2) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hres
    push_cast at k3
    linarith
  obtain ⟨us, hus, hsad⟩ := exists_saddle (P := P) (ut := ut) (ρ := d.rho) (m := d.m)
    (ε := d.m * d.rho / 2) (M := d.M3) (hρR.trans hRΩ) hm' hmf'' hε
    (fun w hw => hM3' w (hρR hw)) hMρ' le_rfl
  obtain ⟨hu1, hu2, hu3, hu4⟩ := re_im_bounds_of_mem_closedBall hus
  have husR : us ∈ closedBall ut R := hρR hus
  have hutR : ut ∈ closedBall ut R := mem_closedBall_self (by rw [hR]; linarith)
  have hdist : dist us ut ≤ d.rho := hus
  -- the path
  set D : PathData := ⟨us, vC, (d.x1 : ℝ)⟩ with hD
  have hbotre : D.bot.re = us.re - d.vr := by simp [D, PathData.bot, vC]
  have hbotim : D.bot.im = us.im - d.vi := by simp [D, PathData.bot, vC]
  have htopre : D.top.re = us.re + d.vr := by simp [D, PathData.top, vC]
  have htopim : D.top.im = us.im + d.vi := by simp [D, PathData.top, vC]
  have hcornre : D.corner.re = d.x1 := by simp [D, PathData.corner]
  have hcornim : D.corner.im = D.top.im := by simp [D, PathData.corner]
  -- ‖v‖ ≤ V
  have hnormv2 : ‖vC‖ ^ 2 = d.nsqv := by
    rw [← normSq_eq_norm_sq, hvC, normSq_apply]; simp [SData.nsqv]; ring
  have hvV : ‖vC‖ ≤ d.V := by
    refine norm_le_of_normSq_le hV' ?_
    rw [normSq_eq_norm_sq, hnormv2, SData.nsqv]
    exact_mod_cast hnsqv
  -- (N2) `Re a` and the decay along `σ`
  have hdf'' : ‖P.f'' us - P.f'' ut‖ ≤ d.M3 * d.rho := by
    refine (norm_f''_sub_le hRΩ hM3' husR hutR).trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hdist hM3nn
  have hA : ((aQ P d : ℚ) : ℝ) - d.M3 * d.rho * d.nsqv / 2 ≤ (-(P.f'' us) * vC ^ 2 / 2).re := by
    have e : -(P.f'' us) * vC ^ 2 / 2 =
        -(P.f'' ut) * vC ^ 2 / 2 - (P.f'' us - P.f'' ut) * vC ^ 2 / 2 := by ring
    have e2 : (-(P.f'' ut) * vC ^ 2 / 2).re = ((aQ P d : ℚ) : ℝ) := by
      rw [hf''ut, hvC, re_neg_f''_mul]; rfl
    have k : |((P.f'' us - P.f'' ut) * vC ^ 2 / 2).re| ≤ (d.M3 : ℝ) * d.rho * d.nsqv / 2 := by
      refine (abs_re_le_norm _).trans ?_
      rw [norm_div, norm_mul, norm_pow, hnormv2]
      simp only [Complex.norm_ofNat]
      have : (0 : ℝ) ≤ d.nsqv := by rw [← hnormv2]; positivity
      have := mul_le_mul_of_nonneg_right hdf'' this
      linarith
    rw [e, sub_re, e2]
    linarith [(abs_le.1 k).2]
  have hbQ : ((bQ P d : ℚ) : ℝ) = ((aQ P d : ℚ) : ℝ) - d.M3 * d.rho * d.nsqv / 2 -
      d.M3 * d.V ^ 3 / 6 := by simp [bQ, SData.nsqv]
  have hb : (0 : ℝ) < ((bQ P d : ℚ) : ℝ) := by exact_mod_cast h3'
  have hv3 : ‖vC‖ ^ 3 ≤ (d.V : ℝ) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hvV 3
  have hM3v : (d.M3 : ℝ) * ‖vC‖ ^ 3 ≤ d.M3 * d.V ^ 3 := mul_le_mul_of_nonneg_left hv3 hM3nn
  have hsR : closedBall us ‖vC‖ ⊆ closedBall ut R :=
    closedBall_subset_closedBall' (by rw [hR]; linarith)
  -- (N3), (N4): `Fd` at `u*` versus `ut`
  have hd0 : (0 : ℝ) < -((d.ui : ℝ) + d.rho) := by linarith
  have hM2 : ∀ w ∈ closedBall ut d.rho, ‖P.f'' w‖ ≤ ((M2Q P d : ℚ) : ℝ) := by
    intro w hw
    obtain ⟨-, -, -, hw4⟩ := re_im_bounds_of_mem_closedBall hw
    refine (norm_f''_le_of_im hd0 (by linarith)).trans (le_of_eq ?_)
    simp [M2Q]
  have hFd := norm_Fd_sub_le (hρR.trans hRΩ) hus hsad hM2
  have hδ : 2 * ((M2Q P d : ℚ) : ℝ) * d.rho ^ 2 = ((deltaQ P d : ℚ) : ℝ) := by simp [deltaQ]
  rw [hδ] at hFd
  have hre := (abs_re_le_norm (P.Fd us - P.Fd ut)).trans hFd
  have him := (abs_im_le_norm (P.Fd us - P.Fd ut)).trans hFd
  rw [sub_re] at hre
  rw [sub_im] at him
  have kRe := mem_FdReI (P := P) d.ur d.ui d.prec
  have kIm := mem_FdImI (P := P) d.ur d.ui d.prec
  have hH' : (((FdReI P d.ur d.ui d.prec).hi + deltaQ P d : ℚ) : ℝ) < d.H := by
    exact_mod_cast hH
  have hα1' : ((d.m0 : ℚ) : ℝ) * Num.piLo <
      (((FdImI P d.ur d.ui d.prec).lo - deltaQ P d : ℚ) : ℝ) := by exact_mod_cast hα1
  have hα2' : ((d.m0 : ℚ) : ℝ) * Num.piHi <
      (((FdImI P d.ur d.ui d.prec).lo - deltaQ P d : ℚ) : ℝ) := by exact_mod_cast hα2
  have hα3' : (((FdImI P d.ur d.ui d.prec).hi + deltaQ P d : ℚ) : ℝ) <
      (((d.m0 : ℚ) + 1 : ℚ) : ℝ) * Num.piLo := by exact_mod_cast hα3
  have hα4' : (((FdImI P d.ur d.ui d.prec).hi + deltaQ P d : ℚ) : ℝ) <
      (((d.m0 : ℚ) + 1 : ℚ) : ℝ) * Num.piHi := by exact_mod_cast hα4
  push_cast at hH' hα1' hα2' hα3' hα4'
  refine ⟨D, (bQ P d : ℝ), d.c, 1 / 2, 1 / 2, ?_, ?_, ?_⟩
  rotate_left
  · -- `Re Fd(u*) < H`
    rw [abs_le] at hre
    linarith [kRe.2, hre.2]
  · -- `α ∉ πℤ`
    intro k hk
    rw [abs_le] at him
    have hlo : (d.m0 : ℝ) * Real.pi < (P.Fd D.u).im :=
      mul_pi_lt (by linarith [kIm.1, him.1]) (by linarith [kIm.1, him.1])
    have hhi : (P.Fd D.u).im < ((d.m0 : ℝ) + 1) * Real.pi :=
      lt_mul_pi (by linarith [kIm.2, him.2]) (by linarith [kIm.2, him.2])
    rw [hk] at hlo hhi
    have hpi := Real.pi_pos
    have e1 : (d.m0 : ℝ) < k := lt_of_mul_lt_mul_right hlo hpi.le
    have e2 : (k : ℝ) < d.m0 + 1 := lt_of_mul_lt_mul_right hhi hpi.le
    have e1' : d.m0 < k := by exact_mod_cast e1
    have e2' : k < d.m0 + 1 := by exact_mod_cast e2
    omega
  -- the path certificate
  have hx1gt : -(P.etaOne : ℝ) < d.x1 := by linarith
  have hgood : ∀ z ∈ D.pathSet, (d.x1 : ℝ) ≤ z.re ∧ z.im ≤ 0 ∧ z.re + z.im ≤ 0 ∧
      (z.im ≤ -1 / 2 ∨ z.re ≤ -1 / 2) := by
    have S1 : ∀ z : ℂ, (d.x1 : ℝ) ≤ z.re → z.im ≤ -1 / 2 → z.re + z.im ≤ 0 →
        (d.x1 : ℝ) ≤ z.re ∧ z.im ≤ 0 ∧ z.re + z.im ≤ 0 ∧ (z.im ≤ -1 / 2 ∨ z.re ≤ -1 / 2) :=
      fun z h1 h2 h3 => ⟨h1, by linarith, h3, Or.inl h2⟩
    have b1 : (d.x1 : ℝ) ≤ D.bot.re := by rw [hbotre]; linarith
    have b2 : D.bot.im ≤ -1 / 2 := by rw [hbotim]; linarith
    have b3 : D.bot.re + D.bot.im ≤ 0 := by rw [hbotre, hbotim]; linarith
    have t1 : (d.x1 : ℝ) ≤ D.top.re := by rw [htopre]; linarith
    have t2 : D.top.im ≤ -1 / 2 := by rw [htopim]; linarith
    have t3 : D.top.re + D.top.im ≤ 0 := by rw [htopre, htopim]; linarith
    have c1 : (d.x1 : ℝ) ≤ D.corner.re := by rw [hcornre]
    have c2 : D.corner.im ≤ -1 / 2 := by rw [hcornim]; exact t2
    have c3 : D.corner.re + D.corner.im ≤ 0 := by rw [hcornre, hcornim, htopim]; linarith
    have seg1 : ∀ {a b z : ℂ}, z ∈ segment ℝ a b → (d.x1 : ℝ) ≤ a.re → a.im ≤ -1 / 2 →
        a.re + a.im ≤ 0 → (d.x1 : ℝ) ≤ b.re → b.im ≤ -1 / 2 → b.re + b.im ≤ 0 →
        (d.x1 : ℝ) ≤ z.re ∧ z.im ≤ -1 / 2 ∧ z.re + z.im ≤ 0 := by
      intro a b z hz ha1 ha2 ha3 hb1 hb2 hb3
      refine ⟨?_, ?_, ?_⟩
      · have := lin_of_mem_segment hz (α := -1) (β := 0) (γ := -d.x1) (by linarith) (by linarith)
        linarith
      · have := lin_of_mem_segment hz (α := 0) (β := 1) (γ := -1 / 2) (by linarith) (by linarith)
        linarith
      · have := lin_of_mem_segment hz (α := 1) (β := 1) (γ := 0) (by linarith) (by linarith)
        linarith
    rintro z (((⟨hz1, hz2⟩ | hz) | hz) | hz)
    · exact S1 z (by rw [hz1]; exact b1) (by linarith) (by rw [hz1]; linarith)
    · obtain ⟨k1, k2, k3⟩ := seg1 hz b1 b2 b3 t1 t2 t3
      exact S1 z k1 k2 k3
    · obtain ⟨k1, k2, k3⟩ := seg1 hz t1 t2 t3 c1 c2 c3
      exact S1 z k1 k2 k3
    · have hx : ((D.x1 : ℂ)).re = d.x1 := by simp [D]
      have hy : ((D.x1 : ℂ)).im = 0 := by simp
      have k1 := lin_of_mem_segment hz (α := 1) (β := 0) (γ := d.x1) (by rw [hcornre]; linarith)
        (by rw [hx]; linarith)
      have k2 := lin_of_mem_segment hz (α := -1) (β := 0) (γ := -d.x1) (by rw [hcornre]; linarith)
        (by rw [hx]; linarith)
      have k3 := lin_of_mem_segment hz (α := 0) (β := 1) (γ := 0) (by linarith)
        (by rw [hy]; linarith)
      refine ⟨by linarith, by linarith, by linarith, Or.inr (by linarith)⟩
  have hbx : (((d.ur - d.vr - d.rho : ℚ) : ℝ) ≤ D.bot.re ∧
      D.bot.re ≤ ((d.ur - d.vr + d.rho : ℚ) : ℝ)) := by
    rw [hbotre]; push_cast; constructor <;> linarith
  have hty : (((d.ui + d.vi - d.rho : ℚ) : ℝ) ≤ D.top.im ∧
      D.top.im ≤ ((d.ui + d.vi + d.rho : ℚ) : ℝ)) := by
    rw [htopim]; push_cast; constructor <;> linarith
  have hty2Q : d.ui + d.vi + d.rho < 0 := by
    have : (d.ui : ℚ) + d.vi + d.rho ≤ -1 / 2 := hty2
    linarith
  refine
    { saddle := hsad
      re_a_pos := ?_
      b_pos := hb
      sigma_decay := ?_
      c_pos := hc'
      ray := ?_
      x1_lt := by change (d.x1 : ℝ) < D.top.re; rw [htopre]; linarith
      horiz := ?_
      vert := ?_
      x1_neg := by change (d.x1 : ℝ) < 0; linarith
      x1_gt := hx1gt
      top_im_neg := by rw [htopim]; linarith
      bot_im_neg := by rw [hbotim]; linarith
      c₀_pos := by norm_num
      ε₀_pos := by norm_num
      path_norm := fun z hz => by
        obtain ⟨g1, g2, g3, g4⟩ := hgood z hz; exact (path_props g1 g2 g3 g4 hx1η' hx1η0').1
      path_arg := fun z hz => by
        obtain ⟨g1, g2, g3, g4⟩ := hgood z hz; exact (path_props g1 g2 g3 g4 hx1η' hx1η0').2.1
      path_re := fun z hz => by
        obtain ⟨g1, g2, g3, g4⟩ := hgood z hz; exact (path_props g1 g2 g3 g4 hx1η' hx1η0').2.2.1
      path_eta0 := fun z hz => by
        obtain ⟨g1, g2, g3, g4⟩ := hgood z hz; exact (path_props g1 g2 g3 g4 hx1η' hx1η0').2.2.2 }
  · -- `Re a > 0`
    change 0 < (-(P.f'' us) * vC ^ 2 / 2).re
    have : (0 : ℝ) ≤ d.M3 * d.V ^ 3 := by positivity
    linarith
  · -- decay along `σ`
    intro s hs
    change (P.Fd (us + s * vC) - P.Fd us).re ≤ -((bQ P d : ℚ) : ℝ) * s ^ 2
    have k := re_Fd_sub_le (P := P) (u := us) (v := vC) (M := d.M3) (hsR.trans hRΩ) hsad
      (fun w hw => hM3' w (hsR hw)) hs
    have hbX : ((bQ P d : ℚ) : ℝ) ≤ (-(P.f'' us) * vC ^ 2 / 2).re - d.M3 * ‖vC‖ ^ 3 / 6 := by
      linarith
    have := mul_le_mul_of_nonneg_right hbX (sq_nonneg s)
    linarith
  · -- the ray
    have hx1r : -(P.etaOne : ℝ) < ((d.ur - d.vr - d.rho : ℚ) : ℝ) := by push_cast; linarith
    have hfin : ∀ y ∈ Icc (-(d.Y : ℝ)) D.bot.im,
        (P.f' (D.bot.re + y * I)).im + ((P.r : ℝ) - 2) * Real.pi ≤ -d.c := by
      intro y hy
      refine forall_of_allSteps
        (p := fun y : ℝ => (P.f' (D.bot.re + y * I)).im + ((P.r : ℝ) - 2) * Real.pi ≤ -d.c)
        (chk := rayBox P d) (fun s t hst => ?_) h4 y ⟨?_, ?_⟩
      · obtain ⟨ht, hchk⟩ := of_decide_eq_true hst
        exact ray_box hP hx1r ht hchk hbx
      · push_cast; exact hy.1
      · linarith [hy.2]
    have htail' : -2 * Real.pi + P.r * (P.eta0 + 2 * |D.bot.re|) / d.Y ≤ -d.c := by
      have k := (Rat.cast_le (K := ℝ)).2 htail
      push_cast at k
      have hX : |D.bot.re| ≤ max (-((d.ur : ℝ) - d.vr - d.rho)) ((d.ur : ℝ) - d.vr + d.rho) := by
        rw [abs_le']
        constructor
        · exact le_max_of_le_right (by rw [hbotre]; linarith)
        · exact le_max_of_le_left (by rw [hbotre]; linarith)
      have h1 : (P.r : ℝ) * (P.eta0 + 2 * |D.bot.re|) / d.Y ≤
          P.r * (P.eta0 + 2 * max (-((d.ur : ℝ) - d.vr - d.rho)) ((d.ur : ℝ) - d.vr + d.rho)) /
            d.Y :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))
          hY'.le
      have h2 := Num.piLo_lt_pi
      linarith
    exact ray_of_tail hP hY' hfin htail'
  · -- the horizontal segment
    intro x hx
    refine forall_of_allSteps (p := fun x : ℝ => 0 < (P.f' (x + D.top.im * I)).re)
      (chk := horBox P d) (fun s t hst => ?_) h5 x ⟨hx.1, ?_⟩
    · rw [horBox, Bool.and_eq_true] at hst
      obtain ⟨hs1, hs2⟩ := hst
      exact hor_box hP (of_decide_eq_true hs1) hty2Q hs2 hty
    · have := hx.2
      rw [htopre] at this
      linarith
  · -- the vertical segment
    intro y hy
    refine forall_of_allSteps
      (p := fun y : ℝ => 0 < (P.f' ((d.x1 : ℝ) + y * I)).im + ((P.r : ℝ) - 2) * Real.pi)
      (chk := verBox P d) (fun s t hst => ?_) h6 y ⟨?_, ?_⟩
    · obtain ⟨ht, hchk⟩ := of_decide_eq_true hst
      exact ver_box hP hx1gt (by
        have : (d.x1 : ℚ) ≤ -1 / 2 := hx1
        linarith) ht hchk
    · have := hy.1
      rw [htopim] at this
      linarith
    · rw [Rat.cast_zero]; exact hy.2

end OddZeta.Cert
