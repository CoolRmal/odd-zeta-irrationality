import OddZeta.Family.SmallSeg
import OddZeta.Family.CertDef
import OddZeta.Family.Regions

/-!
# The per-`r` certificate checker for the family (`3 ≤ r ≤ 299`)

A data record `SmData` (a rational approximation `ũ` of the saddle point `u*` of `Fd`, the
half-length vector `v` of `σ`, the path `-i∞ → P_R = 20 + i y_R → bot → σ → top → P_L → -2`,
short rational approximations of `bot = u* - v`, `top = u* + v`, grids for the three segments and
the constants of `PathCert2`), the Bool checker `famCertOK r d` and its soundness
`famCert_of_ok : famCertOK r d = true → FamCert r`:
* the saddle point by the contraction argument (`exists_saddle`, radius `ρ = 10⁻¹⁰`);
* `sigma_decay` by the cubic Taylor bound for `Φ_r = r g + e - 2πi u` on the disc of radius
  `|v|` around `u*` (bounded by `F3Disc`, from lower bounds `normLo` of the distances to the
  singularities; the disc may cross the positive real axis);
* `off_sigma`: the ray by `regRay_bound`, the segments `[P_R, bot]`, `[top, P_L]` by the perturbed
  segment check `chkSegP`, `[P_L, -2]` by `chkSegP` and `lastOK`;
* `H_d < -(214.8 r - 3)` and `α ∉ πℤ` from an enclosure of `Fd(ũ)`;
* the geometric conditions from linear inequalities at the end points of the pieces.
-/

namespace OddZeta.Small

open Complex Metric Set OddZeta.Cert OddZeta.Cert.QI OddZeta.FamNum

/-! ### Lower bounds for norms and a bound for `‖Φ_r'''‖` on a disc -/

theorem lin_abs_le_norm {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≤ 1) (z : ℂ) :
    a * |z.re| + b * |z.im| ≤ ‖z‖ := by
  apply le_norm_of_sq_le_normSq
  rw [normSq_apply]
  have h1 := sq_abs z.re
  have h2 := sq_abs z.im
  nlinarith [sq_nonneg (a * |z.im| - b * |z.re|), abs_nonneg z.re, abs_nonneg z.im,
    mul_nonneg (sub_nonneg.2 hab) (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))]

theorem lin_le_norm {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≤ 1) (z : ℂ) : a * z.re + b * z.im ≤ ‖z‖ := by
  apply le_norm_of_sq_le_normSq
  rw [normSq_apply]
  nlinarith [sq_nonneg (a * z.im - b * z.re),
    mul_nonneg (sub_nonneg.2 hab) (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))]

/-- A lower bound for `‖x + y i‖` (a 16-gon). -/
def normLo (x y : ℚ) : ℚ :=
  max (max (max |x| |y|) (7071 / 10000 * (|x| + |y|)))
    (max (9238 / 10000 * |x| + 3826 / 10000 * |y|) (3826 / 10000 * |x| + 9238 / 10000 * |y|))

theorem normLo_le (x y : ℚ) : (normLo x y : ℝ) ≤ ‖cq x y‖ := by
  have h1 := abs_re_le_norm (cq x y)
  have h2 := abs_im_le_norm (cq x y)
  have h3 := lin_abs_le_norm (a := 7071 / 10000) (b := 7071 / 10000) (by norm_num) (cq x y)
  have h4 := lin_abs_le_norm (a := 9238 / 10000) (b := 3826 / 10000) (by norm_num) (cq x y)
  have h5 := lin_abs_le_norm (a := 3826 / 10000) (b := 9238 / 10000) (by norm_num) (cq x y)
  simp only [cq_re, cq_im] at h1 h2 h3 h4 h5
  simp only [normLo, Rat.cast_max, Rat.cast_abs, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat]
  refine max_le (max_le (max_le h1 h2) (by linarith)) (max_le (by linarith) (by linarith))

theorem inv_sq_le_disc {a x y R : ℚ} {w : ℂ} (hw : w ∈ closedBall (cq x y) R)
    (hR : R < normLo (a + x) y) :
    ‖(((a : ℂ) + w) ^ 2)⁻¹‖ ≤ ((1 / (normLo (a + x) y - R) ^ 2 : ℚ) : ℝ) := by
  have k1 := norm_add_ge_of_mem_closedBall (a := (a : ℂ)) hw
  have e : (a : ℂ) + cq x y = cq (a + x) y := by unfold cq; push_cast; ring
  rw [e] at k1
  have k2 := normLo_le (a + x) y
  have hR' : (R : ℝ) < normLo (a + x) y := by exact_mod_cast hR
  have := norm_inv_sq_le_one_div (z := (a : ℂ) + w) (l := (normLo (a + x) y : ℝ) - R)
    (by linarith) (by linarith)
  push_cast
  exact this

/-- A bound for `‖Φ_r'''‖` on the closed disc of radius `R` around `x + y i`. -/
def F3Disc (r : ℕ) (x y R : ℚ) : ℚ :=
  r * (famCB.map fun bc : ℕ × ℤ => |(bc.2 : ℚ)| / (normLo (bc.1 + x) y - R) ^ 2).sum +
    (1 / (normLo (74 + x) y - R) ^ 2 + 1 / (normLo (76 + x) y - R) ^ 2)

theorem norm_Phi3_le_disc (r : ℕ) {x y R : ℚ} {w : ℂ} (hw : w ∈ closedBall (cq x y) R)
    (hpos : ∀ bc ∈ famCB, R < normLo (bc.1 + x) y) (h4 : R < normLo (74 + x) y)
    (h6 : R < normLo (76 + x) y) : ‖Phi3 r w‖ ≤ F3Disc r x y R := by
  unfold Phi3
  refine (norm_add_le _ _).trans ?_
  simp only [F3Disc, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
  rw [norm_mul, Complex.norm_natCast]
  refine add_le_add (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) ?_
  · unfold famG3
    rw [norm_neg, cast_list_sum_map]
    refine norm_list_sum_map_le _ fun bc hbc => ?_
    have k := inv_sq_le_disc (a := (bc.1 : ℚ)) hw (hpos bc hbc)
    rw [Rat.cast_natCast] at k
    rw [norm_mul, Complex.norm_intCast]
    push_cast at k ⊢
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left k (abs_nonneg _)
  · unfold famE3
    rw [norm_neg]
    have k4 := inv_sq_le_disc (a := 74) hw h4
    have k6 := inv_sq_le_disc (a := 76) hw h6
    push_cast at k4 k6 ⊢
    exact (norm_sub_le _ _).trans (add_le_add k4 k6)

/-! ### Segments -/

theorem seg_right_pert {P Q Q' z : ℂ} {ρ : ℝ} (hQ : ‖Q' - Q‖ ≤ ρ) (hz : z ∈ segment ℝ P Q') :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧ ∃ δ : ℂ, ‖δ‖ ≤ ρ ∧ z = P + τ * (Q - P) + δ := by
  rw [segment_eq_image'] at hz
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hz
  refine ⟨τ, h0, h1, τ * (Q' - Q), ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    nlinarith [norm_nonneg (Q' - Q)]
  · simp only [Complex.real_smul]; ring

theorem seg_left_pert {P P' Q z : ℂ} {ρ : ℝ} (hP : ‖P' - P‖ ≤ ρ) (hz : z ∈ segment ℝ P' Q) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧ ∃ δ : ℂ, ‖δ‖ ≤ ρ ∧ z = P + τ * (Q - P) + δ := by
  rw [segment_eq_image'] at hz
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hz
  refine ⟨τ, h0, h1, ((1 - τ : ℝ) : ℂ) * (P' - P), ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (P' - P)]
  · simp only [Complex.real_smul]; push_cast; ring

theorem cq_sub (a b c e : ℚ) : cq c e - cq a b = cq (c - a) (e - b) := by
  unfold cq; push_cast; ring

/-- The properties of a point of a segment whose end points satisfy them. -/
theorem seg_good {a b z : ℂ} {c₀ K : ℝ} (hz : z ∈ segment ℝ a b) (hc₀ : 0 < c₀)
    (ha1 : a.im ≤ -c₀) (hb1 : b.im ≤ -c₀) (ha2 : -40 ≤ a.re) (hb2 : -40 ≤ b.re)
    (ha3 : a.re + K * a.im ≤ 0) (hb3 : b.re + K * b.im ≤ 0) :
    z.im < 0 ∧ -40 ≤ z.re ∧ z.re + K * z.im ≤ 0 ∧ c₀ ≤ ‖z‖ := by
  have k1 := lin_of_mem_segment (α := 0) (β := 1) (γ := -c₀) hz (by linarith) (by linarith)
  have k2 := lin_of_mem_segment (α := -1) (β := 0) (γ := 40) hz (by linarith) (by linarith)
  have k3 := lin_of_mem_segment (α := 1) (β := K) (γ := 0) hz (by linarith) (by linarith)
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  have := abs_im_le_norm z
  rw [abs_of_neg (by linarith)] at this
  linarith

theorem im_neg_of_seg {a b z : ℂ} (hz : z ∈ segment ℝ a b) (ha : a.im < 0) (hb : b.im < 0) :
    z.im < 0 := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  simp only [add_im, smul_im, smul_eq_mul]
  rcases eq_or_lt_of_le hs with h | h
  · subst h; simp only [zero_add] at hst; subst hst; linarith
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hb.le]

/-- `|arg (-z)| ≤ π/2 + arctan K` if `Im z < 0` and `Re z ≤ K |Im z|` (`K ≥ 0`). -/
theorem abs_arg_neg_le' {z : ℂ} {K : ℝ} (hz : z.im < 0) (h : z.re ≤ K * -z.im) :
    |(-z).arg| ≤ Real.pi - (Real.pi / 2 - Real.arctan K) := by
  have him : 0 < (-z).im := by rw [neg_im]; linarith
  have harg := Cert.arg_mk_of_im_pos (-z).re him
  rw [← Cert.arg_eq_mk] at harg
  have hnn : 0 ≤ (-z).arg := Complex.arg_nonneg_iff.2 him.le
  rw [abs_of_nonneg hnn, harg]
  have h1 : -K ≤ (-z).re / (-z).im := by
    rw [le_div_iff₀ him, neg_re, neg_im]
    linarith
  have h2 := Real.arctan_strictMono.monotone h1
  rw [Real.arctan_neg] at h2
  linarith

/-! ### The data and the checker -/

/-- The data of a per-`r` certificate. -/
structure SmData where
  /-- `ũ = ur + ui i ≈ u*` -/
  ur : ℚ
  ui : ℚ
  /-- `v = vr + vi i` -/
  vr : ℚ
  vi : ℚ
  /-- `‖v‖ ≤ V` -/
  V : ℚ
  /-- `m ≤ ‖f''(ũ)‖` -/
  m : ℚ
  /-- `‖Φ'''‖ ≤ M3` on the disc of radius `V + ρ` around `ũ` -/
  M3 : ℚ
  /-- the decay constant -/
  b : ℚ
  /-- `Re Fd ≤ T` on `L \ σ`, `T + b ≤ Re Fd(u*)` -/
  T : ℚ
  /-- `Im Fd(u*) ∈ (m0 π, (m0 + 1) π)` -/
  m0 : ℤ
  /-- `P_R = 20 + yR i` -/
  yR : ℚ
  /-- approximations of `bot`, `top` within `rs` -/
  br : ℚ
  bi : ℚ
  tr : ℚ
  ti : ℚ
  rs : ℚ
  /-- `P_L` -/
  plx : ℚ
  ply : ℚ
  /-- the last piece of `[P_L, -2]` starts at the parameter `lam` -/
  lam : ℚ
  /-- the grids of `[P_R, bot]`, `[top, P_L]`, `[P_L, Q]` -/
  gR : List ℚ
  gT : List ℚ
  gL : List ℚ
  /-- `c₀` and the normal `(na, nb)` of `[P_L, -2]` -/
  c0 : ℚ
  na : ℚ
  nb : ℚ
  /-- `Re z ≤ K |Im z|` on the path -/
  K : ℚ

/-- The contraction radius `ρ`. -/
def rho : ℚ := 1 / 10000000000

/-- The precision at the saddle point. -/
def pS : ℕ := 60

/-- The precision on the grids. -/
def pG : ℕ := 30

/-- The geometric and rational side conditions. -/
def geomOK (r : ℕ) (d : SmData) : Bool :=
  decide (1 ≤ r ∧ 0 ≤ d.V ∧ d.vr ^ 2 + d.vi ^ 2 ≤ d.V ^ 2 ∧
    d.ui - d.vi + rho < 0 ∧ d.ui + d.vi + rho < 0 ∧ d.ply < 0 ∧ d.yR ≤ -1 / 4 ∧
    (r : ℚ) * (-2400670 / 10000) + -97210 / 10000 + 6 * d.yR ≤ d.T ∧
    |d.ur - d.vr - d.br| + |d.ui - d.vi - d.bi| + rho ≤ d.rs ∧
    |d.ur + d.vr - d.tr| + |d.ui + d.vi - d.ti| + rho ≤ d.rs ∧
    0 < d.c0 ∧ d.c0 ≤ 2 ∧ d.c0 ≤ -d.yR ∧ d.c0 ≤ -(d.ui - d.vi + rho) ∧
    d.c0 ≤ -(d.ui + d.vi + rho) ∧ d.c0 ≤ -d.ply ∧
    d.na ^ 2 + d.nb ^ 2 ≤ 1 ∧ d.c0 ≤ d.na * d.plx + d.nb * d.ply ∧ d.c0 ≤ -2 * d.na ∧
    0 ≤ d.K ∧ 20 + d.K * d.yR ≤ 0 ∧ d.ur - d.vr + rho + d.K * (d.ui - d.vi + rho) ≤ 0 ∧
    d.ur + d.vr + rho + d.K * (d.ui + d.vi + rho) ≤ 0 ∧ d.plx + d.K * d.ply ≤ 0 ∧
    -40 ≤ d.ur - d.vr - rho ∧ -40 ≤ d.ur + d.vr - rho ∧ -40 ≤ d.plx ∧
    0 < d.lam ∧ d.lam < 1)

/-- `Re (-f''(ũ) v² / 2)`. -/
def aQ (r : ℕ) (d : SmData) : ℚ :=
  -((F2Q r d.ur d.ui).re * (d.vr ^ 2 - d.vi ^ 2) - (F2Q r d.ur d.ui).im * (2 * d.vr * d.vi)) / 2

/-- The contraction argument and the decay along `σ` (`F` encloses `Fd`, `Fd'` at `ũ`). -/
def saddleOK (r : ℕ) (d : SmData) (F : Pt) : Bool :=
  okBox (d.ur - (d.V + rho)) (d.ur + (d.V + rho)) (d.ui - (d.V + rho)) (d.ui + (d.V + rho)) &&
  decide (0 < d.m ∧ d.m ^ 2 ≤ (F2Q r d.ur d.ui).nsq ∧
    (∀ bc ∈ famCB, d.V + rho < normLo (bc.1 + d.ur) d.ui) ∧ d.V + rho < normLo (74 + d.ur) d.ui ∧
    d.V + rho < normLo (76 + d.ur) d.ui ∧ F3Disc r d.ur d.ui (d.V + rho) ≤ d.M3 ∧
    d.M3 * rho ≤ d.m / 2 ∧ F.dre.sqB + F.dim.sqB ≤ (d.m * rho / 2) ^ 2 ∧
    0 < d.b ∧ d.b ≤ aQ r d - d.M3 * rho * (d.vr ^ 2 + d.vi ^ 2) / 2 - d.M3 * d.V ^ 3 / 6)

/-- The perturbation bound `‖Fd u* - Fd ũ‖ ≤ δ`. -/
def deltaQ (r : ℕ) (d : SmData) : ℚ :=
  2 * F2Box r (d.ur - rho) (d.ur + rho) (d.ui - rho) (d.ui + rho) * rho ^ 2

/-- `T + b ≤ Re Fd(u*)`, `H_d < -(214.8 r - 3)` and `α ∉ πℤ`. -/
def fdOK (r : ℕ) (d : SmData) (F : Pt) : Bool :=
  okBox (d.ur - rho) (d.ur + rho) (d.ui - rho) (d.ui + rho) &&
  decide (d.T + d.b ≤ F.re.lo - deltaQ r d ∧ F.re.hi + deltaQ r d < -(2148 / 10 * r - 3) ∧
    (d.m0 : ℚ) * Num.piLo < F.im.lo - deltaQ r d ∧ (d.m0 : ℚ) * Num.piHi < F.im.lo - deltaQ r d ∧
    F.im.hi + deltaQ r d < ((d.m0 : ℚ) + 1) * Num.piLo ∧
    F.im.hi + deltaQ r d < ((d.m0 : ℚ) + 1) * Num.piHi)

/-- The three segments. -/
def segOK (r : ℕ) (d : SmData) : Bool :=
  chkSegP (fun x y => FPt r x y pG) (F2Box r) okBox 20 d.yR (d.br - 20) (d.bi - d.yR) d.rs d.T 1
      d.gR &&
    chkSegP (fun x y => FPt r x y pG) (F2Box r) okBox d.tr d.ti (d.plx - d.tr) (d.ply - d.ti) d.rs
      d.T 1 d.gT &&
    chkSegP (fun x y => FPt r x y pG) (F2Box r) okBox d.plx d.ply (-2 - d.plx) (-d.ply) 0 d.T d.lam
      d.gL &&
    lastOK r pG (d.plx + d.lam * (-2 - d.plx)) (d.ply + d.lam * -d.ply) d.T

/-- **The checker.** -/
def famCertOK (r : ℕ) (d : SmData) : Bool :=
  geomOK r d && saddleOK r d (FPt r d.ur d.ui pS) && fdOK r d (FPt r d.ur d.ui pS) && segOK r d

end OddZeta.Small
