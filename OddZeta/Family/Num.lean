import OddZeta.Family.Phase
import OddZeta.Cert.SaddleNum
import Mathlib.Analysis.Complex.AbsMax

/-!
# Verified numerics for the functions `g` and `e` of the family `η^(r)` (Section 8)

Reusable tools for kernel-checked (`decide +kernel`) bounds on `famG`, `famE` and their
derivatives (`p` is the precision in bits of the `log` / `arg` evaluations, `cq x y = x + y i`):

* **point enclosures**: a record `Pt` of rational intervals for `Re Φ(u)`, `Im Φ(u)`, `Re Φ'(u)`,
  `Im Φ'(u)`: `gPt x y p` (`Φ = famG`, `mem_gPt`), `ePt` (`famE`, `mem_ePt`), `esPt`
  (`famEs u = famE u - 2πi u`, `mem_esPt`), `FPt r` (`r famG + famEs`, `mem_FPt`; this is `Fd` of
  `η^(r)`, with derivative `f' + i(r-2)π`, on the lower half plane: `mem_FPt_Fd`). Kernel cost:
  about 15–20 ms per `gPt`, 12 ms per `g2Box`;
* **exact second derivatives** `g2Q`, `e2Q`, `F2Q` (`toC_g2Q`, `toC_e2Q`, `toC_F2Q`) and **box
  bounds** (via `lowN`, a lower bound for `‖z‖` on a box) `g2Box`, `g3Box`, `e2Box`, `e3Box`,
  `F2Box`, `F3Box` (`norm_famG2_le_box`, …, `norm_f''_le_box`, `norm_f'''_le_box`);
* **derivatives** on the slit plane: `hasDerivAt_famG`, `hasDerivAt_famG1`, `hasDerivAt_famG2`,
  `hasDerivAt_famE`, `hasDerivAt_famE1`, `hasDerivAt_famE2`, `hasDerivAt_famEs`,
  `hasDerivAt_famEs1`;
* **Taylor bounds** `re_le_taylor`, `re_le_quad`;
* **the segment lemma** (Lemma 4.8 of the note): the Bool checker `chkSeg` on a grid of a segment
  (each grid point controls half of each adjacent piece by a second-order Taylor bound whose
  first-order term is taken along the segment) and its soundness `chkSeg_sound`, for any `Φ` with
  an enclosure oracle (`EvOK`) and a box bound for `‖Φ''‖` (`BoxOK`); instances `gEvOK`, `gBoxOK`,
  `esEvOK`, `esBoxOK`; the rectangle version `chkRect` / `chkRect_sound` (maximum principle,
  `re_le_of_frontier`);
* **monotonicity on vertical rays** `re_antitone_ray`.
-/

namespace OddZeta.FamNum

open Complex Metric Set OddZeta.Cert OddZeta.Cert.QI

/-! ### Enclosures of `log ‖x + y i‖` and `arg (x + y i)` from a single evaluation -/

/-- `[log ‖x + y i‖]` (both bounds from one evaluation of `Num.logAbsCore`). -/
def logAbsQ (x y : ℚ) (p : ℕ) : QI :=
  if x = 0 ∧ y = 0 then ⟨0, 0⟩ else
    let P := Num.workPrec p
    let r := Num.logAbsCore x y P
    ⟨Num.subQ r.lp r.ln (P + 1), Num.subQ r.hp r.hn (P + 1)⟩

theorem mem_logAbsQ (x y : ℚ) (p : ℕ) : (logAbsQ x y p).Mem (Real.log ‖cq x y‖) := by
  unfold logAbsQ
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [QI.Mem, cq]
  · have hs := Num.logAbsCore_spec (not_and_or.1 h) (Num.workPrec_le p)
    exact ⟨Num.SB.lo_le hs, Num.SB.le_hi hs⟩

/-- `[arg (x + y i)]` (both bounds from one evaluation of `Num.argCore`). -/
def argQ (x y : ℚ) (p : ℕ) : QI :=
  if x = 0 ∧ y = 0 then ⟨0, 0⟩ else
    let P := Num.workPrec p
    let r := Num.argCore x y P
    ⟨Num.subQ r.lp r.ln P, Num.subQ r.hp r.hn P⟩

theorem mem_argQ (x y : ℚ) (p : ℕ) : (argQ x y p).Mem (arg (cq x y)) := by
  unfold argQ
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [QI.Mem, cq]
  · have hs := Num.argCore_spec (not_and_or.1 h) (Num.workPrec_le p)
    rw [show cq x y = ((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I from Num.ratCast_add_mul_I x y]
    exact ⟨Num.SB.lo_le hs, Num.SB.le_hi hs⟩

/-! ### Point enclosures -/

/-- Enclosures of `Re Φ(u)`, `Im Φ(u)`, `Re Φ'(u)`, `Im Φ'(u)` at a point `u`. -/
structure Pt where
  re : QI
  im : QI
  dre : QI
  dim : QI

namespace Pt

/-- `P` encloses the value `v = Φ(u)` and the derivative `d = Φ'(u)`. -/
def Mem (P : Pt) (v d : ℂ) : Prop :=
  P.re.Mem v.re ∧ P.im.Mem v.im ∧ P.dre.Mem d.re ∧ P.dim.Mem d.im

/-- Sum of enclosures. -/
def add (P Q : Pt) : Pt := ⟨P.re.add Q.re, P.im.add Q.im, P.dre.add Q.dre, P.dim.add Q.dim⟩

/-- The enclosure of `0`. -/
def zero : Pt := ⟨QI.zero, QI.zero, QI.zero, QI.zero⟩

theorem mem_add {P Q : Pt} {v d v' d' : ℂ} (hP : P.Mem v d) (hQ : Q.Mem v' d') :
    (P.add Q).Mem (v + v') (d + d') := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  obtain ⟨k1, k2, k3, k4⟩ := hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [add_re]; exact QI.mem_add h1 k1
  · rw [add_im]; exact QI.mem_add h2 k2
  · rw [add_re]; exact QI.mem_add h3 k3
  · rw [add_im]; exact QI.mem_add h4 k4

theorem mem_zero : zero.Mem 0 0 := by
  simp [Mem, zero, QI.zero, QI.Mem]

end Pt

/-- Real and imaginary part of `c · w log w` for real `c`. -/
theorem re_mul_wlog (c : ℝ) (w : ℂ) :
    ((c : ℂ) * w * log w).re = c * (w.re * Real.log ‖w‖ - w.im * arg w) := by
  simp [mul_re, mul_im, log_re, log_im]
  ring

theorem im_mul_wlog (c : ℝ) (w : ℂ) :
    ((c : ℂ) * w * log w).im = c * (w.im * Real.log ‖w‖ + w.re * arg w) := by
  simp [mul_re, mul_im, log_re, log_im]
  ring

/-- The term `c (b + u) log (b + u)` of `g`, with derivative `c log (b + u)`. -/
def gTerm (x y : ℚ) (p : ℕ) (bc : ℕ × ℤ) : Pt :=
  let w : ℚ := bc.1 + x
  let c : ℚ := bc.2
  let L := logAbsQ w y p
  let A := argQ w y p
  ⟨smul c ((smul w L).sub (smul y A)), smul c ((smul y L).add (smul w A)), smul c L, smul c A⟩

theorem intCast_eq_ofReal (c : ℤ) : (c : ℂ) = ((c : ℝ) : ℂ) := by push_cast; rfl

theorem mem_gTerm (x y : ℚ) (p : ℕ) (bc : ℕ × ℤ) :
    (gTerm x y p bc).Mem ((bc.2 : ℂ) * ((bc.1 : ℂ) + cq x y) * log ((bc.1 : ℂ) + cq x y))
      ((bc.2 : ℂ) * log ((bc.1 : ℂ) + cq x y)) := by
  rw [natCast_add_cq, intCast_eq_ofReal]
  have hc : ((bc.2 : ℚ) : ℝ) = (bc.2 : ℝ) := by push_cast; rfl
  have hL := mem_logAbsQ ((bc.1 : ℚ) + x) y p
  have hA := mem_argQ ((bc.1 : ℚ) + x) y p
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [re_mul_wlog, cq_re, cq_im]
    exact mem_smul' _ hc (mem_sub (mem_smul _ hL) (mem_smul _ hA))
  · rw [im_mul_wlog, cq_re, cq_im]
    exact mem_smul' _ hc (mem_add (mem_smul _ hL) (mem_smul _ hA))
  · rw [re_ofReal_mul, log_re]
    exact mem_smul' _ hc hL
  · rw [im_ofReal_mul, log_im]
    exact mem_smul' _ hc hA

/-- The sum of the terms of `g` over a coefficient list. -/
def gSum (x y : ℚ) (p : ℕ) : List (ℕ × ℤ) → Pt
  | [] => Pt.zero
  | bc :: L => (gTerm x y p bc).add (gSum x y p L)

theorem mem_gSum (x y : ℚ) (p : ℕ) : ∀ L : List (ℕ × ℤ),
    (gSum x y p L).Mem
      (L.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * ((bc.1 : ℂ) + cq x y) * log ((bc.1 : ℂ) + cq x y)).sum
      (L.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * log ((bc.1 : ℂ) + cq x y)).sum
  | [] => by simpa [gSum] using Pt.mem_zero
  | bc :: L => by
    simpa only [gSum, List.map_cons, List.sum_cons] using
      Pt.mem_add (mem_gTerm x y p bc) (mem_gSum x y p L)

/-- Lower bound for `κ_g`. -/
def kgLo : ℚ := mkRat 47517520411842014 100000000000000

/-- Upper bound for `κ_g`. -/
def kgHi : ℚ := mkRat 47517520411842017 100000000000000

/-- `[κ_g]`. -/
def kgI : QI := ⟨kgLo, kgHi⟩

theorem kg_check :
    kgLo ≤ -90 * (logNI 45 60).hi + 54 * (logNI 54 60).lo + 50 * (logNI 50 60).lo +
      44 * (logNI 44 60).lo + 38 * (logNI 38 60).lo + 30 * (logNI 30 60).lo ∧
    -90 * (logNI 45 60).lo + 54 * (logNI 54 60).hi + 50 * (logNI 50 60).hi +
      44 * (logNI 44 60).hi + 38 * (logNI 38 60).hi + 30 * (logNI 30 60).hi ≤ kgHi := by
  decide +kernel

theorem mem_kgI : kgI.Mem famKg := by
  obtain ⟨h1, h2⟩ := kg_check
  have h1' := (Rat.cast_le (K := ℝ)).2 h1
  have h2' := (Rat.cast_le (K := ℝ)).2 h2
  push_cast at h1' h2'
  have a := mem_logNI 45 60
  have b := mem_logNI 54 60
  have c := mem_logNI 50 60
  have d := mem_logNI 44 60
  have e := mem_logNI 38 60
  have f := mem_logNI 30 60
  simp only [QI.Mem, Nat.cast_ofNat] at a b c d e f
  refine ⟨?_, ?_⟩ <;> simp only [kgI, famKg] <;>
    linarith [a.1, a.2, b.1, b.2, c.1, c.2, d.1, d.2, e.1, e.2, f.1, f.2]

/-- **Enclosure of `g`, `g'` at `x + y i`.** -/
def gPt (x y : ℚ) (p : ℕ) : Pt :=
  let S := gSum x y p famCB
  ⟨S.re.add kgI, S.im, S.dre, S.dim⟩

theorem mem_gPt (x y : ℚ) (p : ℕ) : (gPt x y p).Mem (famG (cq x y)) (famG1 (cq x y)) := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_gSum x y p famCB
  refine ⟨?_, ?_, h3, h4⟩
  · simp only [gPt, famG, add_re, ofReal_re]
    exact mem_add h1 mem_kgI
  · simpa only [gPt, famG, add_im, ofReal_im, add_zero] using h2

/-- Lower bound for `2 log 2`. -/
def l2Lo : ℚ := mkRat 138629436111989 100000000000000

/-- Upper bound for `2 log 2`. -/
def l2Hi : ℚ := mkRat 138629436111990 100000000000000

/-- `[2 log 2]`. -/
def l2I : QI := ⟨l2Lo, l2Hi⟩

theorem l2_check : l2Lo ≤ 2 * (logNI 2 60).lo ∧ 2 * (logNI 2 60).hi ≤ l2Hi := by
  decide +kernel

theorem mem_l2I : l2I.Mem (2 * Real.log 2) := by
  obtain ⟨h1, h2⟩ := l2_check
  have h1' := (Rat.cast_le (K := ℝ)).2 h1
  have h2' := (Rat.cast_le (K := ℝ)).2 h2
  push_cast at h1' h2'
  have a := mem_logNI 2 60
  simp only [QI.Mem, Nat.cast_ofNat] at a
  exact ⟨by simp only [l2I]; linarith [a.1], by simp only [l2I]; linarith [a.2]⟩

theorem add74_cq (x y : ℚ) : (74 : ℂ) + cq x y = cq (74 + x) y := by
  unfold cq; push_cast; ring

theorem add76_cq (x y : ℚ) : (76 : ℂ) + cq x y = cq (76 + x) y := by
  unfold cq; push_cast; ring

theorem two_log_two_re : ((2 : ℂ) * (Real.log 2 : ℂ)).re = 2 * Real.log 2 := by
  rw [show ((2 : ℂ) * (Real.log 2 : ℂ)) = ((2 * Real.log 2 : ℝ) : ℂ) by
    rw [ofReal_mul, ofReal_ofNat], ofReal_re]

theorem two_log_two_im : ((2 : ℂ) * (Real.log 2 : ℂ)).im = 0 := by
  rw [show ((2 : ℂ) * (Real.log 2 : ℂ)) = ((2 * Real.log 2 : ℝ) : ℂ) by
    rw [ofReal_mul, ofReal_ofNat], ofReal_im]

/-- **Enclosure of `e`, `e'` at `x + y i`.** -/
def ePt (x y : ℚ) (p : ℕ) : Pt :=
  let L4 := logAbsQ (74 + x) y p
  let A4 := argQ (74 + x) y p
  let L6 := logAbsQ (76 + x) y p
  let A6 := argQ (76 + x) y p
  ⟨(((smul (74 + x) L4).sub (smul y A4)).sub ((smul (76 + x) L6).sub (smul y A6))).add l2I,
    ((smul y L4).add (smul (74 + x) A4)).sub ((smul y L6).add (smul (76 + x) A6)),
    L4.sub L6, A4.sub A6⟩

theorem mem_ePt (x y : ℚ) (p : ℕ) : (ePt x y p).Mem (famE (cq x y)) (famE1 (cq x y)) := by
  have hL4 := mem_logAbsQ (74 + x) y p
  have hA4 := mem_argQ (74 + x) y p
  have hL6 := mem_logAbsQ (76 + x) y p
  have hA6 := mem_argQ (76 + x) y p
  have e4 : ((74 + cq x y) * log (74 + cq x y)) = (((1 : ℝ) : ℂ) * cq (74 + x) y *
      log (cq (74 + x) y)) := by rw [add74_cq]; simp
  have e6 : ((76 + cq x y) * log (76 + cq x y)) = (((1 : ℝ) : ℂ) * cq (76 + x) y *
      log (cq (76 + x) y)) := by rw [add76_cq]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [famE, add_re, sub_re, e4, e6, re_mul_wlog, one_mul, cq_re, cq_im]
    rw [two_log_two_re]
    exact mem_add (mem_sub (mem_sub (mem_smul _ hL4) (mem_smul _ hA4))
      (mem_sub (mem_smul _ hL6) (mem_smul _ hA6))) mem_l2I
  · simp only [famE, add_im, sub_im, e4, e6, im_mul_wlog, one_mul, cq_re, cq_im]
    rw [two_log_two_im, add_zero]
    exact mem_sub (mem_add (mem_smul _ hL4) (mem_smul _ hA4))
      (mem_add (mem_smul _ hL6) (mem_smul _ hA6))
  · simp only [famE1, sub_re, log_re, add74_cq, add76_cq]
    exact mem_sub hL4 hL6
  · simp only [famE1, sub_im, log_im, add74_cq, add76_cq]
    exact mem_sub hA4 hA6

/-- `e(u) - 2πi u`, whose real part is `Re e(u) + 2π Im u`. -/
noncomputable def famEs (u : ℂ) : ℂ := famE u - 2 * Real.pi * I * u

/-- `e'(u) - 2πi`. -/
noncomputable def famEs1 (u : ℂ) : ℂ := famE1 u - 2 * Real.pi * I

theorem famEs_re (u : ℂ) : (famEs u).re = (famE u).re + 2 * u.im * Real.pi := by
  simp [famEs, mul_re, mul_im]; ring

theorem famEs_im (u : ℂ) : (famEs u).im = (famE u).im - 2 * u.re * Real.pi := by
  simp [famEs, mul_re, mul_im]; ring

theorem famEs1_re (u : ℂ) : (famEs1 u).re = (famE1 u).re := by simp [famEs1]

theorem famEs1_im (u : ℂ) : (famEs1 u).im = (famE1 u).im - 2 * Real.pi := by simp [famEs1]

/-- **Enclosure of `e(u) - 2πi u` and `e'(u) - 2πi` at `u = x + y i`.** -/
def esPt (x y : ℚ) (p : ℕ) : Pt :=
  let P := ePt x y p
  ⟨P.re.add (smul (2 * y) piI), P.im.sub (smul (2 * x) piI), P.dre, P.dim.sub (smul 2 piI)⟩

theorem mem_esPt (x y : ℚ) (p : ℕ) : (esPt x y p).Mem (famEs (cq x y)) (famEs1 (cq x y)) := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_ePt x y p
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [famEs_re, cq_im]
    exact mem_add h1 (mem_smul' _ (by push_cast; ring) mem_piI)
  · rw [famEs_im, cq_re]
    exact mem_sub h2 (mem_smul' _ (by push_cast; ring) mem_piI)
  · rw [famEs1_re]; exact h3
  · rw [famEs1_im]
    exact mem_sub h4 (mem_smul' _ (by push_cast; ring) mem_piI)

/-! ### Exact second derivatives at a rational point -/

/-- `c · z` for rational `c` and a rational complex number `z`. -/
def qcScale (c : ℚ) (z : QC) : QC := ⟨c * z.re, c * z.im⟩

theorem toC_qcScale (c : ℚ) (z : QC) : (qcScale c z).toC = (c : ℂ) * z.toC := by
  apply Complex.ext <;> simp [qcScale, QC.toC, cq]

/-- `g''(x + y i)`, exactly. -/
def g2Q (x y : ℚ) : QC := QC.sumL famCB fun bc => qcScale bc.2 (QC.inv ⟨bc.1 + x, y⟩)

theorem toC_g2Q (x y : ℚ) : (g2Q x y).toC = famG2 (cq x y) := by
  simp only [g2Q, QC.toC_sumL, toC_qcScale, QC.toC_inv, famG2]
  congr 1
  refine List.map_congr_left fun bc _ => ?_
  simp only [QC.toC, natCast_add_cq, Rat.cast_intCast]

/-- `e''(x + y i)`, exactly. -/
def e2Q (x y : ℚ) : QC := (QC.inv ⟨74 + x, y⟩).sub (QC.inv ⟨76 + x, y⟩)

theorem toC_e2Q (x y : ℚ) : (e2Q x y).toC = famE2 (cq x y) := by
  rw [e2Q, QC.toC_sub, QC.toC_inv, QC.toC_inv]
  simp only [QC.toC, famE2, add74_cq, add76_cq]

/-! ### Bounds on boxes -/

/-- A lower bound for `‖z‖` on the box `[xl, xh] × [yl, yh]`. -/
def lowN (xl xh yl yh : ℚ) : ℚ := max (lowAbs xl xh) (lowAbs yl yh)

theorem lowAbs_le_abs {a b : ℚ} {t : ℝ} (h1 : (a : ℝ) ≤ t) (h2 : t ≤ b) :
    ((lowAbs a b : ℚ) : ℝ) ≤ |t| := by
  simp only [lowAbs, Rat.cast_max, Rat.cast_neg, Rat.cast_zero]
  refine max_le (max_le (h1.trans (le_abs_self t)) ?_) (abs_nonneg t)
  have := neg_abs_le t
  linarith

theorem lowN_le_norm {z : ℂ} {xl xh yl yh : ℚ} (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh)
    (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh) : ((lowN xl xh yl yh : ℚ) : ℝ) ≤ ‖z‖ := by
  simp only [lowN, Rat.cast_max]
  exact max_le ((lowAbs_le_abs hx.1 hx.2).trans (abs_re_le_norm z))
    ((lowAbs_le_abs hy.1 hy.2).trans (abs_im_le_norm z))

theorem lowN_shift_le_norm {z : ℂ} {xl xh yl yh : ℚ} (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh)
    (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh) (a : ℚ) :
    ((lowN (a + xl) (a + xh) yl yh : ℚ) : ℝ) ≤ ‖(a : ℂ) + z‖ := by
  refine lowN_le_norm ?_ (by simpa using hy)
  simp only [add_re, ratCast_re, Rat.cast_add]
  constructor <;> linarith [hx.1, hx.2]

theorem norm_inv_le_one_div {z : ℂ} {l : ℝ} (hl : 0 < l) (h : l ≤ ‖z‖) : ‖z⁻¹‖ ≤ 1 / l := by
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le hl h

theorem norm_inv_sq_le_one_div {z : ℂ} {l : ℝ} (hl : 0 < l) (h : l ≤ ‖z‖) :
    ‖(z ^ 2)⁻¹‖ ≤ 1 / l ^ 2 := by
  rw [norm_inv, norm_pow, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl.le h 2)

/-- An upper bound for `‖g''‖` on the box `[xl, xh] × [yl, yh]`. -/
def g2Box (xl xh yl yh : ℚ) : ℚ :=
  (famCB.map fun bc : ℕ × ℤ => |(bc.2 : ℚ)| / lowN (bc.1 + xl) (bc.1 + xh) yl yh).sum

/-- An upper bound for `‖g'''‖` on the box `[xl, xh] × [yl, yh]`. -/
def g3Box (xl xh yl yh : ℚ) : ℚ :=
  (famCB.map fun bc : ℕ × ℤ => |(bc.2 : ℚ)| / lowN (bc.1 + xl) (bc.1 + xh) yl yh ^ 2).sum

theorem natCast_eq_ratCast (b : ℕ) : (b : ℂ) = ((b : ℚ) : ℂ) := by simp

theorem norm_famG2_le_box {z : ℂ} {xl xh yl yh : ℚ} (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh)
    (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh)
    (hpos : ∀ bc ∈ famCB, 0 < lowN (bc.1 + xl) (bc.1 + xh) yl yh) :
    ‖famG2 z‖ ≤ g2Box xl xh yl yh := by
  unfold famG2 g2Box
  rw [cast_list_sum_map]
  refine norm_list_sum_map_le _ fun bc hbc => ?_
  have hl : (0 : ℝ) < (lowN (bc.1 + xl) (bc.1 + xh) yl yh : ℚ) := by exact_mod_cast hpos bc hbc
  have h1 : ‖((bc.1 : ℂ) + z)⁻¹‖ ≤ 1 / _ := norm_inv_le_one_div hl (by
    simpa only [Rat.cast_natCast] using lowN_shift_le_norm hx hy (bc.1 : ℚ))
  rw [norm_mul, Complex.norm_intCast]
  push_cast
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem norm_famG3_le_box {z : ℂ} {xl xh yl yh : ℚ} (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh)
    (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh)
    (hpos : ∀ bc ∈ famCB, 0 < lowN (bc.1 + xl) (bc.1 + xh) yl yh) :
    ‖famG3 z‖ ≤ g3Box xl xh yl yh := by
  unfold famG3 g3Box
  rw [norm_neg, cast_list_sum_map]
  refine norm_list_sum_map_le _ fun bc hbc => ?_
  have hl : (0 : ℝ) < (lowN (bc.1 + xl) (bc.1 + xh) yl yh : ℚ) := by exact_mod_cast hpos bc hbc
  have h1 : ‖(((bc.1 : ℂ) + z) ^ 2)⁻¹‖ ≤ 1 / _ := norm_inv_sq_le_one_div hl (by
    simpa only [Rat.cast_natCast] using lowN_shift_le_norm hx hy (bc.1 : ℚ))
  rw [norm_mul, Complex.norm_intCast]
  push_cast
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- An upper bound for `‖e''‖ = 2 / (‖74 + z‖ ‖76 + z‖)` on the box `[xl, xh] × [yl, yh]`. -/
def e2Box (xl xh yl yh : ℚ) : ℚ :=
  2 / (lowN (74 + xl) (74 + xh) yl yh * lowN (76 + xl) (76 + xh) yl yh)

/-- An upper bound for `‖e'''‖` on the box `[xl, xh] × [yl, yh]`. -/
def e3Box (xl xh yl yh : ℚ) : ℚ :=
  1 / lowN (74 + xl) (74 + xh) yl yh ^ 2 + 1 / lowN (76 + xl) (76 + xh) yl yh ^ 2

theorem norm_famE2_le_box {z : ℂ} {xl xh yl yh : ℚ} (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh)
    (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh) (h4 : 0 < lowN (74 + xl) (74 + xh) yl yh)
    (h6 : 0 < lowN (76 + xl) (76 + xh) yl yh) :
    ‖famE2 z‖ ≤ e2Box xl xh yl yh := by
  have k4 := lowN_shift_le_norm hx hy 74
  have k6 := lowN_shift_le_norm hx hy 76
  have h4' : (0 : ℝ) < (lowN (74 + xl) (74 + xh) yl yh : ℚ) := by exact_mod_cast h4
  have h6' : (0 : ℝ) < (lowN (76 + xl) (76 + xh) yl yh : ℚ) := by exact_mod_cast h6
  push_cast at k4 k6
  have n4 : (74 : ℂ) + z ≠ 0 := norm_pos_iff.1 (h4'.trans_le k4)
  have n6 : (76 : ℂ) + z ≠ 0 := norm_pos_iff.1 (h6'.trans_le k6)
  have e : famE2 z = 2 / ((74 + z) * (76 + z)) := by
    unfold famE2
    field_simp
    ring
  rw [e, norm_div, norm_mul, Complex.norm_ofNat]
  simp only [e2Box, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul k4 k6 h6'.le
    (norm_nonneg _))

theorem norm_famE3_le_box {z : ℂ} {xl xh yl yh : ℚ} (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh)
    (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh) (h4 : 0 < lowN (74 + xl) (74 + xh) yl yh)
    (h6 : 0 < lowN (76 + xl) (76 + xh) yl yh) :
    ‖famE3 z‖ ≤ e3Box xl xh yl yh := by
  have k4 := lowN_shift_le_norm hx hy 74
  have k6 := lowN_shift_le_norm hx hy 76
  have h4' : (0 : ℝ) < (lowN (74 + xl) (74 + xh) yl yh : ℚ) := by exact_mod_cast h4
  have h6' : (0 : ℝ) < (lowN (76 + xl) (76 + xh) yl yh : ℚ) := by exact_mod_cast h6
  push_cast at k4 k6
  unfold famE3
  rw [norm_neg]
  simp only [e3Box, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_pow]
  exact (norm_sub_le _ _).trans (add_le_add (norm_inv_sq_le_one_div h4' k4)
    (norm_inv_sq_le_one_div h6' k6))

/-- The box `[xl, xh] × [yl, yh]` lies in the slit plane (`0 < xl`, or it avoids the real axis). -/
def okBox (xl _xh yl yh : ℚ) : Bool := decide (0 < xl ∨ yh < 0 ∨ 0 < yl)

theorem mem_slitPlane_of_okBox {xl xh yl yh : ℚ} (h : okBox xl xh yl yh = true) {z : ℂ}
    (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh) (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh) : z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases of_decide_eq_true h with h | h | h
  · left; exact lt_of_lt_of_le (by exact_mod_cast h) hx.1
  · right; exact (lt_of_le_of_lt hy.2 (by exact_mod_cast h)).ne
  · right; exact (lt_of_lt_of_le (by exact_mod_cast h) hy.1).ne'

theorem lowN_pos_of_okBox {xl xh yl yh : ℚ} (h : okBox xl xh yl yh = true) {a : ℚ}
    (ha : 0 ≤ a) : 0 < lowN (a + xl) (a + xh) yl yh := by
  simp only [lowN, lowAbs]
  rcases of_decide_eq_true h with h | h | h
  · exact lt_max_of_lt_left (lt_max_of_lt_left (lt_max_of_lt_left (by linarith)))
  · exact lt_max_of_lt_right (lt_max_of_lt_left (lt_max_of_lt_right (by linarith)))
  · exact lt_max_of_lt_right (lt_max_of_lt_left (lt_max_of_lt_left h))

/-! ### Derivatives -/

theorem add_mem_slitPlane {u : ℂ} (hu : u ∈ slitPlane) {a : ℝ} (ha : 0 ≤ a) :
    (a : ℂ) + u ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hu ⊢
  simp only [add_re, ofReal_re, add_im, ofReal_im, zero_add]
  rcases hu with h | h
  · left; linarith
  · right; exact h

theorem natCast_add_mem_slitPlane {u : ℂ} (hu : u ∈ slitPlane) (b : ℕ) :
    (b : ℂ) + u ∈ slitPlane := by
  simpa using add_mem_slitPlane hu (Nat.cast_nonneg b)

theorem hasDerivAt_wlog (a : ℂ) {u : ℂ} (hu : a + u ∈ slitPlane) :
    HasDerivAt (fun v => (a + v) * log (a + v)) (log (a + u) + 1) u := by
  have h1 : HasDerivAt (fun v => a + v) 1 u := (hasDerivAt_id' u).const_add a
  have h2 := h1.clog hu
  have hne : a + u ≠ 0 := slitPlane_ne_zero hu
  convert h1.mul h2 using 1
  rw [mul_one_div_cancel hne]
  ring

theorem hasDerivAt_clog_add (a : ℂ) {u : ℂ} (hu : a + u ∈ slitPlane) :
    HasDerivAt (fun v => log (a + v)) (a + u)⁻¹ u := by
  simpa [one_div] using ((hasDerivAt_id' u).const_add a).clog hu

theorem hasDerivAt_inv_add (a : ℂ) {u : ℂ} (hu : a + u ≠ 0) :
    HasDerivAt (fun v => (a + v)⁻¹) (-((a + u) ^ 2)⁻¹) u := by
  have := ((hasDerivAt_id' u).const_add a).inv hu
  convert this using 1
  field_simp

theorem hasDerivAt_sum_wlog (L : List (ℕ × ℤ)) {u : ℂ} (hu : u ∈ slitPlane) :
    HasDerivAt
      (fun v => (L.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * ((bc.1 : ℂ) + v) * log ((bc.1 : ℂ) + v)).sum)
      (L.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * (log ((bc.1 : ℂ) + u) + 1)).sum u := by
  induction L with
  | nil => simpa using hasDerivAt_const u (0 : ℂ)
  | cons bc L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine HasDerivAt.add ?_ ih
    have := (hasDerivAt_wlog (bc.1 : ℂ) (natCast_add_mem_slitPlane hu bc.1)).const_mul
      (bc.2 : ℂ)
    simpa only [mul_assoc] using this

theorem hasDerivAt_sum_clog (L : List (ℕ × ℤ)) {u : ℂ} (hu : u ∈ slitPlane) :
    HasDerivAt (fun v => (L.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * log ((bc.1 : ℂ) + v)).sum)
      (L.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * ((bc.1 : ℂ) + u)⁻¹).sum u := by
  induction L with
  | nil => simpa using hasDerivAt_const u (0 : ℂ)
  | cons bc L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hasDerivAt_clog_add (bc.1 : ℂ) (natCast_add_mem_slitPlane hu bc.1)).const_mul
      (bc.2 : ℂ)).add ih

theorem hasDerivAt_sum_inv (L : List (ℕ × ℤ)) {u : ℂ} (hu : u ∈ slitPlane) :
    HasDerivAt (fun v => (L.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * ((bc.1 : ℂ) + v)⁻¹).sum)
      (L.map fun bc : ℕ × ℤ => (bc.2 : ℂ) * -(((bc.1 : ℂ) + u) ^ 2)⁻¹).sum u := by
  induction L with
  | nil => simpa using hasDerivAt_const u (0 : ℂ)
  | cons bc L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hasDerivAt_inv_add (bc.1 : ℂ)
      (slitPlane_ne_zero (natCast_add_mem_slitPlane hu bc.1))).const_mul (bc.2 : ℂ)).add ih

theorem hasDerivAt_famG {u : ℂ} (hu : u ∈ slitPlane) : HasDerivAt famG (famG1 u) u := by
  refine ((hasDerivAt_sum_wlog famCB hu).add_const (famKg : ℂ)).congr_deriv ?_
  simp only [famG1, famCB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

theorem hasDerivAt_famG1 {u : ℂ} (hu : u ∈ slitPlane) : HasDerivAt famG1 (famG2 u) u :=
  hasDerivAt_sum_clog famCB hu

theorem hasDerivAt_famG2 {u : ℂ} (hu : u ∈ slitPlane) : HasDerivAt famG2 (famG3 u) u := by
  refine (hasDerivAt_sum_inv famCB hu).congr_deriv ?_
  simp only [famG3, famCB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem hasDerivAt_famE {u : ℂ} (h4 : 74 + u ∈ slitPlane) (h6 : 76 + u ∈ slitPlane) :
    HasDerivAt famE (famE1 u) u := by
  refine (((hasDerivAt_wlog 74 h4).sub (hasDerivAt_wlog 76 h6)).add_const
    (2 * (Real.log 2 : ℂ))).congr_deriv ?_
  simp only [famE1]
  ring

theorem hasDerivAt_famE1 {u : ℂ} (h4 : 74 + u ∈ slitPlane) (h6 : 76 + u ∈ slitPlane) :
    HasDerivAt famE1 (famE2 u) u :=
  (hasDerivAt_clog_add 74 h4).sub (hasDerivAt_clog_add 76 h6)

theorem hasDerivAt_famE2 {u : ℂ} (h4 : 74 + u ≠ 0) (h6 : 76 + u ≠ 0) :
    HasDerivAt famE2 (famE3 u) u := by
  refine ((hasDerivAt_inv_add 74 h4).sub (hasDerivAt_inv_add 76 h6)).congr_deriv ?_
  simp only [famE3]
  ring

theorem hasDerivAt_famEs {u : ℂ} (h4 : 74 + u ∈ slitPlane) (h6 : 76 + u ∈ slitPlane) :
    HasDerivAt famEs (famEs1 u) u := by
  refine ((hasDerivAt_famE h4 h6).sub
    ((hasDerivAt_id' u).const_mul (2 * (Real.pi : ℂ) * I))).congr_deriv ?_
  simp [famEs1]

theorem hasDerivAt_famEs1 {u : ℂ} (h4 : 74 + u ∈ slitPlane) (h6 : 76 + u ∈ slitPlane) :
    HasDerivAt famEs1 (famE2 u) u :=
  (hasDerivAt_famE1 h4 h6).sub_const _

/-- The shifted box condition used for `e`. -/
def okBoxE (xl xh yl yh : ℚ) : Bool := okBox (74 + xl) (74 + xh) yl yh

theorem slit_of_okBoxE {xl xh yl yh : ℚ} (h : okBoxE xl xh yl yh = true) {z : ℂ}
    (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh) (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh) :
    74 + z ∈ slitPlane ∧ 76 + z ∈ slitPlane := by
  have h74 : (74 : ℂ) + z ∈ slitPlane := by
    refine mem_slitPlane_of_okBox h ?_ (by simpa using hy)
    simp only [add_re, re_ofNat, Rat.cast_add, Rat.cast_ofNat]
    constructor <;> linarith [hx.1, hx.2]
  refine ⟨h74, ?_⟩
  have := add_mem_slitPlane h74 (a := 2) (by norm_num)
  rw [show ((2 : ℝ) : ℂ) + (74 + z) = 76 + z by push_cast; ring] at this
  exact this

/-! ### Taylor bounds -/

theorem mem_segment_param {a w : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    a + (t : ℂ) * (w - a) ∈ segment ℝ a w := by
  rw [segment_eq_image']
  exact ⟨t, ht, by simp [Complex.real_smul]⟩

/-- **Second-order Taylor bound for the real part.** If `Φ` has derivative `Φ'`, `Φ'` has
derivative `Φ''` and `‖Φ''‖ ≤ B` on the segment `[a, w]`, then
`Re Φ(w) ≤ Re Φ(a) + Re (Φ'(a) (w - a)) + B ‖w - a‖² / 2`. -/
theorem re_le_taylor {Φ Φ' Φ'' : ℂ → ℂ} {a w : ℂ} {B : ℝ}
    (h : ∀ z ∈ segment ℝ a w, HasDerivAt Φ (Φ' z) z ∧ HasDerivAt Φ' (Φ'' z) z ∧ ‖Φ'' z‖ ≤ B) :
    (Φ w).re ≤ (Φ a).re + (Φ' a * (w - a)).re + B * ‖w - a‖ ^ 2 / 2 := by
  have hconv : Convex ℝ (segment ℝ a w) := convex_segment a w
  have ha : a ∈ segment ℝ a w := left_mem_segment ℝ a w
  have hlip : ∀ z ∈ segment ℝ a w, ‖Φ' z - Φ' a‖ ≤ B * ‖z - a‖ := fun z hz =>
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v hv => (h v hv).2.1.hasDerivWithinAt) (fun v hv => (h v hv).2.2) ha hz
  set ψ : ℝ → ℂ := fun t => Φ (a + (t : ℂ) * (w - a)) - Φ a - Φ' a * (w - a) * t with hψ
  have hψd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt ψ ((Φ' (a + (t : ℂ) * (w - a)) - Φ' a) * (w - a)) t := by
    intro t ht
    have h1 := (h _ (mem_segment_param ht)).1.comp t (hasDerivAt_line a (w - a) t)
    have h2 := (hasDerivAt_ofReal' t).const_mul (Φ' a * (w - a))
    have h3 : HasDerivAt (fun t : ℝ => Φ (a + (t : ℂ) * (w - a)) - Φ a - Φ' a * (w - a) * t)
        (Φ' (a + ↑t * (w - a)) * (w - a) - Φ' a * (w - a) * 1) t := (h1.sub_const (Φ a)).sub h2
    exact h3.congr_deriv (by ring)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ) (a := 0) (b := 1)
    (f' := fun t => (Φ' (a + (t : ℂ) * (w - a)) - Φ' a) * (w - a))
    (B := fun t => B * ‖w - a‖ ^ 2 * t ^ 2 / 2) (B' := fun t => B * ‖w - a‖ ^ 2 * t)
    (fun t ht => (hψd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hψd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (by simp [hψ])
    (fun t => by
      convert ((hasDerivAt_pow 2 t).const_mul (B * ‖w - a‖ ^ 2)).div_const 2 using 1
      push_cast; ring)
    (fun t ht => by
      rw [norm_mul]
      have := hlip _ (mem_segment_param (Ico_subset_Icc_self ht))
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht.1] at this
      calc ‖Φ' (a + ↑t * (w - a)) - Φ' a‖ * ‖w - a‖ ≤ B * (t * ‖w - a‖) * ‖w - a‖ := by gcongr
        _ = B * ‖w - a‖ ^ 2 * t := by ring)
    (right_mem_Icc.2 zero_le_one)
  simp only [hψ, ofReal_one, one_mul, mul_one, add_sub_cancel, one_pow] at key
  have := (re_le_norm _).trans key
  simp only [sub_re] at this
  linarith

/-- A convex quadratic on `[0, l]` is bounded by the maximum of its endpoint values. -/
theorem quad_le_max {σ l D K : ℝ} (hσ : 0 ≤ σ) (hσl : σ ≤ l) (hK : 0 ≤ K) :
    σ * D + K * σ ^ 2 ≤ max 0 (l * D + K * l ^ 2) := by
  rcases eq_or_lt_of_le (hσ.trans hσl) with hl | hl
  · have : σ = 0 := by linarith
    subst this
    simp
  · have key : σ * D + K * σ ^ 2 ≤ (σ / l) * (l * D + K * l ^ 2) := by
      have e : (σ / l) * (l * D + K * l ^ 2) = σ * D + K * σ * l := by field_simp
      rw [e]
      nlinarith [mul_nonneg hK (mul_nonneg hσ (sub_nonneg.2 hσl))]
    have h01 : σ / l ≤ 1 := (div_le_one hl).2 hσl
    have h0 : 0 ≤ σ / l := div_nonneg hσ hl.le
    refine key.trans ?_
    rcases le_total 0 (l * D + K * l ^ 2) with h | h
    · exact (mul_le_of_le_one_left h h01).trans (le_max_right _ _)
    · exact (mul_nonpos_of_nonneg_of_nonpos h0 h).trans (le_max_left _ _)

/-- **One-sided bound along a direction.** If `Re Φ(u) ≤ R`, `Re (Φ'(u) e) ≤ D` and `Φ` is twice
differentiable with `‖Φ''‖ ≤ B` on `[u, u + σ e]`, `0 ≤ σ ≤ l`, then
`Re Φ(u + σ e) ≤ R + max 0 (l D + (B ‖e‖² / 2) l²)`. -/
theorem re_le_quad {Φ Φ' Φ'' : ℂ → ℂ} {u e : ℂ} {B R D l σ : ℝ} (hσ : 0 ≤ σ) (hσl : σ ≤ l)
    (hR : (Φ u).re ≤ R) (hD : (Φ' u * e).re ≤ D)
    (h : ∀ z ∈ segment ℝ u (u + σ * e),
      HasDerivAt Φ (Φ' z) z ∧ HasDerivAt Φ' (Φ'' z) z ∧ ‖Φ'' z‖ ≤ B) :
    (Φ (u + σ * e)).re ≤ R + max 0 (l * D + B * ‖e‖ ^ 2 / 2 * l ^ 2) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (h u (left_mem_segment ℝ _ _)).2.2
  have ht := re_le_taylor h
  rw [add_sub_cancel_left] at ht
  have e1 : (Φ' u * ((σ : ℂ) * e)).re = σ * (Φ' u * e).re := by
    rw [mul_left_comm]; exact re_ofReal_mul σ _
  have e2 : ‖(σ : ℂ) * e‖ ^ 2 = σ ^ 2 * ‖e‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hq := quad_le_max (D := D) (K := B * ‖e‖ ^ 2 / 2) hσ hσl (by positivity)
  have h3 : σ * (Φ' u * e).re ≤ σ * D := mul_le_mul_of_nonneg_left hD hσ
  rw [e1, e2] at ht
  linarith

/-! ### The segment lemma (Lemma 4.8) as a Bool checker -/

/-- `[Re (Φ'(u) (ex + ey i))]` from an enclosure `P` of `Φ'(u)`. -/
def dirI (P : Pt) (ex ey : ℚ) : QI := (smul ex P.dre).sub (smul ey P.dim)

theorem mem_dirI {P : Pt} {v d : ℂ} (hP : P.Mem v d) (ex ey : ℚ) :
    (dirI P ex ey).Mem (d * cq ex ey).re := by
  have e : (d * cq ex ey).re = ex * d.re - ey * d.im := by simp [mul_re]; ring
  rw [e]
  exact mem_sub (mem_smul _ hP.2.2.1) (mem_smul _ hP.2.2.2)

/-- `ev` encloses `Φ`, `Φ'` at every rational point. -/
def EvOK (Φ Φ' : ℂ → ℂ) (ev : ℚ → ℚ → Pt) : Prop :=
  ∀ x y : ℚ, (ev x y).Mem (Φ (cq x y)) (Φ' (cq x y))

/-- On every box `[xl, xh] × [yl, yh]` accepted by `ok`, `Φ' = dΦ`, `Φ'' = dΦ'` and
`‖Φ''‖ ≤ bnd xl xh yl yh`. -/
def BoxOK (Φ Φ' Φ'' : ℂ → ℂ) (bnd : ℚ → ℚ → ℚ → ℚ → ℚ) (ok : ℚ → ℚ → ℚ → ℚ → Bool) : Prop :=
  ∀ xl xh yl yh : ℚ, ok xl xh yl yh = true → ∀ z : ℂ, (xl : ℝ) ≤ z.re → z.re ≤ xh →
    (yl : ℝ) ≤ z.im → z.im ≤ yh →
      HasDerivAt Φ (Φ' z) z ∧ HasDerivAt Φ' (Φ'' z) z ∧ ‖Φ'' z‖ ≤ bnd xl xh yl yh

theorem gEvOK (p : ℕ) : EvOK famG famG1 (fun x y => gPt x y p) := fun x y => mem_gPt x y p

theorem gBoxOK : BoxOK famG famG1 famG2 g2Box okBox := by
  intro xl xh yl yh hok z h1 h2 h3 h4
  have hz := mem_slitPlane_of_okBox hok ⟨h1, h2⟩ ⟨h3, h4⟩
  refine ⟨hasDerivAt_famG hz, hasDerivAt_famG1 hz, norm_famG2_le_box ⟨h1, h2⟩ ⟨h3, h4⟩ ?_⟩
  intro bc _
  exact lowN_pos_of_okBox hok (Nat.cast_nonneg _)

theorem esEvOK (p : ℕ) : EvOK famEs famEs1 (fun x y => esPt x y p) := fun x y => mem_esPt x y p

theorem esBoxOK : BoxOK famEs famEs1 famE2 e2Box okBoxE := by
  intro xl xh yl yh hok z h1 h2 h3 h4
  obtain ⟨k4, k6⟩ := slit_of_okBoxE hok ⟨h1, h2⟩ ⟨h3, h4⟩
  refine ⟨hasDerivAt_famEs k4 k6, hasDerivAt_famEs1 k4 k6,
    norm_famE2_le_box ⟨h1, h2⟩ ⟨h3, h4⟩ ?_ ?_⟩
  · exact lowN_pos_of_okBox hok (a := 0) le_rfl |>.trans_le (by simp)
  · have := lowN_pos_of_okBox (a := 2) hok (by norm_num)
    rwa [show (2 : ℚ) + (74 + xl) = 76 + xl by ring,
      show (2 : ℚ) + (74 + xh) = 76 + xh by ring] at this

/-- One piece `[t, s]` of a grid on the segment `A + [0, 1] e`, `A = ax + ay i`, `e = ex + ey i`:
`P`, `Q` enclose `Φ`, `Φ'` at the endpoints; each endpoint controls half of the piece. -/
def pieceOK (bnd : ℚ → ℚ → ℚ → ℚ → ℚ) (ok : ℚ → ℚ → ℚ → ℚ → Bool) (ax ay ex ey T t : ℚ)
    (P : Pt) (s : ℚ) (Q : Pt) : Bool :=
  let xu := ax + t * ex
  let yu := ay + t * ey
  let xv := ax + s * ex
  let yv := ay + s * ey
  let xl := min xu xv
  let xh := max xu xv
  let yl := min yu yv
  let yh := max yu yv
  let h := s - t
  let K := bnd xl xh yl yh * (ex ^ 2 + ey ^ 2) / 2
  ok xl xh yl yh && decide (0 < h ∧
    P.re.hi + max 0 (h / 2 * (dirI P ex ey).hi + K * (h / 2) ^ 2) ≤ T ∧
    Q.re.hi + max 0 (h / 2 * -(dirI Q ex ey).lo + K * (h / 2) ^ 2) ≤ T)

/-- The grid `0 = t₀ < t < t₁ < ⋯ < 1` of the segment, evaluated from the point `t`. -/
def segGo (ev : ℚ → ℚ → Pt) (bnd : ℚ → ℚ → ℚ → ℚ → ℚ) (ok : ℚ → ℚ → ℚ → ℚ → Bool)
    (ax ay ex ey T : ℚ) : ℚ → Pt → List ℚ → Bool
  | t, P, [] => pieceOK bnd ok ax ay ex ey T t P 1 (ev (ax + 1 * ex) (ay + 1 * ey))
  | t, P, s :: l =>
    pieceOK bnd ok ax ay ex ey T t P s (ev (ax + s * ex) (ay + s * ey)) &&
      segGo ev bnd ok ax ay ex ey T s (ev (ax + s * ex) (ay + s * ey)) l

/-- **The segment check**: `Re Φ ≤ T` on `A + [0, 1] e`, with interior grid parameters `ts`. -/
def chkSeg (ev : ℚ → ℚ → Pt) (bnd : ℚ → ℚ → ℚ → ℚ → ℚ) (ok : ℚ → ℚ → ℚ → ℚ → Bool)
    (ax ay ex ey T : ℚ) (ts : List ℚ) : Bool :=
  segGo ev bnd ok ax ay ex ey T 0 (ev (ax + 0 * ex) (ay + 0 * ey)) ts

theorem cq_line (ax ay ex ey t : ℚ) :
    cq (ax + t * ex) (ay + t * ey) = cq ax ay + ((t : ℝ) : ℂ) * cq ex ey := by
  apply Complex.ext <;> simp

theorem between_of_le {a b t s τ : ℝ} (h1 : t ≤ τ) (h2 : τ ≤ s) :
    min (a + t * b) (a + s * b) ≤ a + τ * b ∧ a + τ * b ≤ max (a + t * b) (a + s * b) := by
  rcases le_total 0 b with hb | hb
  · have k1 : t * b ≤ τ * b := mul_le_mul_of_nonneg_right h1 hb
    have k2 : τ * b ≤ s * b := mul_le_mul_of_nonneg_right h2 hb
    exact ⟨(min_le_left _ _).trans (by linarith), le_trans (by linarith) (le_max_right _ _)⟩
  · have k1 : τ * b ≤ t * b := mul_le_mul_of_nonpos_right h1 hb
    have k2 : s * b ≤ τ * b := mul_le_mul_of_nonpos_right h2 hb
    exact ⟨(min_le_right _ _).trans (by linarith), le_trans (by linarith) (le_max_left _ _)⟩

/-- Points of a sub-segment of the line `A + ℝ e`. -/
theorem mem_segment_line {A e z : ℂ} {τ₁ τ₂ : ℝ} (hz : z ∈ segment ℝ (A + τ₁ * e) (A + τ₂ * e)) :
    ∃ τ : ℝ, min τ₁ τ₂ ≤ τ ∧ τ ≤ max τ₁ τ₂ ∧ z = A + τ * e := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  refine ⟨τ₁ + θ * (τ₂ - τ₁), ?_, ?_, ?_⟩
  · have := between_of_le (a := τ₁) (b := τ₂ - τ₁) (t := 0) (s := 1) hθ.1 hθ.2
    simp only [zero_mul, add_zero, one_mul, add_sub_cancel] at this
    exact this.1
  · have := between_of_le (a := τ₁) (b := τ₂ - τ₁) (t := 0) (s := 1) hθ.1 hθ.2
    simp only [zero_mul, add_zero, one_mul, add_sub_cancel] at this
    exact this.2
  · simp only [Complex.real_smul]; push_cast; ring

variable {Φ Φ' Φ'' : ℂ → ℂ} {ev : ℚ → ℚ → Pt} {bnd : ℚ → ℚ → ℚ → ℚ → ℚ}
  {ok : ℚ → ℚ → ℚ → ℚ → Bool}

theorem pieceOK_sound (hbox : BoxOK Φ Φ' Φ'' bnd ok) {ax ay ex ey T t s : ℚ} {P Q : Pt}
    (hP : P.Mem (Φ (cq (ax + t * ex) (ay + t * ey))) (Φ' (cq (ax + t * ex) (ay + t * ey))))
    (hQ : Q.Mem (Φ (cq (ax + s * ex) (ay + s * ey))) (Φ' (cq (ax + s * ex) (ay + s * ey))))
    (h : pieceOK bnd ok ax ay ex ey T t P s Q = true) :
    ∀ τ : ℝ, (t : ℝ) ≤ τ → τ ≤ s → (Φ (cq ax ay + τ * cq ex ey)).re ≤ T := by
  simp only [pieceOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hh, hl, hr⟩ := h
  set A := cq ax ay
  set e := cq ex ey
  set B : ℚ := bnd (min (ax + t * ex) (ax + s * ex)) (max (ax + t * ex) (ax + s * ex))
    (min (ay + t * ey) (ay + s * ey)) (max (ay + t * ey) (ay + s * ey)) with hB
  -- every point of the piece lies in the box
  have hin : ∀ τ : ℝ, (t : ℝ) ≤ τ → τ ≤ s → ∀ z : ℂ, z = A + τ * e →
      HasDerivAt Φ (Φ' z) z ∧ HasDerivAt Φ' (Φ'' z) z ∧ ‖Φ'' z‖ ≤ (B : ℝ) := by
    intro τ h1 h2 z hz
    have hre : z.re = ax + τ * ex := by rw [hz]; simp [A, e]
    have him : z.im = ay + τ * ey := by rw [hz]; simp [A, e]
    obtain ⟨x1, x2⟩ := between_of_le (a := (ax : ℝ)) (b := ex) h1 h2
    obtain ⟨y1, y2⟩ := between_of_le (a := (ay : ℝ)) (b := ey) h1 h2
    refine hbox _ _ _ _ hok z ?_ ?_ ?_ ?_
    · push_cast; rw [hre]; exact x1
    · push_cast; rw [hre]; exact x2
    · push_cast; rw [him]; exact y1
    · push_cast; rw [him]; exact y2
  have hseg : ∀ τ₁ τ₂ : ℝ, (t : ℝ) ≤ τ₁ → τ₁ ≤ s → (t : ℝ) ≤ τ₂ → τ₂ ≤ s →
      ∀ z ∈ segment ℝ (A + τ₁ * e) (A + τ₂ * e),
        HasDerivAt Φ (Φ' z) z ∧ HasDerivAt Φ' (Φ'' z) z ∧ ‖Φ'' z‖ ≤ (B : ℝ) := by
    intro τ₁ τ₂ a1 a2 b1 b2 z hz
    obtain ⟨τ, k1, k2, rfl⟩ := mem_segment_line hz
    exact hin τ (le_trans (le_min a1 b1) k1) (k2.trans (max_le a2 b2)) _ rfl
  have hts : (t : ℝ) < s := by
    have : (0 : ℚ) < s - t := hh
    exact_mod_cast (show t < s by linarith)
  have hnorm : ‖e‖ ^ 2 = ((ex ^ 2 + ey ^ 2 : ℚ) : ℝ) := by
    rw [← normSq_eq_norm_sq, normSq_apply]; simp [e]; ring
  have hK : ((B * (ex ^ 2 + ey ^ 2) / 2 : ℚ) : ℝ) = (B : ℝ) * ‖e‖ ^ 2 / 2 := by
    rw [hnorm]; push_cast; ring
  intro τ h1 h2
  rcases le_total τ (((t : ℝ) + s) / 2) with hτ | hτ
  · -- left half: from `u = A + t e`
    have hu : cq (ax + t * ex) (ay + t * ey) = A + ((t : ℝ) : ℂ) * e := cq_line _ _ _ _ _
    have hw : A + (τ : ℂ) * e = (A + ((t : ℝ) : ℂ) * e) + ((τ - t : ℝ) : ℂ) * e := by
      push_cast; ring
    rw [hw]
    have hR : (Φ (A + ((t : ℝ) : ℂ) * e)).re ≤ (P.re.hi : ℝ) := by rw [← hu]; exact hP.1.2
    have hD : (Φ' (A + ((t : ℝ) : ℂ) * e) * e).re ≤ ((dirI P ex ey).hi : ℝ) := by
      rw [← hu]; exact (mem_dirI hP ex ey).2
    have k := re_le_quad (Φ'' := Φ'') (B := (B : ℝ)) (l := ((s - t : ℚ) : ℝ) / 2)
      (sub_nonneg.2 h1) (by push_cast; linarith) hR hD (by
        rw [← hw]
        exact hseg t τ le_rfl hts.le h1 h2)
    refine k.trans ?_
    have hl' := (Rat.cast_le (K := ℝ)).2 hl
    push_cast at hl' ⊢
    rw [hnorm] at *
    push_cast at *
    linarith
  · -- right half: from `v = A + s e`
    have hv : cq (ax + s * ex) (ay + s * ey) = A + ((s : ℝ) : ℂ) * e := cq_line _ _ _ _ _
    have hw : A + (τ : ℂ) * e = (A + ((s : ℝ) : ℂ) * e) + ((s - τ : ℝ) : ℂ) * (-e) := by
      push_cast; ring
    rw [hw]
    have hR : (Φ (A + ((s : ℝ) : ℂ) * e)).re ≤ (Q.re.hi : ℝ) := by rw [← hv]; exact hQ.1.2
    have hD : (Φ' (A + ((s : ℝ) : ℂ) * e) * -e).re ≤ -((dirI Q ex ey).lo : ℝ) := by
      rw [mul_neg, neg_re, neg_le_neg_iff, ← hv]; exact (mem_dirI hQ ex ey).1
    have k := re_le_quad (Φ'' := Φ'') (B := (B : ℝ)) (l := ((s - t : ℚ) : ℝ) / 2)
      (sub_nonneg.2 h2) (by push_cast; linarith) hR hD (by
        rw [← hw]
        exact hseg s τ hts.le le_rfl h1 h2)
    rw [norm_neg] at k
    refine k.trans ?_
    have hr' := (Rat.cast_le (K := ℝ)).2 hr
    push_cast at hr' ⊢
    rw [hnorm] at *
    push_cast at *
    linarith

theorem segGo_sound (hev : EvOK Φ Φ' ev) (hbox : BoxOK Φ Φ' Φ'' bnd ok) {ax ay ex ey T : ℚ} :
    ∀ (l : List ℚ) (t : ℚ), segGo ev bnd ok ax ay ex ey T t (ev (ax + t * ex) (ay + t * ey)) l =
      true → ∀ τ : ℝ, (t : ℝ) ≤ τ → τ ≤ 1 → (Φ (cq ax ay + τ * cq ex ey)).re ≤ T
  | [], t, h => by
    intro τ h1 h2
    exact pieceOK_sound hbox (hev _ _) (hev _ _) h τ h1 (by simpa using h2)
  | s :: l, t, h => by
    intro τ h1 h2
    simp only [segGo, Bool.and_eq_true] at h
    rcases le_total τ s with hτ | hτ
    · exact pieceOK_sound hbox (hev _ _) (hev _ _) h.1 τ h1 hτ
    · exact segGo_sound hev hbox l s h.2 τ hτ h2

/-- **Soundness of the segment check** (Lemma 4.8 of the note). -/
theorem chkSeg_sound (hev : EvOK Φ Φ' ev) (hbox : BoxOK Φ Φ' Φ'' bnd ok) {ax ay ex ey T : ℚ}
    {ts : List ℚ} (h : chkSeg ev bnd ok ax ay ex ey T ts = true) :
    ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → (Φ (cq ax ay + τ * cq ex ey)).re ≤ T := by
  intro τ h1 h2
  exact segGo_sound hev hbox ts 0 h τ (by simpa using h1) h2

/-! ### Rectangles: the maximum principle -/

/-- **Maximum principle for `Re Φ`** on a compact set. -/
theorem re_le_of_frontier {Φ : ℂ → ℂ} {U : Set ℂ} (hU : Bornology.IsBounded U) (hc : IsClosed U)
    (hd : ∀ z ∈ U, DifferentiableAt ℂ Φ z) {T : ℝ} (hb : ∀ z ∈ frontier U, (Φ z).re ≤ T) :
    ∀ z ∈ U, (Φ z).re ≤ T := by
  intro z hz
  have hdc : DiffContOnCl ℂ (fun z => exp (Φ z)) U := by
    refine ⟨fun w hw => (hd w hw).cexp.differentiableWithinAt, ?_⟩
    rw [hc.closure_eq]
    exact fun w hw => (hd w hw).cexp.continuousAt.continuousWithinAt
  have := Complex.norm_le_of_forall_mem_frontier_norm_le hU hdc (C := Real.exp T)
    (fun w hw => by rw [Complex.norm_exp]; exact Real.exp_le_exp.2 (hb w hw)) (subset_closure hz)
  rw [Complex.norm_exp] at this
  exact Real.exp_le_exp.1 this

/-- **The rectangle check**: `Re Φ ≤ T` on `[x1, x2] × [y1, y2]` from its four edges. -/
def chkRect (ev : ℚ → ℚ → Pt) (bnd : ℚ → ℚ → ℚ → ℚ → ℚ) (ok : ℚ → ℚ → ℚ → ℚ → Bool)
    (x1 x2 y1 y2 T : ℚ) (tsB tsT tsL tsR : List ℚ) : Bool :=
  ok x1 x2 y1 y2 && decide (x1 < x2 ∧ y1 < y2) &&
    chkSeg ev bnd ok x1 y1 (x2 - x1) 0 T tsB && chkSeg ev bnd ok x1 y2 (x2 - x1) 0 T tsT &&
    chkSeg ev bnd ok x1 y1 0 (y2 - y1) T tsL && chkSeg ev bnd ok x2 y1 0 (y2 - y1) T tsR

theorem isBounded_rect (x1 x2 y1 y2 : ℝ) : Bornology.IsBounded (Icc x1 x2 ×ℂ Icc y1 y2) := by
  refine (isBounded_closedBall (x := (0 : ℂ)) (r := |x1| + |x2| + |y1| + |y2|)).subset ?_
  intro z ⟨hx, hy⟩
  rw [mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  have h1 : |z.re| ≤ |x1| + |x2| := abs_le.2
    ⟨by linarith [neg_abs_le x1, abs_nonneg x2, hx.1],
      by linarith [le_abs_self x2, abs_nonneg x1, hx.2]⟩
  have h2 : |z.im| ≤ |y1| + |y2| := abs_le.2
    ⟨by linarith [neg_abs_le y1, abs_nonneg y2, hy.1],
      by linarith [le_abs_self y2, abs_nonneg y1, hy.2]⟩
  linarith

theorem edge_h {z : ℂ} {x1 x2 y : ℚ} (hx : (x1 : ℝ) < x2) (him : z.im = y) :
    z = cq x1 y + (((z.re - x1) / (x2 - x1) : ℝ) : ℂ) * cq (x2 - x1) 0 := by
  have hne : (x2 : ℝ) - x1 ≠ 0 := by linarith
  apply Complex.ext
  · simp only [add_re, cq_re, mul_re, ofReal_re, ofReal_im, cq_im]
    push_cast
    field_simp
    ring
  · simp only [add_im, cq_im, mul_im, ofReal_re, ofReal_im, cq_re]
    push_cast
    rw [him]
    ring

theorem edge_v {z : ℂ} {x y1 y2 : ℚ} (hy : (y1 : ℝ) < y2) (hre : z.re = x) :
    z = cq x y1 + (((z.im - y1) / (y2 - y1) : ℝ) : ℂ) * cq 0 (y2 - y1) := by
  have hne : (y2 : ℝ) - y1 ≠ 0 := by linarith
  apply Complex.ext
  · simp only [add_re, cq_re, mul_re, ofReal_re, ofReal_im, cq_im]
    push_cast
    rw [hre]
    ring
  · simp only [add_im, cq_im, mul_im, ofReal_re, ofReal_im, cq_re]
    push_cast
    field_simp
    ring

/-- **Soundness of the rectangle check** (maximum principle + segment lemma on the edges). -/
theorem chkRect_sound (hev : EvOK Φ Φ' ev) (hbox : BoxOK Φ Φ' Φ'' bnd ok)
    {x1 x2 y1 y2 T : ℚ} {tsB tsT tsL tsR : List ℚ}
    (h : chkRect ev bnd ok x1 x2 y1 y2 T tsB tsT tsL tsR = true) :
    ∀ z : ℂ, (x1 : ℝ) ≤ z.re → z.re ≤ x2 → (y1 : ℝ) ≤ z.im → z.im ≤ y2 → (Φ z).re ≤ T := by
  simp only [chkRect, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hok, hx, hy⟩, hB⟩, hT⟩, hL⟩, hR⟩ := h
  have hx' : (x1 : ℝ) < x2 := by exact_mod_cast hx
  have hy' : (y1 : ℝ) < y2 := by exact_mod_cast hy
  set U := Icc (x1 : ℝ) x2 ×ℂ Icc (y1 : ℝ) y2 with hU
  have hdiff : ∀ z ∈ U, DifferentiableAt ℂ Φ z := fun z hz =>
    (hbox _ _ _ _ hok z hz.1.1 hz.1.2 hz.2.1 hz.2.2).1.differentiableAt
  have hfr : ∀ z ∈ frontier U, (Φ z).re ≤ T := by
    intro z hz
    rw [hU, frontier_reProdIm, closure_Icc, closure_Icc, frontier_Icc hx'.le,
      frontier_Icc hy'.le] at hz
    rcases hz with ⟨hzx, hzy⟩ | ⟨hzx, hzy⟩
    · -- horizontal edges
      simp only [mem_preimage, mem_Icc, mem_insert_iff, mem_singleton_iff] at hzx hzy
      have hτ0 : 0 ≤ (z.re - x1) / (x2 - x1) := div_nonneg (by linarith [hzx.1]) (by linarith)
      have hτ1 : (z.re - x1) / (x2 - x1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith [hzx.2])
      rcases hzy with hzy | hzy
      · rw [edge_h hx' hzy]; exact chkSeg_sound hev hbox hB _ hτ0 hτ1
      · rw [edge_h hx' hzy]; exact chkSeg_sound hev hbox hT _ hτ0 hτ1
    · -- vertical edges
      simp only [mem_preimage, mem_Icc, mem_insert_iff, mem_singleton_iff] at hzx hzy
      have hτ0 : 0 ≤ (z.im - y1) / (y2 - y1) := div_nonneg (by linarith [hzy.1]) (by linarith)
      have hτ1 : (z.im - y1) / (y2 - y1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith [hzy.2])
      rcases hzx with hzx | hzx
      · rw [edge_v hy' hzx]; exact chkSeg_sound hev hbox hL _ hτ0 hτ1
      · rw [edge_v hy' hzx]; exact chkSeg_sound hev hbox hR _ hτ0 hτ1
  intro z h1 h2 h3 h4
  exact re_le_of_frontier (isBounded_rect _ _ _ _) (isClosed_Icc.reProdIm isClosed_Icc) hdiff hfr
    z ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-! ### Monotonicity on vertical rays -/

/-- If `Im Φ' ≤ 0` on the ray `x - i [y₀, ∞)`, then `y ↦ Re Φ(x - i y)` is antitone there. -/
theorem re_antitone_ray {Φ Φ' : ℂ → ℂ} {x y₀ : ℝ}
    (hd : ∀ y : ℝ, y₀ ≤ y → HasDerivAt Φ (Φ' (x - y * I)) (x - y * I))
    (hneg : ∀ y : ℝ, y₀ < y → (Φ' (x - y * I)).im ≤ 0) {y : ℝ} (hy : y₀ ≤ y) :
    (Φ (x - y * I)).re ≤ (Φ (x - y₀ * I)).re := by
  set f : ℝ → ℝ := fun y => (Φ (x - y * I)).re with hf
  have hderiv : ∀ y : ℝ, y₀ ≤ y → HasDerivAt f (Φ' (x - y * I)).im y := by
    intro y hy
    have hpath : HasDerivAt (fun y : ℝ => (x : ℂ) - (y : ℂ) * I) (-I) y := by
      simpa using ((hasDerivAt_ofReal' y).mul_const I).const_sub (x : ℂ)
    have h1 := (hd y hy).comp y hpath
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h1
    simp only [Complex.reCLM_apply, Function.comp_def] at h2
    convert h2 using 1
    simp
  have hanti : AntitoneOn f (Ici y₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici y₀)
      (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ici]
      exact fun y hy => (hderiv y (le_of_lt hy)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro y hy
      rw [(hderiv y (le_of_lt hy)).deriv]
      exact hneg y hy
  exact hanti self_mem_Ici hy hy

/-! ### The phase function `Fd = r g + e - 2πi u` of `η^(r)` -/

/-- Scaling of an enclosure by a rational number. -/
def Pt.smul (c : ℚ) (P : Pt) : Pt :=
  ⟨QI.smul c P.re, QI.smul c P.im, QI.smul c P.dre, QI.smul c P.dim⟩

theorem Pt.mem_smul (c : ℚ) {P : Pt} {v d : ℂ} (h : P.Mem v d) :
    (P.smul c).Mem ((c : ℂ) * v) ((c : ℂ) * d) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e : ((c : ℚ) : ℂ) = (((c : ℚ) : ℝ) : ℂ) := by simp
  rw [e]
  exact ⟨by rw [re_ofReal_mul]; exact QI.mem_smul c h1,
    by rw [im_ofReal_mul]; exact QI.mem_smul c h2,
    by rw [re_ofReal_mul]; exact QI.mem_smul c h3,
    by rw [im_ofReal_mul]; exact QI.mem_smul c h4⟩

/-- **Enclosure of `r g(u) + e(u) - 2πi u` and `r g'(u) + e'(u) - 2πi` at `u = x + y i`.** -/
def FPt (r : ℕ) (x y : ℚ) (p : ℕ) : Pt := ((gPt x y p).smul r).add (esPt x y p)

theorem mem_FPt (r : ℕ) (x y : ℚ) (p : ℕ) :
    (FPt r x y p).Mem (r * famG (cq x y) + famEs (cq x y))
      (r * famG1 (cq x y) + famEs1 (cq x y)) := by
  have h := Pt.mem_add (Pt.mem_smul (r : ℚ) (mem_gPt x y p)) (mem_esPt x y p)
  simp only [Rat.cast_natCast] at h
  exact h

theorem Fd_eq_famEs {r : ℕ} (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    (fam r).Fd u = r * famG u + famEs u := by
  rw [Fam.Fd_eq hr hu, famEs]
  ring

theorem Fd'_eq_famEs1 {r : ℕ} (hr : 1 ≤ r) {u : ℂ} (hu : u.im < 0) :
    (fam r).f' u + I * (((fam r).r : ℂ) - 2) * Real.pi = r * famG1 u + famEs1 u := by
  rw [Fam.f'_eq hr hu, Fam.r_eq, famEs1]
  ring

/-- `FPt` encloses `Fd` of `η^(r)` and its derivative `f' + i(r-2)π` on the lower half plane. -/
theorem mem_FPt_Fd {r : ℕ} (hr : 1 ≤ r) {x y : ℚ} (hy : y < 0) (p : ℕ) :
    (FPt r x y p).Mem ((fam r).Fd (cq x y))
      ((fam r).f' (cq x y) + I * (((fam r).r : ℂ) - 2) * Real.pi) := by
  have hu : (cq x y).im < 0 := by rw [cq_im]; exact_mod_cast hy
  rw [Fd_eq_famEs hr hu, Fd'_eq_famEs1 hr hu]
  exact mem_FPt r x y p

/-- `f''(x + y i) = r g''(x + y i) + e''(x + y i)`, exactly. -/
def F2Q (r : ℕ) (x y : ℚ) : QC := ((g2Q x y).nsmul r).add (e2Q x y)

theorem toC_F2Q {r : ℕ} (hr : 1 ≤ r) (x y : ℚ) : (F2Q r x y).toC = (fam r).f'' (cq x y) := by
  rw [F2Q, QC.toC_add, QC.toC_nsmul, toC_g2Q, toC_e2Q, Fam.f''_eq hr]

/-- An upper bound for `‖f''‖ = ‖r g'' + e''‖` on the box `[xl, xh] × [yl, yh]`. -/
def F2Box (r : ℕ) (xl xh yl yh : ℚ) : ℚ := r * g2Box xl xh yl yh + e2Box xl xh yl yh

/-- An upper bound for `‖f'''‖ = ‖r g''' + e'''‖` on the box `[xl, xh] × [yl, yh]`. -/
def F3Box (r : ℕ) (xl xh yl yh : ℚ) : ℚ := r * g3Box xl xh yl yh + e3Box xl xh yl yh

theorem norm_f''_le_box {r : ℕ} (hr : 1 ≤ r) {z : ℂ} {xl xh yl yh : ℚ}
    (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh) (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh)
    (hpos : ∀ bc ∈ famCB, 0 < lowN (bc.1 + xl) (bc.1 + xh) yl yh)
    (h4 : 0 < lowN (74 + xl) (74 + xh) yl yh) (h6 : 0 < lowN (76 + xl) (76 + xh) yl yh) :
    ‖(fam r).f'' z‖ ≤ F2Box r xl xh yl yh := by
  rw [Fam.f''_eq hr]
  refine (norm_add_le _ _).trans ?_
  simp only [F2Box, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
  rw [norm_mul, Complex.norm_natCast]
  exact add_le_add (mul_le_mul_of_nonneg_left (norm_famG2_le_box hx hy hpos) (Nat.cast_nonneg _))
    (norm_famE2_le_box hx hy h4 h6)

theorem norm_f'''_le_box {r : ℕ} (hr : 1 ≤ r) {z : ℂ} {xl xh yl yh : ℚ}
    (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh) (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh)
    (hpos : ∀ bc ∈ famCB, 0 < lowN (bc.1 + xl) (bc.1 + xh) yl yh)
    (h4 : 0 < lowN (74 + xl) (74 + xh) yl yh) (h6 : 0 < lowN (76 + xl) (76 + xh) yl yh) :
    ‖(fam r).f''' z‖ ≤ F3Box r xl xh yl yh := by
  rw [Fam.f'''_eq hr]
  refine (norm_add_le _ _).trans ?_
  simp only [F3Box, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
  rw [norm_mul, Complex.norm_natCast]
  exact add_le_add (mul_le_mul_of_nonneg_left (norm_famG3_le_box hx hy hpos) (Nat.cast_nonneg _))
    (norm_famE3_le_box hx hy h4 h6)

end OddZeta.FamNum
