import OddZeta.Cert.Tools
import OddZeta.Numerics.IntervalComplex

/-!
# Verified rational interval arithmetic for the saddle-point certificates

A small layer on top of `OddZeta.Numerics`: rational intervals `QI` (with sound `add`, `sub`,
`smul`, list sums), exact rational complex numbers `QC`, and enclosures of the quantities that
occur in the saddle-point certificates (`f'`, `f`, `Fd` and `f''` at a rational point, a bound for
`‖f'''‖` on a box, and the corner bounds of `im_f'_le_box`, `le_im_f'_box`, `re_f'_pos_box`).
All functions are computable and meant to be evaluated by the kernel (`decide +kernel`).
-/

namespace OddZeta.Cert

open Complex

/-- `x + y i` for rationals `x, y`. -/
def cq (x y : ℚ) : ℂ := (x : ℂ) + (y : ℂ) * I

@[simp] theorem cq_re (x y : ℚ) : (cq x y).re = x := by simp [cq]

@[simp] theorem cq_im (x y : ℚ) : (cq x y).im = y := by simp [cq]

theorem mk_eq_cq {a b : ℝ} {x y : ℚ} (ha : (x : ℝ) = a) (hb : (y : ℝ) = b) :
    (⟨a, b⟩ : ℂ) = cq x y := Complex.ext (by simp [ha]) (by simp [hb])

theorem natCast_add_cq (a : ℕ) (x y : ℚ) : (a : ℂ) + cq x y = cq (a + x) y := by
  unfold cq; push_cast; ring

theorem sub_add_cq (a b : ℕ) (x y : ℚ) : (a : ℂ) - b + cq x y = cq (a - b + x) y := by
  unfold cq; push_cast; ring

theorem neg_cq (x y : ℚ) : -cq x y = cq (-x) (-y) := by
  unfold cq; push_cast; ring

/-! ### Casting list sums and products -/

theorem cast_list_sum_map {ι : Type*} (L : List ι) (g : ι → ℚ) :
    (((L.map g).sum : ℚ) : ℝ) = (L.map fun i => ((g i : ℚ) : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem cast_list_prod_map {ι : Type*} (L : List ι) (g : ι → ℚ) :
    (((L.map g).prod : ℚ) : ℝ) = (L.map fun i => ((g i : ℚ) : ℝ)).prod := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem list_sum_map_const {ι : Type*} (L : List ι) (c : ℝ) :
    (L.map fun _ => c).sum = L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

/-! ### Safe log / arg bounds (exact at the origin) -/

/-- Lower bound for `arg (x + y i)`. -/
def argL (x y : ℚ) (p : ℕ) : ℚ := if x = 0 ∧ y = 0 then 0 else Num.argLo x y p

/-- Upper bound for `arg (x + y i)`. -/
def argU (x y : ℚ) (p : ℕ) : ℚ := if x = 0 ∧ y = 0 then 0 else Num.argHi x y p

/-- Lower bound for `log ‖x + y i‖`. -/
def logAbsL (x y : ℚ) (p : ℕ) : ℚ := if x = 0 ∧ y = 0 then 0 else Num.logAbsLo x y p

/-- Upper bound for `log ‖x + y i‖`. -/
def logAbsU (x y : ℚ) (p : ℕ) : ℚ := if x = 0 ∧ y = 0 then 0 else Num.logAbsHi x y p

/-- Lower bound for `log n`. -/
def logNL (n p : ℕ) : ℚ := if n = 0 then 0 else Num.logLo n p

/-- Upper bound for `log n`. -/
def logNU (n p : ℕ) : ℚ := if n = 0 then 0 else Num.logHi n p

theorem argL_le (x y : ℚ) (p : ℕ) : (argL x y p : ℝ) ≤ arg (cq x y) := by
  unfold argL cq
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; simp
  · exact Num.argLo_le (not_and_or.1 h) p

theorem le_argU (x y : ℚ) (p : ℕ) : arg (cq x y) ≤ (argU x y p : ℝ) := by
  unfold argU cq
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; simp
  · exact Num.le_argHi (not_and_or.1 h) p

theorem logAbsL_le (x y : ℚ) (p : ℕ) : (logAbsL x y p : ℝ) ≤ Real.log ‖cq x y‖ := by
  unfold logAbsL cq
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; simp
  · exact Num.logAbsLo_le (not_and_or.1 h) p

theorem le_logAbsU (x y : ℚ) (p : ℕ) : Real.log ‖cq x y‖ ≤ (logAbsU x y p : ℝ) := by
  unfold logAbsU cq
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; simp
  · exact Num.le_logAbsHi (not_and_or.1 h) p

theorem logNL_le (n p : ℕ) : (logNL n p : ℝ) ≤ Real.log n := by
  unfold logNL
  split_ifs with h
  · subst h; simp
  · have := Num.logLo_le (x := (n : ℚ)) (by exact_mod_cast Nat.pos_of_ne_zero h) p
    simpa using this

theorem le_logNU (n p : ℕ) : Real.log n ≤ (logNU n p : ℝ) := by
  unfold logNU
  split_ifs with h
  · subst h; simp
  · have := Num.le_logHi (x := (n : ℚ)) (by exact_mod_cast Nat.pos_of_ne_zero h) p
    simpa using this

/-! ### Rational intervals -/

/-- A rational interval `[lo, hi]`. -/
structure QI where
  lo : ℚ
  hi : ℚ

namespace QI

/-- `x ∈ [lo, hi]`. -/
def Mem (I : QI) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

def add (I J : QI) : QI := ⟨I.lo + J.lo, I.hi + J.hi⟩

def sub (I J : QI) : QI := ⟨I.lo - J.hi, I.hi - J.lo⟩

def smul (c : ℚ) (I : QI) : QI :=
  if 0 ≤ c then ⟨c * I.lo, c * I.hi⟩ else ⟨c * I.hi, c * I.lo⟩

def zero : QI := ⟨0, 0⟩

def sumL {ι : Type*} (L : List ι) (g : ι → QI) : QI :=
  L.foldr (fun a acc => (g a).add acc) zero

/-- An upper bound for `x²` on the interval. -/
def sqB (I : QI) : ℚ := max (I.lo ^ 2) (I.hi ^ 2)

theorem mem_add {I J : QI} {x y : ℝ} (hI : I.Mem x) (hJ : J.Mem y) : (I.add J).Mem (x + y) := by
  obtain ⟨h1, h2⟩ := hI
  obtain ⟨h3, h4⟩ := hJ
  simp only [Mem, add, Rat.cast_add]
  constructor <;> linarith

theorem mem_sub {I J : QI} {x y : ℝ} (hI : I.Mem x) (hJ : J.Mem y) : (I.sub J).Mem (x - y) := by
  obtain ⟨h1, h2⟩ := hI
  obtain ⟨h3, h4⟩ := hJ
  simp only [Mem, sub, Rat.cast_sub]
  constructor <;> linarith

theorem mem_smul (c : ℚ) {I : QI} {x : ℝ} (h : I.Mem x) : (smul c I).Mem (c * x) := by
  obtain ⟨h1, h2⟩ := h
  unfold smul
  split_ifs with hc
  · have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
    simp only [Mem, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left h1 hc', mul_le_mul_of_nonneg_left h2 hc'⟩
  · have hc' : (c : ℝ) ≤ 0 := by exact_mod_cast (not_le.1 hc).le
    simp only [Mem, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonpos_left h2 hc', mul_le_mul_of_nonpos_left h1 hc'⟩

theorem mem_smul' (c : ℚ) {a : ℝ} (ha : (c : ℝ) = a) {I : QI} {x : ℝ} (h : I.Mem x) :
    (smul c I).Mem (a * x) := ha ▸ mem_smul c h

theorem mem_sumL {ι : Type*} (L : List ι) {g : ι → QI} {h : ι → ℝ}
    (hg : ∀ i ∈ L, (g i).Mem (h i)) : (sumL L g).Mem (L.map h).sum := by
  induction L with
  | nil => simp [sumL, zero, Mem]
  | cons a L ih =>
    simp only [sumL, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    exact mem_add (hg a List.mem_cons_self) (ih fun i hi => hg i (List.mem_cons_of_mem _ hi))

theorem sq_le_sqB {I : QI} {x : ℝ} (h : I.Mem x) : x ^ 2 ≤ (sqB I : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  simp only [sqB, Rat.cast_max, Rat.cast_pow]
  rcases le_total 0 x with hx | hx
  · exact le_max_of_le_right (pow_le_pow_left₀ hx h2 2)
  · exact le_max_of_le_left (by nlinarith)

theorem lt_of_mem_hi {I : QI} {x : ℝ} (h : I.Mem x) {c : ℝ} (hc : (I.hi : ℝ) < c) : x < c :=
  lt_of_le_of_lt h.2 hc

/-- `[log ‖x + yi‖]`. -/
def logAbsI (x y : ℚ) (p : ℕ) : QI := ⟨logAbsL x y p, logAbsU x y p⟩

/-- `[arg (x + yi)]`. -/
def argI (x y : ℚ) (p : ℕ) : QI := ⟨argL x y p, argU x y p⟩

/-- `[log n]`. -/
def logNI (n p : ℕ) : QI := ⟨logNL n p, logNU n p⟩

/-- `[π]`. -/
def piI : QI := ⟨Num.piLo, Num.piHi⟩

theorem mem_logAbsI (x y : ℚ) (p : ℕ) : (logAbsI x y p).Mem (Real.log ‖cq x y‖) :=
  ⟨logAbsL_le x y p, le_logAbsU x y p⟩

theorem mem_argI (x y : ℚ) (p : ℕ) : (argI x y p).Mem (arg (cq x y)) :=
  ⟨argL_le x y p, le_argU x y p⟩

theorem mem_logNI (n p : ℕ) : (logNI n p).Mem (Real.log n) := ⟨logNL_le n p, le_logNU n p⟩

theorem mem_piI : piI.Mem Real.pi := ⟨Num.piLo_lt_pi.le, Num.pi_lt_piHi.le⟩

end QI

open QI

/-! ### Enclosures of `w log w` -/

/-- `[Re (w log w)]` for `w = x + yi`. -/
def wlogReI (x y : ℚ) (p : ℕ) : QI := (smul x (logAbsI x y p)).sub (smul y (argI x y p))

/-- `[Im (w log w)]` for `w = x + yi`. -/
def wlogImI (x y : ℚ) (p : ℕ) : QI := (smul y (logAbsI x y p)).add (smul x (argI x y p))

theorem mem_wlogReI (x y : ℚ) (p : ℕ) : (wlogReI x y p).Mem (cq x y * log (cq x y)).re := by
  have e : (cq x y * log (cq x y)).re = x * Real.log ‖cq x y‖ - y * arg (cq x y) := by
    simp [mul_re, log_re, log_im]
  rw [e]
  exact mem_sub (mem_smul _ (mem_logAbsI x y p)) (mem_smul _ (mem_argI x y p))

theorem mem_wlogImI (x y : ℚ) (p : ℕ) : (wlogImI x y p).Mem (cq x y * log (cq x y)).im := by
  have e : (cq x y * log (cq x y)).im = y * Real.log ‖cq x y‖ + x * arg (cq x y) := by
    simp [mul_im, log_re, log_im]; ring
  rw [e]
  exact mem_add (mem_smul _ (mem_logAbsI x y p)) (mem_smul _ (mem_argI x y p))

/-! ### Enclosures of `f'`, `f`, `Fd` at a rational point -/

variable (P : Params)

/-- `[Re f'(x + yi)]`. -/
def f'ReI (x y : ℚ) (p : ℕ) : QI :=
  (smul P.r ((logAbsI (P.eta0 + x) y p).sub (logAbsI x y p))).add
    (sumL (P.zs ++ P.ps) fun η : ℕ => (logAbsI (η + x) y p).sub (logAbsI (P.eta0 - η + x) y p))

/-- `[Im f'(x + yi)]`. -/
def f'ImI (x y : ℚ) (p : ℕ) : QI :=
  (smul P.r ((argI (P.eta0 + x) y p).sub (argI (-x) (-y) p))).add
    (sumL (P.zs ++ P.ps) fun η : ℕ => (argI (η + x) y p).sub (argI (P.eta0 - η + x) y p))

/-- `[κ₀]`. -/
def kappaI (p : ℕ) : QI :=
  (sumL P.ps fun η : ℕ => smul ((P.eta0 - 2 * η : ℕ) : ℚ) (logNI (P.eta0 - 2 * η) p)).sub
    (smul 2 (sumL P.zs fun η : ℕ => smul (η : ℚ) (logNI η p)))

/-- `[Re f(x + yi)]`. -/
def fReI (x y : ℚ) (p : ℕ) : QI :=
  ((smul P.r ((wlogReI (-x) (-y) p).add (wlogReI (P.eta0 + x) y p))).add
    (sumL (P.zs ++ P.ps) fun η : ℕ => (wlogReI (η + x) y p).sub (wlogReI (P.eta0 - η + x) y p))).add
    (kappaI P p)

/-- `[Im f(x + yi)]`. -/
def fImI (x y : ℚ) (p : ℕ) : QI :=
  (smul P.r ((wlogImI (-x) (-y) p).add (wlogImI (P.eta0 + x) y p))).add
    (sumL (P.zs ++ P.ps) fun η : ℕ => (wlogImI (η + x) y p).sub (wlogImI (P.eta0 - η + x) y p))

/-- `[Re Fd(x + yi)]`. -/
def FdReI (x y : ℚ) (p : ℕ) : QI := (fReI P x y p).add (smul (((P.r : ℚ) - 2) * (-y)) piI)

/-- `[Im Fd(x + yi)]`. -/
def FdImI (x y : ℚ) (p : ℕ) : QI := (fImI P x y p).add (smul (((P.r : ℚ) - 2) * x) piI)

/-- `[Im f'(x + yi) + (r-2)π]`. -/
def f'ImShI (x y : ℚ) (p : ℕ) : QI := (f'ImI P x y p).add (smul ((P.r : ℚ) - 2) piI)

variable {P}

theorem re_natCast_mul' (n : ℕ) (z : ℂ) : ((n : ℂ) * z).re = n * z.re := by simp

theorem im_natCast_mul' (n : ℕ) (z : ℂ) : ((n : ℂ) * z).im = n * z.im := by simp

theorem mem_f'ReI (x y : ℚ) (p : ℕ) : (f'ReI P x y p).Mem (P.f' (cq x y)).re := by
  rw [re_f']
  simp only [natCast_add_cq, sub_add_cq]
  refine mem_add (mem_smul' _ (by simp) (mem_sub (mem_logAbsI _ _ _) (mem_logAbsI _ _ _)))
    (mem_sumL _ fun η _ => mem_sub (mem_logAbsI _ _ _) (mem_logAbsI _ _ _))

theorem mem_f'ImI (x y : ℚ) (p : ℕ) : (f'ImI P x y p).Mem (P.f' (cq x y)).im := by
  rw [im_f']
  simp only [natCast_add_cq, sub_add_cq, neg_cq]
  refine mem_add (mem_smul' _ (by simp) (mem_sub (mem_argI _ _ _) (mem_argI _ _ _)))
    (mem_sumL _ fun η _ => mem_sub (mem_argI _ _ _) (mem_argI _ _ _))

theorem mem_f'ImShI (x y : ℚ) (p : ℕ) :
    (f'ImShI P x y p).Mem ((P.f' (cq x y)).im + ((P.r : ℝ) - 2) * Real.pi) :=
  mem_add (mem_f'ImI x y p) (mem_smul' _ (by simp) mem_piI)

theorem mem_kappaI (p : ℕ) : (kappaI P p).Mem P.kappa0 := by
  unfold Params.kappa0
  simp only [bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def]
  refine mem_sub (mem_sumL _ fun η _ => mem_smul' _ (by simp) (mem_logNI _ _))
    (mem_smul' _ (by simp) (mem_sumL _ fun η _ => mem_smul' _ (by simp) (mem_logNI _ _)))

theorem f_re (u : ℂ) : (P.f u).re =
    P.r * ((-u * log (-u)).re + ((P.eta0 + u) * log (P.eta0 + u)).re) +
      ((P.zs ++ P.ps).map fun η : ℕ => (((η : ℂ) + u) * log (η + u)).re -
        (((P.eta0 : ℂ) - η + u) * log (P.eta0 - η + u)).re).sum + P.kappa0 := by
  simp only [Params.f, add_re, re_natCast_mul', re_list_sum, sub_re, ofReal_re]

theorem f_im (u : ℂ) : (P.f u).im =
    P.r * ((-u * log (-u)).im + ((P.eta0 + u) * log (P.eta0 + u)).im) +
      ((P.zs ++ P.ps).map fun η : ℕ => (((η : ℂ) + u) * log (η + u)).im -
        (((P.eta0 : ℂ) - η + u) * log (P.eta0 - η + u)).im).sum := by
  simp only [Params.f, add_im, im_natCast_mul', im_list_sum, sub_im, ofReal_im, add_zero]

theorem mem_fReI (x y : ℚ) (p : ℕ) : (fReI P x y p).Mem (P.f (cq x y)).re := by
  rw [f_re]
  simp only [natCast_add_cq, sub_add_cq, neg_cq]
  exact mem_add (mem_add (mem_smul' _ (by simp) (mem_add (mem_wlogReI _ _ _) (mem_wlogReI _ _ _)))
    (mem_sumL _ fun η _ => mem_sub (mem_wlogReI _ _ _) (mem_wlogReI _ _ _))) (mem_kappaI p)

theorem mem_fImI (x y : ℚ) (p : ℕ) : (fImI P x y p).Mem (P.f (cq x y)).im := by
  rw [f_im]
  simp only [natCast_add_cq, sub_add_cq, neg_cq]
  exact mem_add (mem_smul' _ (by simp) (mem_add (mem_wlogImI _ _ _) (mem_wlogImI _ _ _)))
    (mem_sumL _ fun η _ => mem_sub (mem_wlogImI _ _ _) (mem_wlogImI _ _ _))

theorem Fd_re (u : ℂ) : (P.Fd u).re = (P.f u).re + ((P.r : ℝ) - 2) * (-u.im) * Real.pi := by
  simp [Params.Fd, mul_re, mul_im]; ring

theorem Fd_im (u : ℂ) : (P.Fd u).im = (P.f u).im + ((P.r : ℝ) - 2) * u.re * Real.pi := by
  simp [Params.Fd, mul_re, mul_im]; ring

theorem mem_FdReI (x y : ℚ) (p : ℕ) : (FdReI P x y p).Mem (P.Fd (cq x y)).re := by
  rw [Fd_re]
  exact mem_add (mem_fReI x y p) (mem_smul' _ (by simp) mem_piI)

theorem mem_FdImI (x y : ℚ) (p : ℕ) : (FdImI P x y p).Mem (P.Fd (cq x y)).im := by
  rw [Fd_im]
  exact mem_add (mem_fImI x y p) (mem_smul' _ (by simp) mem_piI)

/-! ### Exact rational complex arithmetic -/

/-- A complex number with rational coordinates. -/
structure QC where
  re : ℚ
  im : ℚ

namespace QC

def toC (z : QC) : ℂ := cq z.re z.im

def add (z w : QC) : QC := ⟨z.re + w.re, z.im + w.im⟩

def sub (z w : QC) : QC := ⟨z.re - w.re, z.im - w.im⟩

def inv (z : QC) : QC := ⟨z.re / (z.re ^ 2 + z.im ^ 2), -z.im / (z.re ^ 2 + z.im ^ 2)⟩

def nsmul (n : ℕ) (z : QC) : QC := ⟨n * z.re, n * z.im⟩

def sumL {ι : Type*} (L : List ι) (g : ι → QC) : QC := L.foldr (fun a acc => (g a).add acc) ⟨0, 0⟩

/-- The squared norm. -/
def nsq (z : QC) : ℚ := z.re ^ 2 + z.im ^ 2

theorem toC_add (z w : QC) : (z.add w).toC = z.toC + w.toC := by
  apply Complex.ext <;> simp [toC, add]

theorem toC_sub (z w : QC) : (z.sub w).toC = z.toC - w.toC := by
  apply Complex.ext <;> simp [toC, sub]

theorem toC_nsmul (n : ℕ) (z : QC) : (z.nsmul n).toC = n * z.toC := by
  apply Complex.ext <;> simp [toC, nsmul]

theorem toC_inv (z : QC) : z.inv.toC = z.toC⁻¹ := by
  apply Complex.ext <;> simp [toC, inv, inv_re, inv_im, normSq_apply] <;> ring

theorem toC_sumL {ι : Type*} (L : List ι) (g : ι → QC) :
    (sumL L g).toC = (L.map fun i => (g i).toC).sum := by
  induction L with
  | nil => simp [sumL, toC, cq]
  | cons a L ih =>
    simp only [sumL, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [toC_add, ih]

theorem normSq_toC (z : QC) : normSq z.toC = (z.nsq : ℝ) := by
  simp [toC, nsq, normSq_apply]; ring

end QC

variable (P) in
/-- `f''(x + yi)`, exactly. -/
def f''Q (x y : ℚ) : QC :=
  (QC.nsmul P.r ((QC.inv ⟨P.eta0 + x, y⟩).sub (QC.inv ⟨x, y⟩))).add
    (QC.sumL (P.zs ++ P.ps) fun η : ℕ =>
      (QC.inv ⟨η + x, y⟩).sub (QC.inv ⟨P.eta0 - η + x, y⟩))

theorem toC_f''Q (x y : ℚ) : (f''Q P x y).toC = P.f'' (cq x y) := by
  simp only [f''Q, QC.toC_add, QC.toC_nsmul, QC.toC_sub, QC.toC_inv, QC.toC_sumL, Params.f'']
  simp only [QC.toC, natCast_add_cq, sub_add_cq]

/-! ### A bound for `‖f'''‖` on a box -/

/-- A lower bound for `|t|`, `t ∈ [a, b]`. -/
def lowAbs (a b : ℚ) : ℚ := max (max a (-b)) 0

/-- A lower bound for `‖z‖²`, `z ∈ [xl, xh] × [yl, yh]`. -/
def nsqLow (xl xh yl yh : ℚ) : ℚ := lowAbs xl xh ^ 2 + lowAbs yl yh ^ 2

variable (P) in
/-- An upper bound for `‖f'''‖` on the box `[xl, xh] × [yl, yh]` (`yh < 0`). -/
def f'''Box (xl xh yl yh : ℚ) : ℚ :=
  P.r * (1 / nsqLow (P.eta0 + xl) (P.eta0 + xh) yl yh + 1 / nsqLow xl xh yl yh) +
    ((P.zs ++ P.ps).map fun η : ℕ => 1 / nsqLow (η + xl) (η + xh) yl yh +
      1 / nsqLow (P.eta0 - η + xl) (P.eta0 - η + xh) yl yh).sum

theorem lowAbs_sq_le {a b : ℚ} {t : ℝ} (h1 : (a : ℝ) ≤ t) (h2 : t ≤ b) :
    ((lowAbs a b : ℚ) : ℝ) ^ 2 ≤ t ^ 2 := by
  have h0 : (0 : ℝ) ≤ lowAbs a b := by
    simp only [lowAbs, Rat.cast_max, Rat.cast_neg, Rat.cast_zero]; exact le_max_right _ _
  have h3 : ((lowAbs a b : ℚ) : ℝ) ≤ |t| := by
    simp only [lowAbs, Rat.cast_max, Rat.cast_neg, Rat.cast_zero]
    refine max_le (max_le (h1.trans (le_abs_self t)) ?_) (abs_nonneg t)
    have := neg_abs_le t
    linarith
  calc ((lowAbs a b : ℚ) : ℝ) ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ h0 h3 2
    _ = t ^ 2 := sq_abs t

theorem lowAbs_pos {a b : ℚ} (hb : b < 0) : 0 < lowAbs a b := by
  simp only [lowAbs]
  exact lt_max_of_lt_left (lt_max_of_lt_right (by linarith))

theorem norm_inv_sq_le_box {z : ℂ} {xl xh yl yh : ℚ} (hx : (xl : ℝ) ≤ z.re ∧ z.re ≤ xh)
    (hy : (yl : ℝ) ≤ z.im ∧ z.im ≤ yh) (hyh : yh < 0) :
    ‖(z ^ 2)⁻¹‖ ≤ ((1 / nsqLow xl xh yl yh : ℚ) : ℝ) := by
  have hpos : (0 : ℝ) < nsqLow xl xh yl yh := by
    have := lowAbs_pos (a := yl) hyh
    have h : (0 : ℚ) < nsqLow xl xh yl yh := by unfold nsqLow; positivity
    exact_mod_cast h
  have hle : ((nsqLow xl xh yl yh : ℚ) : ℝ) ≤ ‖z‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp only [nsqLow, Rat.cast_add, Rat.cast_pow]
    have := lowAbs_sq_le hx.1 hx.2
    have := lowAbs_sq_le hy.1 hy.2
    nlinarith
  rw [norm_inv, norm_pow, Rat.cast_div, Rat.cast_one, ← one_div]
  exact one_div_le_one_div_of_le hpos hle

theorem norm_f'''_le_box {w : ℂ} {xl xh yl yh : ℚ} (hx : (xl : ℝ) ≤ w.re ∧ w.re ≤ xh)
    (hy : (yl : ℝ) ≤ w.im ∧ w.im ≤ yh) (hyh : yh < 0) :
    ‖P.f''' w‖ ≤ (f'''Box P xl xh yl yh : ℝ) := by
  have key : ∀ (a : ℚ) (c : ℂ), c = (a : ℂ) → ‖((c + w) ^ 2)⁻¹‖ ≤
      ((1 / nsqLow (a + xl) (a + xh) yl yh : ℚ) : ℝ) := by
    intro a c hc
    subst hc
    refine norm_inv_sq_le_box ?_ ?_ hyh
    · simp only [add_re, ratCast_re, Rat.cast_add]; constructor <;> linarith [hx.1, hx.2]
    · simpa using hy
  simp only [f'''Box, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, cast_list_sum_map]
  unfold Params.f'''
  rw [norm_neg]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_natCast]
    gcongr
    refine (norm_sub_le _ _).trans (add_le_add (key _ _ (by simp)) ?_)
    have := key 0 0 (by simp)
    simpa using this
  · refine norm_list_sum_map_le _ fun η _ => ?_
    exact (norm_sub_le _ _).trans (add_le_add (key _ _ (by simp)) (key _ _ (by push_cast; ring)))

/-- A crude bound for `‖f''‖` in the half-plane `Im w ≤ -d`. -/
theorem norm_f''_le_of_im {w : ℂ} {d : ℝ} (hd : 0 < d) (h : w.im ≤ -d) :
    ‖P.f'' w‖ ≤ (2 * P.r + 2 * (P.zs ++ P.ps).length) / d := by
  have key : ∀ c : ℂ, c.im = 0 → ‖(c + w)⁻¹‖ ≤ 1 / d := by
    intro c hc
    rw [norm_inv, ← one_div]
    refine one_div_le_one_div_of_le hd ?_
    refine le_trans ?_ (abs_im_le_norm _)
    rw [add_im, hc, zero_add, abs_of_neg (by linarith)]
    linarith
  unfold Params.f''
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(P.r : ℂ) * (((P.eta0 : ℂ) + w)⁻¹ - w⁻¹)‖ ≤ P.r * (1 / d + 1 / d) := by
    rw [norm_mul, Complex.norm_natCast]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    have := key 0 (by simp)
    rw [zero_add] at this
    linarith [key (P.eta0 : ℂ) (by simp)]
  have h2 := norm_list_sum_map_le (P.zs ++ P.ps) (b := fun _ => 1 / d + 1 / d)
    (g := fun η : ℕ => ((η : ℂ) + w)⁻¹ - ((P.eta0 : ℂ) - η + w)⁻¹) fun η _ => by
      refine (norm_sub_le _ _).trans ?_
      linarith [key (η : ℂ) (by simp), key ((P.eta0 : ℂ) - η) (by simp)]
  rw [list_sum_map_const] at h2
  calc _ ≤ P.r * (1 / d + 1 / d) + (P.zs ++ P.ps).length * (1 / d + 1 / d) := add_le_add h1 h2
    _ = _ := by field_simp; ring

/-! ### Corner bounds for `Im f'` and the product criterion for `Re f'` on boxes -/

variable (P) in
/-- Upper bound for the right-hand side of `im_f'_le_box`. -/
def imUpperQ (x1 x2 y1 y2 : ℚ) (p : ℕ) : ℚ :=
  P.r * (argU (P.eta0 + x2) y2 p - min (argL (-x1) (-y1) p) (argL (-x1) (-y2) p)) +
    ((P.zs ++ P.ps).map fun η : ℕ => argU (η + x2) y2 p - argL (P.eta0 - η + x1) y1 p).sum

variable (P) in
/-- Lower bound for the left-hand side of `le_im_f'_box`. -/
def imLowerQ (x1 x2 y1 y2 : ℚ) (p : ℕ) : ℚ :=
  P.r * (argL (P.eta0 + x1) y1 p - max (argU (-x2) (-y1) p) (argU (-x2) (-y2) p)) +
    ((P.zs ++ P.ps).map fun η : ℕ => argL (η + x1) y1 p - argU (P.eta0 - η + x2) y2 p).sum

theorem arg_mk_le_argU {a b : ℝ} (x y : ℚ) (ha : (x : ℝ) = a) (hb : (y : ℝ) = b) (p : ℕ) :
    arg ⟨a, b⟩ ≤ (argU x y p : ℝ) := by
  rw [mk_eq_cq ha hb]; exact le_argU x y p

theorem argL_le_arg_mk {a b : ℝ} (x y : ℚ) (ha : (x : ℝ) = a) (hb : (y : ℝ) = b) (p : ℕ) :
    (argL x y p : ℝ) ≤ arg ⟨a, b⟩ := by
  rw [mk_eq_cq ha hb]; exact argL_le x y p

theorem le_imUpperQ (x1 x2 y1 y2 : ℚ) (p : ℕ) :
    P.r * (arg ⟨P.eta0 + (x2 : ℝ), y2⟩ - min (arg ⟨-(x1 : ℝ), -(y1 : ℝ)⟩)
        (arg ⟨-(x1 : ℝ), -(y2 : ℝ)⟩)) +
      ((P.zs ++ P.ps).map fun η : ℕ =>
        arg ⟨η + (x2 : ℝ), y2⟩ - arg ⟨(P.eta0 : ℝ) - η + x1, y1⟩).sum ≤
    (imUpperQ P x1 x2 y1 y2 p : ℝ) := by
  simp only [imUpperQ, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub, Rat.cast_min,
    cast_list_sum_map]
  refine add_le_add (mul_le_mul_of_nonneg_left (sub_le_sub ?_ (min_le_min ?_ ?_))
    (Nat.cast_nonneg _)) (List.sum_le_sum fun η _ => sub_le_sub ?_ ?_)
  · exact arg_mk_le_argU _ _ (by push_cast; ring) rfl p
  · exact argL_le_arg_mk _ _ (by push_cast; ring) (by push_cast; ring) p
  · exact argL_le_arg_mk _ _ (by push_cast; ring) (by push_cast; ring) p
  · exact arg_mk_le_argU _ _ (by push_cast; ring) rfl p
  · exact argL_le_arg_mk _ _ (by push_cast; ring) rfl p

theorem imLowerQ_le (x1 x2 y1 y2 : ℚ) (p : ℕ) :
    (imLowerQ P x1 x2 y1 y2 p : ℝ) ≤
    P.r * (arg ⟨P.eta0 + (x1 : ℝ), y1⟩ - max (arg ⟨-(x2 : ℝ), -(y1 : ℝ)⟩)
        (arg ⟨-(x2 : ℝ), -(y2 : ℝ)⟩)) +
      ((P.zs ++ P.ps).map fun η : ℕ =>
        arg ⟨η + (x1 : ℝ), y1⟩ - arg ⟨(P.eta0 : ℝ) - η + x2, y2⟩).sum := by
  simp only [imLowerQ, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub, Rat.cast_max,
    cast_list_sum_map]
  refine add_le_add (mul_le_mul_of_nonneg_left (sub_le_sub ?_ (max_le_max ?_ ?_))
    (Nat.cast_nonneg _)) (List.sum_le_sum fun η _ => sub_le_sub ?_ ?_)
  · exact argL_le_arg_mk _ _ (by push_cast; ring) rfl p
  · exact arg_mk_le_argU _ _ (by push_cast; ring) (by push_cast; ring) p
  · exact arg_mk_le_argU _ _ (by push_cast; ring) (by push_cast; ring) p
  · exact argL_le_arg_mk _ _ (by push_cast; ring) rfl p
  · exact arg_mk_le_argU _ _ (by push_cast; ring) rfl p

variable (P) in
/-- The product criterion of `re_f'_pos_box`, in rational arithmetic. -/
def reBoxQ (x1 x2 y1 y2 : ℚ) : Bool :=
  decide ((max (x1 ^ 2) (x2 ^ 2) + y1 ^ 2) ^ P.r *
      ((P.zs ++ P.ps).map fun η : ℕ => ((P.eta0 : ℚ) - η + x2) ^ 2 + y1 ^ 2).prod <
    (((P.eta0 : ℚ) + x1) ^ 2 + y2 ^ 2) ^ P.r *
      ((P.zs ++ P.ps).map fun η : ℕ => ((η : ℚ) + x1) ^ 2 + y2 ^ 2).prod)

theorem reBoxQ_spec {x1 x2 y1 y2 : ℚ} (h : reBoxQ P x1 x2 y1 y2 = true) :
    (max ((x1 : ℝ) ^ 2) ((x2 : ℝ) ^ 2) + (y1 : ℝ) ^ 2) ^ P.r *
        ((P.zs ++ P.ps).map fun η : ℕ => ((P.eta0 : ℝ) - η + x2) ^ 2 + (y1 : ℝ) ^ 2).prod <
      (((P.eta0 : ℝ) + x1) ^ 2 + (y2 : ℝ) ^ 2) ^ P.r *
        ((P.zs ++ P.ps).map fun η : ℕ => ((η : ℝ) + x1) ^ 2 + (y2 : ℝ) ^ 2).prod := by
  unfold reBoxQ at h
  have h' := Rat.cast_lt (K := ℝ) |>.2 (of_decide_eq_true h)
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_max, cast_list_prod_map,
    Rat.cast_sub, Rat.cast_natCast] using h'

end OddZeta.Cert
