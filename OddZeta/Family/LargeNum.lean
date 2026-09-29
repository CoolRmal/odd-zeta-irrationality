import OddZeta.Family.LargeAux
import OddZeta.Numerics.Interval

/-!
# The constants of Section 8.3 of the note for the asymptotic regime

`a = famA` is a zero of `ĝ'` in `[aLo, aHi] = [4.1929527, 4.1929528]` (intermediate value
theorem, the signs of `ĝ'` at the endpoints from verified logarithm enclosures), and
`D̄ = famD = -ĝ''(a) ∈ [0.1832, 0.1833]`, `ĝ(a) ∈ [-232.05, -232]`, `e(a) ∈ [-9.36, -9]`,
`|e'(a)| ≤ 2/78`. All numerical facts are checked by the kernel (`decide +kernel`).
-/

namespace OddZeta

open Complex Set

namespace Large

/-! ### Real versions of `g, g', g'', e` on `(0, ∞)` -/

/-- `ĝ(x)`. -/
noncomputable def gR (x : ℝ) : ℝ :=
  (famCB.map fun bc : ℕ × ℤ => (bc.2 : ℝ) * ((bc.1 : ℝ) + x) * Real.log ((bc.1 : ℝ) + x)).sum +
    famKg

/-- `ĝ'(x)`. -/
noncomputable def g1R (x : ℝ) : ℝ :=
  (famCB.map fun bc : ℕ × ℤ => (bc.2 : ℝ) * Real.log ((bc.1 : ℝ) + x)).sum

/-- `ĝ''(x)`. -/
noncomputable def g2R (x : ℝ) : ℝ :=
  (famCB.map fun bc : ℕ × ℤ => (bc.2 : ℝ) * ((bc.1 : ℝ) + x)⁻¹).sum

/-- `e(x)`. -/
noncomputable def eR (x : ℝ) : ℝ :=
  (74 + x) * Real.log (74 + x) - (76 + x) * Real.log (76 + x) + 2 * Real.log 2

theorem ofReal_list_sum_map {ι : Type*} (L : List ι) (f : ι → ℝ) :
    (((L.map f).sum : ℝ) : ℂ) = (L.map fun i => ((f i : ℝ) : ℂ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem ratCast_list_sum_map {ι : Type*} (L : List ι) (f : ι → ℚ) :
    (((L.map f).sum : ℚ) : ℝ) = (L.map fun i => ((f i : ℚ) : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem log_natCast_add_ofReal (b : ℕ) {x : ℝ} (hx : 0 < x) :
    log ((b : ℂ) + x) = ((Real.log ((b : ℝ) + x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_log (by positivity)]
  push_cast
  rfl

theorem log_ofNat_add_ofReal (c : ℝ) {x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) :
    log ((c : ℂ) + x) = ((Real.log (c + x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_log (by positivity)]
  push_cast
  rfl

theorem famG_ofReal {x : ℝ} (hx : 0 < x) : famG x = ((gR x : ℝ) : ℂ) := by
  unfold famG gR
  have : ∀ bc ∈ famCB, (bc.2 : ℂ) * ((bc.1 : ℂ) + x) * log ((bc.1 : ℂ) + x) =
      (((bc.2 : ℝ) * ((bc.1 : ℝ) + x) * Real.log ((bc.1 : ℝ) + x) : ℝ) : ℂ) := by
    intro bc _
    rw [log_natCast_add_ofReal bc.1 hx]
    push_cast
    ring
  rw [List.map_congr_left this]
  push_cast [ofReal_list_sum_map]
  rfl

theorem famG1_ofReal {x : ℝ} (hx : 0 < x) : famG1 x = ((g1R x : ℝ) : ℂ) := by
  unfold famG1 g1R
  have : ∀ bc ∈ famCB, (bc.2 : ℂ) * log ((bc.1 : ℂ) + x) =
      (((bc.2 : ℝ) * Real.log ((bc.1 : ℝ) + x) : ℝ) : ℂ) := by
    intro bc _
    rw [log_natCast_add_ofReal bc.1 hx]
    push_cast
    ring
  rw [List.map_congr_left this]
  push_cast [ofReal_list_sum_map]
  rfl

theorem famG2_ofReal (x : ℝ) : famG2 x = ((g2R x : ℝ) : ℂ) := by
  unfold famG2 g2R
  push_cast [ofReal_list_sum_map]
  rfl

theorem famE_ofReal {x : ℝ} (hx : 0 < x) : famE x = ((eR x : ℝ) : ℂ) := by
  unfold famE eR
  have h74 := log_ofNat_add_ofReal 74 (by norm_num) hx
  have h76 := log_ofNat_add_ofReal 76 (by norm_num) hx
  push_cast at h74 h76 ⊢
  rw [h74, h76]

theorem famE1_ofReal {x : ℝ} (hx : 0 < x) :
    famE1 x = ((Real.log (74 + x) - Real.log (76 + x) : ℝ) : ℂ) := by
  unfold famE1
  have h74 := log_ofNat_add_ofReal 74 (by norm_num) hx
  have h76 := log_ofNat_add_ofReal 76 (by norm_num) hx
  push_cast at h74 h76 ⊢
  rw [h74, h76]

/-! ### Rational enclosures -/

open _root_.OddZeta.Num

/-- Lower bound for `ĝ'(x)`. -/
def g1Lo (x : ℚ) (p : ℕ) : ℚ :=
  (famCB.map fun bc : ℕ × ℤ => if 0 ≤ bc.2 then (bc.2 : ℚ) * logLo ((bc.1 : ℚ) + x) p
    else (bc.2 : ℚ) * logHi ((bc.1 : ℚ) + x) p).sum

/-- Upper bound for `ĝ'(x)`. -/
def g1Hi (x : ℚ) (p : ℕ) : ℚ :=
  (famCB.map fun bc : ℕ × ℤ => if 0 ≤ bc.2 then (bc.2 : ℚ) * logHi ((bc.1 : ℚ) + x) p
    else (bc.2 : ℚ) * logLo ((bc.1 : ℚ) + x) p).sum

theorem g1Lo_le {x : ℚ} (hx : 0 < x) (p : ℕ) : (g1Lo x p : ℝ) ≤ g1R x := by
  unfold g1Lo g1R
  rw [ratCast_list_sum_map]
  refine List.sum_le_sum fun bc _ => ?_
  have hpos : (0 : ℚ) < (bc.1 : ℚ) + x := by positivity
  have h1 := logLo_le hpos p
  have h2 := le_logHi hpos p
  push_cast at h1 h2
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left h1 (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_left h2 (by exact_mod_cast (not_le.1 hc).le)

theorem le_g1Hi {x : ℚ} (hx : 0 < x) (p : ℕ) : g1R x ≤ (g1Hi x p : ℝ) := by
  unfold g1Hi g1R
  rw [ratCast_list_sum_map]
  refine List.sum_le_sum fun bc _ => ?_
  have hpos : (0 : ℚ) < (bc.1 : ℚ) + x := by positivity
  have h1 := logLo_le hpos p
  have h2 := le_logHi hpos p
  push_cast at h1 h2
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left h2 (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_left h1 (by exact_mod_cast (not_le.1 hc).le)

theorem xlogx_lo {y₁ y l : ℝ} (h1 : 1 ≤ y₁) (h : y₁ ≤ y) (hl : l ≤ Real.log y₁) :
    y₁ * l ≤ y * Real.log y := by
  have h0 : 0 < y₁ := by linarith
  calc y₁ * l ≤ y₁ * Real.log y₁ := mul_le_mul_of_nonneg_left hl h0.le
    _ ≤ y * Real.log y := mul_le_mul h (Real.log_le_log h0 h) (Real.log_nonneg h1) (by linarith)

theorem xlogx_hi {y y₂ l : ℝ} (h1 : 1 ≤ y) (h : y ≤ y₂) (hl : Real.log y₂ ≤ l) :
    y * Real.log y ≤ y₂ * l := by
  have h0 : 0 < y := by linarith
  calc y * Real.log y ≤ y₂ * Real.log y₂ :=
        mul_le_mul h (Real.log_le_log h0 h) (Real.log_nonneg h1) (by linarith)
    _ ≤ y₂ * l := mul_le_mul_of_nonneg_left hl (by linarith)

/-- Lower bound for `κ_g`. -/
def kgLo (p : ℕ) : ℚ :=
  -90 * logHi 45 p + 54 * logLo 54 p + 50 * logLo 50 p + 44 * logLo 44 p + 38 * logLo 38 p +
    30 * logLo 30 p

/-- Upper bound for `κ_g`. -/
def kgHi (p : ℕ) : ℚ :=
  -90 * logLo 45 p + 54 * logHi 54 p + 50 * logHi 50 p + 44 * logHi 44 p + 38 * logHi 38 p +
    30 * logHi 30 p

theorem logLo_nat (n : ℕ) (hn : 0 < n) (p : ℕ) : (logLo (n : ℚ) p : ℝ) ≤ Real.log n := by
  have := logLo_le (x := (n : ℚ)) (by exact_mod_cast hn) p
  simpa using this

theorem logHi_nat (n : ℕ) (hn : 0 < n) (p : ℕ) : Real.log n ≤ (logHi (n : ℚ) p : ℝ) := by
  have := le_logHi (x := (n : ℚ)) (by exact_mod_cast hn) p
  simpa using this

theorem kgLo_le (p : ℕ) : (kgLo p : ℝ) ≤ famKg := by
  have a1 := logHi_nat 45 (by norm_num) p
  have a2 := logLo_nat 54 (by norm_num) p
  have a3 := logLo_nat 50 (by norm_num) p
  have a4 := logLo_nat 44 (by norm_num) p
  have a5 := logLo_nat 38 (by norm_num) p
  have a6 := logLo_nat 30 (by norm_num) p
  push_cast at a1 a2 a3 a4 a5 a6
  unfold kgLo famKg
  push_cast
  linarith

theorem le_kgHi (p : ℕ) : famKg ≤ (kgHi p : ℝ) := by
  have a1 := logLo_nat 45 (by norm_num) p
  have a2 := logHi_nat 54 (by norm_num) p
  have a3 := logHi_nat 50 (by norm_num) p
  have a4 := logHi_nat 44 (by norm_num) p
  have a5 := logHi_nat 38 (by norm_num) p
  have a6 := logHi_nat 30 (by norm_num) p
  push_cast at a1 a2 a3 a4 a5 a6
  unfold kgHi famKg
  push_cast
  linarith

/-- Lower bound for `ĝ(x)`, `x ∈ [x₁, x₂]`. -/
def gLo (x₁ x₂ : ℚ) (p : ℕ) : ℚ :=
  (famCB.map fun bc : ℕ × ℤ => if 0 ≤ bc.2 then
      (bc.2 : ℚ) * (((bc.1 : ℚ) + x₁) * logLo ((bc.1 : ℚ) + x₁) p)
    else (bc.2 : ℚ) * (((bc.1 : ℚ) + x₂) * logHi ((bc.1 : ℚ) + x₂) p)).sum + kgLo p

/-- Upper bound for `ĝ(x)`, `x ∈ [x₁, x₂]`. -/
def gHi (x₁ x₂ : ℚ) (p : ℕ) : ℚ :=
  (famCB.map fun bc : ℕ × ℤ => if 0 ≤ bc.2 then
      (bc.2 : ℚ) * (((bc.1 : ℚ) + x₂) * logHi ((bc.1 : ℚ) + x₂) p)
    else (bc.2 : ℚ) * (((bc.1 : ℚ) + x₁) * logLo ((bc.1 : ℚ) + x₁) p)).sum + kgHi p

theorem gLo_le {x₁ x₂ : ℚ} {x : ℝ} (h1 : 1 ≤ x₁) (hx₁ : (x₁ : ℝ) ≤ x) (hx₂ : x ≤ x₂) (p : ℕ) :
    (gLo x₁ x₂ p : ℝ) ≤ gR x := by
  unfold gLo gR
  rw [Rat.cast_add, ratCast_list_sum_map]
  refine add_le_add (List.sum_le_sum fun bc _ => ?_) (kgLo_le p)
  have h1' : (1 : ℝ) ≤ x₁ := by exact_mod_cast h1
  have hb : (0 : ℝ) ≤ bc.1 := Nat.cast_nonneg _
  have hbq : (0 : ℚ) ≤ bc.1 := Nat.cast_nonneg _
  have hq : x₁ ≤ x₂ := by exact_mod_cast hx₁.trans hx₂
  have hq' : (x₁ : ℝ) ≤ x₂ := hx₁.trans hx₂
  have hp1 : (0 : ℚ) < (bc.1 : ℚ) + x₁ := by linarith
  have hp2 : (0 : ℚ) < (bc.1 : ℚ) + x₂ := by linarith
  have l1 := logLo_le hp1 p
  have l2 := le_logHi hp2 p
  push_cast at l1 l2
  split_ifs with hc
  · push_cast
    rw [mul_assoc (bc.2 : ℝ)]
    refine mul_le_mul_of_nonneg_left (xlogx_lo (y₁ := (bc.1 : ℝ) + x₁) (y := (bc.1 : ℝ) + x)
      (by linarith) (by linarith) l1) ?_
    exact_mod_cast hc
  · push_cast
    rw [mul_assoc (bc.2 : ℝ)]
    refine mul_le_mul_of_nonpos_left (xlogx_hi (y := (bc.1 : ℝ) + x) (y₂ := (bc.1 : ℝ) + x₂)
      (by linarith) (by linarith) l2) ?_
    exact_mod_cast (not_le.1 hc).le

theorem le_gHi {x₁ x₂ : ℚ} {x : ℝ} (h1 : 1 ≤ x₁) (hx₁ : (x₁ : ℝ) ≤ x) (hx₂ : x ≤ x₂) (p : ℕ) :
    gR x ≤ (gHi x₁ x₂ p : ℝ) := by
  unfold gHi gR
  rw [Rat.cast_add, ratCast_list_sum_map]
  refine add_le_add (List.sum_le_sum fun bc _ => ?_) (le_kgHi p)
  have h1' : (1 : ℝ) ≤ x₁ := by exact_mod_cast h1
  have hb : (0 : ℝ) ≤ bc.1 := Nat.cast_nonneg _
  have hbq : (0 : ℚ) ≤ bc.1 := Nat.cast_nonneg _
  have hq : x₁ ≤ x₂ := by exact_mod_cast hx₁.trans hx₂
  have hq' : (x₁ : ℝ) ≤ x₂ := hx₁.trans hx₂
  have hp1 : (0 : ℚ) < (bc.1 : ℚ) + x₁ := by linarith
  have hp2 : (0 : ℚ) < (bc.1 : ℚ) + x₂ := by linarith
  have l1 := logLo_le hp1 p
  have l2 := le_logHi hp2 p
  push_cast at l1 l2
  split_ifs with hc
  · push_cast
    rw [mul_assoc (bc.2 : ℝ)]
    refine mul_le_mul_of_nonneg_left (xlogx_hi (y := (bc.1 : ℝ) + x) (y₂ := (bc.1 : ℝ) + x₂)
      (by linarith) (by linarith) l2) ?_
    exact_mod_cast hc
  · push_cast
    rw [mul_assoc (bc.2 : ℝ)]
    refine mul_le_mul_of_nonpos_left (xlogx_lo (y₁ := (bc.1 : ℝ) + x₁) (y := (bc.1 : ℝ) + x)
      (by linarith) (by linarith) l1) ?_
    exact_mod_cast (not_le.1 hc).le

/-- Lower bound for `e(x)`, `x ∈ [x₁, x₂]`. -/
def eLo (x₁ x₂ : ℚ) (p : ℕ) : ℚ :=
  (74 + x₁) * logLo (74 + x₁) p - (76 + x₂) * logHi (76 + x₂) p + 2 * logLo 2 p

/-- Upper bound for `e(x)`, `x ∈ [x₁, x₂]`. -/
def eHi (x₁ x₂ : ℚ) (p : ℕ) : ℚ :=
  (74 + x₂) * logHi (74 + x₂) p - (76 + x₁) * logLo (76 + x₁) p + 2 * logHi 2 p

theorem eLo_le {x₁ x₂ : ℚ} {x : ℝ} (h1 : 1 ≤ x₁) (hx₁ : (x₁ : ℝ) ≤ x) (hx₂ : x ≤ x₂) (p : ℕ) :
    (eLo x₁ x₂ p : ℝ) ≤ eR x := by
  have h1' : (1 : ℝ) ≤ x₁ := by exact_mod_cast h1
  have hq : x₁ ≤ x₂ := by exact_mod_cast hx₁.trans hx₂
  have l1 := logLo_le (x := 74 + x₁) (by linarith) p
  have l2 := le_logHi (x := 76 + x₂) (by linarith) p
  have l3 := logLo_le (x := 2) (by norm_num) p
  push_cast at l1 l2 l3
  have t1 := xlogx_lo (y₁ := 74 + (x₁ : ℝ)) (y := 74 + x) (by linarith) (by linarith) l1
  have t2 := xlogx_hi (y := 76 + x) (y₂ := 76 + (x₂ : ℝ)) (by linarith) (by linarith) l2
  unfold eLo eR
  push_cast
  linarith

theorem le_eHi {x₁ x₂ : ℚ} {x : ℝ} (h1 : 1 ≤ x₁) (hx₁ : (x₁ : ℝ) ≤ x) (hx₂ : x ≤ x₂) (p : ℕ) :
    eR x ≤ (eHi x₁ x₂ p : ℝ) := by
  have h1' : (1 : ℝ) ≤ x₁ := by exact_mod_cast h1
  have hq : x₁ ≤ x₂ := by exact_mod_cast hx₁.trans hx₂
  have l1 := le_logHi (x := 74 + x₂) (by linarith) p
  have l2 := logLo_le (x := 76 + x₁) (by linarith) p
  have l3 := le_logHi (x := 2) (by norm_num) p
  push_cast at l1 l2 l3
  have t1 := xlogx_hi (y := 74 + x) (y₂ := 74 + (x₂ : ℝ)) (by linarith) (by linarith) l1
  have t2 := xlogx_lo (y₁ := 76 + (x₁ : ℝ)) (y := 76 + x) (by linarith) (by linarith) l2
  unfold eHi eR
  push_cast
  linarith

/-- Lower bound for `ĝ''(x)`, `x ∈ [x₁, x₂]`. -/
def g2Lo (x₁ x₂ : ℚ) : ℚ :=
  (famCB.map fun bc : ℕ × ℤ => if 0 ≤ bc.2 then (bc.2 : ℚ) / ((bc.1 : ℚ) + x₂)
    else (bc.2 : ℚ) / ((bc.1 : ℚ) + x₁)).sum

/-- Upper bound for `ĝ''(x)`, `x ∈ [x₁, x₂]`. -/
def g2Hi (x₁ x₂ : ℚ) : ℚ :=
  (famCB.map fun bc : ℕ × ℤ => if 0 ≤ bc.2 then (bc.2 : ℚ) / ((bc.1 : ℚ) + x₁)
    else (bc.2 : ℚ) / ((bc.1 : ℚ) + x₂)).sum

theorem g2Lo_le {x₁ x₂ : ℚ} {x : ℝ} (h1 : 0 < x₁) (hx₁ : (x₁ : ℝ) ≤ x) (hx₂ : x ≤ x₂) :
    (g2Lo x₁ x₂ : ℝ) ≤ g2R x := by
  unfold g2Lo g2R
  rw [ratCast_list_sum_map]
  refine List.sum_le_sum fun bc _ => ?_
  have h1' : (0 : ℝ) < x₁ := by exact_mod_cast h1
  have hb : (0 : ℝ) ≤ bc.1 := Nat.cast_nonneg _
  split_ifs with hc
  · push_cast
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hc)
    exact inv_anti₀ (by linarith) (by linarith)
  · push_cast
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonpos_left ?_ (by exact_mod_cast (not_le.1 hc).le)
    exact inv_anti₀ (by linarith) (by linarith)

theorem le_g2Hi {x₁ x₂ : ℚ} {x : ℝ} (h1 : 0 < x₁) (hx₁ : (x₁ : ℝ) ≤ x) (hx₂ : x ≤ x₂) :
    g2R x ≤ (g2Hi x₁ x₂ : ℝ) := by
  unfold g2Hi g2R
  rw [ratCast_list_sum_map]
  refine List.sum_le_sum fun bc _ => ?_
  have h1' : (0 : ℝ) < x₁ := by exact_mod_cast h1
  have hb : (0 : ℝ) ≤ bc.1 := Nat.cast_nonneg _
  split_ifs with hc
  · push_cast
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast hc)
    exact inv_anti₀ (by linarith) (by linarith)
  · push_cast
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonpos_left ?_ (by exact_mod_cast (not_le.1 hc).le)
    exact inv_anti₀ (by linarith) (by linarith)

/-! ### The kernel-checked numerical facts -/

/-- The bracket of the zero `a` of `ĝ'`. -/
def aLo : ℚ := 41929527 / 10000000

def aHi : ℚ := 41929528 / 10000000

theorem num_g1 : 0 < g1Lo aLo 64 ∧ g1Hi aHi 64 < 0 := by decide +kernel

theorem num_g : (-232.05 : ℚ) ≤ gLo aLo aHi 64 ∧ gHi aLo aHi 64 ≤ -232 := by decide +kernel

theorem num_e : (-9.36 : ℚ) ≤ eLo aLo aHi 64 ∧ eHi aLo aHi 64 ≤ -9 := by decide +kernel

theorem num_g2 : (0.1832 : ℚ) ≤ -g2Hi aLo aHi ∧ -g2Lo aLo aHi ≤ 0.1833 := by decide +kernel

/-! ### The zero `a` of `ĝ'` and the constants at `a` -/

theorem continuousOn_g1R : ContinuousOn g1R (Ioi 0) := by
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  have h1 : ContinuousAt (fun y : ℝ => (famG1 (y : ℂ)).re) x :=
    Complex.continuous_re.continuousAt.comp
      ((hasDerivAt_famG1 (u := (x : ℂ)) (by simpa using hx')).continuousAt.comp
        Complex.continuous_ofReal.continuousAt)
  have h2 : (fun y : ℝ => (famG1 (y : ℂ)).re) =ᶠ[nhds x] g1R := by
    filter_upwards [Ioi_mem_nhds hx'] with y hy
    rw [famG1_ofReal hy, ofReal_re]
  exact (h1.congr h2).continuousWithinAt

theorem exists_root : ∃ a ∈ Icc (aLo : ℝ) aHi, g1R a = 0 := by
  have hlo : 0 < g1R aLo :=
    lt_of_lt_of_le (by exact_mod_cast num_g1.1) (g1Lo_le (by norm_num [aLo]) 64)
  have hhi : g1R aHi < 0 :=
    lt_of_le_of_lt (le_g1Hi (by norm_num [aHi]) 64) (by exact_mod_cast num_g1.2)
  have hle : (aLo : ℝ) ≤ aHi := by norm_num [aLo, aHi]
  have hc : ContinuousOn g1R (Icc (aLo : ℝ) aHi) :=
    continuousOn_g1R.mono fun x hx => lt_of_lt_of_le (by norm_num [aLo]) hx.1
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hle hc ⟨hhi.le, hlo.le⟩
  exact ⟨c, hc, hc0⟩

/-- The zero `a ≈ 4.192952714` of `ĝ'`. -/
noncomputable def famA : ℝ := exists_root.choose

theorem famA_mem : famA ∈ Icc (aLo : ℝ) aHi := exists_root.choose_spec.1

theorem g1R_famA : g1R famA = 0 := exists_root.choose_spec.2

theorem famA_lo : (4.1929527 : ℝ) ≤ famA := by
  have := famA_mem.1
  norm_num [aLo] at this
  linarith

theorem famA_hi : famA ≤ (4.1929528 : ℝ) := by
  have := famA_mem.2
  norm_num [aHi] at this
  linarith

theorem famA_pos : 0 < famA := lt_of_lt_of_le (by norm_num) famA_lo

/-- `D̄ = -ĝ''(a)`. -/
noncomputable def famD : ℝ := -g2R famA

theorem famD_bounds : (0.1832 : ℝ) ≤ famD ∧ famD ≤ 0.1833 := by
  have h1 := le_g2Hi (x := famA) (x₁ := aLo) (x₂ := aHi) (by norm_num [aLo]) famA_mem.1 famA_mem.2
  have h2 := g2Lo_le (x := famA) (x₁ := aLo) (x₂ := aHi) (by norm_num [aLo]) famA_mem.1 famA_mem.2
  have n1 : ((0.1832 : ℚ) : ℝ) ≤ ((-g2Hi aLo aHi : ℚ) : ℝ) := by exact_mod_cast num_g2.1
  have n2 : ((-g2Lo aLo aHi : ℚ) : ℝ) ≤ ((0.1833 : ℚ) : ℝ) := by exact_mod_cast num_g2.2
  push_cast at n1 n2
  unfold famD
  constructor <;> linarith

theorem famD_pos : 0 < famD := lt_of_lt_of_le (by norm_num) famD_bounds.1

theorem gR_famA : (-232.05 : ℝ) ≤ gR famA ∧ gR famA ≤ -232 := by
  have h1 := gLo_le (x := famA) (x₁ := aLo) (x₂ := aHi) (by norm_num [aLo]) famA_mem.1
    famA_mem.2 64
  have h2 := le_gHi (x := famA) (x₁ := aLo) (x₂ := aHi) (by norm_num [aLo]) famA_mem.1
    famA_mem.2 64
  have n1 : ((-232.05 : ℚ) : ℝ) ≤ ((gLo aLo aHi 64 : ℚ) : ℝ) := by exact_mod_cast num_g.1
  have n2 : ((gHi aLo aHi 64 : ℚ) : ℝ) ≤ ((-232 : ℚ) : ℝ) := by exact_mod_cast num_g.2
  push_cast at n1 n2
  constructor <;> linarith

theorem eR_famA : (-9.36 : ℝ) ≤ eR famA ∧ eR famA ≤ -9 := by
  have h1 := eLo_le (x := famA) (x₁ := aLo) (x₂ := aHi) (by norm_num [aLo]) famA_mem.1
    famA_mem.2 64
  have h2 := le_eHi (x := famA) (x₁ := aLo) (x₂ := aHi) (by norm_num [aLo]) famA_mem.1
    famA_mem.2 64
  have n1 : ((-9.36 : ℚ) : ℝ) ≤ ((eLo aLo aHi 64 : ℚ) : ℝ) := by exact_mod_cast num_e.1
  have n2 : ((eHi aLo aHi 64 : ℚ) : ℝ) ≤ ((-9 : ℚ) : ℝ) := by exact_mod_cast num_e.2
  push_cast at n1 n2
  constructor <;> linarith

theorem famG1_famA : famG1 (famA : ℂ) = 0 := by
  rw [famG1_ofReal famA_pos, g1R_famA, ofReal_zero]

theorem famG2_famA : famG2 (famA : ℂ) = -((famD : ℝ) : ℂ) := by
  rw [famG2_ofReal, famD, ofReal_neg, neg_neg]

theorem norm_famE1_famA : ‖famE1 (famA : ℂ)‖ ≤ 2 / 78 := by
  rw [famE1_ofReal famA_pos, Complex.norm_real, Real.norm_eq_abs]
  have ha := famA_lo
  have h74 : (0 : ℝ) < 74 + famA := by linarith
  have h1 : Real.log (74 + famA) ≤ Real.log (76 + famA) := Real.log_le_log h74 (by linarith)
  have h2 : Real.log (76 + famA) - Real.log (74 + famA) ≤ 2 / 78 := by
    rw [← Real.log_div (by linarith) (by linarith)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one h74.ne', div_le_div_iff₀ h74 (by norm_num)]
    linarith
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  exact h2

end Large

end OddZeta
