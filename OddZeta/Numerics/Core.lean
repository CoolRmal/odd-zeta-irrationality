/-
Copyright (c) 2026. All rights reserved.
-/
import OddZeta.Numerics.SeriesBounds

/-!
# Kernel-friendly evaluation of the `artanh` / `arctan` series

All computations here use only `ℕ` arithmetic (which the Lean kernel accelerates with GMP):
`Int` arithmetic is avoided since in the kernel it is several times slower.

* `horner neg A B cs` evaluates `∑ cs[k] (±A)^k B^(len-1-k)` exactly.
* `seriesNN neg a b n P` returns natural numbers `lo ≤ 2^P f(a/b) ≤ hi`, where
  `f = artanh` (`neg = false`) or `f = arctan` (`neg = true`) and `a < b`; it sums `n` terms of
  the power series exactly (as a rational number with a single final rounding) and adds a
  rigorous tail bound computed from `a / b`.
-/

namespace OddZeta.Num

open Finset

/-! ### Coefficients `L / (2k+1)` -/

/-- `oddProd n = 1 * 3 * 5 * ⋯ * (2n-1)`. -/
def oddProd : ℕ → ℕ
  | 0 => 1
  | n + 1 => oddProd n * (2 * n + 1)

/-- `[L/1, L/3, …, L/(2n-1)]` with `L = oddProd n`. -/
def oddCoeffs (n : ℕ) : List ℕ := (List.range n).map fun k => oddProd n / (2 * k + 1)

/-- Literal value of `oddCoeffs 16` (so that the kernel does not recompute it). -/
def coeffList16 : List ℕ :=
  [191898783962510625, 63966261320836875, 38379756792502125, 27414111994644375,
   21322087106945625, 17445343996591875, 14761444920193125, 12793252264167375,
   11288163762500625, 10099935998026875, 9138037331548125, 8343425389674375,
   7675951358500425, 7107362368981875, 6617199446983125, 6190283353629375]

/-- Literal value of `oddProd 16`. -/
def coeffL16 : ℕ := 191898783962510625

/-- Coefficient list (whose first `n` entries are used) and the common numerator `L`. -/
def coeffs (n : ℕ) : List ℕ × ℕ :=
  bif Nat.ble n 16 then (coeffList16, coeffL16) else (oddCoeffs n, oddProd n)

/-! ### Horner scheme -/

/-- `horner neg A B cs = (H, B^len)` with `H * B = ∑ cs[k] (±A)^k B^(len-k)`
(the sign is `-` if `neg`).  Defined with `List.rec` directly: the kernel evaluates raw
recursors much faster than equation-compiler (`brecOn`) definitions. -/
def horner (neg : Bool) (A B : ℕ) (cs : List ℕ) : ℕ × ℕ :=
  cs.rec (0, 1) fun c _ r => (bif neg then c * r.2 - A * r.1 else c * r.2 + A * r.1, B * r.2)

@[simp] theorem horner_nil (neg : Bool) (A B : ℕ) : horner neg A B [] = (0, 1) := rfl

@[simp] theorem horner_cons (neg : Bool) (A B c : ℕ) (cs : List ℕ) :
    horner neg A B (c :: cs) =
      (bif neg then c * (horner neg A B cs).2 - A * (horner neg A B cs).1
        else c * (horner neg A B cs).2 + A * (horner neg A B cs).1, B * (horner neg A B cs).2) :=
  rfl

/-- `horner` on the first `n` entries of `cs` (lazily: the rest of the list is not visited). -/
def hornerN (neg : Bool) (A B : ℕ) (cs : List ℕ) : ℕ → ℕ × ℕ :=
  cs.rec (fun _ => (0, 1)) fun c _ r n =>
    match n with
    | 0 => (0, 1)
    | m + 1 =>
      let x := r m
      (bif neg then Nat.sub (Nat.mul c x.2) (Nat.mul A x.1)
        else Nat.add (Nat.mul c x.2) (Nat.mul A x.1), Nat.mul B x.2)

theorem hornerN_eq (neg : Bool) (A B : ℕ) :
    ∀ (cs : List ℕ) (n : ℕ), hornerN neg A B cs n = horner neg A B (cs.take n)
  | [], n => by cases n <;> rfl
  | c :: cs, 0 => rfl
  | c :: cs, m + 1 => by
    rw [List.take_succ_cons, horner_cons, ← hornerN_eq neg A B cs m]
    rfl

/-- Bounds `lo ≤ 2^P * f (a/b) ≤ hi` for `f = artanh` (`neg = false`) or `f = arctan`
(`neg = true`), valid when `a < b`, using `n` terms of the power series.
(Written with `Nat.mul` etc. rather than `*`, which saves the kernel the instance unfolding;
see `seriesNN_eq` for the readable form.) -/
def seriesNN (neg : Bool) (a b n P : ℕ) : ℕ × ℕ :=
  let A := Nat.mul a a
  let B := Nat.mul b b
  let cL := coeffs n
  let r := hornerN neg A B cL.1 n
  let q := Nat.div (Nat.shiftLeft (Nat.mul (Nat.mul a b) r.1) P) (Nat.mul cL.2 r.2)
  let F := Nat.div (Nat.shiftLeft (Nat.mul (Nat.pow a (Nat.add (Nat.mul 2 n) 1)) b) P)
    (Nat.mul r.2 (Nat.sub B A))
  (Nat.sub (Nat.sub q F) 1, Nat.add (Nat.add q F) 2)

theorem seriesNN_eq (neg : Bool) (a b n P : ℕ) : seriesNN neg a b n P =
    (let A := a * a
     let B := b * b
     let cL := coeffs n
     let r := hornerN neg A B cL.1 n
     let q := ((a * b * r.1) <<< P) / (cL.2 * r.2)
     let F := ((a ^ (2 * n + 1) * b) <<< P) / (r.2 * (B - A))
     (q - F - 1, q + F + 2)) := rfl

/-! ### Correctness -/

/-- Valid coefficient data for `n` terms. -/
structure CoeffOK (n : ℕ) (cs : List ℕ) (L : ℕ) : Prop where
  length : cs.length = n
  mul : ∀ k < n, cs.getD k 0 * (2 * k + 1) = L
  anti : cs.Pairwise (· ≥ ·)
  pos : 0 < L

theorem dvd_oddProd {n k : ℕ} (hk : k < n) : 2 * k + 1 ∣ oddProd n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [oddProd]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · exact Dvd.dvd.mul_right (ih h) _
    · subst h; exact Dvd.intro_left _ rfl

theorem oddProd_pos : ∀ n, 0 < oddProd n
  | 0 => Nat.one_pos
  | n + 1 => Nat.mul_pos (oddProd_pos n) (by omega)

theorem oddCoeffs_ok (n : ℕ) : CoeffOK n (oddCoeffs n) (oddProd n) where
  length := by simp [oddCoeffs]
  mul k hk := by
    simp only [oddCoeffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some]
    exact Nat.div_mul_cancel (dvd_oddProd hk)
  anti := by
    unfold oddCoeffs
    rw [List.pairwise_map]
    refine List.Pairwise.imp (fun {i j} (h : i < j) => ?_) (List.pairwise_lt_range (n := n))
    exact Nat.div_le_div_left (by omega) (by omega)
  pos := oddProd_pos n

theorem coeffList16_ok : CoeffOK 16 coeffList16 coeffL16 := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro k hk
  interval_cases k <;> decide

theorem coeffs_ok (n : ℕ) : CoeffOK n ((coeffs n).1.take n) (coeffs n).2 := by
  unfold coeffs
  cases hn' : Nat.ble n 16
  · simp only [Bool.cond_false]
    have h := oddCoeffs_ok n
    rwa [List.take_of_length_le (le_of_eq h.length)]
  · have hn : n ≤ 16 := Nat.le_of_ble_eq_true hn'
    simp only [Bool.cond_true]
    obtain ⟨hl, hm, ha, hp⟩ := coeffList16_ok
    refine ⟨by simp [hl, hn], fun k hk => ?_, ha.sublist (List.take_sublist _ _), hp⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, ← List.getD_eq_getElem?_getD]
    exact hm k (by omega)

theorem horner_snd (neg : Bool) (A B : ℕ) :
    ∀ cs : List ℕ, (horner neg A B cs).2 = B ^ cs.length
  | [] => rfl
  | c :: cs => by
    simp only [horner_cons, List.length_cons, horner_snd neg A B cs, pow_succ, mul_comm]

theorem horner_true_fst_le (A B c : ℕ) (cs : List ℕ) :
    (horner true A B (c :: cs)).1 ≤ c * B ^ cs.length := by
  simp only [horner_cons, Bool.cond_true, horner_snd]
  exact Nat.sub_le _ _

theorem horner_real (neg : Bool) {A B : ℕ} (hAB : A ≤ B) :
    ∀ cs : List ℕ, cs.Pairwise (· ≥ ·) →
      ((horner neg A B cs).1 : ℝ) * B =
        ∑ k ∈ range cs.length, (cs.getD k 0 : ℝ) * (serSign neg * A) ^ k * (B : ℝ) ^ (cs.length - k)
  | [] => fun _ => by simp
  | c :: cs => fun hcs => by
    have ih := horner_real neg hAB cs hcs.of_cons
    have hH : ((horner neg A B (c :: cs)).1 : ℝ) =
        c * (B : ℝ) ^ cs.length + serSign neg * A * (horner neg A B cs).1 := by
      cases neg
      · simp [horner_snd, serSign]
      · -- no truncation in the subtraction
        have hle : A * (horner true A B cs).1 ≤ c * B ^ cs.length := by
          rcases cs with _ | ⟨c', cs'⟩
          · simp
          · have h1 := horner_true_fst_le A B c' cs'
            have hc' : c' ≤ c := List.rel_of_pairwise_cons hcs (by simp)
            calc A * (horner true A B (c' :: cs')).1
                ≤ B * (c' * B ^ cs'.length) := Nat.mul_le_mul hAB h1
              _ ≤ c * B ^ (c' :: cs').length := by
                rw [List.length_cons, pow_succ]
                calc B * (c' * B ^ cs'.length) = c' * (B ^ cs'.length * B) := by ring
                  _ ≤ c * (B ^ cs'.length * B) := Nat.mul_le_mul_right _ hc'
        simp only [horner_cons, Bool.cond_true, horner_snd]
        rw [Nat.cast_sub (by simpa [horner_snd] using hle)]
        simp [serSign]
        ring
    rw [hH, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, Nat.sub_zero]
    have hsum : ∑ k ∈ range cs.length, (cs.getD k 0 : ℝ) * (serSign neg * A) ^ (k + 1) *
        (B : ℝ) ^ (cs.length + 1 - (k + 1)) =
        serSign neg * A * ∑ k ∈ range cs.length,
          (cs.getD k 0 : ℝ) * (serSign neg * A) ^ k * (B : ℝ) ^ (cs.length - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.add_sub_add_right, pow_succ]
      ring
    rw [hsum, ← ih]
    ring

/-- `x / y ≤ ⌊x / y⌋ + 1` for natural division, as reals. -/
theorem natCast_div_lt_add_one (x : ℕ) {y : ℕ} (hy : 0 < y) :
    (x : ℝ) / y < ((x / y : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_div_mul_add (a := x) hy
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  rw [div_lt_iff₀ hy']
  have : (x : ℝ) < ((x / y : ℕ) : ℝ) * y + y := by exact_mod_cast h
  linarith

/-- The partial sum of the series equals `a b H / (L B^n)`. -/
theorem sum_serTerm_eq (neg : Bool) {a b n : ℕ} (hab : a < b) :
    ∑ k ∈ range n, serTerm neg ((a : ℝ) / b) k =
      ((a * b * (horner neg (a * a) (b * b) ((coeffs n).1.take n)).1 : ℕ) : ℝ) /
        (((coeffs n).2 * (b * b) ^ n : ℕ) : ℝ) := by
  obtain ⟨hlen, hmul, hanti, hLpos⟩ := coeffs_ok n
  set cs := (coeffs n).1.take n
  set L := (coeffs n).2
  set H := (horner neg (a * a) (b * b) cs).1
  have hb : (0 : ℝ) < b := by exact_mod_cast (Nat.zero_le a).trans_lt hab
  have hAB : a * a ≤ b * b := Nat.mul_le_mul hab.le hab.le
  have hH := horner_real neg hAB cs hanti
  rw [hlen] at hH
  have hL : (0 : ℝ) < L := by exact_mod_cast hLpos
  have key : ∀ k ∈ range n, serTerm neg ((a : ℝ) / b) k * (L * ((b : ℝ) * b) ^ n * (b * b)) =
      a * b * ((cs.getD k 0 : ℝ) * (serSign neg * ((a : ℝ) * a)) ^ k *
        ((b : ℝ) * b) ^ (n - k)) := by
    intro k hk
    have hk' := mem_range.mp hk
    have hc : (cs.getD k 0 : ℝ) = L / (2 * k + 1) := by
      have := hmul k hk'
      rw [eq_div_iff (by positivity)]
      exact_mod_cast this
    obtain ⟨j, rfl⟩ : ∃ j, n = k + 1 + j := ⟨n - k - 1, by omega⟩
    have hj : k + 1 + j - k = j + 1 := by omega
    have hb' : (b : ℝ) ≠ 0 := hb.ne'
    rw [hc, hj, serTerm, div_pow]
    field_simp
    ring
  have hsum : (∑ k ∈ range n, serTerm neg ((a : ℝ) / b) k) * (L * ((b : ℝ) * b) ^ n) * (b * b) =
      a * b * (H * (b * b)) := by
    have := Finset.sum_congr rfl key
    rw [← Finset.sum_mul, ← Finset.mul_sum] at this
    push_cast at hH ⊢
    rw [hH, ← this]
    ring
  have hbb : (0 : ℝ) < b * b := by positivity
  have h3 : (∑ k ∈ range n, serTerm neg ((a : ℝ) / b) k) * (L * ((b : ℝ) * b) ^ n) * (b * b) =
      (a * b * H) * (b * b) := by rw [hsum]; ring
  have h2 := mul_right_cancel₀ hbb.ne' h3
  push_cast
  rw [eq_div_iff (by positivity)]
  exact h2

theorem seriesNN_spec (neg : Bool) {a b : ℕ} (hab : a < b) (n P : ℕ) :
    ((seriesNN neg a b n P).1 : ℝ) ≤ 2 ^ P * serF neg ((a : ℝ) / b) ∧
      2 ^ P * serF neg ((a : ℝ) / b) ≤ ((seriesNN neg a b n P).2 : ℝ) := by
  obtain ⟨hlen, hmul, hanti, hLpos⟩ := coeffs_ok n
  have hb0 : 0 < b := (Nat.zero_le a).trans_lt hab
  have hb : (0 : ℝ) < b := by exact_mod_cast hb0
  have hu0 : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
  have hu1 : (a : ℝ) / b < 1 := by
    rw [div_lt_one hb]; exact_mod_cast hab
  have hu : |(a : ℝ) / b| < 1 := by rw [abs_of_nonneg hu0]; exact hu1
  have htail := abs_serF_sub_sum_le neg hu n
  rw [sum_serTerm_eq neg hab, abs_of_nonneg hu0] at htail
  have hpos := serF_nonneg neg hu0 hu1
  set H := (horner neg (a * a) (b * b) ((coeffs n).1.take n)).1
  set L := (coeffs n).2
  have hr2 : (horner neg (a * a) (b * b) ((coeffs n).1.take n)).2 = (b * b) ^ n := by
    rw [horner_snd, hlen]
  -- the rounded main term
  set q := ((a * b * H) <<< P) / (L * (b * b) ^ n) with hq
  set F := ((a ^ (2 * n + 1) * b) <<< P) / ((b * b) ^ n * (b * b - a * a)) with hF
  have hs : seriesNN neg a b n P = (q - F - 1, q + F + 2) := by
    simp only [seriesNN_eq, hornerN_eq, hr2]; rfl
  have hden : 0 < L * (b * b) ^ n := Nat.mul_pos hLpos (by positivity)
  have hBA : 0 < b * b - a * a := Nat.sub_pos_of_lt (Nat.mul_lt_mul'' hab hab)
  have hFden : 0 < (b * b) ^ n * (b * b - a * a) := Nat.mul_pos (by positivity) hBA
  have hq1 : (q : ℝ) ≤ 2 ^ P * ((a * b * H : ℕ) / ((L * (b * b) ^ n : ℕ) : ℝ)) := by
    rw [hq, Nat.shiftLeft_eq]
    refine (Nat.cast_div_le).trans (le_of_eq ?_)
    push_cast; ring
  have hq2 : 2 ^ P * ((a * b * H : ℕ) / ((L * (b * b) ^ n : ℕ) : ℝ)) < q + 1 := by
    have := natCast_div_lt_add_one ((a * b * H) <<< P) hden
    rw [Nat.shiftLeft_eq] at this
    rw [hq, Nat.shiftLeft_eq]
    refine lt_of_eq_of_lt ?_ this
    push_cast; ring
  -- the tail bound, scaled
  have herr : 2 ^ P * (((a : ℝ) / b) ^ (2 * n + 1) / (1 - ((a : ℝ) / b) ^ 2)) =
      (((a ^ (2 * n + 1) * b) <<< P : ℕ) : ℝ) / (((b * b) ^ n * (b * b - a * a) : ℕ) : ℝ) := by
    rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_mul ((b * b) ^ n),
      Nat.cast_sub (Nat.mul_le_mul hab.le hab.le)]
    have hBA' : (0 : ℝ) < (b : ℝ) * b - a * a := by
      have : ((a * a : ℕ) : ℝ) < ((b * b : ℕ) : ℝ) := by exact_mod_cast Nat.mul_lt_mul'' hab hab
      push_cast at this; linarith
    have h1 : 1 - ((a : ℝ) / b) ^ 2 = ((b : ℝ) * b - a * a) / (b * b) := by
      field_simp
    have hb' : (b : ℝ) ≠ 0 := hb.ne'
    have hBA'' : (b : ℝ) * b - a * a ≠ 0 := hBA'.ne'
    rw [h1, div_pow]
    push_cast
    field_simp
    ring
  have hF2 : 2 ^ P * (((a : ℝ) / b) ^ (2 * n + 1) / (1 - ((a : ℝ) / b) ^ 2)) < F + 1 := by
    rw [herr, hF]; exact natCast_div_lt_add_one _ hFden
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  rw [abs_le] at htail
  obtain ⟨ht1, ht2⟩ := htail
  rw [hs]
  constructor
  · simp only
    rcases le_or_gt (F + 1) q with h | h
    · rw [Nat.sub_sub, Nat.cast_sub h]
      push_cast
      nlinarith
    · rw [Nat.sub_sub, Nat.sub_eq_zero_of_le h.le]
      simp only [Nat.cast_zero]
      positivity
  · simp only
    push_cast
    nlinarith

end OddZeta.Num
