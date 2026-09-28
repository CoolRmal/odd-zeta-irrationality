import OddZeta.Phi.Defs

/-!
# A kernel-checkable certificate for lower bounds of `φ(x) = min_y φ₀(x, y)`

## Mathematics

For `t ∈ [0, 1)` and every `x`, each `ι`-term of `φ₀(x, t)` is an integer combination of
`⌊a x⌋`, `[t < {a x}]`, `[t = {a x}]` and `[{a x} < t]` for multipliers `a ∈ ℕ`
(`terms`, `phi0_add_eq_terms`; the term `-[{η₀ x} < t]` is rewritten as
`[t < {η₀ x}] + [t = {η₀ x}] - 1`, so that all indicator weights are in `ℕ`).  Collecting equal
multipliers (`atoms`, `phi0_add_eq_atoms`) gives, for `t ∈ [0, 1)`,
`φ₀(x, t) + |zs| = ∑_a ((cp - cn)(a) ⌊a x⌋ + l(a) [t < {a x}] + e(a) [t = {a x}]`
`+ r(a) [{a x} < t])`.

On an interval `(α, β)` with `α = nα/dα`, `β = nβ/dβ`, the checker (`stepI`)
* verifies `⌊a x⌋ = k_a := ⌊a α⌋` on `(α, β)` (`a nβ ≤ (k_a + 1) dβ`);
* sorts the points `{a x} = a x - k_a` of the atoms with indicator weights (key: `({a α}, a)`
  lexicographically, i.e. the order at `α⁺`) by insertion sort, starting from the order of the
  previous interval, and verifies that consecutive points are strictly increasing on the whole
  interval (a linear condition, checked at `α` if the slope difference is positive and at `β`
  otherwise);
* computes `min_t` of the step function in `t` by a sweep over the sorted points (`sweep`);
* checks `v + |zs| + ∑ cn(a) k_a ≤ ∑ cp(a) k_a + min`.

All arithmetic is on `ℕ`, written with `Nat.add`, `Nat.mul`, `Nat.ble`, `cond` for fast kernel
reduction.  To keep the kernel's memory bounded, the order is reset every `chunkB + 1 = 100`
intervals, and `checkPhiCert` is proved from the chunks `chunkOK … j`, each by its own
`decide +kernel` (`checkPhiCert_of_chunks`).

## Main results

* `checkPhiCert η₀ zs ps X vals : Bool`.
* `phi0_ge_of_checkPhiCert`: on `(X[i], X[i+1])`, `vals[i] ≤ φ₀(x, y)` for all `y`.
* `phiStep X vals x` (the step function `vals[i]` on `{x} ∈ (X[i], X[i+1])`, `0` elsewhere),
  `phiStep_le` and `phiStep_eq`.
* `checkPhiCert_length`, `globalOK_of_checkPhiCert`: `X` is strictly increasing from `0` to `1`
  and has one more entry than `vals`.
-/

namespace OddZeta

namespace PhiCert

/-! ## The computable checker -/

/-- A multiplier `a` with weights; it stands for
`(cp - cn) ⌊a x⌋ + l [t < {a x}] + e [t = {a x}] + r [{a x} < t]` (see `Atom.val`). -/
structure Atom where
  /-- the multiplier -/
  a : ℕ
  /-- positive weight of `⌊a x⌋` -/
  cp : ℕ
  /-- negative weight of `⌊a x⌋` -/
  cn : ℕ
  /-- weight of `[t < {a x}]` -/
  l : ℕ
  /-- weight of `[t = {a x}]` -/
  e : ℕ
  /-- weight of `[{a x} < t]` -/
  r : ℕ

/-- The terms whose values sum to `φ₀(x, t) + |zs|` for `t ∈ [0, 1)` (see `phi0_eq_terms`). -/
def terms (η₀ : ℕ) (zs ps : List ℕ) : List Atom :=
  zs.flatMap (fun η => [⟨η, 0, 1, 1, 0, 0⟩, ⟨η₀, 1, 0, 1, 1, 0⟩, ⟨η₀ - η, 0, 1, 0, 0, 1⟩]) ++
  ps.flatMap (fun η => [⟨η₀ - 2 * η, 1, 0, 0, 0, 0⟩, ⟨η, 1, 0, 1, 0, 0⟩, ⟨η₀ - η, 0, 1, 0, 0, 1⟩])

/-- Total weight `f` of the multiplier `a` in `T`. -/
def wsum (T : List Atom) (a : ℕ) (f : Atom → ℕ) : ℕ :=
  (T.map fun c => if c.a = a then f c else 0).sum

/-- All terms of `T` with multiplier `a`, merged into one atom. -/
def merge (T : List Atom) (a : ℕ) : Atom :=
  let cp := wsum T a Atom.cp
  let cn := wsum T a Atom.cn
  ⟨a, cp - cn, cn - cp, wsum T a Atom.l, wsum T a Atom.e, wsum T a Atom.r⟩

/-- The distinct multipliers, with their merged weights. -/
def atoms (η₀ : ℕ) (zs ps : List ℕ) : List Atom :=
  let T := terms η₀ zs ps
  ((T.map Atom.a).dedup).map (merge T)

/-- The atoms without indicator weights. -/
def atomsF (η₀ : ℕ) (zs ps : List ℕ) : List Atom :=
  (atoms η₀ zs ps).filter fun c => c.l + c.e + c.r = 0

/-- The atoms with indicator weights (the points of the sweep). -/
def atomsS (η₀ : ℕ) (zs ps : List ℕ) : List Atom :=
  (atoms η₀ zs ps).filter fun c => c.l + c.e + c.r ≠ 0

/-- An atom evaluated on the interval `(nα/dα, nβ/dβ)`: `k = ⌊a α⌋`, `r = a nα - k dα`,
`w = a nβ`, `kd = k dβ`; `key` encodes the order of `{a x}` at `α⁺`. -/
structure Entry where
  /-- sort key -/
  key : ℕ
  /-- `⌊a α⌋` -/
  k : ℕ
  /-- `a nα mod dα` -/
  r : ℕ
  /-- `a nβ` -/
  w : ℕ
  /-- `k dβ` -/
  kd : ℕ
  /-- the atom -/
  atom : Atom

/-! The functions below are evaluated by the kernel; they use `Nat.add`, `Nat.mul`, `Nat.ble`
and `cond` directly (no type classes, no `Decidable`) for speed. -/

/-- Evaluate an atom on the interval `(nα/dα, nβ/dβ)`. -/
def mkEntry (nα dα nβ dβ : ℕ) (c : Atom) : Entry :=
  let P := Nat.mul c.a nα
  let k := Nat.div P dα
  let r := Nat.mod P dα
  ⟨Nat.add (Nat.mul r 1024) c.a, k, r, Nat.mul c.a nβ, Nat.mul k dβ, c⟩

/-- Insert into a list sorted by `key`. -/
def insE (e : Entry) : List Entry → List Entry
  | [] => [e]
  | f :: l => cond (Nat.ble e.key f.key) (e :: f :: l) (f :: insE e l)

/-- Insertion sort by `key` (linear time on almost sorted input). -/
def sortE : List Entry → List Entry
  | [] => []
  | e :: l => insE e (sortE l)

/-- `⌊a x⌋ = k` on the interval, for all entries. -/
def entsOK (dβ : ℕ) : List Entry → Bool
  | [] => true
  | e :: l => Nat.ble e.w (Nat.add e.kd dβ) && entsOK dβ l

/-- Consecutive points are strictly increasing on the interval. -/
def chainOK : List Entry → Bool
  | e :: f :: rest =>
    cond (Nat.blt e.atom.a f.atom.a) (Nat.ble e.r f.r)
      (cond (Nat.blt f.atom.a e.atom.a) (Nat.ble (Nat.add e.w f.kd) (Nat.add f.w e.kd)) false) &&
    chainOK (f :: rest)
  | _ => true

/-- `min` on `ℕ`. -/
def nmin (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

/-- Sweep over the sorted points: returns `(∑ l, min_t g(t))` where
`g(t) = ∑ l [t < p] + e [t = p] + r [p < t]`. -/
def sweep : List Entry → ℕ × ℕ
  | [] => (0, 0)
  | e :: rest =>
    match sweep rest with
    | (s, m) => (Nat.add e.atom.l s,
        nmin (Nat.add e.atom.l s) (nmin (Nat.add e.atom.e s) (Nat.add e.atom.r m)))

/-- `∑ cp k` over the entries. -/
def cpSum : List Entry → ℕ
  | [] => 0
  | e :: l => Nat.add (Nat.mul e.atom.cp e.k) (cpSum l)

/-- `∑ cn k` over the entries. -/
def cnSum : List Entry → ℕ
  | [] => 0
  | e :: l => Nat.add (Nat.mul e.atom.cn e.k) (cnSum l)

/-- `⌊a x⌋ = ⌊a α⌋` on the interval, for the floor-only atoms. -/
def floorsOK (nα dα nβ dβ : ℕ) : List Atom → Bool
  | [] => true
  | c :: l => Nat.ble (Nat.mul c.a nβ) (Nat.add (Nat.mul (Nat.div (Nat.mul c.a nα) dα) dβ) dβ) &&
      floorsOK nα dα nβ dβ l

/-- `∑ cp ⌊a α⌋` over the floor-only atoms. -/
def fpSum (nα dα : ℕ) : List Atom → ℕ
  | [] => 0
  | c :: l => Nat.add (Nat.mul c.cp (Nat.div (Nat.mul c.a nα) dα)) (fpSum nα dα l)

/-- `∑ cn ⌊a α⌋` over the floor-only atoms. -/
def fnSum (nα dα : ℕ) : List Atom → ℕ
  | [] => 0
  | c :: l => Nat.add (Nat.mul c.cn (Nat.div (Nat.mul c.a nα) dα)) (fnSum nα dα l)

/-- Check one interval `(α, β)` with value `v`, given the previous order `ord` of the sweep
atoms; returns the new order. `off = |zs|`. -/
def stepI (atF : List Atom) (off : ℕ) (ord : List Atom) (α β : ℚ) (v : ℕ) :
    Option (List Atom) :=
  match α.num, β.num with
  | Int.ofNat nα, Int.ofNat nβ =>
    let dα := α.den
    let dβ := β.den
    let es := sortE (ord.map (mkEntry nα dα nβ dβ))
    cond (Nat.blt (Nat.mul nα dβ) (Nat.mul nβ dα) && floorsOK nα dα nβ dβ atF &&
        entsOK dβ es && chainOK es &&
        Nat.ble (Nat.add (Nat.add (Nat.add v off) (fnSum nα dα atF)) (cnSum es))
          (Nat.add (Nat.add (fpSum nα dα atF) (cpSum es)) (sweep es).2))
      (some (es.map Entry.atom)) none
  | _, _ => none

/-- Check the intervals, restarting the sweep order from `S` every `B + 1` intervals
(`c` counts down the remaining intervals of the current block).  With `stop = true` the check
stops (successfully) at the end of the first block; this is used to split the kernel
computation into independent chunks (`loopGen_of_chunks`). -/
def loopGen (atF S : List Atom) (off B : ℕ) (stop : Bool) :
    ℕ → List Atom → List ℚ → List ℕ → Bool
  | c, ord, α :: β :: rest, v :: vs =>
    match stepI atF off ord α β v with
    | some ord' =>
      match c with
      | 0 => cond stop true (loopGen atF S off B stop B S (β :: rest) vs)
      | c + 1 => loopGen atF S off B stop c ord' (β :: rest) vs
    | none => false
  | _, _, [_], [] => true
  | _, _, _, _ => false

/-- Length of a chunk, minus one. -/
def chunkB : ℕ := 99

/-- The global part of the check. -/
def globalOK (η₀ : ℕ) (zs ps : List ℕ) (X : List ℚ) : Bool :=
  zs.all (fun η => decide (η ≤ η₀)) && ps.all (fun η => decide (2 * η ≤ η₀)) &&
  decide (X.head? = some 0) && decide (X.getLast? = some 1)

/-- The `j`-th chunk of the check (intervals `j (chunkB + 1), …, j (chunkB + 1) + chunkB`). -/
def chunkOK (η₀ : ℕ) (zs ps : List ℕ) (X : List ℚ) (vals : List ℕ) (j : ℕ) : Bool :=
  loopGen (atomsF η₀ zs ps) (atomsS η₀ zs ps) zs.length chunkB true chunkB (atomsS η₀ zs ps)
    (X.drop (j * (chunkB + 1))) (vals.drop (j * (chunkB + 1)))

end PhiCert

open PhiCert in
/-- The certificate checker: `X` is strictly increasing from `0` to `1`, `vals` has one entry
per interval, and `vals[i] ≤ φ₀(x, y)` for `x ∈ (X[i], X[i+1])` (see
`phi0_ge_of_checkPhiCert`). -/
def checkPhiCert (η₀ : ℕ) (zs ps : List ℕ) (X : List ℚ) (vals : List ℕ) : Bool :=
  globalOK η₀ zs ps X &&
  loopGen (atomsF η₀ zs ps) (atomsS η₀ zs ps) zs.length chunkB false chunkB (atomsS η₀ zs ps) X vals

namespace PhiCert

/-! ## Soundness: the identity for `φ₀` -/

/-- The indicator part of an atom at the point `p`. -/
noncomputable def indVal (c : Atom) (p t : ℝ) : ℕ :=
  c.l * (if t < p then 1 else 0) + c.e * (if t = p then 1 else 0) + c.r * (if p < t then 1 else 0)

/-- The value `(cp - cn) ⌊a x⌋ + l [t < {a x}] + e [t = {a x}] + r [{a x} < t]` of an atom. -/
noncomputable def Atom.val (c : Atom) (x t : ℝ) : ℤ :=
  ((c.cp : ℤ) - c.cn) * ⌊(c.a : ℝ) * x⌋ + (indVal c (Int.fract ((c.a : ℝ) * x)) t : ℤ)

theorem floor_t {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : ⌊t⌋ = 0 :=
  Int.floor_eq_zero_iff.2 ⟨ht0, ht1⟩

theorem floor_t_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (u : ℝ) :
    ⌊t - u⌋ = -⌊u⌋ - (if t < Int.fract u then 1 else 0) := by
  have h0 := Int.fract_nonneg u
  have h1 := Int.fract_lt_one u
  have hu := Int.floor_add_fract u
  rw [Int.floor_eq_iff]
  split_ifs with h <;> push_cast <;> constructor <;> linarith

theorem floor_sub_t {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (u : ℝ) :
    ⌊u - t⌋ = ⌊u⌋ - (if Int.fract u < t then 1 else 0) := by
  have h0 := Int.fract_nonneg u
  have h1 := Int.fract_lt_one u
  have hu := Int.floor_add_fract u
  rw [Int.floor_eq_iff]
  split_ifs with h <;> push_cast <;> constructor <;> linarith

theorem ite_lt_eq (p t : ℝ) :
    (if p < t then (1 : ℤ) else 0) = 1 - (if t < p then 1 else 0) - (if t = p then 1 else 0) := by
  rcases lt_trichotomy t p with h | h | h
  · simp [h, h.ne, not_lt.2 h.le]
  · simp [h]
  · simp [h, h.ne', not_lt.2 h.le]

theorem sum_val_zs (η₀ η : ℕ) (h : η ≤ η₀) (x : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (([⟨η, 0, 1, 1, 0, 0⟩, ⟨η₀, 1, 0, 1, 1, 0⟩, ⟨η₀ - η, 0, 1, 0, 0, 1⟩] : List Atom).map
      (·.val x t)).sum =
    iota (t - η * x) (η * x) + iota ((η₀ - η : ℝ) * x - t) (η * x) + 1 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Atom.val, indVal,
    Nat.cast_sub h]
  unfold iota
  rw [sub_add_cancel, show ((η₀ : ℝ) - η) * x - t + η * x = η₀ * x - t by ring, floor_t ht0 ht1,
    floor_t_sub ht0 ht1, floor_sub_t ht0 ht1, floor_sub_t ht0 ht1,
    ite_lt_eq (Int.fract ((η₀ : ℝ) * x)) t]
  push_cast
  ring

theorem sum_val_ps (η₀ η : ℕ) (h : 2 * η ≤ η₀) (x : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (([⟨η₀ - 2 * η, 1, 0, 0, 0, 0⟩, ⟨η, 1, 0, 1, 0, 0⟩, ⟨η₀ - η, 0, 1, 0, 0, 1⟩] : List Atom).map
      (·.val x t)).sum =
    iota (t - η * x) ((η₀ - η : ℝ) * x - t) := by
  have h' : η ≤ η₀ := by omega
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Atom.val, indVal,
    Nat.cast_sub h, Nat.cast_sub h', Nat.cast_mul, Nat.cast_ofNat]
  unfold iota
  rw [show t - η * x + ((η₀ - η : ℝ) * x - t) = (η₀ - 2 * η) * x by ring,
    floor_t_sub ht0 ht1, floor_sub_t ht0 ht1]
  push_cast
  ring

theorem sum_val_zs_list (η₀ : ℕ) (zs : List ℕ) (hz : ∀ η ∈ zs, η ≤ η₀) (x : ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ((zs.flatMap fun η => ([⟨η, 0, 1, 1, 0, 0⟩, ⟨η₀, 1, 0, 1, 1, 0⟩, ⟨η₀ - η, 0, 1, 0, 0, 1⟩] :
      List Atom)).map (·.val x t)).sum =
    (zs.map fun η : ℕ => iota (t - η * x) (η * x) + iota ((η₀ - η : ℝ) * x - t) (η * x)).sum +
      zs.length := by
  induction zs with
  | nil => simp
  | cons η zs ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append,
      sum_val_zs η₀ η (hz η (by simp)) x ht0 ht1,
      ih fun η' h => hz η' (List.mem_cons_of_mem _ h)]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    ring

theorem sum_val_ps_list (η₀ : ℕ) (ps : List ℕ) (hp : ∀ η ∈ ps, 2 * η ≤ η₀) (x : ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ((ps.flatMap fun η => ([⟨η₀ - 2 * η, 1, 0, 0, 0, 0⟩, ⟨η, 1, 0, 1, 0, 0⟩,
      ⟨η₀ - η, 0, 1, 0, 0, 1⟩] : List Atom)).map (·.val x t)).sum =
    (ps.map fun η : ℕ => iota (t - η * x) ((η₀ - η : ℝ) * x - t)).sum := by
  induction ps with
  | nil => simp
  | cons η ps ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append,
      sum_val_ps η₀ η (hp η (by simp)) x ht0 ht1,
      ih fun η' h => hp η' (List.mem_cons_of_mem _ h)]
    simp

/-- For `t ∈ [0, 1)`, `φ₀(x, t) + |zs|` is the sum of the values of the terms. -/
theorem phi0_add_eq_terms {η₀ : ℕ} {zs ps : List ℕ} (hz : ∀ η ∈ zs, η ≤ η₀)
    (hp : ∀ η ∈ ps, 2 * η ≤ η₀) (x : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    phi0 η₀ zs ps x t + zs.length = ((terms η₀ zs ps).map (·.val x t)).sum := by
  unfold phi0 terms
  rw [List.map_append, List.sum_append, sum_val_zs_list η₀ zs hz x ht0 ht1,
    sum_val_ps_list η₀ ps hp x ht0 ht1]
  ring

/-! ### Collecting equal multipliers -/

theorem natCast_sub_sub (p n : ℕ) : ((p - n : ℕ) : ℤ) - ((n - p : ℕ) : ℤ) = (p : ℤ) - n := by
  omega

theorem wsum_cons (c : Atom) (T : List Atom) (a : ℕ) (f : Atom → ℕ) :
    wsum (c :: T) a f = (if c.a = a then f c else 0) + wsum T a f := by
  simp [wsum]

theorem val_merge (T : List Atom) (a : ℕ) (x t : ℝ) :
    (merge T a).val x t = (T.map fun c => if c.a = a then c.val x t else 0).sum := by
  have key : ∀ T : List Atom,
      ((wsum T a Atom.cp : ℤ) - wsum T a Atom.cn) * ⌊(a : ℝ) * x⌋ +
        (indVal ⟨a, 0, 0, wsum T a Atom.l, wsum T a Atom.e, wsum T a Atom.r⟩
          (Int.fract ((a : ℝ) * x)) t : ℤ) =
      (T.map fun c => if c.a = a then c.val x t else 0).sum := by
    intro T
    induction T with
    | nil => simp [wsum, indVal]
    | cons c T ih =>
      rw [List.map_cons, List.sum_cons, ← ih]
      simp only [wsum_cons]
      by_cases hc : c.a = a
      · simp only [hc, ite_true, Atom.val, indVal]
        push_cast
        ring
      · simp only [hc, ite_false, zero_add]
  rw [← key T]
  simp only [merge, Atom.val]
  rw [natCast_sub_sub]
  rfl

theorem sum_ite_nodup (D : List ℕ) (hD : D.Nodup) (a : ℕ) (ha : a ∈ D) (z : ℤ) :
    (D.map fun b => if a = b then z else 0).sum = z := by
  rw [← List.sum_toFinset _ hD, Finset.sum_ite_eq]
  simp [ha]

theorem sum_swap (D : List ℕ) (hD : D.Nodup) (g : Atom → ℤ) :
    ∀ T : List Atom, (∀ c ∈ T, c.a ∈ D) →
      (D.map fun a => (T.map fun c => if c.a = a then g c else 0).sum).sum = (T.map g).sum := by
  intro T
  induction T with
  | nil => intro _; simp
  | cons c T ih =>
    intro hT
    simp only [List.map_cons, List.sum_cons]
    rw [List.sum_map_add, ih fun c' h => hT c' (List.mem_cons_of_mem _ h)]
    congr 1
    exact sum_ite_nodup D hD c.a (hT c (by simp)) (g c)

theorem sum_val_atoms (η₀ : ℕ) (zs ps : List ℕ) (x t : ℝ) :
    ((atoms η₀ zs ps).map (·.val x t)).sum = ((terms η₀ zs ps).map (·.val x t)).sum := by
  unfold atoms
  simp only [List.map_map]
  rw [← sum_swap _ (List.nodup_dedup _) (·.val x t) (terms η₀ zs ps)
    (fun c h => List.mem_dedup.2 (List.mem_map_of_mem h))]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp, val_merge]

theorem sum_filter_add (l : List Atom) (p : Atom → Bool) (f : Atom → ℤ) :
    ((l.filter p).map f).sum + ((l.filter fun c => !p c).map f).sum = (l.map f).sum := by
  rw [← List.sum_append, ← List.map_append]
  exact ((List.filter_append_perm p l).map f).sum_eq

/-- For `t ∈ [0, 1)`: `φ₀(x, t) + |zs| = ∑_{atomsF} + ∑_{atomsS}`. -/
theorem phi0_add_eq_atoms {η₀ : ℕ} {zs ps : List ℕ} (hz : ∀ η ∈ zs, η ≤ η₀)
    (hp : ∀ η ∈ ps, 2 * η ≤ η₀) (x : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    phi0 η₀ zs ps x t + zs.length =
      ((atomsF η₀ zs ps).map (·.val x t)).sum + ((atomsS η₀ zs ps).map (·.val x t)).sum := by
  rw [phi0_add_eq_terms hz hp x ht0 ht1, ← sum_val_atoms, atomsF, atomsS,
    ← sum_filter_add (atoms η₀ zs ps) (fun c => decide (c.l + c.e + c.r = 0))]
  congr 3

/-! ## Soundness: one interval -/

theorem floor_eq_of_bounds {a k nα dα nβ dβ : ℕ} (hdα : 0 < dα) (hdβ : 0 < dβ)
    (h1 : k * dα ≤ a * nα) (h2 : a * nβ ≤ k * dβ + dβ) {x : ℝ} (hx1 : (nα : ℝ) < x * dα)
    (hx2 : x * dβ < nβ) : ⌊(a : ℝ) * x⌋ = k := by
  rw [Int.floor_eq_iff]
  have h1' : (k : ℝ) * dα ≤ a * nα := by exact_mod_cast h1
  have h2' : (a : ℝ) * nβ ≤ k * dβ + dβ := by exact_mod_cast h2
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hdα' : (0 : ℝ) < dα := by exact_mod_cast hdα
  have hdβ' : (0 : ℝ) < dβ := by exact_mod_cast hdβ
  push_cast
  constructor
  · have : (a : ℝ) * nα ≤ a * (x * dα) := mul_le_mul_of_nonneg_left hx1.le ha
    nlinarith
  · rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      simp only [Nat.cast_zero, zero_mul]
      positivity
    · have ha' : (0 : ℝ) < a := by exact_mod_cast h
      have : (a : ℝ) * (x * dβ) < a * nβ := mul_lt_mul_of_pos_left hx2 ha'
      nlinarith

theorem lt_of_chain_lt {a b ka kb ra rb nα dα : ℕ} (hdα : 0 < dα) (hra : ra + ka * dα = a * nα)
    (hrb : rb + kb * dα = b * nα) (hab : a < b) (hr : ra ≤ rb) {x : ℝ}
    (hx1 : (nα : ℝ) < x * dα) : (a : ℝ) * x - ka < b * x - kb := by
  have hra' : (ra : ℝ) + ka * dα = a * nα := by exact_mod_cast hra
  have hrb' : (rb : ℝ) + kb * dα = b * nα := by exact_mod_cast hrb
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hr' : (ra : ℝ) ≤ rb := by exact_mod_cast hr
  have hdα' : (0 : ℝ) < dα := by exact_mod_cast hdα
  have h1 : ((b : ℝ) - a) * nα < ((b : ℝ) - a) * (x * dα) :=
    mul_lt_mul_of_pos_left hx1 (by linarith)
  nlinarith

theorem lt_of_chain_gt {a b ka kb nβ dβ : ℕ} (hdβ : 0 < dβ) (hab : b < a)
    (h : a * nβ + kb * dβ ≤ b * nβ + ka * dβ) {x : ℝ} (hx2 : x * dβ < nβ) :
    (a : ℝ) * x - ka < b * x - kb := by
  have h' : (a : ℝ) * nβ + kb * dβ ≤ b * nβ + ka * dβ := by exact_mod_cast h
  have hab' : (b : ℝ) < a := by exact_mod_cast hab
  have hdβ' : (0 : ℝ) < dβ := by exact_mod_cast hdβ
  have h1 : ((a : ℝ) - b) * (x * dβ) < ((a : ℝ) - b) * nβ :=
    mul_lt_mul_of_pos_left hx2 (by linarith)
  nlinarith

/-- The arithmetic relations satisfied by `mkEntry nα dα nβ dβ c`. -/
def Valid (nα dα nβ dβ : ℕ) (e : Entry) : Prop :=
  e.r + e.k * dα = e.atom.a * nα ∧ e.w = e.atom.a * nβ ∧ e.kd = e.k * dβ

theorem valid_mkEntry (nα dα nβ dβ : ℕ) (c : Atom) :
    Valid nα dα nβ dβ (mkEntry nα dα nβ dβ c) := by
  have h : (c.a * nα) % dα + (c.a * nα) / dα * dα = c.a * nα := by
    rw [Nat.mul_comm ((c.a * nα) / dα), Nat.mod_add_div]
  exact ⟨h, rfl, rfl⟩

/-- The point `{a x}` of an entry (valid on the interval). -/
def pt (x : ℝ) (e : Entry) : ℝ := e.atom.a * x - e.k

theorem entsOK_spec {dβ : ℕ} : ∀ {es : List Entry}, entsOK dβ es = true → ∀ e ∈ es, e.w ≤ e.kd + dβ
  | [], _ => by simp
  | e :: l, h => by
    simp only [entsOK, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at h
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact h.1
    · exact entsOK_spec h.2 f hf

theorem floorsOK_spec {nα dα nβ dβ : ℕ} : ∀ {l : List Atom}, floorsOK nα dα nβ dβ l = true →
    ∀ c ∈ l, c.a * nβ ≤ c.a * nα / dα * dβ + dβ
  | [], _ => by simp
  | c :: l, h => by
    simp only [floorsOK, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at h
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact h.1
    · exact floorsOK_spec h.2 f hf

theorem pairwise_of_chainOK {nα dα nβ dβ : ℕ} (hdα : 0 < dα) (hdβ : 0 < dβ) {x : ℝ}
    (hx1 : (nα : ℝ) < x * dα) (hx2 : x * dβ < nβ) :
    ∀ {es : List Entry}, (∀ e ∈ es, Valid nα dα nβ dβ e) → chainOK es = true →
      es.Pairwise fun e f => pt x e < pt x f
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => List.pairwise_singleton _ _
  | e :: f :: rest, hv, h => by
    simp only [chainOK, Bool.and_eq_true] at h
    have ih := pairwise_of_chainOK hdα hdβ hx1 hx2 (fun g hg => hv g (List.mem_cons_of_mem _ hg))
      h.2
    have hef : pt x e < pt x f := by
      obtain ⟨he1, he2, he3⟩ := hv e (by simp)
      obtain ⟨hf1, hf2, hf3⟩ := hv f (by simp)
      have h1 := h.1
      unfold pt
      rcases lt_trichotomy e.atom.a f.atom.a with hab | hab | hab
      · have hb : Nat.blt e.atom.a f.atom.a = true := by rw [Nat.blt_eq]; exact hab
        rw [hb, Bool.cond_true, Nat.ble_eq] at h1
        exact lt_of_chain_lt hdα he1 hf1 hab h1 hx1
      · have hb1 : Nat.blt e.atom.a f.atom.a = false := by
          rw [← Bool.not_eq_true, Nat.blt_eq]; omega
        have hb2 : Nat.blt f.atom.a e.atom.a = false := by
          rw [← Bool.not_eq_true, Nat.blt_eq]; omega
        rw [hb1, Bool.cond_false, hb2, Bool.cond_false] at h1
        exact absurd h1 Bool.false_ne_true
      · have hb1 : Nat.blt e.atom.a f.atom.a = false := by
          rw [← Bool.not_eq_true, Nat.blt_eq]; omega
        have hb2 : Nat.blt f.atom.a e.atom.a = true := by rw [Nat.blt_eq]; exact hab
        rw [hb1, Bool.cond_false, hb2, Bool.cond_true, Nat.ble_eq, Nat.add_eq, Nat.add_eq, he2,
          he3, hf2, hf3] at h1
        exact lt_of_chain_gt hdβ hab h1 hx2
    refine List.Pairwise.cons (fun g hg => ?_) ih
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hef
    · exact hef.trans (List.rel_of_pairwise_cons ih hg)

theorem nmin_eq (a b : ℕ) : nmin a b = min a b := by
  unfold nmin
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := by rw [← Nat.ble_eq, h]; simp
    simp only [Bool.cond_false]; omega
  · have : a ≤ b := by rw [← Nat.ble_eq, h]
    simp only [Bool.cond_true]; omega

theorem sweep_fst : ∀ es : List Entry, (sweep es).1 = (es.map fun e => e.atom.l).sum
  | [] => rfl
  | e :: rest => by
    rw [sweep]
    rcases h : sweep rest with ⟨s, m⟩
    have := sweep_fst rest
    rw [h] at this
    simp only [Nat.add_eq, List.map_cons, List.sum_cons]
    rw [← this]

theorem sum_indVal_of_lt (P : Entry → ℝ) (t : ℝ) :
    ∀ es : List Entry, (∀ e ∈ es, t < P e) →
      (es.map fun e => indVal e.atom (P e) t).sum = (es.map fun e => e.atom.l).sum
  | [], _ => rfl
  | e :: rest, h => by
    have he := h e (by simp)
    simp only [List.map_cons, List.sum_cons,
      sum_indVal_of_lt P t rest fun f hf => h f (List.mem_cons_of_mem _ hf)]
    simp [indVal, he, he.ne, not_lt.2 he.le]

/-- The sweep computes a lower bound for the step function `t ↦ ∑ indVal`. -/
theorem sweep_le (P : Entry → ℝ) (t : ℝ) :
    ∀ es : List Entry, es.Pairwise (fun e f => P e < P f) →
      (sweep es).2 ≤ (es.map fun e => indVal e.atom (P e) t).sum
  | [], _ => by simp [sweep]
  | e :: rest, hp => by
    rw [List.pairwise_cons] at hp
    have ih := sweep_le P t rest hp.2
    have hs := sweep_fst rest
    rw [sweep]
    rcases h : sweep rest with ⟨s, m⟩
    rw [h] at ih hs
    simp only [nmin_eq, Nat.add_eq, List.map_cons, List.sum_cons]
    rcases lt_trichotomy t (P e) with ht | ht | ht
    · have hr : ∀ f ∈ rest, t < P f := fun f hf => ht.trans (hp.1 f hf)
      have h1 : (rest.map fun f => indVal f.atom (P f) t).sum = s := by
        rw [sum_indVal_of_lt P t rest hr, ← hs]
      have h2 : indVal e.atom (P e) t = e.atom.l := by
        simp [indVal, ht, ht.ne, not_lt.2 ht.le]
      rw [h1, h2]
      omega
    · have hr : ∀ f ∈ rest, t < P f := fun f hf => ht ▸ hp.1 f hf
      have h1 : (rest.map fun f => indVal f.atom (P f) t).sum = s := by
        rw [sum_indVal_of_lt P t rest hr, ← hs]
      have h2 : indVal e.atom (P e) t = e.atom.e := by
        simp [indVal, ht]
      rw [h1, h2]
      omega
    · have h2 : indVal e.atom (P e) t = e.atom.r := by
        simp [indVal, ht, ht.ne', not_lt.2 ht.le]
      rw [h2]
      omega

theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem nat_mod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem cpSum_eq : ∀ es : List Entry, cpSum es = (es.map fun e => e.atom.cp * e.k).sum
  | [] => rfl
  | e :: l => by simp [cpSum, cpSum_eq l, Nat.add_eq, Nat.mul_eq]

theorem cnSum_eq : ∀ es : List Entry, cnSum es = (es.map fun e => e.atom.cn * e.k).sum
  | [] => rfl
  | e :: l => by simp [cnSum, cnSum_eq l, Nat.add_eq, Nat.mul_eq]

theorem fSum_eq (nα dα : ℕ) : ∀ l : List Atom,
    (fpSum nα dα l : ℤ) - fnSum nα dα l =
      (l.map fun c => ((c.cp : ℤ) - c.cn) * ((c.a * nα / dα : ℕ) : ℤ)).sum
  | [] => by simp [fpSum, fnSum]
  | c :: l => by
    have := fSum_eq nα dα l
    simp only [fpSum, fnSum, Nat.add_eq, Nat.mul_eq, nat_div_eq, List.map_cons, List.sum_cons,
      Nat.cast_add, Nat.cast_mul] at this ⊢
    rw [← this]
    ring

theorem insE_perm (e : Entry) : ∀ l : List Entry, (insE e l).Perm (e :: l)
  | [] => List.Perm.refl _
  | f :: l => by
    unfold insE
    cases Nat.ble e.key f.key
    · exact ((insE_perm e l).cons f).trans (List.Perm.swap e f l)
    · exact List.Perm.refl _

theorem sortE_perm : ∀ l : List Entry, (sortE l).Perm l
  | [] => List.Perm.refl _
  | e :: l => (insE_perm e (sortE l)).trans ((sortE_perm l).cons e)

theorem ratCast_eq {q : ℚ} {n : ℕ} (h : q.num = Int.ofNat n) : (q : ℝ) = n / q.den := by
  rw [Rat.cast_def, h]
  simp

theorem sum_val_entries (x t : ℝ) : ∀ es : List Entry,
    (∀ e ∈ es, ⌊(e.atom.a : ℝ) * x⌋ = e.k) →
    (es.map fun e => e.atom.val x t).sum =
      ((cpSum es : ℤ) - cnSum es) + ((es.map fun e => indVal e.atom (pt x e) t).sum : ℕ)
  | [], _ => by simp [cpSum, cnSum]
  | e :: l, hfl => by
    have hf := hfl e (by simp)
    rw [List.map_cons, List.sum_cons,
      sum_val_entries x t l fun f hf => hfl f (List.mem_cons_of_mem _ hf)]
    simp only [cpSum, cnSum, Nat.add_eq, Nat.mul_eq, List.map_cons, List.sum_cons,
      Nat.cast_add, Nat.cast_mul, Atom.val, pt]
    rw [Int.fract, hf, Int.cast_natCast]
    ring

/-- Soundness of one interval step. -/
theorem stepI_sound {atF ord ord' : List Atom} {off v : ℕ} {α β : ℚ}
    (h : stepI atF off ord α β v = some ord') :
    ord'.Perm ord ∧ α < β ∧ ∀ x : ℝ, (α : ℝ) < x → x < β → ∀ t : ℝ,
      (v : ℤ) + off ≤ (atF.map (·.val x t)).sum + (ord.map (·.val x t)).sum := by
  unfold stepI at h
  split at h
  next nα nβ hα hβ =>
    simp only [Bool.cond_eq_ite] at h
    split_ifs at h with hB
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at hB
    obtain ⟨⟨⟨⟨hlt, hF⟩, hE⟩, hC⟩, hV⟩ := hB
    set dα := α.den with hdα_def
    set dβ := β.den with hdβ_def
    set es := sortE (ord.map (mkEntry nα dα nβ dβ)) with hes
    have hdα : 0 < dα := α.den_pos
    have hdβ : 0 < dβ := β.den_pos
    have hperm : es.Perm (ord.map (mkEntry nα dα nβ dβ)) := sortE_perm _
    refine ⟨?_, ?_, ?_⟩
    · have := hperm.map Entry.atom
      rwa [List.map_map, show Entry.atom ∘ mkEntry nα dα nβ dβ = id from rfl, List.map_id] at this
    · rw [← Rat.num_div_den α, ← Rat.num_div_den β, hα, hβ,
        div_lt_div_iff₀ (by exact_mod_cast hdα) (by exact_mod_cast hdβ)]
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
      exact_mod_cast hlt
    intro x hx1 hx2 t
    rw [ratCast_eq hα, div_lt_iff₀ (by exact_mod_cast hdα)] at hx1
    rw [ratCast_eq hβ, lt_div_iff₀ (by exact_mod_cast hdβ)] at hx2
    -- entries
    have hvalid : ∀ e ∈ es, Valid nα dα nβ dβ e := by
      intro e he
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 (hperm.mem_iff.1 he)
      exact valid_mkEntry _ _ _ _ c
    have hfl : ∀ e ∈ es, ⌊(e.atom.a : ℝ) * x⌋ = e.k := by
      intro e he
      obtain ⟨h1, h2, h3⟩ := hvalid e he
      have h4 := entsOK_spec hE e he
      exact floor_eq_of_bounds hdα hdβ (by omega) (by rw [← h2, ← h3]; exact h4) hx1 hx2
    have hpw := pairwise_of_chainOK hdα hdβ hx1 hx2 hvalid hC
    have hsw := sweep_le (pt x) t es hpw
    -- the sum over `ord` is the sum over `es`
    have hord : (ord.map (·.val x t)).sum = (es.map fun e => e.atom.val x t).sum := by
      have := (hperm.map fun e => e.atom.val x t).sum_eq
      rw [this, List.map_map]
      rfl
    have hes_val := sum_val_entries x t es hfl
    -- the floor-only atoms
    have hF' := floorsOK_spec hF
    have hatF : ((fpSum nα dα atF : ℤ) - fnSum nα dα atF) ≤ (atF.map (·.val x t)).sum := by
      rw [fSum_eq]
      refine List.sum_le_sum fun c hc => ?_
      have hk : ⌊(c.a : ℝ) * x⌋ = (c.a * nα / dα : ℕ) :=
        floor_eq_of_bounds hdα hdβ (Nat.div_mul_le_self _ _) (hF' c hc) hx1 hx2
      simp only [Atom.val, hk]
      have : (0 : ℤ) ≤ (indVal c (Int.fract ((c.a : ℝ) * x)) t : ℤ) := Nat.cast_nonneg _
      linarith
    rw [hord, hes_val]
    have hV' : ((v + off + fnSum nα dα atF + cnSum es : ℕ) : ℤ) ≤
        ((fpSum nα dα atF + cpSum es + (sweep es).2 : ℕ) : ℤ) := by exact_mod_cast hV
    have hsw' : (((sweep es).2 : ℕ) : ℤ) ≤
        (((es.map fun e => indVal e.atom (pt x e) t).sum : ℕ) : ℤ) := by exact_mod_cast hsw
    push_cast at hV'
    linarith
  next => simp at h

/-! ## Soundness: all intervals -/

theorem loopGen_sound (atF S : List Atom) (off B : ℕ) :
    ∀ (X : List ℚ) (vals : List ℕ) (c : ℕ) (ord : List Atom), ord.Perm S →
      loopGen atF S off B false c ord X vals = true →
      ∀ (i : ℕ) (hi : i + 1 < X.length) (x : ℝ), (X[i] : ℝ) < x → x < X[i + 1] → ∀ t : ℝ,
        (vals.getD i 0 : ℤ) + off ≤ (atF.map (·.val x t)).sum + (S.map (·.val x t)).sum := by
  intro X
  induction X with
  | nil => intro _ _ _ _ _ i hi; simp at hi
  | cons α X ih =>
    intro vals c ord hperm h i hi x hx1 hx2 t
    match X, vals, h, hi, hx1, hx2, ih with
    | [], _, _, hi, _, _, _ => simp at hi
    | β :: rest, [], h, _, _, _, _ => simp [loopGen] at h
    | β :: rest, v :: vs, h, hi, hx1, hx2, ih =>
      rw [loopGen] at h
      split at h
      next ord' hs =>
        obtain ⟨hperm', -, hsound⟩ := stepI_sound hs
        cases i with
        | zero =>
          have := hsound x hx1 hx2 t
          rw [(hperm.map (·.val x t)).sum_eq] at this
          simpa using this
        | succ i =>
          have hrec : ∃ c' ord'', ord''.Perm S ∧
              loopGen atF S off B false c' ord'' (β :: rest) vs = true := by
            cases c with
            | zero => exact ⟨B, S, List.Perm.refl _, by simpa using h⟩
            | succ c => exact ⟨c, ord', hperm'.trans hperm, h⟩
          obtain ⟨c', ord'', hp'', h''⟩ := hrec
          have := ih vs c' ord'' hp'' h'' i (by simpa using hi) x (by simpa using hx1)
            (by simpa using hx2) t
          simpa using this
      next => simp at h

theorem loopGen_length (atF S : List Atom) (off B : ℕ) :
    ∀ (X : List ℚ) (vals : List ℕ) (c : ℕ) (ord : List Atom),
      loopGen atF S off B false c ord X vals = true →
      X.length = vals.length + 1 ∧ X.Pairwise (· < ·) := by
  intro X
  induction X with
  | nil => intro vals c ord h; simp [loopGen] at h
  | cons α X ih =>
    intro vals c ord h
    match X, vals, h, ih with
    | [], [], _, _ => simp
    | [], _ :: _, h, _ => simp [loopGen] at h
    | β :: rest, [], h, _ => simp [loopGen] at h
    | β :: rest, v :: vs, h, ih =>
      rw [loopGen] at h
      split at h
      next ord' hs =>
        obtain ⟨-, hlt, -⟩ := stepI_sound hs
        have hrec : ∃ c' ord'', loopGen atF S off B false c' ord'' (β :: rest) vs = true := by
          cases c with
          | zero => exact ⟨B, S, by simpa using h⟩
          | succ c => exact ⟨c, ord', h⟩
        obtain ⟨c', ord'', h''⟩ := hrec
        obtain ⟨hl, hp⟩ := ih vs c' ord'' h''
        refine ⟨by simp [hl], List.Pairwise.cons (fun y hy => ?_) hp⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hlt
        · exact hlt.trans (List.rel_of_pairwise_cons hp hy)
      next => simp at h

theorem loopGen_split (atF S : List Atom) (off B : ℕ) :
    ∀ (X : List ℚ) (vals : List ℕ) (c : ℕ) (ord : List Atom),
      loopGen atF S off B true c ord X vals = true →
      (c < vals.length →
        loopGen atF S off B false B S (X.drop (c + 1)) (vals.drop (c + 1)) = true) →
      loopGen atF S off B false c ord X vals = true := by
  intro X
  induction X with
  | nil => intro vals c ord h; simp [loopGen] at h
  | cons α X ih =>
    intro vals c ord h1 h2
    match X, vals, h1, h2, ih with
    | [], [], _, _, _ => simp [loopGen]
    | [], _ :: _, h1, _, _ => simp [loopGen] at h1
    | β :: rest, [], h1, _, _ => simp [loopGen] at h1
    | β :: rest, v :: vs, h1, h2, ih =>
      rw [loopGen] at h1 ⊢
      split at h1
      next ord' hs =>
        cases c with
        | zero =>
          simp only [Bool.cond_false]
          simpa using h2 (by simp)
        | succ c =>
          exact ih vs c ord' h1 fun hc => by simpa using h2 (by simpa using hc)
      next => simp at h1

theorem loopGen_of_chunks (atF S : List Atom) (off B : ℕ) :
    ∀ (N : ℕ) (X : List ℚ) (vals : List ℕ),
      (∀ j ≤ N, loopGen atF S off B true B S (X.drop (j * (B + 1))) (vals.drop (j * (B + 1)))
        = true) →
      vals.length ≤ N * (B + 1) + B → loopGen atF S off B false B S X vals = true := by
  intro N
  induction N with
  | zero =>
    intro X vals h hl
    exact loopGen_split atF S off B X vals B S (by simpa using h 0 le_rfl) fun h' => by omega
  | succ N ih =>
    intro X vals h hl
    refine loopGen_split atF S off B X vals B S (by simpa using h 0 (Nat.zero_le _)) fun _ => ?_
    have hNB : (N + 1) * (B + 1) = N * (B + 1) + (B + 1) := by ring
    refine ih _ _ (fun j hj => ?_) (by rw [List.length_drop]; omega)
    have := h (j + 1) (by omega)
    rwa [List.drop_drop, List.drop_drop, show B + 1 + j * (B + 1) = (j + 1) * (B + 1) by ring]

end PhiCert

open PhiCert

/-! ## Main results -/

theorem checkPhiCert_of_chunks {η₀ : ℕ} {zs ps : List ℕ} {X : List ℚ} {vals : List ℕ}
    (hg : globalOK η₀ zs ps X = true) (N : ℕ) (hl : vals.length ≤ N * (chunkB + 1) + chunkB)
    (h : ∀ j ≤ N, chunkOK η₀ zs ps X vals j = true) : checkPhiCert η₀ zs ps X vals = true := by
  unfold checkPhiCert
  rw [hg, Bool.true_and]
  exact loopGen_of_chunks _ _ _ _ N X vals h hl

theorem globalOK_of_checkPhiCert {η₀ : ℕ} {zs ps : List ℕ} {X : List ℚ} {vals : List ℕ}
    (h : checkPhiCert η₀ zs ps X vals = true) :
    (∀ η ∈ zs, η ≤ η₀) ∧ (∀ η ∈ ps, 2 * η ≤ η₀) ∧ X.head? = some 0 ∧ X.getLast? = some 1 := by
  unfold checkPhiCert globalOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

theorem checkPhiCert_length {η₀ : ℕ} {zs ps : List ℕ} {X : List ℚ} {vals : List ℕ}
    (h : checkPhiCert η₀ zs ps X vals = true) :
    X.length = vals.length + 1 ∧ X.Pairwise (· < ·) := by
  unfold checkPhiCert at h
  simp only [Bool.and_eq_true] at h
  exact loopGen_length _ _ _ _ X vals _ _ h.2

/-- On the `i`-th interval of a checked certificate, `vals[i] ≤ φ₀(x, y)` for all `y`. -/
theorem phi0_ge_of_checkPhiCert {η₀ : ℕ} {zs ps : List ℕ} {X : List ℚ} {vals : List ℕ}
    (h : checkPhiCert η₀ zs ps X vals = true) (i : ℕ) (hi : i + 1 < X.length)
    (x : ℝ) (hx₁ : (X[i] : ℝ) < x) (hx₂ : x < X[i + 1]) (y : ℝ) :
    ((vals.getD i 0 : ℕ) : ℤ) ≤ phi0 η₀ zs ps x y := by
  obtain ⟨hz, hp, -, -⟩ := globalOK_of_checkPhiCert h
  unfold checkPhiCert at h
  simp only [Bool.and_eq_true] at h
  have h1 := loopGen_sound _ _ _ _ X vals _ _ (List.Perm.refl _) h.2 i hi x hx₁ hx₂ (Int.fract y)
  have h2 := phi0_add_eq_atoms hz hp x (Int.fract_nonneg y) (Int.fract_lt_one y)
  rw [← phi0_fract_right]
  linarith

/-- Auxiliary for `phiStep`: the value on the first interval of `X` containing `x`. -/
noncomputable def phiStepAux : List ℚ → List ℕ → ℝ → ℕ
  | α :: β :: rest, v :: vs, x => if (α : ℝ) < x ∧ x < β then v else phiStepAux (β :: rest) vs x
  | _, _, _ => 0

/-- The step function `vals[i]` on `{x} ∈ (X[i], X[i+1])`, `0` elsewhere. -/
noncomputable def phiStep (X : List ℚ) (vals : List ℕ) (x : ℝ) : ℕ :=
  phiStepAux X vals (Int.fract x)

theorem phiStepAux_cases : ∀ (X : List ℚ) (vals : List ℕ) (x : ℝ),
    phiStepAux X vals x = 0 ∨ ∃ (i : ℕ) (hi : i + 1 < X.length), (X[i] : ℝ) < x ∧
      x < X[i + 1] ∧ phiStepAux X vals x = vals.getD i 0
  | α :: β :: rest, v :: vs, x => by
    rw [phiStepAux]
    split_ifs with h
    · exact Or.inr ⟨0, by simp, h.1, h.2, rfl⟩
    · rcases phiStepAux_cases (β :: rest) vs x with h' | ⟨i, hi, h1, h2, h3⟩
      · exact Or.inl h'
      · exact Or.inr ⟨i + 1, by simpa using hi, by simpa using h1, by simpa using h2, by simpa⟩
  | [], _, _ => Or.inl (by simp [phiStepAux])
  | [_], _, _ => Or.inl (by simp [phiStepAux])
  | _ :: _ :: _, [], _ => Or.inl (by simp [phiStepAux])

/-- The step function is a lower bound for `φ₀`. -/
theorem phiStep_le {η₀ : ℕ} {zs ps : List ℕ} {X : List ℚ} {vals : List ℕ}
    (h : checkPhiCert η₀ zs ps X vals = true) (x y : ℝ) :
    (phiStep X vals x : ℤ) ≤ phi0 η₀ zs ps x y := by
  rcases phiStepAux_cases X vals (Int.fract x) with h0 | ⟨i, hi, h1, h2, h3⟩
  · simp only [phiStep, h0, Nat.cast_zero]
    exact phi0_nonneg _ _ _ _ _
  · rw [phiStep, h3, ← phi0_fract_left]
    exact phi0_ge_of_checkPhiCert h i hi _ h1 h2 y

theorem phiStepAux_eq : ∀ (X : List ℚ) (vals : List ℕ), X.Pairwise (· < ·) →
    ∀ (i : ℕ) (hi : i + 1 < X.length) (x : ℝ), (X[i] : ℝ) < x → x < X[i + 1] →
      phiStepAux X vals x = vals.getD i 0
  | α :: β :: rest, v :: vs, hX, i, hi, x, h1, h2 => by
    rw [phiStepAux]
    cases i with
    | zero => simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2; simp [h1, h2]
    | succ i =>
      have hi' : i + 1 < (β :: rest).length := by simpa using hi
      have h1' : ((β :: rest)[i] : ℝ) < x := by simpa using h1
      have hβ : (β : ℝ) ≤ (β :: rest)[i] := by
        cases i with
        | zero => simp
        | succ i =>
          have hir : i < rest.length := by simp at hi'; omega
          have hmem : rest[i] ∈ rest := List.getElem_mem hir
          have := (List.rel_of_pairwise_cons hX.of_cons hmem).le
          simpa using (Rat.cast_le (K := ℝ)).2 this
      have hx : ¬ ((α : ℝ) < x ∧ x < β) := by
        rintro ⟨-, h⟩
        linarith
      simp only [hx, ↓reduceIte]
      simpa using phiStepAux_eq (β :: rest) vs hX.of_cons i hi' x h1' (by simpa using h2)
  | [], _, _, i, hi, _, _, _ => by simp at hi
  | [_], _, _, i, hi, _, _, _ => by simp at hi
  | _ :: _ :: _, [], _, i, _, x, _, _ => by
    cases i <;> simp [phiStepAux]

/-- On the `i`-th interval, the step function takes the value `vals[i]`. -/
theorem phiStep_eq {η₀ : ℕ} {zs ps : List ℕ} {X : List ℚ} {vals : List ℕ}
    (h : checkPhiCert η₀ zs ps X vals = true) (i : ℕ) (hi : i + 1 < X.length) (x : ℝ)
    (hx₁ : (X[i] : ℝ) < Int.fract x) (hx₂ : Int.fract x < X[i + 1]) :
    phiStep X vals x = vals.getD i 0 :=
  phiStepAux_eq X vals (checkPhiCert_length h).2 i hi _ hx₁ hx₂

end OddZeta
