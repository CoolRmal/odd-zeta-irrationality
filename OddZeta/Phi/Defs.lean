import Mathlib

/-!
# The function `φ₀` of the arithmetic lemma

`iota A B = ⌊A + B⌋ - ⌊A⌋ - ⌊B⌋ ∈ {0, 1}` and `phi0 η₀ zs ps x y`, the sum of the indicator
terms of the zero blocks (`zs`) and of the pole blocks (`ps`); `φ(x) = min_y phi0 x y`.
`phi0` is `1`-periodic in `x` and in `y`.
-/

namespace OddZeta

/-- `ι(A, B) = ⌊A + B⌋ - ⌊A⌋ - ⌊B⌋`. -/
noncomputable def iota (A B : ℝ) : ℤ := ⌊A + B⌋ - ⌊A⌋ - ⌊B⌋

/-- The function `φ₀(x, y)` (a sum of `2 |zs| + |ps|` terms `ι`). -/
noncomputable def phi0 (η₀ : ℕ) (zs ps : List ℕ) (x y : ℝ) : ℤ :=
  (zs.map fun η : ℕ => iota (y - η * x) (η * x) + iota ((η₀ - η : ℝ) * x - y) (η * x)).sum +
  (ps.map fun η : ℕ => iota (y - η * x) ((η₀ - η : ℝ) * x - y)).sum

theorem iota_nonneg (A B : ℝ) : 0 ≤ iota A B := by
  have := Int.le_floor_add A B
  unfold iota; omega

theorem iota_le_one (A B : ℝ) : iota A B ≤ 1 := by
  have := Int.le_floor_add_floor A B
  unfold iota; omega

/-- `ι` is invariant under integer shifts of its arguments. -/
theorem iota_congr_intCast {A B A' B' : ℝ} (m n : ℤ) (hA : A' = A + m) (hB : B' = B + n) :
    iota A' B' = iota A B := by
  subst hA hB
  unfold iota
  rw [show A + m + (B + n) = A + B + ((m + n : ℤ) : ℝ) by push_cast; ring,
    Int.floor_add_intCast, Int.floor_add_intCast, Int.floor_add_intCast]
  ring

theorem phi0_add_intCast_left (η₀ : ℕ) (zs ps : List ℕ) (x y : ℝ) (m : ℤ) :
    phi0 η₀ zs ps (x + m) y = phi0 η₀ zs ps x y := by
  unfold phi0
  congr 2
  · refine List.map_congr_left fun η _ => ?_
    congr 1
    · exact iota_congr_intCast (-(η * m)) (η * m) (by push_cast; ring) (by push_cast; ring)
    · exact iota_congr_intCast ((η₀ - η) * m) (η * m) (by push_cast; ring) (by push_cast; ring)
  · refine List.map_congr_left fun η _ => ?_
    exact iota_congr_intCast (-(η * m)) ((η₀ - η) * m) (by push_cast; ring) (by push_cast; ring)

theorem phi0_add_intCast_right (η₀ : ℕ) (zs ps : List ℕ) (x y : ℝ) (m : ℤ) :
    phi0 η₀ zs ps x (y + m) = phi0 η₀ zs ps x y := by
  unfold phi0
  congr 2
  · refine List.map_congr_left fun η _ => ?_
    congr 1
    · exact iota_congr_intCast m 0 (by ring) (by push_cast; ring)
    · exact iota_congr_intCast (-m) 0 (by push_cast; ring) (by push_cast; ring)
  · refine List.map_congr_left fun η _ => ?_
    exact iota_congr_intCast m (-m) (by ring) (by push_cast; ring)

theorem phi0_nonneg (η₀ : ℕ) (zs ps : List ℕ) (x y : ℝ) : 0 ≤ phi0 η₀ zs ps x y := by
  unfold phi0
  refine add_nonneg (List.sum_nonneg ?_) (List.sum_nonneg ?_) <;>
  · simp only [List.mem_map]
    rintro _ ⟨η, _, rfl⟩
    first
    | exact add_nonneg (iota_nonneg _ _) (iota_nonneg _ _)
    | exact iota_nonneg _ _

theorem phi0_fract_left (η₀ : ℕ) (zs ps : List ℕ) (x y : ℝ) :
    phi0 η₀ zs ps (Int.fract x) y = phi0 η₀ zs ps x y := by
  rw [Int.fract, sub_eq_add_neg, ← Int.cast_neg, phi0_add_intCast_left]

theorem phi0_fract_right (η₀ : ℕ) (zs ps : List ℕ) (x y : ℝ) :
    phi0 η₀ zs ps x (Int.fract y) = phi0 η₀ zs ps x y := by
  rw [Int.fract, sub_eq_add_neg, ← Int.cast_neg, phi0_add_intCast_right]

end OddZeta
