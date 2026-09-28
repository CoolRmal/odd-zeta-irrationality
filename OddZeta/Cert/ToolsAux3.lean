import OddZeta.Cert.ToolsAux1

/-!
# Analytic tools for the saddle-point certificates, part 3: bounds for `Im f'`

* explicit formulas for `arg ⟨a, b⟩` in terms of `Real.arctan`;
* monotonicity of `arg ⟨a, b⟩` in `a` and `b`;
* `im_f'_le_box`, `le_im_f'_box`: upper and lower bounds for `Im f'` on a box
  `[x₁, x₂] × [y₁, y₂]` in the closed lower half-plane, in terms of `arg` at the corners;
* `im_f'_add_le_tail`: the bound `Im f'(x+iy) + (r-2)π ≤ -2π + r(η₀+2|x|)/Y` for `y ≤ -Y < 0`.
-/

namespace OddZeta.Cert

open Complex

/-! ### `arg` via `arctan` -/

theorem arg_mk_of_re_pos {a : ℝ} (ha : 0 < a) (b : ℝ) :
    arg ⟨a, b⟩ = Real.arctan (b / a) := by
  have h1 := abs_lt.1 ((abs_arg_lt_pi_div_two_iff (z := ⟨a, b⟩)).2 (Or.inl ha))
  have h2 : Real.tan (arg ⟨a, b⟩) = b / a := tan_arg _
  rw [← h2, Real.arctan_tan h1.1 h1.2]

theorem arg_mk_of_im_pos (a : ℝ) {b : ℝ} (hb : 0 < b) :
    arg ⟨a, b⟩ = Real.pi / 2 - Real.arctan (a / b) := by
  have hpos : 0 < arg ⟨a, b⟩ := by
    rcases ((arg_nonneg_iff (z := ⟨a, b⟩)).2 hb.le).lt_or_eq with h | h
    · exact h
    · exact absurd (arg_eq_zero_iff.1 h.symm).2 hb.ne'
  have hlt : arg ⟨a, b⟩ < Real.pi := arg_lt_pi_iff.2 (Or.inr hb.ne')
  have h2 : Real.tan (Real.pi / 2 - arg ⟨a, b⟩) = a / b := by
    rw [Real.tan_pi_div_two_sub, show Real.tan (arg ⟨a, b⟩) = b / a from tan_arg _, inv_div]
  have := Real.arctan_tan (x := Real.pi / 2 - arg ⟨a, b⟩) (by linarith) (by linarith)
  rw [h2] at this
  linarith

theorem arg_mk_of_im_neg (a : ℝ) {b : ℝ} (hb : b < 0) :
    arg ⟨a, b⟩ = -(Real.pi / 2) - Real.arctan (a / b) := by
  have h := arg_mk_of_im_pos a (b := -b) (by linarith)
  have hc : (⟨a, -b⟩ : ℂ) = (starRingEnd ℂ) ⟨a, b⟩ := by apply Complex.ext <;> simp
  rw [hc, arg_conj] at h
  split_ifs at h with h'
  · exact absurd (arg_eq_pi_iff.1 h').2 hb.ne
  · rw [div_neg, Real.arctan_neg] at h
    linarith

theorem arg_eq_mk (z : ℂ) : arg z = arg ⟨z.re, z.im⟩ := rfl

/-! ### Monotonicity of `arg ⟨a, b⟩` -/

/-- For `a > 0`, `arg ⟨a, b⟩` is increasing in `b`. -/
theorem arg_mk_mono_im {a b b' : ℝ} (ha : 0 < a) (h : b ≤ b') : arg ⟨a, b⟩ ≤ arg ⟨a, b'⟩ := by
  rw [arg_mk_of_re_pos ha, arg_mk_of_re_pos ha]
  exact Real.arctan_strictMono.monotone (div_le_div_of_nonneg_right h ha.le)

/-- For `b ≤ 0`, `arg ⟨a, b⟩` is increasing in `a > 0`. -/
theorem arg_mk_mono_re {a a' b : ℝ} (ha : 0 < a) (h : a ≤ a') (hb : b ≤ 0) :
    arg ⟨a, b⟩ ≤ arg ⟨a', b⟩ := by
  rw [arg_mk_of_re_pos ha, arg_mk_of_re_pos (ha.trans_le h)]
  apply Real.arctan_strictMono.monotone
  rw [div_le_div_iff₀ ha (ha.trans_le h)]
  nlinarith

/-- For `b ≥ 0`, `arg ⟨a, b⟩` is decreasing in `a > 0`. -/
theorem arg_mk_anti_re {a a' b : ℝ} (ha : 0 < a) (h : a ≤ a') (hb : 0 ≤ b) :
    arg ⟨a', b⟩ ≤ arg ⟨a, b⟩ := by
  rw [arg_mk_of_re_pos ha, arg_mk_of_re_pos (ha.trans_le h)]
  apply Real.arctan_strictMono.monotone
  rw [div_le_div_iff₀ (ha.trans_le h) ha]
  nlinarith

/-- For `b < 0`, `arg ⟨a, b⟩` is increasing in `a ∈ ℝ`. -/
theorem arg_mk_mono_re_of_im_neg {a a' b : ℝ} (h : a ≤ a') (hb : b < 0) :
    arg ⟨a, b⟩ ≤ arg ⟨a', b⟩ := by
  rw [arg_mk_of_im_neg a hb, arg_mk_of_im_neg a' hb]
  have := Real.arctan_strictMono.monotone (div_le_div_of_nonpos_of_le hb.le h)
  linarith

/-- For `b > 0`, `arg ⟨a, b⟩` is decreasing in `a ∈ ℝ`. -/
theorem arg_mk_anti_re_of_im_pos {a a' b : ℝ} (h : a ≤ a') (hb : 0 < b) :
    arg ⟨a', b⟩ ≤ arg ⟨a, b⟩ := by
  rw [arg_mk_of_im_pos a hb, arg_mk_of_im_pos a' hb]
  have := Real.arctan_strictMono.monotone (div_le_div_of_nonneg_right h hb.le)
  linarith

/-- For fixed `a`, `t ↦ arg ⟨a, t⟩` on `[t₁, t₂] ⊆ (0, ∞)` lies between its endpoint values. -/
theorem arg_mk_im_pos_between {a t t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (h₁ : t₁ ≤ t) (h₂ : t ≤ t₂) :
    min (arg ⟨a, t₁⟩) (arg ⟨a, t₂⟩) ≤ arg ⟨a, t⟩ ∧
      arg ⟨a, t⟩ ≤ max (arg ⟨a, t₁⟩) (arg ⟨a, t₂⟩) := by
  have ht : 0 < t := ht₁.trans_le h₁
  have ht₂ : 0 < t₂ := ht.trans_le h₂
  rw [arg_mk_of_im_pos a ht, arg_mk_of_im_pos a ht₁, arg_mk_of_im_pos a ht₂]
  rcases le_total 0 a with ha | ha
  · -- `a / t` is decreasing in `t`
    have e1 : a / t ≤ a / t₁ := div_le_div_of_nonneg_left ha ht₁ h₁
    have e2 : a / t₂ ≤ a / t := div_le_div_of_nonneg_left ha ht h₂
    have f1 := Real.arctan_strictMono.monotone e1
    have f2 := Real.arctan_strictMono.monotone e2
    constructor
    · exact (min_le_left _ _).trans (by linarith)
    · exact le_trans (by linarith) (le_max_right _ _)
  · -- `a / t` is increasing in `t`
    have e1 : a / t₁ ≤ a / t := by
      rw [div_le_div_iff₀ ht₁ ht]; nlinarith
    have e2 : a / t ≤ a / t₂ := by
      rw [div_le_div_iff₀ ht ht₂]; nlinarith
    have f1 := Real.arctan_strictMono.monotone e1
    have f2 := Real.arctan_strictMono.monotone e2
    constructor
    · exact (min_le_right _ _).trans (by linarith)
    · exact le_trans (by linarith) (le_max_left _ _)

/-! ### Corner bounds for `arg` on boxes -/

/-- Upper corner bound in the closed lower half-plane with positive real part. -/
theorem arg_le_corner {z : ℂ} {a₂ b₂ : ℝ} (hre : 0 < z.re) (ha : z.re ≤ a₂) (hb : z.im ≤ b₂)
    (hb₂ : b₂ ≤ 0) : arg z ≤ arg ⟨a₂, b₂⟩ := by
  rw [arg_eq_mk z]
  exact (arg_mk_mono_re hre ha (hb.trans hb₂)).trans (arg_mk_mono_im (hre.trans_le ha) hb)

/-- Lower corner bound in the closed lower half-plane with positive real part. -/
theorem corner_le_arg {z : ℂ} {a₁ b₁ : ℝ} (ha₁ : 0 < a₁) (ha : a₁ ≤ z.re) (hb : b₁ ≤ z.im)
    (hb0 : z.im ≤ 0) : arg ⟨a₁, b₁⟩ ≤ arg z := by
  rw [arg_eq_mk z]
  exact (arg_mk_mono_im ha₁ hb).trans (arg_mk_mono_re ha₁ ha hb0)

/-- Upper corner bound in the closed upper half-plane with positive real part. -/
theorem arg_le_corner' {z : ℂ} {a₁ b₂ : ℝ} (ha₁ : 0 < a₁) (ha : a₁ ≤ z.re) (hb : z.im ≤ b₂)
    (hb0 : 0 ≤ z.im) : arg z ≤ arg ⟨a₁, b₂⟩ := by
  rw [arg_eq_mk z]
  exact (arg_mk_anti_re ha₁ ha hb0).trans (arg_mk_mono_im ha₁ hb)

/-- Lower corner bound in the closed upper half-plane with positive real part. -/
theorem corner_le_arg' {z : ℂ} {a₂ b₁ : ℝ} (hre : 0 < z.re) (ha : z.re ≤ a₂) (hb : b₁ ≤ z.im)
    (hb₁ : 0 ≤ b₁) : arg ⟨a₂, b₁⟩ ≤ arg z := by
  rw [arg_eq_mk z]
  exact (arg_mk_anti_re hre ha hb₁).trans (arg_mk_mono_im hre hb)

/-- Bounds for `arg (-u)` on a box `[x₁, x₂] × [y₁, y₂]` with `y₂ ≤ 0`, provided `y₂ < 0` or
`x₂ < 0`. -/
theorem arg_neg_box {u : ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ u.re ∧ u.re ≤ x₂)
    (hy : y₁ ≤ u.im ∧ u.im ≤ y₂) (hy₂ : y₂ ≤ 0) (hcase : y₂ < 0 ∨ x₂ < 0) :
    min (arg ⟨-x₁, -y₁⟩) (arg ⟨-x₁, -y₂⟩) ≤ arg (-u) ∧
      arg (-u) ≤ max (arg ⟨-x₂, -y₁⟩) (arg ⟨-x₂, -y₂⟩) := by
  rw [arg_eq_mk (-u), neg_re, neg_im]
  rcases hcase with h | h
  · have hpos : 0 < -u.im := by linarith [hy.2]
    constructor
    · refine le_trans ?_ (arg_mk_anti_re_of_im_pos (neg_le_neg hx.1) hpos)
      exact (arg_mk_im_pos_between (a := -x₁) (by linarith) (neg_le_neg hy.2)
        (neg_le_neg hy.1)).1.trans_eq' (min_comm _ _)
    · refine (arg_mk_anti_re_of_im_pos (neg_le_neg hx.2) hpos).trans ?_
      exact (arg_mk_im_pos_between (a := -x₂) (by linarith) (neg_le_neg hy.2)
        (neg_le_neg hy.1)).2.trans_eq (max_comm _ _)
  · have hre : 0 < -u.re := by linarith [hx.2]
    constructor
    · refine (min_le_right _ _).trans ?_
      exact corner_le_arg' (z := ⟨-u.re, -u.im⟩) hre (neg_le_neg hx.1) (neg_le_neg hy.2)
        (by linarith)
    · refine le_trans ?_ (le_max_left _ _)
      exact arg_le_corner' (z := ⟨-u.re, -u.im⟩) (by linarith) (neg_le_neg hx.2)
        (neg_le_neg hy.1) (by simp only; linarith [hy.2])

/-! ### Bounds for `Im f'` on boxes -/

variable {P : Params}

/-- The terms `arg (c + u)` with `c + x₁ > 0`: corner bounds. -/
theorem arg_add_box {c : ℝ} {u : ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hc : 0 < c + x₁)
    (hx : x₁ ≤ u.re ∧ u.re ≤ x₂) (hy : y₁ ≤ u.im ∧ u.im ≤ y₂) (hy₂ : y₂ ≤ 0) :
    arg ⟨c + x₁, y₁⟩ ≤ arg ((c : ℂ) + u) ∧ arg ((c : ℂ) + u) ≤ arg ⟨c + x₂, y₂⟩ := by
  have hre : ((c : ℂ) + u).re = c + u.re := by simp
  have him : ((c : ℂ) + u).im = u.im := by simp
  constructor
  · exact corner_le_arg hc (by rw [hre]; linarith [hx.1]) (by rw [him]; exact hy.1)
      (by rw [him]; linarith [hy.2])
  · exact arg_le_corner (by rw [hre]; linarith [hx.1]) (by rw [hre]; linarith [hx.2])
      (by rw [him]; exact hy.2) hy₂

/-- **Upper bound for `Im f'` on a box** `[x₁, x₂] × [y₁, y₂]` with `-η₁ < x₁`, `y₂ ≤ 0`, and
`y₂ < 0` or `x₂ < 0`. -/
theorem im_f'_le_box (hP : P.Valid) {u : ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hx₁ : -(P.etaOne : ℝ) < x₁)
    (hx : x₁ ≤ u.re ∧ u.re ≤ x₂) (hy : y₁ ≤ u.im ∧ u.im ≤ y₂) (hy₂ : y₂ ≤ 0)
    (hcase : y₂ < 0 ∨ x₂ < 0) :
    (P.f' u).im ≤ P.r * (arg ⟨P.eta0 + x₂, y₂⟩ - min (arg ⟨-x₁, -y₁⟩) (arg ⟨-x₁, -y₂⟩)) +
      ((P.zs ++ P.ps).map fun η : ℕ =>
        arg ⟨η + x₂, y₂⟩ - arg ⟨(P.eta0 : ℝ) - η + x₁, y₁⟩).sum := by
  obtain ⟨h0, h⟩ := re_pos_of_re hP (u := (x₁ : ℂ)) (by simpa using hx₁)
  simp only [ofReal_re] at h0 h
  rw [im_f']
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  gcongr ?_ + ?_
  · have h1 := (arg_add_box (c := P.eta0) h0 hx hy hy₂).2
    have h2 := (arg_neg_box hx hy hy₂ hcase).1
    push_cast at h1
    gcongr
  · refine List.sum_le_sum fun η hη => ?_
    have h1 := (arg_add_box (c := η) (h η hη).1 hx hy hy₂).2
    have h2 := (arg_add_box (c := (P.eta0 : ℝ) - η) (h η hη).2 hx hy hy₂).1
    push_cast at h1 h2
    linarith

/-- **Lower bound for `Im f'` on a box** `[x₁, x₂] × [y₁, y₂]` with `-η₁ < x₁`, `y₂ ≤ 0`, and
`y₂ < 0` or `x₂ < 0`. -/
theorem le_im_f'_box (hP : P.Valid) {u : ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hx₁ : -(P.etaOne : ℝ) < x₁)
    (hx : x₁ ≤ u.re ∧ u.re ≤ x₂) (hy : y₁ ≤ u.im ∧ u.im ≤ y₂) (hy₂ : y₂ ≤ 0)
    (hcase : y₂ < 0 ∨ x₂ < 0) :
    P.r * (arg ⟨P.eta0 + x₁, y₁⟩ - max (arg ⟨-x₂, -y₁⟩) (arg ⟨-x₂, -y₂⟩)) +
      ((P.zs ++ P.ps).map fun η : ℕ =>
        arg ⟨η + x₁, y₁⟩ - arg ⟨(P.eta0 : ℝ) - η + x₂, y₂⟩).sum ≤ (P.f' u).im := by
  obtain ⟨h0, h⟩ := re_pos_of_re hP (u := (x₁ : ℂ)) (by simpa using hx₁)
  simp only [ofReal_re] at h0 h
  rw [im_f']
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  gcongr ?_ + ?_
  · have h1 := (arg_add_box (c := P.eta0) h0 hx hy hy₂).1
    have h2 := (arg_neg_box hx hy hy₂ hcase).2
    push_cast at h1
    gcongr
  · refine List.sum_le_sum fun η hη => ?_
    have h1 := (arg_add_box (c := η) (h η hη).1 hx hy hy₂).1
    have h2 := (arg_add_box (c := (P.eta0 : ℝ) - η) (h η hη).2 hx hy hy₂).2
    push_cast at h1 h2
    linarith

/-! ### The tail of the ray -/

/-- **Tail of the ray.** For `y ≤ -Y < 0`: `Im f'(x+iy) + (r-2)π ≤ -2π + r(η₀+2|x|)/Y`. -/
theorem im_f'_add_le_tail (hP : P.Valid) {x y Y : ℝ} (hY : 0 < Y) (hy : y ≤ -Y) :
    (P.f' (x + y * I)).im + ((P.r : ℝ) - 2) * Real.pi ≤
      -2 * Real.pi + P.r * (P.eta0 + 2 * |x|) / Y := by
  have hy0 : y < 0 := by linarith
  rw [im_f']
  -- the sum is nonpositive
  have hsum : ((P.zs ++ P.ps).map fun η : ℕ =>
      arg (η + ((x : ℂ) + y * I)) - arg (P.eta0 - η + ((x : ℂ) + y * I))).sum ≤ 0 := by
    have := List.sum_le_sum (l := P.zs ++ P.ps) (g := fun _ => (0 : ℝ))
      (f := fun η : ℕ => arg (η + ((x : ℂ) + y * I)) - arg (P.eta0 - η + ((x : ℂ) + y * I)))
      (fun η hη => by
        have h2 : ((2 * η : ℕ) : ℝ) < P.eta0 := by exact_mod_cast (valid_bounds hP hη).2
        push_cast at h2
        rw [arg_eq_mk (η + ((x : ℂ) + y * I)), arg_eq_mk (P.eta0 - η + ((x : ℂ) + y * I))]
        simp only [add_re, natCast_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero, add_im, natCast_im, mul_im, zero_add, sub_re, sub_im]
        have := arg_mk_mono_re_of_im_neg (a := η + x) (a' := P.eta0 - η + x) (by linarith) hy0
        linarith)
    simpa using this
  -- the main term
  have hmain : arg (P.eta0 + ((x : ℂ) + y * I)) - arg (-((x : ℂ) + y * I)) ≤
      -Real.pi + (P.eta0 + 2 * |x|) / Y := by
    rw [arg_eq_mk (P.eta0 + ((x : ℂ) + y * I)), arg_eq_mk (-((x : ℂ) + y * I))]
    simp only [add_re, natCast_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, add_im, natCast_im, mul_im, zero_add, neg_re, neg_im]
    rw [arg_mk_of_im_neg _ hy0, arg_mk_of_im_pos _ (by linarith), neg_div_neg_eq]
    have hY' : Y ≤ |y| := by rw [abs_of_neg hy0]; linarith
    have e1 : |(P.eta0 + x) / y| ≤ (P.eta0 + |x|) / Y := by
      rw [abs_div]
      have : |(P.eta0 : ℝ) + x| ≤ P.eta0 + |x| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
      calc |(P.eta0 : ℝ) + x| / |y| ≤ (P.eta0 + |x|) / |y| := by gcongr
        _ ≤ (P.eta0 + |x|) / Y := by gcongr
    have e2 : |x / y| ≤ |x| / Y := by
      rw [abs_div]; gcongr
    have a1 := neg_abs_le (Real.arctan ((P.eta0 + x) / y))
    have a2 := le_abs_self (Real.arctan (x / y))
    have b1 := (Real.abs_arctan_le_abs (x := (P.eta0 + x) / y)).trans e1
    have b2 := (Real.abs_arctan_le_abs (x := x / y)).trans e2
    have : (P.eta0 + 2 * |x|) / Y = (P.eta0 + |x|) / Y + |x| / Y := by ring
    rw [this]
    linarith
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hmain hr
  have e : (P.r : ℝ) * (-Real.pi + (P.eta0 + 2 * |x|) / Y) =
      -P.r * Real.pi + P.r * (P.eta0 + 2 * |x|) / Y := by ring
  linarith

/-- **The ray condition from a finite part and the tail**: if `Im f' + (r-2)π ≤ -c` on the
vertical segment `[x - iY, x + iy₀]` and `-2π + r(η₀+2|x|)/Y ≤ -c`, then it holds on the whole
ray `{x + iy : y ≤ y₀}`. -/
theorem ray_of_tail (hP : P.Valid) {x y₀ Y c : ℝ} (hY : 0 < Y)
    (hfin : ∀ y ∈ Set.Icc (-Y) y₀, (P.f' (x + y * I)).im + ((P.r : ℝ) - 2) * Real.pi ≤ -c)
    (htail : -2 * Real.pi + P.r * (P.eta0 + 2 * |x|) / Y ≤ -c) :
    ∀ y ≤ y₀, (P.f' (x + y * I)).im + ((P.r : ℝ) - 2) * Real.pi ≤ -c := by
  intro y hy
  rcases le_total (-Y) y with h | h
  · exact hfin y ⟨h, hy⟩
  · exact (im_f'_add_le_tail hP hY h).trans htail

end OddZeta.Cert
