import Mathlib

/-!
# Polygonal contour integrals

We define the integral `segInt f a b` of a function `f : ℂ → ℂ` along the oriented segment
from `a` to `b`, and the integral `polyInt f l` along the polygonal path through the points of a
list `l`. We prove:

* `segInt_eq_sub_of_hasDerivAt`, `polyInt_eq_sub_of_hasDerivAt`: the fundamental theorem of
  calculus along segments and polygonal paths lying in a convex set carrying a primitive;
* `polyInt_eq_of_ball`, `polyInt_closed_of_ball`: Cauchy's theorem for polygonal paths in a disc;
* `segInt_line`, `segInt_vertical`, `segInt_horizontal`: comparison with real interval integrals;
* `segInt_mul_mul`, `polyInt_map_mul`: behaviour under scaling;
* `norm_segInt_le`: the standard length times sup bound.
-/

open Complex MeasureTheory Set

namespace OddZeta

/-- Integral of `f` along the oriented segment from `a` to `b`. -/
noncomputable def segInt (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ s in (0:ℝ)..1, f (a + s * (b - a)) * (b - a)

/-- Integral along the polygonal path through the points of a list. -/
noncomputable def polyInt (f : ℂ → ℂ) : List ℂ → ℂ
  | a :: b :: l => segInt f a b + polyInt f (b :: l)
  | _ => 0

@[simp] lemma polyInt_nil (f : ℂ → ℂ) : polyInt f [] = 0 := rfl

@[simp] lemma polyInt_singleton (f : ℂ → ℂ) (a : ℂ) : polyInt f [a] = 0 := rfl

@[simp] lemma polyInt_cons_cons (f : ℂ → ℂ) (a b : ℂ) (l : List ℂ) :
    polyInt f (a :: b :: l) = segInt f a b + polyInt f (b :: l) := rfl

lemma polyInt_pair (f : ℂ → ℂ) (a b : ℂ) : polyInt f [a, b] = segInt f a b := by simp

/-! ### Fundamental theorem of calculus -/

lemma add_mul_sub_mem_segment {a b : ℂ} {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    a + (s : ℂ) * (b - a) ∈ segment ℝ a b := by
  rw [segment_eq_image']
  exact ⟨s, hs, by simp [Complex.real_smul]⟩

/-- Fundamental theorem of calculus along a segment. -/
theorem segInt_eq_sub_of_hasDerivAt {f g : ℂ → ℂ} {a b : ℂ}
    (hg : ∀ z ∈ segment ℝ a b, HasDerivAt g (f z) z) (hf : ContinuousOn f (segment ℝ a b)) :
    segInt f a b = g b - g a := by
  have hγ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => a + (s : ℂ) * (b - a)) (b - a) s := by
    intro s
    simpa using (((hasDerivAt_id s).ofReal_comp).mul_const (b - a)).const_add a
  have hmaps : MapsTo (fun s : ℝ => a + (s : ℂ) * (b - a)) (uIcc 0 1) (segment ℝ a b) := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact add_mul_sub_mem_segment hs
  have hcont : ContinuousOn (fun s : ℝ => f (a + (s : ℂ) * (b - a)) * (b - a)) (uIcc 0 1) :=
    (hf.comp (by fun_prop : Continuous fun s : ℝ => a + (s : ℂ) * (b - a)).continuousOn
      hmaps).mul continuousOn_const
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => g (a + (s : ℂ) * (b - a)))
    (f' := fun s : ℝ => f (a + (s : ℂ) * (b - a)) * (b - a)) (a := 0) (b := 1)
    (fun s hs => (hg _ (hmaps hs)).comp s (hγ s)) hcont.intervalIntegrable
  simpa [segInt] using key

/-- Fundamental theorem of calculus along a polygonal path in a convex set on which `f` is
continuous and has the primitive `g`. -/
theorem polyInt_eq_sub_of_hasDerivAt {f g : ℂ → ℂ} {U : Set ℂ} (hU : Convex ℝ U)
    (hg : ∀ z ∈ U, HasDerivAt g (f z) z) (hf : ContinuousOn f U) (a : ℂ) (l : List ℂ)
    (hl : ∀ z ∈ a :: l, z ∈ U) :
    polyInt f (a :: l) = g ((a :: l).getLast (List.cons_ne_nil a l)) - g a := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have ha : a ∈ U := hl a (by simp)
    have hb : b ∈ U := hl b (by simp)
    have hseg := hU.segment_subset ha hb
    rw [polyInt_cons_cons, ih b (fun z hz => hl z (List.mem_cons_of_mem a hz)),
      segInt_eq_sub_of_hasDerivAt (fun z hz => hg z (hseg hz)) (hf.mono hseg),
      List.getLast_cons_cons]
    ring

/-- **Cauchy's theorem for polygonal paths in a disc.** Two polygonal paths in a disc on which
`f` is holomorphic, with the same initial and the same final point, give the same integral. -/
theorem polyInt_eq_of_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c R)) {l₁ l₂ : List ℂ}
    (h₁ : ∀ z ∈ l₁, z ∈ Metric.ball c R) (h₂ : ∀ z ∈ l₂, z ∈ Metric.ball c R)
    (hhead : l₁.head? = l₂.head?) (hlast : l₁.getLast? = l₂.getLast?) :
    polyInt f l₁ = polyInt f l₂ := by
  obtain ⟨g, hg⟩ := hf.isExactOn_ball
  have H := polyInt_eq_sub_of_hasDerivAt (convex_ball c R) hg hf.continuousOn
  match l₁, l₂ with
  | [], [] => rfl
  | [], _ :: _ => simp at hhead
  | _ :: _, [] => simp at hhead
  | a₁ :: l₁, a₂ :: l₂ =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _),
      List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), Option.some.injEq] at hlast
    rw [H a₁ l₁ h₁, H a₂ l₂ h₂, hlast, hhead]

/-- **Cauchy's theorem for closed polygonal paths in a disc.** -/
theorem polyInt_closed_of_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c R)) (a : ℂ) (l : List ℂ)
    (hl : ∀ z ∈ a :: l, z ∈ Metric.ball c R) :
    polyInt f (a :: l ++ [a]) = 0 := by
  have hl' : ∀ z ∈ a :: l ++ [a], z ∈ Metric.ball c R := by
    intro z hz
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hz
    exact hl z (by rcases hz with h | h | h | h <;> simp_all)
  have := polyInt_eq_of_ball hf hl' (l₂ := [a]) (by simpa using hl a (by simp)) (by simp)
    (by rw [List.getLast?_append]; simp)
  simpa using this

/-! ### Comparison with real interval integrals -/

/-- The integral along the segment from `c + s₁ v` to `c + s₂ v`. -/
theorem segInt_line (f : ℂ → ℂ) (c v : ℂ) (s₁ s₂ : ℝ) :
    segInt f (c + s₁ * v) (c + s₂ * v) = v * ∫ s in s₁..s₂, f (c + s * v) := by
  have h := intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1)
    (f := fun s : ℝ => f (c + s * v)) (s₂ - s₁) s₁
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at h
  rw [← h, Complex.real_smul, segInt, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  congr 1
  ext t
  rw [show c + (s₁ : ℂ) * v + t * (c + s₂ * v - (c + s₁ * v)) = c + ((s₂ - s₁) * t + s₁ : ℝ) * v
    by push_cast; ring]
  push_cast
  ring

/-- The integral along a vertical segment. -/
theorem segInt_vertical (f : ℂ → ℂ) (x y₁ y₂ : ℝ) :
    segInt f (x + y₁ * I) (x + y₂ * I) = I * ∫ y in y₁..y₂, f (x + y * I) :=
  segInt_line f x I y₁ y₂

/-- The integral along a horizontal segment. -/
theorem segInt_horizontal (f : ℂ → ℂ) (x₁ x₂ y : ℝ) :
    segInt f (x₁ + y * I) (x₂ + y * I) = ∫ x in x₁..x₂, f (x + y * I) := by
  have h := segInt_line f (y * I) 1 x₁ x₂
  simp only [mul_one, one_mul] at h
  rw [add_comm (x₁ : ℂ), add_comm (x₂ : ℂ), h]
  simp only [add_comm (y * I : ℂ)]

/-! ### Scaling -/

theorem segInt_mul_mul (f : ℂ → ℂ) (n a b : ℂ) :
    segInt f (n * a) (n * b) = n * segInt (fun u => f (n * u)) a b := by
  simp only [segInt, ← intervalIntegral.integral_const_mul]
  congr 1
  ext s
  rw [show n * a + (s : ℂ) * (n * b - n * a) = n * (a + s * (b - a)) by ring]
  ring

theorem polyInt_map_mul (f : ℂ → ℂ) (n : ℂ) (l : List ℂ) :
    polyInt f (l.map (n * ·)) = n * polyInt (fun u => f (n * u)) l := by
  match l with
  | [] => simp
  | [a] => simp
  | a :: b :: l =>
    simp only [List.map_cons, polyInt_cons_cons, segInt_mul_mul, mul_add]
    rw [← polyInt_map_mul f n (b :: l), List.map_cons]

/-! ### Estimates -/

/-- The integral along a segment is bounded by the length of the segment times a bound for
`‖f‖` on it. -/
theorem norm_segInt_le {f : ℂ → ℂ} {a b : ℂ} {B : ℝ} (hB : ∀ z ∈ segment ℝ a b, ‖f z‖ ≤ B) :
    ‖segInt f a b‖ ≤ B * ‖b - a‖ := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := B * ‖b - a‖)
    (f := fun s : ℝ => f (a + s * (b - a)) * (b - a)) (fun s hs => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _ (add_mul_sub_mem_segment (Ioc_subset_Icc_self
        (by simpa using hs)))) (norm_nonneg _))
  simpa [segInt] using this

end OddZeta
