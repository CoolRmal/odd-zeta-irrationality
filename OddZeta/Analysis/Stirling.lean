import Mathlib

/-!
# Complex Stirling formula in sectors

We prove that for `z` in a sector `|arg z| ≤ π - ε₀` with `‖z‖ ≥ 1`,
`Γ(z) = √(2π) exp((z - 1/2) log z - z + μ(z))` with `‖μ(z)‖ ≤ C / ‖z‖`.

The remainder is `μ(z) = ∑_{k ≥ 0} g(z + k)` where
`g(w) = (w + 1/2) (log (w + 1) - log w) - 1 = O(1/‖w‖²)`.
-/

open Complex Filter Topology Finset
open scoped Nat

namespace OddZeta

namespace StirlingAux

/-- The summand of the Stirling remainder series. -/
noncomputable def g (w : ℂ) : ℂ := (w + 1 / 2) * (Complex.log (w + 1) - Complex.log w) - 1

lemma add_one_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) : w + 1 ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  simp only [add_re, one_re, add_im, one_im, add_zero]
  rcases hw with h | h
  · left; linarith
  · right; exact h

lemma add_natCast_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) (k : ℕ) : w + k ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  simp only [add_re, natCast_re, add_im, natCast_im, add_zero]
  rcases hw with h | h
  · left; positivity
  · right; exact h

lemma log_add_one_eq {w : ℂ} (hw : w ∈ slitPlane) :
    Complex.log (w + 1) = Complex.log w + Complex.log (1 + 1 / w) := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hw1 : w + 1 ≠ 0 := slitPlane_ne_zero (add_one_mem_slitPlane hw)
  have h1 : w + 1 = w * (1 + 1 / w) := by field_simp
  have hy0 : (1 + 1 / w) ≠ 0 := by
    intro h
    apply hw1
    rw [h1, h, mul_zero]
  rw [h1, log_mul_eq_add_log_iff hw0 hy0]
  have hns : 0 < normSq w := normSq_pos.mpr hw0
  have him : (1 + 1 / w).im = -w.im / normSq w := by
    simp [div_eq_mul_inv, inv_im]
  have h1 := neg_pi_lt_arg w
  have h2 := arg_le_pi w
  have h3 := neg_pi_lt_arg (1 + 1 / w)
  have h4 := arg_le_pi (1 + 1 / w)
  rcases lt_trichotomy w.im 0 with h | h | h
  · have ha : w.arg < 0 := arg_neg_iff.mpr h
    have hb : 0 ≤ (1 + 1 / w).arg := by
      rw [arg_nonneg_iff, him]
      exact div_nonneg (by linarith) hns.le
    constructor <;> linarith
  · have hre : 0 < w.re := by
      rcases mem_slitPlane_iff.mp hw with h' | h'
      · exact h'
      · exact absurd h h'
    have ha : w.arg = 0 := arg_eq_zero_iff.mpr ⟨hre.le, h⟩
    rw [ha, zero_add]
    exact ⟨h3, h4⟩
  · have ha : 0 ≤ w.arg := arg_nonneg_iff.mpr h.le
    have hb : (1 + 1 / w).arg < 0 := by
      rw [arg_neg_iff, him]
      exact div_neg_of_neg_of_pos (by linarith) hns
    constructor <;> linarith

/-- Taylor bound for `g`. -/
lemma norm_g_le_of_two_le {w : ℂ} (hw : w ∈ slitPlane) (h2 : 2 ≤ ‖w‖) :
    ‖g w‖ ≤ 2 / ‖w‖ ^ 2 := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  set x : ℂ := 1 / w with hx
  set b : ℝ := ‖x‖ with hb
  have hbw : b = 1 / ‖w‖ := by rw [hb, hx, norm_div, norm_one]
  have hwpos : 0 < ‖w‖ := by linarith
  have hbpos : 0 < b := by rw [hbw]; positivity
  have hb2 : b ≤ 1 / 2 := by
    rw [hbw, div_le_div_iff₀ hwpos (by norm_num)]; linarith
  have hbw' : b * ‖w‖ = 1 := by rw [hbw]; field_simp
  have hT := Complex.norm_log_sub_logTaylor_le 2 (z := x) (by rw [← hb]; linarith)
  have hlt : Complex.logTaylor (2 + 1) x = x - x ^ 2 / 2 := by
    simp [Complex.logTaylor, Finset.sum_range_succ]
    ring
  rw [hlt] at hT
  set r := Complex.log (1 + x) - (x - x ^ 2 / 2) with hr
  have hwx : w * x = 1 := by rw [hx]; field_simp
  have hg : g w = r * w + r / 2 - x ^ 2 / 4 := by
    unfold g
    rw [log_add_one_eq hw, ← hx]
    have : Complex.log (1 + x) = r + (x - x ^ 2 / 2) := by rw [hr]; ring
    rw [this]
    linear_combination (1 - x / 2) * hwx
  have hrb : ‖r‖ ≤ 2 * b ^ 3 / 3 := by
    refine hT.trans ?_
    rw [← hb]
    have h1b : (1 - b)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have : b ^ (2 + 1) * (1 - b)⁻¹ ≤ b ^ 3 * 2 := by
      norm_num
      exact mul_le_mul_of_nonneg_left h1b (by positivity)
    push_cast
    linarith
  have hrw : ‖r * w‖ ≤ 2 * b ^ 2 / 3 := by
    rw [norm_mul]
    calc ‖r‖ * ‖w‖ ≤ 2 * b ^ 3 / 3 * ‖w‖ := mul_le_mul_of_nonneg_right hrb hwpos.le
      _ = 2 * b ^ 2 / 3 * (b * ‖w‖) := by ring
      _ = 2 * b ^ 2 / 3 := by rw [hbw', mul_one]
  have hx2 : ‖x ^ 2 / 4‖ = b ^ 2 / 4 := by
    rw [norm_div, norm_pow, ← hb]; norm_num
  have hr2 : ‖r / 2‖ = ‖r‖ / 2 := by rw [norm_div]; norm_num
  have hfin : 2 / ‖w‖ ^ 2 = 2 * b ^ 2 := by rw [hbw]; field_simp
  rw [hg, hfin]
  calc ‖r * w + r / 2 - x ^ 2 / 4‖ ≤ ‖r * w‖ + ‖r / 2‖ + ‖x ^ 2 / 4‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 2 * b ^ 2 / 3 + (2 * b ^ 3 / 3) / 2 + b ^ 2 / 4 := by
        rw [hr2, hx2]; gcongr
    _ ≤ 2 * b ^ 2 := by nlinarith

lemma abs_log_le (t : ℝ) (ht : 0 < t) : |Real.log t| ≤ t + t⁻¹ := by
  have h1 := Real.log_le_sub_one_of_pos ht
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at h2
  have : 0 < t⁻¹ := inv_pos.mpr ht
  rw [abs_le]; constructor <;> linarith

lemma norm_log_le {u : ℂ} (hu : u ≠ 0) : ‖Complex.log u‖ ≤ ‖u‖ + ‖u‖⁻¹ + Real.pi := by
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  rw [log_re, log_im]
  have := abs_log_le ‖u‖ (norm_pos_iff.mpr hu)
  have := abs_arg_le_pi u
  linarith

lemma norm_g_le_crude (w : ℂ) :
    ‖g w‖ ≤ (‖w‖ + 1 / 2) * (‖Complex.log (w + 1)‖ + ‖Complex.log w‖) + 1 := by
  unfold g
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_one]
  gcongr
  · exact (norm_add_le _ _).trans (by norm_num)
  · exact norm_sub_le _ _

/-- Sector geometry: `‖z + t‖ ≥ c (‖z‖ + t)` for `t ≥ 0`. -/
lemma exists_sector_bound {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ z : ℂ, |z.arg| ≤ Real.pi - ε₀ → ∀ t : ℝ, 0 ≤ t →
      c * (‖z‖ + t) ≤ ‖z + t‖ := by
  set ε := min ε₀ (Real.pi / 2) with hε
  have hεpos : 0 < ε := lt_min hε₀ (by positivity)
  have hεle : ε ≤ Real.pi / 2 := min_le_right _ _
  set a := Real.cos ε with ha
  have ha0 : 0 ≤ a := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hεle
  have ha1 : a < 1 := by
    rw [ha, ← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) hεpos
  refine ⟨Real.sqrt ((1 - a) / 2), Real.sqrt_pos.mpr (by linarith), ?_, ?_⟩
  · rw [Real.sqrt_le_one]; linarith
  intro z hz t ht
  have hc2 : Real.sqrt ((1 - a) / 2) ^ 2 = (1 - a) / 2 := Real.sq_sqrt (by linarith)
  have hc0 : 0 ≤ Real.sqrt ((1 - a) / 2) := Real.sqrt_nonneg _
  have hre : -a * ‖z‖ ≤ z.re := by
    rcases eq_or_ne z 0 with h0 | h0
    · simp [h0]
    have hcos := cos_arg h0
    have hmono : Real.cos (Real.pi - ε) ≤ Real.cos |z.arg| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
        (hz.trans (by linarith [min_le_left ε₀ (Real.pi / 2)]))
    rw [Real.cos_pi_sub, Real.cos_abs, hcos] at hmono
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr h0
    rw [le_div_iff₀ hn] at hmono
    linarith
  have hsq : ‖z + t‖ ^ 2 = (z.re + t) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; simp; ring
  have hsq' : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  rw [← pow_le_pow_iff_left₀ (mul_nonneg hc0 (by positivity)) (norm_nonneg _) two_ne_zero,
    mul_pow, hc2, hsq]
  have hn0 := norm_nonneg z
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a) (sq_nonneg (‖z‖ - t)),
    mul_le_mul_of_nonneg_left hre (by linarith : (0 : ℝ) ≤ 2 * t)]

lemma sum_inv_sq_le {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    ∑ k ∈ range n, 1 / (a + k) ^ 2 ≤ 2 / a - 2 / (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hpos : 0 < a + n := by positivity
    have key : 1 / (a + n) ^ 2 ≤ 2 / (a + n) - 2 / (a + (n + 1 : ℕ)) := by
      push_cast
      rw [div_sub_div _ _ hpos.ne' (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

lemma summable_inv_sq {a : ℝ} (ha : 1 ≤ a) : Summable fun k : ℕ => 1 / (a + k) ^ 2 :=
  summable_of_sum_range_le (c := 2 / a) (fun k => by positivity)
    (fun n => (sum_inv_sq_le ha n).trans (by
      have : 0 ≤ 2 / (a + n) := by positivity
      linarith))

lemma tsum_inv_sq_le {a : ℝ} (ha : 1 ≤ a) : ∑' k : ℕ, 1 / (a + k) ^ 2 ≤ 2 / a :=
  Real.tsum_le_of_sum_range_le (fun k => by positivity)
    (fun n => (sum_inv_sq_le ha n).trans (by
      have : 0 ≤ 2 / (a + n) := by positivity
      linarith))

lemma mem_slitPlane_of_arg {z : ℂ} {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hz0 : z ≠ 0)
    (hz : |z.arg| ≤ Real.pi - ε₀) : z ∈ slitPlane := by
  rw [mem_slitPlane_iff_arg]
  refine ⟨fun h => ?_, hz0⟩
  rw [h, abs_of_pos Real.pi_pos] at hz
  linarith

/-- Uniform bound on the terms `g (z + k)` in a sector. -/
lemma exists_norm_g_le {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → |z.arg| ≤ Real.pi - ε₀ → ∀ k : ℕ,
      ‖g (z + k)‖ ≤ K / (‖z‖ + k) ^ 2 := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_sector_bound hε₀
  set B : ℝ := (2 + 1 / 2) * ((3 + c⁻¹ + Real.pi) + (2 + c⁻¹ + Real.pi)) + 1 with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  refine ⟨(2 + 4 * B) / c ^ 2, by positivity, ?_⟩
  intro z hz1 hz k
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hslit : z + k ∈ slitPlane := add_natCast_mem_slitPlane (mem_slitPlane_of_arg hε₀ hz0 hz) k
  have hk := hc z hz k (Nat.cast_nonneg k)
  have hk1 := hc z hz (k + 1) (by positivity)
  push_cast at hk hk1
  rw [show z + ((k : ℂ) + 1) = z + k + 1 by ring] at hk1
  have hpos : 0 < ‖z‖ + k := by positivity
  have hwpos : 0 < ‖z + k‖ := lt_of_lt_of_le (by positivity) hk
  rcases le_or_gt 2 ‖z + k‖ with h2 | h2
  · refine (norm_g_le_of_two_le hslit h2).trans ?_
    have hsq : c ^ 2 * (‖z‖ + k) ^ 2 ≤ ‖z + k‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hk 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ 4 * B * (‖z‖ + k) ^ 2 := by positivity
    calc 2 * (‖z‖ + k) ^ 2 ≤ 2 * (‖z‖ + k) ^ 2 + 4 * B * (‖z‖ + k) ^ 2 := by linarith
      _ = (2 + 4 * B) / c ^ 2 * (c ^ 2 * (‖z‖ + k) ^ 2) := by field_simp
      _ ≤ (2 + 4 * B) / c ^ 2 * ‖z + k‖ ^ 2 := by gcongr
  · -- the crude region
    have hcw : c ≤ ‖z + k‖ := by nlinarith
    have hcw1 : c ≤ ‖z + k + 1‖ := by nlinarith
    have hw1 : ‖z + k + 1‖ ≤ 3 := by
      refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
    have hl1 : ‖Complex.log (z + k)‖ ≤ 2 + c⁻¹ + Real.pi := by
      refine (norm_log_le (norm_pos_iff.mp hwpos)).trans ?_
      have : ‖z + k‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc0 hcw
      linarith
    have hl2 : ‖Complex.log (z + k + 1)‖ ≤ 3 + c⁻¹ + Real.pi := by
      refine (norm_log_le (norm_pos_iff.mp (lt_of_lt_of_le hc0 hcw1))).trans ?_
      have : ‖z + k + 1‖⁻¹ ≤ c⁻¹ := inv_anti₀ hc0 hcw1
      linarith
    have hgB : ‖g (z + k)‖ ≤ B := by
      refine (norm_g_le_crude _).trans ?_
      rw [hB]
      gcongr
    refine hgB.trans ?_
    have hsmall : c * (‖z‖ + k) < 2 := lt_of_le_of_lt hk h2
    have hsq : c ^ 2 * (‖z‖ + k) ^ 2 ≤ 4 := by
      rw [← mul_pow]; nlinarith [mul_pos hc0 hpos]
    rw [le_div_iff₀ (by positivity)]
    calc B * (‖z‖ + k) ^ 2 = B * (c ^ 2 * (‖z‖ + k) ^ 2) / c ^ 2 := by field_simp
      _ ≤ B * 4 / c ^ 2 := by gcongr
      _ ≤ (2 + 4 * B) / c ^ 2 := by gcongr; linarith

/-- The remainder series converges, with an explicit `O(1/‖z‖)` bound. -/
lemma exists_hasSum_g {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → |z.arg| ≤ Real.pi - ε₀ →
      ∃ μ : ℂ, HasSum (fun k : ℕ => g (z + k)) μ ∧ ‖μ‖ ≤ C / ‖z‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_g_le hε₀
  refine ⟨2 * K, by positivity, fun z hz1 hz => ?_⟩
  have hsum : Summable fun k : ℕ => K * (1 / (‖z‖ + k) ^ 2) :=
    (summable_inv_sq hz1).mul_left K
  have hle : ∀ k : ℕ, ‖g (z + k)‖ ≤ K * (1 / (‖z‖ + k) ^ 2) := fun k => by
    rw [mul_one_div]; exact hK z hz1 hz k
  have hnorm : Summable fun k : ℕ => ‖g (z + k)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum
  refine ⟨_, hnorm.of_norm.hasSum, ?_⟩
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  refine (hnorm.tsum_le_tsum hle hsum).trans ?_
  rw [tsum_mul_left]
  calc K * ∑' k : ℕ, 1 / (‖z‖ + k) ^ 2 ≤ K * (2 / ‖z‖) :=
        mul_le_mul_of_nonneg_left (tsum_inv_sq_le hz1) hK0.le
    _ = 2 * K / ‖z‖ := by ring

/-- Summation by parts for the partial sums of the remainder series. -/
lemma sum_g_eq (z : ℂ) (N : ℕ) :
    ∑ k ∈ range N, g (z + k) + (z - 1 / 2) * Complex.log z =
      (z + N - 1 / 2) * Complex.log (z + N) - ∑ k ∈ range N, Complex.log (z + k) - N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ]
    have hg : g (z + N) = (z + N + 1 / 2) * (Complex.log (z + (N + 1)) - Complex.log (z + N))
        - 1 := by
      simp only [g, add_assoc]
    rw [hg]
    push_cast
    linear_combination ih

lemma tendsto_aux (z : ℂ) :
    Tendsto (fun N : ℕ => z - (z + N + 1 / 2) * Complex.log (1 + z / N)) atTop (𝓝 0) := by
  have hu : Tendsto (fun N : ℕ => z / (N : ℂ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat z
  have hlog : Tendsto (fun N : ℕ => Complex.log (1 + z / N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 1 + z / (N : ℂ)) atTop (𝓝 1) := by
      simpa using hu.const_add 1
    have := (continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp h1
    rw [Complex.log_one] at this
    exact this
  have hmain : Tendsto (fun N : ℕ => z - N * Complex.log (1 + z / N)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => ‖z‖ ^ 2 / N)
    · filter_upwards [eventually_ge_atTop ⌈2 * ‖z‖⌉₊, eventually_ge_atTop 1] with N hN hN1
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have hNz : 2 * ‖z‖ ≤ N := Nat.ceil_le.mp hN
      set u := z / N with hu_def
      have hun : ‖u‖ = ‖z‖ / N := by simp [u]
      have hu2 : ‖u‖ ≤ 1 / 2 := by
        rw [hun, div_le_iff₀ hNpos]; linarith
      have hb := Complex.norm_log_one_add_sub_self_le (z := u) (by linarith)
      have heq : z - N * Complex.log (1 + u) = -(N * (Complex.log (1 + u) - u)) := by
        have : (N : ℂ) * u = z := by rw [hu_def]; field_simp
        linear_combination -this
      rw [heq, norm_neg, norm_mul, Complex.norm_natCast]
      have h1u : (1 - ‖u‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      calc (N : ℝ) * ‖Complex.log (1 + u) - u‖ ≤ N * (‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2) := by gcongr
        _ ≤ N * ‖u‖ ^ 2 := by
          gcongr
          nlinarith [sq_nonneg ‖u‖]
        _ = ‖z‖ ^ 2 / N := by rw [hun]; field_simp
    · exact tendsto_const_div_atTop_nhds_zero_nat _
  have := hmain.sub (hlog.const_mul (z + 1 / 2))
  rw [mul_zero, sub_zero] at this
  exact this.congr (fun N => by ring)

/-- The key algebraic identity relating `GammaSeq` to the Stirling expression. -/
lemma key_identity {z : ℂ} (hz : z ∈ slitPlane) {N : ℕ} (hN : 1 ≤ N) :
    (Real.sqrt (2 * Real.pi) : ℂ) *
      Complex.exp (((z - 1 / 2) * Complex.log z - z + ∑ k ∈ range N, g (z + k)) +
        (((Real.log (Stirling.stirlingSeq N) - Real.log (Real.sqrt Real.pi) : ℝ) : ℂ) +
          (z - (z + N + 1 / 2) * Complex.log (1 + z / N)))) = GammaSeq z N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hzk : ∀ k : ℕ, z + k ≠ 0 := fun k => slitPlane_ne_zero (add_natCast_mem_slitPlane hz k)
  have hlog1 : Complex.log (1 + z / N) = Complex.log (z + N) - (Real.log N : ℂ) := by
    have h1 : (1 + z / N) ≠ 0 := by
      intro h
      apply hzk N
      have : z + N = N * (1 + z / N) := by field_simp; ring
      rw [this, h, mul_zero]
    have := Complex.log_ofReal_mul hNpos h1
    have h2 : ((N : ℝ) : ℂ) * (1 + z / N) = z + N := by push_cast; field_simp; ring
    rw [h2] at this
    rw [this]; ring
  have hS := sum_g_eq z N
  have hst := Stirling.log_stirlingSeq_formula N
  have h2N : Real.log (2 * N) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) hNpos.ne'
  have hNe : Real.log (N / Real.exp 1) = Real.log N - 1 := by
    rw [Real.log_div hNpos.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hsp : Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 :=
    Real.log_sqrt Real.pi_pos.le
  have hs2p : Real.log (Real.sqrt (2 * Real.pi)) = (Real.log 2 + Real.log Real.pi) / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) Real.pi_pos.ne']
  have hR : Real.log (Stirling.stirlingSeq N) - Real.log (Real.sqrt Real.pi) =
      Real.log (N ! : ℝ) - Real.log (Real.sqrt (2 * Real.pi)) - (N + 1 / 2) * Real.log N + N := by
    rw [hst, h2N, hNe, hsp, hs2p]; ring
  have hexp : ((z - 1 / 2) * Complex.log z - z + ∑ k ∈ range N, g (z + k)) +
        (((Real.log (Stirling.stirlingSeq N) - Real.log (Real.sqrt Real.pi) : ℝ) : ℂ) +
          (z - (z + N + 1 / 2) * Complex.log (1 + z / N))) =
      -(∑ k ∈ range (N + 1), Complex.log (z + k)) + (Real.log (N ! : ℝ) : ℂ) +
        (Real.log N : ℂ) * z - (Real.log (Real.sqrt (2 * Real.pi)) : ℂ) := by
    rw [hR, hlog1, sum_range_succ]
    push_cast
    linear_combination hS
  rw [hexp, Complex.exp_sub, Complex.exp_add, Complex.exp_add, Complex.exp_neg, Complex.exp_sum,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp,
    Real.exp_log (by positivity), Real.exp_log (by positivity)]
  have hprod : ∏ k ∈ range (N + 1), Complex.exp (Complex.log (z + k)) =
      ∏ k ∈ range (N + 1), (z + k) :=
    prod_congr rfl fun k _ => Complex.exp_log (hzk k)
  have hcpow : Complex.exp ((Real.log N : ℂ) * z) = (N : ℂ) ^ z := by
    rw [cpow_def_of_ne_zero hN0, Complex.ofReal_log hNpos.le, Complex.ofReal_natCast]
  have hP : ∏ k ∈ range (N + 1), (z + k) ≠ 0 := prod_ne_zero_iff.mpr fun k _ => hzk k
  have hsq : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [hprod, hcpow, GammaSeq]
  push_cast
  field_simp

/-- Stirling's formula from the convergent remainder series. -/
lemma Gamma_eq_of_hasSum {z : ℂ} (hz : z ∈ slitPlane) {μ : ℂ}
    (hμ : HasSum (fun k : ℕ => g (z + k)) μ) :
    Complex.Gamma z = Real.sqrt (2 * Real.pi) *
      Complex.exp ((z - 1 / 2) * Complex.log z - z + μ) := by
  have hA : Tendsto (fun N : ℕ => (z - 1 / 2) * Complex.log z - z + ∑ k ∈ range N, g (z + k))
      atTop (𝓝 ((z - 1 / 2) * Complex.log z - z + μ)) :=
    tendsto_const_nhds.add hμ.tendsto_sum_nat
  have h1 : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq N) -
      Real.log (Real.sqrt Real.pi)) atTop (𝓝 0) := by
    have := (Stirling.tendsto_stirlingSeq_sqrt_pi.log
      (Real.sqrt_pos.mpr Real.pi_pos).ne').sub_const (Real.log (Real.sqrt Real.pi))
    simpa using this
  have h1' : Tendsto (fun N : ℕ => ((Real.log (Stirling.stirlingSeq N) -
      Real.log (Real.sqrt Real.pi) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := Filter.tendsto_ofReal_iff.mpr h1
    simpa using this
  have hE := h1'.add (tendsto_aux z)
  rw [add_zero] at hE
  have hlim := ((Complex.continuous_exp.tendsto _).comp (hA.add hE)).const_mul
    (Real.sqrt (2 * Real.pi) : ℂ)
  rw [add_zero] at hlim
  have heq : ∀ᶠ N : ℕ in atTop, (Real.sqrt (2 * Real.pi) : ℂ) *
      Complex.exp (((z - 1 / 2) * Complex.log z - z + ∑ k ∈ range N, g (z + k)) +
        (((Real.log (Stirling.stirlingSeq N) - Real.log (Real.sqrt Real.pi) : ℝ) : ℂ) +
          (z - (z + N + 1 / 2) * Complex.log (1 + z / N)))) = GammaSeq z N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact key_identity hz hN
  exact tendsto_nhds_unique (GammaSeq_tendsto_Gamma z) (hlim.congr' heq)

lemma Gamma_add_nat_eq_mul_prod {z : ℂ} (hz : z ∈ slitPlane) (b : ℕ) :
    Complex.Gamma (z + b) = Complex.Gamma z * ∏ i ∈ range b, (z + i) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih]
    push_cast
    rw [← add_assoc, Complex.Gamma_add_one _ (slitPlane_ne_zero (add_natCast_mem_slitPlane hz b))]
    ring

end StirlingAux

open StirlingAux in
/-- Complex Stirling formula in a sector. -/
theorem exists_Gamma_eq_stirling {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → |z.arg| ≤ Real.pi - ε₀ →
      ∃ μ : ℂ, ‖μ‖ ≤ C / ‖z‖ ∧
        Complex.Gamma z = Real.sqrt (2 * Real.pi) *
          Complex.exp ((z - 1 / 2) * Complex.log z - z + μ) := by
  obtain ⟨C, hC, h⟩ := exists_hasSum_g hε₀
  refine ⟨C, hC, fun z hz1 hz => ?_⟩
  obtain ⟨μ, hμ, hμC⟩ := h z hz1 hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  exact ⟨μ, hμC, Gamma_eq_of_hasSum (mem_slitPlane_of_arg hε₀ hz0 hz) hμ⟩

open StirlingAux in
/-- Shifted version: `Γ(z + b)` for a fixed natural shift `b`. -/
theorem exists_Gamma_add_nat_eq_stirling {ε₀ : ℝ} (hε₀ : 0 < ε₀) (b : ℕ) :
    ∃ C R : ℝ, 0 < C ∧ ∀ z : ℂ, R ≤ ‖z‖ → |z.arg| ≤ Real.pi - ε₀ →
      ∃ μ : ℂ, ‖μ‖ ≤ C / ‖z‖ ∧
        Complex.Gamma (z + b) = Real.sqrt (2 * Real.pi) *
          Complex.exp ((z + b - 1 / 2) * Complex.log z - z + μ) := by
  obtain ⟨C, hC, h⟩ := exists_Gamma_eq_stirling hε₀
  refine ⟨C + 3 / 2 * ∑ i ∈ range b, (i : ℝ), max 1 (2 * b),
    add_pos_of_pos_of_nonneg hC (by positivity), fun z hzR hz => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hzR
  have hzb : 2 * (b : ℝ) ≤ ‖z‖ := (le_max_right _ _).trans hzR
  have hzpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hzs := mem_slitPlane_of_arg hε₀ hz0 hz
  obtain ⟨μ, hμC, hΓ⟩ := h z hz1 hz
  have hsmall : ∀ i ∈ range b, ‖(i : ℂ) / z‖ ≤ 1 / 2 := by
    intro i hi
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hzpos]
    have : (i : ℝ) ≤ b := by exact_mod_cast (mem_range.mp hi).le
    linarith
  refine ⟨μ + ∑ i ∈ range b, Complex.log (1 + i / z), ?_, ?_⟩
  · have hn : ‖∑ i ∈ range b, Complex.log (1 + i / z)‖ ≤
        ∑ i ∈ range b, 3 / 2 * ((i : ℝ) / ‖z‖) := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
      have := norm_log_one_add_half_le_self (hsmall i hi)
      rwa [norm_div, Complex.norm_natCast] at this
    calc ‖μ + ∑ i ∈ range b, Complex.log (1 + i / z)‖
        ≤ ‖μ‖ + ‖∑ i ∈ range b, Complex.log (1 + i / z)‖ := norm_add_le _ _
      _ ≤ C / ‖z‖ + ∑ i ∈ range b, 3 / 2 * ((i : ℝ) / ‖z‖) := add_le_add hμC hn
      _ = (C + 3 / 2 * ∑ i ∈ range b, (i : ℝ)) / ‖z‖ := by
        rw [add_div, mul_div_assoc, sum_div, mul_sum]
  · have hprod : ∏ i ∈ range b, (z + i) =
        Complex.exp (b * Complex.log z + ∑ i ∈ range b, Complex.log (1 + i / z)) := by
      have h1 : ∀ i ∈ range b, z + i = Complex.exp (Complex.log z + Complex.log (1 + i / z)) := by
        intro i hi
        have hne : (1 + (i : ℂ) / z) ≠ 0 := by
          intro h0
          have h1' : (i : ℂ) / z = -1 := by linear_combination h0
          have := hsmall i hi
          rw [h1', norm_neg, norm_one] at this
          norm_num at this
        rw [Complex.exp_add, Complex.exp_log hz0, Complex.exp_log hne]
        field_simp
      rw [prod_congr rfl h1, ← Complex.exp_sum, sum_add_distrib, sum_const, card_range,
        nsmul_eq_mul]
    rw [Gamma_add_nat_eq_mul_prod hzs b, hΓ, hprod, mul_assoc, ← Complex.exp_add]
    congr 2
    ring

end OddZeta
