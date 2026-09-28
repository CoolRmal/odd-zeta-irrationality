/-
Ported from PrimeNumberTheoremAnd
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, commit 650d312, Apache-2.0),
file PrimeNumberTheoremAnd/Consequences.lean (`WeakPNT'`, `WeakPNT''`, `isLittleO_sqrt_mul_log`,
`chebyshev_asymptotic`); adapted to Lean v4.35.0-rc3 / Mathlib 3cb72cfd.
-/
import OddZeta.PNT.Wiener

/-!
# The prime number theorem for `ψ` and `θ`

From PNT+'s `WeakPNT` (`∑_{n < N} Λ(n) / N → 1`) we derive `ψ(x) ~ x` and `θ(x) ~ x`, and state
them as `ψ(x) / x → 1` and `θ(x) / x → 1`.
-/

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open Filter Real Asymptotics
open scoped Chebyshev

namespace OddZeta.PNT

/-- If `u ~ v` and `u - w = o(v)` then `w ~ v`. -/
theorem isEquivalent_of_sub_isLittleO {α β : Type*} [NormedAddCommGroup β]
    {u v w : α → β} {l : Filter α}
    (huv : u ~[l] v) (hwu : (u - w) =o[l] v) : w ~[l] v := by
  rw [← sub_sub_self u w]
  exact huv.sub_isLittleO hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n) / N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _
  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simp only [pow_one, one_mul, add_zero] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
  rw [(by rfl : ψ = (fun x ↦ ψ x))]
  simp_rw [Chebyshev.psi_eq_sum_Icc]
  apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊ : ℝ))
  · rw [isEquivalent_iff_tendsto_one]
    · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
      infer_instance
    rw [eventually_iff]
    simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
      Set.mem_ofPred_eq]
    use 1
    simp only [imp_self, implies_true]
  apply IsLittleO.isEquivalent
  rw [← isLittleO_neg_left]
  apply IsLittleO.of_bound
  intro ε hε
  simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
  use ε⁻¹
  intro b hb
  have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
  rw [abs_of_nonneg, abs_of_nonneg hb']
  · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
    linarith [Nat.lt_floor_add_one b]
  rw [sub_nonneg]
  exact floor_le hb'

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine isEquivalent_of_sub_isLittleO WeakPNT''
    (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2

end OddZeta.PNT

namespace OddZeta

open Filter Topology

/-- The prime number theorem in the form `θ(x) / x → 1`. -/
theorem tendsto_theta_div_atTop :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  have h := PNT.chebyshev_asymptotic
  rw [Asymptotics.isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx using hx.ne')] at h
  exact h

/-- The prime number theorem in the form `ψ(x) / x → 1`. -/
theorem tendsto_psi_div_atTop :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
  have h := PNT.WeakPNT''
  rw [Asymptotics.isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx using hx.ne')] at h
  exact h

end OddZeta
