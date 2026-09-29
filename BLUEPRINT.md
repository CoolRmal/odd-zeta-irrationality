# Blueprint of the formal proof

This file records the mathematical plan of the formalisation and the interfaces between the
Lean modules. It follows the note (`higher_derivative_proof.pdf`, cited as [N]) and Zudilin's
paper (J. Théor. Nombres Bordeaux 16 (2004), §7–8, cited as [Z]), with the changes listed in
"Deviations" below, which are chosen to make every numerical ingredient checkable by the Lean
kernel (no `native_decide`).

## 0. Data

Two cases (the third case (C) of [N] is not formalised):

| case | r | q  | η₀  | η₁..η_r (zero blocks)  | η_{r+1}..η_q (pole blocks) |
|------|---|----|-----|------------------------|----------------------------|
| A    | 5 | 23 | 196 | 58,58,58,59,60         | 62,62,63,64,64,65,66,66,68,69,70,72,73,75,76,77,79,80 |
| B    | 7 | 35 | 151 | 46×7                   | 47,47,48,49,49,49,50,51,51,51,52,53,53,53,54,55,55,55,56,57,57,57,58,59,59,59,60,61 |

For `n ≥ 1`: `h₀ = η₀ n + 2`, `hⱼ = ηⱼ n + 1`.

## 1. The rational function and its partial fractions

`Rₙ(t) = (h₀+2t) ∏_{j≤r} (t+1)_{hⱼ-1}(t+h₀-hⱼ+1)_{hⱼ-1}/((hⱼ-1)!)² · ∏_{j>r} (h₀-2hⱼ)!/(t+hⱼ)_{h₀-2hⱼ+1}`.

Poles: `-k` for `k ∈ [h_{r+1}, h₀-h_{r+1}]`, order `m_k = #{j>r : hⱼ ≤ k ≤ h₀-hⱼ} ≤ q-r`.

**Bricks at a pole.** For such `k`, `ε^{q-r} Rₙ(-k+ε) ∈ ℚ⟦ε⟧` is the product of the power series
* `(h₀-2k) + 2ε`;
* `Pⱼ⁺(-k+ε) = ∏_{i=1}^{hⱼ-1}(i-k+ε)/(hⱼ-1)!`, `Pⱼ⁻(-k+ε) = ∏_{i=h₀-hⱼ+1}^{h₀-1}(i-k+ε)/(hⱼ-1)!` (j ≤ r);
* `ε·Cⱼ(-k+ε) = ε (h₀-2hⱼ)! / ∏_{i=hⱼ}^{h₀-hⱼ}(i-k+ε)` (j > r; the factor `ε` cancels `i = k`).

`a_{i,k} := coeff_{q-r-i}(ε^{q-r} Rₙ(-k+ε))` (1 ≤ i ≤ q-r). Then (general partial fraction
lemma, module `PartialFractions`)
`Rₙ(t) = ∑_k ∑_{i=1}^{q-r} a_{i,k} (t+k)^{-i}`,  and `∑_k a_{1,k} = 0` (deg Rₙ ≤ -2),
and `a_{i,k} = (-1)^{i+1} a_{i,h₀-k}` (from `Rₙ(-t-h₀) = -Rₙ(t)`).

**The linear form.** `ρₙ(m) := ∑_{i,k} C(i+r-2,r-1) a_{i,k} (m+k)^{-(i+r-1)}` (this is
`Rₙ^{(r-1)}(m)/(r-1)!`), and `Fₙ := ∑_{m ≥ 1-h₁} ρₙ(m)`. Then
`Fₙ = ∑_{s=r}^{q-1} A_s ζ(s) - A₀`, `A_s = C(s-1,r-1) ∑_k a_{s-r+1,k}`,
`A₀ = ∑_{i,k} C(i+r-2,r-1) a_{i,k} ∑_{l=1}^{k-h₁} l^{-(i+r-1)}`; `A_s = 0` for `s = r` and for even `s`.

## 2. Arithmetic (Lemma 3.2 of [N] = Lemma 19 of [Z], reorganised p-adically)

For a prime `p` and `x ∈ ℚ` write `v_p(x) ≥ e` for `x = 0 ∨ e ≤ padicValRat p x`.
Coefficients of a product of power series satisfy `v_p(coeff_l ∏_β f_β) ≥ -l + ∑ ν_β` as soon as
`v_p(coeff_j f_β) ≥ -j + ν_β` for all `β, j`.

* **Large primes** `p > √h₀` (so `v_p(c) ≤ 1` for `0 < |c| < h₀`): each brick satisfies
  `v_p(coeff_l) ≥ -l + ι_β` with `ι(u,v) = ⌊(u+v)/p⌋ - ⌊u/p⌋ - ⌊v/p⌋ ∈ {0,1}`, hence
  `v_p(a_{i,k}) ≥ -(q-r-i) + φ₀(n/p, (k-1)/p)` with `φ₀` of (3.2) of [N]. If moreover `p > m̂₀ n`
  every brick coefficient is `p`-integral.
* **Small primes** `p ≤ √h₀`: crude bound `v_p(coeff_l) ≥ -(l+1) L_p`, `L_p = ⌊log_p h₀⌋`.

`Δₙ := ∏_{p ≤ √h₀} p^{3q L_p} · ∏_{√h₀ < p} p^{e_p}`, `e_p = r[p ≤ m̂₁n] + ∑_{j≥2}[p ≤ m̂ⱼn] - [p ≤ m̂₀n] φ'(n/p)`,
where `φ' ≤ φ` is the certified step function of §3. Then `Δₙ A_s ∈ ℤ` for all `s`.

## 3. The function φ and the constant C₂

`φ₀(x,y) = ∑_β ι_β` (sum of `q+r` indicator terms `⌊A+B⌋-⌊A⌋-⌊B⌋`), `φ(x) = min_y φ₀(x,y)`.
On each open interval between consecutive points of the finite set `X` of [N, Lemma 3.1] the
circular order of the points `{a x} (a ∈ {0, η₀, ηⱼ, η₀-ηⱼ})` is constant; the kernel checks a
certificate (interval, value) for each interval (module `PhiCert`).

`log Δₙ ≤ n (C₂' + o(1))` with `C₂' = r m̂₁ + ∑_{j≥2} m̂ⱼ - I'`, where
`I' = ∑_i v_i [∑_{k=1}^{K} (1/(k+αᵢ) - 1/(k+βᵢ)) + [αᵢ ≥ 1/m̂₀](1/αᵢ - 1/βᵢ)]` (rational, truncation of
(3.6) at `K` periods; needs only the prime number theorem `θ(x) ~ x`).

| case | K  | C₂' (≈) | C₀ (≈) |
|------|----|---------|--------|
| A    | 20 | 937.32  | 939.03 |
| B    | 20 | 1171.86 | 1175.78 |

## 4. Analysis

* **Integral representation.** `M = 1/2 - h₁`. By partial fractions and explicit vertical-line
  integrals of `(t-p)^{-j}`: `∫_{Re t=M} Rₙ(t)(t-m)^{-r} dt = -2πi ρₙ(m)` if `m > M`, `0` if `m < M`.
  With `∑_{m∈ℤ}(t-m)^{-r} = π^r S(t)/sin^r(πt)`, `S(t) = ∑_{|k|≤r-2, k≡r (2)} c_k e^{ikπt}`
  (Lipschitz formula + Eulerian numbers) and `Rₙ(t) = (-sin πt/π)^r G(t)`,
  `G(t) = Norm·(h₀+2t)Γ(-t)^rΓ(t+h₀)^r ∏_j Γ(t+hⱼ)/Γ(t+h₀-hⱼ+1)`:
  `Fₙ = (1/2πi) ∫_{Re t=M} S(t)G(t) dt = (1/π) Im ∫_{M-i∞}^{M} S(t)G(t) dt`.
* **Contour.** `L` (lower half only): vertical ray `{Re u = Re bot, Im u ≤ Im bot}`, segment
  `σ = [bot, top]` through the saddle point `u*` in direction `φ`, horizontal segment from `top` to
  `x₁ + i Im top`, vertical segment up to `x₁ ∈ (-η₁,0)`. Cauchy's theorem on discs
  (`DifferentiableOn.isExactOn_ball`) moves `∫_{M-i∞}^{M}` to `n∫_L` plus a real segment (whose
  contribution is real, hence invisible in `Im`).
* **Stirling** in sectors `|arg z| ≤ π-ε₀`: `G(nu) = Aₙ e^{n f(u)} Ĝ(u)(1+εₙ(u))`, `|εₙ| ≤ C/n` on `L`.
* **Saddle point.** `F = f + i(r-2)πu`; dominant mode `k = r-2`; other modes are smaller by
  `e^{-2πn|Im u|}`. Laplace's method on `σ`; on `L \ σ`, `Re F` is monotone (derivative sign
  checks), hence `≤ Re F(u*) - δ`.
* **Conclusion.** `Fₙ = Kₙ (Im(e^{inα}B) + o(1))`, `Kₙ > 0`, `(1/n) log Kₙ → H_d = Re F(u*) = -C₀`,
  `B ≠ 0`, `α = Im F(u*) ∉ πℤ`.

## 5. Numerical certificates (all kernel-checked)

* (N1) existence of the saddle `u*` within `10⁻⁸` of a rational point (contraction mapping);
* (N2) bounds for `f''(u*)`, `|f'''|` on the disc of radius `s₀` (rational);
* (N3) `H_d < -C₂'` (log / arctan enclosures at one point);
* (N4) `α ∉ πℤ`;
* (N5) monotonicity along the three pieces of `L \ σ`: `Im f' + (r-2)π ≤ -c` on the ray (arctan),
  `Re f' > 0` on the horizontal segment (rational), `Im f' + (r-2)π > 0` on the vertical segment
  (arctan);
* (N6) the φ certificate and `I'` (rational).

## Deviations from [N]

1. `Δₙ` contains an extra factor `∏_{p ≤ √h₀} p^{3q⌊log_p h₀⌋} = e^{O(√n log n)}` (crude treatment of
   small primes instead of Zudilin's Lemmas 15–16).
2. `I_Φ` is replaced by the rational truncation `I'` (no digamma values).
3. The path `L` is replaced by one on which `Re F` is monotone off `σ`, and the upper half-plane
   is handled by the symmetry `G(t̄) = conj G(t)`; conditions (P3)–(P4) of [N] are replaced by
   derivative-sign checks.
4. `Fₙ` is summed from `t = 1-h₁` (as in [Z]); the line of integration is `Re t = 1/2 - h₁`.

# Theorem 8.1: one of ζ(r+2), …, ζ(6r−1) is irrational for every odd r ≥ 3

Source: `higher_derivative_proof_1.pdf` (September 29, 2026), Section 8. Statements of record:
`Challenge6r.lean`; proofs `Solution6r.lean`; comparator config `comparator6r.json`.

## Plan (as formalised)

A single family is used for **every** odd `r ≥ 3` (the note uses other direction vectors for
`r ≤ 15`; numerically the family works for all `r`, with `C₀ − C₂ ≥ 80` at `r = 3`):
`η^(r) = (150; 45^r; 48^r, 50^r, 53^r, 56^r, 60^r, 74)`, `q = 6r + 1`
(`OddZeta/Family/Defs.lean`).

* **Arithmetic** (`Family/Arith.lean`, `Family/PhiBase.lean`; Lemma 8.4): `φ₀(η^(r)) = r φ̄₀ + ι₇₄ ≥ r φ̄₀`
  for the base vector `(150; 45; 48, 50, 53, 56, 60)`, whose `φ̄` is certified once (1211 intervals);
  `I' = r Ī'` with `Ī' ≥ 116.2` (truncation `K = 20`); `r m̂₁ + ∑ m̂ⱼ = 331 r − 3`; so `C₂' ≤ 214.8 r − 3`.
* **Structure** (`Family/Phase.lean`; Lemma 8.2): on `Im u < 0`, `Fd = r g + e − 2πi u` with the
  `r`-independent `g`, `e`; hence all evaluations cost `O(1)` in `r`.
* **Generalised saddle framework** (`Analytic/Saddle2.lean`, `Final/Main2.lean`): paths
  `-i∞ → P_R → bot → σ → top → P_L → x₁` with sup-bound conditions (`PathCert2`) instead of the
  monotonicity conditions of `PathCert`.
* **Certificates** `FamCert r` (`Family/Cert*.lean`):
  * `3 ≤ r ≤ 299`: one kernel-checked certificate per `r` (contraction for the saddle point; the ray
    `Re u = 20` covered for all `r` by the region bound of Lemma 8.7; three short segments checked on
    grids of ≈ 30–40 points; `y_R = min(−1/4, Im bot)`).
  * `r ≥ 301`: the asymptotic bounds of Section 8.7 (Newton–Kantorovich around
    `u₁ = a + (e₁ − 2πi)/(r D̄)`, explicit Taylor bounds), with the `r`-independent regions of
    Section 8.4 (`Family/Regions.lean`: Lemma 8.7's suprema of `Re g` and `Re e + 2π Im u` over
    `B_L`, `B_R`, `[P_L, x₀]` and the ray; rectangles by the maximum principle).

## Deviations from the note (Theorem 8.1)

1. One family for all `r` (no separate vectors for `r ≤ 15`, no Table 6 path shapes).
2. The per-`r` regime is `3 ≤ r ≤ 299` (the note: `17 ≤ r ≤ 49` by Section 5 paths, `51 ≤ r ≤ 19999` by
   scalar checks) and the asymptotic regime starts at `r = 301` (the note: `20001`); the bounds of
   Section 8.7 already hold there.
3. The region bounds of Lemma 8.7 are loosened by `≈ 5·10⁻⁴`.
