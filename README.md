# At least one of ζ(7), …, ζ(21) and at least one of ζ(9), …, ζ(33) is irrational

A Lean 4 / Mathlib formalisation (in progress) of the two main theorems of the note
[`higher_derivative_proof.pdf`](higher_derivative_proof.pdf):

* **Theorem 1.1** (`r = 5`): at least one of `ζ(7), ζ(9), …, ζ(21)` is irrational;
* **Theorem 1.2** (`r = 7`): at least one of `ζ(9), ζ(11), …, ζ(33)` is irrational.

The proof follows Zudilin's higher-derivative hypergeometric construction
(W. Zudilin, *Arithmetic of linear forms involving odd zeta values*, J. Théor. Nombres Bordeaux
16 (2004), §8): the linear forms `Fₙ = (1/(r-1)!) ∑ₜ Rₙ^{(r-1)}(t)`, their arithmetic
(Zudilin's Lemma 19 and the Chudnovsky–Rukhadze–Hata asymptotics, which need the prime number
theorem), and a saddle-point analysis of their size with certified numerical constants.

## Statements

`Challenge.lean` states the theorems (for Mathlib's `riemannZeta`, and for the real series
`∑ 1/nˢ`); `Solution.lean` proves them, and `lake comparator` (configured by
`comparator.json`) checks that the proofs prove exactly these statements from the standard
axioms `propext`, `Quot.sound`, `Classical.choice` (no `native_decide`).

## Status

Work in progress — see the commit history. The development lives in `OddZeta/`;
`scripts/` contains the (untrusted) Python programs used to design the certificates.

## Building

```bash
lake exe cache get
lake build
lake comparator --config comparator.json
```
