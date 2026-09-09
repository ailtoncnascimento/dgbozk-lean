/-
# §5.  The localized cubic cancellation — the technical heart of the defocusing argument

This file formalizes the algebraic core of `Lemma lem:localized-cancellation`
and of the identity `(eq:cancellation-computation)` in

  A. C. Nascimento, *Local well-posedness for two-sign dispersion-generalized
  Benjamin–Ono–Zakharov–Kuznetsov equations*.

The paper's own commentary is that this is the step which cannot be omitted:

  "The proof uses the following two elementary facts and one localized
   cancellation.  They are included because omitting the last one gives a false
   proof of (5.13)."

and, of the principal term, that it "is exactly the negative of (eq:bad-sm), so
the two cancel identically, with no error and no denominator."

That is a claim about a **sign**, asserted with no room to spare, and it is
therefore exactly the kind of key calculation Tao's conditional-formalization
strategy is meant to isolate.

## The reduction

The three terms on the left of `(eq:cancellation-computation)` arise by
differentiating the cubic correction

  `H^{2τ−1} ∫ b · Π_H(P_{≪H}u, P_{∼H}u) · P_H u`

along the **transverse** linear evolution `∂_t u = −∂_x∂_y² u`.  Write the three
factors as `1 = v = P_{≪H}u`, `2 = z_{∼H}`, `3 = z_H`, with frequencies
`θ_j = (a_j, b_j)`.

Two structural facts, both stated in the paper, reduce the identity to algebra:

* `Π_H` is a **bilinear Fourier multiplier in its two arguments jointly**, so
  its symbol `e_{3,H}(θ₁,θ₂)` is a common factor of every term and the Leibniz
  rule `∂_y Π(f,g) = Π(∂_y f, g) + Π(f, ∂_y g)` holds (the paper displays this);
* the integral of a product of three frequency-localized factors is supported on
  `θ₁ + θ₂ + θ₃ = 0`.

On the Fourier side `∂_x ↦ i a_j` and `∂_y ↦ i b_j`, so `−∂_x∂_y²` acting on the
`j`-th factor has symbol `−(i a_j)(i b_j)²`.  Every term appearing in the
identity carries **exactly three** derivative factors, so the common factor `i³`
is uniform and the identity below is a polynomial identity valid over any
commutative ring containing the imaginary unit — no property of `i` is used, and
`ring` discharges it.

## What this file established, and how the manuscript uses it

`transverse_flow_identity` proves that the transverse flow derivative of the
cubic correction, taken with a **`+`** sign in `(eq:localized-functional)`,
carries the principal term with coefficient **`−2`**: it would *reinforce* the
bad term `(eq:bad-sm)` rather than cancel it.  `transverse_flow_identity_negated`
gives the same computation for the correction taken with a **`−`** sign, where
the principal coefficient is `+2` and the cancellation is exact.

An earlier draft of the manuscript displayed the `+` correction together with a
`+2` principal term, which is inconsistent; `paper_identity_forces` records
precisely what that combination would entail.  **The current manuscript carries
the minus sign in `(eq:localized-functional)`**, so it is
`transverse_flow_identity_negated` that corresponds to the published identity,
and `T2`/`T3` below are its `𝒯⁽²⁾` and `𝒯⁽³⁾`.

Note one thing this file does *not* settle, and which the manuscript establishes
separately: the computation here takes the weight `b` constant, so it says
nothing about the terms carrying `b'`.  In the manuscript those are collected as
`ℬ^lin`, and the Leibniz cross term `2Π(∂_yv,∂_yz')` produced by the two
`y`-integrations by parts cancels against the `b'` term generated when the
principal term is integrated by parts in `x`.  That cancellation is genuine but
is outside the scope of the symbol calculus used here.

A second, independent hand derivation of the `+`-sign case agrees with
`transverse_flow_identity`: integrating by parts twice in `y` in the third term
and expanding `∂_y²Π(v,z) = Π(∂_y²v,z) + 2Π(∂_yv,∂_yz) + Π(v,∂_y²z)` produces
`−2 ∫ b Π(∂_yv,∂_yz)∂_x z` directly.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Field.Basic

set_option autoImplicit false

namespace DGBOZK.Cancellation

variable {R : Type*} [CommRing R]

/-! ## Symbols

`I` denotes the imaginary unit.  None of the results below use `I² = −1`; the
identity is a polynomial identity in `I`.  This is a feature: it shows the sign
conclusion does not depend on any convention for the Fourier transform beyond
`∂_x ↦ i a`, `∂_y ↦ i b`.
-/

/-- Symbol of `−∂_x∂_y²` (the transverse linear evolution `∂_t u = −∂_x∂_y²u`)
acting on a factor of frequency `(a, b)`. -/
def Lsym (I a b : R) : R := -((I * a) * (I * b) ^ 2)

/-- Symbol of the **principal** trilinear expression
`Π(∂_y v, ∂_y z_{∼H}) · ∂_x z_H`, i.e. of the term displayed in
`(eq:cancellation-computation)` and, up to sign, of the "bad" term
`(eq:bad-sm)`. -/
def T1 (I b₁ b₂ a₃ : R) : R := (I * b₁) * (I * b₂) * (I * a₃)

/-- Symbol of `Π(∂_x v, ∂_y² z_{∼H}) · z_H`.  This is the paper's
**Taylor-remainder term**, which it lists and estimates by
`T^{1/2}𝒜⁺(ℰ⁺)²`. -/
def T2 (I a₁ b₂ : R) : R := (I * a₁) * (I * b₂) ^ 2

/-- Symbol of `Π(∂_y² v, ∂_x z_{∼H}) · z_H` — the manuscript's `𝒯⁽³⁾`.  It is
produced by the same expansion as `T2`, and an earlier draft omitted it from the
list of remainders; see `residual_term_unlisted` below. -/
def T3 (I b₁ a₂ : R) : R := (I * b₁) ^ 2 * (I * a₂)

/-! ## The exact identity -/

/-- **The real symbol identity.**  Under the frequency constraints
`Σ a_j = Σ b_j = 0`,

  `a₁b₁² + a₂b₂² + a₃b₃² = 2 a₃ b₁ b₂ − a₁ b₂² − a₂ b₁²`.

This is the entire content of `(eq:cancellation-computation)`, stripped of the
common factor `i³` and of the multiplier symbol `e_{3,H}`.  Note that it is
*exact*: no error term, no denominator, in agreement with the paper's claim on
that point. -/
theorem flow_symbol_identity (a₁ a₂ a₃ b₁ b₂ b₃ : R)
    (ha : a₁ + a₂ + a₃ = 0) (hb : b₁ + b₂ + b₃ = 0) :
    a₁ * b₁ ^ 2 + a₂ * b₂ ^ 2 + a₃ * b₃ ^ 2
      = 2 * a₃ * b₁ * b₂ - a₁ * b₂ ^ 2 - a₂ * b₁ ^ 2 := by
  have ha3 : a₃ = -a₁ - a₂ := by linear_combination ha
  have hb3 : b₃ = -b₁ - b₂ := by linear_combination hb
  subst ha3
  subst hb3
  ring

/-- **The identity in operator form.**  The derivative of the cubic correction
along the transverse flow equals

  `(−2)·Π(∂_y v, ∂_y z_{∼H})∂_x z_H  +  Π(∂_x v, ∂_y² z_{∼H})z_H
     +  Π(∂_y² v, ∂_x z_{∼H})z_H`.

The coefficient of the principal term is **`−2`**.  This is why the manuscript
carries a **minus** sign on the cubic correction in `(eq:localized-functional)`;
see `transverse_flow_identity_negated`, which is the form it uses.

No property of `I` is used: the identity is polynomial in `I`.  The sign flip
relative to `flow_symbol_identity` is exactly the uniform factor `i³ = −i`
carried by every term (each has one `∂_x` and two `∂_y`). -/
theorem transverse_flow_identity (I a₁ a₂ a₃ b₁ b₂ b₃ : R)
    (ha : a₁ + a₂ + a₃ = 0) (hb : b₁ + b₂ + b₃ = 0) :
    Lsym I a₁ b₁ + Lsym I a₂ b₂ + Lsym I a₃ b₃
      = (-2) * T1 I b₁ b₂ a₃ + T2 I a₁ b₂ + T3 I b₁ a₂ := by
  have ha3 : a₃ = -a₁ - a₂ := by linear_combination ha
  have hb3 : b₃ = -b₁ - b₂ := by linear_combination hb
  subst ha3
  subst hb3
  unfold Lsym T1 T2 T3
  ring

/-! ## Consequences of the sign

The next two statements pin down what the discrepancy means, without overstating
it.
-/

/-- **What the inconsistent combination would force.**  Suppose the transverse
flow derivative of the `+`-sign correction equals `+2·T1 + N` for some remainder
`N`, as an earlier draft of `(eq:cancellation-computation)` displayed.  Comparing
with `transverse_flow_identity` forces

  `4·T1 = T2 + T3 − N`,

i.e. **four times the principal term** would have to be expressible through the
remainder.  Since `T1` is the term the cubic correction exists in order to
cancel, this is not available. -/
theorem paper_identity_forces (I a₁ a₂ a₃ b₁ b₂ b₃ N : R)
    (ha : a₁ + a₂ + a₃ = 0) (hb : b₁ + b₂ + b₃ = 0)
    (hpaper : Lsym I a₁ b₁ + Lsym I a₂ b₂ + Lsym I a₃ b₃
                = 2 * T1 I b₁ b₂ a₃ + N) :
    4 * T1 I b₁ b₂ a₃ = T2 I a₁ b₂ + T3 I b₁ a₂ - N := by
  have h := transverse_flow_identity I a₁ a₂ a₃ b₁ b₂ b₃ ha hb
  rw [hpaper] at h
  linear_combination h

/-- The conclusion of `paper_identity_forces` is not vacuous: over a field the
principal symbol `T1` is nonzero for any admissible frequency triple with
`b₁, b₂, a₃ ≠ 0`, which is the generic situation in the low–high interaction the
correction is designed for (`b₁ ≠ 0` is precisely the transverse derivative on
the low factor). -/
theorem T1_ne_zero {K : Type*} [Field K] (I b₁ b₂ a₃ : K)
    (hI : I ≠ 0) (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0) (h₃ : a₃ ≠ 0) :
    T1 I b₁ b₂ a₃ ≠ 0 := by
  unfold T1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hI h₁) (mul_ne_zero hI h₂))
    (mul_ne_zero hI h₃)

/-- **The identity the manuscript uses.**  With the cubic correction in
`(eq:localized-functional)` taken with a minus sign, the principal term appears
with coefficient `+2` and cancels `(eq:bad-sm)` exactly.

Note that renormalizing `Π_H` by `−1` would *not* achieve this: the symbol
`e_{3,H}` is fixed by the Littlewood--Paley expansion `(eq:LP-Taylor)` and
appears in `(eq:bad-sm)` as well as in the correction, so flipping it flips both
and leaves their relative sign unchanged.  The explicit sign in
`(eq:localized-functional)` is the only available repair — this is
`rem:correction-sign` of the manuscript. -/
theorem transverse_flow_identity_negated (I a₁ a₂ a₃ b₁ b₂ b₃ : R)
    (ha : a₁ + a₂ + a₃ = 0) (hb : b₁ + b₂ + b₃ = 0) :
    -(Lsym I a₁ b₁ + Lsym I a₂ b₂ + Lsym I a₃ b₃)
      = 2 * T1 I b₁ b₂ a₃ - T2 I a₁ b₂ - T3 I b₁ a₂ := by
  have h := transverse_flow_identity I a₁ a₂ a₃ b₁ b₂ b₃ ha hb
  linear_combination -h

/-! ## The unlisted residual term

The paper's description of the collected remainder `𝒩` is:

  "the terms in which at least one `∂_y` and the `∂_x` act on the same
   frequency-localized factor, together with the terms in which the `∂_x` has
   been moved onto `b`".

`T2 = Π(∂_x v, ∂_y² z_{∼H})z_H` is listed separately and estimated (it is the
"Taylor-remainder term").  But `T3 = Π(∂_y² v, ∂_x z_{∼H})z_H` has its two `∂_y`
on the low factor `v` and its `∂_x` on a *different* factor, so it matches
neither clause of the description, and it does not appear among the terms
estimated in the proof.

It is nevertheless produced by the expansion, unconditionally:
-/

/-- The residual `T3` is genuinely present: the identity fails without it. -/
theorem residual_term_unlisted (I a₁ a₂ a₃ b₁ b₂ b₃ : R)
    (ha : a₁ + a₂ + a₃ = 0) (hb : b₁ + b₂ + b₃ = 0) :
    Lsym I a₁ b₁ + Lsym I a₂ b₂ + Lsym I a₃ b₃
        - ((-2) * T1 I b₁ b₂ a₃ + T2 I a₁ b₂) = T3 I b₁ a₂ := by
  have h := transverse_flow_identity I a₁ a₂ a₃ b₁ b₂ b₃ ha hb
  linear_combination h

/-- `T3` does not vanish identically, so it cannot simply be dropped. -/
theorem T3_ne_zero {K : Type*} [Field K] (I b₁ a₂ : K)
    (hI : I ≠ 0) (h₁ : b₁ ≠ 0) (h₂ : a₂ ≠ 0) : T3 I b₁ a₂ ≠ 0 := by
  unfold T3
  exact mul_ne_zero (pow_ne_zero 2 (mul_ne_zero hI h₁)) (mul_ne_zero hI h₂)

end DGBOZK.Cancellation
