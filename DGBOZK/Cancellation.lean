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

and

  "The displayed principal term of (5.29) is exactly the negative of (5.28), so
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

## The finding

The identity that actually holds carries the principal term with coefficient
**`−2`**, not `+2` as displayed in `(eq:cancellation-computation)`.  See
`transverse_flow_identity` and the discussion in `paper_identity_forces` below.
The discrepancy is a factor `−1` and is traceable to the `i³ = −i` bookkeeping;
it is repaired by flipping the sign of the cubic correction in
`(eq:localized-functional)` (equivalently, by the normalization of `Π_H`, a
freedom the paper explicitly invokes).  With that flip the cancellation is exact
and everything downstream is unaffected.

A second, independent hand derivation agrees: integrating by parts twice in `y`
in the third term of `(eq:cancellation-computation)` and expanding
`∂_y²Π(v,z) = Π(∂_y²v,z) + 2Π(∂_yv,∂_yz) + Π(v,∂_y²z)` produces
`−2 ∫ b Π(∂_yv,∂_yz)∂_x z` directly.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Field.Basic

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

/-- Symbol of `Π(∂_y² v, ∂_x z_{∼H}) · z_H`.  This term is produced by the same
expansion but is **not** among the remainder terms the paper lists; see
`residual_term_unlisted` below. -/
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

The coefficient of the principal term is **`−2`**.  The paper's
`(eq:cancellation-computation)` displays `+2`.

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

/-- **What the paper's displayed identity would force.**  Suppose the transverse
flow derivative equals `+2·T1 + N` for some remainder `N`, as displayed in
`(eq:cancellation-computation)`.  Comparing with `transverse_flow_identity`
forces

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

/-- **The repair.**  If the cubic correction in `(eq:localized-functional)` is
taken with the opposite sign — equivalently if `Π_H` is normalized with an extra
factor `−1`, a freedom the paper explicitly invokes when it says `Π_H` is
"normalized so as to correspond to writing `−uu_x = −½∂_x(u²)`" — then the
principal term appears with coefficient `+2` and cancels `(eq:bad-sm)` exactly,
as claimed.  Formally: negating the whole identity turns `−2` into `+2`. -/
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
