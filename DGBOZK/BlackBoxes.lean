/-
# The black boxes

This library follows Terence Tao's strategy of **partial, conditional
formalization**: formalize a key calculation completely, while accepting all
other cited lemmas and standard results as black boxes.  This raises confidence
in a paper's correctness when the black boxes are all *standard* and the key
calculation is *sensitive to sign and exponent errors*.

The discipline only works if the black boxes are named and their statements
written down.  This file does that.  It contains **no axioms** — every black box
is discharged in one of two ways:

* **as a hypothesis**, so it appears in the statement of every theorem that uses
  it (`[BB-TAYLOR]`, `[BB-HESS]`); or
* **as a definition** matching a formula the paper displays, so that the
  formula is what the library is *about* rather than something it proves
  (`[BB-DIFF]`).

Consequently `#print axioms` on every theorem in this library returns only the
three axioms of Lean's own logic (`propext`, `Classical.choice`, `Quot.sound`).
`DGBOZK/Audit.lean` checks this.  Nothing is assumed silently.

--------------------------------------------------------------------------------

## `[BB-DIFF]` — elementary differentiation

**Where:** `DGBOZK/Phase.lean`, `DGBOZK/Fold.lean`.

**What:** the first- and second-order partial derivatives of
`ω_σ(ξ,η) = ξ(η² + σ|ξ|^α)` on the half-plane `ξ > 0`, and the second and third
derivatives of the reduced phase `Ψ(ξ) = xξ + tξ^{α+1} − y²/(4tξ)`:

  `∂_ξω_σ = σ(α+1)ξ^α + η²`,   `∂_ηω_σ = 2ξη`,
  `∂²_ξω_σ = σα(α+1)ξ^{α−1}`,  `∂_ξ∂_ηω_σ = 2η`,   `∂²_ηω_σ = 2ξ`,
  `Ψ''  = tα(α+1)ξ^{α−1} − y²/(2tξ³)`,
  `Ψ''' = tα(α+1)(α−1)ξ^{α−2} + 3y²/(2tξ⁴)`.

**Why it is a legitimate black box:** these are one-line applications of the
power rule.  They are *standard*.  Sign errors in a paper do not live here; they
live in the substitution and comparison steps that follow, which is what this
library proves.

**Why it is black-boxed rather than proved:** the derivative theory of
`Real.rpow` (`Mathlib.Analysis.SpecialFunctions.Pow.Deriv`) transitively
requires essentially all of Mathlib, which this repository's CI budget does not
allow to build from source.  A `Mathlib`-cached environment can discharge it;
see `DGBOZK/Optional/Differentiation.lean` for the intended statements.

**Partial check performed anyway:** `Phase.hessDet_eq_det` verifies that the
displayed determinant `2σα(α+1)ξ^α − 4η²` really is
`∂²_ξω · ∂²_ηω − (∂_ξ∂_ηω)²` computed from the displayed second derivatives.
This is a genuine consistency check: it exercises `ξ^{α−1}·ξ = ξ^α`, the one
place the exponent could be off by one.

--------------------------------------------------------------------------------

## `[BB-TAYLOR]` — Taylor expansion of the resonance function

**Where:** `DGBOZK/Resonance.lean`, hypothesis `hTaylor`.

**What:** `(eq:Omega-taylor)`,
`Ω(θ,ζ) = ω_-(θ) − ∂_ξω_-(ζ)a − ∂_ηω_-(ζ)b − R`, valid because the segment
`[ζ, ζ+θ]` stays in a fixed conic neighbourhood of `ζ` on which `ξ` does not
change sign and `ω_-` is smooth.

**Why standard:** second-order Taylor with integral remainder.

--------------------------------------------------------------------------------

## `[BB-HESS]` — size of the Taylor remainder

**Where:** `DGBOZK/Resonance.lean`, hypothesis `hR`.

**What:** `|R| ≤ N^{α−1}a² + N^{α/2}|a||b| + Nb²`, from the Hessian bounds
`|∂²_ξω_-| ≲ N^{α−1}`, `|∂_ξ∂_ηω_-| ≲ N^{α/2}`, `|∂²_ηω_-| ≲ N` on the segment.

**Why standard:** direct evaluation of `[BB-DIFF]` on the transition band.

--------------------------------------------------------------------------------

## `[BB-MULT]` — the bilinear multiplier structure

**Where:** `DGBOZK/Cancellation.lean`, built into the symbol calculus.

**What:** two facts the paper states explicitly:

* `Π_H` is a bilinear Fourier multiplier in its two arguments jointly, with
  symbol `e_{3,H}(θ₁,θ₂)`; hence the Leibniz rule
  `∂_yΠ(f,g) = Π(∂_yf,g) + Π(f,∂_yg)` and the fact that `e_{3,H}` is a common
  factor of every term in the identity;
* the integral of a product of three frequency-localized factors is supported on
  `θ₁ + θ₂ + θ₃ = 0`, and integration by parts in `y` produces no boundary term
  and does not meet `b`, which depends on `x` alone.

**Why standard:** these are the defining properties of a bilinear multiplier and
Plancherel.  The paper displays both.

**What is *not* black-boxed:** the resulting algebraic identity, which is the
sign-sensitive step and is proved in full.

--------------------------------------------------------------------------------

## What is deliberately **not** attempted

The genuinely hard analysis of the paper is out of scope and is *not* claimed:
the van der Corput / stationary-phase kernel bounds (`prop:ell-kernel`,
`prop:hyp-kernel`, `prop:majorants`), the abstract `TT*` block estimate
(`lem:abstract`) and the block exponents, the mixed maximal function estimates
(`prop:ell-max`, `prop:hyp-max`), the anisotropic Coifman–Meyer bounds
`(eq:Pi-bounds)`, `(eq:Pi-weighted)`, sharp Gårding, the Bernstein and algebra
properties of `E^r_α`, the compactness construction, and the Bona–Smith
continuity argument.

This library therefore does **not** verify the paper.  It verifies the exponent
bookkeeping and the sign-sensitive algebra on which the paper's stated theorems
depend, conditionally on that standard machinery — which is exactly the claim
the Tao strategy licenses, and no more.
-/

namespace DGBOZK.BlackBoxes

/-- A marker with no content, so that the module is non-empty and importable. -/
def documentation : Unit := ()

end DGBOZK.BlackBoxes
