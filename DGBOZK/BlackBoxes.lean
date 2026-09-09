/-
# Trust boundary for the cleaned manuscript

This library is a targeted consistency formalization.  It checks selected
sign-sensitive, polynomial, and exponent-sensitive calculations.  It does not
formalize or prove the local-well-posedness theorem.

The current default target covers:

* exact exponent and threshold arithmetic;
* selected algebraic consequences of the displayed phase formulas;
* the fold and velocity scalar calculations;
* the polynomial Fourier-symbol identity behind the localized cancellation;
* the scalar defocusing parameter and bootstrap calculations;
* the focusing threshold and intermediate-parameter arithmetic in the cleaned
  manuscript; and
* the final scalar absorption consequence of a quadratic frequency-envelope
  inequality.

## Displayed derivatives

In Phase.lean and Fold.lean, several derivative formulas are definitions
matching the manuscript.  Downstream theorems validate consequences of those
formulas but do not prove that they are derivatives of the original phase.
The Hessian determinant identity is proved from the displayed Hessian entries.

## Multiplier model

Cancellation.lean uses a finite-dimensional symbol model.  It verifies the
sign-sensitive polynomial identity.  It does not construct the bilinear
multiplier, prove weighted operator bounds, justify integrations by parts, or
control terms carrying derivatives of the weight.

## Legacy resonance file

Resonance.lean is retained as a supplementary audit of an earlier normal-form
draft.  It is not imported by the default DGBOZK target and does not validate
the cleaned manuscript, which no longer uses that argument.  Its Taylor
identity and Hessian remainder are explicit hypotheses, not derived results.

## Analysis not formalized

The following parts of the cleaned manuscript remain outside Lean:

* anisotropic Littlewood--Paley theory beyond the preliminary convention files;
* oscillatory-integral and van der Corput estimates;
* the TT-star argument and mixed maximal-function estimates;
* bilinear multiplier and weighted paraproduct estimates;
* the positive-commutator and direct focusing transition estimates, including
  every term containing a derivative of the weight;
* sharp Garding and coercivity;
* refined short-time Strichartz and microlocal smoothing estimates;
* the frequency-resolved nonlinear energy inequality itself;
* construction, compactness, uniqueness, frequency-envelope propagation, and
  Bona--Smith continuity.

FocusingThreshold.lean proves only the parameter arithmetic that follows once
the direct transition estimate is available.  EnergyEnvelope.lean proves only
the final scalar absorption step once the nonlinear envelope inequality has
been established analytically.

There are no project-level axioms in this file.  Successful compilation is
evidence only for the encoded declarations, never for the omitted analysis.
-/

namespace DGBOZK.BlackBoxes

set_option autoImplicit false

/-- A content-free marker making this documentation module importable. -/
def documentation : Unit := ()

end DGBOZK.BlackBoxes
