/-
# Trust boundary for the cleaned manuscript

This library is a targeted consistency formalization. It checks selected
sign-sensitive, polynomial, exponent-sensitive, and finite-dimensional
closure arguments. It does not formalize or prove the local-well-posedness
theorem.

The default target covers:

* exact exponent and threshold arithmetic;
* selected algebraic consequences of the displayed phase formulas;
* the fold and velocity scalar calculations;
* the polynomial Fourier-symbol identity behind the localized cubic
  cancellation;
* the scalar defocusing parameter and bootstrap calculations;
* the focusing threshold and intermediate-parameter arithmetic;
* finite frequency-envelope algebra, construction of the maximizing block,
  and passage of an envelope bound to a pointwise limit under explicit
  convergence hypotheses;
* exact transverse-resonance identities, sector reductions, component
  estimates, and the final algebraic lower-bound deduction;
* the sign-sensitive algebra in the localized positive commutator;
* the two-component parametrix numerator and reconstruction identity; and
* the scalar positivity and absorption consequences used after the analytic
  estimates have been established.

## Displayed derivatives

In `Phase.lean` and `Fold.lean`, several derivative formulas are definitions
matching the manuscript. Downstream theorems validate consequences of those
formulas but do not prove that they are derivatives of the original phase.
The Hessian determinant identity is proved from the displayed Hessian entries.

## Localized cubic cancellation

`Cancellation.lean` uses a finite-dimensional Fourier-symbol model. It checks
the sign of the principal cubic cancellation and the presence of every
polynomial residual term. It does not construct the bilinear multiplier,
prove weighted operator estimates, justify integration by parts, or control
the terms carrying derivatives of the spatial weight.

## Supplementary resonance files

The `ResonanceTransverse*` modules encode algebra from an earlier
resonance-divisor route. The cleaned target manuscript contains no
transverse-resonance lemma or reciprocal-resonance multiplier argument.
These modules are retained only as supplementary experiments and are not
imported by the default target or included in its integrated axiom audit.

## Positive commutator

`PositiveCommutatorCore.lean` checks:

* the Fourier-symbol identity behind
  `[partial_x partial_y^2,b] = b' partial_y^2`;
* the two negative signs arising from
  `- [L_+^{long},b]` with `L_+^{long}=-Op(ell)`;
* the positive sign produced by the exact phase-difference factorization;
* the two-component parametrix numerator and reconstruction identities;
* nonnegativity of the principal quadratic density; and
* the final scalar absorption step.

It does not prove the Wiener-algebra estimate `eq:D-wiener`, the
continuous-shift covering, weighted multiplier estimates, Fourier inversion
of the error kernel, or the integrations by parts. The separate file
`WIENER_PHASE_AUDIT.md` records the mathematical audit of these analytic
interfaces.

## Frequency envelopes

The finite envelope calculation, the maximizing-block argument, and the
order-theoretic passage of a pointwise estimate to a limit are formalized.

The frequency-resolved nonlinear PDE energy inequality, existence of the
required convergent approximation sequence, and identification of its limit
with the constructed solution remain analytic inputs.

## Supplementary transverse-resonance route

The `ResonanceTransverse*`, `FractionalPhase*`,
`FractionalPowerSumCore`, `ResonanceMuScale`, and
`ResonanceLongitudinal*` modules form a supplementary audit of an
earlier transverse-resonance route. They are intentionally not imported
by the default `DGBOZK` target because the identified cleaned manuscript
does not contain `lem:resonance-transverse`.

Within this supplementary route, Lean proves:

* the exact transverse-resonance expansion and polynomial component
  estimates;
* the derivative and global secant estimate for
  `x * |x| ^ alpha`;
* the universal fractional longitudinal increment estimate;
* conversion of `N ^ (alpha / 2) <= Cmu * mu` and
  `C1 * mu <= |b|` into longitudinal control by `N * b ^ 2`; and
* the final transverse-resonance lower bound without an independent
  `hLong` hypothesis.

The reciprocal-resonance multiplier, all-order symbol estimates,
Marcinkiewicz bounds, and associated operator estimates remain outside
Lean.

## Exact trilinear cancellation

`TrilinearCancellationCore.lean` proves the identity labeled
`lem:trilinear` and `eq:trilinear-master` from the two abstract
slot-differentiation identities and commutation of the Cartesian
derivatives. The proof is exact algebra over a commutative ring.


`TrilinearDifferentiationCore.lean` derives the two slot-differentiation
identities from abstract multiplier Leibniz rules, additivity of the weighted
pairing, and weighted integration-by-parts laws. Their realization by the
actual Fourier multiplier and spatial integral remains analytic input.

The module does not construct the bilinear Fourier multiplier, justify the
integrations by parts, or prove estimates for the resulting trilinear terms.

## Scalar anisotropic gauge

The `Gauge*Core` modules formalize the positive-root construction of the
anisotropic gauge for `1 <= alpha <= 2`. They prove:

* existence and uniqueness of the positive root away from the origin;
* construction of a globally defined gauge, with value zero at the origin;
* positivity and the defining equation away from the origin;
* the exact comparison

    `(1 / 2) * (|xi|^alpha + eta^2) <= rho <= |xi|^alpha + eta^2`;

* evenness in each frequency coordinate;
* the exact values on the two coordinate axes; and
* anisotropic homogeneity under the manuscript's frequency scaling.

The selected gauge uses classical choice applied to the proved unique positive
root. Smoothness away from the origin, implicit differentiation, explicit
derivative formulas, and uniform all-orders symbol estimates are not yet
formalized.

## Analysis not formalized

The following parts of the cleaned manuscript remain outside Lean:

* anisotropic Littlewood--Paley theory beyond preliminary convention files;
* oscillatory-integral and van der Corput estimates;
* the TT-star argument and mixed maximal-function estimates;
* bilinear multiplier and weighted paraproduct estimates;
* the analytic Wiener estimates used in the positive commutator;
* weighted positive-commutator, sharp-Garding, and coercivity estimates;
* the direct focusing transition estimate;
* refined short-time Strichartz and microlocal smoothing estimates;
* the frequency-resolved nonlinear energy inequality itself;
* construction and compactness of approximate solutions;
* uniqueness and Bona--Smith continuity; and
* all-order Marcinkiewicz estimates for reciprocal resonance symbols.

`FocusingThreshold.lean` proves only the parameter arithmetic that follows
once the direct transition estimate is available. `EnergyEnvelope.lean` and
the `FrequencyEnvelope*` modules prove the discrete and limiting closure
steps only after the analytic block-energy system and convergence hypotheses
have been supplied.

There are no project-level axioms in this file. Successful compilation is
evidence only for the encoded declarations, never for the omitted analysis.
-/

namespace DGBOZK.BlackBoxes

set_option autoImplicit false

/-- A content-free marker making this documentation module importable. -/
def documentation : Unit := ()

end DGBOZK.BlackBoxes
