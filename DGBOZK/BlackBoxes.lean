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

## Verified phase differentiation

The first- and second-order derivatives displayed in `Phase.lean` are no
longer part of the analytic trust boundary.

`PhaseTransverseDifferentiationCore.lean` proves:

* the transverse derivative of `omega`;
* the transverse derivative of `velX`;
* the transverse derivative of `velY`;
* the longitudinal derivative of `velY`; and
* equality of the two verified mixed derivative values.

`PhaseLongitudinalDifferentiationCore.lean` proves:

* the global longitudinal derivative of `omega` for `alpha > 0`;
* its identification with `velX` on the half-plane `xi > 0`; and
* the identification of the longitudinal derivative of `velX` with `hessXX`.

Thus all gradient and Hessian entries used by the phase-geometry calculation
are genuine Lean derivative theorems. The Hessian determinant identity is
proved algebraically from those entries.

`FoldDifferentiationCore.lean` additionally proves the genuine derivative
chain from the reduced phase `Psi` through `Psi1`, `Psi2`, and `Psi3` on
`xi > 0` and `t != 0`. Thus the elementary phase and reduced-fold
differentiation formulas no longer belong to the analytic trust boundary.

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
root. `GaugeImplicitCore.lean` proves that the radial implicit denominator
belongs to `[1,2]`, that the radial derivative of the defining residual is
strictly negative, and that the formal differentiated equations imply the
displayed first-order derivative formulas.

The module does not prove that the choice-defined gauge is differentiable.
Smoothness away from the origin, a formal implicit-function-theorem
application, realization of the structural derivative hypotheses, and uniform
all-orders symbol estimates remain outside Lean.

## Fourier foundations

The registered `Foundations` modules formalize:

* the physical and frequency coordinate spaces;
* the manuscript Fourier phase and normalization conventions;
* anisotropic low-frequency regions and dyadic annuli;
* coordinate bounds implied by membership in those regions;
* an abstract smooth scalar cutoff profile;
* low-pass and band-pass symbols and their support identities;
* the finite telescoping identity for dyadic bands;
* construction of a canonical scalar profile from
  `Real.smoothTransition`; and
* Fourier inversion for Schwartz functions in the manuscript convention,
  including the two-dimensional `(2 * pi) ^ (-2)` normalization.

These modules do not prove global smoothness of every fractional anisotropic
symbol at `xi = 0`, infinite Littlewood--Paley convergence, multiplier
boundedness, square-function norm equivalence, or inversion for general
`L1`, `L2`, or tempered-distribution data.

## Fourier multipliers and dyadic projectors

`L2MultiplierCore.lean` proves the pointwise bounded-multiplier estimate,
preservation of `MemLp`, the corresponding `eLpNorm` inequality, and an
abstract norm-conjugation theorem.

`DyadicProjectorL2Core.lean` applies this theory to the constructed
anisotropic dyadic band symbols. It proves their uniform norm bound, annular
support, frequency-side `L2` contraction, and transport of a contractive
frequency multiplier through explicitly supplied norm-preserving forward and
inverse transforms.

The concrete Euclidean Plancherel realization of those transforms is not
available in the pinned Mathlib and remains outside the machine-checked
artifact. Accordingly, the physical-space projector theorem is conditional on
the stated norm-preservation hypotheses.

## Dyadic separation and finite overlap

The dyadic-foundation modules now prove the exact scalar support combinatorics
behind finite overlap:

* dyadic bands whose indices differ by at least three cannot be simultaneously
  active at the same frequency;
* every band interacting with a fixed band of index `k` has index within two
  steps of `k`;
* a finite dyadic interaction sum can be restricted exactly to those nearby
  indices; and
* at most five indices in any finite family can interact with a fixed dyadic
  band.

These are pointwise support and finite-sum statements. They do not prove a
Littlewood--Paley square-function equivalence, vector-valued multiplier
estimate, weighted almost orthogonality, product-frequency convolution bound,
or nonlinear paraproduct estimate.

## Quantitative dyadic interaction bound

`DyadicFiniteSumBoundCore.lean` converts a cardinality bound of five into
the explicit estimate that a finite sum of uniformly bounded absolute-valued
contributions is at most five times the common bound.

`DyadicInteractionBoundCore.lean` applies this result to the dyadic band
symbols and proves

  `sum_j |psi_k(zeta) psi_j(zeta)| <= 5`

over every finite index family. The proof uses the unit symbol bound and the
exact five-index interaction window.

This is a pointwise scalar estimate. It does not establish an `L2`
square-function equivalence, Cotlar--Stein almost orthogonality, a weighted
operator estimate, or a nonlinear paraproduct bound.

## Finite dyadic family norm bridge

`DyadicFiniteFamilyNormCore.lean` lifts the five-index cardinality estimate
from scalar sums to families in an arbitrary seminormed additive commutative
group. It proves that a sum of at most five vectors, each having norm bounded
by `B`, has norm at most `5 * B`.

The theorem is specialized both to the near-index filter and to the actual
active dyadic-index filter. It can therefore be instantiated with vectors in
an `L2` space once the relevant Fourier multiplier outputs have been
constructed.

The module does not construct those multiplier outputs, prove a
Littlewood--Paley square-function equivalence, establish Hilbert-space
orthogonality, or invoke the Cotlar--Stein lemma.

## Analysis not formalized

The following parts of the cleaned manuscript remain outside Lean:

* analytic anisotropic Littlewood--Paley multiplier bounds, infinite decompositions, and norm equivalences;
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
