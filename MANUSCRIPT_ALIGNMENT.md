# Cleaned-manuscript alignment

Target manuscript:

    dgbozk_nonlinear_analysis_clean.tex
    SHA-256 9a0920d31a4ce57d8d78dc046b727ac27b892ae8fbe4c82de60b0b70c7e2b1a0

## Scope

This document aligns the principal arguments of the cleaned manuscript with the
Lean declarations registered by `DGBOZK.lean`. “Checked” means that the stated
algebraic, scalar, finite-dimensional, or order-theoretic assertion is proved
in Lean. “Conditional” means that Lean proves the conclusion from explicit
analytic or convergence hypotheses. Successful compilation is not a formal
proof of the local-well-posedness theorem.

## Alignment table

| Manuscript component | Representative Lean declarations | Status and exact scope |
|---|---|---|
| Phase geometry | `exchange_of_degeneracies`, `hessDet_eq_det`, `velX_defocusing_pos`, `hessDet_focusing_neg` | **Checked.** Displayed derivative formulas are encoded as definitions; Lean checks their consequences, not differentiation of the original phase. |
| Fold calculation | `Psi2_eq_hessDet`, `Psi3_on_gamma_plus`, `Psi3_ne_zero_on_gamma_plus`, `Psi3_lower_bound` | **Checked** from the encoded formulas and stated side conditions. Oscillatory-integral estimates remain outside Lean. |
| Focusing velocity | `velocity_lower_bound`, `velocity_sharp` | **Checked** as scalar frequency calculations. |
| Exponents and thresholds | `R1_sub_R0`, `R1_sub_Kfold`, `Kfold_lt_R1`, `rPlus_lt_rRV`, `lifespanExp_one`, `scalingExp_rCrit`, `algebra_margin_on_range` | **Checked.** This does not formalize the PDE scaling map or lifespan construction. |
| Localized cubic cancellation | `Cancellation.flow_symbol_identity`, `Cancellation.transverse_flow_identity`, `Cancellation.paper_identity_forces`, `Cancellation.residual_term_unlisted` | **Checked** in a commutative-ring Fourier-symbol model. Multiplier bounds, integrations by parts, and weighted estimates remain outside Lean. |
| Positive-commutator signs | `PositiveCommutatorCore.transverse_commutator_symbol`, `PositiveCommutatorCore.longitudinal_double_negative`, `PositiveCommutatorCore.longitudinal_commutator_kernel_sign` | **Checked.** |
| Two-component parametrix algebra | `PositiveCommutatorCore.parametrix_numerator_identity`, `PositiveCommutatorCore.two_component_parametrix_identity` | **Checked** from an explicit inverse-symbol hypothesis. |
| Positive density and absorption | `PositiveCommutatorCore.positive_density_nonneg`, `PositiveCommutatorCore.absorb_half_of_positive_form` | **Checked.** |
| `lem:wiener-phase` and `eq:D-wiener` | — | **Analytically audited, not machine-checked.** See `WIENER_PHASE_AUDIT.md`. |
| Full `lem:positive-comm` | — | **Outside Lean.** Weighted multiplier estimates, Fourier-kernel reconstruction, continuous-shift covering, and integrations by parts remain analytic inputs. |
| Focusing threshold arithmetic | `sMinus_eq`, `direct_commutator_gap_iff`, `exists_admissible_tau_iff`, `exists_refined_epsilon`, `focusing_parameter_package` | **Checked.** The direct focusing transition estimate itself remains outside Lean. |
| Frequency-envelope algebra | `FrequencyEnvelope.envelopeSq_nonneg`, `FrequencyEnvelope.envelopeSq_slowVariation`, `FrequencyEnvelope.sum_envelopeSq_le` | **Checked.** |
| Finite envelope propagation | `FrequencyEnvelope.finite_envelope_propagation`, `FrequencyEnvelope.finite_envelope_propagation_from_system` | **Conditional.** The finite block-energy system is an explicit hypothesis. |
| Passage to a pointwise limit | `FrequencyEnvelope.bound_passes_to_pointwise_limit`, `FrequencyEnvelope.finite_to_limit_envelope_propagation` | **Conditional.** The required convergence is an explicit hypothesis. |
| Scalar closure and bootstrap | `quadratic_envelope_closure`, `envelope_decay_margin`, `bootstrap_closure`, `exists_eps_defocusing`, `coupled_admissible_defocusing` | **Checked.** |
| Nonlinear energy estimate, construction, uniqueness, and continuity | — | **Outside Lean.** |

## Main results

| Manuscript result | Formalization status |
|---|---|
| Mixed maximal-function theorem (`thm:intro-maximal`) | **Outside Lean.** Only selected phase, fold, velocity, and exponent calculations are checked. |
| Localized positive commutator (`lem:positive-comm`) | **Partially checked and analytically audited.** The sign-sensitive algebra is formalized; the operator estimates are not. |
| Main local-well-posedness theorem (`thm:main`) | **Outside Lean.** |

## Verified phase differentiation

| Manuscript assertion | Lean declaration | Status |
|---|---|---|
| `partial_eta omega_sigma = 2 xi eta` | `PhaseTransverseDifferentiationCore.hasDerivAt_omega_eta` | **Checked as a genuine derivative.** |
| `partial_xi omega_sigma = eta^2 + sigma (alpha+1)|xi|^alpha` | `PhaseLongitudinalDifferentiationCore.hasDerivAt_omega_xi_abs` | **Checked globally for `alpha > 0`.** |
| Positive-half-plane longitudinal velocity | `PhaseLongitudinalDifferentiationCore.hasDerivAt_omega_xi_of_pos` | **Checked.** The derivative is exactly `velX` when `xi > 0`. |
| `partial_xi velX = hessXX` | `PhaseLongitudinalDifferentiationCore.hasDerivAt_velX_xi_of_pos` | **Checked for `xi > 0`.** |
| `partial_eta velX = hessXY` | `PhaseTransverseDifferentiationCore.hasDerivAt_velX_eta` | **Checked.** |
| `partial_xi velY = hessXY` | `PhaseTransverseDifferentiationCore.hasDerivAt_velY_xi` | **Checked.** |
| `partial_eta velY = hessYY` | `PhaseTransverseDifferentiationCore.hasDerivAt_velY_eta` | **Checked.** |
| Equality of the mixed derivatives | `PhaseTransverseDifferentiationCore.verified_mixed_derivatives_agree` | **Checked.** |

The phase gradient and Hessian formulas are therefore no longer merely
displayed definitions. This checkpoint does not automatically formalize
separate derivative assertions appearing in `Fold.lean`.

## Verified reduced-fold differentiation

| Manuscript assertion | Lean declaration | Status |
|---|---|---|
| First reduced-phase derivative | `FoldDifferentiationCore.hasDerivAt_Psi` | **Checked for `xi > 0` and `t != 0`.** |
| `Psi'' = Psi2` | `FoldDifferentiationCore.hasDerivAt_Psi1` | **Checked as the second derivative step.** |
| `Psi''' = Psi3` | `FoldDifferentiationCore.hasDerivAt_Psi2` | **Checked as the third derivative step.** |
| Lean derivative identities | `deriv_Psi_eq_Psi1`, `deriv_Psi1_eq_Psi2`, `deriv_Psi2_eq_Psi3` | **Checked.** |
| Fold substitution and nondegeneracy | declarations in `Fold.lean` | **Previously checked algebraically; now based on verified derivatives.** |

This closes the elementary differentiation input formerly labeled
`[BB-DIFF]`. It does not formalize the subsequent oscillatory-integral
or van der Corput estimates.

## Fourier foundations

The relevant modules under `DGBOZK/Foundations` are now imported transitively
by `DGBOZK.lean` through `SmoothCutoffConstruction` and `FourierInversion`.
They are part of the passing default target and integrated axiom audit.

| Manuscript component | Lean declaration | Status |
|---|---|---|
| anisotropic frequency size | `Foundations.anisotropicSymbol` | Encoded from `|xi|^alpha + eta^2`. |
| low-frequency region and dyadic annulus | `Foundations.lowFrequencyRegion`, `Foundations.dyadicAnnulus` | **Checked.** |
| coordinate control on an annulus | `Foundations.xiPower_le_of_mem_dyadicAnnulus`, `etaSq_le_of_mem_dyadicAnnulus` | **Checked.** |
| abstract scalar cutoff | `Foundations.SmoothCutoffProfile` | Encodes smoothness, support, and range requirements. |
| finite dyadic telescoping | `Foundations.sum_dyadicBandSymbol` | **Checked.** |
| canonical decreasing cutoff | `Foundations.standardSmoothCutoffProfile` | Constructed from Mathlib's `Real.smoothTransition`. |
| band support localization | `Foundations.standardBandPassActiveSet_subset_dyadicAnnulus` | **Checked.** |
| manuscript-normalized Schwartz inversion | `Foundations.normalized_paperFourier_inversion` | **Checked.** Includes the two-dimensional Fourier normalization. |

The artifact does not claim analytic multiplier boundedness, infinite
Littlewood--Paley convergence, square-function norm equivalence, or Fourier
inversion outside the stated Schwartz-function interface.

## Verified integration checkpoint

At this checkpoint:

- `lake build DGBOZK` succeeds;
- `lake env lean DGBOZK/Audit.lean` succeeds;
- the integrated audit reports no dependency on `sorryAx`; and
- the default root imports the positive-commutator and frequency-envelope
  limiting modules relevant to the cleaned manuscript.

These facts certify only the registered declarations. They must not be
described as a complete machine-checked proof of the manuscript.

## Supplementary resonance files

The files `DGBOZK/ResonanceTransverse*.lean` encode algebra from an earlier
resonance-divisor route. The target manuscript identified above contains no
`lem:resonance-transverse`, no reciprocal-resonance divisor, and no associated
Marcinkiewicz argument. These modules may be retained as supplementary
experiments, but they are not part of the cleaned-manuscript alignment and must
not be imported by the default `DGBOZK` target or its integrated axiom audit.

## Supplementary transverse-resonance formalization

The target cleaned manuscript does not contain
`lem:resonance-transverse`. Accordingly, the transverse-resonance
modules are not part of the default manuscript-alignment target.

They instead provide a supplementary audit of an earlier auxiliary
route. The corrected final theorem is

`DGBOZK.ResonanceTransverse.resonance_transverse_sector_conclusion_from_mu_scale`.

Unlike the earlier conditional interface, this theorem does not assume
`hLong`. It derives the longitudinal estimate from

\[
1\leq\alpha\leq2,\qquad
|\xi|\leq c_+N,\qquad
|a|\leq\varepsilon N,\qquad
N^{\alpha/2}\leq C_\mu\mu,\qquad
C_1\mu\leq |b|.
\]

Thus the missing relation identified during the audit is explicit in
the formal theorem statement.

## Exact trilinear cancellation

| Manuscript location | Lean declaration | Status |
|---|---|---|
| `lem:trilinear`, `eq:trilinear-master` | `TrilinearCancellationCore.exact_trilinear_cancellation` | **Checked conditionally.** The master identity follows exactly from the two slot-differentiation identities and commuting derivatives. Construction of the multiplier and analytic integration by parts remain outside this theorem. |

## Structural trilinear differentiation

| Manuscript location | Lean declaration | Status |
|---|---|---|
| `eq:delta-identities` | `TrilinearDifferentiationCore.transverse_slot_identity` | **Conditionally checked.** Derived from the transverse multiplier Leibniz rule and weighted integration by parts. |
| `eq:delta-identities` | `TrilinearDifferentiationCore.longitudinal_slot_identity` | **Conditionally checked.** Produces exactly the negative weight-derivative functional. |
| `lem:trilinear` | `TrilinearDifferentiationCore.exact_trilinear_cancellation_from_structural_laws` | **Checked from structural laws.** No slot-differentiation identity remains as a direct hypothesis. |

## Scalar anisotropic gauge

| Manuscript location | Lean declaration | Status |
|---|---|---|
| `eq:gauge-def` | `GaugeEquationCore.gaugeEquation` | The positive-root equation is encoded exactly. |
| normalized summands in `lem:gauge` | `GaugeEquationCore.normalized_terms_mem_unit_interval` | **Checked.** |
| coordinate consequences | `GaugeLowerEquivalenceCore.abs_x_rpow_le_rho`, `y_square_le_rho` | **Checked.** |
| lower half of `eq:gauge-equiv` | `GaugeLowerEquivalenceCore.half_energy_le_rho` | **Checked.** |
| upper half of `eq:gauge-equiv` | `GaugeUpperEquivalenceCore.rho_le_energy` | **Checked for `1 <= alpha <= 2`.** |
| complete `eq:gauge-equiv` | `GaugeUpperEquivalenceCore.gauge_energy_equivalence` | **Checked conditionally on a positive solution of `eq:gauge-def`.** |

## Positive gauge-root uniqueness

| Manuscript location | Lean declaration | Status |
|---|---|---|
| uniqueness assertion in `lem:gauge` | `GaugeUniquenessCore.positive_root_unique` | **Checked for `alpha > 0`.** Any two positive solutions of `eq:gauge-def` coincide. |

## Positive gauge-root existence

| Manuscript location | Lean declaration | Status |
|---|---|---|
| existence assertion in `lem:gauge` | `GaugeExistenceCore.exists_positive_gauge_root` | **Checked for `1 <= alpha <= 2` away from the origin.** The root lies in the explicit interval `[E/2,E]`. |
| existence and uniqueness | `GaugeExistenceCore.existsUnique_positive_gauge_root` | **Checked.** This combines the IVT construction with positive-root uniqueness. |

## Constructed anisotropic gauge

| Manuscript location | Lean declaration | Status |
|---|---|---|
| selected gauge in `lem:gauge` | `GaugeFunctionCore.anisotropicGauge` | **Constructed.** It is the unique positive root away from the origin and is defined to be zero at the origin. |
| origin normalization | `GaugeFunctionCore.anisotropicGauge_origin` | **Checked.** |
| positivity away from the origin | `GaugeFunctionCore.anisotropicGauge_pos` | **Checked for `1 <= alpha <= 2`.** |
| `eq:gauge-def` | `GaugeFunctionCore.anisotropicGauge_equation` | **Checked away from the origin.** |
| positive-root characterization | `GaugeFunctionCore.anisotropicGauge_eq_of_positive_solution` | **Checked.** Every positive solution of the defining equation equals the selected gauge. |
| `eq:gauge-equiv` | `GaugeFunctionCore.anisotropicGauge_energy_equivalence` | **Checked for the constructed gauge.** |
| coordinate reflection symmetries | `GaugeSymmetryAxesCore.anisotropicGauge_neg_x`, `anisotropicGauge_neg_y`, `anisotropicGauge_neg_both` | **Checked.** |
| coordinate-axis identities | `GaugeSymmetryAxesCore.anisotropicGauge_zero_x`, `anisotropicGauge_zero_y` | **Checked.** |
| anisotropic scaling identity | `GaugeHomogeneityCore.anisotropicGauge_homogeneous` | **Checked for positive scaling factors.** |

Actual differentiability and smoothness of the choice-defined gauge, the
analytic implicit-function-theorem step, and uniform all-orders symbol
estimates remain outside the current Lean formalization.

## Implicit-gauge nondegeneracy

| Manuscript component | Lean declaration | Status |
|---|---|---|
| radial implicit denominator | `GaugeImplicitCore.gaugeRadialDenominator` | Encoded exactly from the normalized gauge equation. |
| denominator coercivity | `GaugeImplicitCore.gaugeRadialDenominator_mem_Icc` | **Checked.** For `1 <= alpha <= 2`, the denominator lies in `[1,2]`. |
| radial nondegeneracy | `GaugeImplicitCore.gaugeRadialDerivative_neg` | **Checked.** The radial derivative of the defining residual is strictly negative. |
| longitudinal formal derivative formula | `GaugeImplicitCore.longitudinal_implicit_derivative_formula` | **Conditionally checked.** Derived exactly from the corresponding differentiated structural identity. |
| transverse formal derivative formula | `GaugeImplicitCore.transverse_implicit_derivative_formula` | **Conditionally checked.** Derived exactly from the corresponding differentiated structural identity. |
| constructed-gauge denominator bound | `GaugeImplicitCore.anisotropicGauge_radialDenominator_mem_Icc` | **Checked away from the origin.** |
| constructed-gauge radial nondegeneracy | `GaugeImplicitCore.anisotropicGauge_radialDerivative_neg` | **Checked away from the origin.** |

The two derivative formulas are algebraic consequences of differentiated
identities. The present artifact does not claim that the choice-defined gauge
has already been differentiated in Lean.

## L2 multiplier and dyadic-projector foundation

| Manuscript interface | Lean declaration | Status |
|---|---|---|
| bounded frequency multiplier | `L2MultiplierCore.eLpNorm_two_bounded_pointwise_multiplier_le` | **Checked.** A uniformly bounded complex symbol gives the corresponding `eLpNorm` estimate. |
| dyadic cutoff bound | `DyadicProjectorL2Core.complexDyadicBandSymbol_norm_le_one` | **Checked.** The constructed complexified band symbol has norm at most one. |
| dyadic annular localization | `DyadicProjectorL2Core.complexDyadicBandSymbol_active_subset_dyadicAnnulus` | **Checked.** |
| frequency-side dyadic contraction | `DyadicProjectorL2Core.standardDyadicBandMultiplier_eLpNorm_two_le` | **Checked.** |
| physical-space projector contraction | `DyadicProjectorL2Core.conjugatedDyadicProjector_norm_le` | **Conditionally checked.** It assumes norm-preserving forward and inverse transforms. |
| Euclidean Plancherel realization | — | **Outside Lean.** The pinned Mathlib does not presently supply the required Euclidean `L2` Fourier isometry. |

## Dyadic finite-overlap calculus

| Analytic role | Lean declaration | Status |
|---|---|---|
| Separation of dyadic annuli | `DyadicAnnulusSeparationCore.dyadicBandSymbol_mul_eq_zero_of_separated` | **Checked.** Separated bands have zero pointwise symbol product. |
| Separation from an index gap | `DyadicFiniteOverlapCore.dyadicBandSymbol_mul_eq_zero_of_index_separation` | **Checked.** An index separation of at least three forces disjoint activity. |
| Localization of active interactions | `DyadicFiniteOverlapCore.active_dyadic_indices_within_two` | **Checked.** Simultaneously active indices differ by at most two. |
| Restriction of an interaction sum | `DyadicInteractionSumCore.dyadicBand_interaction_sum_eq_near_filter` | **Checked.** A finite interaction sum equals its restriction to nearby indices. |
| Cardinality of nearby indices | `DyadicActiveCardinalityCore.nearDyadicIndexSet_card_le_five` | **Checked.** The nearby-index set has at most five members. |
| Cardinality of active interactions | `DyadicActiveCardinalityCore.active_indices_card_le_five` | **Checked.** At most five indices in a finite family interact with a fixed band. |

This layer formalizes the support combinatorics used before analytic
Littlewood--Paley and paraproduct estimates. It does not establish
square-function norm equivalence, weighted operator estimates, or nonlinear
frequency-interaction bounds.

## Quantitative dyadic interaction estimate

| Analytic role | Lean declaration | Status |
|---|---|---|
| Abstract five-term estimate | `DyadicFiniteSumBoundCore.sum_abs_le_five_mul_of_card_le_five` | **Checked.** A finite family of at most five absolute-valued contributions is bounded by five times their common bound. |
| Pointwise dyadic interaction estimate | `DyadicInteractionBoundCore.dyadicBand_interaction_abs_sum_le_five` | **Checked.** Any finite interaction family has total absolute symbol contribution at most five. |
| Canonical cutoff specialization | `DyadicInteractionBoundCore.standardDyadicBand_interaction_abs_sum_le_five` | **Checked.** The result applies to the constructed standard smooth cutoff profile. |

The estimate is pointwise in frequency. No square-function norm equivalence,
weighted multiplier estimate, or nonlinear paraproduct theorem is claimed.

## Finite-family norm bridge

| Analytic role | Lean declaration | Status |
|---|---|---|
| Abstract norm bound for at most five terms | `DyadicFiniteFamilyNormCore.norm_sum_le_five_mul_of_card_le_five` | **Checked.** Triangle inequality plus the explicit cardinality estimate. |
| Near-index vector-family estimate | `DyadicFiniteFamilyNormCore.norm_near_dyadic_sum_le_five` | **Checked.** |
| Active dyadic vector-family estimate | `DyadicFiniteFamilyNormCore.norm_active_dyadic_sum_le_five` | **Checked.** |
| Canonical-cutoff specialization | `DyadicFiniteFamilyNormCore.norm_standard_active_dyadic_sum_le_five` | **Checked.** |

This is an abstract finite-family norm estimate. Its use with actual Fourier
projectors requires the analytic multiplier realization already identified in
the trust boundary.
