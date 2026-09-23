/-
# Axiom audit

The point of a conditional formalization is that the reader can see exactly what
was assumed.  This file prints the axiom dependencies of every headline result
in the library.

Each result must depend on at most the standard allowlist
`propext`, `Classical.choice`, `Quot.sound`; many algebraic results use a strict
subset or no axioms at all.  `scripts/check_axiom_report.py` checks every
printed declaration against this list and fails CI if a report is missing or
contains another axiom.

Hypotheses such as `hTaylor` and `hR` are inputs to theorem statements, not
axioms, and therefore do not appear in `#print axioms`.  Their mathematical
strength must be assessed by reading the statement as part of the scope audit.

Run with `lake env lean DGBOZK/Audit.lean`.
-/
import DGBOZK

set_option autoImplicit false

open DGBOZK

/-! ## Critical exponent and cancellation proposals -/
#print axioms DGBOZK.ExponentCritical.fold_block_exponent
#print axioms DGBOZK.ExponentCritical.residual_admissible_iff
#print axioms DGBOZK.ConditionalFocusing.inputs_iff
#print axioms DGBOZK.ConditionalFocusing.inputs_with_tau_gt_one_iff
#print axioms DGBOZK.ComposedCancellation.composed_cancellation
#print axioms DGBOZK.ComposedCancellation.wrong_sign_doubles

/-! ## §3  Phase geometry -/
#print axioms DGBOZK.exchange_of_degeneracies
#print axioms DGBOZK.hessDet_eq_det
#print axioms DGBOZK.velX_defocusing_pos
#print axioms DGBOZK.hessDet_focusing_neg
#print axioms DGBOZK.hessDet_focusing_comparable
#print axioms DGBOZK.velX_defocusing_comparable
#print axioms DGBOZK.dHessDetDefocusing_pos

/-! ## §3  The fold -/
#print axioms DGBOZK.Psi2_eq_hessDet
#print axioms DGBOZK.Psi3_substituted
#print axioms DGBOZK.Psi3_on_gamma_plus
#print axioms DGBOZK.Psi3_ne_zero_on_gamma_plus
#print axioms DGBOZK.Psi3_lower_bound

/-! ## §3  The focusing velocity -/
#print axioms DGBOZK.velocity_lower_bound
#print axioms DGBOZK.velocity_sharp

/-! ## §1  Exponents and thresholds -/
#print axioms DGBOZK.R1_sub_R0
#print axioms DGBOZK.R1_sub_Kfold
#print axioms DGBOZK.Kfold_lt_R1
#print axioms DGBOZK.aPlus_delta_two
#print axioms DGBOZK.aPlus_delta_twelveFifths
#print axioms DGBOZK.aMinus_nu_two
#print axioms DGBOZK.bMinus_nu_two
#print axioms DGBOZK.rPlus_sub_rRV
#print axioms DGBOZK.rPlus_lt_rRV
#print axioms DGBOZK.rPlus_lt_half_iff
#print axioms DGBOZK.lifespanExp_one
#print axioms DGBOZK.scalingExp_rCrit
#print axioms DGBOZK.algebra_margin_on_range

/-! ## Cleaned focusing theorem: scalar threshold arithmetic -/
#print axioms DGBOZK.sMinus_eq
#print axioms DGBOZK.sMinus_strictAnti
#print axioms DGBOZK.direct_commutator_gap_iff
#print axioms DGBOZK.exists_admissible_tau_iff
#print axioms DGBOZK.focusing_parameter_package

/-! ## §5  The localized cubic cancellation -/
#print axioms DGBOZK.Cancellation.flow_symbol_identity
#print axioms DGBOZK.Cancellation.transverse_flow_identity
#print axioms DGBOZK.Cancellation.paper_identity_forces
#print axioms DGBOZK.Cancellation.residual_term_unlisted

/-! ## §8–§9  Closure -/
#print axioms DGBOZK.bootstrap_closure
#print axioms DGBOZK.exists_eps_defocusing
#print axioms DGBOZK.coupled_admissible_defocusing
#print axioms DGBOZK.quadratic_envelope_closure
#print axioms DGBOZK.envelope_decay_margin

/-! ## Frequency-envelope calculus -/
#print axioms DGBOZK.FrequencyEnvelope.envelopeSq_nonneg
#print axioms DGBOZK.FrequencyEnvelope.envelopeSq_slowVariation
#print axioms DGBOZK.FrequencyEnvelope.sum_envelopeSq_le
#print axioms DGBOZK.FrequencyEnvelope.finite_envelope_propagation
#print axioms DGBOZK.FrequencyEnvelope.finite_envelope_propagation_from_system

/-! ## Frequency-envelope limiting argument -/
#print axioms DGBOZK.FrequencyEnvelope.bound_passes_to_pointwise_limit
#print axioms DGBOZK.FrequencyEnvelope.finite_to_limit_envelope_propagation

/-! ## Localized positive-commutator algebra -/
#print axioms DGBOZK.PositiveCommutatorCore.transverse_commutator_symbol
#print axioms DGBOZK.PositiveCommutatorCore.longitudinal_double_negative
#print axioms DGBOZK.PositiveCommutatorCore.longitudinal_commutator_kernel_sign
#print axioms DGBOZK.PositiveCommutatorCore.parametrix_numerator_identity
#print axioms DGBOZK.PositiveCommutatorCore.two_component_parametrix_identity
#print axioms DGBOZK.PositiveCommutatorCore.positive_density_nonneg
#print axioms DGBOZK.PositiveCommutatorCore.absorb_half_of_positive_form


/-! ## Exact trilinear cancellation -/
#print axioms DGBOZK.TrilinearCancellationCore.exact_trilinear_cancellation

/-! ## Structural trilinear differentiation -/
#print axioms DGBOZK.TrilinearDifferentiationCore.transverse_slot_identity
#print axioms DGBOZK.TrilinearDifferentiationCore.longitudinal_slot_identity
#print axioms DGBOZK.TrilinearDifferentiationCore.exact_trilinear_cancellation_from_structural_laws

/-! ## Scalar anisotropic gauge equivalence -/
#print axioms DGBOZK.GaugeEquationCore.normalized_terms_mem_unit_interval
#print axioms DGBOZK.GaugeEquationCore.coordinate_square_bounds
#print axioms DGBOZK.GaugeLowerEquivalenceCore.abs_x_rpow_le_rho
#print axioms DGBOZK.GaugeLowerEquivalenceCore.half_energy_le_rho
#print axioms DGBOZK.GaugeUpperEquivalenceCore.rho_le_energy
#print axioms DGBOZK.GaugeUpperEquivalenceCore.gauge_energy_equivalence

/-! ## Uniqueness of the positive gauge root -/
#print axioms DGBOZK.GaugeUniquenessCore.gauge_sum_strict_decrease_of_x_ne_zero
#print axioms DGBOZK.GaugeUniquenessCore.positive_root_eq_y_square_of_x_eq_zero
#print axioms DGBOZK.GaugeUniquenessCore.positive_root_unique

/-! ## Existence of the positive gauge root -/
#print axioms DGBOZK.GaugeExistenceEndpointsCore.anisotropicEnergy_pos
#print axioms DGBOZK.GaugeExistenceEndpointsCore.gaugeLeftSide_energy_le_one
#print axioms DGBOZK.GaugeExistenceEndpointsCore.one_le_gaugeLeftSide_half_energy
#print axioms DGBOZK.GaugeExistenceCore.gaugeLeftSide_continuousOn
#print axioms DGBOZK.GaugeExistenceCore.exists_positive_gauge_root
#print axioms DGBOZK.GaugeExistenceCore.existsUnique_positive_gauge_root

/-! ## Anisotropic gauge construction -/
#print axioms DGBOZK.GaugeExistenceCore.exists_positive_gauge_root
#print axioms DGBOZK.GaugeExistenceCore.existsUnique_positive_gauge_root
#print axioms DGBOZK.GaugeFunctionCore.anisotropicGauge_pos
#print axioms DGBOZK.GaugeFunctionCore.anisotropicGauge_equation
#print axioms DGBOZK.GaugeFunctionCore.anisotropicGauge_eq_of_positive_solution
#print axioms DGBOZK.GaugeFunctionCore.anisotropicGauge_energy_equivalence
#print axioms DGBOZK.GaugeSymmetryAxesCore.anisotropicGauge_neg_x
#print axioms DGBOZK.GaugeSymmetryAxesCore.anisotropicGauge_neg_y
#print axioms DGBOZK.GaugeSymmetryAxesCore.anisotropicGauge_zero_x
#print axioms DGBOZK.GaugeSymmetryAxesCore.anisotropicGauge_zero_y
#print axioms DGBOZK.GaugeHomogeneityCore.anisotropicGauge_homogeneous

/-! ## Implicit-gauge nondegeneracy -/
#print axioms DGBOZK.GaugeImplicitCore.gaugeRadialDenominator_mem_Icc
#print axioms DGBOZK.GaugeImplicitCore.gaugeRadialDerivative_neg
#print axioms DGBOZK.GaugeImplicitCore.longitudinal_implicit_derivative_formula
#print axioms DGBOZK.GaugeImplicitCore.transverse_implicit_derivative_formula
#print axioms DGBOZK.GaugeImplicitCore.anisotropicGauge_radialDenominator_mem_Icc
#print axioms DGBOZK.GaugeImplicitCore.anisotropicGauge_radialDerivative_neg

/-! ## Fourier and Littlewood--Paley foundations -/
#print axioms DGBOZK.Foundations.sum_dyadicBandSymbol
#print axioms DGBOZK.Foundations.standardSmoothCutoffProfile_antitone
#print axioms DGBOZK.Foundations.standardBandPassActiveSet_subset_dyadicAnnulus
#print axioms DGBOZK.Foundations.integral_comp_twoPi_smul
#print axioms DGBOZK.Foundations.normalized_paperFourier_inversion

/-! ## Bounded pointwise multipliers and abstract L2 bridge -/
#print axioms DGBOZK.Foundations.L2MultiplierCore.pointwise_product_norm_bound
#print axioms DGBOZK.Foundations.L2MultiplierCore.bounded_pointwise_multiplier_memLp
#print axioms DGBOZK.Foundations.L2MultiplierCore.eLpNorm_bounded_pointwise_multiplier_le
#print axioms DGBOZK.Foundations.L2MultiplierCore.bounded_pointwise_multiplier_memLp_two
#print axioms DGBOZK.Foundations.L2MultiplierCore.eLpNorm_two_bounded_pointwise_multiplier_le
#print axioms DGBOZK.Foundations.L2MultiplierCore.norm_conjugated_operator_le

/-! ## Dyadic L2 projector foundation -/
#print axioms DGBOZK.Foundations.DyadicProjectorL2Core.complexDyadicBandSymbol_norm_le_one
#print axioms DGBOZK.Foundations.DyadicProjectorL2Core.complexDyadicBandSymbol_active_subset_dyadicAnnulus
#print axioms DGBOZK.Foundations.DyadicProjectorL2Core.dyadicBandMultiplier_eLpNorm_two_le
#print axioms DGBOZK.Foundations.DyadicProjectorL2Core.dyadicBandMultiplier_memLp_two
#print axioms DGBOZK.Foundations.DyadicProjectorL2Core.standardDyadicBandMultiplier_eLpNorm_two_le
#print axioms DGBOZK.Foundations.DyadicProjectorL2Core.conjugatedDyadicProjector_norm_le

/-! ## Dyadic separation and finite-overlap calculus -/
#print axioms DGBOZK.Foundations.DyadicAnnulusSeparationCore.dyadicBandSymbol_mul_eq_zero_of_separated
#print axioms DGBOZK.Foundations.DyadicAnnulusSeparationCore.no_common_active_frequency_of_separated_dyadic_bands
#print axioms DGBOZK.Foundations.DyadicFiniteOverlapCore.dyadicScale_separated_of_three_le
#print axioms DGBOZK.Foundations.DyadicFiniteOverlapCore.dyadicBandSymbol_mul_eq_zero_of_index_separation
#print axioms DGBOZK.Foundations.DyadicFiniteOverlapCore.active_dyadic_indices_within_two
#print axioms DGBOZK.Foundations.DyadicFiniteOverlapCore.active_dyadic_index_bounds
#print axioms DGBOZK.Foundations.DyadicInteractionSumCore.not_nearDyadicIndex_iff
#print axioms DGBOZK.Foundations.DyadicInteractionSumCore.dyadicBand_interaction_sum_eq_near_filter
#print axioms DGBOZK.Foundations.DyadicInteractionSumCore.standardDyadicBand_interaction_sum_eq_near_filter
#print axioms DGBOZK.Foundations.DyadicInteractionSumCore.nearDyadicIndex_of_both_active
#print axioms DGBOZK.Foundations.DyadicActiveCardinalityCore.mem_nearDyadicIndexSet_iff
#print axioms DGBOZK.Foundations.DyadicActiveCardinalityCore.nearDyadicIndexSet_card_le_five
#print axioms DGBOZK.Foundations.DyadicActiveCardinalityCore.active_indices_subset_nearDyadicIndexSet
#print axioms DGBOZK.Foundations.DyadicActiveCardinalityCore.active_indices_card_le_five
#print axioms DGBOZK.Foundations.DyadicActiveCardinalityCore.standard_active_indices_card_le_five

/-! ## Quantitative dyadic interaction bound -/
#print axioms DGBOZK.Foundations.DyadicFiniteSumBoundCore.sum_abs_le_five_mul_of_card_le_five
#print axioms DGBOZK.Foundations.DyadicInteractionBoundCore.standardDyadicBand_interaction_abs_sum_le_five

/-! ## Finite dyadic family norm bridge -/
#print axioms DGBOZK.Foundations.DyadicFiniteFamilyNormCore.norm_standard_active_dyadic_sum_le_five

/-! ## Verified phase differentiation -/
#print axioms DGBOZK.PhaseTransverseDifferentiationCore.hasDerivAt_omega_eta
#print axioms DGBOZK.PhaseTransverseDifferentiationCore.hasDerivAt_velX_eta
#print axioms DGBOZK.PhaseTransverseDifferentiationCore.hasDerivAt_velY_eta
#print axioms DGBOZK.PhaseTransverseDifferentiationCore.hasDerivAt_velY_xi
#print axioms DGBOZK.PhaseTransverseDifferentiationCore.verified_mixed_derivatives_agree
#print axioms DGBOZK.PhaseLongitudinalDifferentiationCore.hasDerivAt_omega_xi_abs
#print axioms DGBOZK.PhaseLongitudinalDifferentiationCore.hasDerivAt_omega_xi_of_pos
#print axioms DGBOZK.PhaseLongitudinalDifferentiationCore.hasDerivAt_positive_rpow
#print axioms DGBOZK.PhaseLongitudinalDifferentiationCore.hasDerivAt_velX_xi_of_pos
#print axioms DGBOZK.PhaseLongitudinalDifferentiationCore.deriv_omega_xi_of_pos
#print axioms DGBOZK.PhaseLongitudinalDifferentiationCore.deriv_velX_xi_of_pos

/-! ## Verified reduced-fold differentiation -/
#print axioms DGBOZK.FoldDifferentiationCore.hasDerivAt_Psi
#print axioms DGBOZK.FoldDifferentiationCore.hasDerivAt_Psi1
#print axioms DGBOZK.FoldDifferentiationCore.hasDerivAt_Psi2
#print axioms DGBOZK.FoldDifferentiationCore.deriv_Psi_eq_Psi1
#print axioms DGBOZK.FoldDifferentiationCore.deriv_Psi1_eq_Psi2
#print axioms DGBOZK.FoldDifferentiationCore.deriv_Psi2_eq_Psi3

/-! ## Finite Wiener-phase algebraic bound; full lemma remains open -/
#print axioms DGBOZK.WienerPhaseAlgebraCore.norm_cutoff_mul_power_le
#print axioms DGBOZK.WienerPhaseAlgebraCore.norm_scalar_cutoff_mul_power_le
#print axioms DGBOZK.WienerPhaseAlgebraCore.norm_finite_localized_phase_le

#print axioms DGBOZK.WienerPhaseAlgebraCore.localized_exp_hasSum

#print axioms DGBOZK.WienerPhaseAlgebraCore.hasDerivAt_localized_exp
