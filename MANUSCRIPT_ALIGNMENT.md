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

## Fourier foundations

The modules under `DGBOZK/Foundations` develop conventions for coordinates,
Fourier transformation and inversion, anisotropic regions, and smooth dyadic
cutoffs. Some have been compiled separately, but they are not imported by
`DGBOZK.lean`. They are therefore not part of the passing default target or
the integrated axiom audit recorded here.

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
