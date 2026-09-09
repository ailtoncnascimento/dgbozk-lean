# Cleaned-manuscript alignment

Target manuscript:

    dgbozk_nonlinear_analysis_clean.tex
    SHA-256 9a0920d31a4ce57d8d78dc046b727ac27b892ae8fbe4c82de60b0b70c7e2b1a0

## New focusing declarations

| Manuscript location | Lean declaration | Meaning |
|---|---|---|
| eq:sfoc | sMinus, sMinus_eq | exact focusing threshold |
| eq:sfoc endpoints | sMinus_one, sMinus_two | values at alpha one and two |
| prop:foc-direct-commutator exponent condition | direct_commutator_gap_iff | scalar rearrangement only |
| interval following eq:eps0-focusing | exists_admissible_tau_iff | interval is nonempty exactly above threshold |
| eq:eps0-focusing | focusingEps0, focusingTau, focusingTau_eq | canonical endpoint choice |
| prop:coupled focusing parameter paragraph | exists_refined_epsilon | remaining scalar slack |
| same paragraph | focusing_parameter_package | collected scalar package |

## Frequency-envelope declarations

| Manuscript location | Lean declaration | Meaning |
|---|---|---|
| eq:delta-gamma | envelope_decay_margin | positivity of gamma minus two delta |
| absorption after eq:block-system | quadratic_envelope_closure | final scalar closure |

Neither file proves prop:foc-direct-commutator or prop:block-system.  Those are
analytic inputs and remain outside the formalization.  The default target also
does not import the legacy Resonance.lean file because the cleaned manuscript
does not use the earlier normal-form route.
