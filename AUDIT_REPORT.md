# DGBOZK Lean 4 manuscript-alignment report

Date: 9 September 2026

## Conclusion

This revision aligns the default Lean target with the cleaned manuscript
identified by SHA-256
9a0920d31a4ce57d8d78dc046b727ac27b892ae8fbe4c82de60b0b70c7e2b1a0.

The material remains a targeted consistency check.  It is not a formal proof of
the article or of local well posedness.

## Changes made for the cleaned focusing argument

1. FocusingThreshold.lean defines

       s_minus(alpha) = 3/2 - alpha/4

   and proves its equivalent form, endpoint values, strict monotonicity, and
   the exact equivalence between the threshold and the existence of an
   intermediate exponent tau above one.

2. It fixes the manuscript choice

       epsilon_0 = 1/2 - alpha/4,
       tau = s - epsilon_0 = s - 1/2 + alpha/4,

   proves epsilon_0 is positive for alpha below two, and proves the existence
   of the remaining positive refined-estimate slack.

3. EnergyEnvelope.lean proves the final scalar absorption step following from a
   quadratic frequency-envelope inequality and the positivity of the dyadic
   decay margin gamma minus 2 delta.

4. The earlier s greater than one focusing parameter declarations were removed
   from Bootstrap.lean and Audit.lean.

5. Resonance.lean, which concerns the abandoned normal-form route, is retained
   only as a legacy source file and is no longer imported by the default
   DGBOZK target.

## What the new declarations establish

| Cleaned manuscript | Lean declaration | Status |
|---|---|---|
| Equation sfoc | sMinus, sMinus_eq | Exact scalar identity |
| Endpoint values | sMinus_one, sMinus_two | Exact scalar identities |
| Transition exponent ceiling | direct_commutator_gap_iff | Exact scalar equivalence |
| Nonempty tau interval | exists_admissible_tau_iff | Exact if-and-only-if theorem |
| Equation eps0-focusing | focusingEps0, focusingTau_eq | Exact definitions and identity |
| Remaining exponent slack in Proposition coupled | exists_refined_epsilon, focusing_parameter_package | Exact scalar feasibility |
| Condition delta-gamma | envelope_decay_margin | Exact scalar implication |
| Final envelope absorption | quadratic_envelope_closure | Exact scalar implication |

## What is not established

The hypotheses and estimates that make the scalar implications applicable are
not formalized.  In particular, this project does not prove:

- Lemma wiener-phase;
- Lemma positive-commutator or equation D-wiener;
- the direct focusing transition commutator proposition;
- the refined Strichartz or microlocal smoothing propositions;
- the frequency-resolved nonlinear energy system;
- the envelope-kernel estimate;
- modified-energy coercivity;
- construction, uniqueness, continuity, or the main theorem.

These are substantive analytic results.  Exact arithmetic tests cannot validate
them, and their absence must be disclosed.

## Checks completed in this environment

- 2,569 independent exact rational and integer regression checks pass.
- Shell verification scripts pass syntax checking.
- No sorry, admit, or project-level axiom declaration is found by the static
  source scan.
- The default import graph excludes the legacy resonance module.

This environment does not contain the pinned Lean executable or Mathlib build
cache.  Therefore the new Lean modules have not yet been kernel-built here.
They are candidate source until the Codespace procedure below returns zero and
the pushed commit receives a green workflow for the same SHA.

## Required Codespace verification

Run from the repository root:

    cd /workspaces/dgbozk-lean
    bash scripts/setup.sh
    bash scripts/verify.sh
    git diff --check
    git status --short

Then record:

    git rev-parse HEAD
    lake env lean --version
    git -C .lake/packages/mathlib rev-parse HEAD

The expected versions are Lean 4.22.0 and Mathlib commit
79e94a093aff4a60fb1b1f92d9681e407124c2ca.

Do not call this article-level formal verification unless the omitted analytic
results and a theorem matching the complete statement of the manuscript's main
theorem have also been formalized.
