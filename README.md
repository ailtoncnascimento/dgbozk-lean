# dgbozk-lean

Targeted Lean 4 checks accompanying A. C. Nascimento, Local well-posedness for
two-sign dispersion-generalized Benjamin--Ono--Zakharov--Kuznetsov equations.

The current validation target is the cleaned manuscript whose SHA-256 is

    9a0920d31a4ce57d8d78dc046b727ac27b892ae8fbe4c82de60b0b70c7e2b1a0

The project is pinned to Lean 4.22.0 and Mathlib 4.22.0.

## Exact scope

This repository is not an article-level formal verification and does not prove
the local-well-posedness theorem.  The default DGBOZK target machine-checks:

1. the exponent, scaling, and defocusing threshold arithmetic;
2. selected algebraic consequences of the displayed phase and fold formulas;
3. the scalar focusing velocity bound;
4. the polynomial sign identity behind the localized cubic cancellation;
5. the defocusing parameter choices and scalar small-data bootstrap;
6. the cleaned focusing threshold

       s_minus(alpha) = 3/2 - alpha/4 = (6-alpha)/4,

   its endpoint values, and the existence of the intermediate exponents used
   after the direct transition estimate; and
7. the final scalar absorption implication for a quadratic frequency-envelope
   system.
8. the Wiener-algebra lemmas `lem:wiener` and `lem:wiener-phase`, including
   both bounds of `eq:wiener-average` and a bound on the `t`-derivative that is
   uniform in `|t| <= 1` (DGBOZK/Foundations/WienerAlgebraCore.lean).  These
   are proved from Mathlib alone, without hypotheses.

The source contains no sorry, admit, or project-level axiom declaration.
Audit.lean prints the axiom dependencies of the headline results.

## What remains outside Lean

Successful compilation does not validate the analytic heart of the article.
The following remain unformalized:

- the full anisotropic Littlewood--Paley theory;
- oscillatory-integral and van der Corput estimates;
- TT-star and mixed maximal-function estimates;
- bilinear multiplier and weighted paraproduct estimates;
- the positive-commutator and direct focusing transition estimates, including
  the terms containing derivatives of the weight;
- sharp Garding and coercivity;
- refined short-time Strichartz and microlocal smoothing;
- the frequency-resolved nonlinear energy inequality itself;
- construction, compactness, uniqueness, frequency-envelope propagation, and
  Bona--Smith continuity; and
- a Lean theorem whose conclusion is the manuscript's main theorem.

BlackBoxes.lean records this boundary in the source.

## Manuscript-aligned focusing check

FocusingThreshold.lean formalizes the exact scalar logic:

- s_minus(alpha) = 3/2 - alpha/4;
- s_minus(1) = 5/4 and s_minus(2) = 1;
- the direct commutator exponent condition is equivalent to

      tau <= s - 1/2 + alpha/4;

- an exponent tau with 1 < tau below that ceiling exists if and only if
  s_minus(alpha) < s; and
- for 1 <= alpha < 2 this supplies the positive slack required by the refined
  estimate's scalar exponent bookkeeping.

These theorems do not prove the direct commutator estimate.  They verify only
what follows arithmetically once that analytic estimate is established.

EnergyEnvelope.lean similarly proves only

    Z <= C0 + Theta C_beta Z,   Theta C_beta <= 1/2,   0 <= Z
    implies
    Z <= 2 C0.

It does not prove the frequency-resolved nonlinear inequality that supplies the
first line.

## Legacy material

Resonance.lean is retained for historical comparison with an earlier
normal-form draft.  It is deliberately not imported by the default target and
is not part of the validation claim for the cleaned manuscript.

The Foundations directory contains Fourier-convention and dyadic work, and
the Wiener-algebra module WienerAlgebraCore.lean.  It is not an anisotropic
Littlewood--Paley formalization.

## Reproducible verification

From a clean clone in a GitHub Codespace:

    cd /workspaces/dgbozk-lean
    cat lean-toolchain
    grep -n 'inputRev\|"rev"\|"name": "mathlib"' lake-manifest.json
    bash scripts/setup.sh
    bash scripts/verify.sh
    lake env lean --version
    git -C .lake/packages/mathlib rev-parse HEAD

The expected toolchain is leanprover/lean4:v4.22.0.  The pinned Mathlib commit
is 79e94a093aff4a60fb1b1f92d9681e407124c2ca.

Before citing the artifact, push the exact commit, require the workflow to pass,
and record:

    git rev-parse HEAD
    git status --short

The status output must be empty, and the successful workflow run must display
the same commit SHA.

## Suggested disclosure

Selected sign-, polynomial-, and exponent-sensitive calculations, and the
Wiener-algebra lemmas lem:wiener and lem:wiener-phase, were checked in Lean 4.
The artifact does not formalize the remaining harmonic-analysis estimates or
the local-well-posedness theorem; those arguments remain subject to conventional
mathematical review.

Apache-2.0 license.
