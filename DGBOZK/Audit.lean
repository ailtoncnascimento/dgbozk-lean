/-
# Axiom audit

The point of a conditional formalization is that the reader can see exactly what
was assumed.  This file prints the axiom dependencies of every headline result
in the library.

Expected output for **all** of them:

  'theorem' depends on axioms: [propext, Classical.choice, Quot.sound]

that is, only the three axioms of Lean's own logic — no `sorry`, and no
project-specific axiom.  The black boxes of `DGBOZK/BlackBoxes.lean` are carried
as *hypotheses* or as *definitions*, never as axioms, so they are visible in the
statements rather than hidden in the trusted base.

Run with `lake env lean DGBOZK/Audit.lean`.
-/
import DGBOZK

open DGBOZK

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

/-! ## §5  The localized cubic cancellation -/
#print axioms DGBOZK.Cancellation.flow_symbol_identity
#print axioms DGBOZK.Cancellation.transverse_flow_identity
#print axioms DGBOZK.Cancellation.paper_identity_forces
#print axioms DGBOZK.Cancellation.residual_term_unlisted

/-! ## §6  The focusing resonance -/
#print axioms DGBOZK.Resonance.resonance_lower_bound
#print axioms DGBOZK.Resonance.middle_term_bound

/-! ## §8–§9  Closure -/
#print axioms DGBOZK.bootstrap_closure
#print axioms DGBOZK.exists_eps_defocusing
#print axioms DGBOZK.exists_eps_focusing
#print axioms DGBOZK.coupled_admissible_defocusing
#print axioms DGBOZK.coupled_admissible_focusing
