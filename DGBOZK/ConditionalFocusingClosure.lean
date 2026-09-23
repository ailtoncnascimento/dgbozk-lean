/-
# Conditional focusing closure (PFR-style proposal)

This file is a *proposal* for the dgbozk-lean repository.  Instead of
transcribing the manuscript's final list of constraints on `τ`, it states each
analytic input of the focusing closure as a named hypothesis whose content is
the exponent condition under which the corresponding manuscript proposition is
applied.  The theorem then *derives* the admissible range of `s`.

Doing this exposes a gap: the manuscript imposes `1 < τ` (said to be "used in
the focusing smoothing proposition"), but no step of the written proofs of
`prop:hyp-smoothing`, `prop:hyp-product` or `prop:foc-direct-commutator` uses
it.  Without it, the exponent bookkeeping closes for
`s > max 1 (2 - 3α/4)`, which is strictly below `s⁻_α = 3/2 - α/4` for
`1 < α < 2`.  With it, the range is exactly `s > s⁻_α`.

Nothing here proves any analytic estimate.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DGBOZK.ConditionalFocusing

/-- Exponent-level record of where each focusing input is applied
(manuscript labels in comments).  `ε` is the refined-Strichartz slack. -/
structure Inputs (α s τ ε : ℝ) : Prop where
  /-- `eq:refined-hyp-opt`, homogeneous term: `J^{(3-α)/2+ε} u ∈ L^∞_T L²`. -/
  refinedHom : (3 - α) / 2 + ε ≤ s
  /-- `prop:hyp-product` with `γ = 1/2 + ε` (Strichartz and maximal forcing). -/
  product : (1 / 2 + ε) + (1 - α / 2) < τ
  /-- `prop:foc-direct-commutator`, `eq:foc-direct-summed`. -/
  transition : τ ≤ s - 1 / 2 + α / 4
  /-- `eq:foc-sup-square-sum`: geometric summation needs `τ < s`. -/
  smoothingGap : τ < s
  /-- `H^s ↪ L^∞` and the algebra property (used for `‖v‖_∞ ≤ 𝓔⁻`). -/
  embedding : 1 < s
  slack : 0 < ε

/-- Without the extra constraint `1 < τ` the inputs are satisfiable exactly
when `s > max 1 (2 - 3α/4)`. -/
theorem inputs_iff {α s : ℝ} (hα1 : 1 ≤ α) (hα2 : α < 2) :
    (∃ τ ε : ℝ, Inputs α s τ ε) ↔ (1 < s ∧ 2 - 3 * α / 4 < s) := by
  constructor
  · rintro ⟨τ, ε, h⟩
    exact ⟨h.embedding, by linarith [h.product, h.transition, h.slack]⟩
  · rintro ⟨h1, h2⟩
    -- slack below the product/transition gap and below the Strichartz margin
    set g := s - (2 - 3 * α / 4) with hg
    have hgpos : 0 < g := by linarith
    refine ⟨s - 1 / 2 + α / 4, g / 2, ?_, ?_, le_refl _, ?_, h1, by linarith⟩
    · -- (3-α)/2 ≤ 2 - 3α/4 because α ≤ 2
      linarith
    · linarith
    · linarith

/-- With the manuscript's additional constraint `1 < τ`, the admissible range
is exactly `s > 3/2 - α/4`. -/
theorem inputs_with_tau_gt_one_iff {α s : ℝ} (hα1 : 1 ≤ α) (hα2 : α < 2) :
    (∃ τ ε : ℝ, Inputs α s τ ε ∧ 1 < τ) ↔ 3 / 2 - α / 4 < s := by
  constructor
  · rintro ⟨τ, ε, h, hτ⟩
    linarith [h.transition]
  · intro hs
    set g := s - (3 / 2 - α / 4) with hg
    have hgpos : 0 < g := by linarith
    refine ⟨s - 1 / 2 + α / 4, g / 2, ⟨?_, ?_, le_refl _, ?_, ?_, by linarith⟩, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith
    · linarith

/-- The two thresholds agree at `α = 1` and differ for every `1 < α < 2`. -/
theorem thresholds_differ {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    max 1 (2 - 3 * α / 4) < 3 / 2 - α / 4 := by
  rcases le_total 1 (2 - 3 * α / 4) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

end DGBOZK.ConditionalFocusing
