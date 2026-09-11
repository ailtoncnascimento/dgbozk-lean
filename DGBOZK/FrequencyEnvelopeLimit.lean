/-
# Passage from finite frequency envelopes to limiting blocks

This module records the order-theoretic limit step used after obtaining
uniform estimates for finite frequency truncations.

No convergence of PDE solutions is proved here. Convergence of the squared
blocks and of their frequency envelopes is represented by explicit `Tendsto`
hypotheses.
-/

import DGBOZK.FrequencyEnvelopeMaximum
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open scoped Topology
open Filter

namespace DGBOZK
namespace FrequencyEnvelope

noncomputable section

variable {ι : Type*}

/--
A uniform inequality between two families of real numbers passes to their
pointwise limits.

This is the abstract closed-order argument needed for the passage from finite
frequency truncations to an infinite dyadic decomposition.
-/
theorem bound_passes_to_pointwise_limit
    {blockSq envelopeSqApprox : ℕ → ι → ℝ}
    {blockSqLimit envelopeSqLimit : ι → ℝ}
    {C : ℝ}
    (hblock : ∀ k,
      Tendsto
        (fun n => blockSq n k)
        atTop
        (𝓝 (blockSqLimit k)))
    (henvelope : ∀ k,
      Tendsto
        (fun n => envelopeSqApprox n k)
        atTop
        (𝓝 (envelopeSqLimit k)))
    (hbound : ∀ n k,
      blockSq n k ≤ C * envelopeSqApprox n k) :
    ∀ k, blockSqLimit k ≤ C * envelopeSqLimit k := by
  intro k

  have hright :
      Tendsto
        (fun n => C * envelopeSqApprox n k)
        atTop
        (𝓝 (C * envelopeSqLimit k)) :=
    tendsto_const_nhds.mul (henvelope k)

  have hdiff :
      Tendsto
        (fun n =>
          C * envelopeSqApprox n k - blockSq n k)
        atTop
        (𝓝
          (C * envelopeSqLimit k - blockSqLimit k)) :=
    hright.sub (hblock k)

  have hnegative :
      -(C * envelopeSqLimit k - blockSqLimit k) ≤ 0 := by
    apply le_of_tendsto hdiff.neg
    exact Filter.Eventually.of_forall fun n =>
      neg_nonpos.mpr
        (sub_nonneg.mpr (hbound n k))

  have hlimit :
      0 ≤ C * envelopeSqLimit k - blockSqLimit k :=
    neg_nonpos.mp hnegative

  exact sub_nonneg.mp hlimit

/--
Finite propagated frequency-envelope bounds pass to the limiting squared
blocks.

The hypotheses state convergence directly at the squared-energy level.
Deriving this convergence from the frequency-truncated PDE solutions is a
separate analytic task.
-/
theorem finite_to_limit_envelope_propagation
    {Y : ℕ → ι → ℝ}
    {cSq : ℕ → ι → ℝ}
    {Ylimit cSqLimit : ι → ℝ}
    {C₀ : ℝ}
    (hY : ∀ k,
      Tendsto
        (fun n => (Y n k) ^ 2)
        atTop
        (𝓝 ((Ylimit k) ^ 2)))
    (hcSq : ∀ k,
      Tendsto
        (fun n => cSq n k)
        atTop
        (𝓝 (cSqLimit k)))
    (hfinite : ∀ n k,
      (Y n k) ^ 2 ≤ 2 * C₀ * cSq n k) :
    ∀ k, (Ylimit k) ^ 2 ≤ 2 * C₀ * cSqLimit k := by
  exact bound_passes_to_pointwise_limit
    hY hcSq hfinite

end

end FrequencyEnvelope
end DGBOZK
