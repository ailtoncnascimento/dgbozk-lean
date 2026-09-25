/-
# Quantitative bounds for finite dyadic interaction sums

The preceding dyadic modules prove that at most five indices can interact
with a fixed dyadic band. This module records the elementary ordered-ring
consequence: a sum of terms bounded by `B` is bounded by five times `B`.

This is finite-dimensional arithmetic. It does not prove a
Littlewood--Paley square-function estimate, an operator-valued almost
orthogonality theorem, or a nonlinear paraproduct estimate.
-/

import DGBOZK.Foundations.DyadicActiveCardinalityCore
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DGBOZK
namespace Foundations
namespace DyadicFiniteSumBoundCore

section FiniteSum

variable {ι : Type*}

/--
A finite sum is bounded by the cardinality times a common pointwise bound.
No positivity assumption on the summands is required.
-/
theorem sum_le_card_mul_of_term_le
    (indices : Finset ι)
    (term : ι → ℝ)
    {bound : ℝ}
    (hterm :
      ∀ i ∈ indices, term i ≤ bound) :
    ∑ i ∈ indices, term i
      ≤
    (indices.card : ℝ) * bound := by
  calc
    ∑ i ∈ indices, term i
        ≤
      ∑ _i ∈ indices, bound := by
        exact Finset.sum_le_sum fun i hi => hterm i hi
    _ = (indices.card : ℝ) * bound := by
      simp

/--
If the finite index family has at most five elements and every term is
bounded above by a nonnegative number `bound`, then the sum is bounded by
`5 * bound`.
-/
theorem sum_le_five_mul_of_card_le_five
    (indices : Finset ι)
    (term : ι → ℝ)
    {bound : ℝ}
    (hcard : indices.card ≤ 5)
    (hbound : 0 ≤ bound)
    (hterm :
      ∀ i ∈ indices, term i ≤ bound) :
    ∑ i ∈ indices, term i
      ≤
    5 * bound := by
  have hcardReal :
      (indices.card : ℝ) ≤ 5 := by
    exact_mod_cast hcard
  calc
    ∑ i ∈ indices, term i
        ≤
      (indices.card : ℝ) * bound :=
        sum_le_card_mul_of_term_le
          indices term hterm
    _ ≤ 5 * bound :=
      mul_le_mul_of_nonneg_right
        hcardReal hbound

/--
Absolute-valued contributions over at most five indices satisfy the same
explicit bound.
-/
theorem sum_abs_le_five_mul_of_card_le_five
    (indices : Finset ι)
    (term : ι → ℝ)
    {bound : ℝ}
    (hcard : indices.card ≤ 5)
    (hbound : 0 ≤ bound)
    (hterm :
      ∀ i ∈ indices, |term i| ≤ bound) :
    ∑ i ∈ indices, |term i|
      ≤
    5 * bound := by
  exact
    sum_le_five_mul_of_card_le_five
      indices
      (fun i => |term i|)
      hcard
      hbound
      hterm

end FiniteSum

end DyadicFiniteSumBoundCore
end Foundations
end DGBOZK
