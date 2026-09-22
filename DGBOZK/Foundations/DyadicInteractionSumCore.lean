/-
# Finite dyadic interaction sums

This module packages the finite-overlap theorem into a form suitable for
Littlewood--Paley interaction sums.

For a fixed dyadic index `k`, only indices `j` satisfying

  j <= k + 2  and  k <= j + 2

can contribute to the pointwise product of the kth and jth band symbols.
Thus every finite interaction sum reduces exactly to this five-index window.
-/

import DGBOZK.Foundations.DyadicFiniteOverlapCore

set_option autoImplicit false

namespace DGBOZK
namespace Foundations
namespace DyadicInteractionSumCore

open DyadicFiniteOverlapCore

/--
The finite interaction window for two dyadic indices.
-/
def nearDyadicIndex (k j : ℕ) : Prop :=
  j ≤ k + 2 ∧ k ≤ j + 2

instance nearDyadicIndexDecidable
    (k j : ℕ) :
    Decidable (nearDyadicIndex k j) := by
  unfold nearDyadicIndex
  infer_instance

/--
Failure of the five-index interaction condition is equivalent to separation
by at least three indices in one direction.
-/
theorem not_nearDyadicIndex_iff
    (k j : ℕ) :
    ¬ nearDyadicIndex k j
      ↔
    k + 3 ≤ j ∨ j + 3 ≤ k := by
  unfold nearDyadicIndex
  omega

/--
A non-near dyadic interaction has pointwise zero symbol product.
-/
theorem dyadicBandSymbol_mul_eq_zero_of_not_near
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k j : ℕ)
    (zeta : FrequencySpace)
    (hnotNear :
      ¬ nearDyadicIndex k j) :
    dyadicBandSymbol chi alpha k zeta
        * dyadicBandSymbol chi alpha j zeta
      =
    0 := by
  exact
    dyadicBandSymbol_mul_eq_zero_of_index_separation
      chi alpha k j zeta
      ((not_nearDyadicIndex_iff k j).mp hnotNear)

/--
Every finite interaction sum reduces exactly to the indices in the
five-position window around `k`.
-/
theorem dyadicBand_interaction_sum_eq_near_filter
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace)
    (indices : Finset ℕ) :
    (∑ j ∈ indices,
      dyadicBandSymbol chi alpha k zeta
        * dyadicBandSymbol chi alpha j zeta)
      =
    ∑ j ∈ indices.filter (nearDyadicIndex k),
      dyadicBandSymbol chi alpha k zeta
        * dyadicBandSymbol chi alpha j zeta := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j hjIndices hjNotFiltered
  have hnotNear :
      ¬ nearDyadicIndex k j := by
    intro hnear
    apply hjNotFiltered
    exact
      Finset.mem_filter.mpr
        ⟨hjIndices, hnear⟩
  exact
    dyadicBandSymbol_mul_eq_zero_of_not_near
      chi alpha k j zeta hnotNear

/--
The finite-sum reduction for the canonical smooth cutoff profile.
-/
theorem standardDyadicBand_interaction_sum_eq_near_filter
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace)
    (indices : Finset ℕ) :
    (∑ j ∈ indices,
      dyadicBandSymbol
          standardSmoothCutoffProfile alpha k zeta
        *
      dyadicBandSymbol
          standardSmoothCutoffProfile alpha j zeta)
      =
    ∑ j ∈ indices.filter (nearDyadicIndex k),
      dyadicBandSymbol
          standardSmoothCutoffProfile alpha k zeta
        *
      dyadicBandSymbol
          standardSmoothCutoffProfile alpha j zeta :=
  dyadicBand_interaction_sum_eq_near_filter
    standardSmoothCutoffProfile alpha k zeta indices

/--
Any two simultaneously active indices satisfy the interaction-window
predicate.
-/
theorem nearDyadicIndex_of_both_active
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k j : ℕ)
    (zeta : FrequencySpace)
    (hk :
      dyadicBandSymbol chi alpha k zeta ≠ 0)
    (hj :
      dyadicBandSymbol chi alpha j zeta ≠ 0) :
    nearDyadicIndex k j := by
  exact
    active_dyadic_indices_within_two
      chi alpha k j zeta hk hj

end DyadicInteractionSumCore
end Foundations
end DGBOZK
