/-
# Quantitative dyadic interaction bound

This module combines:

* pointwise separation of non-near dyadic bands;
* the cardinality bound for the five-index interaction window;
* the unit bound for the dyadic band symbol; and
* the abstract finite-sum estimate.

It proves that the sum of the absolute values of the interactions of a
fixed dyadic band with any finite family is bounded by five.

This remains a pointwise scalar estimate. It is not a Littlewood--Paley
square-function theorem, an operator-valued almost-orthogonality result,
or a nonlinear paraproduct estimate.
-/

import DGBOZK.Foundations.DyadicFiniteSumBoundCore
import DGBOZK.Foundations.DyadicProjectorL2Core
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DGBOZK
namespace Foundations
namespace DyadicInteractionBoundCore

open DyadicInteractionSumCore
open DyadicActiveCardinalityCore
open DyadicFiniteSumBoundCore
open DyadicProjectorL2Core

/--
The real dyadic band symbol has absolute value at most one.
This is the real-valued form of the complex-symbol norm estimate.
-/
theorem dyadicBandSymbol_abs_le_one
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace) :
    |dyadicBandSymbol chi alpha k zeta| ≤ 1 := by
  simpa [complexDyadicBandSymbol] using
    (complexDyadicBandSymbol_norm_le_one
      chi alpha k zeta)

/--
The absolute value of a product of two dyadic band symbols is at most one.
-/
theorem dyadicBandSymbol_product_abs_le_one
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k j : ℕ)
    (zeta : FrequencySpace) :
    |dyadicBandSymbol chi alpha k zeta
        * dyadicBandSymbol chi alpha j zeta|
      ≤
    1 := by
  rw [abs_mul]
  calc
    |dyadicBandSymbol chi alpha k zeta|
          * |dyadicBandSymbol chi alpha j zeta|
        ≤
      1 * 1 := by
        exact
          mul_le_mul
            (dyadicBandSymbol_abs_le_one
              chi alpha k zeta)
            (dyadicBandSymbol_abs_le_one
              chi alpha j zeta)
            (abs_nonneg
              (dyadicBandSymbol chi alpha j zeta))
            zero_le_one
    _ = 1 := by norm_num

/--
The indices in a finite family that lie in the interaction window around
`k` have cardinality at most five.
-/
theorem near_filter_card_le_five
    (k : ℕ)
    (indices : Finset ℕ) :
    (indices.filter (nearDyadicIndex k)).card ≤ 5 := by
  have hsubset :
      indices.filter (nearDyadicIndex k)
        ⊆ nearDyadicIndexSet k := by
    intro j hj
    exact
      (mem_nearDyadicIndexSet_iff k j).2
        (Finset.mem_filter.mp hj).2
  calc
    (indices.filter (nearDyadicIndex k)).card
        ≤
      (nearDyadicIndexSet k).card :=
        Finset.card_le_card hsubset
    _ ≤ 5 :=
      nearDyadicIndexSet_card_le_five k

/--
The sum of absolute interaction contributions reduces exactly to the
five-index window.
-/
theorem dyadicBand_interaction_abs_sum_eq_near_filter
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace)
    (indices : Finset ℕ) :
    (∑ j ∈ indices,
      |dyadicBandSymbol chi alpha k zeta
        * dyadicBandSymbol chi alpha j zeta|)
      =
    ∑ j ∈ indices.filter (nearDyadicIndex k),
      |dyadicBandSymbol chi alpha k zeta
        * dyadicBandSymbol chi alpha j zeta| := by
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
  have hzero :
      dyadicBandSymbol chi alpha k zeta
          * dyadicBandSymbol chi alpha j zeta
        =
      0 :=
    dyadicBandSymbol_mul_eq_zero_of_not_near
      chi alpha k j zeta hnotNear
  simp [hzero]

/--
Any finite family of dyadic bands contributes at most five in absolute
pointwise interaction with a fixed band.
-/
theorem dyadicBand_interaction_abs_sum_le_five
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace)
    (indices : Finset ℕ) :
    (∑ j ∈ indices,
      |dyadicBandSymbol chi alpha k zeta
        * dyadicBandSymbol chi alpha j zeta|)
      ≤
    5 := by
  rw [
    dyadicBand_interaction_abs_sum_eq_near_filter
      chi alpha k zeta indices
  ]
  have hbound :=
    sum_abs_le_five_mul_of_card_le_five
      (indices.filter (nearDyadicIndex k))
      (fun j =>
        dyadicBandSymbol chi alpha k zeta
          * dyadicBandSymbol chi alpha j zeta)
      (bound := 1)
      (near_filter_card_le_five k indices)
      zero_le_one
      (by
        intro j hj
        exact
          dyadicBandSymbol_product_abs_le_one
            chi alpha k j zeta)
  simpa using hbound

/--
The quantitative interaction bound for the canonical smooth cutoff profile.
-/
theorem standardDyadicBand_interaction_abs_sum_le_five
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace)
    (indices : Finset ℕ) :
    (∑ j ∈ indices,
      |dyadicBandSymbol
          standardSmoothCutoffProfile alpha k zeta
        *
       dyadicBandSymbol
          standardSmoothCutoffProfile alpha j zeta|)
      ≤
    5 := by
  exact
    dyadicBand_interaction_abs_sum_le_five
      standardSmoothCutoffProfile
      alpha k zeta indices

end DyadicInteractionBoundCore
end Foundations
end DGBOZK
