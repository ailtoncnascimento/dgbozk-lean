/-
# Norm bounds for finite dyadic interaction families

This module lifts the scalar five-term estimate to families taking values in
a seminormed additive commutative group.

It proves that a sum of at most five vectors, each having norm at most `B`,
has norm at most `5 * B`. It then specializes the statement to the near and
active dyadic-index filters constructed in the preceding modules.

The result may be instantiated with an `L2` space. It does not itself identify
a Fourier multiplier with an `L2` operator, prove square-function
orthogonality, or establish a Cotlar--Stein estimate.
-/

import DGBOZK.Foundations.DyadicInteractionBoundCore
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace DGBOZK
namespace Foundations
namespace DyadicFiniteFamilyNormCore

open DyadicFiniteSumBoundCore
open DyadicInteractionSumCore
open DyadicActiveCardinalityCore
open DyadicInteractionBoundCore

section AbstractFamily

variable {ι E : Type*}
variable [SeminormedAddCommGroup E]

/--
The triangle inequality followed by the cardinality-times-bound estimate.
-/
theorem norm_sum_le_card_mul
    (indices : Finset ι)
    (vector : ι → E)
    {bound : ℝ}
    (hvector :
      ∀ i ∈ indices, ‖vector i‖ ≤ bound) :
    ‖∑ i ∈ indices, vector i‖
      ≤
    (indices.card : ℝ) * bound := by
  calc
    ‖∑ i ∈ indices, vector i‖
        ≤
      ∑ i ∈ indices, ‖vector i‖ := by
        exact norm_sum_le _ _
    _ ≤ (indices.card : ℝ) * bound :=
      sum_le_card_mul_of_term_le
        indices
        (fun i => ‖vector i‖)
        hvector

/--
A family with at most five members and common norm bound `bound` has total
norm at most `5 * bound`.
-/
theorem norm_sum_le_five_mul_of_card_le_five
    (indices : Finset ι)
    (vector : ι → E)
    {bound : ℝ}
    (hcard : indices.card ≤ 5)
    (hbound : 0 ≤ bound)
    (hvector :
      ∀ i ∈ indices, ‖vector i‖ ≤ bound) :
    ‖∑ i ∈ indices, vector i‖
      ≤
    5 * bound := by
  calc
    ‖∑ i ∈ indices, vector i‖
        ≤
      (indices.card : ℝ) * bound :=
        norm_sum_le_card_mul
          indices vector hvector
    _ ≤ 5 * bound := by
      have hcardReal :
          (indices.card : ℝ) ≤ 5 := by
        exact_mod_cast hcard
      exact
        mul_le_mul_of_nonneg_right
          hcardReal hbound

end AbstractFamily

section DyadicFamily

variable {E : Type*}
variable [SeminormedAddCommGroup E]

/--
A vector-valued sum over the near dyadic interaction window has total norm
at most five times a common norm bound.
-/
theorem norm_near_dyadic_sum_le_five
    (k : ℕ)
    (indices : Finset ℕ)
    (vector : ℕ → E)
    {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hvector :
      ∀ j ∈ indices.filter (nearDyadicIndex k),
        ‖vector j‖ ≤ bound) :
    ‖∑ j ∈ indices.filter (nearDyadicIndex k),
        vector j‖
      ≤
    5 * bound := by
  exact
    norm_sum_le_five_mul_of_card_le_five
      (indices.filter (nearDyadicIndex k))
      vector
      (near_filter_card_le_five k indices)
      hbound
      hvector

/--
If the reference band is active, the vector-valued sum over every active
dyadic index in a finite family has total norm at most five times a common
norm bound.
-/
theorem norm_active_dyadic_sum_le_five
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace)
    (indices : Finset ℕ)
    (vector : ℕ → E)
    {bound : ℝ}
    (hk :
      dyadicBandSymbol chi alpha k zeta ≠ 0)
    (hbound : 0 ≤ bound)
    (hvector :
      ∀ j ∈ indices.filter
          (fun j =>
            dyadicBandSymbol chi alpha j zeta ≠ 0),
        ‖vector j‖ ≤ bound) :
    ‖∑ j ∈ indices.filter
          (fun j =>
            dyadicBandSymbol chi alpha j zeta ≠ 0),
        vector j‖
      ≤
    5 * bound := by
  exact
    norm_sum_le_five_mul_of_card_le_five
      (indices.filter
        (fun j =>
          dyadicBandSymbol chi alpha j zeta ≠ 0))
      vector
      (active_indices_card_le_five
        chi alpha k zeta indices hk)
      hbound
      hvector

/--
Canonical-cutoff specialization of the active-family norm estimate.
-/
theorem norm_standard_active_dyadic_sum_le_five
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace)
    (indices : Finset ℕ)
    (vector : ℕ → E)
    {bound : ℝ}
    (hk :
      dyadicBandSymbol
        standardSmoothCutoffProfile alpha k zeta ≠ 0)
    (hbound : 0 ≤ bound)
    (hvector :
      ∀ j ∈ indices.filter
          (fun j =>
            dyadicBandSymbol
              standardSmoothCutoffProfile
              alpha j zeta ≠ 0),
        ‖vector j‖ ≤ bound) :
    ‖∑ j ∈ indices.filter
          (fun j =>
            dyadicBandSymbol
              standardSmoothCutoffProfile
              alpha j zeta ≠ 0),
        vector j‖
      ≤
    5 * bound := by
  exact
    norm_active_dyadic_sum_le_five
      standardSmoothCutoffProfile
      alpha k zeta indices vector
      hk hbound hvector

end DyadicFamily

end DyadicFiniteFamilyNormCore
end Foundations
end DGBOZK
