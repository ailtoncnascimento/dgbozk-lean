/-
# Cardinality of the active dyadic interaction window

This module turns the index inequalities from finite overlap into the explicit
cardinality bound used in Littlewood--Paley arguments.

For a fixed active index `k`, every other active index belongs to

  [k - 2, k + 2] ∩ Nat,

which contains at most five natural numbers.
-/

import DGBOZK.Foundations.DyadicInteractionSumCore

set_option autoImplicit false

namespace DGBOZK
namespace Foundations
namespace DyadicActiveCardinalityCore

open DyadicInteractionSumCore

/--
The finite set of natural-number indices within two positions of `k`.
-/
def nearDyadicIndexSet (k : ℕ) : Finset ℕ :=
  Finset.Icc (k - 2) (k + 2)

/--
Membership in the explicit finite interval is equivalent to the interaction
window predicate.
-/
theorem mem_nearDyadicIndexSet_iff
    (k j : ℕ) :
    j ∈ nearDyadicIndexSet k
      ↔
    nearDyadicIndex k j := by
  simp only [
    nearDyadicIndexSet,
    Finset.mem_Icc,
    nearDyadicIndex
  ]
  omega

/--
The interaction window contains at most five natural-number indices.
Near the origin it can contain fewer because natural-number subtraction is
truncated.
-/
theorem nearDyadicIndexSet_card_le_five
    (k : ℕ) :
    (nearDyadicIndexSet k).card ≤ 5 := by
  unfold nearDyadicIndexSet
  rw [Nat.card_Icc]
  omega

/--
If the kth band is active, all active indices in any finite collection lie in
the five-position interaction window around `k`.
-/
theorem active_indices_subset_nearDyadicIndexSet
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace)
    (indices : Finset ℕ)
    (hk :
      dyadicBandSymbol chi alpha k zeta ≠ 0) :
    indices.filter
        (fun j =>
          dyadicBandSymbol chi alpha j zeta ≠ 0)
      ⊆
    nearDyadicIndexSet k := by
  classical
  intro j hj
  have hjActive :
      dyadicBandSymbol chi alpha j zeta ≠ 0 :=
    (Finset.mem_filter.mp hj).2
  exact
    (mem_nearDyadicIndexSet_iff k j).2
      (nearDyadicIndex_of_both_active
        chi alpha k j zeta hk hjActive)

/--
At a fixed frequency, any finite collection contains at most five active
dyadic indices, provided one active reference index is specified.
-/
theorem active_indices_card_le_five
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace)
    (indices : Finset ℕ)
    (hk :
      dyadicBandSymbol chi alpha k zeta ≠ 0) :
    (indices.filter
        (fun j =>
          dyadicBandSymbol chi alpha j zeta ≠ 0)).card
      ≤
    5 := by
  calc
    (indices.filter
        (fun j =>
          dyadicBandSymbol chi alpha j zeta ≠ 0)).card
        ≤
      (nearDyadicIndexSet k).card :=
        Finset.card_le_card
          (active_indices_subset_nearDyadicIndexSet
            chi alpha k zeta indices hk)
    _ ≤ 5 :=
      nearDyadicIndexSet_card_le_five k

/--
The explicit cardinality bound for the canonical smooth cutoff profile.
-/
theorem standard_active_indices_card_le_five
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace)
    (indices : Finset ℕ)
    (hk :
      dyadicBandSymbol
        standardSmoothCutoffProfile alpha k zeta ≠ 0) :
    (indices.filter
        (fun j =>
          dyadicBandSymbol
            standardSmoothCutoffProfile alpha j zeta ≠ 0)).card
      ≤
    5 :=
  active_indices_card_le_five
    standardSmoothCutoffProfile
    alpha k zeta indices hk

end DyadicActiveCardinalityCore
end Foundations
end DGBOZK
