/-
# Finite overlap of anisotropic dyadic bands

This module converts separation of dyadic indices into separation of the
corresponding anisotropic annuli.

Because the kth band is supported where

  dyadicScale (k + 1) / 2 <= rho_alpha
    <= 2 * dyadicScale (k + 1),

bands whose indices differ by at least three have disjoint active sets.
Consequently, two simultaneously active dyadic bands have indices differing
by at most two.
-/

import DGBOZK.Foundations.DyadicAnnulusSeparationCore

set_option autoImplicit false

namespace DGBOZK
namespace Foundations
namespace DyadicFiniteOverlapCore

open DyadicAnnulusSeparationCore

/--
Three dyadic steps produce strict separation between the upper edge of the
lower annulus and the lower edge of the higher annulus.
-/
theorem dyadicScale_separated_three_steps
    (k : ℕ) :
    2 * dyadicScale (k + 1)
      <
    dyadicScale (k + 3 + 1) / 2 := by
  rw [dyadicScale_succ (k + 3)]
  rw [show k + 3 = (k + 2) + 1 by omega]
  rw [dyadicScale_succ (k + 2)]
  rw [show k + 2 = (k + 1) + 1 by omega]
  rw [dyadicScale_succ (k + 1)]
  nlinarith [dyadicScale_pos (k + 1)]

/--
Any index gap of at least three implies strict separation of the associated
annular scales.
-/
theorem dyadicScale_separated_of_three_le
    {k j : ℕ}
    (hgap : k + 3 ≤ j) :
    2 * dyadicScale (k + 1)
      <
    dyadicScale (j + 1) / 2 := by
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_add_of_le hgap
  induction d with
  | zero =>
      simpa using dyadicScale_separated_three_steps k
  | succ d ih =>
      have hindex :
          (k + 3 + (d + 1)) + 1
            =
          ((k + 3 + d) + 1) + 1 := by
        omega
      rw [hindex]
      rw [dyadicScale_succ ((k + 3 + d) + 1)]
      have ihBound :
          2 * dyadicScale (k + 1)
            <
          dyadicScale (k + 3 + d + 1) / 2 :=
        ih (by omega)
      have hScalePos :
          0 < dyadicScale (k + 3 + d + 1) :=
        dyadicScale_pos (k + 3 + d + 1)
      nlinarith

/--
Forward index separation forces the pointwise product of the two real dyadic
symbols to vanish.
-/
theorem dyadicBandSymbol_mul_eq_zero_of_three_le
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    {k j : ℕ}
    (zeta : FrequencySpace)
    (hgap : k + 3 ≤ j) :
    dyadicBandSymbol chi alpha k zeta
        * dyadicBandSymbol chi alpha j zeta
      =
    0 := by
  exact
    dyadicBandSymbol_mul_eq_zero_of_separated
      chi alpha k j zeta
      (dyadicScale_separated_of_three_le hgap)

/--
Separation in either index direction forces pointwise orthogonality.
-/
theorem dyadicBandSymbol_mul_eq_zero_of_index_separation
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k j : ℕ)
    (zeta : FrequencySpace)
    (hseparation :
      k + 3 ≤ j ∨ j + 3 ≤ k) :
    dyadicBandSymbol chi alpha k zeta
        * dyadicBandSymbol chi alpha j zeta
      =
    0 := by
  rcases hseparation with hforward | hreverse
  · exact
      dyadicBandSymbol_mul_eq_zero_of_three_le
        chi alpha zeta hforward
  · rw [mul_comm]
    exact
      dyadicBandSymbol_mul_eq_zero_of_three_le
        chi alpha zeta hreverse

/--
Two dyadic bands that are simultaneously active have indices within two of
each other.
-/
theorem active_dyadic_indices_within_two
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k j : ℕ)
    (zeta : FrequencySpace)
    (hk :
      dyadicBandSymbol chi alpha k zeta ≠ 0)
    (hj :
      dyadicBandSymbol chi alpha j zeta ≠ 0) :
    j ≤ k + 2 ∧ k ≤ j + 2 := by
  have hnotForward :
      ¬ k + 3 ≤ j := by
    intro hgap
    exact
      (mul_ne_zero hk hj)
        (dyadicBandSymbol_mul_eq_zero_of_three_le
          chi alpha zeta hgap)
  have hnotReverse :
      ¬ j + 3 ≤ k := by
    intro hgap
    exact
      (mul_ne_zero hj hk)
        (dyadicBandSymbol_mul_eq_zero_of_three_le
          chi alpha zeta hgap)
  omega

/--
Equivalent finite-overlap statement: at any fixed frequency, an active band
can interact only with the five index positions from two below to two above.
-/
theorem active_dyadic_index_bounds
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k j : ℕ)
    (zeta : FrequencySpace)
    (hk :
      dyadicBandSymbol chi alpha k zeta ≠ 0)
    (hj :
      dyadicBandSymbol chi alpha j zeta ≠ 0) :
    j ≤ k + 2 ∧ k ≤ j + 2 :=
  active_dyadic_indices_within_two
    chi alpha k j zeta hk hj

end DyadicFiniteOverlapCore
end Foundations
end DGBOZK
