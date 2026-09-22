/-
# Separation of anisotropic dyadic annuli

This module proves the geometric core of finite dyadic overlap.

If two annular scales `H` and `K` satisfy

  2 H < K / 2,

then the corresponding closed anisotropic annuli have no common frequency.
Consequently, band-pass symbols at those scales have pointwise zero product.

The conversion from an index gap such as `k + 3 <= j` to the displayed scale
separation is deliberately deferred to the next arithmetic module.
-/

import DGBOZK.Foundations.DyadicProjectorL2Core

set_option autoImplicit false

namespace DGBOZK
namespace Foundations
namespace DyadicAnnulusSeparationCore

/--
Two annuli with strictly separated radial ranges cannot contain the same
frequency.
-/
theorem no_common_frequency_of_separated_annuli
    {alpha H K : ℝ}
    {zeta : FrequencySpace}
    (hseparation : 2 * H < K / 2)
    (hzetaH : zeta ∈ dyadicAnnulus alpha H)
    (hzetaK : zeta ∈ dyadicAnnulus alpha K) :
    False := by
  have hUpper :
      anisotropicSymbol alpha zeta ≤ 2 * H :=
    hzetaH.2
  have hLower :
      K / 2 ≤ anisotropicSymbol alpha zeta :=
    hzetaK.1
  linarith

/--
Band-pass symbols at strictly separated positive scales have pointwise zero
product.
-/
theorem bandPassSymbol_mul_eq_zero_of_separated
    (chi : SmoothCutoffProfile)
    (alpha H K : ℝ)
    (zeta : FrequencySpace)
    (hH : 0 < H)
    (hK : 0 < K)
    (hseparation : 2 * H < K / 2) :
    bandPassSymbol chi alpha H zeta
        * bandPassSymbol chi alpha K zeta
      =
    0 := by
  by_cases hleft :
      bandPassSymbol chi alpha H zeta = 0
  · simp [hleft]
  by_cases hright :
      bandPassSymbol chi alpha K zeta = 0
  · simp [hright]
  exfalso
  have hzetaH :
      zeta ∈ dyadicAnnulus alpha H :=
    bandPassActiveSet_subset_dyadicAnnulus
      chi hH hleft
  have hzetaK :
      zeta ∈ dyadicAnnulus alpha K :=
    bandPassActiveSet_subset_dyadicAnnulus
      chi hK hright
  exact
    no_common_frequency_of_separated_annuli
      hseparation hzetaH hzetaK

/--
Dyadic band symbols have zero product whenever their associated annular
scales satisfy the strict separation inequality.
-/
theorem dyadicBandSymbol_mul_eq_zero_of_separated
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k j : ℕ)
    (zeta : FrequencySpace)
    (hseparation :
      2 * dyadicScale (k + 1)
        <
      dyadicScale (j + 1) / 2) :
    dyadicBandSymbol chi alpha k zeta
        * dyadicBandSymbol chi alpha j zeta
      =
    0 := by
  simpa only [dyadicBandSymbol_eq_bandPassSymbol] using
    bandPassSymbol_mul_eq_zero_of_separated
      chi
      alpha
      (dyadicScale (k + 1))
      (dyadicScale (j + 1))
      zeta
      (dyadicScale_pos (k + 1))
      (dyadicScale_pos (j + 1))
      hseparation

/--
Under scale separation, two dyadic symbols cannot both be nonzero at the same
frequency.
-/
theorem no_common_active_frequency_of_separated_dyadic_bands
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k j : ℕ)
    (zeta : FrequencySpace)
    (hseparation :
      2 * dyadicScale (k + 1)
        <
      dyadicScale (j + 1) / 2)
    (hk :
      dyadicBandSymbol chi alpha k zeta ≠ 0)
    (hj :
      dyadicBandSymbol chi alpha j zeta ≠ 0) :
    False := by
  exact
    (mul_ne_zero hk hj)
      (dyadicBandSymbol_mul_eq_zero_of_separated
        chi alpha k j zeta hseparation)

/--
The pointwise orthogonality statement is symmetric in the two dyadic bands.
-/
theorem dyadicBandSymbol_reverse_mul_eq_zero_of_separated
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k j : ℕ)
    (zeta : FrequencySpace)
    (hseparation :
      2 * dyadicScale (k + 1)
        <
      dyadicScale (j + 1) / 2) :
    dyadicBandSymbol chi alpha j zeta
        * dyadicBandSymbol chi alpha k zeta
      =
    0 := by
  rw [mul_comm]
  exact
    dyadicBandSymbol_mul_eq_zero_of_separated
      chi alpha k j zeta hseparation

end DyadicAnnulusSeparationCore
end Foundations
end DGBOZK
