/-
# Dyadic projector L2 core

This module connects the constructed anisotropic dyadic cutoff symbols with
the bounded pointwise multiplier estimates.

It proves:

* the complexified dyadic band symbol is bounded in norm by one;
* its nonzero set lies in the expected anisotropic dyadic annulus;
* multiplication by this symbol is contractive at the `eLpNorm` level;
* it preserves `MemLp` once measurability of the symbol is supplied; and
* an abstract norm-preserving Fourier transform transports the frequency-side
  contraction to the corresponding physical-space projector.

The last result is deliberately abstract. The pinned Mathlib does not provide
the Euclidean Plancherel realization required to instantiate the forward and
inverse maps for the manuscript's Fourier transform.
-/

import DGBOZK.Foundations.L2MultiplierCore

set_option autoImplicit false

open MeasureTheory

namespace DGBOZK
namespace Foundations
namespace DyadicProjectorL2Core

open L2MultiplierCore

/--
The real dyadic band symbol, regarded as a complex-valued Fourier multiplier.
-/
noncomputable def complexDyadicBandSymbol
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace) : ℂ :=
  (dyadicBandSymbol chi alpha k zeta : ℂ)

/--
Every complexified dyadic band symbol has pointwise norm at most one.

This uses only the interval bound `[-1,1]` for the real band-pass symbol; no
monotonicity hypothesis on the cutoff profile is required.
-/
theorem complexDyadicBandSymbol_norm_le_one
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (zeta : FrequencySpace) :
    ‖complexDyadicBandSymbol chi alpha k zeta‖ ≤ 1 := by
  have hLower :
      -1 ≤ dyadicBandSymbol chi alpha k zeta := by
    rw [dyadicBandSymbol_eq_bandPassSymbol]
    exact
      neg_one_le_bandPassSymbol
        chi alpha (dyadicScale (k + 1)) zeta
  have hUpper :
      dyadicBandSymbol chi alpha k zeta ≤ 1 := by
    rw [dyadicBandSymbol_eq_bandPassSymbol]
    exact
      bandPassSymbol_le_one
        chi alpha (dyadicScale (k + 1)) zeta
  have hAbs :
      |dyadicBandSymbol chi alpha k zeta| ≤ 1 :=
    abs_le.mpr ⟨hLower, hUpper⟩
  simpa [complexDyadicBandSymbol, Complex.norm_real] using hAbs

/--
The nonzero complex multiplier is confined to the same annulus as the
underlying real dyadic symbol.
-/
theorem complexDyadicBandSymbol_active_subset_dyadicAnnulus
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ) :
    {zeta |
        complexDyadicBandSymbol chi alpha k zeta ≠ 0}
      ⊆
    dyadicAnnulus alpha (dyadicScale (k + 1)) := by
  intro zeta hzeta
  apply dyadicBandActive_subset_dyadicAnnulus chi alpha k
  intro hzero
  apply hzeta
  simp [complexDyadicBandSymbol, hzero]

/--
Frequency-side multiplication by the complexified dyadic cutoff.
-/
noncomputable def dyadicBandMultiplier
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (f : FrequencySpace → ℂ) :
    FrequencySpace → ℂ :=
  fun zeta =>
    complexDyadicBandSymbol chi alpha k zeta * f zeta

@[simp]
theorem dyadicBandMultiplier_apply
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (f : FrequencySpace → ℂ)
    (zeta : FrequencySpace) :
    dyadicBandMultiplier chi alpha k f zeta
      =
    complexDyadicBandSymbol chi alpha k zeta * f zeta :=
  rfl

/--
The frequency-side dyadic multiplier is contractive in the `L2` seminorm.
-/
theorem dyadicBandMultiplier_eLpNorm_two_le
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (μ : Measure FrequencySpace)
    (f : FrequencySpace → ℂ) :
    eLpNorm (dyadicBandMultiplier chi alpha k f) 2 μ
      ≤
    eLpNorm f 2 μ := by
  have hbound :
      ∀ᵐ zeta ∂μ,
        ‖complexDyadicBandSymbol chi alpha k zeta‖
          ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall
      (complexDyadicBandSymbol_norm_le_one chi alpha k)
  have hEstimate :=
    eLpNorm_two_bounded_pointwise_multiplier_le
      (μ := μ)
      (m := complexDyadicBandSymbol chi alpha k)
      (f := f)
      hbound
  simpa [dyadicBandMultiplier] using hEstimate

/--
The dyadic multiplier preserves `MemLp` at exponent two once strong
measurability of the multiplier is available.

The measurability assumption is explicit because this module is isolating the
multiplier estimate from the separate analytic realization of the cutoff.
-/
theorem dyadicBandMultiplier_memLp_two
    (chi : SmoothCutoffProfile)
    (alpha : ℝ)
    (k : ℕ)
    (μ : Measure FrequencySpace)
    (f : FrequencySpace → ℂ)
    (hsymbol :
      AEStronglyMeasurable
        (complexDyadicBandSymbol chi alpha k) μ)
    (hf : MemLp f 2 μ) :
    MemLp (dyadicBandMultiplier chi alpha k f) 2 μ := by
  have hbound :
      ∀ᵐ zeta ∂μ,
        ‖complexDyadicBandSymbol chi alpha k zeta‖
          ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall
      (complexDyadicBandSymbol_norm_le_one chi alpha k)
  exact
    bounded_pointwise_multiplier_memLp_two
      hsymbol hf hbound

/--
The canonical smooth dyadic multiplier is contractive in the `L2` seminorm.
-/
theorem standardDyadicBandMultiplier_eLpNorm_two_le
    (alpha : ℝ)
    (k : ℕ)
    (μ : Measure FrequencySpace)
    (f : FrequencySpace → ℂ) :
    eLpNorm
        (dyadicBandMultiplier
          standardSmoothCutoffProfile alpha k f)
        2 μ
      ≤
    eLpNorm f 2 μ :=
  dyadicBandMultiplier_eLpNorm_two_le
    standardSmoothCutoffProfile alpha k μ f

section AbstractPhysicalProjector

variable {PhysicalL2 FrequencyL2 : Type*}
variable [NormedAddCommGroup PhysicalL2]
variable [NormedAddCommGroup FrequencyL2]

/--
An abstract physical-space dyadic projector obtained by conjugating a
frequency-side multiplier with forward and inverse Fourier maps.
-/
def conjugatedDyadicProjector
    (forward : PhysicalL2 → FrequencyL2)
    (inverse : FrequencyL2 → PhysicalL2)
    (multiplier : FrequencyL2 → FrequencyL2)
    (f : PhysicalL2) :
    PhysicalL2 :=
  inverse (multiplier (forward f))

/--
A contractive frequency multiplier remains contractive after conjugation by
norm-preserving forward and inverse transforms.
-/
theorem conjugatedDyadicProjector_norm_le
    (forward : PhysicalL2 → FrequencyL2)
    (inverse : FrequencyL2 → PhysicalL2)
    (multiplier : FrequencyL2 → FrequencyL2)
    (hforward :
      ∀ f, ‖forward f‖ = ‖f‖)
    (hinverse :
      ∀ g, ‖inverse g‖ = ‖g‖)
    (hmultiplier :
      ∀ g, ‖multiplier g‖ ≤ ‖g‖)
    (f : PhysicalL2) :
    ‖conjugatedDyadicProjector
        forward inverse multiplier f‖
      ≤
    ‖f‖ := by
  have hmultiplierOne :
      ∀ g, ‖multiplier g‖ ≤ (1 : ℝ) * ‖g‖ := by
    intro g
    simpa using hmultiplier g
  have hEstimate :=
    norm_conjugated_operator_le
      forward
      inverse
      multiplier
      1
      hforward
      hinverse
      hmultiplierOne
      f
  simpa [conjugatedDyadicProjector] using hEstimate

end AbstractPhysicalProjector

end DyadicProjectorL2Core
end Foundations
end DGBOZK
