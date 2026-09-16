import DGBOZK.Foundations.FourierBridge
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Fourier inversion for the DGBOZK convention

This file connects the manuscript Fourier convention

  f̂(ξ, η) = ∫ exp(-i(xξ + yη)) f(x,y) dx dy

with Mathlib's convention

  𝓕f(w) = ∫ exp(-2πi⟪z,w⟫) f(z) dz.

The frequency coordinates are related by

  (ξ,η) = 2π w.

The present module records:

* the two-dimensional frequency-space dimension;
* the frequency dilation identities;
* the corresponding Haar-integral scaling formula;
* integrability of the Mathlib Fourier transform of a Schwartz function;
* Fourier inversion for Schwartz functions.

The final manuscript-normalized inversion identity is obtained by combining
these results with the positive-kernel bridge and the factor `(2π)⁻²`.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace DGBOZK
namespace Foundations

/-- The DGBOZK physical space has real dimension two. -/
@[simp] theorem finrank_physicalSpace :
    Module.finrank ℝ PhysicalSpace = 2 := by
  simp [PhysicalSpace]

/-- The DGBOZK frequency space has real dimension two. -/
@[simp] theorem finrank_frequencySpace :
    Module.finrank ℝ FrequencySpace = 2 := by
  simp [FrequencySpace]

/--
Passing from Mathlib frequency coordinates to manuscript coordinates is
multiplication by `2π`.
-/
@[simp] theorem fromMathlibFrequency_eq_twoPi_smul
    (w : FrequencySpace) :
    fromMathlibFrequency w = twoPi • w := by
  ext i
  fin_cases i <;>
    simp [fromMathlibFrequency, frequencyPoint, xiCoord, etaCoord]

/--
Passing from manuscript frequency coordinates to Mathlib coordinates is
multiplication by `(2π)⁻¹`.
-/
@[simp] theorem toMathlibFrequency_eq_twoPi_inv_smul
    (ζ : FrequencySpace) :
    toMathlibFrequency ζ = twoPi⁻¹ • ζ := by
  ext i
  fin_cases i <;>
    simp [toMathlibFrequency, frequencyPoint, xiCoord, etaCoord,
      div_eq_mul_inv, mul_comm]

/-- The two algebraically equivalent forms of the inverse-square factor. -/
@[simp] theorem twoPi_inv_sq :
    twoPi⁻¹ ^ 2 = (twoPi ^ 2)⁻¹ := by
  simp only [inv_pow]

/--
The change of variables `ζ = 2π w` in two-dimensional frequency space.

This is the precise Haar-measure identity responsible for the factor
`(2π)⁻²` in the manuscript inverse Fourier transform.
-/
theorem integral_comp_twoPi_smul
    (g : FrequencySpace → ℂ) :
    (∫ w, g (twoPi • w)) =
      (twoPi ^ 2)⁻¹ • ∫ ζ, g ζ := by
  simpa only [finrank_frequencySpace] using
    (MeasureTheory.Measure.integral_comp_smul_of_nonneg
      (volume : Measure FrequencySpace) g twoPi
      (hR := le_of_lt twoPi_pos))

/--
The reverse form of the two-dimensional change of variables, retained in the
form supplied directly by Mathlib.
-/
theorem integral_comp_twoPi_inv_smul
    (g : FrequencySpace → ℂ) :
    (∫ ζ, g (twoPi⁻¹ • ζ)) =
      |twoPi ^ 2| • ∫ w, g w := by
  simpa only [finrank_frequencySpace] using
    (MeasureTheory.Measure.integral_comp_inv_smul
      (volume : Measure FrequencySpace) g twoPi)

/--
The Mathlib Fourier transform of a DGBOZK Schwartz test function is
integrable.
-/
theorem mathlibFourierSchwartz_integrable
    (f : TestFunction) :
    Integrable (Real.fourierIntegral (fun z => f z)) := by
  exact (SchwartzMap.fourierTransformCLM ℂ f).integrable

/--
Mathlib Fourier inversion specialized to DGBOZK Schwartz test functions.
-/
theorem mathlib_fourier_inversion_schwartz
    (f : TestFunction) :
    Real.fourierIntegralInv
        (Real.fourierIntegral (fun z => f z)) =
      fun z => f z := by
  exact Continuous.fourier_inversion
    f.continuous
    f.integrable
    (mathlibFourierSchwartz_integrable f)

/--
At a frequency written in Mathlib coordinates, the manuscript transform
equals the ordinary Mathlib Fourier integral.
-/
theorem paperFourierSchwartz_fromMathlibFrequency
    (f : TestFunction) (w : FrequencySpace) :
    paperFourierSchwartz f (fromMathlibFrequency w) =
      Real.fourierIntegral (fun z => f z) w := by
  rw [paperFourierSchwartz_eq_mathlibFourierAtPaperFrequency]
  unfold mathlibFourierAtPaperFrequency
  rw [toMathlibFrequency_fromMathlibFrequency]

/-- Under `ζ = 2π w`, the manuscript pairing is Mathlib's inverse phase. -/
theorem phasePairing_fromMathlibFrequency
    (z : PhysicalSpace) (w : FrequencySpace) :
    phasePairing z (fromMathlibFrequency w) =
      twoPi * inner ℝ w z := by
  rw [euclideanInner_eq_phasePairing]
  unfold phasePairing
  rw [xiCoord_fromMathlibFrequency, etaCoord_fromMathlibFrequency]
  unfold xCoord yCoord xiCoord etaCoord
  ring

theorem positivePlaneWave_fromMathlibFrequency
    (z : PhysicalSpace) (w : FrequencySpace) :
    positivePlaneWave z (fromMathlibFrequency w) =
      Complex.exp
        (((2 * Real.pi * inner ℝ w z : ℝ) : ℂ) * Complex.I) := by
  unfold positivePlaneWave
  rw [phasePairing_fromMathlibFrequency]
  have hscale :
      twoPi * inner ℝ w z =
        2 * Real.pi * inner ℝ w z := by
    rfl
  rw [hscale]
  congr 1
  exact mul_comm _ _

theorem mathlibFourierIntegralInv_eq_paperKernel
    (g : FrequencySpace → ℂ) (z : PhysicalSpace) :
    Real.fourierIntegralInv g z =
      ∫ w, positivePlaneWave z (fromMathlibFrequency w) * g w := by
  rw [Real.fourierIntegralInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro w
  change
    Complex.exp
        ((↑(2 * Real.pi * inner ℝ w z) : ℂ) * Complex.I) • g w =
      positivePlaneWave z (fromMathlibFrequency w) * g w
  rw [positivePlaneWave_fromMathlibFrequency]
  simp only [smul_eq_mul]

/-- Fourier inversion in Mathlib frequency coordinates. -/
theorem rescaled_paperFourier_inversion
    (f : TestFunction) (z : PhysicalSpace) :
    Real.fourierIntegralInv
        (fun w => paperFourierSchwartz f (fromMathlibFrequency w)) z =
      f z := by
  have htransform :
      (fun w => paperFourierSchwartz f (fromMathlibFrequency w)) =
        Real.fourierIntegral (fun x => f x) := by
    funext w
    exact paperFourierSchwartz_fromMathlibFrequency f w
  rw [htransform]
  exact congrFun (mathlib_fourier_inversion_schwartz f) z

/-- The rescaled positive-kernel integral reconstructs a Schwartz function. -/
theorem integral_rescaled_paperFourier_inversion
    (f : TestFunction) (z : PhysicalSpace) :
    (∫ w,
        positivePlaneWave z (fromMathlibFrequency w) *
          paperFourierSchwartz f (fromMathlibFrequency w)) =
      f z := by
  rw [← mathlibFourierIntegralInv_eq_paperKernel]
  exact rescaled_paperFourier_inversion f z

/--
The manuscript-normalized Fourier inversion formula at the integral level.

The factor `(2π)⁻²` follows from the dimension-two Haar-measure change of
variables `ζ = 2π w`.
-/
theorem normalized_paperFourier_inversion
    (f : TestFunction) (z : PhysicalSpace) :
    (twoPi ^ 2)⁻¹ •
        (∫ ζ,
          positivePlaneWave z ζ *
            paperFourierSchwartz f ζ) =
      f z := by
  let G : FrequencySpace → ℂ :=
    fun ζ =>
      positivePlaneWave z ζ *
        paperFourierSchwartz f ζ
  change (twoPi ^ 2)⁻¹ • (∫ ζ, G ζ) = f z
  rw [← integral_comp_twoPi_smul G]
  simpa only [G, fromMathlibFrequency_eq_twoPi_smul] using
    (integral_rescaled_paperFourier_inversion f z)

/-- Exact Fourier inversion in the normalization printed in the manuscript. -/
@[simp] theorem paperInverseFourier_paperFourierSchwartz
    (f : TestFunction) (z : PhysicalSpace) :
    paperInverseFourier (paperFourierSchwartz f) z = f z := by
  simpa [paperInverseFourier, paperInverseFourierIntegral,
    inverseFourierNormalization, twoPi_inv_sq, Algebra.smul_def] using
    (normalized_paperFourier_inversion f z)

end Foundations
end DGBOZK
