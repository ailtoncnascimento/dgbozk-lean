import DGBOZK.Foundations.FourierConvention
import Mathlib.Tactic

/-!
# Bridge between the DGBOZK and Mathlib Fourier conventions

This file proves that the manuscript Fourier transform

  f̂(ξ,η) = ∫ exp(-i(xξ+yη)) f(x,y) dx dy

agrees with Mathlib's Fourier integral after rescaling the frequency by
`1 / (2π)`.

This is an equality of the defining Bochner integrals. No Fourier inversion
or Plancherel theorem is asserted in this file.
-/

set_option autoImplicit false

open MeasureTheory

namespace DGBOZK
namespace Foundations

/-- On the real Euclidean plane, Mathlib's inner product is exactly the
coordinate pairing used in the manuscript. -/
theorem euclideanInner_eq_phasePairing
    (z : PhysicalSpace) (ζ : FrequencySpace) :
    inner ℝ z ζ = phasePairing z ζ := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, phasePairing,
    xCoord, yCoord, xiCoord, etaCoord]
  ring

/-- Rescaling the frequency by `1 / (2π)` rescales the Euclidean pairing by
the same factor. -/
theorem inner_toMathlibFrequency
    (z : PhysicalSpace) (ζ : FrequencySpace) :
    inner ℝ z (toMathlibFrequency ζ) =
      phasePairing z ζ / twoPi := by
  rw [euclideanInner_eq_phasePairing]
  simp only [phasePairing, xiCoord_toMathlibFrequency,
    etaCoord_toMathlibFrequency]
  ring

/-- The real exponent in Mathlib's Fourier kernel becomes the negative
manuscript phase after frequency rescaling. -/
theorem scaledInner_toMathlibFrequency
    (z : PhysicalSpace) (ζ : FrequencySpace) :
    -2 * Real.pi * inner ℝ z (toMathlibFrequency ζ) =
      -phasePairing z ζ := by
  rw [inner_toMathlibFrequency]
  calc
    -2 * Real.pi * (phasePairing z ζ / twoPi) =
        -twoPi * (phasePairing z ζ / twoPi) := by
      simp [twoPi]
    _ = -phasePairing z ζ := by
      field_simp [twoPi_ne_zero]
      ring

/-- Equality of the complex exponents appearing in the two conventions. -/
theorem mathlibExponent_eq_paperExponent
    (z : PhysicalSpace) (ζ : FrequencySpace) :
    (↑(-2 * Real.pi *
        inner ℝ z (toMathlibFrequency ζ)) : ℂ) * Complex.I =
      -Complex.I * (phasePairing z ζ : ℂ) := by
  rw [scaledInner_toMathlibFrequency]
  push_cast
  ring

/-- Mathlib's Fourier kernel at the rescaled frequency is the manuscript's
negative plane wave. -/
@[simp] theorem mathlibKernel_eq_negativePlaneWave
    (z : PhysicalSpace) (ζ : FrequencySpace) :
    Complex.exp
        ((↑(-2 * Real.pi *
          inner ℝ z (toMathlibFrequency ζ)) : ℂ) * Complex.I) =
      negativePlaneWave z ζ := by
  rw [mathlibExponent_eq_paperExponent]
  rfl

/-- The DGBOZK Fourier transform of a Schwartz function agrees exactly with
Mathlib's Fourier integral evaluated at the rescaled frequency. -/
theorem paperFourierSchwartz_eq_mathlibFourierAtPaperFrequency
    (f : TestFunction) (ζ : FrequencySpace) :
    paperFourierSchwartz f ζ =
      mathlibFourierAtPaperFrequency f ζ := by
  unfold paperFourierSchwartz
  unfold paperFourier
  unfold mathlibFourierAtPaperFrequency
  rw [Real.fourierIntegral_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro z
  simp only [mathlibKernel_eq_negativePlaneWave, smul_eq_mul]

end Foundations
end DGBOZK
