import DGBOZK.Foundations.Coordinates
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# Fourier-transform convention used by DGBOZK

The manuscript uses

`f̂(ξ,η) = ∫ exp(-i (x ξ + y η)) f(x,y) dx dy`

and the inverse normalization `(2π)⁻²`. Mathlib uses an exponent containing
`-2π i`. Consequently, manuscript frequency `ζ` corresponds to Mathlib
frequency `ζ/(2π)`. This file records that conversion explicitly.

No Fourier inversion or Plancherel theorem is asserted here. Those theorems
must be proved later from Mathlib's Schwartz-space Fourier API using the maps
defined below.
-/

set_option autoImplicit false

open MeasureTheory

namespace DGBOZK
namespace Foundations

/-- The nonzero scale relating the manuscript and Mathlib conventions. -/
noncomputable def twoPi : ℝ := 2 * Real.pi

theorem twoPi_ne_zero : twoPi ≠ 0 := by
  dsimp [twoPi]
  positivity

theorem twoPi_pos : 0 < twoPi := by
  dsimp [twoPi]
  positivity

/-- Convert a manuscript frequency `ζ` to Mathlib frequency `ζ/(2π)`. -/
noncomputable def toMathlibFrequency
    (ζ : FrequencySpace) : FrequencySpace :=
  frequencyPoint (xiCoord ζ / twoPi) (etaCoord ζ / twoPi)

/-- Convert a Mathlib frequency `w` to manuscript frequency `2πw`. -/
noncomputable def fromMathlibFrequency
    (w : FrequencySpace) : FrequencySpace :=
  frequencyPoint (twoPi * xiCoord w) (twoPi * etaCoord w)

@[simp] theorem xiCoord_toMathlibFrequency (ζ : FrequencySpace) :
    xiCoord (toMathlibFrequency ζ) = xiCoord ζ / twoPi := by
  simp [toMathlibFrequency]

@[simp] theorem etaCoord_toMathlibFrequency (ζ : FrequencySpace) :
    etaCoord (toMathlibFrequency ζ) = etaCoord ζ / twoPi := by
  simp [toMathlibFrequency]

@[simp] theorem xiCoord_fromMathlibFrequency (w : FrequencySpace) :
    xiCoord (fromMathlibFrequency w) = twoPi * xiCoord w := by
  simp [fromMathlibFrequency]

@[simp] theorem etaCoord_fromMathlibFrequency (w : FrequencySpace) :
    etaCoord (fromMathlibFrequency w) = twoPi * etaCoord w := by
  simp [fromMathlibFrequency]

@[simp] theorem fromMathlibFrequency_toMathlibFrequency
    (ζ : FrequencySpace) :
    fromMathlibFrequency (toMathlibFrequency ζ) = ζ := by
  ext i
  fin_cases i
  · change xiCoord (fromMathlibFrequency (toMathlibFrequency ζ)) = xiCoord ζ
    rw [xiCoord_fromMathlibFrequency, xiCoord_toMathlibFrequency]
    field_simp [twoPi_ne_zero]
  · change etaCoord (fromMathlibFrequency (toMathlibFrequency ζ)) = etaCoord ζ
    rw [etaCoord_fromMathlibFrequency, etaCoord_toMathlibFrequency]
    field_simp [twoPi_ne_zero]

@[simp] theorem toMathlibFrequency_fromMathlibFrequency
    (w : FrequencySpace) :
    toMathlibFrequency (fromMathlibFrequency w) = w := by
  ext i
  fin_cases i
  · change xiCoord (toMathlibFrequency (fromMathlibFrequency w)) = xiCoord w
    rw [xiCoord_toMathlibFrequency, xiCoord_fromMathlibFrequency]
    field_simp [twoPi_ne_zero]
  · change etaCoord (toMathlibFrequency (fromMathlibFrequency w)) = etaCoord w
    rw [etaCoord_toMathlibFrequency, etaCoord_fromMathlibFrequency]
    field_simp [twoPi_ne_zero]

/-- The manuscript kernel `exp(-i (x ξ + y η))`. -/
noncomputable def negativePlaneWave
    (z : PhysicalSpace) (ζ : FrequencySpace) : ℂ :=
  Complex.exp (-Complex.I * (phasePairing z ζ : ℂ))

/-- The inverse-transform kernel `exp(+i (x ξ + y η))`. -/
noncomputable def positivePlaneWave
    (z : PhysicalSpace) (ζ : FrequencySpace) : ℂ :=
  Complex.exp (Complex.I * (phasePairing z ζ : ℂ))

@[simp] theorem negativePlaneWave_zero_frequency
    (z : PhysicalSpace) :
    negativePlaneWave z (0 : FrequencySpace) = 1 := by
  simp [negativePlaneWave]

@[simp] theorem positivePlaneWave_zero_frequency
    (z : PhysicalSpace) :
    positivePlaneWave z (0 : FrequencySpace) = 1 := by
  simp [positivePlaneWave]

@[simp] theorem negativePlaneWave_zero_point
    (ζ : FrequencySpace) :
    negativePlaneWave (0 : PhysicalSpace) ζ = 1 := by
  simp [negativePlaneWave]

@[simp] theorem positivePlaneWave_zero_point
    (ζ : FrequencySpace) :
    positivePlaneWave (0 : PhysicalSpace) ζ = 1 := by
  simp [positivePlaneWave]

/-- Direct definition of the manuscript Fourier transform.

For a non-integrable function, this uses Mathlib's standard convention for the
Bochner integral. Analytic theorems will therefore carry the appropriate
integrability or Schwartz hypotheses.
-/
noncomputable def paperFourier
    (f : PhysicalSpace → ℂ) (ζ : FrequencySpace) : ℂ :=
  ∫ z, negativePlaneWave z ζ * f z

/-- The unnormalized integral in the manuscript inverse Fourier transform. -/
noncomputable def paperInverseFourierIntegral
    (g : FrequencySpace → ℂ) (z : PhysicalSpace) : ℂ :=
  ∫ ζ, positivePlaneWave z ζ * g ζ

/-- The two-dimensional inverse Fourier normalization `(2π)⁻²`. -/
noncomputable def inverseFourierNormalization : ℝ :=
  twoPi⁻¹ ^ 2

/-- Direct definition of the manuscript inverse Fourier transform. -/
noncomputable def paperInverseFourier
    (g : FrequencySpace → ℂ) (z : PhysicalSpace) : ℂ :=
  (inverseFourierNormalization : ℂ) *
    paperInverseFourierIntegral g z

@[simp] theorem paperFourier_zero (ζ : FrequencySpace) :
    paperFourier (fun _ => 0) ζ = 0 := by
  simp [paperFourier]

theorem paperFourier_zero_frequency
    (f : PhysicalSpace → ℂ) :
    paperFourier f (0 : FrequencySpace) = ∫ z, f z := by
  simp [paperFourier]

@[simp] theorem paperInverseFourierIntegral_zero
    (z : PhysicalSpace) :
    paperInverseFourierIntegral (fun _ => 0) z = 0 := by
  simp [paperInverseFourierIntegral]

@[simp] theorem paperInverseFourier_zero
    (z : PhysicalSpace) :
    paperInverseFourier (fun _ => 0) z = 0 := by
  simp [paperInverseFourier]

/-- The manuscript transform specialized to Schwartz test functions. -/
noncomputable def paperFourierSchwartz
    (f : TestFunction) (ζ : FrequencySpace) : ℂ :=
  paperFourier (fun z => f z) ζ

/-- Mathlib's Fourier transform evaluated at the rescaled manuscript
frequency. This is the object to identify with `paperFourierSchwartz` in the
next formalization step.
-/
noncomputable def mathlibFourierAtPaperFrequency
    (f : TestFunction) (ζ : FrequencySpace) : ℂ :=
  Real.fourierIntegral
    (fun z => f z)
    (toMathlibFrequency ζ)

end Foundations
end DGBOZK
