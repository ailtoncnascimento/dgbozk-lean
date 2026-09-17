/-
# Bounded pointwise multipliers and the abstract Plancherel bridge

This module proves the concrete measure-theoretic estimate underlying an
L2 Fourier multiplier:

  ‖m(x) f(x)‖ <= C ‖f(x)‖

almost everywhere implies

  ‖m f‖_{Lp} <= C ‖f‖_{Lp},

and in particular multiplication by an essentially bounded symbol preserves
`MemLp`.

The final theorem records the elementary conjugation argument: if a forward
transform and its inverse preserve norms, then conjugating a bounded frequency
operator by them preserves the same operator bound.

The pinned Mathlib does not currently provide a Euclidean L2 Fourier-transform
isometry on `R^2`. Consequently, this file does not claim that the abstract
norm-preserving maps are realized by the manuscript Fourier transform.
-/

import DGBOZK.Foundations.SmoothCutoffConstruction
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory

namespace DGBOZK
namespace Foundations
namespace L2MultiplierCore

section PointwiseMultiplier

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X}
variable {p : ENNReal}

/--
A uniform almost-everywhere bound on a complex symbol produces the
corresponding pointwise product bound.
-/
theorem pointwise_product_norm_bound
    {m f : X → ℂ} {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) :
    ∀ᵐ x ∂μ,
      ‖m x * f x‖ ≤ C * ‖f x‖ := by
  filter_upwards [hbound] with x hx
  rw [norm_mul]
  exact
    mul_le_mul_of_nonneg_right
      hx
      (norm_nonneg (f x))

/--
Multiplication by a measurable essentially bounded complex symbol preserves
`MemLp`.
-/
theorem bounded_pointwise_multiplier_memLp
    {m f : X → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable m μ)
    (hf : MemLp f p μ)
    (hbound : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) :
    MemLp (fun x => m x * f x) p μ := by
  exact
    MemLp.of_le_mul
      hf
      (hm.mul hf.aestronglyMeasurable)
      (pointwise_product_norm_bound hbound)

/--
The seminorm of a product with an essentially bounded symbol is at most the
symbol bound times the original seminorm.
-/
theorem eLpNorm_bounded_pointwise_multiplier_le
    {m f : X → ℂ} {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) :
    eLpNorm (fun x => m x * f x) p μ
      ≤
    ENNReal.ofReal C * eLpNorm f p μ := by
  exact
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (pointwise_product_norm_bound hbound)
      p

/--
The `L2` specialization of bounded pointwise multiplication.
-/
theorem bounded_pointwise_multiplier_memLp_two
    {m f : X → ℂ} {C : ℝ}
    (hm : AEStronglyMeasurable m μ)
    (hf : MemLp f 2 μ)
    (hbound : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) :
    MemLp (fun x => m x * f x) 2 μ := by
  exact
    bounded_pointwise_multiplier_memLp
      hm hf hbound

/--
The `L2` seminorm estimate for a bounded pointwise multiplier.
-/
theorem eLpNorm_two_bounded_pointwise_multiplier_le
    {m f : X → ℂ} {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) :
    eLpNorm (fun x => m x * f x) 2 μ
      ≤
    ENNReal.ofReal C * eLpNorm f 2 μ := by
  exact
    eLpNorm_bounded_pointwise_multiplier_le
      hbound

end PointwiseMultiplier

section AbstractPlancherel

variable {PhysicalL2 FrequencyL2 : Type*}
variable [NormedAddCommGroup PhysicalL2]
variable [NormedAddCommGroup FrequencyL2]

/--
Abstract Plancherel conjugation principle.

If the forward and inverse transforms preserve norms and the frequency-side
operator has bound `C`, then the conjugated physical-side operator has the
same bound.

No existence of the transforms is asserted by this theorem.
-/
theorem norm_conjugated_operator_le
    (forward : PhysicalL2 → FrequencyL2)
    (inverse : FrequencyL2 → PhysicalL2)
    (multiplier : FrequencyL2 → FrequencyL2)
    (C : ℝ)
    (hforward :
      ∀ f, ‖forward f‖ = ‖f‖)
    (hinverse :
      ∀ g, ‖inverse g‖ = ‖g‖)
    (hmultiplier :
      ∀ g, ‖multiplier g‖ ≤ C * ‖g‖)
    (f : PhysicalL2) :
    ‖inverse (multiplier (forward f))‖
      ≤
    C * ‖f‖ := by
  calc
    ‖inverse (multiplier (forward f))‖
        =
      ‖multiplier (forward f)‖ :=
        hinverse _
    _ ≤ C * ‖forward f‖ :=
      hmultiplier _
    _ = C * ‖f‖ := by
      rw [hforward]

end AbstractPlancherel

end L2MultiplierCore
end Foundations
end DGBOZK
