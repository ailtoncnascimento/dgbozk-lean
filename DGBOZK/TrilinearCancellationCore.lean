/-
# Exact trilinear cancellation

This module formalizes the purely algebraic identity appearing as
`lem:trilinear` and `eq:trilinear-master` in the cleaned manuscript.

The trilinear functionals `T` and `Tprime` are abstract. The proof assumes
exactly the two identities corresponding to differentiation in the transverse
and longitudinal variables:

* the sum of the three transverse derivatives is zero;
* the sum of the three longitudinal derivatives is `-Tprime`.

It also assumes that the two abstract derivative operations commute.

The theorem does not construct the Fourier multiplier, justify integration by
parts, or prove analytic bounds for any resulting term.
-/

import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace DGBOZK
namespace TrilinearCancellationCore

section AbstractIdentity

variable {R V : Type*} [CommRing R]

/--
Abstract version of the exact trilinear cancellation.

`dx` and `dy` represent the two Cartesian derivatives, while `Tprime`
represents the functional obtained by differentiating the spatial weight.
The operator `D = dx ∘ dy ∘ dy` is written explicitly in the statement.
-/
theorem exact_trilinear_cancellation
    {T Tprime : V → V → V → R}
    {dx dy : V → V}
    (hdy :
      ∀ u v w,
        T (dy u) v w
          + T u (dy v) w
          + T u v (dy w)
        = 0)
    (hdx :
      ∀ u v w,
        T (dx u) v w
          + T u (dx v) w
          + T u v (dx w)
        = -Tprime u v w)
    (hcomm :
      ∀ u, dy (dx u) = dx (dy u))
    (f g h : V) :
    2 * T (dy f) (dx (dy g)) h
        +
      (T (dx (dy (dy f))) g h
        + T f (dx (dy (dy g))) h
        + T f g (dx (dy (dy h))))
      =
    -2 * T (dy (dy f)) (dx g) h
      - T (dy (dy f)) g (dx h)
      + T (dx f) (dy g) (dy h)
      + T (dx (dy f)) g (dy h)
      - Tprime (dy (dy f)) g h
      + Tprime (dy f) g (dy h)
      + Tprime f (dy g) (dy h) := by
  have hy₁ := hdy (dy f) (dx g) h
  have hy₂ := hdy f (dx (dy g)) h
  have hy₃ := hdy f g (dx (dy h))

  have hx₁ := hdx f (dy g) (dy h)
  have hx₂ := hdx (dy f) g (dy h)
  have hx₃ := hdx (dy (dy f)) g h

  simp only [hcomm] at hy₁ hy₂ hy₃

  linear_combination
    hy₁ + hy₂ + hy₃ - hx₁ - hx₂ + hx₃

end AbstractIdentity

end TrilinearCancellationCore
end DGBOZK
