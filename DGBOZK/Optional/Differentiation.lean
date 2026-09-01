/-
# OPTIONAL — discharging `[BB-DIFF]`

## ⚠ THIS FILE IS UNVERIFIED STARTER CODE. IT HAS NEVER BEEN COMPILED. ⚠

It is deliberately **not** imported by `DGBOZK.lean`, so it does not take part in
`lake build` and cannot break the verified core.  It is an exercise, with the
pieces laid out, not a result.

## What it is for

`[BB-DIFF]` is the one black box in this library that is not really "cited
literature" — it is the power rule.  In `DGBOZK/Phase.lean` and
`DGBOZK/Fold.lean` the partial derivatives of

  `ω_σ(ξ,η) = ξ(η² + σ|ξ|^α)`   and   `Ψ(ξ) = xξ + tξ^{α+1} − y²/(4tξ)`

are introduced as *definitions* matching the formulas the paper displays, rather
than derived.  That was forced by a build constraint, not by mathematics:
Mathlib's derivative theory for `Real.rpow`
(`Mathlib.Analysis.SpecialFunctions.Pow.Deriv`) transitively imports essentially
all of Mathlib, which could not be built from source in the environment where
this library was written.

In a Codespace with `lake exe cache get`, that constraint is gone.  Finishing
this file promotes `[BB-DIFF]` from *assumed* to *proved*, and closes the last
gap in the §3 chain.

## The one subtlety, stated up front

`s * s^α = s^{α+1}` holds only for `s > 0`.  So the phase is *not* globally equal
to `η²s + σ s^{α+1}`; it is equal to it only on the half-line `(0,∞)`.
`HasDerivAt` is a **local** property, so this is fine — but you must say so, with
`Filter.EventuallyEq` on a neighbourhood of `ξ` inside `(0,∞)`, and
`HasDerivAt.congr_of_eventuallyEq`.  This is the step where a first attempt
usually gets stuck.  `isOpen_Ioi.mem_nhds` gives you the neighbourhood.

## Suggested order of work

1. `hasDerivAt_rpow_succ` — the power rule for `s ↦ s^{α+1}`.  Should be almost
   immediate from `Real.hasDerivAt_rpow_const`.
2. `hasDerivAt_omega_fst` — `∂_ξ ω_σ = velX`.  This is where the
   `EventuallyEq` step lives.
3. `hasDerivAt_omega_snd` — `∂_η ω_σ = velY`.  Easy: for fixed `ξ` the map is a
   polynomial in `η`.
4. The second derivatives, then `Ψ''` and `Ψ'''`.

When each `sorry` is gone, delete the corresponding `[BB-DIFF]` marker from the
docstring in `DGBOZK/BlackBoxes.lean` and re-run `DGBOZK/Audit.lean`.

## Lemmas you will want

* `Real.hasDerivAt_rpow_const : (x ≠ 0 ∨ 1 ≤ p) → HasDerivAt (· ^ p) (p * x ^ (p - 1)) x`
* `HasDerivAt.congr_of_eventuallyEq`
* `Filter.eventuallyEq_of_mem`, `isOpen_Ioi.mem_nhds`
* `HasDerivAt.const_mul`, `HasDerivAt.add`, `HasDerivAt.mul`
* `hasDerivAt_id`
* `Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_one`

Use `exact?` and `apply?` freely — that is what they are for.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import DGBOZK.Phase
import DGBOZK.Fold

namespace DGBOZK.Optional

open Real

/-- Step 1.  The power rule at exponent `α+1`, on the positive half-line.

Hint: `Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hξ))` gives you
`HasDerivAt (· ^ (α+1)) ((α+1) * ξ ^ (α+1-1)) ξ`.  All that remains is
`α + 1 - 1 = α`, by `ring_nf` or `norm_num`. -/
theorem hasDerivAt_rpow_succ {α ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun s : ℝ => s ^ (α + 1)) ((α + 1) * ξ ^ α) ξ := by
  sorry

/-- Step 2.  `∂_ξ ω_σ(ξ,η) = σ(α+1)ξ^α + η² = velX α σ ξ η`, for `ξ > 0`.

This is the statement that `[BB-DIFF]` asserts for the first component of
`(eq:grad-ell)` / `(eq:grad-hyp)`.

Plan:
* let `g s := η^2 * s + σ * s ^ (α+1)`; differentiate `g` with
  `HasDerivAt.add`, `HasDerivAt.const_mul`, `hasDerivAt_id` and step 1;
* show `Set.EqOn (fun s => s * (η^2 + σ * s ^ α)) g (Set.Ioi 0)` using
  `Real.rpow_add hs α 1` / `Real.rpow_one` to turn `s * s^α` into `s^(α+1)`;
* upgrade to `Filter.EventuallyEq` at `ξ` with `isOpen_Ioi.mem_nhds hξ`;
* conclude with `HasDerivAt.congr_of_eventuallyEq`. -/
theorem hasDerivAt_omega_fst {α σ ξ η : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun s : ℝ => s * (η ^ 2 + σ * s ^ α)) (velX α σ ξ η) ξ := by
  sorry

/-- Step 3.  `∂_η ω_σ(ξ,η) = 2ξη = velY ξ η`.  For fixed `ξ` this is a
polynomial in `η`, so no `rpow` subtlety arises. -/
theorem hasDerivAt_omega_snd {α σ ξ η : ℝ} :
    HasDerivAt (fun w : ℝ => ξ * (w ^ 2 + σ * |ξ| ^ α)) (velY ξ η) η := by
  sorry

/-- Step 4a.  `∂²_ξ ω_σ = σα(α+1)ξ^{α−1} = hessXX α σ ξ`.  Differentiate the
first component of the gradient, i.e. `s ↦ σ(α+1)s^α + η²`. -/
theorem hasDerivAt_hessXX {α σ ξ η : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun s : ℝ => σ * (α + 1) * s ^ α + η ^ 2) (hessXX α σ ξ) ξ := by
  sorry

/-- Step 4b.  `∂_ξ∂_η ω_σ = 2η = hessXY η`. -/
theorem hasDerivAt_hessXY {ξ η : ℝ} :
    HasDerivAt (fun w : ℝ => velY ξ w) (hessYY ξ) η := by
  sorry

/-- Step 5.  `Ψ''` is the second derivative of the reduced phase.

Once this and `hasDerivAt_Psi_three` are proved, `Psi2` and `Psi3` in
`DGBOZK/Fold.lean` stop being definitions-by-fiat: everything already proved
about them (`Psi2_eq_hessDet`, `Psi3_on_gamma_plus`, `Psi3_lower_bound`, …)
becomes a statement about the genuine derivatives of `Psi`. -/
theorem hasDerivAt_Psi_two {α x y t ξ : ℝ} (hξ : 0 < ξ) (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => x + t * (α + 1) * s ^ α + y ^ 2 / (4 * t * s ^ 2))
      (Psi2 α y t ξ) ξ := by
  sorry

/-- Step 6.  `Ψ'''`. -/
theorem hasDerivAt_Psi_three {α y t ξ : ℝ} (hξ : 0 < ξ) (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => Psi2 α y t s) (Psi3 α y t ξ) ξ := by
  sorry

end DGBOZK.Optional
