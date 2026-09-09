/-
# §6.  `Lemma lem:resonance` — the focusing resonance lower bound

Formalizes the lower bound `(eq:resonance)` of

  A. C. Nascimento, *Local well-posedness for two-sign dispersion-generalized
  Benjamin–Ono–Zakharov–Kuznetsov equations*.

The resonance function is
`Ω(θ,ζ) = ω_-(θ) + ω_-(ζ) − ω_-(ζ+θ)`, and the lemma asserts, for `ζ` in the
transition band `𝒯_N` and `θ` in the normal sector `ℬ_{N,K}`,

  `|Ω(θ,ζ)| ≥ c₁ N^{1+α/2}|b|`.

The paper's own remark is that this "is exactly the input a cubic normal form
needs", and that "the `α`-dependence is not a matter of substituting exponents".
The proof is a competition between one principal term and four error terms, each
dominated by a different power bookkeeping.  Getting one exponent wrong changes
which term wins.  That bookkeeping is what is checked here.

## Black boxes

* `[BB-TAYLOR]` — the Taylor expansion `(eq:Omega-taylor)`,
  `Ω = ω_-(θ) − ∂_ξω_-(ζ)a − ∂_ηω_-(ζ)b − R`, valid because the segment
  `[ζ, ζ+θ]` stays in a conic neighbourhood on which `ω_-` is smooth.  Supplied
  as a hypothesis.
* `[BB-HESS]` — the Hessian bounds on that segment, giving
  `|R| ≤ N^{α−1}a² + N^{α/2}|a||b| + N b²`.  Supplied as a hypothesis.

Everything else — the four dominations and the assembly — is proved.

## A remark on the paper's proof

The paper dispatches the middle Hessian term with

  "For the middle term, `N^{α/2}|a||b| ≤ (1/K)N^{1+α/2}|b|` **directly from
   (eq:normal-sector)**."

The normal sector alone gives `N^{α/2}|a||b| ≤ K^{-1} N |b|²`, and passing from
there to `K^{-1}N^{1+α/2}|b|` uses in addition `|b| ≤ N^{α/2}`, which comes from
the *low-frequency* hypothesis `ρ_α(θ) ≤ δN^α` rather than from the sector.  The
step is correct, but it uses two hypotheses, not one.  In `middle_term_bound`
below both are required explicitly, so the dependence is visible.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace DGBOZK.Resonance

open Real

variable {α N a b d K : ℝ}

/-! ## Exponent bookkeeping

Each of the four dominations is one exponent addition.  These are the identities
whose failure would change the lemma.
-/

/-- `N^α · N^{1−α/2} = N^{1+α/2}`.  Used for the `∂_ξω_-` term and for `ω_-(θ)`. -/
theorem exp_band (hN : 0 < N) (α : ℝ) :
    N ^ α * N ^ (1 - α/2) = N ^ (1 + α/2) := by
  rw [← Real.rpow_add hN]
  congr 1
  ring

/-- `N · N^{α/2} = N^{1+α/2}`.  Used for the `Nb²` Hessian term. -/
theorem exp_transverse (hN : 0 < N) (α : ℝ) :
    N * N ^ (α/2) = N ^ (1 + α/2) := by
  have h := Real.rpow_add hN 1 (α/2)
  rw [Real.rpow_one] at h
  exact h.symm

/-- `N^{α/2} · N^{1−α/2} = N`.  Used for the mixed Hessian term. -/
theorem exp_mixed (hN : 0 < N) (α : ℝ) :
    N ^ (α/2) * N ^ (1 - α/2) = N := by
  rw [← Real.rpow_add hN]
  norm_num

/-- `N^{α−1} · N^{1−α/2} = N^{α/2}`.  Used for the `N^{α−1}a²` Hessian term. -/
theorem exp_longitudinal (hN : 0 < N) (α : ℝ) :
    N ^ (α - 1) * N ^ (1 - α/2) = N ^ (α/2) := by
  rw [← Real.rpow_add hN]
  congr 1
  ring

/-! ## The four dominations

Throughout, `P := N^{1+α/2}|b|` is the size of the principal term
`∂_ηω_-(ζ)·b`, and the hypotheses are:

* `hsector` : `|a| ≤ K⁻¹ N^{1−α/2}|b|`   — the normal sector `ℬ_{N,K}`;
* `hlow`    : `|b| ≤ d · N^{α/2}`        — from `ρ_α(θ) ≤ δN^α`, with `d = √δ`.
-/

/-- **First error term.**  `|∂_ξω_-(ζ)·a| ≤ (c₀/K)·N^{1+α/2}|b|`, from the band
bound `|∂_ξω_-(ζ)| ≤ c₀N^α` and the normal sector. -/
theorem longitudinal_term_bound {c₀ vξ : ℝ} (hN : 0 < N) (hK : 0 < K)
    (hc₀ : 0 ≤ c₀)
    (hvξ : |vξ| ≤ c₀ * N ^ α)
    (hsector : |a| ≤ K⁻¹ * N ^ (1 - α/2) * |b|) :
    |vξ * a| ≤ (c₀ / K) * (N ^ (1 + α/2) * |b|) := by
  have hNa : (0:ℝ) < N ^ α := Real.rpow_pos_of_pos hN α
  have hNb : (0:ℝ) < N ^ (1 - α/2) := Real.rpow_pos_of_pos hN _
  have habs : |vξ * a| = |vξ| * |a| := abs_mul _ _
  have hstep : |vξ| * |a| ≤ (c₀ * N ^ α) * (K⁻¹ * N ^ (1 - α/2) * |b|) := by
    apply mul_le_mul hvξ hsector (abs_nonneg _)
    positivity
  have hcollapse : (c₀ * N ^ α) * (K⁻¹ * N ^ (1 - α/2) * |b|)
      = (c₀ / K) * ((N ^ α * N ^ (1 - α/2)) * |b|) := by
    field_simp
    ring
  rw [habs]
  rw [hcollapse, exp_band hN α] at hstep
  exact hstep

/-- **Second error term.**  `|ω_-(θ)| ≤ (δ/K)·N^{1+α/2}|b|`, from
`|ω_-(θ)| = |a|·|b² − |a|^α| ≤ |a|ρ_α(θ) ≤ δN^α|a|` and the normal sector.
Structurally identical to the first. -/
theorem low_phase_bound {δ ωθ : ℝ} (hN : 0 < N) (hK : 0 < K) (hδ : 0 ≤ δ)
    (hωθ : |ωθ| ≤ δ * N ^ α * |a|)
    (hsector : |a| ≤ K⁻¹ * N ^ (1 - α/2) * |b|) :
    |ωθ| ≤ (δ / K) * (N ^ (1 + α/2) * |b|) := by
  have hNa : (0:ℝ) < N ^ α := Real.rpow_pos_of_pos hN α
  have hNb : (0:ℝ) < N ^ (1 - α/2) := Real.rpow_pos_of_pos hN _
  have hstep : δ * N ^ α * |a| ≤ δ * N ^ α * (K⁻¹ * N ^ (1 - α/2) * |b|) := by
    apply mul_le_mul_of_nonneg_left hsector
    positivity
  have hcollapse : δ * N ^ α * (K⁻¹ * N ^ (1 - α/2) * |b|)
      = (δ / K) * ((N ^ α * N ^ (1 - α/2)) * |b|) := by
    field_simp; ring
  rw [hcollapse, exp_band hN α] at hstep
  linarith

/-- **Third error term (transverse Hessian).**  `N b² ≤ d · N^{1+α/2}|b|`,
directly from `|b| ≤ d N^{α/2}`. -/
theorem transverse_term_bound (hN : 0 < N) (_hd : 0 ≤ d)
    (hlow : |b| ≤ d * N ^ (α/2)) :
    N * b ^ 2 ≤ d * (N ^ (1 + α/2) * |b|) := by
  have hNh : (0:ℝ) < N ^ (α/2) := Real.rpow_pos_of_pos hN _
  have hb2 : b ^ 2 = |b| * |b| := by rw [← sq_abs]; ring
  have hstep : N * (|b| * |b|) ≤ N * (|b| * (d * N ^ (α/2))) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hN)
    exact mul_le_mul_of_nonneg_left hlow (abs_nonneg b)
  have hcollapse : N * (|b| * (d * N ^ (α/2))) = d * ((N * N ^ (α/2)) * |b|) := by ring
  rw [hcollapse, exp_transverse hN α] at hstep
  rw [hb2]
  exact hstep

/-- **Fourth error term (mixed Hessian).**  `N^{α/2}|a||b| ≤ (d/K)·N^{1+α/2}|b|`.

Note the two hypotheses: the normal sector supplies `N^{α/2}|a||b| ≤ K⁻¹N|b|²`,
and only then does `|b| ≤ dN^{α/2}` convert `N|b|²` into `dN^{1+α/2}|b|`.  The
paper attributes this step to the normal sector alone. -/
theorem middle_term_bound (hN : 0 < N) (hK : 0 < K) (_hd : 0 ≤ d)
    (hsector : |a| ≤ K⁻¹ * N ^ (1 - α/2) * |b|)
    (hlow : |b| ≤ d * N ^ (α/2)) :
    N ^ (α/2) * (|a| * |b|) ≤ (d / K) * (N ^ (1 + α/2) * |b|) := by
  have hNh : (0:ℝ) < N ^ (α/2) := Real.rpow_pos_of_pos hN _
  have hNb : (0:ℝ) < N ^ (1 - α/2) := Real.rpow_pos_of_pos hN _
  -- step 1: use the sector on |a|
  have s1 : N ^ (α/2) * (|a| * |b|) ≤ N ^ (α/2) * ((K⁻¹ * N ^ (1 - α/2) * |b|) * |b|) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hNh)
    exact mul_le_mul_of_nonneg_right hsector (abs_nonneg b)
  have e1 : N ^ (α/2) * ((K⁻¹ * N ^ (1 - α/2) * |b|) * |b|)
      = K⁻¹ * ((N ^ (α/2) * N ^ (1 - α/2)) * (|b| * |b|)) := by ring
  rw [e1, exp_mixed hN α] at s1
  -- step 2: use the low-frequency bound on one factor of |b|
  have s2 : K⁻¹ * (N * (|b| * |b|)) ≤ K⁻¹ * (N * (|b| * (d * N ^ (α/2)))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hN)
    exact mul_le_mul_of_nonneg_left hlow (abs_nonneg b)
  have e2 : K⁻¹ * (N * (|b| * (d * N ^ (α/2)))) = (d / K) * ((N * N ^ (α/2)) * |b|) := by
    field_simp; ring
  rw [e2, exp_transverse hN α] at s2
  linarith

/-- **Fifth error term (longitudinal Hessian).**  `N^{α−1}a² ≤ K⁻¹N^{α/2}|a||b|`,
so it is dominated by the middle term, as the paper says. -/
theorem longitudinal_hessian_bound (hN : 0 < N) (_hK : 0 < K)
    (hsector : |a| ≤ K⁻¹ * N ^ (1 - α/2) * |b|) :
    N ^ (α - 1) * a ^ 2 ≤ K⁻¹ * (N ^ (α/2) * (|a| * |b|)) := by
  have hNl : (0:ℝ) < N ^ (α - 1) := Real.rpow_pos_of_pos hN _
  have hNb : (0:ℝ) < N ^ (1 - α/2) := Real.rpow_pos_of_pos hN _
  have ha2 : a ^ 2 = |a| * |a| := by rw [← sq_abs]; ring
  have s1 : N ^ (α - 1) * (|a| * |a|) ≤ N ^ (α - 1) * (|a| * (K⁻¹ * N ^ (1 - α/2) * |b|)) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hNl)
    exact mul_le_mul_of_nonneg_left hsector (abs_nonneg a)
  have e1 : N ^ (α - 1) * (|a| * (K⁻¹ * N ^ (1 - α/2) * |b|))
      = K⁻¹ * ((N ^ (α - 1) * N ^ (1 - α/2)) * (|a| * |b|)) := by ring
  rw [e1, exp_longitudinal hN α] at s1
  rw [ha2]
  exact s1

/-! ## Assembly -/

/-- **`Lemma lem:resonance`, lower bound `(eq:resonance)`.**

Given the Taylor expansion `[BB-TAYLOR]`, the Hessian remainder bound
`[BB-HESS]`, the band bound on `∂_ξω_-`, the normal sector, and the
low-frequency bound, together with the smallness condition

  `c₀/K + δ/K + d + d/K + d/K² ≤ 1/2`

("choose `K` large and then `c₀, δ` small"), one has

  `|Ω| ≥ ½ N^{1+α/2}|b|`,

i.e. `(eq:resonance)` with the explicit constant `c₁ = 1/2`.

The principal term is `∂_ηω_-(ζ)·b`, of size at least `N^{1+α/2}|b|` on the
transition band, where `|∂_ηω_-(ζ)| = 2|ξη| ∼ N^{1+α/2}`. -/
theorem resonance_lower_bound {c₀ δ Ω ωθ vξ vη R : ℝ}
    (hN : 0 < N) (hK : 0 < K) (_hK1 : 1 ≤ K) (hc₀ : 0 ≤ c₀) (hδ : 0 ≤ δ) (hd : 0 ≤ d)
    -- `[BB-TAYLOR]` : (eq:Omega-taylor)
    (hTaylor : Ω = ωθ - vξ * a - vη * b - R)
    -- principal term: `|∂_ηω_-(ζ)| ≳ N^{1+α/2}` on the band `𝒯_N`
    (hprincipal : N ^ (1 + α/2) * |b| ≤ |vη * b|)
    -- band bound on the longitudinal velocity
    (hvξ : |vξ| ≤ c₀ * N ^ α)
    -- size of `ω_-(θ)`
    (hωθ : |ωθ| ≤ δ * N ^ α * |a|)
    -- normal sector `ℬ_{N,K}`
    (hsector : |a| ≤ K⁻¹ * N ^ (1 - α/2) * |b|)
    -- low-frequency bound, `d = √δ`
    (hlow : |b| ≤ d * N ^ (α/2))
    -- `[BB-HESS]` : the Hessian remainder
    (hR : |R| ≤ N ^ (α - 1) * a ^ 2 + N ^ (α/2) * (|a| * |b|) + N * b ^ 2)
    -- smallness
    (hsmall : c₀ / K + δ / K + d + d / K + d / K ^ 2 ≤ 1/2) :
    (1/2 : ℝ) * (N ^ (1 + α/2) * |b|) ≤ |Ω| := by
  set P := N ^ (1 + α/2) * |b| with hP
  have hPnonneg : 0 ≤ P := by
    have : (0:ℝ) < N ^ (1 + α/2) := Real.rpow_pos_of_pos hN _
    positivity
  -- the four error bounds
  have B1 : |vξ * a| ≤ (c₀ / K) * P := longitudinal_term_bound hN hK hc₀ hvξ hsector
  have B2 : |ωθ| ≤ (δ / K) * P := low_phase_bound hN hK hδ hωθ hsector
  have B3 : N * b ^ 2 ≤ d * P := transverse_term_bound hN hd hlow
  have B4 : N ^ (α/2) * (|a| * |b|) ≤ (d / K) * P := middle_term_bound hN hK hd hsector hlow
  have B5 : N ^ (α - 1) * a ^ 2 ≤ K⁻¹ * (N ^ (α/2) * (|a| * |b|)) :=
    longitudinal_hessian_bound hN hK hsector
  have B5' : N ^ (α - 1) * a ^ 2 ≤ (d / K ^ 2) * P := by
    have hKinv : (0:ℝ) ≤ K⁻¹ := by positivity
    have hstep : K⁻¹ * (N ^ (α/2) * (|a| * |b|)) ≤ K⁻¹ * ((d / K) * P) :=
      mul_le_mul_of_nonneg_left B4 hKinv
    have heq : K⁻¹ * ((d / K) * P) = (d / K ^ 2) * P := by
      simp only [div_eq_mul_inv, ← inv_pow]
      ring
    rw [heq] at hstep
    exact le_trans B5 hstep
  -- remainder
  have BR : |R| ≤ (d / K ^ 2 + d / K + d) * P := by linarith [hR, B5', B4, B3]
  -- assemble
  have hsum : |ωθ| + |vξ * a| + |R| ≤ (c₀ / K + δ / K + d + d / K + d / K ^ 2) * P := by
    linarith [B1, B2, BR]
  have hhalf : |ωθ| + |vξ * a| + |R| ≤ (1/2 : ℝ) * P := by
    have := mul_le_mul_of_nonneg_right hsmall hPnonneg
    linarith
  -- `vη·b = ωθ − vξ·a − R − Ω`, so `|vη·b| ≤ |ωθ| + |vξ·a| + |R| + |Ω|`
  have hvb : vη * b = ωθ + -(vξ * a) + -R + -Ω := by rw [hTaylor]; ring
  have htri : |vη * b| ≤ |ωθ| + |vξ * a| + |R| + |Ω| := by
    rw [hvb]
    have h1 := abs_add (ωθ + -(vξ * a) + -R) (-Ω)
    have h2 := abs_add (ωθ + -(vξ * a)) (-R)
    have h3 := abs_add ωθ (-(vξ * a))
    simp only [abs_neg] at h1 h2 h3
    linarith
  linarith

end DGBOZK.Resonance
