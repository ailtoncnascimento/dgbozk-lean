# dgbozk-lean

**Status:** builds clean on Lean 4.22.0 + Mathlib. 104 theorems, 39 definitions,
~1900 lines. **No `sorry`, no project axioms.** Every headline theorem depends
only on `propext`, `Classical.choice`, `Quot.sound`; the results in
`Cancellation.lean` do not even need `Classical.choice`.

---

A **conditional** Lean 4 formalization of the key calculations in

> A. C. Nascimento, *Local well-posedness for two-sign dispersion-generalized
> Benjamin–Ono–Zakharov–Kuznetsov equations.*

for the Cauchy problem

```
∂_t u − σ D_x^α ∂_x u + ∂_x ∂_y² u + u ∂_x u = 0,   (x,y) ∈ ℝ², 1 ≤ α < 2, σ = ±1.
```

## What this repository claims — and what it does not

It follows the strategy Terence Tao has described for using proof assistants on
research papers: **formalize a key calculation conditionally on accepting every
other cited lemma as a black box.** This raises confidence in a paper when the
black boxes are all *standard* but the key calculation is *sensitive to sign and
exponent errors*.

So this repository does **not** verify the paper. It verifies:

1. **every numerical exponent** the paper's thresholds depend on, uniformly in
   `α` rather than at sample values;
2. **the sign-dependent phase geometry** that organizes the whole argument;
3. **the algebra of the localized cubic cancellation**, which the paper itself
   flags as the step whose omission "gives a false proof";
4. **the exponent bookkeeping of the focusing resonance lower bound**;
5. **that the parameter choices in the a priori system are consistent**, and
   that the small-data bootstrap closes,

conditionally on the standard machinery listed in
[`DGBOZK/BlackBoxes.lean`](DGBOZK/BlackBoxes.lean) — stationary phase, `TT*`,
Coifman–Meyer, sharp Gårding, Bernstein, compactness, Bona–Smith.

Every black box is carried **as a hypothesis or as a definition, never as an
axiom**. `#print axioms` on each headline theorem returns only Lean's own
`propext`, `Classical.choice`, `Quot.sound`. See
[`DGBOZK/Audit.lean`](DGBOZK/Audit.lean).

## Findings

Two things surfaced that the paper should address. Both are recorded as
machine-checked statements, not as prose.

### 1. The sign of the principal term in the localized cancellation (§5)

`(eq:cancellation-computation)` displays the derivative of the cubic correction
along the transverse flow as

```
… = +2 H⁻¹ ∫ b Π_H(∂_y v, ∂_y z_{∼H}) ∂_x z_H  +  𝒩
```

and concludes that this "is exactly the negative of (eq:bad-sm), so the two
cancel identically".

`DGBOZK.Cancellation.transverse_flow_identity` proves the identity that actually
holds. Its principal coefficient is **`−2`, not `+2`**. Two independent
derivations agree:

* on the Fourier side, `−∂_x∂_y²` acting on the `j`-th factor has symbol
  `−(i a_j)(i b_j)²`, every term carries exactly three derivative factors, and
  under `Σ a_j = Σ b_j = 0` one gets
  `a₁b₁² + a₂b₂² + a₃b₃² = 2a₃b₁b₂ − a₁b₂² − a₂b₁²`, which after the uniform
  factor `i³ = −i` gives coefficient `−2` in operator form;
* directly, integrating by parts twice in `y` in the third term and expanding
  `∂_y²Π(v,z) = Π(∂_y²v,z) + 2Π(∂_yv,∂_yz) + Π(v,∂_y²z)` produces
  `−2 ∫ b Π(∂_yv,∂_yz)∂_x z`.

As displayed, the correction would *double* the bad term instead of cancelling
it. `paper_identity_forces` states the consequence precisely: assuming the
paper's `+2` forces `4·T1 = T2 + T3 − 𝒩`, i.e. the principal term would have to
be a remainder term.

**This is repairable and does not affect any stated theorem.** Flipping the sign
of the cubic correction in `(eq:localized-functional)` — equivalently absorbing
`−1` into the normalization of `Π_H`, a freedom the paper explicitly invokes
when it says `Π_H` is "normalized so as to correspond to writing
`−uu_x = −½∂_x(u²)`" — restores exact cancellation. See
`transverse_flow_identity_negated`.

### 2. An unlisted residual term (§5)

The same expansion produces, unconditionally, a term with symbol `−a₂b₁²`, i.e.

```
Π_H(∂_y² P^ρ_{≪H}u, ∂_x z_{∼H}) z_H .
```

Its two `∂_y` fall on the low factor and its `∂_x` on a different factor, so it
matches neither clause of the paper's description of `𝒩` ("at least one `∂_y`
and the `∂_x` act on the same frequency-localized factor … the `∂_x` has been
moved onto `b`"), and it is not among the terms estimated in the proof. The
companion term `−a₁b₂²` **is** listed, as the "Taylor-remainder term".

`residual_term_unlisted` shows the identity fails without it, and `T3_ne_zero`
shows it does not vanish identically. It appears to be a bookkeeping omission
rather than a gap — putting `∂_y²P^ρ_{H'}u` in `L^∞` costs `H'` and the
resulting factor `(H'/H)^{1−1/α}` sums over `H' ≪ H` for `α > 1`, with the `H^ε`
absorbing the borderline case `α = 1` — but the term should be displayed and
estimated.

### 3. A step with two hypotheses attributed to one (§6)

In the proof of `lem:resonance` the middle Hessian term is dispatched with
"`N^{α/2}|a||b| ≤ (1/K)N^{1+α/2}|b|` **directly from (eq:normal-sector)**". The
normal sector alone gives `N^{α/2}|a||b| ≤ K⁻¹N|b|²`; converting that to
`K⁻¹N^{1+α/2}|b|` additionally uses `|b| ≤ N^{α/2}`, which comes from the
low-frequency hypothesis `ρ_α(θ) ≤ δN^α`. The step is correct.
`Resonance.middle_term_bound` requires both hypotheses explicitly.

### Everything else checked out

In particular all of the following are confirmed exactly as printed, uniformly
in `α`:

| Paper | Lean |
|---|---|
| `det D²ω_+ = 2α(α+1)\|ξ\|^α − 4η²`, `det D²ω_- = −2α(α+1)\|ξ\|^α − 4η²` | `hessDet_defocusing`, `hessDet_focusing`, `hessDet_eq_det` |
| Exchange of degeneracies (`prop:exchange`) | `exchange_of_degeneracies` |
| `Ψ'' = (t/2ξ)·det D²ω_+(ξ,η_*)` | `Psi2_eq_hessDet` |
| `Ψ'''\|_{Γ⁺} = tα(α+1)(α+2)ξ^{α−2}` | `Psi3_on_gamma_plus` |
| `\|∇ω_-\| ≳ N^α`, sharp at `η = 0` | `velocity_lower_bound`, `velocity_sharp` |
| `p*_α = 4(α+1)/(α+2)`, `p*_1 = 8/3`, `p*_2 = 3` | `Eplus_pStar`, `pStar_one`, `pStar_two` |
| `a⁺_{δ_α}(2) = (3−α)/(2α)`, `a⁺_{δ_α}(12/5) = 3(4−α)/(8α)` | `aPlus_delta_two`, `aPlus_delta_twelveFifths` |
| `𝖱_{α,1} − 𝖱_{α,0} = 1/8` | `R1_sub_R0` |
| `𝖱_{α,1} − 𝖪_α = 5(2−α)/(24α) > 0` | `R1_sub_Kfold`, `Kfold_lt_R1` |
| `a⁻_{ν_α}(2) = (3−α)/2`, `b⁻_{ν_α}(2) = 1/2` | `aMinus_nu_two`, `bMinus_nu_two` |
| `r⁺_α − r̃_α = (3α−4)/(8α)`, improvement on `1 ≤ α < 4/3` | `rPlus_sub_rRV`, `rPlus_lt_rRV` |
| `9/8` against `5/4` at `α = 1` | `rPlus_one`, `rRV_one` |
| `r⁺_α < 1/2` iff `α > 12/7` | `rPlus_lt_half_iff` |
| `κ_α − 1/4 = (α+1)/(12α)` | `kappa_sub_quarter` |
| `r_c = 1/(2α) − 3/4` is the scaling-critical index | `scalingExp_rCrit` |
| lifespan exponent `4(α+1)/(3α−2)`, `= 8` at `α = 1` | `lifespanExp_eq`, `lifespanExp_one` |
| bootstrap `X ≤ C₀e₀ + C₁(X^{3/2}+X²+X^{5/2})` closes | `bootstrap_closure` |
| the `ε₀` of `prop:coupled` exists, both signs | `exists_eps_defocusing`, `exists_eps_focusing` |

One margin worth noting even though it is satisfied: `prop:ell-smoothing`
needs `τ > d_α/2`, and `τ` may be taken just above `r⁺_α`, so one needs
`r⁺_α > d_α/2`, i.e. `α < 8/5` (`algebra_margin`). The defocusing range
`α < 4/3` is inside it, but the margin closes at `8/5`, not at `2` — worth
recording if the range is ever pushed.

## Layout

| File | Contents |
|---|---|
| `DGBOZK/BlackBoxes.lean` | what is assumed, and why each assumption is standard |
| `DGBOZK/Exponents.lean` | §1.5–1.6, all exponent arithmetic — **no black boxes** |
| `DGBOZK/Phase.lean` | §3, `(eq:grad-ell)`, `(eq:grad-hyp)`, `prop:exchange` |
| `DGBOZK/Fold.lean` | §3, `lem:fold` — reduced-phase identities |
| `DGBOZK/Velocity.lean` | §3, `lem:velocity` — focusing group velocity |
| `DGBOZK/Resonance.lean` | §6, `lem:resonance` — resonance lower bound |
| `DGBOZK/Cancellation.lean` | §5, `lem:localized-cancellation` — the cubic cancellation |
| `DGBOZK/Bootstrap.lean` | §8–§9, parameter consistency and small-data closure |
| `DGBOZK/Audit.lean` | `#print axioms` on every headline theorem |

## Building

### In a GitHub Codespace (no local install)

Open this repository in a Codespace. `.devcontainer/devcontainer.json` installs
the Lean 4 VS Code extension and runs `scripts/setup.sh`, which installs `elan`,
fetches prebuilt Mathlib and builds the project. If you would rather drive it by
hand, open a terminal and run:

```bash
bash scripts/setup.sh
```

Then the honesty check:

```bash
lake env lean DGBOZK/Audit.lean
```

### Locally

```bash
curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
lake exe cache get      # prebuilt Mathlib, ~5 GB
lake build
lake env lean DGBOZK/Audit.lean
```

`lean-toolchain` pins Lean to `v4.22.0`; `lake-manifest.json` pins Mathlib to
the `v4.22.0` release commit, so `lake exe cache get` always has a cache to hit.

**Do not skip `lake exe cache get`.** Without it, `lake build` compiles Mathlib
from source — hours on a small machine.

### Optional exercise

`DGBOZK/Optional/Differentiation.lean` is unverified starter code for
discharging `[BB-DIFF]`. It is deliberately not imported by `DGBOZK.lean`, so it
takes no part in `lake build` and cannot break the verified core.

## Citing

If this formalization is referenced in the paper, the natural sentence is:

> The sign-dependent phase geometry of §3, the exponent arithmetic of §1.6, the
> algebraic core of the cancellation of §5, and the parameter consistency of §8
> have been formalized in Lean 4, conditionally on the standard harmonic
> analysis inputs, at `github.com/<user>/dgbozk-lean`.

## License

Apache 2.0.
