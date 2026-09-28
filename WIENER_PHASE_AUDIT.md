# Audit of `lem:wiener-phase` and `eq:D-wiener`

## Scope

This document records the analytic audit of the Wiener-algebra arguments used
in the cleaned DGBOZK manuscript.

**Update.** `lem:wiener` (with both bounds of `eq:wiener-average`) and the two
Wiener-norm bounds of `lem:wiener-phase` are now proved in Lean, without
hypotheses, in `DGBOZK/Foundations/WienerAlgebraCore.lean`: see
`inWiener_abs_rpow_mul_schwartz`, `inWiener_mul_abs_rpow_mul_schwartz`,
`wienerAverage_uniform`, `wienerAverage_integral`, `IsWienerKernel.mul`,
`IsWienerKernel.exp_mul`, `hasDerivAt_wienerPhase` and `wienerPhase`.  The
derivative bound is proved uniformly in `|t| <= 1`, which implies the integral
bound.  The maximal-function consequence
`∫ sup_{|t|<=1} |k_t(x)| dx < ∞` derived below, and `eq:D-wiener`, remain
outside Lean.

The Lean library verifies the exact sign and algebraic identities surrounding
the localized positive commutator in:

- `DGBOZK/PositiveCommutatorCore.lean`.

The genuinely harmonic-analytic estimates described below remain outside the
formal kernel and belong to the declared trust boundary.

## Wiener-algebra convention

The manuscript uses

\[
\|m\|_{A(\mathbb R^d)}
  = \|\mathcal F^{-1}m\|_{L^1(\mathbb R^d)}.
\]

With this convention, the following properties are used:

1. \(A(\mathbb R^d)\) is a Banach algebra under pointwise multiplication.
2. Multiplication by a character preserves the Wiener norm.
3. Precomposition with an invertible linear transformation preserves the
   Wiener norm.
4. Compactly supported functions with sufficient Sobolev regularity belong
   to the Wiener algebra.
5. Fourier inversion identifies an \(A\)-valued absolutely continuous curve
   with an \(L^1\)-valued absolutely continuous curve.

These properties are standard analytic inputs and are not formalized in the
current Lean artifact.

## Audit of `lem:wiener-phase`

Let

\[
F(\xi)=\xi|\xi|^\alpha\widetilde\chi(\xi),
\]

where \(\widetilde\chi\) is compactly supported and equals one on the support
of \(\chi\).

For \(1\leq\alpha<2\), the function \(F\) belongs to the Wiener algebra. Near
the origin its second derivative has size \(O(|\xi|^{\alpha-1})\), which is
locally square-integrable. Compact support therefore gives sufficient
Sobolev regularity for Wiener membership.

Because the Wiener algebra on \(\mathbb R\) is nonunital, the exponential is
interpreted in its unitization. Multiplication by \(\chi\) removes the scalar
identity component, and

\[
\chi e^{-itF}
 =\chi+\sum_{j\geq1}\frac{(-it)^j}{j!}\chi F^j .
\]

The Banach-algebra estimate gives

\[
\|\chi e^{-itF}\|_A
 \leq \|\chi\|_A e^{|t|\|F\|_A}.
\]

Differentiation of the exponential series in the unitized algebra yields

\[
\partial_t(\chi e^{-itF})
  =-i\chi F e^{-itF},
\]

and consequently

\[
\int_{-1}^{1}
 \|\partial_t(\chi e^{-itF})\|_A\,dt
 \leq
 2\|\chi\|_A\|F\|_A e^{\|F\|_A}.
\]

If

\[
k_t=\mathcal F^{-1}(\chi e^{-itF}),
\]

then \(t\mapsto k_t\) has an absolutely continuous \(L^1\)-valued
representative. For almost every spatial point,

\[
\sup_{|t|\leq1}|k_t(x)|
 \leq |k_0(x)|
   +\int_{-1}^{1}|\partial_t k_t(x)|\,dt .
\]

Fubini's theorem therefore gives

\[
\int_{\mathbb R}\sup_{|t|\leq1}|k_t(x)|\,dx
 \leq
 \|k_0\|_1+
 \int_{-1}^{1}\|\partial_tk_t\|_1\,dt<\infty.
\]

No sign error or missing growth factor was found in this argument.

## Audit of `eq:D-wiener`

Set \(\epsilon=R^{-1}\). The localized remainder is decomposed as

\[
\begin{aligned}
&\int_0^1|x-s\epsilon h|^\alpha\,ds
 -|x|^{\alpha/2}|x-\epsilon h|^{\alpha/2}\\
&\quad=
 \int_0^1
 \bigl(|x-s\epsilon h|^\alpha-|x|^\alpha\bigr)\,ds\\
&\qquad\quad+
 |x|^{\alpha/2}
 \bigl(|x|^{\alpha/2}
       -|x-\epsilon h|^{\alpha/2}\bigr).
\end{aligned}
\]

The first contribution uses the difference estimate with
\(\beta=\alpha\). It is bounded by

\[
\begin{cases}
C\epsilon\log(2/\epsilon),&\alpha=1,\\
C_\alpha\epsilon,&1<\alpha<2.
\end{cases}
\]

The second contribution uses \(\beta=\alpha/2\in[1/2,1)\) and the Banach
algebra property, giving

\[
C_\alpha\epsilon^{\alpha/2}.
\]

For \(0<\epsilon\leq1\),

\[
\epsilon\leq\epsilon^{\alpha/2},
 \qquad 1<\alpha<2,
\]

while at \(\alpha=1\),

\[
\epsilon\log(2/\epsilon)
 \leq C\epsilon^{1/2}.
\]

Hence both contributions are bounded by
\(C_\alpha\epsilon^{\alpha/2}\).

The rescaling

\[
\mathcal D_{\lambda,R}(\xi,\xi')
 =
 \lambda^\alpha
 d_{1/R}
 \left(
   \frac{\xi}{\lambda},
   \frac{R(\xi-\xi')}{\lambda}
 \right)
\]

uses an invertible linear transformation. Invariance of the Wiener norm under
invertible linear precomposition therefore gives

\[
\|\mathcal D_{\lambda,R}\|_{A(\mathbb R^2)}
 =
 \lambda^\alpha\|d_{1/R}\|_{A(\mathbb R^2)}
 \leq
 C_\alpha\lambda^\alpha R^{-\alpha/2}.
\]

The exponent and scaling in `eq:D-wiener` are therefore consistent.

## Formalization status

The following components are machine-checked:

- the transverse commutator symbol and its sign;
- the two longitudinal minus signs;
- the sign obtained from the exact phase-difference factorization;
- the two-component parametrix numerator;
- positivity of the principal quadratic density;
- the final scalar absorption step.

The following components are analytically audited but not machine-checked:

- Wiener membership of the compactly supported fractional-power symbols;
- the quantitative Wiener difference estimate;
- differentiation of the Wiener-algebra exponential;
- the \(L^1\)-valued fundamental theorem of calculus;
- Fourier-kernel representation of the commutator error;
- continuous-shift covering by translated strip centers;
- weighted multiplier and parametrix estimates.

Accordingly, the Lean artifact must not be described as a complete
formalization of `lem:wiener-phase`, `eq:D-wiener`, or
`lem:positive-comm`.
