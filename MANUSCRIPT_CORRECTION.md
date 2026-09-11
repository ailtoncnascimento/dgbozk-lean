# Remaining manuscript correction found by the Lean audit

In the proof of `lem:resonance`, replace the sentence beginning “For the middle
term” with the following LaTeX.

```latex
For the middle term, the normal-sector bound first gives
\[
 N^{\alpha/2}|a||b|
 \le K^{-1}N|b|^2.
\]
Using in addition
$|b|\le\delta^{1/2}N^{\alpha/2}$, which follows from
$\rho_\alpha(\theta)\le\delta N^\alpha$, we obtain
\[
 N^{\alpha/2}|a||b|
 \le \frac{\delta^{1/2}}{K}
 N^{1+\alpha/2}|b|.
\]
Thus this term is small after choosing $K$ large and $\delta$ small.
```

Reason: `(eq:normal-sector)` alone controls `|a|` by a multiple of `|b|`; a
second `|b|` remains.  Its conversion to the principal scale uses the
low-frequency hypothesis.  The Lean theorem
`DGBOZK.Resonance.middle_term_bound` already exposes both hypotheses.
