#!/usr/bin/env python3
"""Exact regression checks independent of Lean's proof scripts.

These checks deliberately duplicate selected rational and polynomial identities
with Python's exact ``Fraction`` arithmetic.  They are not a substitute for the
Lean kernel build; they help detect transcription or sign regressions.
"""

from fractions import Fraction as Q
from itertools import product


def check_exponents(alpha: Q) -> int:
    delta = 1 / alpha - Q(1, 2)
    nu = 1 - alpha / 2
    d_aniso = 1 / alpha + Q(1, 2)
    kappa = Q(1, 2) - (2 * alpha - 1) / (12 * alpha)
    p_star = 4 * (alpha + 1) / (alpha + 2)

    def e_plus(p: Q) -> Q:
        return (alpha + 2) / (4 * alpha) - (alpha + 1) / (alpha * p)

    def e_minus(p: Q) -> Q:
        return (alpha + 2) / 4 - (alpha + 1) / p

    def a_plus(theta: Q, p: Q) -> Q:
        return 1 / alpha + e_plus(p) + theta / p

    def a_minus(theta: Q, p: Q) -> Q:
        return 1 + e_minus(p) + theta / p

    def b_minus(theta: Q, p: Q) -> Q:
        return a_minus(theta, p) - theta

    r0 = (3 - alpha) / (2 * alpha)
    r1 = 3 * (4 - alpha) / (8 * alpha)
    k_fold = (13 - 2 * alpha) / (12 * alpha)
    s0 = (3 - alpha) / 2
    r_plus = r1
    r_rv = 2 / alpha - Q(3, 4)
    r_crit = 1 / (2 * alpha) - Q(3, 4)
    lifespan = 4 * (alpha + 1) / (3 * alpha - 2)
    lambda_exp = 4 / (3 * alpha - 2)

    checks = (
        delta == (2 - alpha) / (2 * alpha),
        nu == alpha * delta,
        kappa == (4 * alpha + 1) / (12 * alpha),
        kappa - Q(1, 4) == (alpha + 1) / (12 * alpha),
        e_plus(p_star) == 0,
        e_minus(p_star) == 0,
        a_plus(delta, 2) == r0,
        a_plus(delta, Q(12, 5)) == r1,
        k_fold == kappa + delta,
        r1 - r0 == Q(1, 8),
        r1 - k_fold == 5 * (2 - alpha) / (24 * alpha),
        a_minus(nu, 2) == s0,
        b_minus(nu, 2) == Q(1, 2),
        r_plus - r_rv == (3 * alpha - 4) / (8 * alpha),
        alpha * r_crit + 3 * alpha / 4 - Q(1, 2) == 0,
        lifespan == (alpha + 1) * lambda_exp,
        r_plus - d_aniso / 2 == (8 - 5 * alpha) / (8 * alpha),
    )
    assert all(checks), f"exponent identity failed at alpha={alpha}"
    return len(checks)


def check_clean_focusing_threshold(alpha: Q) -> int:
    s_minus = Q(3, 2) - alpha / 4
    direct_loss = Q(1, 2) - alpha / 4
    upper_offset = -Q(1, 2) + alpha / 4
    s0 = (3 - alpha) / 2
    nu = 1 - alpha / 2

    checks = (
        s_minus == (6 - alpha) / 4,
        s_minus == 1 + direct_loss,
        s0 == Q(1, 2) + nu,
        1 - upper_offset == s_minus,
    )
    assert all(checks), f"focusing threshold identity failed at alpha={alpha}"
    return len(checks)


def check_cancellation() -> int:
    count = 0
    for a1, a2, b1, b2 in product(range(-3, 4), repeat=4):
        a3 = -a1 - a2
        b3 = -b1 - b2
        lhs = a1 * b1**2 + a2 * b2**2 + a3 * b3**2
        rhs = 2 * a3 * b1 * b2 - a1 * b2**2 - a2 * b1**2
        assert lhs == rhs, (a1, a2, a3, b1, b2, b3)
        count += 1
    return count


def main() -> None:
    samples = (Q(1), Q(9, 8), Q(6, 5), Q(5, 4), Q(4, 3), Q(3, 2), Q(8, 5), Q(7, 4))
    count = sum(check_exponents(alpha) for alpha in samples)
    count += sum(check_clean_focusing_threshold(alpha) for alpha in samples)
    count += check_cancellation()
    print(f"PASS: {count} exact rational/integer identity checks")


if __name__ == "__main__":
    main()
