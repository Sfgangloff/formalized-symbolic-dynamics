"""1D factor / pattern complexity tools.

For a 1D subshift `X`, the *factor complexity* is `p_X(n) = |L_n(X)|`,
the number of distinct length-`n` factors appearing in some point of
`X`. For 1D SFTs defined by forbidden factors, this equals the number
of length-`n` words containing no forbidden factor.

For a single bi-infinite word `x ∈ Σ^ℤ`, the factor complexity of its
orbit closure is `p_x(n) = #{factors of x of length n}`. For a finite
word `w` or a periodic word `(w)^∞`, this is computable directly.
"""

from __future__ import annotations

from typing import Sequence


def _is_admissible(word: tuple[str, ...], forbidden: set[tuple[str, ...]]) -> bool:
    for f in forbidden:
        m = len(f)
        if m == 0:
            return False
        for i in range(len(word) - m + 1):
            if word[i : i + m] == f:
                return False
    return True


def sft_factor_complexity(
    alphabet: Sequence[str], forbidden: Sequence[Sequence[str]], n_max: int
) -> list[int]:
    """Compute `p_X(1), ..., p_X(n_max)` for the 1D SFT.

    Naive enumeration. Practical up to `|Σ|^n_max ≈ 10^6`.
    """
    if n_max < 1:
        raise ValueError(f"n_max must be ≥ 1, got {n_max}")
    forb = {tuple(f) for f in forbidden}
    out: list[int] = []
    words: list[tuple[str, ...]] = [(a,) for a in alphabet]
    words = [w for w in words if _is_admissible(w, forb)]
    out.append(len(words))
    for _ in range(n_max - 1):
        extended: list[tuple[str, ...]] = []
        for w in words:
            for a in alphabet:
                v = w + (a,)
                if _is_admissible(v, forb):
                    extended.append(v)
        words = extended
        out.append(len(words))
    return out


def word_factor_complexity(word: str, n_max: int) -> list[int]:
    """Compute `p_w(1), ..., p_w(n_max)` for a finite word `w`.

    `p_w(n)` is the number of distinct length-`n` factors of `w`.
    """
    if n_max < 1:
        raise ValueError(f"n_max must be ≥ 1, got {n_max}")
    return [len({word[i : i + n] for i in range(len(word) - n + 1)}) for n in range(1, n_max + 1)]


def periodic_word_factor_complexity(period: str, n_max: int) -> list[int]:
    """Compute `p_x(1), ..., p_x(n_max)` for `x = (period)^∞`.

    Eventually plateau at `len(period)`.
    """
    if not period:
        raise ValueError("period must be non-empty")
    if n_max < 1:
        raise ValueError(f"n_max must be ≥ 1, got {n_max}")
    p = len(period)
    doubled = period + period
    out = []
    for n in range(1, n_max + 1):
        if n >= p:
            # All length-n factors are cyclic shifts of `period * ceil(n/p)`;
            # for n ≥ p, # distinct = p (the period itself).
            out.append(p)
        else:
            out.append(len({doubled[i : i + n] for i in range(p)}))
    return out


def morse_hedlund_eventually_periodic(complexity: Sequence[int]) -> dict:
    """Morse–Hedlund eventual-periodicity test.

    For a bi-infinite word `x`, `x` is *eventually periodic* iff there
    exists `n ≥ 1` with `p_x(n) ≤ n`. Equivalently, if `p_x(n) ≥ n + 1`
    for every `n` in the visible range, then either `x` is non-periodic
    or the witness `n` is larger than the input.

    Returns `{eventually_periodic: bool, witness_n: int | None,
              checked_up_to: int}`.

    `witness_n` is the smallest `n` with `p(n) ≤ n` if any was found;
    `None` otherwise.
    """
    for i, p in enumerate(complexity, start=1):
        if p <= i:
            return {
                "eventually_periodic": True,
                "witness_n": i,
                "checked_up_to": len(complexity),
            }
    return {
        "eventually_periodic": False,
        "witness_n": None,
        "checked_up_to": len(complexity),
    }
