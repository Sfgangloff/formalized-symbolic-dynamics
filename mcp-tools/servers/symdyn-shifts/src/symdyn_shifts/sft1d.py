"""1D SFT primitives: admissible-pattern counts, spectral-radius entropy.

A 1D SFT over alphabet `Σ` is defined by a finite set of forbidden
factors `F ⊆ Σ*`. A word `w ∈ Σ*` is *admissible* iff no factor of `w`
lies in `F`. The language `L_n(X)` is the set of admissible length-`n`
words, and the topological entropy is

    h_top(X) = lim_n (log |L_n(X)|) / n.

For a "step-k" SFT (all forbidden factors of length k+1; equivalently a
sliding-block code of memory k), `h_top(X) = log ρ(M)` where `M` is the
0/1 transition matrix on length-k allowed words.
"""

from __future__ import annotations

import math
from typing import Sequence

import numpy as np


def _is_admissible(word: tuple[str, ...], forbidden: set[tuple[str, ...]]) -> bool:
    """Check whether `word` contains no factor in `forbidden`."""
    for f in forbidden:
        m = len(f)
        if m == 0:
            return False  # an empty forbidden factor forbids everything
        for i in range(len(word) - m + 1):
            if word[i : i + m] == f:
                return False
    return True


def admissible_words(
    alphabet: Sequence[str], forbidden: Sequence[Sequence[str]], length: int
) -> list[tuple[str, ...]]:
    """Enumerate all admissible words of given `length` over `alphabet`.

    Naive enumeration: O(|Σ|^length · max|F|·length). Practical up to
    `|Σ|^length ≈ 10^6`.
    """
    if length < 0:
        raise ValueError(f"length must be ≥ 0, got {length}")
    forb = {tuple(f) for f in forbidden}
    if length == 0:
        return [()]
    words: list[tuple[str, ...]] = [(a,) for a in alphabet]
    for _ in range(length - 1):
        extended: list[tuple[str, ...]] = []
        for w in words:
            for a in alphabet:
                v = w + (a,)
                if _is_admissible(v, forb):
                    extended.append(v)
        words = extended
    return words


def admissible_count(
    alphabet: Sequence[str], forbidden: Sequence[Sequence[str]], length: int
) -> int:
    """Count admissible words of given `length`."""
    return len(admissible_words(alphabet, forbidden, length))


def transition_matrix_step_k(
    alphabet: Sequence[str], forbidden: Sequence[Sequence[str]], k: int
) -> tuple[list[tuple[str, ...]], np.ndarray]:
    """Build the step-`k` transition matrix.

    States = admissible words of length `k`. Transition `u → v` allowed
    iff `u[1:] == v[:-1]` (overlap) and the concatenation `u + (v[-1],)`
    of length `k+1` is admissible.

    Returns `(states, M)` where `M[i, j] = 1` iff `states[i] → states[j]`.
    """
    if k < 1:
        raise ValueError(f"k must be ≥ 1, got {k}")
    forb = {tuple(f) for f in forbidden}
    states = admissible_words(alphabet, forbidden, k)
    n = len(states)
    M = np.zeros((n, n), dtype=np.int64)
    state_to_idx = {s: i for i, s in enumerate(states)}
    for i, u in enumerate(states):
        for a in alphabet:
            v = u[1:] + (a,)
            if v in state_to_idx:
                # Check (k+1)-window is admissible.
                if _is_admissible(u + (a,), forb):
                    M[i, state_to_idx[v]] = 1
    return states, M


def spectral_radius(M: np.ndarray) -> float:
    """Largest |eigenvalue| of `M`. Returns 0 for empty matrix."""
    if M.size == 0:
        return 0.0
    eigvals = np.linalg.eigvals(M.astype(float))
    return float(max(abs(e) for e in eigvals))


def entropy_1d_step_k(
    alphabet: Sequence[str], forbidden: Sequence[Sequence[str]], k: int | None = None
) -> dict:
    """Exact 1D SFT entropy = log ρ(M_k).

    If `k` is `None`, defaults to `max_forbidden_length - 1` (so all
    forbidden factors have length ≤ k+1, i.e. the SFT is step-k).

    Returns `{n_states, spectral_radius, entropy}`. `entropy = 0` if the
    SFT is empty (no admissible state).
    """
    forb = list(forbidden)
    if k is None:
        max_f = max((len(f) for f in forb), default=1)
        k = max(max_f - 1, 1)
    states, M = transition_matrix_step_k(alphabet, forbidden, k)
    rho = spectral_radius(M)
    entropy = math.log(rho) if rho > 0 else 0.0
    return {"k": k, "n_states": len(states), "spectral_radius": rho, "entropy": entropy}
