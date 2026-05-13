import json

from symdyn_complexity.server import (
    symdyn_complexity_1d_periodic,
    symdyn_complexity_1d_sft,
    symdyn_complexity_1d_word,
    symdyn_complexity_info,
    symdyn_morse_hedlund_check,
)


def test_info_mentions_phase_b():
    out = symdyn_complexity_info()
    assert "symdyn-complexity" in out
    assert "Phase B" in out


def test_complexity_sft_golden_mean_fibonacci():
    out = json.loads(symdyn_complexity_1d_sft("01", "11", 6))
    # Same Fibonacci values as in symdyn-shifts.
    assert out["p_X"] == [2, 3, 5, 8, 13, 21]


def test_complexity_sft_full_shift_powers():
    out = json.loads(symdyn_complexity_1d_sft("01", "[]", 5))
    assert out["p_X"] == [2, 4, 8, 16, 32]


def test_complexity_word_basic():
    # "aabb" has factors of length 1: {a, b} → 2;
    # length 2: {aa, ab, bb} → 3;
    # length 3: {aab, abb} → 2;
    # length 4: {aabb} → 1.
    out = json.loads(symdyn_complexity_1d_word("aabb", 4))
    assert out["p_w"] == [2, 3, 2, 1]


def test_complexity_periodic_plateau():
    # (abc)^∞ has 3 distinct factors of each length n ≥ 3.
    out = json.loads(symdyn_complexity_1d_periodic("abc", 6))
    assert out["p_x"] == [3, 3, 3, 3, 3, 3]
    assert out["period_length"] == 3


def test_morse_hedlund_detects_periodic():
    # Periodic word (abc)^∞ has p_x(3) = 3 ≤ 3 → eventually periodic.
    out = json.loads(symdyn_morse_hedlund_check("[3, 3, 3, 3]"))
    assert out["eventually_periodic"] is True
    assert out["witness_n"] == 3


def test_morse_hedlund_no_witness_for_growing_complexity():
    # Sturmian-like: p(n) = n + 1; never ≤ n.
    values = [n + 1 for n in range(1, 11)]
    out = json.loads(symdyn_morse_hedlund_check(json.dumps(values)))
    assert out["eventually_periodic"] is False
    assert out["witness_n"] is None
