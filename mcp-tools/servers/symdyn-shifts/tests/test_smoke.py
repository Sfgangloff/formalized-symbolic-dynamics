import json
import math

from symdyn_shifts.server import (
    symdyn_sft_admissible_count,
    symdyn_sft_entropy_1d,
    symdyn_lean_emit_subshift,
    symdyn_shifts_info,
)


def test_info_mentions_phase_b():
    out = symdyn_shifts_info()
    assert "symdyn-shifts" in out
    assert "Phase B" in out


def test_golden_mean_admissible_count_is_fibonacci():
    # No "11" over {0,1}: |L_n| follows Fibonacci.
    counts = [
        json.loads(symdyn_sft_admissible_count("01", "11", n))["count"]
        for n in range(1, 7)
    ]
    # n=1: 2 (0, 1); n=2: 3 (00, 01, 10); n=3: 5; etc.
    assert counts == [2, 3, 5, 8, 13, 21]


def test_golden_mean_entropy_is_log_phi():
    out = json.loads(symdyn_sft_entropy_1d("01", "11"))
    phi = (1 + math.sqrt(5)) / 2
    assert math.isclose(out["entropy"], math.log(phi), rel_tol=1e-6)


def test_full_shift_entropy_is_log_k():
    # Empty forbidden set: full k-shift.
    for k, sigma in [(2, "01"), (3, "012")]:
        out = json.loads(symdyn_sft_entropy_1d(sigma, "[]"))
        assert math.isclose(out["entropy"], math.log(k), rel_tol=1e-6)


def test_lean_emit_subshift_contains_name():
    stub = symdyn_lean_emit_subshift("01", "11", "GoldenMean")
    assert "GoldenMean" in stub
    assert "Subshift" in stub
