from symdyn_complexity.server import symdyn_complexity_info


def test_info_mentions_server_name():
    out = symdyn_complexity_info()
    assert "symdyn-complexity" in out
    assert "Phase A" in out


def test_info_mentions_planned_tools():
    out = symdyn_complexity_info()
    for tool in (
        "symdyn_complexity_1d",
        "symdyn_complexity_2d",
        "symdyn_periods_2d",
        "symdyn_nivat_check_finite",
        "symdyn_morse_hedlund_test",
        "symdyn_lean_emit_complexity_lemma",
    ):
        assert tool in out
