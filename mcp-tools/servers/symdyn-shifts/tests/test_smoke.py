from symdyn_shifts.server import symdyn_shifts_info


def test_info_mentions_server_name():
    out = symdyn_shifts_info()
    assert "symdyn-shifts" in out
    assert "Phase A" in out


def test_info_mentions_planned_tools():
    out = symdyn_shifts_info()
    for tool in (
        "symdyn_sft_admissible_count",
        "symdyn_sft_entropy_1d",
        "symdyn_sofic_fischer_cover",
        "symdyn_lean_emit_subshift",
    ):
        assert tool in out
