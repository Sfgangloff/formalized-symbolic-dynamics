from symdyn_tilings.server import symdyn_tilings_info


def test_info_mentions_server_name():
    out = symdyn_tilings_info()
    assert "symdyn-tilings" in out
    assert "Phase A" in out


def test_info_mentions_planned_tools():
    out = symdyn_tilings_info()
    for tool in (
        "symdyn_wang_finite_tileability",
        "symdyn_wang_entropy_bounds",
        "symdyn_tileset_catalog_get",
        "symdyn_lean_emit_tileset",
    ):
        assert tool in out


def test_info_mentions_named_tilesets():
    out = symdyn_tilings_info()
    for name in ("berger", "robinson", "kari", "culik", "kari_culik", "jeandel_rao"):
        assert name in out
