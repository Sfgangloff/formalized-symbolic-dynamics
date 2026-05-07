from symdyn_viz.server import symdyn_viz_info


def test_info_mentions_server_name():
    out = symdyn_viz_info()
    assert "symdyn-viz" in out
    assert "Phase A" in out


def test_info_mentions_planned_tools():
    out = symdyn_viz_info()
    for tool in (
        "symdyn_draw_pattern_2d",
        "symdyn_draw_wang_tileset",
        "symdyn_draw_wang_tiling",
        "symdyn_draw_presentation_graph",
        "symdyn_plot_complexity_curve",
    ):
        assert tool in out
