import base64
import json

from symdyn_viz.server import (
    symdyn_draw_wang_tileset,
    symdyn_draw_wang_tiling,
    symdyn_plot_complexity_curve,
    symdyn_viz_info,
)


def test_info_mentions_phase_b():
    out = symdyn_viz_info()
    assert "symdyn-viz" in out
    assert "Phase B" in out


def _assert_png_payload(payload: dict) -> None:
    assert "image" in payload
    assert "description" in payload
    raw = base64.b64decode(payload["image"])
    # PNG magic number: 89 50 4E 47 0D 0A 1A 0A
    assert raw[:8] == b"\x89PNG\r\n\x1a\n"


def test_draw_wang_tileset_returns_png():
    tiles = json.dumps(
        [
            {"N": "a", "S": "b", "E": "x", "W": "y"},
            {"N": "b", "S": "a", "E": "y", "W": "x"},
        ]
    )
    payload = symdyn_draw_wang_tileset(tiles)
    _assert_png_payload(payload)


def test_draw_wang_tiling_returns_png():
    tiles = json.dumps([{"N": "a", "S": "a", "E": "a", "W": "a"}])
    witness = json.dumps([[0, 0, 0], [0, 0, 0]])
    payload = symdyn_draw_wang_tiling(tiles, witness)
    _assert_png_payload(payload)


def test_plot_complexity_curve_returns_png():
    values = json.dumps([2, 3, 5, 8, 13, 21])
    payload = symdyn_plot_complexity_curve(values, "golden_mean")
    _assert_png_payload(payload)
