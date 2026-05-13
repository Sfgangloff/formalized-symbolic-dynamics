import json
import math

from symdyn_tilings.server import (
    symdyn_lean_emit_tileset,
    symdyn_tileset_catalog_get,
    symdyn_tileset_catalog_list,
    symdyn_tilings_info,
    symdyn_wang_entropy_upper_bound,
    symdyn_wang_finite_tileability,
    symdyn_wang_periodic_search,
    symdyn_wang_transfer_matrix_size,
)


def test_info_mentions_server_and_phase():
    out = symdyn_tilings_info()
    assert "symdyn-tilings" in out
    assert "Phase B" in out


def test_catalog_list_contains_kari_culik():
    names = json.loads(symdyn_tileset_catalog_list())
    assert "kari_culik_13" in names
    assert "kari_culik_14_dgg" in names


def test_catalog_get_kari_culik_13_has_13_tiles():
    tiles = json.loads(symdyn_tileset_catalog_get("kari_culik_13"))
    assert len(tiles) == 13
    for t in tiles:
        assert set(t.keys()) == {"N", "S", "E", "W"}


def test_transfer_matrix_size_kari_culik_13():
    out = json.loads(symdyn_wang_transfer_matrix_size("kari_culik_13", 2))
    # Should be > 0 (some 2-rows are horizontally compatible) and < 13² = 169.
    assert 0 < out["n_rows"] < 169


def test_entropy_upper_bound_decreases_in_n_for_kari_culik_13():
    # The bound log ρ(M_n) / n is non-increasing in n; for KC it
    # decreases sharply.
    b1 = json.loads(symdyn_wang_entropy_upper_bound("kari_culik_13", 1))["bound"]
    b2 = json.loads(symdyn_wang_entropy_upper_bound("kari_culik_13", 2))["bound"]
    b3 = json.loads(symdyn_wang_entropy_upper_bound("kari_culik_13", 3))["bound"]
    assert b1 >= b2 >= b3
    # Each bound is a valid upper bound on the (positive) KC entropy.
    assert b3 > 0  # DGG show positive entropy, so the bound must be > 0.


def test_entropy_bound_inline_tileset():
    # Trivial 1-tile SFT (single tile, all same color): exactly one
    # tiling exists per shape, so entropy = 0.
    one_tile = json.dumps([{"N": "a", "S": "a", "E": "a", "W": "a"}])
    r1 = json.loads(symdyn_wang_entropy_upper_bound(one_tile, 1))
    r2 = json.loads(symdyn_wang_entropy_upper_bound(one_tile, 3))
    assert r1["n_rows"] == 1
    assert r2["n_rows"] == 1
    assert r1["bound"] == 0.0
    assert r2["bound"] == 0.0


def test_entropy_bound_full_kn_shift_via_unconstrained_tiles():
    # All-`*` edges on k tiles: full k-shift on Z² has entropy log k.
    for k in (2, 3):
        tiles = json.dumps(
            [{"N": "*", "S": "*", "E": "*", "W": "*"} for _ in range(k)]
        )
        r = json.loads(symdyn_wang_entropy_upper_bound(tiles, 1))
        assert r["n_rows"] == k
        # ρ(M_1) for all-1s k×k matrix is k; log k / 1 = log k.
        assert math.isclose(r["bound"], math.log(k), rel_tol=1e-9)


def test_finite_tileability_one_tile_tiles_anything():
    one_tile = json.dumps([{"N": "a", "S": "a", "E": "a", "W": "a"}])
    out = json.loads(symdyn_wang_finite_tileability(one_tile, 3, 3))
    assert out["tileable"] is True
    assert out["witness"] == [[0, 0, 0], [0, 0, 0], [0, 0, 0]]


def test_finite_tileability_kari_culik_small_rectangle():
    # 2×2 tiling of KC must exist (the shift is nonempty).
    out = json.loads(symdyn_wang_finite_tileability("kari_culik_13", 2, 2))
    assert out["tileable"] is True
    assert out["witness"] is not None


def test_periodic_search_kari_culik_is_aperiodic_at_small_periods():
    # Kari–Culik is aperiodic: no periodic tiling at any (small) period.
    for p in (1, 2, 3):
        out = json.loads(symdyn_wang_periodic_search("kari_culik_13", p, p))
        assert out["periodic"] is False, f"unexpected periodic tiling at period {p}"


def test_lean_emit_tileset_contains_name_and_tile_count():
    stub = symdyn_lean_emit_tileset("kari_culik_13", "KariCulikShift")
    assert "KariCulikShift" in stub
    assert "13 tiles" in stub
