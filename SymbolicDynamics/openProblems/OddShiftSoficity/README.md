# Multidimensional odd shift — is it sofic?

**Status:** `open` (`d ≥ 3`) / `partially-solved` + `unpublished` (`d = 2`)
/ `solved` (`d = 1`, trivial).

## Statement

Fix `d ≥ 1` and view a configuration `x ∈ {0,1}^{ℤ^d}` as a percolation
on `ℤ^d`: the set `S x := {v | x v = 1}`. Put a Cayley graph structure
on `ℤ^d` with the standard generators, so two lattice points are
adjacent iff their ℓ¹-distance is exactly `1`. This induces a graph on
`S x` (the *occupied* sites), and we can talk about its connected
components.

Define

  `Y_d := { x ∈ {0,1}^{ℤ^d} | every finite component of S x has odd size }`.

**Problem.** *Is `Y_d` a sofic subshift?*

## Known cases

- **`d = 1` — solved (sofic, trivial).** In one dimension the
  components of `S x` are maximal blocks of `1`s. The condition "every
  finite block of `1`s has odd length" defines a classical sofic
  shift (it is the labelled-graph image of a small SFT with state
  parity).
- **`d = 2` — partially-solved, unpublished.** Reported proved sofic.
  (User communication; no published reference yet.)
- **`d ≥ 3` — open.**

Hochman's original note (cited below) phrases the problem only in
`d = 2` and conjectures the answer is *no*; subsequent unpublished work
in `d = 2` reverses the conjecture (positive answer). The status in
higher dimensions remains open.

## Companion even shift `X_d`

Hochman's note also introduces

  `X_d := { x | every finite component of S x has even size }`,

and remarks that `X_d` is sofic (in particular in `d = 2`) — an
"exercise". The odd shift `Y_d` is the harder cousin.

## Files in this folder

- [`README.md`](README.md) — problem statement (this file).
- [`formalization_plan.md`](formalization_plan.md) — formalization
  plan.
- [`implementation_list.md`](implementation_list.md) — implementation
  checklist.
- [`OddShiftSoficity.lean`](OddShiftSoficity.lean) — Lean formalization
  of the statement.

## References

- M. Hochman, *Is the multidimensional odd shift sofic?*,
  problem note, [PDF](https://math.huji.ac.il/~mhochman/problems/multidimensional-odd-shift.pdf).
