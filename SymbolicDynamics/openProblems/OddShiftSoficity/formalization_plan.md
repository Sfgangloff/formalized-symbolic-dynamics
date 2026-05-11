# Multidimensional odd shift — formalization plan

## Goal

Formalize the **statement** in Lean. Following the repository
convention, all supporting definitions (Cayley adjacency on `Lat d`,
connected components, the subshift `Y_d`) live in `dependencies/`; the
file `OddShiftSoficity.lean` records only the conjecture.

## Definitions to add (in `dependencies/`)

The natural home is a new file `dependencies/Percolation.lean`.

1. **`Lat.adjOne d : SimpleGraph (Lat d)`** — the Cayley graph of
   `ℤ^d` with the standard generators: `u, v` adjacent iff their
   ℓ¹-distance equals `1` (equivalently, they differ in exactly one
   coordinate by exactly `±1`).

2. **`occupiedSet (x : FullShift Bool d) : Set (Lat d)`** — the set
   `{v | x v = true}`.

3. **`SimpleGraph.induce_set (G : SimpleGraph V) (s : Set V)`** — if
   not already in Mathlib, the subgraph induced on the subset `s`.
   (Mathlib has `SimpleGraph.induce`; we may be able to reuse it
   directly.)

4. **`finiteComponentsAllOdd (x : FullShift Bool d) : Prop`** —
   shorthand for "every finite connected component of `occupiedSet x`
   under the induced subgraph of `Lat.adjOne d` has odd cardinality".

5. **`OddShift d : Subshift Bool d`** — the subshift `Y_d`:
   - `carrier := { x | finiteComponentsAllOdd x }`,
   - `isClosed` — proof that this is closed in `FullShift Bool d`,
   - `isInvariant` — proof of shift-invariance.

   Both topological properties follow because (i) the adjacency graph
   on `Lat d` is shift-invariant, and (ii) finiteness/odd-parity
   conditions on components are determined by finite-window data, so
   the carrier is intersection of clopen sets.

## Conjecture statement (in `OddShiftSoficity.lean`)

```
def OddShiftSoficityStatement (d : ℕ) : Prop :=
  IsSofic (OddShift d)
```

Recorded as a `def`, not proved.

## Out-of-scope (for the statement-only milestone)

- The `d = 1` proof (constructing an explicit SFT cover via the
  right-resolving labelled graph of the `1`-parity automaton).
- The unpublished `d = 2` proof.
- Any progress on `d ≥ 3`.

## Milestones

1. **M1** — Add `dependencies/Percolation.lean` with `Lat.adjOne`,
   `occupiedSet`, and the predicate
   `finiteComponentsAllOdd` (definitions only, compiles).
2. **M2** — Add `OddShift : ℕ → Subshift Bool d` with the closedness
   and shift-invariance proofs (this is the harder definitional
   step; expect ~50 lines using Mathlib's `SimpleGraph` /
   `connectedComponent` infrastructure).
3. **M3** — Statement: `OddShiftSoficityStatement` in
   `OddShiftSoficity.lean` (one line, depends on M2 and on
   `IsSofic` from `dependencies/FactorMap.lean`).
4. **M4** (far future) — `d = 1` proof.
5. **M5** (far future) — `d = 2` proof (porting the unpublished
   argument).
