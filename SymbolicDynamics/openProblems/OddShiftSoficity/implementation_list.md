# Odd shift soficity — implementation checklist

Everything **except** the conjecture statement itself lives in
`dependencies/`. Tick when each item compiles.

---

## Percolation infrastructure (in `dependencies/Percolation.lean`)

- [ ] D.P.1 `def Lat.adjOne (d : ℕ) : SimpleGraph (Lat d)` — the
  Cayley graph: `u, v` adjacent iff they differ in exactly one
  coordinate by exactly `±1`.
- [ ] D.P.2 `def occupiedSet (x : FullShift Bool d) : Set (Lat d)` —
  `{v | x v = true}`.
- [ ] D.P.3 `def finiteComponentsAllOdd
       (x : FullShift Bool d) : Prop` — "every finite component of
  `occupiedSet x` under (the induced subgraph of) `Lat.adjOne d`
  has odd cardinality".
- [ ] D.P.4 `def OddShift (d : ℕ) : Subshift Bool d` —
  `carrier := { x | finiteComponentsAllOdd x }` with closedness and
  shift-invariance proofs.
- [ ] D.P.5 (optional, parallel) `def EvenShift (d : ℕ) :
       Subshift Bool d` — the companion "every finite component has
  even size" subshift.
- [ ] D.P.6 (optional) `theorem EvenShift_isSofic` — Hochman's
  exercise (specifically for `d = 2`).

## Conjecture statement (in `OddShiftSoficity.lean`)

- [ ] O.1 `def OddShiftSoficityStatement (d : ℕ) : Prop` —
  `IsSofic (OddShift d)`. Recorded as a `def`, not proved.

## Not started / out of scope

- The `d = 1` proof.
- The unpublished `d = 2` proof.
- Anything in `d ≥ 3` (open problem).
