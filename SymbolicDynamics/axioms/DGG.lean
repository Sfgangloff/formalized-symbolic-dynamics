import dependencies.Subshift
import dependencies.KariCulik
import dependencies.DGG

/-! # Axioms for Durand–Gamard–Grandjean (arXiv:1312.4126)

Opaque DGG-paper constants whose definition requires significant Lean
infrastructure that has not yet been formalised. Each carries an
`@ontology` marker so the ontology back-link survives renames.

What is axiomatic here:
- `dggSubstitutivePairs` — existence of the two `2 × 2` substitutive
  pairs `(A₁, A'₁)` and `(A₂, A'₂)` of Wang patterns over the 14-tile
  DGG alphabet, each pair sharing identical north/south/east/west
  boundary colours. The explicit tiles are listed in §3 of the paper
  but not yet transcribed; see also `dgg_A1`/`dgg_A1'`/`dgg_A2`/`dgg_A2'`
  in `axioms/KariCulik.lean`.
- `cylindricityFunction` — Monteil's cylindricity function (recalled in
  DGG §4), opaque pending the underlying tilable-portion machinery.

Reference: Durand, Gamard, Grandjean. *Aperiodic tilings and entropy.*
DLT 2014 / arXiv:1312.4126v2.
-/

/-- **Construction (DGG, §3).** The two DGG substitutive pairs
`(A₁, A'₁)` and `(A₂, A'₂)` of `2 × 2` Wang patterns over the 14-tile
DGG alphabet, each pair sharing identical north/south/east/west
boundary colours. Existence-only here; the explicit tiles are listed in
§3 of the paper. -/
-- @ontology: dgg:constr:dgg-substitutive-pairs
axiom dggSubstitutivePairs :
  ∃ (W B : Finset (Lat 2)) (_hB : B ⊆ W)
    (A₁ A₁' A₂ A₂' : Pattern KCTile W),
      SubstitutivePair W B _hB A₁ A₁' ∧
      SubstitutivePair W B _hB A₂ A₂' ∧
      (A₁, A₁') ≠ (A₂, A₂')

/-- **Definition (Monteil 2012, recalled in DGG §4).** For an aperiodic
tileset `T`, the *cylindricity function* maps `n` to the smallest
growing bound on the vertical size of a tilable portion of a horizontal
cylinder of perimeter `n`. Opaque here. -/
-- @ontology: dgg:def:cylindricity
axiom cylindricityFunction {α : Type*} [TopologicalSpace α]
    (_X : Subshift α 2) : ℕ → ℕ
