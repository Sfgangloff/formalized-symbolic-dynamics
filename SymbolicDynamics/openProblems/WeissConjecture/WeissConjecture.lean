import dependencies.FactorMap

/-! # Weiss conjecture — entropy-preserving SFT covers of sofic shifts

**Conjecture (B. Weiss, ca. 1973).** *Every sofic `ℤ^d`-shift admits an
SFT cover of the same topological entropy.*

The conjecture is known for `d = 1` (via the right-resolving presentation
of the labelled graph of a 1D sofic shift) and **open** for `d ≥ 2`.

This file records the **statement** of the conjecture in Lean. All
supporting definitions (`IsSFT`, `FactorMap`, `IsSofic`,
`HasEntropyPreservingSFTCover`) live in `dependencies/`. We do not
attempt the proof — that's the open problem.

See [`README.md`](README.md) for the problem statement, references, and
the surrounding context. -/

/-- **Weiss conjecture (statement).** For every dimension `d`, every
finite alphabet `α`, and every sofic subshift `X : Subshift α d`,
`X` has an entropy-preserving SFT cover.

Recorded as a `Prop` (not proved). The proof would be a major open
problem for `d ≥ 2`; the `d = 1` case is a classical theorem (separate
formalization effort). -/
-- @ontology: op:weiss-conjecture
def WeissConjectureStatement (d : ℕ) : Prop :=
  ∀ (α : Type) (_ : Fintype α) (_ : DecidableEq α)
    (_ : TopologicalSpace α) (_ : T1Space α)
    (X : Subshift α d), IsSofic X → HasEntropyPreservingSFTCover X
