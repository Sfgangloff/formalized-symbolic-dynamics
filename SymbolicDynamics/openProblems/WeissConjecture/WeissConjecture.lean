import dependencies.FactorMap

/-! # Weiss conjecture — entropy-preserving SFT covers of sofic shifts

**Conjecture (B. Weiss, ca. 1973).** *Every sofic `ℤ^d`-shift admits an
SFT cover of the same topological entropy.*

The conjecture is known for `d = 1` (via the right-resolving presentation
of the labelled graph of a 1D sofic shift) and **open** for `d ≥ 2`.

This file records the **statement** of the conjecture in Lean, plus a
few trivial sanity lemmas. We do not attempt the proof — that's the open
problem.

See [`README.md`](README.md) for the problem statement, references, and
the surrounding context. The companion file
[`dependencies/FactorMap.lean`](../../dependencies/FactorMap.lean)
provides the `FactorMap` and `IsSofic` definitions. -/

/-- A subshift `X : Subshift α d` is a **shift of finite type (SFT)** if
it equals `mkSFT F L` for some finite window `F` and finite list of
allowed `F`-patterns `L`. -/
def IsSFT {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    (X : Subshift α d) : Prop :=
  ∃ (F : Finset (Lat d)) (L : Finset (Pattern α F)),
    X.carrier = (mkSFT F L).carrier

/-- Every `mkSFT F L` is, by definition, an SFT. -/
theorem mkSFT_isSFT {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) :
    IsSFT (mkSFT F L) := ⟨F, L, rfl⟩

/-- A subshift `X : Subshift α d` has an **entropy-preserving SFT cover**
if there exists a finite alphabet `β`, an SFT `Y : Subshift β d`, and an
onto factor map `Y → X` with `topEntropy Y = topEntropy X`. -/
def HasEntropyPreservingSFTCover {α : Type*} {d : ℕ}
    [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) : Prop :=
  ∃ (β : Type) (_ : Fintype β) (_ : DecidableEq β)
    (_ : TopologicalSpace β) (_ : T1Space β)
    (F : Finset (Lat d)) (L : Finset (Pattern β F))
    (π : FactorMap (mkSFT F L) X), π.IsOnto ∧
      topEntropy (mkSFT F L) = topEntropy X

/-- **Weiss conjecture (statement).** For every dimension `d`, every
finite alphabet `α`, and every sofic subshift `X : Subshift α d`,
`X` has an entropy-preserving SFT cover.

Recorded as a `Prop` (not proved). The proof would be a major open
problem for `d ≥ 2`; the `d = 1` case is a classical theorem (separate
formalization effort). -/
def WeissConjectureStatement (d : ℕ) : Prop :=
  ∀ (α : Type) (_ : Fintype α) (_ : DecidableEq α)
    (_ : TopologicalSpace α) (_ : T1Space α)
    (X : Subshift α d), IsSofic X → HasEntropyPreservingSFTCover X

/-! ## Trivial sanity lemmas

Every SFT trivially has an entropy-preserving SFT cover (itself, via the
identity factor map). Every SFT is sofic for the same reason. -/

/-- Every SFT is its own entropy-preserving SFT cover, via the identity
factor map. -/
theorem mkSFT_hasEntropyPreservingSFTCover
    {α : Type} {d : ℕ} [Fintype α] [DecidableEq α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) :
    HasEntropyPreservingSFTCover (mkSFT F L) :=
  ⟨α, inferInstance, inferInstance, inferInstance, inferInstance,
    F, L, FactorMap.id (mkSFT F L),
    FactorMap.id_isOnto _, rfl⟩

/-- Every `mkSFT` is sofic — it factors onto itself via the identity. -/
theorem mkSFT_isSofic {α : Type} {d : ℕ} [Fintype α] [DecidableEq α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) :
    IsSofic (mkSFT F L) :=
  ⟨α, inferInstance, inferInstance, inferInstance, inferInstance,
    F, L, FactorMap.id (mkSFT F L), FactorMap.id_isOnto _⟩
