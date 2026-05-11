# Weiss conjecture — formalization plan

## Goal

Formalize the **statement** of the Weiss conjecture in Lean (the proof is
open). Reuse `Subshift`, `mkSFT`, `topEntropy`, and `shiftMap` from
`papers/HochmanMeyerovitch/HochmanMeyerovitch.lean`. Add the missing
infrastructure (shift-equivariant continuous maps, sofic-shift predicate)
to a small companion module so other open-problems can reuse it.

## Definitions to add

1. **`FactorMap`** — a continuous, shift-equivariant map between subshifts.

   Concretely: given subshifts `X : Subshift α d` and `Y : Subshift β d`,
   a `FactorMap X Y` is the data of

   - a function `φ : FullShift α d → FullShift β d`,
   - continuity of `φ` (`Continuous φ`),
   - shift-equivariance (`φ ∘ shiftMap u = shiftMap u ∘ φ` for every `u`),
   - and the inclusion `φ '' X.carrier ⊆ Y.carrier`.

   A factor map is **onto** if `φ '' X.carrier = Y.carrier`. (By
   Curtis–Hedlund–Lyndon, continuous shift-equivariant maps between full
   shifts are exactly sliding-block codes — useful for sanity but not
   needed for stating the conjecture.)

2. **`IsSFT`** — a subshift is an SFT if it equals `mkSFT F L` for some
   finite window `F` and finite list `L`. (Some such predicate may already
   live in the HM file; check and reuse.)

3. **`IsSofic`** — a subshift `X : Subshift α d` is sofic if there exists a
   finite alphabet `β`, an SFT `Y : Subshift β d`, and an *onto* factor
   map `Y → X`. (For finite alphabets, `β` is `Fintype`.)

4. **`HasEntropyPreservingSFTCover`** — `X : Subshift α d` has an
   entropy-preserving SFT cover if there exists a finite alphabet `β`, an
   SFT `Y : Subshift β d`, and an onto factor map `Y → X` with
   `topEntropy Y = topEntropy X`.

## Conjecture statement

```
theorem WeissConjecture (α : Type) [Fintype α] [TopologicalSpace α]
    [DiscreteTopology α] {d : ℕ} (X : Subshift α d)
    (hSofic : IsSofic X) :
    HasEntropyPreservingSFTCover X
```

Marked as a `def` or `axiom` placeholder for now (the open conjecture).
We will record the statement in Lean but **not prove it**; we may instead
record a `def` that captures the conjecture body, with no claim attached.

## Companion infrastructure (dependencies)

A new file `dependencies/FactorMap.lean` provides:

- `structure FactorMap (X : Subshift α d) (Y : Subshift β d)` bundling the
  shift-equivariant continuous map and inclusion.
- `def FactorMap.IsOnto`.
- `def IsSofic`.
- A few basic lemmas (e.g. `topEntropy_image_le` — entropy can only
  decrease under factor maps, useful as immediate sanity).

This dependencies module is intentionally minimal — the Weiss file imports
it and instantiates the statement.

## Out-of-scope

- We do **not** prove the 1D case here. (Could be a separate
  `Theorem 1D-Weiss` exercise later — the construction needs labelled
  graphs and the right-resolving presentation, which is its own
  formalization milestone.)
- We do **not** axiomatize a proof of the multidimensional case. It is
  open.

## Milestones

1. **M1**: write `dependencies/FactorMap.lean` (definitions only,
   compiles).
2. **M2**: write `WeissConjecture.lean` with `IsSofic`,
   `HasEntropyPreservingSFTCover`, and the conjecture statement
   (recorded, not proved).
3. **M3** (optional): add a trivial lemma — every SFT vacuously has an
   entropy-preserving SFT cover (itself, with the identity factor map).
4. **M4** (optional, far future): prove the 1D case (separate effort).
