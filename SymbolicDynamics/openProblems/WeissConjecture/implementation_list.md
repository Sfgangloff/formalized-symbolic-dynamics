# Weiss conjecture — implementation checklist

Each item is a single self-contained Lean unit. Tick when it compiles.

---

## Dependencies (in `dependencies/FactorMap.lean`)

- [ ] D.1 `structure FactorMap (X : Subshift α d) (Y : Subshift β d)`
  bundling: a function `FullShift α d → FullShift β d`, continuity,
  shift-equivariance, image-in-Y.
- [ ] D.2 `def FactorMap.IsOnto`.
- [ ] D.3 `def FactorMap.id` — identity factor map `FactorMap X X`.
- [ ] D.4 `theorem FactorMap.id_isOnto`.

## Subshift predicates (in `WeissConjecture.lean`)

- [ ] W.1 `def IsSFT (X : Subshift α d) : Prop` — `∃ F L, X = mkSFT F L`.
- [ ] W.2 `theorem mkSFT_isSFT` — the obvious witness.
- [ ] W.3 `def IsSofic (X : Subshift α d) : Prop` — exists a finite
  alphabet `β`, an SFT `Y : Subshift β d`, and an onto factor map `Y → X`.

## Conjecture statement

- [ ] W.4 `def HasEntropyPreservingSFTCover (X : Subshift α d) : Prop` —
  exists `β`, SFT `Y : Subshift β d`, onto factor map `Y → X`,
  `topEntropy Y = topEntropy X`.
- [ ] W.5 `def WeissConjectureStatement (d : ℕ) : Prop` — for every
  finite alphabet `α` and every sofic `X : Subshift α d`,
  `HasEntropyPreservingSFTCover X`. **Recorded as a `def`, not proved.**

## Trivial sanity lemmas

- [ ] W.6 `theorem isSFT_imp_hasEntropyPreservingSFTCover` — every SFT
  trivially has an entropy-preserving cover (itself via the identity).
- [ ] W.7 `theorem isSFT_imp_isSofic` — every SFT is sofic via the
  identity factor map.

## Not started / out of scope

- Proof of the 1D case via labelled-graph right-resolving presentations.
- Any progress on the multidimensional case.
