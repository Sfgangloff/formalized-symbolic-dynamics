# Weiss conjecture — implementation checklist

Each item is a single self-contained Lean unit. Everything **except**
the conjecture statement itself lives in `dependencies/` so it can be
reused by other open problems and papers.

---

## Foundational shift-finite-type predicate (in `dependencies/Subshift.lean`)

- [x] D.S.1 `def IsSFT (X : Subshift α d) : Prop` — `∃ F L,
  X.carrier = (mkSFT F L).carrier`.
- [x] D.S.2 `theorem mkSFT_isSFT` — the obvious witness.

## Factor-map infrastructure (in `dependencies/FactorMap.lean`)

- [x] D.F.1 `structure FactorMap (Y : Subshift β d) (X : Subshift α d)`
  bundling: a function `FullShift β d → FullShift α d`, continuity,
  shift-equivariance, image-in-X.
- [x] D.F.2 `def FactorMap.IsOnto`.
- [x] D.F.3 `def FactorMap.id`, `theorem FactorMap.id_isOnto`.
- [x] D.F.4 `def IsSofic (X : Subshift α d) : Prop` — exists a finite
  alphabet `β`, an SFT, and an onto factor map onto `X`.
- [x] D.F.5 `def HasEntropyPreservingSFTCover (X : Subshift α d) : Prop`
  — same as `IsSofic` plus `topEntropy Y = topEntropy X`.
- [x] D.F.6 `theorem mkSFT_hasEntropyPreservingSFTCover`,
  `theorem mkSFT_isSofic` — sanity lemmas (every SFT is its own cover
  via the identity factor map).

## Conjecture statement (in `WeissConjecture.lean`)

- [x] W.1 `def WeissConjectureStatement (d : ℕ) : Prop` — for every
  finite alphabet `α` and every sofic `X : Subshift α d`,
  `HasEntropyPreservingSFTCover X`. **Recorded as a `def`, not proved.**

## Not started / out of scope

- Proof of the 1D case via labelled-graph right-resolving presentations.
- Any progress on the multidimensional (`d ≥ 2`) case — open conjecture.
