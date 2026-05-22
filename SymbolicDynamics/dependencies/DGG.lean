import dependencies.Subshift

/-! # Dependencies for Durand–Gamard–Grandjean (arXiv:1312.4126)

Concept-level definitions used by `papers/DurandGamardGrandjean/DGG.lean`
and by the DGG axioms in `axioms/DGG.lean`. Currently a thin module with
the substitutive-pair predicate; further DGG infrastructure (Monteil
cylindricity proofs, density predicates) will land here as it is
formalised.
-/

/-- **Definition (DGG, §3).** A *substitutive pair* for a window `W` over
alphabet `α` is a pair of distinct patterns on `W` with identical
boundary on a chosen boundary frame `B ⊆ W`. -/
-- @ontology: dgg:def:substitutive-pair
def SubstitutivePair {α : Type*} {d : ℕ} (W B : Finset (Lat d))
    (_hB : B ⊆ W) (p q : Pattern α W) : Prop :=
  p ≠ q ∧ ∀ v : B, p ⟨v.val, _hB v.property⟩ = q ⟨v.val, _hB v.property⟩
