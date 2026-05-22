import dependencies.Subshift
import dependencies.LocallyAdmissible
import dependencies.FactorMap
import dependencies.Computable

/-! # Hochman–Meyerovitch — open problems

Open questions raised explicitly in the body of HM (math/0703206), recorded
as `Prop`-valued `def`s in the project convention. Each carries an
`@ontology` marker so the back-link from the ontology graph survives renames.
-/

/-- **Converse of Theorem 1.3.** Is irreducibility necessary for the
topological entropy of a nonempty SFT to be computable? Equivalently:
does `IsComputableReal (topEntropy (mkSFT F L))` imply
`IsIrreducibleShift (mkSFT F L)` for every nonempty `mkSFT F L`?

Raised explicitly in §1 of HM, immediately after Theorem 1.3. -/
-- @ontology: hm:op:irr-converse
def HM_OpenProblem_irreducibility_necessary (d : ℕ) : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] [Encodable α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)),
    (mkSFT F L).carrier.Nonempty →
    IsComputableReal (topEntropy (mkSFT F L)) →
    IsIrreducibleShift (mkSFT F L)

/-- **Entropy-preserving SFT cover for sofic shifts** (`d ≥ 2`). Does every
nonempty sofic shift admit an SFT extension of equal topological entropy?

Multidimensional analog of the Coven–Paul covering theorem (1975); a
partial result for `d = 2` and equal entropy is in Desai (2006). Recorded
as the `HasEntropyPreservingSFTCover` predicate from
`dependencies/FactorMap.lean`. -/
-- @ontology: hm:op:sofic-covering
def HM_OpenProblem_sofic_covering (d : ℕ) (_hd : 2 ≤ d) : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α]
    [TopologicalSpace α] [T1Space α]
    (Y : Subshift α d), Y.carrier.Nonempty → IsSofic Y →
    HasEntropyPreservingSFTCover Y
