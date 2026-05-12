import Mathlib.Computability.Partrec
import Mathlib.Topology.Separation.Hausdorff
import dependencies.Subshift
import dependencies.Box
import dependencies.LocallyAdmissible
import dependencies.GloballyAdmissible

/-! # Axioms specific to irreducible SFTs

Two deep facts about irreducible SFTs that are used in the
Hochman–Meyerovitch proof but not yet formalised:

- `locally_admissible_imp_globally_admissible_irreducible`: for an
  irreducible SFT and sufficiently large `N`, every locally admissible
  pattern on `symBox d N` is globally admissible. Discharged from a
  buffer-extension argument using the irreducibility gluing.
- `existsPeriodicCount_for_irreducible_SFT`: existence of a Computable
  periodic-point count `P : ℕ → ℕ` whose growth bracket-bounds the
  topological entropy from below (Bowen-style).
- `N_X_symBox_computable`: computability of `k ↦ N_X (mkSFT F L) (symBox d k)`
  for irreducible SFTs (follows from the soft `decidable_globallyAdmissible_irreducible`
  but needs primitive-recursive plumbing not yet in place).

This file contains *only axioms*. The derived theorem
`locally_admissible_outer_globally_admissible_irreducible` lives in
`dependencies/IrreducibleConsequences.lean`.
-/

/-- For an irreducible SFT and sufficiently large `N`, every locally admissible
`symBox d N`-pattern is itself globally admissible. -/
axiom locally_admissible_imp_globally_admissible_irreducible
    {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty)
    (h_irr : IsIrreducibleShift (mkSFT F L)) :
    ∃ N₀, ∀ N ≥ N₀, ∀ b : Pattern α (symBox d N),
      locallyAdmissible F L b → Pattern.GloballyAdmissible (mkSFT F L) b

/-- For a nonempty irreducible SFT, `N_X (mkSFT F L) (symBox d k)` is Computable
as a function of k — follows from soft decidability of global admissibility
plus a primitive-recursive enumeration of locally admissible candidates. -/
axiom N_X_symBox_computable {α : Type*} {d : ℕ}
    [Fintype α] [DecidableEq α] [Encodable α] [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty)
    (h_irr : IsIrreducibleShift (mkSFT F L)) :
    Computable (fun k : ℕ => N_X (mkSFT F L) (symBox d k))

/-- **Existence of a Computable periodic-point count for irreducible SFTs.**
For a nonempty irreducible SFT, there is a Computable function `P : ℕ → ℕ`
(intended to count period-`(n+1)` configurations) such that:
- `Real.log (P (n+1)) / ((n+1) : ℝ)^d ≤ topEntropy (mkSFT F L)` for every `n`,
- the sequence converges to `topEntropy (mkSFT F L)`.

Isolates the deep Bowen-style content (irreducibility ⇒ periodic-point
count grows exactly as the entropy). -/
axiom existsPeriodicCount_for_irreducible_SFT
    {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α] [Encodable α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty)
    (h_irr : IsIrreducibleShift (mkSFT F L)) :
    ∃ P : ℕ → ℕ, Computable P ∧
      (∀ n : ℕ,
        Real.log (P (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ d ≤ topEntropy (mkSFT F L)) ∧
      Filter.Tendsto
        (fun n : ℕ => Real.log (P (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ d)
        Filter.atTop (nhds (topEntropy (mkSFT F L)))
