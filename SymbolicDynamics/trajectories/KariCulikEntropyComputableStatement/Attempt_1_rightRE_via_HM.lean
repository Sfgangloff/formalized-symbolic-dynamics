import Mathlib.Analysis.SpecialFunctions.Log.Basic
import dependencies.Subshift
import dependencies.LocallyAdmissible
import dependencies.GloballyAdmissible
import dependencies.Entropy
import dependencies.Computable
import dependencies.IrreducibleConsequences
import dependencies.KariCulik
import axioms.KariCulik
import openProblems.KariCulikEntropy.KariCulikEntropy
import openProblems.KariCulikEntropy.generated_questions.Computability
import papers.HochmanMeyerovitch.HochmanMeyerovitch

/-! # Attempt 1 — reduce computability to irreducibility

**Targets** `KariCulikEntropyComputableStatement` (in
`openProblems/KariCulikEntropy/generated_questions/Computability.lean`).

**Outcome.** Conditional. We prove

  `IsIrreducibleShift kariCulikShift → IsComputableReal kariCulikEntropy`,

isolating the open content of the main statement on a single auxiliary
question: is the Kari–Culik shift irreducible (in the
`ShiftIrreducible`-for-some-`r > 0` sense)? A positive answer would
close `KariCulikEntropyComputableStatement` by this attempt alone.

The unconditional right-r.e. half (`kariCulikEntropy_isRightRE`) is
also recorded — it follows from `topEntropy_rightRE`
(Hochman–Meyerovitch Theorem 3.1) without irreducibility.

**Strategy.**
1. Extract `(F, L)` from `kariCulikShift_isSFT`, giving carrier
   equality `kariCulikShift.carrier = (mkSFT F L).carrier`.
2. Transport `topEntropy` along the carrier equality
   (`topEntropy_congr_carrier`, via `topEntropy_antitone` in both
   directions).
3. Transport `IsIrreducibleShift` along the carrier equality
   (`IsIrreducibleShift_congr_carrier` — this is the substantive new
   transport lemma, since `ShiftIrreducible` mentions membership
   `∈ X` four times in its quantifier alternation).
4. Apply `topEntropy_irreducible_computable` (Hochman–Meyerovitch
   Theorem 1.3, formalised in this project).

**What is *not* proved.**
- Unconditional `IsComputableReal kariCulikEntropy` —
  `IsIrreducibleShift kariCulikShift` is itself open. The Kari–Culik
  shift contains a proper minimal subsystem (Siefken 2014), which
  suggests it is reducible; but a clean topological-irreducibility
  obstruction has not, to our knowledge, been written down.
-/

namespace KariCulikComputabilityAttempt1

/-- Topological entropy depends only on the carrier. -/
private theorem topEntropy_congr_carrier {α : Type*} {d : ℕ} [Fintype α]
    [TopologicalSpace α] {X Y : Subshift α d}
    (h : X.carrier = Y.carrier) : topEntropy X = topEntropy Y :=
  le_antisymm (topEntropy_antitone h.le) (topEntropy_antitone h.ge)

/-- Membership in a subshift is determined by its carrier. -/
private theorem mem_iff_of_carrier_eq {α : Type*} {d : ℕ}
    [TopologicalSpace α] {X Y : Subshift α d} (h : X.carrier = Y.carrier)
    {x : FullShift α d} : x ∈ X ↔ x ∈ Y := by
  simp only [Subshift.mem_iff, h]

/-- `ShiftIrreducible` depends only on the carrier of a subshift. -/
private theorem ShiftIrreducible_congr_carrier {α : Type*} {d : ℕ}
    [TopologicalSpace α] {X Y : Subshift α d} (h : X.carrier = Y.carrier)
    (r : ℕ) : ShiftIrreducible X r ↔ ShiftIrreducible Y r := by
  unfold ShiftIrreducible
  refine ⟨fun hX A B hsep a b ha hb => ?_, fun hY A B hsep a b ha hb => ?_⟩
  · obtain ⟨xa, hxa, hxa'⟩ := ha
    obtain ⟨xb, hxb, hxb'⟩ := hb
    have ha' : ∃ x ∈ X, Pattern.AppearsAt a x 0 :=
      ⟨xa, (mem_iff_of_carrier_eq h).mpr hxa, hxa'⟩
    have hb' : ∃ x ∈ X, Pattern.AppearsAt b x 0 :=
      ⟨xb, (mem_iff_of_carrier_eq h).mpr hxb, hxb'⟩
    obtain ⟨x, hxX, h1, h2⟩ := hX A B hsep a b ha' hb'
    exact ⟨x, (mem_iff_of_carrier_eq h).mp hxX, h1, h2⟩
  · obtain ⟨xa, hxa, hxa'⟩ := ha
    obtain ⟨xb, hxb, hxb'⟩ := hb
    have ha' : ∃ x ∈ Y, Pattern.AppearsAt a x 0 :=
      ⟨xa, (mem_iff_of_carrier_eq h).mp hxa, hxa'⟩
    have hb' : ∃ x ∈ Y, Pattern.AppearsAt b x 0 :=
      ⟨xb, (mem_iff_of_carrier_eq h).mp hxb, hxb'⟩
    obtain ⟨x, hxY, h1, h2⟩ := hY A B hsep a b ha' hb'
    exact ⟨x, (mem_iff_of_carrier_eq h).mpr hxY, h1, h2⟩

/-- `IsIrreducibleShift` depends only on the carrier of a subshift. -/
private theorem IsIrreducibleShift_congr_carrier {α : Type*} {d : ℕ}
    [TopologicalSpace α] {X Y : Subshift α d} (h : X.carrier = Y.carrier) :
    IsIrreducibleShift X ↔ IsIrreducibleShift Y := by
  unfold IsIrreducibleShift
  exact exists_congr fun r => and_congr_right fun _ =>
    ShiftIrreducible_congr_carrier h r

end KariCulikComputabilityAttempt1

open KariCulikComputabilityAttempt1

/-- **Unconditional partial result.** The topological entropy of the
Kari–Culik shift is right recursively enumerable, by transporting
Hochman–Meyerovitch Theorem 3.1 along the carrier equality
`kariCulikShift.carrier = (mkSFT F L).carrier` supplied by
`kariCulikShift_isSFT`. -/
theorem kariCulikEntropy_isRightRE : IsRightRE kariCulikEntropy := by
  obtain ⟨F, L, h_eq⟩ := kariCulikShift_isSFT
  have h_top : topEntropy kariCulikShift = topEntropy (mkSFT F L) :=
    topEntropy_congr_carrier h_eq
  have h_ne : (mkSFT F L).carrier.Nonempty := by
    rw [← h_eq]; exact kariCulikShift_carrier_nonempty
  change IsRightRE (topEntropy kariCulikShift)
  rw [h_top]
  exact topEntropy_rightRE F L h_ne

/-- **Main result of this attempt.** If the Kari–Culik shift is
irreducible (in the `ShiftIrreducible`-for-some-`r > 0` sense), then
its topological entropy is computable as a real.

This reduces `KariCulikEntropyComputableStatement` to the single open
question:

> **Is the Kari–Culik shift irreducible?**

A positive answer would close the computability question outright.
-/
theorem kariCulikEntropy_isComputableReal_of_irreducible
    (h_irr : IsIrreducibleShift kariCulikShift) :
    IsComputableReal kariCulikEntropy := by
  obtain ⟨F, L, h_eq⟩ := kariCulikShift_isSFT
  have h_top : topEntropy kariCulikShift = topEntropy (mkSFT F L) :=
    topEntropy_congr_carrier h_eq
  have h_ne : (mkSFT F L).carrier.Nonempty := by
    rw [← h_eq]; exact kariCulikShift_carrier_nonempty
  have h_irr' : IsIrreducibleShift (mkSFT F L) :=
    (IsIrreducibleShift_congr_carrier h_eq).mp h_irr
  change IsComputableReal (topEntropy kariCulikShift)
  rw [h_top]
  exact topEntropy_irreducible_computable F L h_ne h_irr'

/-! ## Numerical interval bounds

Combining the positive-entropy axiom with the universal upper bound
`topEntropy_le_log_card` from `dependencies/Entropy.lean` pins
`kariCulikEntropy` to the half-open interval `(0, log 13]`. -/

/-- **Upper bound** by `log |α|`. The Kari–Culik entropy is at most the
log of the alphabet size, by the universal SFT entropy bound. -/
theorem kariCulikEntropy_le_log_card :
    kariCulikEntropy ≤ Real.log (Fintype.card KCTile) :=
  topEntropy_le_log_card kariCulikShift

/-- **Numerical upper bound.** `kariCulikEntropy ≤ log 13`. -/
theorem kariCulikEntropy_le_log_13 :
    kariCulikEntropy ≤ Real.log 13 := by
  have h := kariCulikEntropy_le_log_card
  have hcard : Fintype.card KCTile = 13 := by
    simp [KCTile, Fintype.card_fin]
  rw [hcard] at h
  exact_mod_cast h

/-- **Interval bound.** `0 < kariCulikEntropy ≤ log 13`. Combines
`kariCulikShift_entropy_pos` (Durand–Gamard–Grandjean 2013) with the
universal upper bound. -/
theorem kariCulikEntropy_bounds :
    0 < kariCulikEntropy ∧ kariCulikEntropy ≤ Real.log 13 :=
  ⟨kariCulikShift_entropy_pos, kariCulikEntropy_le_log_13⟩

/-- **Summary under irreducibility.** Assuming the Kari–Culik shift is
irreducible (the open auxiliary question), the entropy is a computable
real in the interval `(0, log 13]`. -/
theorem kariCulikEntropy_full_picture_under_irreducible
    (h_irr : IsIrreducibleShift kariCulikShift) :
    IsComputableReal kariCulikEntropy ∧
      0 < kariCulikEntropy ∧
      kariCulikEntropy ≤ Real.log 13 :=
  ⟨kariCulikEntropy_isComputableReal_of_irreducible h_irr,
   kariCulikShift_entropy_pos,
   kariCulikEntropy_le_log_13⟩

/-! ## Open content of `KariCulikEntropyComputableStatement`

Since `IsRightRE kariCulikEntropy` is unconditional
(`kariCulikEntropy_isRightRE`), and `IsComputableReal` factors as
`IsLeftRE ∧ IsRightRE` (`computable_iff_leftRE_and_rightRE` in
`dependencies/Computable.lean`), the open computability question
reduces *precisely* to whether `kariCulikEntropy` is **left** r.e. -/

/-- **The open content of `KariCulikEntropyComputableStatement` is
exactly `IsLeftRE kariCulikEntropy`.** The right-r.e. half is already
established unconditionally; combining the two gives `IsComputableReal`
via `computable_iff_leftRE_and_rightRE`. -/
theorem kariCulikEntropy_isComputableReal_iff_isLeftRE :
    IsComputableReal kariCulikEntropy ↔ IsLeftRE kariCulikEntropy := by
  refine ⟨computable_imp_leftRE, fun h_left => ?_⟩
  exact computable_iff_leftRE_and_rightRE.mpr ⟨h_left, kariCulikEntropy_isRightRE⟩

/-- Named-Prop version: `KariCulikEntropyComputableStatement` is
equivalent to `IsLeftRE kariCulikEntropy`. -/
theorem KariCulikEntropyComputableStatement_iff_isLeftRE :
    KariCulikEntropyComputableStatement ↔ IsLeftRE kariCulikEntropy :=
  kariCulikEntropy_isComputableReal_iff_isLeftRE

/-! ## A strictly weaker sufficient condition

The conditional `kariCulikEntropy_isComputableReal_of_irreducible`
requires `kariCulikShift` *itself* to be irreducible. But a reducible
SFT can still admit an irreducible "maximum-entropy component" — a
sub-SFT whose entropy matches the original. We record the
corresponding strictly weaker sufficient condition.

For instance: if `kariCulikShift` decomposes as the disjoint union of
its zero-entropy Sturmian-row sub-system (which is *minimal*, hence
irreducible-with-zero-entropy; Siefken 2014) together with a positive-
entropy irreducible component, then this weaker condition is satisfied
even though `kariCulikShift` as a whole is not irreducible. -/

/-- **Strictly weaker reduction.** If there exists an irreducible
sub-SFT `Y` of `kariCulikShift` realising the full entropy
(`topEntropy Y = kariCulikEntropy`), then `kariCulikEntropy` is
computable.

This is **strictly weaker** than full irreducibility of
`kariCulikShift`: irreducibility of the whole gives the hypothesis
with `Y := kariCulikShift`, but the converse fails — a *reducible*
SFT may admit an irreducible sub-SFT with maximal entropy.

The `hY_sub` hypothesis is not used in the proof (the proof goes
through any irreducible SFT with matching entropy), but is recorded
to document the intended use: search among sub-SFTs of
`kariCulikShift`. -/
theorem kariCulikEntropy_isComputableReal_of_irreducible_full_subshift
    (Y : Subshift KCTile 2) (_hY_sub : Y.carrier ⊆ kariCulikShift.carrier)
    (hY_SFT : IsSFT Y) (hY_ne : Y.carrier.Nonempty)
    (hY_irr : IsIrreducibleShift Y)
    (hY_entropy : topEntropy Y = kariCulikEntropy) :
    IsComputableReal kariCulikEntropy := by
  obtain ⟨F, L, h_eq⟩ := hY_SFT
  have h_top_Y : topEntropy Y = topEntropy (mkSFT F L) :=
    topEntropy_congr_carrier h_eq
  have h_ne_mk : (mkSFT F L).carrier.Nonempty := by
    rw [← h_eq]; exact hY_ne
  have h_irr_mk : IsIrreducibleShift (mkSFT F L) :=
    (IsIrreducibleShift_congr_carrier h_eq).mp hY_irr
  have h_comp : IsComputableReal (topEntropy (mkSFT F L)) :=
    topEntropy_irreducible_computable F L h_ne_mk h_irr_mk
  rw [← hY_entropy, h_top_Y]
  exact h_comp

/-- **Cross-check that the new reduction subsumes the irreducibility
one.** The original conditional
`kariCulikEntropy_isComputableReal_of_irreducible` factors through the
sub-SFT version with `Y := kariCulikShift`. -/
example (h_irr : IsIrreducibleShift kariCulikShift) :
    IsComputableReal kariCulikEntropy :=
  kariCulikEntropy_isComputableReal_of_irreducible_full_subshift
    kariCulikShift (Set.Subset.refl _) kariCulikShift_isSFT
    kariCulikShift_carrier_nonempty h_irr rfl
