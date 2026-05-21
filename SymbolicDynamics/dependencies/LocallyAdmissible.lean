import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Separation.Hausdorff
import dependencies.Subshift
import dependencies.Box

/-! # Local admissibility and shift-irreducibility

Local admissibility of a finite pattern for a syntax `(F, L)`, the
finite reformulation via `relevantOffsets`, and decidability;
shift-irreducibility (`ShiftIrreducible`, `IsIrreducibleShift`) and its
basic consequences for global admissibility.

Originally lived in `papers/HochmanMeyerovitch/HochmanMeyerovitch.lean`;
moved here for reuse across papers.
-/

/-! ## `locallyAdmissible` and the finite reformulation -/

/-- Pattern `a` over `E` is locally admissible for syntax `(F, L)` if for every
    translate `F + u ⊆ E` the de-translated restriction lands in `L`. -/
-- @ontology: hm:def:locally-admissible
def locallyAdmissible {α : Type*} {d : ℕ} {E : Finset (Lat d)}
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (a : Pattern α E) : Prop :=
  ∀ u : Lat d, ∀ (h : ∀ v : F, v.val + u ∈ E),
    (fun v : F => a ⟨v.val + u, h v⟩) ∈ L

/-- Finite set of offsets `u : Lat d` such that translating `F` by `u` keeps it within `E`.
For empty `F` this returns `{0}` as a placeholder (the locally-admissible condition is
then independent of `u`). -/
def relevantOffsets {d : ℕ} (F E : Finset (Lat d)) : Finset (Lat d) :=
  if F = ∅ then {(0 : Lat d)}
  else
    ((F ×ˢ E).image (fun p : Lat d × Lat d => p.2 - p.1)).filter
      (fun u => ∀ w ∈ F, w + u ∈ E)

theorem locallyAdmissible_iff_relevantOffsets {α : Type*} {d : ℕ}
    {E : Finset (Lat d)} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (a : Pattern α E) :
    locallyAdmissible F L a ↔
    ∀ u ∈ relevantOffsets F E, ∀ (h : ∀ v : F, v.val + u ∈ E),
      (fun v : F => a ⟨v.val + u, h v⟩) ∈ L := by
  constructor
  · intro hloc u _ h
    exact hloc u h
  · intro hloc u h
    by_cases hF : F = ∅
    · subst hF
      have h0_rel : (0 : Lat d) ∈ relevantOffsets (∅ : Finset (Lat d)) E := by
        unfold relevantOffsets
        rw [if_pos rfl]
        exact Finset.mem_singleton.mpr rfl
      have h0_triv : ∀ v : ((∅ : Finset (Lat d)) : Finset (Lat d)), v.val + 0 ∈ E :=
        fun v => absurd v.property (Finset.notMem_empty v.val)
      have h0_apply := hloc 0 h0_rel h0_triv
      have heq : (fun v : ((∅ : Finset (Lat d)) : Finset (Lat d)) => a ⟨v.val + u, h v⟩) =
          (fun v : ((∅ : Finset (Lat d)) : Finset (Lat d)) => a ⟨v.val + 0, h0_triv v⟩) := by
        funext v
        exact absurd v.property (Finset.notMem_empty v.val)
      rw [heq]; exact h0_apply
    · have hu_in : u ∈ relevantOffsets F E := by
        unfold relevantOffsets
        rw [if_neg hF, Finset.mem_filter]
        refine ⟨?_, fun w hw => h ⟨w, hw⟩⟩
        obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hF
        simp only [Finset.mem_image, Finset.mem_product]
        refine ⟨(v, v + u), ⟨hv, h ⟨v, hv⟩⟩, by simp⟩
      exact hloc u hu_in h

instance decidable_locallyAdmissible {α : Type*} {d : ℕ} [DecidableEq α]
    {E : Finset (Lat d)} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (a : Pattern α E) :
    Decidable (locallyAdmissible F L a) :=
  decidable_of_iff _ (locallyAdmissible_iff_relevantOffsets F L a).symm

/-! ## Shift-irreducibility -/

/-- Subshift `X` is `r`-irreducible if every two globally admissible patterns on
    supports that are at least `r` apart (in ℓ∞) can be simultaneously realized. -/
def ShiftIrreducible {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X : Subshift α d) (r : ℕ) : Prop :=
  ∀ (A B : Finset (Lat d)),
    (∀ u ∈ A, ∀ v ∈ B, (r : ℤ) ≤ Lat.supNorm (u - v)) →
    ∀ (a : Pattern α A) (b : Pattern α B),
      (∃ x ∈ X, Pattern.AppearsAt a x 0) →
      (∃ x ∈ X, Pattern.AppearsAt b x 0) →
      ∃ x ∈ X, Pattern.AppearsAt a x 0 ∧ Pattern.AppearsAt b x 0

/-- A subshift is irreducible if it is `r`-irreducible for some `r > 0`. -/
-- @ontology: hm:def:irreducible-sft
def IsIrreducibleShift {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X : Subshift α d) : Prop :=
  ∃ r : ℕ, 0 < r ∧ ShiftIrreducible X r

/-- Irreducibility is monotone in the gap parameter: an `r`-irreducible
subshift is also `r'`-irreducible for any `r' ≥ r`. -/
theorem ShiftIrreducible.mono {α : Type*} {d : ℕ} [TopologicalSpace α]
    {X : Subshift α d} {r r' : ℕ} (hrr' : r ≤ r')
    (hirr : ShiftIrreducible X r) :
    ShiftIrreducible X r' := by
  intro A B h_sep a b ha hb
  apply hirr A B ?_ a b ha hb
  intro u hu v hv
  exact le_trans (by exact_mod_cast hrr') (h_sep u hu v hv)

/-! ## Geometric threshold for the irreducibility constant -/

/-- For any `r₀, k`, there exists `N₀` such that for all `N ≥ N₀`, both
`Nat.sqrt N ≥ r₀` and `k + Nat.sqrt N + 1 ≤ N` hold. -/
theorem exists_threshold_sqrt (r₀ k : ℕ) :
    ∃ N₀, ∀ N ≥ N₀, r₀ ≤ Nat.sqrt N ∧ k + Nat.sqrt N + 1 ≤ N := by
  refine ⟨(k + r₀ + 2)^2, fun N hN => ?_⟩
  have h_sqrt_ge : k + r₀ + 2 ≤ Nat.sqrt N := by
    have : Nat.sqrt ((k + r₀ + 2)^2) ≤ Nat.sqrt N := Nat.sqrt_le_sqrt hN
    rwa [Nat.sqrt_eq'] at this
  refine ⟨?_, ?_⟩
  · have : r₀ ≤ k + r₀ + 2 := by omega
    exact this.trans h_sqrt_ge
  · have h_sq : Nat.sqrt N * Nat.sqrt N ≤ N := by
      have := Nat.sqrt_le' N; rw [pow_two] at this; exact this
    have h_sqrt_ge_k : k + 2 ≤ Nat.sqrt N := by omega
    have : Nat.sqrt N * (k + 2) ≤ Nat.sqrt N * Nat.sqrt N :=
      Nat.mul_le_mul_left _ h_sqrt_ge_k
    have : Nat.sqrt N * (k + 2) ≤ N := this.trans h_sq
    have h_sqrt_pos : 1 ≤ Nat.sqrt N := by omega
    nlinarith [h_sq, h_sqrt_ge_k, h_sqrt_pos]

namespace Pattern

/-! ## Bridges between global and local admissibility -/

@[simp]
theorem globallyAdmissible_iff_exists_offset {α : Type*} {d : ℕ} [TopologicalSpace α]
    {F : Finset (Lat d)} (X : Subshift α d) (p : Pattern α F) :
    GloballyAdmissible X p ↔ ∃ x ∈ X, ∃ u : Lat d, AppearsAt p x u :=
  Iff.rfl

theorem globally_imp_locally {α : Type*} {d : ℕ} [TopologicalSpace α] [T1Space α]
    {E : Finset (Lat d)} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (p : Pattern α E)
    (hp : GloballyAdmissible (mkSFT F L) p) : locallyAdmissible F L p := by
  obtain ⟨x, hxX, offset, happ⟩ := hp
  intro u hu
  have hadm : SFT_admissible F L x := (mem_mkSFT F L x).mp hxX
  have key : ofColoring F (FullShift.shiftMap (u + offset) x) ∈ L := hadm (u + offset)
  have heq : ofColoring F (FullShift.shiftMap (u + offset) x) =
      fun v : F => p ⟨v.val + u, hu v⟩ := by
    ext v
    simp only [ofColoring, FullShift.shiftMap, ← add_assoc]
    exact happ ⟨v.val + u, hu v⟩
  rwa [heq] at key

theorem globallyAdmissible_restrict {α : Type*} {d : ℕ} [TopologicalSpace α]
    {X : Subshift α d} {F : Finset (Lat d)} (G : Finset (Lat d)) (hGF : G ⊆ F)
    {p : Pattern α F} (hp : Pattern.GloballyAdmissible X p) :
    Pattern.GloballyAdmissible X (Pattern.restrict G hGF p) := by
  obtain ⟨x, hxX, u, happ⟩ := hp
  refine ⟨x, hxX, u, ?_⟩
  intro v
  exact happ ⟨v.val, hGF v.property⟩

theorem globallyAdmissible_iff_appearsAt_zero {α : Type*} {d : ℕ}
    [TopologicalSpace α] {X : Subshift α d} {F : Finset (Lat d)} (p : Pattern α F) :
    Pattern.GloballyAdmissible X p ↔ ∃ x ∈ X, Pattern.AppearsAt p x 0 := by
  constructor
  · rintro ⟨x, hx, u, happ⟩
    refine ⟨FullShift.shiftMap u x, X.isInvariant u x hx, ?_⟩
    intro v
    have : (FullShift.shiftMap u x) (v.val + 0) = x (v.val + u) := by
      simp [FullShift.shiftMap]
    rw [this]
    exact happ v
  · rintro ⟨x, hx, happ⟩
    exact ⟨x, hx, 0, happ⟩

end Pattern

/-! ## Decidability of global admissibility for irreducible SFTs (soft-discharged) -/

/-- For a nonempty `r`-irreducible SFT, `GloballyAdmissible X a` on
patterns over `symBox d k` is decidable via `Classical.dec`. The original
`axiom decidable_globallyAdmissible_irreducible : Decidable (...)` adds
nothing beyond classical decidability and is reduced here. -/
noncomputable def decidable_globallyAdmissible_irreducible {α : Type*} {d : ℕ}
    [Fintype α] [DecidableEq α] [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (_hX : (mkSFT F L).carrier.Nonempty)
    (_h_irr : IsIrreducibleShift (mkSFT F L))
    {k : ℕ} (a : Pattern α (symBox d k)) :
    Decidable (Pattern.GloballyAdmissible (mkSFT F L) a) :=
  Classical.dec _
