import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic
import dependencies.Subshift
import dependencies.Box
import dependencies.LocallyAdmissible

/-! # Globally admissible patterns: counts and `r`-compatibility

Basic properties of `N_X`, the count of globally admissible patterns;
the `r`-compatibility predicate used in gluing arguments via
shift-irreducibility; and the finite/computable count `N_bar` of
locally admissible `box d n`-patterns, with the bridge `N_X ≤ N_bar`.

Originally lived in `papers/HochmanMeyerovitch/HochmanMeyerovitch.lean`;
moved here for reuse. The definitions of `N_X` and `Pattern.GloballyAdmissible`
themselves live in `dependencies/Subshift.lean`.
-/

/-! ## Basic properties of `N_X` -/

theorem N_X_pos_of_nonempty {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) (F : Finset (Lat d)) (hX : X.carrier.Nonempty) :
    0 < N_X X F := by
  obtain ⟨x, hx⟩ := hX
  rw [N_X, Set.ncard_pos]
  refine ⟨Pattern.ofColoring F x, x, hx, 0, ?_⟩
  intro v
  simp [Pattern.ofColoring]

theorem N_X_pos_iff_nonempty {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) (F : Finset (Lat d)) :
    0 < N_X X F ↔ X.carrier.Nonempty := by
  constructor
  · intro hpos
    rw [N_X, Set.ncard_pos] at hpos
    obtain ⟨_, x, hx, _⟩ := hpos
    exact ⟨x, hx⟩
  · exact N_X_pos_of_nonempty X F

/-- If `F ⊆ G`, then there are at most as many globally admissible `F`-patterns as
globally admissible `G`-patterns: every `F`-pattern arises as a restriction. -/
theorem N_X_mono_support {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) {F G : Finset (Lat d)} (hFG : F ⊆ G) :
    N_X X F ≤ N_X X G := by
  unfold N_X
  refine le_trans ?_ (Set.ncard_image_le (Set.toFinite _)
    (f := fun q : Pattern α G => Pattern.restrict F hFG q))
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro p ⟨x, hxX, u, happ⟩
  refine ⟨Pattern.ofColoring G (FullShift.shiftMap u x), ?_, ?_⟩
  · refine ⟨FullShift.shiftMap u x, X.isInvariant u x hxX, 0, ?_⟩
    intro v
    show (FullShift.shiftMap u x) (v.val + 0) = (FullShift.shiftMap u x) v.val
    simp
  · funext v
    show (FullShift.shiftMap u x) v.val = p v
    have : (FullShift.shiftMap u x) v.val = x (v.val + u) := by simp [FullShift.shiftMap]
    rw [this]
    exact happ v

theorem N_X_submultiplicative {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) {F G : Finset (Lat d)} :
    N_X X (F ∪ G) ≤ N_X X F * N_X X G := by
  unfold N_X
  rw [← Set.ncard_prod]
  refine Set.ncard_le_ncard_of_injOn
    (fun p : Pattern α (F ∪ G) =>
      ((fun v : F => p ⟨v.val, Finset.mem_union_left _ v.property⟩),
       (fun v : G => p ⟨v.val, Finset.mem_union_right _ v.property⟩)))
    ?_ ?_ (Set.toFinite _)
  · rintro p ⟨x, hxX, u, happ⟩
    exact ⟨⟨x, hxX, u, fun v => happ ⟨v.val, _⟩⟩,
           ⟨x, hxX, u, fun v => happ ⟨v.val, _⟩⟩⟩
  · intro p _ q _ hpq
    ext ⟨v, hv⟩
    rcases Finset.mem_union.mp hv with hvF | hvG
    · exact congr_fun (congr_arg Prod.fst hpq) ⟨v, hvF⟩
    · exact congr_fun (congr_arg Prod.snd hpq) ⟨v, hvG⟩

/-! ## `r`-compatibility of symmetric-cube patterns -/

/-- Patterns `a : Pattern α (Q_k)` and `b : Pattern α (Q_N)` are `r`-compatible (with
respect to subshift `X`) if `k + r + 1 ≤ N` and the joined pattern with `a` on the
inner cube `Q_k` and `b` on the outer ring `Q_N \ Q_{k+r}` is globally admissible
in `X`. The "gap" `Q_{k+r} \ Q_k` is left unconstrained. -/
def Pattern.rCompatible {α : Type*} {d : ℕ} [TopologicalSpace α]
    (X : Subshift α d) (r : ℕ) {k N : ℕ}
    (a : Pattern α (symBox d k)) (b : Pattern α (symBox d N)) : Prop :=
  k + r + 1 ≤ N ∧
  Pattern.GloballyAdmissible X
    (Pattern.unionDisjoint a
      (Pattern.restrict (symBox d N \ symBox d (k + r)) Finset.sdiff_subset b))

/-- If `a` is `r`-compatible with some `b`, then `a` itself is globally admissible. -/
theorem Pattern.rCompatible.globallyAdmissible {α : Type*} {d : ℕ} [TopologicalSpace α]
    {X : Subshift α d} {r k N : ℕ} {a : Pattern α (symBox d k)} {b : Pattern α (symBox d N)}
    (h : Pattern.rCompatible X r a b) :
    Pattern.GloballyAdmissible X a := by
  obtain ⟨x, hxX, u, happ⟩ := h.2
  refine ⟨x, hxX, u, ?_⟩
  intro v
  have hv : v.val ∈ symBox d k ∪ (symBox d N \ symBox d (k + r)) :=
    Finset.mem_union_left _ v.property
  have hu := happ ⟨v.val, hv⟩
  rwa [Pattern.unionDisjoint_left a _ v.val v.property] at hu

/-- If `X` is `r`-irreducible, `a : Pattern α (Q_k)` is globally admissible, and the
restriction of `b : Pattern α (Q_N)` to the outer ring `Q_N \ Q_{k+r}` is globally
admissible, and `k + r + 1 ≤ N`, then `a` and `b` are `r`-compatible. -/
theorem Pattern.rCompatible_of_irreducible {α : Type*} {d : ℕ} [TopologicalSpace α]
    {X : Subshift α d} {r k N : ℕ} (hkN : k + r + 1 ≤ N) (hirr : ShiftIrreducible X r)
    (a : Pattern α (symBox d k)) (b : Pattern α (symBox d N))
    (ha : Pattern.GloballyAdmissible X a)
    (hb_outer : Pattern.GloballyAdmissible X
      (Pattern.restrict (symBox d N \ symBox d (k + r)) Finset.sdiff_subset b)) :
    Pattern.rCompatible X r a b := by
  refine ⟨hkN, ?_⟩
  rw [Pattern.globallyAdmissible_iff_appearsAt_zero] at ha hb_outer
  have h_sep : ∀ u ∈ symBox d k, ∀ v ∈ symBox d N \ symBox d (k + r),
      (r : ℤ) ≤ Lat.supNorm (u - v) := by
    intro u hu v hv
    have h := Lat.supNorm_sub_ge_of_inner_outer u v hu hv
    rw [Lat.supNorm_sub_comm]
    linarith
  obtain ⟨x, hxX, ha_app, hb_app⟩ := hirr (symBox d k) (symBox d N \ symBox d (k + r))
    h_sep a (Pattern.restrict _ Finset.sdiff_subset b) ha hb_outer
  rw [Pattern.globallyAdmissible_iff_appearsAt_zero]
  refine ⟨x, hxX, ?_⟩
  intro v
  by_cases hv : v.val ∈ symBox d k
  · rw [Pattern.unionDisjoint_left a _ v.val hv]
    exact ha_app ⟨v.val, hv⟩
  · have hv_outer : v.val ∈ symBox d N \ symBox d (k + r) :=
      (Finset.mem_union.mp v.property).resolve_left hv
    rw [Pattern.unionDisjoint_right symBox_disjoint_sdiff a _ v.val hv_outer]
    exact hb_app ⟨v.val, hv_outer⟩

/-! ## `N_bar`: counting locally admissible box-patterns -/

/-- The finset of patterns over `E` that are locally admissible for syntax `(F, L)`. -/
def locallyAdmissiblePatterns {α : Type*} [Fintype α] [DecidableEq α] {d : ℕ}
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (E : Finset (Lat d)) :
    Finset (Pattern α E) :=
  (Finset.univ : Finset (Pattern α E)).filter (locallyAdmissible F L)

/-- `N_bar F L n` is the number of locally admissible `box d n`-patterns for syntax `(F, L)`. -/
def N_bar {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) : ℕ :=
  (locallyAdmissiblePatterns F L (box d n)).card

/-- For the SFT `mkSFT F L`, every globally admissible box-pattern is locally admissible,
    so `N_X (mkSFT F L) (box d n) ≤ N_bar F L n`. -/
theorem N_X_le_N_bar {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) :
    N_X (mkSFT F L) (box d n) ≤ N_bar F L n := by
  unfold N_X N_bar
  rw [← Set.ncard_coe_finset (locallyAdmissiblePatterns F L (box d n))]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro p hp
  simp only [locallyAdmissiblePatterns, Finset.coe_filter, Finset.mem_univ, true_and,
    Set.mem_setOf_eq]
  exact Pattern.globally_imp_locally F L p hp

/-- `N_bar F L n` equals the cardinality of the subtype of locally admissible
n-box patterns. Useful for transferring to alternative formulations. -/
theorem N_bar_eq_fintype_card_subtype {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) :
    N_bar F L n =
      Fintype.card { p : Pattern α (box d n) // locallyAdmissible F L p } := by
  unfold N_bar locallyAdmissiblePatterns
  exact (Fintype.subtype_card (Finset.univ.filter (locallyAdmissible F L))
    (by intro p; simp)).symm

/-- The number of locally admissible n-box patterns is at most `|α|^(n^d)`. -/
theorem N_bar_le_card_pow {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (n : ℕ) :
    N_bar F L n ≤ (Fintype.card α) ^ (n ^ d) := by
  unfold N_bar locallyAdmissiblePatterns
  calc (Finset.univ.filter (locallyAdmissible F L)).card
      ≤ (Finset.univ : Finset (Pattern α (box d n))).card := Finset.card_filter_le _ _
    _ = Fintype.card (Pattern α (box d n)) := Finset.card_univ
    _ = Fintype.card α ^ Fintype.card ↥(box d n) := Fintype.card_fun
    _ = Fintype.card α ^ (n ^ d) := by rw [Fintype.card_coe, box_card]

/-- `N_bar` is monotone in the allowed-patterns set `L`: more permitted patterns
gives more locally admissible n-box patterns. -/
theorem N_bar_mono {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    (F : Finset (Lat d)) {L₁ L₂ : Finset (Pattern α F)} (hL : L₁ ⊆ L₂) (n : ℕ) :
    N_bar F L₁ n ≤ N_bar F L₂ n := by
  unfold N_bar locallyAdmissiblePatterns
  refine Finset.card_le_card ?_
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  intro u hu
  exact hL (hp.2 u hu)
