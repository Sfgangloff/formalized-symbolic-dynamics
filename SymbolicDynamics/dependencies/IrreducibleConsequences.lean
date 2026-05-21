import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import dependencies.Subshift
import dependencies.Box
import dependencies.LocallyAdmissible
import dependencies.GloballyAdmissible
import dependencies.Computable
import dependencies.NbarComputable
import axioms.Irreducible

/-! # Consequences of the irreducible-SFT axioms

Theorems used in the Hochman–Meyerovitch main proofs, deriving from the
axioms in `axioms/Irreducible.lean` together with general compactness
and computability facts:

- `locally_admissible_outer_globally_admissible_irreducible` — the
  outer-ring restriction of any locally admissible `symBox d N`-pattern
  is globally admissible.
- `Lemma_3_4_case_notGA` — the not-globally-admissible branch of the
  Lemma 3.4 dichotomy, proved via compactness of `FullShift α d`.
- `Lemma_3_4_case_GA` — the globally-admissible branch, proved via the
  irreducibility-gluing axiom + `exists_threshold_sqrt`.
- `topEntropy_leftRE_irreducible` — left-recursive enumerability of
  the topological entropy of an irreducible SFT, via the periodic-point
  count axiom + the computable rational lower-approximation theorem.
-/

/-- For irreducible SFTs and large `N`, the outer-ring restriction of any
locally admissible `symBox d N`-pattern is globally admissible. -/
theorem locally_admissible_outer_globally_admissible_irreducible
    {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty)
    (h_irr : IsIrreducibleShift (mkSFT F L)) (k : ℕ) :
    ∃ N₀, ∀ N ≥ N₀, ∀ r : ℕ, k + r + 1 ≤ N → ∀ b : Pattern α (symBox d N),
      locallyAdmissible F L b →
      Pattern.GloballyAdmissible (mkSFT F L)
        (Pattern.restrict (symBox d N \ symBox d (k + r)) Finset.sdiff_subset b) := by
  obtain ⟨N₀, hN₀⟩ :=
    locally_admissible_imp_globally_admissible_irreducible F L hX h_irr
  refine ⟨N₀, fun N hN r _hkN b hb_loc => ?_⟩
  exact Pattern.globallyAdmissible_restrict
    (symBox d N \ symBox d (k + r)) Finset.sdiff_subset (hN₀ N hN b hb_loc)

/-! ## Lemma 3.4 dichotomy: the two cases -/

/-- **J7a: the not-globally-admissible branch of Lemma 3.4.** If `a` is not
globally admissible, then for all sufficiently large `N`, no locally
admissible `Q_N`-pattern restricts to `a`.

Proved via compactness of `FullShift α d`: by contrapositive, assume infinitely
many `N` admit locally admissible extensions of `a`; build configurations
extending these patterns; by compactness, the decreasing sequence of closed sets
"cylinder a 0 ∩ {x | x|symBox d N is locally admissible}" has nonempty
intersection; the limit configuration is in `mkSFT.carrier` and has `a` at
offset 0, contradicting `¬ GloballyAdmissible`. -/
theorem Lemma_3_4_case_notGA {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty)
    (_h_irr : IsIrreducibleShift (mkSFT F L))
    {k : ℕ} (a : Pattern α (symBox d k))
    (h_not_ga : ¬ Pattern.GloballyAdmissible (mkSFT F L) a) :
    ∃ N₀, ∀ N ≥ N₀, ∀ b : Pattern α (symBox d N),
      locallyAdmissible F L b →
      ∀ h : symBox d k ⊆ symBox d N,
        (Pattern.restrict (symBox d k) h b) ≠ a := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x₀, _hx₀⟩ := hX
  let S : Lat d → Set (FullShift α d) := fun u =>
    {x | Pattern.ofColoring F (FullShift.shiftMap u x) ∈ L}
  have hS_closed : ∀ u : Lat d, IsClosed (S u) := by
    intro u
    apply IsClosed.preimage
    · apply continuous_pi; intro v; exact continuous_apply (v.val + u)
    · exact L.finite_toSet.isClosed
  let E : ℕ → Set (FullShift α d) := fun N =>
    Pattern.cylinder a 0 ∩ ⋂ u ∈ relevantOffsets F (symBox d N), S u
  have hE_closed : ∀ N, IsClosed (E N) := by
    intro N
    refine IsClosed.inter (Pattern.cylinder_isClosed a 0) ?_
    apply isClosed_biInter
    intro u _; exact hS_closed u
  have hE_anti : ∀ M N, M ≤ N → E N ⊆ E M := by
    intro M N hMN x hx
    refine ⟨hx.1, ?_⟩
    rw [Set.mem_iInter₂]; intro u hu_M
    have hu_N : u ∈ relevantOffsets F (symBox d N) := by
      unfold relevantOffsets at hu_M ⊢
      by_cases hF : F = ∅
      · simp [hF] at hu_M ⊢; exact hu_M
      · rw [if_neg hF] at hu_M; rw [if_neg hF]
        rw [Finset.mem_filter] at hu_M
        rw [Finset.mem_filter]
        refine ⟨?_, fun w hw => symBox_mono hMN (hu_M.2 w hw)⟩
        simp only [Finset.mem_image, Finset.mem_product] at hu_M ⊢
        obtain ⟨⟨v, w⟩, ⟨hv, hw⟩, hsub⟩ := hu_M.1
        exact ⟨(v, w), ⟨hv, symBox_mono hMN hw⟩, hsub⟩
    exact (Set.mem_iInter₂.mp hx.2) u hu_N
  have hE_nonempty : ∀ N, (E N).Nonempty := by
    intro N
    obtain ⟨M, hMN, b, hb_loc, hsub, hb_restr⟩ := hcon N
    classical
    let x : FullShift α d := fun v =>
      if hv : v ∈ symBox d M then b ⟨v, hv⟩ else x₀ v
    refine ⟨x, ?_, ?_⟩
    · intro v
      have hv_M : v.val ∈ symBox d M := hsub v.property
      change x (v.val + 0) = a v
      simp only [add_zero]
      have hx_eq : x v.val = b ⟨v.val, hv_M⟩ := by
        simp only [x, dif_pos hv_M]
      rw [hx_eq]
      have h_restr : Pattern.restrict (symBox d k) hsub b v = b ⟨v.val, hv_M⟩ := rfl
      rw [← h_restr, hb_restr]
    · rw [Set.mem_iInter₂]; intro u hu_N
      change Pattern.ofColoring F (FullShift.shiftMap u x) ∈ L
      by_cases hF : F = ∅
      · have hempty := _hx₀ u
        have heq : Pattern.ofColoring F (FullShift.shiftMap u x) =
                   Pattern.ofColoring F (FullShift.shiftMap u x₀) := by
          subst hF; funext v; exact absurd v.property (Finset.notMem_empty v.val)
        rw [heq]; exact hempty
      · have hFu_M : ∀ v : F, v.val + u ∈ symBox d M := by
          intro v
          unfold relevantOffsets at hu_N
          rw [if_neg hF, Finset.mem_filter] at hu_N
          exact symBox_mono hMN (hu_N.2 v.val v.property)
        have heq : Pattern.ofColoring F (FullShift.shiftMap u x) =
                   (fun v : F => b ⟨v.val + u, hFu_M v⟩) := by
          funext v
          simp only [Pattern.ofColoring, FullShift.shiftMap, x, dif_pos (hFu_M v)]
        rw [heq]
        exact hb_loc u hFu_M
  have h_inter_ne : (⋂ N, E N).Nonempty := by
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro N
      exact hE_anti N (N + 1) (Nat.le_succ N)
    · exact hE_nonempty
    · exact (CompactSpace.isCompact_univ).of_isClosed_subset
        (hE_closed 0) (Set.subset_univ _)
    · exact hE_closed
  obtain ⟨x, hx⟩ := h_inter_ne
  have hx_cyl : x ∈ Pattern.cylinder a 0 := (Set.mem_iInter.mp hx 0).1
  have hx_S : ∀ u : Lat d, x ∈ S u := by
    intro u
    by_cases hF : F = ∅
    · have h0_rel : (0 : Lat d) ∈ relevantOffsets F (symBox d 0) := by
        unfold relevantOffsets
        simp [hF]
      have hxS0 : x ∈ S 0 :=
        (Set.mem_iInter₂.mp (Set.mem_iInter.mp hx 0).2) 0 h0_rel
      have heq : Pattern.ofColoring F (FullShift.shiftMap u x) =
                 Pattern.ofColoring F (FullShift.shiftMap (0 : Lat d) x) := by
        subst hF; funext v; exact absurd v.property (Finset.notMem_empty v.val)
      change Pattern.ofColoring F (FullShift.shiftMap u x) ∈ L
      rw [heq]
      exact hxS0
    · obtain ⟨v0, hv0⟩ := Finset.nonempty_iff_ne_empty.mpr hF
      let N : ℕ := F.sup (fun v =>
        (Finset.univ.sup (fun i : Fin d => ((v + u) i).natAbs)))
      have hFu_in : ∀ v : F, v.val + u ∈ symBox d N := by
        intro v
        simp only [symBox, Fintype.mem_piFinset, Finset.mem_Icc]
        intro i
        have h_le_local : ((v.val + u) i).natAbs ≤
            Finset.univ.sup (fun i : Fin d => ((v.val + u) i).natAbs) :=
          Finset.le_sup (f := fun i : Fin d => ((v.val + u) i).natAbs)
            (Finset.mem_univ i)
        have h_le_N : Finset.univ.sup (fun i : Fin d => ((v.val + u) i).natAbs) ≤ N :=
          Finset.le_sup (f := fun w : Lat d =>
              Finset.univ.sup (fun i : Fin d => ((w + u) i).natAbs)) v.property
        have h_abs : ((v.val + u) i).natAbs ≤ N := le_trans h_le_local h_le_N
        have h_abs_int : |((v.val + u) i)| ≤ (N : ℤ) := by
          rw [Int.abs_eq_natAbs]; exact_mod_cast h_abs
        exact abs_le.mp h_abs_int
      have hu_rel : u ∈ relevantOffsets F (symBox d N) := by
        unfold relevantOffsets
        rw [if_neg hF, Finset.mem_filter]
        refine ⟨?_, fun w hw => hFu_in ⟨w, hw⟩⟩
        simp only [Finset.mem_image, Finset.mem_product]
        refine ⟨(v0, v0 + u), ⟨hv0, hFu_in ⟨v0, hv0⟩⟩, by simp⟩
      exact (Set.mem_iInter₂.mp (Set.mem_iInter.mp hx N).2) u hu_rel
  have hx_mk : x ∈ mkSFT F L := fun u => hx_S u
  exact h_not_ga ⟨x, hx_mk, 0, hx_cyl⟩

/-- **J7b: the globally-admissible branch of Lemma 3.4.** For an irreducible
SFT and a globally admissible `Q_k`-pattern `a`, every sufficiently large
locally admissible `Q_N`-pattern is `Nat.sqrt N`-compatible with `a`. -/
theorem Lemma_3_4_case_GA {α : Type*} {d : ℕ} [Fintype α] [DecidableEq α]
    [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty)
    (h_irr : IsIrreducibleShift (mkSFT F L))
    {k : ℕ} (a : Pattern α (symBox d k))
    (h_ga : Pattern.GloballyAdmissible (mkSFT F L) a) :
    ∃ N₀, ∀ N ≥ N₀, ∀ b : Pattern α (symBox d N),
      locallyAdmissible F L b → Pattern.rCompatible (mkSFT F L) (Nat.sqrt N) a b := by
  obtain ⟨N₂, hN₂⟩ :=
    locally_admissible_outer_globally_admissible_irreducible F L hX h_irr k
  obtain ⟨r₀, _hr₀_pos, h_irr_r₀⟩ := h_irr
  obtain ⟨N₁, hN₁⟩ := exists_threshold_sqrt r₀ k
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN b hb_loc
  have hN_N₁ : N₁ ≤ N := le_of_max_le_left hN
  have hN_N₂ : N₂ ≤ N := le_of_max_le_right hN
  obtain ⟨h_sqrt_ge, h_kN⟩ := hN₁ N hN_N₁
  have h_irr_sqrt : ShiftIrreducible (mkSFT F L) (Nat.sqrt N) :=
    h_irr_r₀.mono h_sqrt_ge
  have h_outer_ga : Pattern.GloballyAdmissible (mkSFT F L)
      (Pattern.restrict (symBox d N \ symBox d (k + Nat.sqrt N))
         Finset.sdiff_subset b) :=
    hN₂ N hN_N₂ (Nat.sqrt N) h_kN b hb_loc
  exact Pattern.rCompatible_of_irreducible h_kN h_irr_sqrt a b h_ga h_outer_ga

/-! ## Left-recursive enumerability of topological entropy -/

/-- The topological entropy of a nonempty irreducible SFT is left
recursively enumerable. Combines `existsPeriodicCount_for_irreducible_SFT`
(periodic-point count bound + convergence) with
`rationalLowerApprox_log_div_pow_of_computable`. -/
-- @ontology: hm:lean:leftRE-irreducible
theorem topEntropy_leftRE_irreducible {α : Type*} {d : ℕ}
    [Fintype α] [DecidableEq α] [Encodable α] [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty)
    (h_irr : IsIrreducibleShift (mkSFT F L)) :
    IsLeftRE (topEntropy (mkSFT F L)) := by
  obtain ⟨P, hP_comp, hP_le, hP_conv⟩ :=
    existsPeriodicCount_for_irreducible_SFT F L hX h_irr
  have hP_shift : Computable (fun n : ℕ => P (n + 1)) :=
    hP_comp.comp (Primrec.succ.to_comp)
  obtain ⟨q, hq_comp, hq_lower, hq_gap⟩ :=
    rationalLowerApprox_log_div_pow_of_computable (d := d) hP_shift
  refine ⟨q, hq_comp, ?_, ?_⟩
  · intro n
    exact (hq_lower n).trans (hP_le n)
  · have h_sum := hP_conv.sub hq_gap
    have h_target :
        (fun n : ℕ =>
          Real.log (P (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ d -
            (Real.log (P (n + 1)) / ((n + 1 : ℕ) : ℝ) ^ d - (q n : ℝ)))
          = fun n : ℕ => (q n : ℝ) := by
      funext n; ring
    rw [h_target, sub_zero] at h_sum
    exact h_sum
