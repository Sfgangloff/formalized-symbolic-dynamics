import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Card
import dependencies.Subshift
import dependencies.Box
import dependencies.LocallyAdmissible
import dependencies.GloballyAdmissible

/-! # Topological entropy of a subshift

Subadditivity of `logN` in 1D, the 1D Fekete limit, monotonicity and
basic bounds for `topEntropy`, and the upper bound by locally-admissible
counts (`topEntropy_le_log_N_bar_div_pow`).

Originally lived in `papers/HochmanMeyerovitch/HochmanMeyerovitch.lean`;
moved here for reuse. The definition of `topEntropy` itself lives in
`dependencies/Subshift.lean`.
-/

/-! ## 1D subadditivity of `logN` -/

/-- In one dimension, `logN X` is a subadditive sequence. -/
theorem logN_subadditive {α : Type*} [Fintype α] [TopologicalSpace α]
    (X : Subshift α 1) :
    Subadditive (logN X) := by
  intro m n
  set vm : Lat 1 := fun _ => (m : ℤ) with hvm_def
  have hbox_mem : ∀ {k : ℕ} (v : Lat 1), v ∈ box 1 k ↔ 0 ≤ v 0 ∧ v 0 < (k : ℤ) := by
    intro k v
    simp only [box, Fintype.mem_piFinset, Finset.mem_Ico]
    refine ⟨fun h => h 0, fun h i => ?_⟩
    rw [Fin.eq_zero i]; exact h
  have hshift_box : ∀ v ∈ box 1 n, v + vm ∈ box 1 (m + n) := by
    intro v hv
    rw [hbox_mem] at hv
    rw [hbox_mem]
    have hadd : (v + vm) 0 = v 0 + (m : ℤ) := by simp [vm]
    rw [hadd]
    obtain ⟨h1, h2⟩ := hv
    have hm_nonneg : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    push_cast
    exact ⟨by linarith, by linarith⟩
  have hN : N_X X (box 1 (m + n)) ≤ N_X X (box 1 m) * N_X X (box 1 n) := by
    unfold N_X
    rw [← Set.ncard_prod]
    refine Set.ncard_le_ncard_of_injOn
      (fun p : Pattern α (box 1 (m + n)) =>
        ((fun v : box 1 m => p ⟨v.val, box_mono (Nat.le_add_right _ _) v.property⟩),
         (fun v : box 1 n => p ⟨v.val + vm, hshift_box v.val v.property⟩)))
      ?_ ?_ (Set.toFinite _)
    · rintro p ⟨x, hxX, w, happ⟩
      refine ⟨⟨x, hxX, w, fun v => ?_⟩, ⟨x, hxX, w + vm, fun v => ?_⟩⟩
      · exact happ ⟨v.val, box_mono (Nat.le_add_right _ _) v.property⟩
      · have h := happ ⟨v.val + vm, hshift_box v.val v.property⟩
        change x (v.val + (w + vm)) = p ⟨v.val + vm, hshift_box v.val v.property⟩
        have heq : v.val + (w + vm) = (v.val + vm) + w := by ring
        rw [heq]; exact h
    · intro p _ q _ hpq
      ext ⟨v, hv_orig⟩
      have hv : 0 ≤ v 0 ∧ v 0 < ((m + n : ℕ) : ℤ) := (hbox_mem v).mp hv_orig
      by_cases hvm : v 0 < (m : ℤ)
      · have hv_m : v ∈ box 1 m := (hbox_mem v).mpr ⟨hv.1, hvm⟩
        exact congr_fun (congr_arg Prod.fst hpq) ⟨v, hv_m⟩
      · push_neg at hvm
        have hv_n : v - vm ∈ box 1 n := by
          rw [hbox_mem]
          have hsub : (v - vm) 0 = v 0 - (m : ℤ) := by simp [vm]
          rw [hsub]
          obtain ⟨_, h2⟩ := hv
          push_cast at h2
          exact ⟨by linarith, by linarith⟩
        have heq : (v - vm) + vm = v := by ext i; simp [vm]
        have key : (⟨v, hv_orig⟩ : { x : Lat 1 // x ∈ box 1 (m + n) }) =
                   ⟨(v - vm) + vm, hshift_box (v - vm) hv_n⟩ :=
          Subtype.ext heq.symm
        rw [key]
        exact congr_fun (congr_arg Prod.snd hpq) ⟨v - vm, hv_n⟩
  unfold logN
  by_cases hb : N_X X (box 1 m) = 0
  · have ha : N_X X (box 1 (m + n)) = 0 := Nat.le_zero.mp (by simpa [hb] using hN)
    rw [ha, hb]
    push_cast
    rw [Real.log_zero]
    have : (0 : ℝ) ≤ Real.log (N_X X (box 1 n)) := Real.log_natCast_nonneg _
    linarith
  by_cases hc : N_X X (box 1 n) = 0
  · have ha : N_X X (box 1 (m + n)) = 0 := Nat.le_zero.mp (by simpa [hc] using hN)
    rw [ha, hc]
    push_cast
    rw [Real.log_zero]
    have : (0 : ℝ) ≤ Real.log (N_X X (box 1 m)) := Real.log_natCast_nonneg _
    linarith
  have hb' : (0 : ℝ) < (N_X X (box 1 m) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb
  have hc' : (0 : ℝ) < (N_X X (box 1 n) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc
  by_cases ha : N_X X (box 1 (m + n)) = 0
  · rw [ha]
    push_cast
    rw [Real.log_zero]
    have hpos1 : (0 : ℝ) ≤ Real.log (N_X X (box 1 m)) := Real.log_natCast_nonneg _
    have hpos2 : (0 : ℝ) ≤ Real.log (N_X X (box 1 n)) := Real.log_natCast_nonneg _
    linarith
  have ha' : (0 : ℝ) < (N_X X (box 1 (m + n)) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hN' : (N_X X (box 1 (m + n)) : ℝ) ≤
      (N_X X (box 1 m) : ℝ) * (N_X X (box 1 n) : ℝ) := by exact_mod_cast hN
  rw [← Real.log_mul (ne_of_gt hb') (ne_of_gt hc')]
  exact Real.log_le_log ha' hN'

/-- Fekete's lemma in one dimension: a subadditive sequence bounded below has `u n / n`
    converging to `Subadditive.lim`. Wraps `Subadditive.tendsto_lim`. -/
theorem Fekete_1d {u : ℕ → ℝ} (h : Subadditive u)
    (hbdd : BddBelow (Set.range fun n => u n / n)) :
    Filter.Tendsto (fun n => u n / n) Filter.atTop (nhds h.lim) :=
  h.tendsto_lim hbdd

/-- For a 1D subshift `X` over a finite alphabet, `logN X n / n` converges to
    `(logN_subadditive X).lim`. -/
theorem logN_div_pow_tendsto {α : Type*} [Fintype α] [TopologicalSpace α]
    (X : Subshift α 1) :
    Filter.Tendsto (fun n => logN X n / n) Filter.atTop
      (nhds (logN_subadditive X).lim) := by
  apply Fekete_1d (logN_subadditive X)
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst hn; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    apply div_nonneg
    · exact Real.log_natCast_nonneg _
    · exact hn'.le

/-! ## Basic properties of `topEntropy` -/

theorem topEntropy_nonneg {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) :
    0 ≤ topEntropy X := by
  apply le_csInf
  · exact Set.Nonempty.image _ ⟨1, Set.mem_Ici.mpr le_rfl⟩
  · rintro x ⟨n, hn, rfl⟩
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply div_nonneg (Real.log_natCast_nonneg _)
    positivity

theorem topEntropy_fullShift {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α] :
    topEntropy (Subshift.univ α d) = Real.log (Fintype.card α) := by
  classical
  unfold topEntropy
  have hcount : ∀ n : ℕ, 1 ≤ n →
      N_X (Subshift.univ α d) (box d n) = (Fintype.card α) ^ (n ^ d) := by
    intro n hn
    unfold N_X
    by_cases hα : Nonempty α
    · have heq : {p : Pattern α (box d n) |
                  Pattern.GloballyAdmissible (Subshift.univ α d) p} = Set.univ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        refine ⟨fun v => if h : v ∈ box d n then p ⟨v, h⟩ else Classical.arbitrary α,
                Set.mem_univ _, 0, fun v => ?_⟩
        change (fun w => if h : w ∈ box d n then p ⟨w, h⟩ else Classical.arbitrary α)
                 (v.val + 0) = p v
        simp [v.property]
      rw [heq, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun,
          Fintype.card_coe, box_card]
    · rw [not_nonempty_iff] at hα
      haveI := hα
      have hb : (box d n).Nonempty := by
        rw [← Finset.card_pos, box_card]; positivity
      haveI : Nonempty ↥(box d n) := hb.coe_sort
      haveI : IsEmpty (Pattern α (box d n)) := inferInstance
      have hN : ({p : Pattern α (box d n) |
                  Pattern.GloballyAdmissible (Subshift.univ α d) p}).ncard = 0 := by
        rw [Set.ncard_eq_zero (Set.toFinite _)]
        ext p
        exact (IsEmpty.false p).elim
      rw [hN, Fintype.card_eq_zero, zero_pow (by positivity : n ^ d ≠ 0)]
  have hlogN : ∀ n ≥ 1,
      logN (Subshift.univ α d) n / (n : ℝ) ^ d = Real.log (Fintype.card α) := by
    intro n hn
    unfold logN
    rw [hcount n hn]
    have hnd_pos : (0 : ℝ) < (n : ℝ) ^ d := by
      have : (0 : ℝ) < n := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn |>.bot_lt
      positivity
    have hnd_ne : ((n : ℝ) ^ d) ≠ 0 := ne_of_gt hnd_pos
    push_cast
    rw [Real.log_pow]
    push_cast
    field_simp
  have himg : (fun n : ℕ => logN (Subshift.univ α d) n / (n : ℝ) ^ d) '' Set.Ici 1
            = {Real.log (Fintype.card α)} := by
    ext y
    simp only [Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨n, hn, rfl⟩; exact hlogN n hn
    · intro hy; exact ⟨1, le_rfl, by rw [hlogN 1 le_rfl]; exact hy.symm⟩
  rw [himg]
  exact csInf_singleton _

theorem topEntropy_antitone {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    {X Y : Subshift α d} (hXY : X.carrier ⊆ Y.carrier) :
    topEntropy X ≤ topEntropy Y := by
  unfold topEntropy
  have hbdd : BddBelow ((fun n : ℕ => logN X n / (n : ℝ) ^ d) '' Set.Ici 1) := by
    refine ⟨0, ?_⟩
    rintro x ⟨k, hk, rfl⟩
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    apply div_nonneg (Real.log_natCast_nonneg _)
    positivity
  apply le_csInf
  · exact Set.Nonempty.image _ ⟨1, Set.mem_Ici.mpr le_rfl⟩
  rintro y ⟨n, hn, rfl⟩
  have hN : N_X X (box d n) ≤ N_X Y (box d n) := by
    unfold N_X
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro p ⟨x, hxX, u, happ⟩
    exact ⟨x, hXY hxX, u, happ⟩
  have hlog : logN X n ≤ logN Y n := by
    unfold logN
    by_cases hX_zero : N_X X (box d n) = 0
    · rw [hX_zero]; push_cast; rw [Real.log_zero]
      exact Real.log_natCast_nonneg _
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hX_zero
    · exact_mod_cast hN
  have hX_in : logN X n / (n : ℝ) ^ d ∈
      (fun n : ℕ => logN X n / (n : ℝ) ^ d) '' Set.Ici 1 := ⟨n, hn, rfl⟩
  calc sInf _ ≤ logN X n / (n : ℝ) ^ d := csInf_le hbdd hX_in
    _ ≤ logN Y n / (n : ℝ) ^ d := by gcongr

theorem topEntropy_bot {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α] :
    topEntropy (Subshift.bot α d) = 0 := by
  unfold topEntropy
  have h_zero : ∀ n : ℕ, 1 ≤ n →
      logN (Subshift.bot α d) n / (n : ℝ) ^ d = 0 := by
    intro n _
    unfold logN N_X
    have hempty : {p : Pattern α (box d n) |
        Pattern.GloballyAdmissible (Subshift.bot α d) p} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, hx, _⟩
      exact absurd hx (Set.notMem_empty _)
    rw [hempty, Set.ncard_empty, Nat.cast_zero, Real.log_zero, zero_div]
  have himg : (fun n : ℕ => logN (Subshift.bot α d) n / (n : ℝ) ^ d) '' Set.Ici 1 = {0} := by
    ext y
    simp only [Set.mem_image, Set.mem_Ici, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨n, hn, rfl⟩; exact h_zero n hn
    · intro hy; exact ⟨1, le_rfl, by rw [h_zero 1 le_rfl]; exact hy.symm⟩
  rw [himg]
  exact csInf_singleton _

theorem topEntropy_inter_le_left {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X Y : Subshift α d) :
    topEntropy (Subshift.inter X Y) ≤ topEntropy X :=
  topEntropy_antitone Set.inter_subset_left

theorem topEntropy_inter_le_right {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X Y : Subshift α d) :
    topEntropy (Subshift.inter X Y) ≤ topEntropy Y :=
  topEntropy_antitone Set.inter_subset_right

/-- Every subshift's topological entropy is bounded by `log |α|`. -/
theorem topEntropy_le_log_card {α : Type*} {d : ℕ} [Fintype α] [TopologicalSpace α]
    (X : Subshift α d) :
    topEntropy X ≤ Real.log (Fintype.card α) := by
  rw [← topEntropy_fullShift (α := α) (d := d)]
  exact topEntropy_antitone (Set.subset_univ _)

/-! ## Upper bound by locally-admissible counts -/

/-- For a nonempty SFT `mkSFT F L` and any `n ≥ 1`, the topological entropy is
bounded above by `Real.log (N_bar F L n) / n^d`.

Combines `csInf_le` (topEntropy is the inf of `logN X k / k^d`) with
`N_X_le_N_bar` (every globally admissible pattern is locally admissible). -/
theorem topEntropy_le_log_N_bar_div_pow {α : Type*} {d : ℕ}
    [Fintype α] [DecidableEq α] [TopologicalSpace α] [T1Space α]
    (F : Finset (Lat d)) (L : Finset (Pattern α F))
    (hX : (mkSFT F L).carrier.Nonempty) (n : ℕ) (hn : 1 ≤ n) :
    topEntropy (mkSFT F L) ≤ Real.log (N_bar F L n) / (n : ℝ) ^ d := by
  have hbdd : BddBelow
      ((fun k : ℕ => logN (mkSFT F L) k / (k : ℝ) ^ d) '' Set.Ici 1) := by
    refine ⟨0, ?_⟩
    rintro x ⟨k, hk, rfl⟩
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    apply div_nonneg (Real.log_natCast_nonneg _)
    positivity
  have h_inf_le : topEntropy (mkSFT F L) ≤ logN (mkSFT F L) n / (n : ℝ) ^ d := by
    unfold topEntropy
    exact csInf_le hbdd ⟨n, hn, rfl⟩
  have h_log_le : logN (mkSFT F L) n ≤ Real.log (N_bar F L n) := by
    unfold logN
    apply Real.log_le_log
    · exact_mod_cast N_X_pos_of_nonempty _ _ hX
    · exact_mod_cast N_X_le_N_bar F L n
  have hn_pos : (0 : ℝ) < (n : ℝ) ^ d := by
    have hn_real : (0 : ℝ) < (n : ℝ) :=
      by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    positivity
  calc topEntropy (mkSFT F L)
      ≤ logN (mkSFT F L) n / (n : ℝ) ^ d := h_inf_le
    _ ≤ Real.log (N_bar F L n) / (n : ℝ) ^ d :=
        div_le_div_of_nonneg_right h_log_le hn_pos.le
