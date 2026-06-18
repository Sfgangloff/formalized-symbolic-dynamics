import dependencies.Subshift
import dependencies.Box
import dependencies.LocallyAdmissible
import dependencies.GloballyAdmissible
import dependencies.Computable

/-! # `Primrec₂` of the digit-level local-admissibility predicate

This file discharges the former axiom `primrec_admPredDigit`
(`axioms/Computability.lean`): the predicate `admPredDigit F L n k` is
primitive recursive in `(n, k)`.

Strategy (no `Primrec ℤ` needed): reduce the `n`-dependent `relevantOffsets`
quantifier to a bounded `∀ t < n^d` via an anchor enumeration of the box, encode
`F`/`L` as constant ℕ-data, and build a Bool decision procedure `admBoolG`
proven both `Primrec` and equal to `decide ∘ admPredDigit`.
All helpers live in the `AdmPredPrimrec` namespace; the top-level
`primrec_admPredDigit` matches the original axiom's signature. -/

namespace AdmPredPrimrec


/-- For nonempty `F`, an offset `u` is "relevant" for support `E` iff translating
every cell of `F` by `u` stays in `E`. -/
theorem mem_relevantOffsets_iff_forall {d : ℕ} (F E : Finset (Lat d))
    (hF : F.Nonempty) (u : Lat d) :
    u ∈ relevantOffsets F E ↔ ∀ w ∈ F, w + u ∈ E := by
  unfold relevantOffsets
  rw [if_neg hF.ne_empty, Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨w, hw⟩ := hF
    simp only [Finset.mem_image, Finset.mem_product]
    exact ⟨(w, w + u), ⟨hw, h w hw⟩, by simp⟩

/-- `boxIndexInv` maps box elements into `[0, n^d)`. -/
theorem boxIndexInv_lt {d n : ℕ} {w : Lat d} (hw : w ∈ box d n) :
    boxIndexInv d n w < n ^ d := by
  have := (boxIxEquiv d n ⟨w, hw⟩).isLt
  rwa [boxIxEquiv_val] at this

/-- Central enumeration lemma: a universal statement over relevant offsets is the
same as a bounded universal over box indices `t < n^d`, reconstructing the offset
as `boxIndex d n t - a` for a fixed anchor `a ∈ F`. -/
theorem forall_relevantOffsets_iff_boxIndex {d : ℕ} (F : Finset (Lat d))
    (hF : F.Nonempty) (n : ℕ) (P : Lat d → Prop) :
    (∀ u ∈ relevantOffsets F (box d n), P u) ↔
    (∀ t : ℕ, t < n ^ d →
        (∀ w ∈ F, w + (boxIndex d n t - hF.choose) ∈ box d n) →
        P (boxIndex d n t - hF.choose)) := by
  constructor
  · intro h t _ht hrel
    exact h _ ((mem_relevantOffsets_iff_forall F (box d n) hF _).2 hrel)
  · intro h u hu
    rw [mem_relevantOffsets_iff_forall F (box d n) hF] at hu
    set a := hF.choose with ha
    have hau : a + u ∈ box d n := hu a hF.choose_spec
    have ht_lt : boxIndexInv d n (a + u) < n ^ d := boxIndexInv_lt hau
    have hround : boxIndex d n (boxIndexInv d n (a + u)) = a + u :=
      boxIndex_boxIndexInv hau
    have hsub : boxIndex d n (boxIndexInv d n (a + u)) - a = u := by
      rw [hround, add_sub_cancel_left]
    have hkey := h (boxIndexInv d n (a + u)) ht_lt (by rw [hsub]; exact hu)
    rwa [hsub] at hkey

/-- Reformulation of `admPredDigit` (for nonempty `F`) as a bounded universal over
box indices `t < n^d`. Direct consequence of the enumeration lemma. -/
theorem admPredDigit_iff_boxIndex {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d : ℕ} (F : Finset (Lat d)) (L : Finset (Pattern α F)) (hF : F.Nonempty) (n k : ℕ) :
    admPredDigit F L n k ↔
    k < (Fintype.card α) ^ (n ^ d) ∧
    ∀ t : ℕ, t < n ^ d →
      (∀ w ∈ F, w + (boxIndex d n t - hF.choose) ∈ box d n) →
      ∃ ℓ ∈ L, ∀ v : F,
        digit (Fintype.card α) k
            (boxIndexInv d n (v.val + (boxIndex d n t - hF.choose))) =
          (Encodable.fintypeEquivFin (ℓ v)).val := by
  unfold admPredDigit
  refine and_congr_right (fun _ => ?_)
  exact forall_relevantOffsets_iff_boxIndex F hF n _


/-! ## ℕ/ℤ coordinate bridge (part A helpers) -/

/-- The integer coordinate `c + e` (c : ℕ) realized via the (toNat e, toNat (-e)) split. -/
theorem int_add_toNat_eq (c : ℕ) (e : ℤ) :
    ((c : ℤ) + e).toNat = c + e.toNat - (-e).toNat := by
  omega

/-- Membership of `c + e` in `[0, n)` in terms of the ℕ split. -/
theorem int_add_mem_range_iff (c n : ℕ) (e : ℤ) :
    (0 ≤ (c : ℤ) + e ∧ (c : ℤ) + e < (n : ℤ)) ↔
      ((-e).toNat ≤ c + e.toNat ∧ c + e.toNat < n + (-e).toNat) := by
  omega

/-! ## Part A: Primrec building blocks (variable base) -/

/-- Variable-base digit: `j`-th base-`n` digit of `t`. Reads anchor coordinates. -/
def boxDigit (n t j : ℕ) : ℕ := (t / n ^ j) % n

theorem primrec_boxDigit : Primrec (fun p : ℕ × ℕ × ℕ => boxDigit p.1 p.2.1 p.2.2) := by
  unfold boxDigit
  have hpow : Primrec (fun p : ℕ × ℕ × ℕ => p.1 ^ p.2.2) :=
    primrec_nat_pow.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hdiv : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1 / p.1 ^ p.2.2) :=
    Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd) hpow
  exact Primrec.nat_mod.comp hdiv Primrec.fst

/-- Per-coordinate weighted contribution `(coordVal) * n^j` for a `(j,p,q)` triple. -/
def triWeight (n t : ℕ) (jpq : ℕ × ℕ × ℕ) : ℕ :=
  (boxDigit n t jpq.1 + jpq.2.1 - jpq.2.2) * n ^ jpq.1

theorem primrec_triWeight :
    Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => triWeight x.1.1 x.1.2 x.2) := by
  unfold triWeight
  have hn : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.1.1) := Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.1.2) := Primrec.snd.comp Primrec.fst
  have hj : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hq : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hbd : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => boxDigit x.1.1 x.1.2 x.2.1) :=
    primrec_boxDigit.comp (hn.pair (ht.pair hj))
  have hcoord : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
      boxDigit x.1.1 x.1.2 x.2.1 + x.2.2.1 - x.2.2.2) :=
    Primrec.nat_sub.comp (Primrec.nat_add.comp hbd hp) hq
  have hpow : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.1.1 ^ x.2.1) :=
    primrec_nat_pow.comp hn hj
  exact Primrec.nat_mul.comp hcoord hpow

/-- Box index of `v.val + u` reconstructed from a list of `(j,p,q)` triples. -/
def idxFromTriples (n t : ℕ) (tr : List (ℕ × ℕ × ℕ)) : ℕ :=
  tr.foldr (fun jpq acc => acc + triWeight n t jpq) 0

theorem primrec_idxFromTriples :
    Primrec (fun x : (ℕ × ℕ) × List (ℕ × ℕ × ℕ) => idxFromTriples x.1.1 x.1.2 x.2) := by
  unfold idxFromTriples
  refine Primrec.list_foldr (f := fun x : (ℕ × ℕ) × List (ℕ × ℕ × ℕ) => x.2)
    (g := fun _ => (0 : ℕ))
    (h := fun (a : (ℕ × ℕ) × List (ℕ × ℕ × ℕ)) (bs : (ℕ × ℕ × ℕ) × ℕ) =>
      bs.2 + triWeight a.1.1 a.1.2 bs.1)
    Primrec.snd (Primrec.const 0) ?_
  have hs : Primrec (fun y : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ)) × ((ℕ × ℕ × ℕ) × ℕ) => y.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hnt : Primrec (fun y : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ)) × ((ℕ × ℕ × ℕ) × ℕ) => y.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun y : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ)) × ((ℕ × ℕ × ℕ) × ℕ) => y.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htw : Primrec (fun y : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ)) × ((ℕ × ℕ × ℕ) × ℕ) =>
      triWeight y.1.1.1 y.1.1.2 y.2.1) :=
    primrec_triWeight.comp (hnt.pair hb)
  exact Primrec.nat_add.comp hs htw

/-- Whether a single coordinate (triple `(j,p,q)`) keeps the translate in `[0,n)`. -/
def coordOk (n t : ℕ) (jpq : ℕ × ℕ × ℕ) : Bool :=
  decide (jpq.2.2 ≤ boxDigit n t jpq.1 + jpq.2.1) &&
    decide (boxDigit n t jpq.1 + jpq.2.1 < n + jpq.2.2)

theorem primrec_coordOk :
    Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => coordOk x.1.1 x.1.2 x.2) := by
  unfold coordOk
  have hn : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.1.1) := Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.1.2) := Primrec.snd.comp Primrec.fst
  have hj : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hq : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hbd : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => boxDigit x.1.1 x.1.2 x.2.1) :=
    primrec_boxDigit.comp (hn.pair (ht.pair hj))
  have hval : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => boxDigit x.1.1 x.1.2 x.2.1 + x.2.2.1) :=
    Primrec.nat_add.comp hbd hp
  have hc1 := Primrec.nat_le.comp hq hval
  have hnq : Primrec (fun x : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => x.1.1 + x.2.2.2) :=
    Primrec.nat_add.comp hn hq
  have hc2 := Primrec.nat_lt.comp hval hnq
  exact Primrec.and.comp hc1.decide hc2.decide

/-- All coordinates of one `v` keep the translate in the box. -/
def okAll (n t : ℕ) (tr : List (ℕ × ℕ × ℕ)) : Bool :=
  tr.foldr (fun jpq r => coordOk n t jpq && r) true

theorem primrec_okAll :
    Primrec (fun x : (ℕ × ℕ) × List (ℕ × ℕ × ℕ) => okAll x.1.1 x.1.2 x.2) := by
  unfold okAll
  refine Primrec.list_foldr (f := fun x : (ℕ × ℕ) × List (ℕ × ℕ × ℕ) => x.2)
    (g := fun _ => true)
    (h := fun (a : (ℕ × ℕ) × List (ℕ × ℕ × ℕ)) (bs : (ℕ × ℕ × ℕ) × Bool) =>
      coordOk a.1.1 a.1.2 bs.1 && bs.2)
    Primrec.snd (Primrec.const true) ?_
  have hco : Primrec (fun y : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ)) × ((ℕ × ℕ × ℕ) × Bool) =>
      coordOk y.1.1.1 y.1.1.2 y.2.1) :=
    primrec_coordOk.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
  have hr : Primrec (fun y : ((ℕ × ℕ) × List (ℕ × ℕ × ℕ)) × ((ℕ × ℕ × ℕ) × Bool) => y.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp hco hr

/-- All cells of `F` (given as a list of triple-lists `sh`) keep their translates in box. -/
def relevantAllG (n t : ℕ) (sh : List (List (ℕ × ℕ × ℕ))) : Bool :=
  sh.foldr (fun tr r => okAll n t tr && r) true

set_option maxHeartbeats 1000000 in
theorem primrec_relevantAllG :
    Primrec (fun x : (ℕ × ℕ) × List (List (ℕ × ℕ × ℕ)) => relevantAllG x.1.1 x.1.2 x.2) := by
  unfold relevantAllG
  refine Primrec.list_foldr (f := fun x : (ℕ × ℕ) × List (List (ℕ × ℕ × ℕ)) => x.2)
    (g := fun _ => true)
    (h := fun (a : (ℕ × ℕ) × List (List (ℕ × ℕ × ℕ))) (bs : List (ℕ × ℕ × ℕ) × Bool) =>
      okAll a.1.1 a.1.2 bs.1 && bs.2)
    Primrec.snd (Primrec.const true) ?_
  have hok : Primrec (fun y : ((ℕ × ℕ) × List (List (ℕ × ℕ × ℕ))) × (List (ℕ × ℕ × ℕ) × Bool) =>
      okAll y.1.1.1 y.1.1.2 y.2.1) :=
    primrec_okAll.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
  have hr : Primrec (fun y : ((ℕ × ℕ) × List (List (ℕ × ℕ × ℕ))) × (List (ℕ × ℕ × ℕ) × Bool) =>
      y.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.and.comp hok hr

/-- For one allowed pattern (row `zr` = list of `(triples_v, cell_v)`), check that the
digits read off `k` at each reconstructed index match the cell values. -/
def rowMatchG (m n k t : ℕ) (zr : List (List (ℕ × ℕ × ℕ) × ℕ)) : Bool :=
  zr.foldr (fun trc r => decide (boxDigit m k (idxFromTriples n t trc.1) = trc.2) && r) true

set_option maxHeartbeats 2000000 in
theorem primrec_rowMatchG (m : ℕ) :
    Primrec (fun x : (ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ) =>
      rowMatchG m x.1.1 x.1.2.1 x.1.2.2 x.2) := by
  unfold rowMatchG
  refine Primrec.list_foldr
    (f := fun x : (ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ) => x.2)
    (g := fun _ => true)
    (h := fun (a : (ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ))
        (bs : (List (ℕ × ℕ × ℕ) × ℕ) × Bool) =>
      decide (boxDigit m a.1.2.1 (idxFromTriples a.1.1 a.1.2.2 bs.1.1) = bs.1.2) && bs.2)
    Primrec.snd (Primrec.const true) ?_
  have hn : Primrec (fun y : ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ)) ×
      ((List (ℕ × ℕ × ℕ) × ℕ) × Bool) => y.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec (fun y : ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ)) ×
      ((List (ℕ × ℕ × ℕ) × ℕ) × Bool) => y.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have ht : Primrec (fun y : ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ)) ×
      ((List (ℕ × ℕ × ℕ) × ℕ) × Bool) => y.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have htr : Primrec (fun y : ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ)) ×
      ((List (ℕ × ℕ × ℕ) × ℕ) × Bool) => y.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hc : Primrec (fun y : ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ)) ×
      ((List (ℕ × ℕ × ℕ) × ℕ) × Bool) => y.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hr : Primrec (fun y : ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ)) ×
      ((List (ℕ × ℕ × ℕ) × ℕ) × Bool) => y.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hidx : Primrec (fun y : ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ)) ×
      ((List (ℕ × ℕ × ℕ) × ℕ) × Bool) =>
      idxFromTriples y.1.1.1 y.1.1.2.2 y.2.1.1) :=
    primrec_idxFromTriples.comp ((hn.pair ht).pair htr)
  have hbd : Primrec (fun y : ((ℕ × ℕ × ℕ) × List (List (ℕ × ℕ × ℕ) × ℕ)) ×
      ((List (ℕ × ℕ × ℕ) × ℕ) × Bool) =>
      boxDigit m y.1.1.2.1 (idxFromTriples y.1.1.1 y.1.1.2.2 y.2.1.1)) :=
    primrec_boxDigit.comp ((Primrec.const m).pair (hk.pair hidx))
  have hchk := Primrec.eq.comp hbd hc
  exact Primrec.and.comp hchk.decide hr

/-- Some allowed pattern (row in `cz`) matches the digits read off `k`. -/
def matchAnyG (m n k t : ℕ) (cz : List (List (List (ℕ × ℕ × ℕ) × ℕ))) : Bool :=
  cz.foldr (fun zr r => rowMatchG m n k t zr || r) false

set_option maxHeartbeats 2000000 in
theorem primrec_matchAnyG (m : ℕ) :
    Primrec (fun x : (ℕ × ℕ × ℕ) × List (List (List (ℕ × ℕ × ℕ) × ℕ)) =>
      matchAnyG m x.1.1 x.1.2.1 x.1.2.2 x.2) := by
  unfold matchAnyG
  refine Primrec.list_foldr
    (f := fun x : (ℕ × ℕ × ℕ) × List (List (List (ℕ × ℕ × ℕ) × ℕ)) => x.2)
    (g := fun _ => false)
    (h := fun (a : (ℕ × ℕ × ℕ) × List (List (List (ℕ × ℕ × ℕ) × ℕ)))
        (bs : List (List (ℕ × ℕ × ℕ) × ℕ) × Bool) =>
      rowMatchG m a.1.1 a.1.2.1 a.1.2.2 bs.1 || bs.2)
    Primrec.snd (Primrec.const false) ?_
  have hrow : Primrec (fun y : ((ℕ × ℕ × ℕ) × List (List (List (ℕ × ℕ × ℕ) × ℕ))) ×
      (List (List (ℕ × ℕ × ℕ) × ℕ) × Bool) =>
      rowMatchG m y.1.1.1 y.1.1.2.1 y.1.1.2.2 y.2.1) :=
    (primrec_rowMatchG m).comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
  have hr : Primrec (fun y : ((ℕ × ℕ × ℕ) × List (List (List (ℕ × ℕ × ℕ) × ℕ))) ×
      (List (List (ℕ × ℕ × ℕ) × ℕ) × Bool) => y.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.or.comp hrow hr

/-- Per-index body: either offset `t` is not relevant, or some allowed pattern matches. -/
def bodyG (m : ℕ) (sh : List (List (ℕ × ℕ × ℕ)))
    (cz : List (List (List (ℕ × ℕ × ℕ) × ℕ))) (n k t : ℕ) : Bool :=
  !(relevantAllG n t sh) || matchAnyG m n k t cz

set_option maxHeartbeats 2000000 in
theorem primrec_bodyG (m : ℕ) (sh : List (List (ℕ × ℕ × ℕ)))
    (cz : List (List (List (ℕ × ℕ × ℕ) × ℕ))) :
    Primrec (fun x : ℕ × ℕ × ℕ => bodyG m sh cz x.1 x.2.1 x.2.2) := by
  unfold bodyG
  have hrel : Primrec (fun x : ℕ × ℕ × ℕ => relevantAllG x.1 x.2.2 sh) :=
    primrec_relevantAllG.comp
      ((Primrec.fst.pair (Primrec.snd.comp Primrec.snd)).pair (Primrec.const sh))
  have hnot : Primrec (fun x : ℕ × ℕ × ℕ => !(relevantAllG x.1 x.2.2 sh)) :=
    Primrec.not.comp hrel
  have hmatch : Primrec (fun x : ℕ × ℕ × ℕ => matchAnyG m x.1 x.2.1 x.2.2 cz) :=
    (primrec_matchAnyG m).comp (Primrec.id.pair (Primrec.const cz))
  exact Primrec.or.comp hnot hmatch

attribute [irreducible] boxDigit triWeight idxFromTriples coordOk okAll
  relevantAllG rowMatchG matchAnyG bodyG

/-- The full Bool decision procedure for `admPredDigit` (nonempty `F` case),
parameterised by the extracted constant data `(m, d, sh, cz)`. -/
def admBoolG (d m : ℕ) (sh : List (List (ℕ × ℕ × ℕ)))
    (cz : List (List (List (ℕ × ℕ × ℕ) × ℕ))) (n k : ℕ) : Bool :=
  decide (k < m ^ (n ^ d)) &&
    (List.range (n ^ d)).foldr (fun t r => bodyG m sh cz n k t && r) true

set_option maxHeartbeats 4000000 in
theorem primrec_admBoolG (d m : ℕ) (sh : List (List (ℕ × ℕ × ℕ)))
    (cz : List (List (List (ℕ × ℕ × ℕ) × ℕ))) :
    Primrec (fun x : ℕ × ℕ => admBoolG d m sh cz x.1 x.2) := by
  unfold admBoolG
  have hbound : Primrec (fun x : ℕ × ℕ => m ^ (x.1 ^ d)) :=
    (primrec_const_pow_pow m d).comp Primrec.fst
  have hpart1 := Primrec.nat_lt.comp Primrec.snd hbound
  have hpart2 : Primrec (fun x : ℕ × ℕ =>
      (List.range (x.1 ^ d)).foldr (fun t r => bodyG m sh cz x.1 x.2 t && r) true) := by
    refine Primrec.list_foldr
      (f := fun x : ℕ × ℕ => List.range (x.1 ^ d))
      (g := fun _ => true)
      (h := fun (a : ℕ × ℕ) (bs : ℕ × Bool) => bodyG m sh cz a.1 a.2 bs.1 && bs.2)
      (Primrec.list_range.comp ((primrec_pow_const d).comp Primrec.fst))
      (Primrec.const true) ?_
    have hbody : Primrec (fun y : (ℕ × ℕ) × (ℕ × Bool) =>
        bodyG m sh cz y.1.1 y.1.2 y.2.1) :=
      (primrec_bodyG m sh cz).comp
        ((Primrec.fst.comp Primrec.fst).pair
          ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
    have hr : Primrec (fun y : (ℕ × ℕ) × (ℕ × Bool) => y.2.2) := Primrec.snd.comp Primrec.snd
    exact Primrec.and.comp hbody hr
  exact Primrec.and.comp hpart1.decide hpart2

/-! ## Bridge: `foldr &&` over a list = bounded `∀` (for the correctness step) -/

theorem foldr_and_eq {β : Type*} (l : List β) (f : β → Bool) :
    l.foldr (fun a r => f a && r) true = decide (∀ a ∈ l, f a = true) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.forall_mem_cons, ih]
    cases f a <;> simp

theorem foldr_and_range_eq (N : ℕ) (f : ℕ → Bool) :
    (List.range N).foldr (fun t r => f t && r) true = decide (∀ t < N, f t = true) := by
  rw [foldr_and_eq]
  simp only [List.mem_range]


/-! ## Part B: correctness of the Bool procedure -/

theorem foldr_add_eq_sum_map {β : Type*} (l : List β) (f : β → ℕ) :
    l.foldr (fun x acc => acc + f x) 0 = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]; omega

/-- Constant per-cell data: for anchor `a` and point `w`, the `(j, (w-a)⁺, (a-w)⁺)` triples. -/
def triplesOf (d : ℕ) (a w : Lat d) : List (ℕ × ℕ × ℕ) :=
  (List.finRange d).map (fun j => (j.val, (w j - a j).toNat, (a j - w j).toNat))

theorem boxIndex_apply (d n t : ℕ) (j : Fin d) :
    boxIndex d n t j = ((boxDigit n t j.val : ℕ) : ℤ) := by
  unfold boxIndex boxDigit
  push_cast
  rfl

/-- KEYSTONE: the ℕ index reconstructed from `triplesOf` equals the real `boxIndexInv`. -/
theorem idxFromTriples_triplesOf (d n t : ℕ) (a w : Lat d) :
    idxFromTriples n t (triplesOf d a w) = boxIndexInv d n (w + (boxIndex d n t - a)) := by
  unfold idxFromTriples
  rw [foldr_add_eq_sum_map (triplesOf d a w) (triWeight n t)]
  unfold triplesOf
  rw [List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  unfold boxIndexInv
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp]
  unfold triWeight
  congr 1
  rw [Pi.add_apply, Pi.sub_apply, boxIndex_apply]
  rw [show w j + ((boxDigit n t j.val : ℤ) - a j) = (boxDigit n t j.val : ℤ) + (w j - a j) from
        by ring]
  rw [int_add_toNat_eq]
  rw [show a j - w j = -(w j - a j) from by ring]

/-- Per-coordinate: `coordOk` for the `(j,(w-a)⁺,(a-w)⁺)` triple ↔ that coordinate of
`w + (boxIndex - a)` lies in `[0,n)`. -/
theorem coordOk_iff {d : ℕ} (n t : ℕ) (j : Fin d) (a w : Lat d) :
    coordOk n t (j.val, (w j - a j).toNat, (a j - w j).toNat) = true ↔
      (0 ≤ (w + (boxIndex d n t - a)) j ∧ (w + (boxIndex d n t - a)) j < (n : ℤ)) := by
  unfold coordOk
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [Pi.add_apply, Pi.sub_apply, boxIndex_apply,
      show w j + ((boxDigit n t j.val : ℤ) - a j) = (boxDigit n t j.val : ℤ) + (w j - a j) from
        by ring,
      int_add_mem_range_iff, neg_sub]

/-- `okAll` on `triplesOf` ↔ the translated point lies in the box. -/
theorem okAll_triplesOf {d : ℕ} (n t : ℕ) (a w : Lat d) :
    okAll n t (triplesOf d a w) = true ↔ w + (boxIndex d n t - a) ∈ box d n := by
  unfold okAll triplesOf
  rw [foldr_and_eq _ (coordOk n t), decide_eq_true_eq, List.forall_mem_map]
  simp only [List.mem_finRange, true_implies, box, Fintype.mem_piFinset, Finset.mem_Ico]
  exact forall_congr' (fun j => coordOk_iff n t j a w)

theorem digit_eq_boxDigit (m k i : ℕ) : digit m k i = boxDigit m k i := by
  unfold digit boxDigit
  rfl

/-- `relevantAllG` on `F`'s triple-lists ↔ every cell of `F` translates into the box. -/
theorem relevantAllG_eq {d : ℕ} (n t : ℕ) (a : Lat d) (F : Finset (Lat d)) :
    relevantAllG n t (F.toList.map (triplesOf d a)) = true ↔
      ∀ w ∈ F, w + (boxIndex d n t - a) ∈ box d n := by
  unfold relevantAllG
  rw [foldr_and_eq _ (okAll n t), decide_eq_true_eq, List.forall_mem_map]
  simp only [Finset.mem_toList]
  exact forall_congr' (fun w => imp_congr_right (fun _ => okAll_triplesOf n t a w))

theorem foldr_or_eq {β : Type*} (l : List β) (f : β → Bool) :
    l.foldr (fun a r => f a || r) false = decide (∃ a ∈ l, f a = true) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ih]
    simp only [List.exists_mem_cons_iff]
    cases f a <;> simp

/-- `rowMatchG` on the row built from `ℓ` ↔ the digits read off `k` match `ℓ` at every cell. -/
theorem rowMatchG_eq {α : Type*} [Fintype α] [DecidableEq α] [Encodable α] {d : ℕ}
    (m n k t : ℕ) (a : Lat d) {F : Finset (Lat d)} (ℓ : Pattern α F) :
    rowMatchG m n k t
        ((Finset.univ : Finset F).toList.map
          (fun v => (triplesOf d a v.val, (Encodable.fintypeEquivFin (ℓ v)).val))) = true ↔
      ∀ v : F, digit m k (boxIndexInv d n (v.val + (boxIndex d n t - a))) =
        (Encodable.fintypeEquivFin (ℓ v)).val := by
  unfold rowMatchG
  rw [foldr_and_eq, decide_eq_true_eq, List.forall_mem_map]
  simp only [Finset.mem_toList, Finset.mem_univ, true_implies, decide_eq_true_eq,
    idxFromTriples_triplesOf, ← digit_eq_boxDigit]

/-- `matchAnyG` over `L`'s rows ↔ some allowed pattern matches the digits read off `k`. -/
theorem matchAnyG_eq {α : Type*} [Fintype α] [DecidableEq α] [Encodable α] {d : ℕ}
    (m n k t : ℕ) (a : Lat d) {F : Finset (Lat d)} (L : Finset (Pattern α F)) :
    matchAnyG m n k t
        (L.toList.map (fun ℓ => (Finset.univ : Finset F).toList.map
          (fun v => (triplesOf d a v.val, (Encodable.fintypeEquivFin (ℓ v)).val)))) = true ↔
      ∃ ℓ ∈ L, ∀ v : F, digit m k (boxIndexInv d n (v.val + (boxIndex d n t - a))) =
        (Encodable.fintypeEquivFin (ℓ v)).val := by
  unfold matchAnyG
  rw [foldr_or_eq, decide_eq_true_eq]
  simp only [List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨zr, ⟨ℓ, hℓ, rfl⟩, hmatch⟩
    exact ⟨ℓ, hℓ, (rowMatchG_eq m n k t a ℓ).1 hmatch⟩
  · rintro ⟨ℓ, hℓ, hv⟩
    exact ⟨_, ⟨ℓ, hℓ, rfl⟩, (rowMatchG_eq m n k t a ℓ).2 hv⟩

theorem not_or_eq_true (b1 b2 : Bool) : (!b1 || b2) = true ↔ (b1 = true → b2 = true) := by
  cases b1 <;> cases b2 <;> simp

/-- MAIN correctness (nonempty `F`): the Bool procedure decides `admPredDigit`. -/
theorem admBoolG_correct {α : Type*} [Fintype α] [DecidableEq α] [Encodable α] {d : ℕ}
    (F : Finset (Lat d)) (L : Finset (Pattern α F)) (hF : F.Nonempty) (n k : ℕ) :
    admBoolG d (Fintype.card α) (F.toList.map (triplesOf d hF.choose))
        (L.toList.map (fun ℓ => (Finset.univ : Finset F).toList.map
          (fun v => (triplesOf d hF.choose v.val, (Encodable.fintypeEquivFin (ℓ v)).val))))
        n k = true ↔ admPredDigit F L n k := by
  have hbody : ∀ t, bodyG (Fintype.card α) (F.toList.map (triplesOf d hF.choose))
      (L.toList.map (fun ℓ => (Finset.univ : Finset F).toList.map
        (fun v => (triplesOf d hF.choose v.val, (Encodable.fintypeEquivFin (ℓ v)).val))))
      n k t = true ↔
      ((∀ w ∈ F, w + (boxIndex d n t - hF.choose) ∈ box d n) →
        ∃ ℓ ∈ L, ∀ v : F,
          digit (Fintype.card α) k (boxIndexInv d n (v.val + (boxIndex d n t - hF.choose))) =
            (Encodable.fintypeEquivFin (ℓ v)).val) := by
    intro t
    unfold bodyG
    rw [not_or_eq_true, relevantAllG_eq, matchAnyG_eq]
  rw [admPredDigit_iff_boxIndex F L hF]
  unfold admBoolG
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr_right (fun _ => ?_)
  rw [foldr_and_eq, decide_eq_true_eq]
  simp only [List.mem_range]
  exact forall_congr' (fun t => imp_congr_right (fun _ => hbody t))

/-- `F = ∅` case: admissibility reduces to the bound and `L` being nonempty. -/
theorem admPredDigit_empty {α : Type*} [Fintype α] [DecidableEq α] [Encodable α] {d : ℕ}
    (L : Finset (Pattern α (∅ : Finset (Lat d)))) (n k : ℕ) :
    admPredDigit (∅ : Finset (Lat d)) L n k ↔
      k < (Fintype.card α) ^ (n ^ d) ∧ L.Nonempty := by
  unfold admPredDigit
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h
    obtain ⟨ℓ, hℓ, _⟩ := h 0 (by simp [relevantOffsets])
    exact ⟨ℓ, hℓ⟩
  · rintro ⟨ℓ, hℓ⟩ u _
    exact ⟨ℓ, hℓ, fun v => absurd v.property (Finset.notMem_empty v.val)⟩

/-- ★ DISCHARGE: the digit-level local-admissibility predicate is `Primrec₂` in `(n,k)`.
This is exactly the statement of the axiom `primrec_admPredDigit`. -/
theorem primrec_admPredDigit_impl {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d : ℕ} (F : Finset (Lat d)) (L : Finset (Pattern α F)) :
    Primrec₂ (fun n k : ℕ => decide (admPredDigit F L n k)) := by
  by_cases hF : F.Nonempty
  · exact (primrec_admBoolG d (Fintype.card α) (F.toList.map (triplesOf d hF.choose))
      (L.toList.map (fun ℓ => (Finset.univ : Finset F).toList.map
        (fun v => (triplesOf d hF.choose v.val, (Encodable.fintypeEquivFin (ℓ v)).val))))).of_eq
      (fun p => by simp [← admBoolG_correct F L hF p.1 p.2])
  · have hFe : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst hFe
    have key : ∀ n k : ℕ, decide (admPredDigit (∅ : Finset (Lat d)) L n k) =
        (decide (k < (Fintype.card α) ^ (n ^ d)) && decide L.Nonempty) := by
      intro n k; simp only [admPredDigit_empty]; by_cases hL : L.Nonempty <;> simp [hL]
    have hP : Primrec (fun p : ℕ × ℕ =>
        decide (p.2 < (Fintype.card α) ^ (p.1 ^ d)) && decide L.Nonempty) :=
      Primrec.and.comp
        (Primrec.nat_lt.comp Primrec.snd
          ((primrec_const_pow_pow (Fintype.card α) d).comp Primrec.fst)).decide
        (Primrec.const (decide L.Nonempty))
    exact hP.of_eq (fun p => (key p.1 p.2).symm)

end AdmPredPrimrec

/-- The digit-level local-admissibility predicate `admPredDigit F L n k` is
primitive recursive in `(n, k)`. Discharges the former axiom of the same name. -/
theorem primrec_admPredDigit {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    {d : ℕ} (F : Finset (Lat d)) (L : Finset (Pattern α F)) :
    Primrec₂ (fun n k : ℕ => decide (admPredDigit F L n k)) :=
  AdmPredPrimrec.primrec_admPredDigit_impl F L
