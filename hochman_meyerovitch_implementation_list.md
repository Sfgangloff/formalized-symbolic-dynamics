# Implementation List — Hochman–Meyerovitch Formalization

Each item is a single self-contained unit: a `def`, `instance`, `theorem+proof`, or `axiom`.
Items marked [sorry] are admitted for now and revisited later.
Tick the checkbox when the item compiles without errors.

---

## Checklist

### Lat — the lattice ℤ^d
- [x] 0.1  `abbrev Lat (d : ℕ) := Fin d → ℤ`
- [x] 0.2  `def Lat.supNorm`
- [x] 0.3  `theorem Lat.supNorm_zero`
- [x] 0.4  `theorem Lat.supNorm_nonneg`

### FullShift — α^{ℤ^d}
- [x] 0.5  `abbrev FullShift (α : Type*) (d : ℕ) : Type* := Lat d → α`
- [x] 0.5b `@[ext] lemma FullShift.ext`  (register funext as the ext lemma)
- [x] 0.6  `def FullShift.shiftMap`
- [x] 0.7  `theorem FullShift.shiftMap_zero`
- [x] 0.8  `theorem FullShift.shiftMap_add`
- [x] 0.9  `instance FullShift.instAddAction`
- [x] 0.10 `theorem FullShift.vadd_eq_shiftMap`
- [x] 0.11 `theorem FullShift.shiftMap_bijective`
- [x] 0.12 `instance FullShift` topology instances (TopologicalSpace, CompactSpace, T2Space)
- [x] 0.13 `theorem FullShift.shiftMap_continuous`

### A — Missing subshift infrastructure
- [x] A1  `def FullShift.shiftMap_homeomorph` (σ^u is a homeomorphism)
- [x] A2  `def Subshift.bot` (empty subshift)
- [x] A3  `def Subshift.inter` (intersection of two subshifts)
- [x] A4  `def Subshift.iInter` (arbitrary indexed intersection)

### Pattern
- [x] 0.14 `abbrev Pattern (α : Type*) {d : ℕ} (F : Finset (Lat d)) : Type* := F → α`
- [x] 0.15 `def Pattern.ofColoring`
- [x] 0.16 `def Pattern.restrict`
- [x] 0.17 `def Pattern.translateFinset`
- [x] 0.18 `theorem Pattern.mem_translateFinset`
- [x] 0.19 `def Pattern.AppearsAt`
- [x] 0.20 `def Pattern.Appears`
- [x] 0.21 `def Pattern.cylinder`
- [x] 0.22 `theorem Pattern.mem_cylinder_iff`
- [x] 0.23 `theorem Pattern.cylinder_isOpen`
- [x] 0.24 `theorem Pattern.cylinder_isClosed`

### Subshift
- [x] 0.25 `structure Subshift`
- [x] 0.26 `instance Subshift.Membership`
- [x] 0.27 `theorem Subshift.mem_iff`
- [x] 0.28 `def Subshift.univ`

### SFT
- [x] 0.29 `def SFT_admissible`
- [x] 0.30 `def SFT_carrier`
- [x] 0.31 `theorem SFT_carrier_isInvariant`
- [x] 0.32 `theorem SFT_carrier_isClosed`
- [x] 0.33 `def mkSFT`
- [x] 0.34 `theorem mem_mkSFT`

### Local admissibility and irreducibility
- [x] 0.35 `def locallyAdmissible`
- [x] 0.36 `def ShiftIrreducible`
- [x] 0.37 `def IsIrreducibleShift`

### B — Global admissibility and pattern count
- [x] B1  `def Pattern.GloballyAdmissible`
- [x] B2  `theorem Pattern.globallyAdmissible_iff_exists_offset`
- [x] B3  `theorem Pattern.globally_imp_locally`
- [x] B4  `def N_X [Fintype α] (X : Subshift α d) (F : Finset (Lat d)) : ℕ`
- [x] B5  `theorem N_X_pos_of_nonempty`

### C — Boxes F_n = {0,...,n-1}^d
- [x] C1  `def box (d n : ℕ) : Finset (Lat d)`
- [x] C2  `theorem box_card`  (`(box d n).card = n ^ d`)
- [x] C3  `theorem box_mono`  (`m ≤ n → box d m ⊆ box d n`)
- [x] C4  `theorem box_zero`  (`box d 0 = ∅`, requires `0 < d`)

### D — Subadditive structure and Fekete
- [x] D1  `theorem N_X_submultiplicative`
- [x] D2  `def logN (X : Subshift α d) (n : ℕ) : ℝ`
- [x] D3  `theorem logN_subadditive`
- [x] D4  `theorem Fekete_1d`  (wrapper for Mathlib's `Subadditive.tendsto_lim`)
- [x] D5  `theorem logN_div_pow_tendsto`  (1D, via Fekete + D3)

### E — Topological entropy
- [x] E1  `def topEntropy [Fintype α] (X : Subshift α d) : ℝ`
- [x] E2  `theorem topEntropy_nonneg`
- [x] E3  `theorem topEntropy_fullShift`
- [x] E4  `theorem topEntropy_antitone`  (monotone in subshift inclusion)

### F — Computability definitions
- [x] F1  `def IsRightRE (h : ℝ) : Prop`
- [x] F2  `def IsLeftRE (h : ℝ) : Prop`
- [x] F3  `def IsComputableReal (h : ℝ) : Prop`
- [x] F4  `theorem computable_imp_rightRE`
- [x] F4a `theorem computable_imp_leftRE`
- [x] F5  `theorem computable_iff_leftRE_and_rightRE`

### G — Local count and computability
- [x] G1  `def locallyAdmissiblePatterns [DecidableEq α] (L : ...) (E : ...) : Finset (Pattern α E)`
- [x] G2  `def N_bar [DecidableEq α] (L : ...) (n : ℕ) : ℕ`
- [x] G3  `theorem N_X_le_N_bar`
- [x] G4.1 `def relevantOffsets : Finset (Lat d)`
- [x] G4.2 `theorem locallyAdmissible_iff_relevantOffsets`
- [x] G4.3 `instance decidable_locallyAdmissible`  (drops `noncomputable` from G1/G2)
- [x] G4.4a `theorem N_bar_le_card_pow`  (trivial bound `≤ |α|^(n^d)`)
- [x] G4.4b `theorem N_bar_mono`  (monotone in `L`)
- [x] G4.4c `noncomputable def Pattern.toList`  (List α encoding bridge, noncomputable)
- [x] G4.4d `theorem N_bar_eq_fintype_card_subtype`  (alternative formulation via Fintype.card)
- [x] G4.4e `def boxIndex` + `boxIndex_mem`  (computable enumeration via base-n digits)
- [x] G4.4f-pre `def boxFnEquiv : ↥(box d n) ≃ (Fin d → Fin n)`
- [x] G4.4f `def boxIxEquiv : ↥(box d n) ≃ Fin (n^d)` and
            `def patternFnEquiv : Pattern α (box d n) ≃ (Fin (n^d) → α)`
- [x] G4.4g `theorem N_bar_eq_fin_arrow_card` (transports count to `Fin (n^d) → α`)
- [x] G4.4g' `theorem fintype_card_pattern_eq` (`|Pattern α (box d n)| = |α|^(n^d)` via the bridge)
- [x] G4.4h-pre `theorem primrec_nat_pow`, `primrec_pow_const`, `primrec_const_pow_pow`
            (Primrec helpers for the iteration bound `(card α)^(n^d)`)
- [x] G4.4h-step1 `def digit`, `theorem primrec_digit`, `digit_lt`
            (base-m digit extraction, Primrec₂)
- [x] G4.4h-step2 `def decodeList`, `theorem primrec_decodeList`,
            `decodeList_length`, `decodeList_get`, `decodeList_lt`
            (list-of-digits encoding as uniform-shape representation)
- [x] G4.4h-step2.5 `def boxIndexInv` + `boxIxEquiv_val`
            (explicit base-n formula `Σ_j v_j.toNat * n^j` for the `boxIxEquiv`)
- [x] G4.4h-step2.6 `boxIxEquiv_symm_val`, `boxIndex_boxIndexInv`,
            `boxIndexInv_boxIndex` (full explicit-formula bijection
            between `box d n` and `[0, n^d)`)
- [x] G4.4h-step3 `def admissibleEncoded` — Prop predicate on (n, k) at digit level
- [x] G4.4h-step4 `instance decidable_admissibleEncoded` — auto-derived Decidable
- [ ] G4.4h-step5 Connect `admissibleEncoded` to `locallyAdmissible` via patternFnEquiv
            (round-trip via `Encodable.encode_decode`)
- [ ] G4.4i Express `N_bar F L` via `Nat.count (decide ∘ admissibleEncoded) (m^(n^d))`
            and prove Primrec
- [ ] G4.4 `theorem N_bar_computable` — Lean-level `Computable (fun n => N_bar F L n)`

### H — Key axioms for Theorem 3.1
- [ ] H1  `axiom variationalPrinciple`
- [ ] H2  `axiom entropy_usc`
- [ ] H3  `axiom M_compact`

### I — Theorem 3.1
- [ ] I1  `theorem topEntropy_rightRE`

### J — Milestone 4: Symmetric cubes and r-compatibility (Theorem 1.3)
- [x] J1  `def symBox (d n : ℕ) : Finset (Lat d)`  (Q_n)
- [x] J2  `theorem symBox_card`  ((2n+1)^d)
- [x] J3  `theorem symBox_mono`
- [x] J4  `theorem box_subset_symBox`
- [x] J5  `def Pattern.unionDisjoint`  (combine patterns on disjoint supports)
- [x] J6  `def Pattern.rCompatible`  (r-compatibility on symmetric cubes)
- [x] J6a `theorem Pattern.rCompatible.globallyAdmissible`  (inner pattern is gloAdm)
- [x] J6b `theorem symBox_disjoint_sdiff`  (Q_k disjoint from Q_N \ Q_{k+r})
- [x] J6c `theorem Lat.supNorm_sub_ge_of_inner_outer`  (geometric separation ≥ r+1)
- [x] J6d `theorem Lat.supNorm_neg`, `Lat.supNorm_sub_comm`
- [x] J6e `theorem Pattern.globallyAdmissible_iff_appearsAt_zero`  (offset 0 normalization)
- [x] J6f `theorem Pattern.rCompatible_of_irreducible`  (irreducibility → r-compatibility)
- [ ] J7  Lemma 3.4 (compactness dichotomy)
- [ ] J8  Corollary 3.5 (decidability of global admissibility)
- [ ] J9  Theorem 1.3 (entropy of irreducible SFT is computable)

---

## Dependencies (helper modules in `SymbolicDynamics/Dependencies/`)

### Computable ℚ — arithmetic on ℚ for the F-section
- [ ] DEP.Q.1  `Primrec` instance for ℚ via the `(num, den)` pair encoding
- [ ] DEP.Q.2  `Computable` rational addition `(· + ·) : ℚ → ℚ → ℚ`
- [ ] DEP.Q.3  `Computable` rational reciprocal `1 / (·) : ℚ → ℚ`
- [ ] DEP.Q.4  `Computable` natural-cast `(· : ℕ → ℚ)`
- [ ] DEP.Q.5  `Computable` of `fun n : ℕ => 1 / ((n : ℚ) + 1)`
