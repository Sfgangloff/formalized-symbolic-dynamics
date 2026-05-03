# Implementation List — Hochman–Meyerovitch Formalization

Each item is a single self-contained unit: a `def`, `instance`, `theorem+proof`, or `axiom`.
Items marked [sorry] are admitted for now and revisited later.
Tick the checkbox when the item compiles without errors.

---

## Checklist

### Lat — the lattice ℤ^d
- [ ] 0.1  `abbrev Lat (d : ℕ) := Fin d → ℤ`
- [ ] 0.2  `def Lat.supNorm`
- [ ] 0.3  `theorem Lat.supNorm_zero`
- [ ] 0.4  `theorem Lat.supNorm_nonneg`

### FullShift — α^{ℤ^d}
- [ ] 0.5  `abbrev FullShift (α : Type*) (d : ℕ) : Type* := Lat d → α`
- [ ] 0.5b `@[ext] lemma FullShift.ext`  (register funext as the ext lemma)
- [ ] 0.6  `def FullShift.shiftMap`
- [ ] 0.7  `theorem FullShift.shiftMap_zero`
- [ ] 0.8  `theorem FullShift.shiftMap_add`
- [ ] 0.9  `instance FullShift.instAddAction`
- [ ] 0.10 `theorem FullShift.vadd_eq_shiftMap`
- [ ] 0.11 `theorem FullShift.shiftMap_bijective`
- [ ] 0.12 `instance FullShift` topology instances (TopologicalSpace, CompactSpace, T2Space)
- [ ] 0.13 `theorem FullShift.shiftMap_continuous`

### A — Missing subshift infrastructure
- [ ] A1  `def FullShift.shiftMap_homeomorph` (σ^u is a homeomorphism)
- [ ] A2  `def Subshift.bot` (empty subshift)
- [ ] A3  `def Subshift.inter` (intersection of two subshifts)
- [ ] A4  `def Subshift.iInter` (arbitrary indexed intersection)

### Pattern
- [ ] 0.14 `abbrev Pattern (α : Type*) {d : ℕ} (F : Finset (Lat d)) : Type* := F → α`
- [ ] 0.15 `def Pattern.ofColoring`
- [ ] 0.16 `def Pattern.restrict`
- [ ] 0.17 `def Pattern.translateFinset`
- [ ] 0.18 `theorem Pattern.mem_translateFinset`
- [ ] 0.19 `def Pattern.AppearsAt`
- [ ] 0.20 `def Pattern.Appears`
- [ ] 0.21 `def Pattern.cylinder`
- [ ] 0.22 `theorem Pattern.mem_cylinder_iff`
- [ ] 0.23 `theorem Pattern.cylinder_isOpen`
- [ ] 0.24 `theorem Pattern.cylinder_isClosed`

### Subshift
- [ ] 0.25 `structure Subshift`
- [ ] 0.26 `instance Subshift.Membership`
- [ ] 0.27 `theorem Subshift.mem_iff`
- [ ] 0.28 `def Subshift.univ`

### SFT
- [ ] 0.29 `def SFT_admissible`
- [ ] 0.30 `def SFT_carrier`
- [ ] 0.31 `theorem SFT_carrier_isInvariant`
- [ ] 0.32 `theorem SFT_carrier_isClosed`
- [ ] 0.33 `def mkSFT`
- [ ] 0.34 `theorem mem_mkSFT`

### Local admissibility and irreducibility
- [ ] 0.35 `def locallyAdmissible`
- [ ] 0.36 `def ShiftIrreducible`
- [ ] 0.37 `def IsIrreducibleShift`

### B — Global admissibility and pattern count
- [ ] B1  `def Pattern.GloballyAdmissible`
- [ ] B2  `theorem Pattern.globallyAdmissible_iff_exists_offset`
- [ ] B3  `theorem Pattern.globally_imp_locally`
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
- [ ] E2  `theorem topEntropy_nonneg`
- [ ] E3  `theorem topEntropy_fullShift`
- [ ] E4  `theorem topEntropy_antitone`

### F — Computability definitions
- [ ] F1  `def IsRightRE (h : ℝ) : Prop`
- [ ] F2  `def IsLeftRE (h : ℝ) : Prop`
- [ ] F3  `def IsComputableReal (h : ℝ) : Prop`
- [ ] F4  `theorem computable_imp_rightRE`
- [ ] F5  `theorem computable_iff_leftRE_and_rightRE`

### G — Local count and computability
- [ ] G1  `def locallyAdmissiblePatterns [DecidableEq α] (L : ...) (E : ...) : Finset (Pattern α E)`
- [ ] G2  `def N_bar [DecidableEq α] (L : ...) (n : ℕ) : ℕ`
- [ ] G3  `theorem N_X_le_N_bar`
- [ ] G4  `theorem N_bar_computable`

### H — Key axioms for Theorem 3.1
- [ ] H1  `axiom variationalPrinciple`
- [ ] H2  `axiom entropy_usc`
- [ ] H3  `axiom M_compact`

### I — Theorem 3.1
- [ ] I1  `theorem topEntropy_rightRE`
