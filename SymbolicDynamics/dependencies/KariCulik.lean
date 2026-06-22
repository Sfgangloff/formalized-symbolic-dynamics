import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Ring.Int.Parity
import dependencies.Subshift
import dependencies.Box
import Mathlib.Data.Real.Basic

/-! # Kari–Culik tile alphabet and SFT (DGG 14-tile variant)

Concrete formalisation of the Durand–Gamard–Grandjean variant of the
Kari–Culik aperiodic Wang tileset, as 14 tiles with explicit edge
colour data.

The tile-matching SFT is built directly: `kariCulikShift` is now a
`def`, not an axiom, with a 3-element window `kcWindow = {(0,0),
(1,0), (0,1)}` and an explicit `kcAllowed` finset of admissible
L-shape patterns. `IsSFT kariCulikShift` is a theorem.

Non-emptiness (`kariCulikShift_carrier_nonempty`) remains in
`axioms/KariCulik.lean` for now: a 2×2-periodic configuration
`kcWitness` is defined here that witnesses non-emptiness empirically
(the MCP `symdyn-tilings` tool finds it), but the membership proof
involves substantial casework on lattice-coordinate parity that is
deferred. Replacing the axiom by the proof is mechanical but verbose.

References:
- Durand, Gamard, Grandjean 2013, arXiv:1312.4126v2,
  *Aperiodic tilings and entropy* — the 14-tile encoding `t1..t14`
  reproduced here, in the order it appears in the paper.
- Kari, *A small aperiodic set of Wang tiles*, Discrete Math. 160
  (1996) 259–264.
- Culik, *An aperiodic set of 13 Wang tiles*, Discrete Math. 160
  (1996) 245–251 — the *original* Kari–Culik 13-tile sets, distinct
  from the DGG variant encoded here. -/

/-! ## Edge colour types -/

/-- Colours appearing on the N/S (horizontal) sides of a DGG tile.
Three colours, named `letter0`, `letter1`, `letter2` in DGG; we use
the corresponding `Fin 3` indices. -/
abbrev KCHColor : Type := Fin 3

/-- Colours appearing on the E/W (vertical) sides of a DGG tile. Six
colours `state01, state03, state11, state13, state23, statep3` in
DGG, indexed 0..5 in this listing order. -/
abbrev KCVColor : Type := Fin 6

/-! ## The 14-tile alphabet -/

/-- The DGG 14-tile alphabet. -/
-- @ontology: kari-culik-tile-set
def KCTile : Type := Fin 14

namespace KCTile

instance instFintype : Fintype KCTile := inferInstanceAs (Fintype (Fin 14))
instance instDecidableEq : DecidableEq KCTile := inferInstanceAs (DecidableEq (Fin 14))
instance instEncodable : Encodable KCTile := inferInstanceAs (Encodable (Fin 14))
instance instInhabited : Inhabited KCTile := inferInstanceAs (Inhabited (Fin 14))

/-- Discrete topology on the tile alphabet. -/
instance instTopologicalSpace : TopologicalSpace KCTile := ⊥
instance instDiscreteTopology : DiscreteTopology KCTile := ⟨rfl⟩
instance instT1Space : T1Space KCTile := inferInstance
instance instT2Space : T2Space KCTile := inferInstance

end KCTile

/-! ## Edge-colour data for each tile

Tile-by-tile breakdown (DGG t1..t14, here indexed by `Fin 14` 0..13):

| i  | tile | N | S | E | W |
|----|------|---|---|---|---|
| 0  | t1   | letter2 | letter1 | state01 | state01 |
| 1  | t2   | letter0 | letter2 | state03 | state23 |
| 2  | t3   | letter1 | letter1 | state23 | state03 |
| 3  | t4   | letter1 | letter1 | state11 | state01 |
| 4  | t5   | letter0 | letter1 | state13 | state23 |
| 5  | t6   | letter1 | letter2 | state23 | state13 |
| 6  | t7   | letter2 | letter1 | state11 | state11 |
| 7  | t8   | letter2 | letter2 | state13 | statep3 |
| 8  | t9   | letter1 | letter1 | state23 | state13 |
| 9  | t10  | letter1 | letter1 | state13 | state03 |
| 10 | t11  | letter1 | letter1 | state03 | statep3 |
| 11 | t12  | letter2 | letter1 | statep3 | state03 |
| 12 | t13  | letter2 | letter1 | state03 | state13 |
| 13 | t14  | letter2 | letter1 | state13 | state23 |

Indices for V-colours: state01↦0, state03↦1, state11↦2, state13↦3,
state23↦4, statep3↦5. -/

/-- North-edge colour of tile `i`. -/
def kcN : KCTile → KCHColor :=
  ![2, 0, 1, 1, 0, 1, 2, 2, 1, 1, 1, 2, 2, 2]

/-- South-edge colour of tile `i`. -/
def kcS : KCTile → KCHColor :=
  ![1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1]

/-- East-edge colour of tile `i`. -/
def kcE : KCTile → KCVColor :=
  ![0, 1, 4, 2, 3, 4, 2, 3, 4, 3, 1, 5, 1, 3]

/-- West-edge colour of tile `i`. -/
def kcW : KCTile → KCVColor :=
  ![0, 4, 1, 0, 4, 3, 2, 5, 3, 1, 5, 1, 3, 4]

/-! ## SFT presentation

Window: the L-shape `{(0,0), (1,0), (0,1)}`. Allowed patterns: those
whose three tiles agree on the two shared edges — the N edge of (0,0)
matches the S edge of (0,1), and the E edge of (0,0) matches the W
edge of (1,0). -/

/-- The Kari–Culik SFT window: `{(0,0), (1,0), (0,1)} ⊂ ℤ²`. -/
def kcWindow : Finset (Lat 2) :=
  {![0, 0], ![1, 0], ![0, 1]}

private theorem kc_mem_00 : (![(0 : ℤ), 0] : Lat 2) ∈ kcWindow := by
  simp [kcWindow]

private theorem kc_mem_10 : (![(1 : ℤ), 0] : Lat 2) ∈ kcWindow := by
  simp [kcWindow]

private theorem kc_mem_01 : (![(0 : ℤ), 1] : Lat 2) ∈ kcWindow := by
  simp [kcWindow]

/-- Admissible L-shape patterns: tiles agree on shared edges. -/
def kcAllowed : Finset (Pattern KCTile kcWindow) :=
  Finset.univ.filter fun p =>
    kcN (p ⟨![0, 0], kc_mem_00⟩) = kcS (p ⟨![0, 1], kc_mem_01⟩) ∧
    kcE (p ⟨![0, 0], kc_mem_00⟩) = kcW (p ⟨![1, 0], kc_mem_10⟩)

/-- The Kari–Culik 2D shift: the SFT presented by the L-shape window
and the edge-matching constraints on the 14 DGG tiles. -/
-- @ontology: kari-culik-shift
def kariCulikShift : Subshift KCTile 2 := mkSFT kcWindow kcAllowed

/-! ## Trivial structural facts -/

/-- `kariCulikShift` is, by construction, an SFT. -/
theorem kariCulikShift_isSFT : IsSFT kariCulikShift := mkSFT_isSFT _ _

/-! ## A 2×2-periodic witness configuration

The DGG 14-tile variant admits a 2×2-periodic Wang tiling using
tiles t6 (Fin 14 index 5) and t14 (Fin 14 index 13), placed by parity
of the coordinate sum. The MCP `symdyn-tilings` tool finds this witness
via `symdyn_wang_periodic_search('kari_culik_14_dgg', 2, 2)`.

The membership proof
  `kcWitness ∈ kariCulikShift.carrier`
involves a parity case-split on every lattice position and four
finite edge-matching checks per case. It is mechanical but tedious;
in this file we record only the witness function. The non-emptiness
axiom `kariCulikShift_carrier_nonempty` lives in
`axioms/KariCulik.lean` and is justified empirically by this witness
plus the MCP transfer-matrix computation; replacing the axiom by a
proof here is a finite mechanical exercise. -/

/-- The 2×2-periodic Kari–Culik configuration alternating tiles
t6 (`Fin 14` index 5) and t14 (`Fin 14` index 13) by parity of
`u 0 + u 1`. Witnesses non-emptiness. -/
def kcWitness : FullShift KCTile 2 := fun u =>
  if Even (u 0 + u 1) then (5 : Fin 14) else (13 : Fin 14)

/-- The Kari–Culik shift is nonempty: the 2×2-periodic `kcWitness` is a valid
configuration. Discharges the former axiom `kariCulikShift_carrier_nonempty`. -/
-- @ontology: kc:thm:nonempty
theorem kariCulikShift_carrier_nonempty : kariCulikShift.carrier.Nonempty := by
  refine ⟨kcWitness, ?_⟩
  show SFT_admissible kcWindow kcAllowed kcWitness
  intro u
  have sumeq : ∀ a b : ℤ,
      ((![a, b] : Lat 2) + u) 0 + ((![a, b] : Lat 2) + u) 1 = a + b + (u 0 + u 1) := by
    intro a b
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  have wit : ∀ a b : ℤ, kcWitness ((![a, b] : Lat 2) + u)
      = if Even (a + b + (u 0 + u 1)) then (5 : Fin 14) else 13 := by
    intro a b
    show (if Even (((![a, b] : Lat 2) + u) 0 + ((![a, b] : Lat 2) + u) 1)
        then (5 : Fin 14) else 13) = _
    rw [sumeq a b]
  simp only [kcAllowed, Finset.mem_filter, Finset.mem_univ, true_and,
    Pattern.ofColoring, FullShift.shiftMap]
  rw [wit 0 0, wit 0 1, wit 1 0]
  by_cases h : Even (u 0 + u 1) <;> simp [h, parity_simps] <;> decide

/-- The Kari–Culik shift with a finite set `S` of 2×2 patterns additionally
forbidden: intersect `kariCulikShift` with the SFT whose allowed 2×2 patterns
are all those *not* in `S`. Discharges the former opaque axiom of the same name. -/
def kariCulikShift_forbid (S : Finset (Pattern KCTile (box 2 2))) : Subshift KCTile 2 :=
  Subshift.inter kariCulikShift (mkSFT (box 2 2) (Finset.univ \ S))

/-! ## Horizontal (row-0) projection of the Kari–Culik shift -/

/-- Embed a 1D lattice position as the row-0 position in 2D. -/
def kcRowEmbed (p : Lat 1) : Lat 2 := ![p 0, 0]

/-- Project a 2D configuration to its row-0 horizontal line. -/
def kcRowProj (y : FullShift KCTile 2) : FullShift KCTile 1 := fun p => y (kcRowEmbed p)

theorem kcRowEmbed_add (p u : Lat 1) : kcRowEmbed (p + u) = kcRowEmbed p + kcRowEmbed u := by
  funext j
  fin_cases j <;>
    simp [kcRowEmbed, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem continuous_kcRowProj : Continuous kcRowProj :=
  continuous_pi (fun p => continuous_apply (kcRowEmbed p))

/-- The 1D subshift of horizontal (row-0) lines of valid Kari–Culik tilings:
the image of `kariCulikShift` under the row-0 projection. It is closed (a
continuous image of a compact set) and shift-invariant. Discharges the former
opaque axiom `kariCulikHorizontalShift`. -/
def kariCulikHorizontalShift : Subshift KCTile 1 where
  carrier := kcRowProj '' kariCulikShift.carrier
  isClosed := (kariCulikShift.isClosed.isCompact.image continuous_kcRowProj).isClosed
  isInvariant := by
    rintro u x ⟨y, hy, rfl⟩
    refine ⟨FullShift.shiftMap (kcRowEmbed u) y,
      kariCulikShift.isInvariant (kcRowEmbed u) y hy, ?_⟩
    funext v
    show y (kcRowEmbed v + kcRowEmbed u) = y (kcRowEmbed (v + u))
    rw [kcRowEmbed_add]

/-! ## Positive density of patterns -/

/-- `p` appears with **positive (lower) density** in `x`: there is `c > 0` such that,
for all large `n`, the fraction of offsets in `symBox d n` at which `p` occurs is at
least `c`. Discharges the former opaque axiom `Pattern.hasPositiveDensity`. -/
def Pattern.hasPositiveDensity {α : Type*} {d : ℕ} [TopologicalSpace α]
    {F : Finset (Lat d)} (p : Pattern α F) (x : FullShift α d) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
    c ≤ ({u : Lat d | u ∈ symBox d n ∧ Pattern.AppearsAt p x u}.ncard : ℝ)
        / ((2 * (n : ℝ) + 1) ^ d)
