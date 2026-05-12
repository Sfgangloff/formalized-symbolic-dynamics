import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Fintype.Basic
import dependencies.Subshift

/-! # Kari–Culik tile alphabet

The Kari–Culik aperiodic tile set has 13 Wang tiles. We model the
alphabet as `Fin 13` carrying the discrete topology. The actual SFT
structure (tile-matching constraints) is opaque here and axiomatized in
`axioms/KariCulik.lean`; this file only fixes the alphabet and the
instances downstream constructs (Subshift, `topEntropy`, …) need.
-/

/-- The Kari–Culik tile alphabet: 13 tiles. -/
def KCTile : Type := Fin 13

namespace KCTile

instance instFintype : Fintype KCTile := inferInstanceAs (Fintype (Fin 13))
instance instDecidableEq : DecidableEq KCTile := inferInstanceAs (DecidableEq (Fin 13))
instance instEncodable : Encodable KCTile := inferInstanceAs (Encodable (Fin 13))
instance instInhabited : Inhabited KCTile := inferInstanceAs (Inhabited (Fin 13))

/-- Discrete topology on the tile alphabet. -/
instance instTopologicalSpace : TopologicalSpace KCTile := ⊥
instance instDiscreteTopology : DiscreteTopology KCTile := ⟨rfl⟩
instance instT1Space : T1Space KCTile := inferInstance
instance instT2Space : T2Space KCTile := inferInstance

end KCTile
