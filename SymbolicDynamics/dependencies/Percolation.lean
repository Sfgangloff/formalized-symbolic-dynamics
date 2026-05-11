import dependencies.Subshift
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity

/-! # Percolation on `ℤ^d`

This file packages the percolation-theoretic vocabulary needed to state
the *multidimensional odd shift* problem (Hochman). It defines:

- `Lat.adjOne d : SimpleGraph (Lat d)` — the Cayley graph of `ℤ^d` with
  the standard generating set (two lattice points are adjacent iff
  `∑_i |u_i - v_i| = 1`).
- `occupiedGraph x` — the induced subgraph on the set of occupied
  sites `{v | x v = true}` of a configuration `x : FullShift Bool d`.
- `oddShiftSet d` — the set of configurations all of whose finite
  occupied components have odd cardinality.
- `evenShiftSet d` — its even counterpart.

No proofs about these definitions yet — the open problem
(`openProblems/OddShiftSoficity/`) is about whether `oddShiftSet d`
forms a sofic subshift. -/

namespace Lat

/-- The Cayley graph of `ℤ^d` with the standard generating set: two
lattice points are adjacent iff their ℓ¹-distance equals `1`,
equivalently they differ in exactly one coordinate by exactly `±1`. -/
def adjOne (d : ℕ) : SimpleGraph (Lat d) :=
  SimpleGraph.fromRel
    (fun u v : Lat d => ∑ i, ((u i) - (v i)).natAbs = 1)

end Lat

namespace Percolation

variable {d : ℕ}

/-- For a configuration `x : FullShift Bool d`, the induced graph on
the **occupied sites** `{v | x v = true}`, using the `ℓ¹`-adjacency on
`ℤ^d`. -/
def occupiedGraph (x : FullShift Bool d) :
    SimpleGraph {v : Lat d // x v = true} :=
  SimpleGraph.induce {v | x v = true} (Lat.adjOne d)

/-- The **odd shift set** in dimension `d` (Hochman): configurations
`x : FullShift Bool d` such that every finite connected component of
`occupiedGraph x` has *odd* cardinality. -/
def oddShiftSet (d : ℕ) : Set (FullShift Bool d) :=
  { x | ∀ C : (occupiedGraph x).ConnectedComponent,
        C.supp.Finite → Odd C.supp.ncard }

/-- The **even shift set** in dimension `d`: configurations all of
whose finite occupied components have *even* cardinality. Hochman
remarks that the corresponding subshift is sofic (`d = 2`). -/
def evenShiftSet (d : ℕ) : Set (FullShift Bool d) :=
  { x | ∀ C : (occupiedGraph x).ConnectedComponent,
        C.supp.Finite → Even C.supp.ncard }

end Percolation
