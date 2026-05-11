import dependencies.FactorMap
import dependencies.Percolation

/-! # Multidimensional odd shift — is it sofic?

**Conjecture / open problem (Hochman).** *Is the `d`-dimensional odd
shift `Y_d ⊆ {0,1}^{ℤ^d}` sofic?*

`Y_d` is the set of configurations in which **every finite connected
component of the occupied sites** (under the ℓ¹-distance-1 Cayley graph
of `ℤ^d`) has **odd** cardinality. The supporting definitions
(`Lat.adjOne`, `Percolation.occupiedGraph`, `Percolation.oddShiftSet`)
live in [`../../dependencies/Percolation.lean`](../../dependencies/Percolation.lean);
sofic-ness is defined in
[`../../dependencies/FactorMap.lean`](../../dependencies/FactorMap.lean).

This file records the **statement** of the conjecture in Lean. The
existential formulation below sidesteps having to prove (separately)
that `oddShiftSet` is closed and shift-invariant: the existential
witness, if it exists, is the SFT cover that the conjecture concerns.

See [`README.md`](README.md) for known cases and references. -/

/-- **Odd-shift soficity (statement).** There exists a subshift
`S : Subshift Bool d` whose carrier coincides with the percolation odd
set `oddShiftSet d`, and `S` is sofic.

Recorded as a `def`, not proved. -/
def OddShiftSoficityStatement (d : ℕ) : Prop :=
  ∃ S : Subshift Bool d,
    S.carrier = Percolation.oddShiftSet d ∧ IsSofic S
