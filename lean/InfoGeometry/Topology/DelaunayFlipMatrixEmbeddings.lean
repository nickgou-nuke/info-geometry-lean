import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs

/-!
# Local two-by-two block insertion into rational matrices

This definition inserts the entries of a two-by-two block at two selected
indices and uses the identity on all other diagonal coordinates. It does not
define a braid representation or prove multiplicativity of the insertion map.
-/

namespace InfoGeometry.Topology.Delaunay

open Matrix

noncomputable def embedBlock₂ (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b : Fin d) : Matrix (Fin d) (Fin d) ℚ :=
  λ i j =>
    if i = a then
      if j = a then block 0 0
      else if j = b then block 0 1
      else 0
    else if i = b then
      if j = a then block 1 0
      else if j = b then block 1 1
      else 0
    else if i = j then 1 else 0

end InfoGeometry.Topology.Delaunay
