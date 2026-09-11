import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Carrier

/-- The local Triple Algebra operating on a tree node. -/
structure TripleAlgebra (A : Type*) [Ring A] where
  -- 1. Idempotents: Projectors onto occupation sectors (cylinder sets)
  P : A
  is_idempotent : P * P = P
  
  -- 2. Nilpotents: Root vectors / transition operators
  N : A
  is_nilpotent : N * N = 0
  
  -- 3. Null Channels: Lightlike transitions (often aligning with N in Clifford representations)
  L : A
  is_null : L * L = 0 

  /-- The local metric pairing. -/
  pairing : A → A → ℝ

  /-- The null channel is lightlike with respect to the pairing. -/
  pairing_null_L : pairing L L = 0

end InfoGeometry.Carrier
