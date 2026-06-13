import Mathlib.Data.Matrix.Basic

namespace InfoGeometry.Topology.FibonacciFR

/--
Rigorous exact Fibonacci F/R Data structure. 
Decouples the Anyon tensor braiding mathematics from local real representations, 
serving as the algebraic witness for the modular tensor categories.
-/
structure FibonacciFRData (K : Type*) [CommRing K] where
  phi : K
  invPhi : K
  sqrtInvPhi : K
  rOne : K
  rTau : K
  phi_relation : phi * phi = phi + 1
  invPhi_def : invPhi * phi = 1
  sqrtInvPhi_sq : sqrtInvPhi * sqrtInvPhi = invPhi
  F : Matrix (Fin 2) (Fin 2) K := ![![invPhi, sqrtInvPhi], ![sqrtInvPhi, -invPhi]]
  R : Matrix (Fin 2) (Fin 2) K := ![![rOne, 0], ![0, rTau]]
  F_involutive : F * F = 1
  braid_relation :
    -- Note the convention: F⁻¹ = F since F is involutive (F_involutive)
    R * (F * R * F) * R =
    (F * R * F) * R * (F * R * F)

end InfoGeometry.Topology.FibonacciFR
