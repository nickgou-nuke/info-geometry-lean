import InfoGeometry.Canonical.InductiveClosurePacket
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
import InfoGeometry.OperatorAlgebra.SupergradedClosure

noncomputable section

namespace InfoGeometry.Canonical.CantorCellInduction

open InfoGeometry.Canonical.InductiveClosurePacket
open InfoGeometry.OperatorAlgebra.SupergradedClosure

variable (C : InductiveOperatorChain)
variable (Q Qsharp : ∀ n, C.Stage n)

 theorem global_finite_closure_stability
    (hClosure : ∀ n, SupergradedClosureAt (R := C.Stage n) (Q n) (Qsharp n))
    (n : ℕ) :
    SupergradedClosureAt (R := C.Stage n) (Q n) (Qsharp n) :=
  hClosure n

theorem local_dirac_sq_eq_laplacian
    (hClosure : ∀ n, SupergradedClosureAt (R := C.Stage n) (Q n) (Qsharp n))
    (n : ℕ) :
    (Q n + Qsharp n) * (Q n + Qsharp n) =
      Q n * Qsharp n + Qsharp n * Q n :=
  (hClosure n).1

theorem local_Q_commutes_laplacian
    (hClosure : ∀ n, SupergradedClosureAt (R := C.Stage n) (Q n) (Qsharp n))
    (n : ℕ) :
    Q n * (Q n * Qsharp n + Qsharp n * Q n) =
      (Q n * Qsharp n + Qsharp n * Q n) * Q n :=
  (hClosure n).2.1

theorem local_Qsharp_commutes_laplacian
    (hClosure : ∀ n, SupergradedClosureAt (R := C.Stage n) (Q n) (Qsharp n))
    (n : ℕ) :
    Qsharp n * (Q n * Qsharp n + Qsharp n * Q n) =
      (Q n * Qsharp n + Qsharp n * Q n) * Qsharp n :=
  (hClosure n).2.2.1

theorem local_dirac_commutes_laplacian
    (hClosure : ∀ n, SupergradedClosureAt (R := C.Stage n) (Q n) (Qsharp n))
    (n : ℕ) :
    (Q n + Qsharp n) * (Q n * Qsharp n + Qsharp n * Q n) =
      (Q n * Qsharp n + Qsharp n * Q n) * (Q n + Qsharp n) :=
  (hClosure n).2.2.2

theorem transport_laplacian
    (hQ : ∀ n, C.Bonding n (Q n) = Q (n + 1))
    (hQsharp : ∀ n, C.Bonding n (Qsharp n) = Qsharp (n + 1))
    (n : ℕ) :
    C.Bonding n (Q n * Qsharp n + Qsharp n * Q n) =
      Q (n + 1) * Qsharp (n + 1) + Qsharp (n + 1) * Q (n + 1) := by
  simp [map_add, map_mul, hQ, hQsharp]

theorem transport_Q_laplacian_product
    (hQ : ∀ n, C.Bonding n (Q n) = Q (n + 1))
    (hQsharp : ∀ n, C.Bonding n (Qsharp n) = Qsharp (n + 1))
    (n : ℕ) :
    C.Bonding n (Q n * (Q n * Qsharp n + Qsharp n * Q n)) =
      Q (n + 1) *
        (Q (n + 1) * Qsharp (n + 1) +
          Qsharp (n + 1) * Q (n + 1)) := by
  simp [map_add, map_mul, hQ, hQsharp]

theorem transport_Qsharp_laplacian_product
    (hQ : ∀ n, C.Bonding n (Q n) = Q (n + 1))
    (hQsharp : ∀ n, C.Bonding n (Qsharp n) = Qsharp (n + 1))
    (n : ℕ) :
    C.Bonding n (Qsharp n * (Q n * Qsharp n + Qsharp n * Q n)) =
      Qsharp (n + 1) *
        (Q (n + 1) * Qsharp (n + 1) +
          Qsharp (n + 1) * Q (n + 1)) := by
  simp [map_add, map_mul, hQ, hQsharp]

theorem transport_dirac_square
    (hQ : ∀ n, C.Bonding n (Q n) = Q (n + 1))
    (hQsharp : ∀ n, C.Bonding n (Qsharp n) = Qsharp (n + 1))
    (n : ℕ) :
    C.Bonding n ((Q n + Qsharp n) * (Q n + Qsharp n)) =
      (Q (n + 1) + Qsharp (n + 1)) *
        (Q (n + 1) + Qsharp (n + 1)) := by
  simp [map_add, map_mul, hQ, hQsharp]

end InfoGeometry.Canonical.CantorCellInduction
