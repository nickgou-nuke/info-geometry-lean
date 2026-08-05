import InfoGeometry.OperatorAlgebra.KreinAdjoint
import InfoGeometry.Algebra.CuntzSharpTangent

/-!
# Fixed-metric sharp-Cuntz structures

The involution laws are packaged independently from Cuntz data. The metric is
fixed in this layer; varying-metric tangents belong to a separate structure.
-/

namespace InfoGeometry.OperatorAlgebra

open scoped BigOperators
open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace

variable {A : Type*} [Ring A]

structure MetricSharpCuntzFamily
    {A : Type*} [Ring A] [Algebra ℝ A]
    (sharp : A → A)
    (η ηInv : Matrix (Fin N) (Fin N) ℝ) where
  S : Fin N → A
  metric_isometry : ∀ i j,
    sharp (S i) * S j = η i j • (1 : A)
  inverse_left : ηInv * η = 1
  inverse_right : η * ηInv = 1
  metric_range_sum :
    ∑ i : Fin N, ∑ j : Fin N,
      ηInv i j • (S i * sharp (S j)) = 1

structure MetricSharpCuntzTangent
    {A : Type*} [Ring A] [Algebra ℝ A]
    {sharp : A → A}
    {η ηInv : Matrix (Fin N) (Fin N) ℝ}
    (O : MetricSharpCuntzFamily (N := N) sharp η ηInv) where
  X : Fin N → A
  tangent_isometry : ∀ i j,
    sharp (X i) * O.S j + sharp (O.S i) * X j = 0
  tangent_complete :
    ∑ i : Fin N, ∑ j : Fin N,
      ηInv i j •
        (X i * sharp (O.S j) + O.S i * sharp (X j)) = 0

end InfoGeometry.OperatorAlgebra
