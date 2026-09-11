import InfoGeometry.OperatorAlgebra.KreinAdjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

structure InvolutionData (A : Type*) [Ring A] where
  sharp : A → A
  map_add' : ∀ x y, sharp (x + y) = sharp x + sharp y
  map_mul' : ∀ x y, sharp (x * y) = sharp y * sharp x
  map_one' : sharp 1 = 1
  involutive' : Function.Involutive sharp

namespace InvolutionData

instance : CoeFun (InvolutionData A) (fun _ => A → A) := ⟨InvolutionData.sharp⟩

@[simp] theorem map_add (ι : InvolutionData A) (x y : A) :
    ι (x + y) = ι x + ι y := ι.map_add' x y

@[simp] theorem map_mul (ι : InvolutionData A) (x y : A) :
    ι (x * y) = ι y * ι x := ι.map_mul' x y

@[simp] theorem map_one (ι : InvolutionData A) : ι 1 = 1 := ι.map_one'

@[simp] theorem involutive (ι : InvolutionData A) (x : A) : ι (ι x) = x := ι.involutive' x

end InvolutionData

section KreinInvolution

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]

noncomputable def kreinAdjointInvolutionData :
    InvolutionData (H →L[ℝ] H) where
  sharp := kreinAdjoint
  map_add' := by intro x y; simp [kreinAdjoint]
  map_mul' := by intro x y; simp [kreinAdjoint]
  map_one' := by
    change kreinAdjoint (H := H) (ContinuousLinearMap.id ℝ H) = ContinuousLinearMap.id ℝ H
    simp [kreinAdjoint, ContinuousLinearMap.adjoint_id]
  involutive' := by intro x; exact kreinAdjoint_involutive x

end KreinInvolution

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
