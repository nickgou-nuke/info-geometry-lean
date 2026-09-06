import InfoGeometry.Categorical.FibonacciPentagonChannelCarrier
import InfoGeometry.Categorical.FibonacciFiveChannelAssociator

/-!
# Vertex-carrier transport of the finite Fibonacci associator

The five parenthesized vertices have separate formal channel function spaces.
This file transports the existing nontrivial `2 ⊕ 3` associator block between
those spaces through the explicit carrier equivalences.  It does not identify
the cardinality transports with canonical fusion-tree bases and does not claim
the pentagon equation.
-/

namespace InfoGeometry.Categorical.FibonacciPentagonVertexAssociator

open InfoGeometry.Categorical.FibonacciPentagonPathCarrier
open InfoGeometry.Categorical.FibonacciPentagonChannelCarrier
open InfoGeometry.Categorical.FibonacciFiveChannelAssociator
open InfoGeometry.Categorical.FibonacciFusionCategoryData

noncomputable def vertexAssociator
    (v w : PentagonVertex) (τ s : ℂ) :
    ChannelFunctions v →ₗ[ℂ] ChannelFunctions w :=
  (parenthesizedChannelCarrierEquiv w).symm.toLinearMap.comp
    ((Matrix.toLin' (fiveChannelAssociatorMatrix τ s)).comp
      (parenthesizedChannelCarrierEquiv v).toLinearMap)

theorem vertexAssociator_apply
    (v w : PentagonVertex) (τ s : ℂ) (x : ChannelFunctions v)
    (j : ChannelIndex w) :
    vertexAssociator v w τ s x j =
      Matrix.mulVec (fiveChannelAssociatorMatrix τ s)
        (parenthesizedChannelCarrierEquiv v x)
        (parenthesizedChannelEquiv w j) := by
  rfl

theorem vertexAssociator_comp_inverse
    (v w : PentagonVertex) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (vertexAssociator w v τ s).comp (vertexAssociator v w τ s) =
      LinearMap.id := by
  ext x j
  simp [vertexAssociator, LinearMap.comp_apply,
    Matrix.toLin'_mul, fiveChannelAssociatorMatrix_sq τ s hs hτ]
  rw [Equiv.symm_apply_apply]

theorem vertexAssociator_inverse_comp
    (v w : PentagonVertex) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (vertexAssociator v w τ s).comp (vertexAssociator w v τ s) =
      LinearMap.id := by
  ext x j
  simp [vertexAssociator, LinearMap.comp_apply,
    Matrix.toLin'_mul, fiveChannelAssociatorMatrix_sq τ s hs hτ]
  rw [Equiv.symm_apply_apply]

/-! The same transport written directly on the explicit unit/tau block
function spaces.  This is the formal multiplicity carrier, rather than the
noncanonical `Fin 5` presentation. -/

noncomputable def formalVertexAssociator
    (v w : PentagonVertex) (τ s : ℂ) :
    FormalChannelFunctions v →ₗ[ℂ] FormalChannelFunctions w :=
  (formalChannelCarrierEquiv w).symm.toLinearMap.comp
    ((Matrix.toLin' (fiveChannelAssociatorMatrix τ s)).comp
      (formalChannelCarrierEquiv v).toLinearMap)

theorem formalVertexAssociator_apply
    (v w : PentagonVertex) (τ s : ℂ) (x : FormalChannelFunctions v)
    (j : FormalChannelIndex w) :
    formalVertexAssociator v w τ s x j =
      Matrix.mulVec (fiveChannelAssociatorMatrix τ s)
        (formalChannelCarrierEquiv v x)
        (formalChannelBasisEquiv w j) := by
  rfl

theorem formalVertexAssociator_comp_inverse
    (v w : PentagonVertex) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (formalVertexAssociator w v τ s).comp
        (formalVertexAssociator v w τ s) = LinearMap.id := by
  ext x j
  simp [formalVertexAssociator, LinearMap.comp_apply,
    fiveChannelAssociatorMatrix_sq τ s hs hτ]
  rw [Equiv.symm_apply_apply]

theorem formalVertexAssociator_inverse_comp
    (v w : PentagonVertex) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ^ 2 + τ = 1) :
    (formalVertexAssociator v w τ s).comp
        (formalVertexAssociator w v τ s) = LinearMap.id := by
  ext x j
  simp [formalVertexAssociator, LinearMap.comp_apply,
    fiveChannelAssociatorMatrix_sq τ s hs hτ]
  rw [Equiv.symm_apply_apply]

theorem formalVertexAssociator_ne_identity
    (v : PentagonVertex) (τ s : ℂ)
    (hs : s ^ 2 = τ) (hτ : τ ≠ 0) :
    formalVertexAssociator v v τ s ≠ LinearMap.id := by
  intro h
  have hF : Matrix.toLin' (fiveChannelAssociatorMatrix τ s) =
      (LinearMap.id : PathCarrier →ₗ[ℂ] PathCarrier) := by
    apply LinearMap.ext
    intro y
    funext i
    let x := (formalChannelCarrierEquiv v).symm y
    have hx := LinearMap.congr_fun h x
    have hxy := congrArg (formalChannelCarrierEquiv v) hx
    simpa [x, formalVertexAssociator, LinearMap.comp_apply] using
      congrArg (fun z => z i) hxy
  have hmatrix : fiveChannelAssociatorMatrix τ s = 1 := by
    apply Matrix.toLin'.injective
    simpa using hF
  exact fiveChannelAssociatorMatrix_ne_one τ s hs hτ hmatrix

end InfoGeometry.Categorical.FibonacciPentagonVertexAssociator
