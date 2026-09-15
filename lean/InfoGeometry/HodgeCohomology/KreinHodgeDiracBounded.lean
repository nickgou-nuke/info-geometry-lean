import InfoGeometry.HodgeCohomology.KreinHodgeDirac
import InfoGeometry.Krein.KreinSpace

open scoped InnerProductSpace

namespace InfoGeometry.HodgeCohomology.KreinHodgeDiracBounded

open InfoGeometry.Krein
open KreinSpace

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable [CompleteSpace Space] [metric : KreinSpace Space]

theorem kreinBilin_nondegenerate : (kreinBilin (H := Space)).Nondegenerate := by
  constructor
  · intro state orthogonal
    have null_symmetry := orthogonal (J state)
    change ⟪J state, J state⟫_ℝ = 0 at null_symmetry
    have symmetry_zero : J state = 0 := inner_self_eq_zero.mp null_symmetry
    have recovered := congrArg (fun image : Space => J image) symmetry_zero
    simpa only [J_invol, map_zero] using recovered
  · intro state orthogonal
    have null_state := orthogonal (J state)
    change ⟪J (J state), state⟫_ℝ = 0 at null_state
    rw [J_invol] at null_state
    exact inner_self_eq_zero.mp null_state

theorem kreinBilin_symmetric : (kreinBilin (H := Space)).IsSymm :=
  ⟨fun left right => kreinInner_symm left right⟩

theorem kreinAdjoint_eq_of_pairing (operator candidate : Space →L[ℝ] Space)
    (adjunction : LinearMap.IsAdjointPair kreinBilin kreinBilin operator candidate) :
    kreinAdjoint operator = candidate := by
  apply ContinuousLinearMap.coe_injective
  have unique := KreinHodgeDirac.adjoint_unique kreinBilin kreinBilin_nondegenerate
    operator.toLinearMap (kreinAdjoint operator).toLinearMap candidate.toLinearMap
    (kreinInner_kreinAdjoint operator) adjunction
  exact unique

theorem krein_codifferential_square_zero (differential : Space →L[ℝ] Space)
    (nilpotent : differential * differential = 0) :
    kreinAdjoint differential * kreinAdjoint differential = 0 := by
  have adjoint_square := congrArg (kreinAdjoint (H := Space)) nilpotent
  simpa only [kreinAdjoint_mul, kreinAdjoint_zero] using adjoint_square

theorem krein_hodge_factorization (differential : Space →L[ℝ] Space)
    (nilpotent : differential * differential = 0) :
    (differential + kreinAdjoint differential) * (differential + kreinAdjoint differential) =
      differential * kreinAdjoint differential + kreinAdjoint differential * differential := by
  rw [add_mul, mul_add, mul_add, nilpotent,
    krein_codifferential_square_zero differential nilpotent]
  simp

theorem krein_hodge_self_adjoint (differential : Space →L[ℝ] Space) :
    IsKreinSelfAdjoint (differential + kreinAdjoint differential) := by
  change kreinAdjoint (differential + kreinAdjoint differential) = _
  rw [kreinAdjoint_add, kreinAdjoint_involutive, add_comm]

theorem krein_hodge_energy (differential : Space →L[ℝ] Space)
    (nilpotent : differential * differential = 0) (state : Space) :
    kreinInner ((differential * kreinAdjoint differential +
      kreinAdjoint differential * differential) state) state =
    kreinInner ((differential + kreinAdjoint differential) state)
      ((differential + kreinAdjoint differential) state) := by
  have nilpotent_linear : differential.toLinearMap * differential.toLinearMap = 0 :=
    congrArg ContinuousLinearMap.toLinearMap nilpotent
  exact KreinHodgeDirac.signed_hodge_dirac_energy kreinBilin kreinBilin_symmetric
    kreinBilin_nondegenerate differential.toLinearMap (kreinAdjoint differential).toLinearMap
    (kreinInner_kreinAdjoint differential) nilpotent_linear state

theorem krein_square_kernel_eq_of_commutes_symmetry (operator : Space →L[ℝ] Space)
    (self_adjoint : IsKreinSelfAdjoint operator)
    (commutes : operator * jCLM = jCLM * operator) :
    LinearMap.ker (operator.toLinearMap * operator.toLinearMap) =
      LinearMap.ker operator.toLinearMap := by
  apply KreinHodgeDirac.square_kernel_eq_of_symmetry_positive kreinBilin
    (jCLM (H := Space)).toLinearMap operator.toLinearMap
  · exact (isKreinSelfAdjoint_iff operator).mp self_adjoint
  · exact congrArg ContinuousLinearMap.toLinearMap commutes
  · intro state nonzero
    change 0 < ⟪J state, J state⟫_ℝ
    have image_nonzero : J state ≠ 0 := by
      intro image_zero
      have recovered := congrArg (fun image : Space => J image) image_zero
      exact nonzero (by simpa only [J_invol, map_zero] using recovered)
    exact real_inner_self_pos.mpr image_nonzero

theorem krein_hodge_kernel_eq_of_commutes_symmetry (differential : Space →L[ℝ] Space)
    (nilpotent : differential * differential = 0)
    (commutes : (differential + kreinAdjoint differential) * jCLM =
      jCLM * (differential + kreinAdjoint differential)) :
    LinearMap.ker (differential * kreinAdjoint differential +
      kreinAdjoint differential * differential).toLinearMap =
      LinearMap.ker (differential + kreinAdjoint differential).toLinearMap := by
  rw [← krein_hodge_factorization differential nilpotent]
  exact krein_square_kernel_eq_of_commutes_symmetry
    (differential + kreinAdjoint differential) (krein_hodge_self_adjoint differential) commutes

end InfoGeometry.HodgeCohomology.KreinHodgeDiracBounded
