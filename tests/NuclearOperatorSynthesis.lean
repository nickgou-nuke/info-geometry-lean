/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentParity
import InfoGeometry.OperatorAlgebra.PeirceSpine.SupercolorTripotentParity
import InfoGeometry.Core.TripotentChiralRestriction
import InfoGeometry.Physics.OperatorRPABlock
import InfoGeometry.Physics.NuclearPhononOperatorWeights
import InfoGeometry.Physics.NuclearFiveGradeParity
import InfoGeometry.Core.SupercolorMatrixUnitBridge
import InfoGeometry.Core.SupercolorSourceClosure
import InfoGeometry.Core.TripotentEigenspaces
import InfoGeometry.Physics.Cl55SpinorCartanFock
import InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom

/-!
# Integration of the nuclear operator and parity synthesis

This entry point checks the new theorem interfaces together with the native
matrix-unit, adjoint-eigenspace, CAR, spin/isospin, and common-carrier owners.
It introduces no replacement structures or theorem aliases. The construction
dependencies and carrier distinctions are recorded in the accompanying map.
The independently generated acceptance sources check every new declaration's
signature and transitive axioms separately.
-/

-- Common-source matrix units, the two-color tetraktys, and its tripotent.
#check InfoGeometry.Core.SuperGrassmannianSusy.colorBoson_mul_of_common_source
#check InfoGeometry.Core.SupercolorMatrixUnitBridge.colorEmbeddingHom
#check InfoGeometry.Core.SupercolorMatrixUnitBridge.colorEmbedding_injective
#check InfoGeometry.OperatorAlgebra.PeirceSpine.supercolor_tetraktys_corners
#check InfoGeometry.OperatorAlgebra.PeirceSpine.supercolor_tetraktys_mass
#check InfoGeometry.OperatorAlgebra.PeirceSpine.supercolor_tetraktys_spin
#check InfoGeometry.OperatorAlgebra.PeirceSpine.supercolor_fiveGrade_parity

-- Five actual eigenspaces, their parity coarsening, and the tangent equation.
#check InfoGeometry.Core.TripotentAdjoint.fiveGradeRange_eq_eigenspace
#check InfoGeometry.OperatorAlgebra.PeirceSpine.oddGrade_projZero
#check InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade_projZero
#check InfoGeometry.OperatorAlgebra.PeirceSpine.parityConj_projZero_of_mem_fiveGradeRange
#check InfoGeometry.OperatorAlgebra.PeirceSpine.isGrassmannianTangent_iff_oddGrades_fixed

-- Derive total block parity from the native grade memberships.
#check InfoGeometry.Physics.NuclearOperatorSuperSoloviev.invariant_of_even_diagonal_odd_offDiagonal
#check InfoGeometry.Physics.NuclearInternalExternalParityFactorization.parity_factorization_packet
#check InfoGeometry.Physics.NuclearFiveGradeParity.totalParity_invariant_of_fiveGrade
#check InfoGeometry.Physics.NuclearFiveGradeParity.totalParity_invariant_projected_block
#check InfoGeometry.Physics.NuclearFiveGradeParity.PeirceCompatibleBlock.totalParity_invariant

-- Signed RPA blocks retain the noncommuting coefficients and ordered squares.
#check InfoGeometry.Physics.OperatorRPABlock.rpa_square
#check InfoGeometry.Physics.OperatorRPABlock.hadamard_intertwines_rpa
#check InfoGeometry.Physics.OperatorRPABlock.ordered_rpa_products
#check InfoGeometry.Physics.OperatorRPABlock.hadamard_intertwines_rpa_square

-- Operator-weighted phonon dynamics and exact conservation.
#check InfoGeometry.Physics.NuclearPhononRPA.PhononRPA.comm_numberOp_Qdag_same
#check InfoGeometry.Physics.NuclearPhononRPA.PhononRPA.comm_operatorWeightedHamiltonian
#check InfoGeometry.Physics.NuclearPhononRPA.PhononRPA.comm_operatorWeightedHamiltonian_Qdag
#check InfoGeometry.Physics.NuclearPhononRPA.PhononRPA.operatorWeightedHamiltonian_commute_iff

-- An explicit anticommuting involution restricts to the actual kernel.
#check InfoGeometry.Physics.Algebra.zeroModeCommutantRestriction
#check InfoGeometry.Physics.Algebra.anticommute_endProjPos
#check InfoGeometry.Physics.Algebra.anticommute_endProjNeg
#check InfoGeometry.Physics.Algebra.zeroModeChiralEquiv

-- Concrete operator observables and the separately constructed carrier maps.
#check InfoGeometry.Physics.Cl55SpinorCartanFock.five_graded_isospin_and_pairing_grades
#check InfoGeometry.Physics.Cl55SpinorCartanFock.casimir_partition_of_three_one
#check InfoGeometry.Physics.Cl55SpinorCartanFock.pin_majorana_conjugates_isospin_to_pairing
#check InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.spin_isospin_actions_commute
#check InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom.commonRepresentationLieHom
