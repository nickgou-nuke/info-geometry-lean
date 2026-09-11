/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.BostConnesGeneratorsBridge

/-!
# Axiom Audit: Bost-Connes Generator Structure and Cuntz-Hecke Involutive Algebra

This audit verifies that the Bost-Connes generator bridge relies strictly on the
standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`) with 0 `sorry`,
0 `admit`, 0 custom axioms, and 0 proxy certificate wrappers.
-/

open InfoGeometry.Algebra.BostConnesGenerators
open InfoGeometry.Algebra.BostConnesGenerators.BostConnesStructure

-- 1. Projection Idempotence and Self-Adjointness
#print axioms P_idem
#print axioms P_star
#print axioms P_one

-- 2. Phase Unitarity and Group Representation
#print axioms e_mul_star
#print axioms star_mul_e
#print axioms e_sub

-- 3. Adjoint Covariance and Phase Compression
#print axioms covar_left
#print axioms adjoint_compression
#print axioms P_comm_e
#print axioms P_sandwich_e

-- 4. Scale Transformation Pullback and Pushforward
#print axioms scale_pullback
#print axioms scale_pushforward

-- 5. Coprime Hecke Factorization and Commutation
#print axioms coprime_factorization
#print axioms coprime_comm

-- 6. Subprojection Divisibility Absorption and Commutation
#print axioms P_mul_P_mul_right
#print axioms P_mul_right_mul_P
#print axioms P_div_comm

-- 7. Integration with Cuntz Multiplicative Indexing and LCM
#print axioms toCuntzMultiplicativeIndexing_rangeProjection
#print axioms pnatLcm_of_coprime

-- 8. Master Synthesis Conjunction
#print axioms bost_connes_generators_synthesis
