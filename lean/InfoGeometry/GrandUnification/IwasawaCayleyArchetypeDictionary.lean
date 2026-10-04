import InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition
import InfoGeometry.GrandUnification.KleinParabolicPeirceTwist
import InfoGeometry.GrandUnification.IwasawaDiracDecomposition
import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.Algebra.SplitCayleyDicksonRealBridge
import InfoGeometry.Canonical.SplitHypercomplexStructure
import InfoGeometry.Canonical.KleinNativeSemidirectProductBridge
import InfoGeometry.Canonical.KANIwasawaSplitPeirceDiracBridge
import InfoGeometry.Canonical.MasterSplitCayleyDicksonKleinDiracBridge

/-!
# Iwasawa and Split Algebra Source Index

This module unifies the Grand $KAN$ Archetypal Dictionary, mapping the Global
Topological Gauge Bridge (Klein Bottle semidirect product) and the Internal 
Algebraic Hierarchy (Cayley-Dickson, Peirce Projectors, Dirac-Kähler) into a 
single, canonical causal-chain API.
-/

namespace InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary

open Matrix
open InfoGeometry.Canonical.KANIwasawaSplitPeirceDirac
open InfoGeometry.Canonical.MasterSplitCayleyDicksonKleinDirac

/--
The Grand $KAN$ Archetype Dictionary structural API.
This binds the unipotent lightcone shifts $N$, the scale homotheties $A$, 
and the compact/spin phases $K$, alongside the split $C\ell(1,1)$ Peirce projectors.
-/
structure GrandKANArchetypeDictionary where
  -- 1. KAN Determinant Homomorphism (Trifactor map)
  k_det_unit : ∀ ω : ℝ, (matK_rot ω).det = 1
  a_det_scale : ∀ t : ℝ, (matA_boost t).det = 1
  n_det_unimodular : ∀ x : ℝ, (matN x).det = 1
  kan_factorization : ∀ (k a : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ),
    (kanProduct k a (matN x)).det = k.det * a.det

  -- 2. Trace Functional / Log-Generator mapped onto 'a'
  log_generator_a_support : ∀ ω t₁ t₂ x : ℝ,
    (mat_k_gen ω + mat_a_gen t₁ t₂ + mat_n_gen x).trace = (mat_a_gen t₁ t₂).trace

  -- 3. Cl(1,1) Split Peirce Projectors and N-Transitions (Lightcone shears)
  peirce_p_sq : P_plus * P_plus = P_plus
  peirce_m_sq : P_minus * P_minus = P_minus
  n_shear_plus : ∀ x : ℝ, P_plus * matN x * P_minus = x • e_plus
  n_shear_null : ∀ x : ℝ, P_minus * matN x * P_plus = 0

  -- 4. Parabolic / Klein Bottle Semidirect Action
  klein_semidirect_twist : affineTa.trans (affineTb.trans affineTa.symm) = affineTb.symm
  klein_parity_inverts_a : ∀ t : ℝ, matR * matA_boost t * matR = matA_boost (-t)
  klein_parity_swaps_p : matR * P_plus * matR = P_minus
  
  -- 5. Dirac-Kähler Off-Diagonal Factorization
  dirac_off_diag : ∀ d₁ d₂ : ℝ,
    matDirac d₁ d₂ = P_plus * matDirac d₁ d₂ * P_minus + P_minus * matDirac d₁ d₂ * P_plus


/--
Instantiates the canonical causal-chain API by collecting the kernel-verified
proofs from the dispersed underlying topological/algebraic engines.
-/
def makeGrandKANArchetypeDictionary : GrandKANArchetypeDictionary where
  k_det_unit := matK_rot_det
  a_det_scale := matA_boost_det
  n_det_unimodular := matN_det
  kan_factorization := kanProduct_det_of_unipotent
  log_generator_a_support := kan_trace_supported_on_a
  peirce_p_sq := P_plus_sq
  peirce_m_sq := P_minus_sq
  n_shear_plus := P_plus_matN_P_minus
  n_shear_null := P_minus_matN_P_plus
  klein_semidirect_twist := affine_klein_relation
  klein_parity_inverts_a := matR_conjugates_boost
  klein_parity_swaps_p := matR_swaps_peirce_plus
  dirac_off_diag := matDirac_off_diagonal

end InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary
