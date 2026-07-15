import Mathlib
import InfoGeometry.Projective.QuantumTwistorDirac
import InfoGeometry.Algebra.CuntzGNSRepresentation
import InfoGeometry.Canonical.GNSState
import InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Projective.Sandbox.QuantumTwistorDiracGNS

open GNSState
open CuntzTensorQuotient
open CuntzGNSRepresentation
open InfoGeometry.Projective.QuantumTwistorDirac

/-- Complex finite cylinder vectors on binary words. -/
abbrev CylinderVector : Type := BinaryWord →₀ ℂ

-- 1. Target Hilbert space H using gnsPreInner
noncomputable instance : SeminormedAddCommGroup CylinderVector := sorry
noncomputable instance : NormedAddCommGroup CylinderVector := sorry
noncomputable instance : NormedSpace ℂ CylinderVector := sorry

/-- Complexified pre-inner product. -/
def gnsPreInnerComplex (x y : CylinderVector) : ℂ :=
  x.sum (fun w c => star c * y w * (gnsCylinderWeight w : ℂ))

instance : InnerProductSpace ℂ CylinderVector where
  inner x y := gnsPreInnerComplex x y
  norm_sq_eq_re_inner x := sorry
  conj_inner_symm x y := sorry
  add_left x y z := sorry
  smul_left x y r := sorry

-- 2. Define the QuantumDiracOperator
-- The diagonal log-weight Hamiltonian D|n⟩ = log (n)|n⟩ over the GNS basis.
def gnsDirac : QuantumDiracOperator CylinderVector where
  inner := gnsPreInnerComplex
  domain := ⊤
  op x := x.sum (fun w c => Finsupp.single w (c * (w.length : ℂ)))

variable {q : ℂ}
variable (coordinateToCuntz : QuantumGrassmannian.coordinateRing ℂ q →ₐ[ℂ] CuntzAlg 2)
variable (cuntzAction : CuntzAlg 2 →ₐ[ℂ] (Module.End ℂ CylinderVector))

-- 3. Define the representation `rep`
def gnsRep : QuantumGrassmannian.coordinateRing ℂ q →ₐ[ℂ] (Module.End ℂ CylinderVector) :=
  cuntzAction.comp coordinateToCuntz

-- 4. State the `bounded_commutators` constraint for this explicit GNS log-Dirac setup.
def gnsSpectralTriple : QuantumSpectralTriple CylinderVector where
  rep := (gnsRep coordinateToCuntz cuntzAction).toRingHom
  D := gnsDirac
  bounded_commutators := by
    intro a
    sorry

theorem gns_bounded_commutators (a : QuantumGrassmannian.coordinateRing ℂ q) :
  ∃ (C : ℝ), ∀ (x : CylinderVector), x ∈ (gnsDirac).domain →
    ‖(gnsDirac).op ((gnsRep coordinateToCuntz cuntzAction a) x) - (gnsRep coordinateToCuntz cuntzAction a) ((gnsDirac).op x)‖ ≤ C * ‖x‖ :=
  (gnsSpectralTriple coordinateToCuntz cuntzAction).bounded_commutators a

end InfoGeometry.Projective.Sandbox.QuantumTwistorDiracGNS
