import InfoGeometry.Algebra.Zorn.G2NativeLineFiber
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

/-!
# Audit candidate: zero products in the split-Zorn carrier

The old `octCross` relation is not equivariant for the native automorphism
carrier.  This file records a multiplication-based candidate only.  It does
not assert that the candidate is symmetric or that it is the split Cayley
hexagon incidence relation; those are separate finite audits.
-/

namespace InfoGeometry.Algebra.Zorn.G2ZornZeroProductIncidenceAudit

open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

def ZornZeroRelated (u v : OctImIsotropicPoint) : Prop :=
  mul (embed u.1) (embed v.1) = zero

instance : DecidableRel (fun u v : OctImIsotropicPoint => ZornZeroRelated u v) := by
  intro u v
  unfold ZornZeroRelated
  infer_instance

def zornPointAction (g : SplitOctF2Aut) (u : OctImIsotropicPoint) :
    OctImIsotropicPoint :=
  ⟨octImAction g u.1,
    octImAction_isotropic g u.1 u.2.1,
    by
      intro hzero
      apply u.2.2
      apply octImAction_injective g
      rw [hzero, octImAction_zero]⟩

instance : MulAction SplitOctF2Aut OctImIsotropicPoint where
  smul := zornPointAction
  one_smul u := by
    change zornPointAction 1 u = u
    apply Subtype.ext
    exact octImAction_one u.1
  mul_smul g h u := by
    change zornPointAction (g * h) u = zornPointAction g (zornPointAction h u)
    apply Subtype.ext
    exact octImAction_mul g h u.1

theorem zornZeroRelated_aut_iff
    (g : SplitOctF2Aut) (u v : OctImIsotropicPoint) :
    ZornZeroRelated (zornPointAction g u) (zornPointAction g v) ↔
      ZornZeroRelated u v := by
  exact native_multiplication_zero_iff g u.1 v.1

theorem zornZeroRelated_smul_iff
    (g : SplitOctF2Aut) (u v : OctImIsotropicPoint) :
    ZornZeroRelated (g • u) (g • v) ↔ ZornZeroRelated u v := by
  exact zornZeroRelated_aut_iff g u v

def zornZeroNeighbourSet (u : OctImIsotropicPoint) :
    Finset OctImIsotropicPoint :=
  Finset.univ.filter (fun v => ZornZeroRelated u v)

theorem mem_zornZeroNeighbourSet_smul_iff
    (g : SplitOctF2Aut) (u v : OctImIsotropicPoint) :
    v ∈ zornZeroNeighbourSet (g • u) ↔
      g⁻¹ • v ∈ zornZeroNeighbourSet u := by
  simp only [zornZeroNeighbourSet, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro hv
    have hrel :
        ZornZeroRelated (g • u) (g • (g⁻¹ • v)) := by
      simpa [smul_smul] using hv
    exact (zornZeroRelated_smul_iff g u (g⁻¹ • v)).mp hrel
  · intro hv
    have hrel := (zornZeroRelated_smul_iff g u (g⁻¹ • v)).mpr hv
    simpa [smul_smul] using hrel

def zornZeroNeighbourEquiv
    (g : SplitOctF2Aut) (u : OctImIsotropicPoint) :
    {v // v ∈ zornZeroNeighbourSet u} ≃
      {v // v ∈ zornZeroNeighbourSet (g • u)} where
  toFun v := ⟨g • v.1, by
    have hv : ZornZeroRelated u v.1 :=
      (Finset.mem_filter.mp v.2).2
    have hrel := (zornZeroRelated_smul_iff g u v.1).mpr hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel⟩⟩
  invFun v := ⟨g⁻¹ • v.1, by
    have hv : v.1 ∈ zornZeroNeighbourSet (g • u) := v.2
    have h := (mem_zornZeroNeighbourSet_smul_iff g u v.1).mp hv
    exact h⟩
  left_inv v := by
    apply Subtype.ext
    simp [smul_smul]
  right_inv v := by
    apply Subtype.ext
    simp [smul_smul]

theorem zornZeroNeighbourSet_subtype_card_invariant
    (g : SplitOctF2Aut) (u : OctImIsotropicPoint) :
    Fintype.card {v // v ∈ zornZeroNeighbourSet u} =
      Fintype.card {v // v ∈ zornZeroNeighbourSet (g • u)} := by
  exact Fintype.card_congr (zornZeroNeighbourEquiv g u)

end InfoGeometry.Algebra.Zorn.G2ZornZeroProductIncidenceAudit
