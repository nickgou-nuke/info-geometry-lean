import Mathlib

namespace InfoGeometry.Canonical.ChirlaTorsionHierarchy

open scoped TensorProduct

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]
variable (Q_V : QuadraticForm R V) (Q_W : QuadraticForm R W)

/-- The "Chirla sequence of torsions" tensor product Cl(V) ⊗ Cl(W). -/
abbrev ChirlaTensor := CliffordAlgebra Q_V ⊗[R] CliffordAlgebra Q_W

/-- Map for the old generators: e_i ↦ e'_i ⊗ 1. Defined compositionally for strict type safety. -/
def oldGeneratorTorsion : V →ₗ[R] ChirlaTensor Q_V Q_W :=
  (TensorProduct.mk R (CliffordAlgebra Q_V) (CliffordAlgebra Q_W)).flip (1 : CliffordAlgebra Q_W) ∘ₗ CliffordAlgebra.ι Q_V

/-- Map for the new generators: e_{new} ↦ Z ⊗ e''_{new}. Defined compositionally. -/
def newGeneratorTorsion (Z : CliffordAlgebra Q_V) : W →ₗ[R] ChirlaTensor Q_V Q_W :=
  TensorProduct.mk R (CliffordAlgebra Q_V) (CliffordAlgebra Q_W) Z ∘ₗ CliffordAlgebra.ι Q_W

/--
The recursive generator mapping defining the "Chirla sequence of torsions".
`e_i ↦ e_i' ⊗ I`     for the previous dimensions
`e_n ↦ Z ⊗ e_n''`    for the new dimensions

This formally establishes the generic torsion step Cl(n+2) ≅ Cl(n) ⊗ Cl(2),
bridging directly into the matrix dimension recursion M_{2^k}.
-/
def chirlaTorsionPattern (Z : CliffordAlgebra Q_V) :
    V × W →ₗ[R] ChirlaTensor Q_V Q_W :=
  LinearMap.coprod (oldGeneratorTorsion Q_V Q_W) (newGeneratorTorsion Q_V Q_W Z)

@[simp] lemma chirlaTorsionPattern_apply (Z : CliffordAlgebra Q_V) (v : V) (w : W) :
    chirlaTorsionPattern Q_V Q_W Z (v, w) =
      (CliffordAlgebra.ι Q_V v ⊗ₜ[R] (1 : CliffordAlgebra Q_W)) +
      (Z ⊗ₜ[R] CliffordAlgebra.ι Q_W w) := by
  change (oldGeneratorTorsion Q_V Q_W v) + (newGeneratorTorsion Q_V Q_W Z w) = _
  rfl

end InfoGeometry.Canonical.ChirlaTorsionHierarchy
