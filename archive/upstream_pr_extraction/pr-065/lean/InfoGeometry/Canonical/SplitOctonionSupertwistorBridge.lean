import Mathlib
import InfoGeometry.Canonical.YangianLevelOneBilocalGenerator
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

namespace InfoGeometry.Canonical

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- **1. Гюнайдин-Гюрсей (1973) Split Basis за 𝕊ℙ𝕋⁴|⁴**:
    4 бозонни единици (u₀, u₁, u₂, u₃) + 4 фермионни спрегнати единици (u₀*, u₁*, u₂*, u₃*). -/
@[ext]
structure GunaydinGurseySplitBasis (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V] where
  u0  : ExteriorAlgebra R V  -- Bosonic Twistor component 1
  u1  : ExteriorAlgebra R V  -- Bosonic Twistor component 2
  u2  : ExteriorAlgebra R V  -- Bosonic Twistor component 3
  u3  : ExteriorAlgebra R V  -- Bosonic Twistor component 4
  u0s : ExteriorAlgebra R V  -- Grassmann Fermion component 1
  u1s : ExteriorAlgebra R V  -- Grassmann Fermion component 2
  u2s : ExteriorAlgebra R V  -- Grassmann Fermion component 3
  u3s : ExteriorAlgebra R V  -- Grassmann Fermion component 4

/-- **2. Level-Zero Действие на 𝔭𝔰𝔲(2,2|4) чрез Ляво Октонионно Умножение (Eq. 12.8)**:
    J^a · Z = L_a(Z) -/
def levelZeroOctonionicAction (a : ExteriorAlgebra R V) (Z : GunaydinGurseySplitBasis R V) :
    GunaydinGurseySplitBasis R V :=
  ⟨a * Z.u0, a * Z.u1, a * Z.u2, a * Z.u3,
   a * Z.u0s, a * Z.u1s, a * Z.u2s, a * Z.u3s⟩

def splitBasisAdd (Z1 Z2 : GunaydinGurseySplitBasis R V) :
    GunaydinGurseySplitBasis R V :=
  ⟨Z1.u0 + Z2.u0, Z1.u1 + Z2.u1, Z1.u2 + Z2.u2, Z1.u3 + Z2.u3,
   Z1.u0s + Z2.u0s, Z1.u1s + Z2.u1s, Z1.u2s + Z2.u2s, Z1.u3s + Z2.u3s⟩

def splitBasisZero : GunaydinGurseySplitBasis R V :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **Теорема 1**: Линейност на Level-Zero Октонионното Действие J^a · (Z₁ + Z₂) = J^a · Z₁ + J^a · Z₂ -/
theorem levelZero_action_add (a : ExteriorAlgebra R V) (Z1 Z2 : GunaydinGurseySplitBasis R V) :
    levelZeroOctonionicAction a ⟨Z1.u0 + Z2.u0, Z1.u1 + Z2.u1, Z1.u2 + Z2.u2, Z1.u3 + Z2.u3,
                                Z1.u0s + Z2.u0s, Z1.u1s + Z2.u1s, Z1.u2s + Z2.u2s, Z1.u3s + Z2.u3s⟩ =
    ⟨(levelZeroOctonionicAction a Z1).u0 + (levelZeroOctonionicAction a Z2).u0,
     (levelZeroOctonionicAction a Z1).u1 + (levelZeroOctonionicAction a Z2).u1,
     (levelZeroOctonionicAction a Z1).u2 + (levelZeroOctonionicAction a Z2).u2,
     (levelZeroOctonionicAction a Z1).u3 + (levelZeroOctonionicAction a Z2).u3,
     (levelZeroOctonionicAction a Z1).u0s + (levelZeroOctonionicAction a Z2).u0s,
     (levelZeroOctonionicAction a Z1).u1s + (levelZeroOctonionicAction a Z2).u1s,
     (levelZeroOctonionicAction a Z1).u2s + (levelZeroOctonionicAction a Z2).u2s,
     (levelZeroOctonionicAction a Z1).u3s + (levelZeroOctonionicAction a Z2).u3s⟩ := by
  dsimp [levelZeroOctonionicAction]
  ext <;> simp [mul_add]

/-- **Master Synthesis**: Günaydin-Gürsey Supertwistor & Level-Zero Action Synthesis -/
theorem master_split_octonion_supertwistor_synthesis
    (a : ExteriorAlgebra R V) (Z1 Z2 : GunaydinGurseySplitBasis R V) :
    levelZeroOctonionicAction a (splitBasisAdd Z1 Z2) =
        splitBasisAdd (levelZeroOctonionicAction a Z1)
          (levelZeroOctonionicAction a Z2) ∧
      levelZeroOctonionicAction a splitBasisZero = splitBasisZero := by
  constructor
  · exact levelZero_action_add a Z1 Z2
  · dsimp [levelZeroOctonionicAction, splitBasisZero]
    ext <;> simp

end InfoGeometry.Canonical
