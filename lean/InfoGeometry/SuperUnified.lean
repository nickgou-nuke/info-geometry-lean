import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Submodule
import InfoGeometry.Clifford.Cl11
import InfoGeometry.Clifford.Grading
import InfoGeometry.Krein.Metric
import InfoGeometry.Core.UnifiedGeometry
import InfoGeometry.Jordan.Core

/-!
# The Super-Kähler Geometry of Information

Clifford-style endomorphism algebra on `DoubledSpace E` viewed through:
- Lie (antisymmetric) part
- Jordan (symmetric) part
- `ℤ₂` boson/fermion grading relative to an involution.
-/

namespace InfoGeometry.SuperUnified

open InfoGeometry.Jordan
open InfoGeometry.Core

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

section SuperAlgebra

/-- Endomorphisms on the doubled space. -/
abbrev End (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/-- Super-commutator / Lie bracket. -/
def lieBracket (A B : End E) : End E :=
  A.comp B - B.comp A

/-- Super-anticommutator / Jordan product. -/
noncomputable def jordanProduct (A B : End E) : End E :=
  (2 : ℝ)⁻¹ • (A.comp B + B.comp A)

/-- Clifford decomposition `AB = {A,B} + (1/2)[A,B]`. -/
theorem clifford_decomposition (A B : End E) :
    A.comp B = jordanProduct A B + (2 : ℝ)⁻¹ • lieBracket A B := by
  simpa [jordanProduct, lieBracket, jordanProd, clmComm] using
    (comp_eq_jordan_add_half_comm (E := E) A B)

end SuperAlgebra

section SuperKaehlerGeometry

/-- Super-Kähler package from an involutive anticommuting pair (`J^2 = +Id` in this split/Krein model). -/
structure SuperKaehlerStructure where
  J : End E
  epsilon : End E
  J_sq : J.comp J = ContinuousLinearMap.id ℝ (DoubledSpace E)
  eps_sq : epsilon.comp epsilon = ContinuousLinearMap.id ℝ (DoubledSpace E)
  anticomm : J.comp epsilon = -(epsilon.comp J)

variable (S : SuperKaehlerStructure (E := E))

/-- Commutator-generated symplectic operator. -/
noncomputable def symplecticFormOp : End E :=
  lieBracket S.J S.epsilon

/-- Jordan-square metric operator. -/
noncomputable def metricOp : End E :=
  jordanProduct S.epsilon S.epsilon

/-- Supercharge square equals Hamiltonian identity. -/
theorem supercharge_squared_is_hamiltonian :
    S.epsilon.comp S.epsilon = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  S.eps_sq

/-- Commutator closes to `2 * (J ∘ ε)`. -/
theorem symplectic_is_complex_structure :
    symplecticFormOp S = (2 : ℝ) • (S.J.comp S.epsilon) := by
  have hεJ : S.epsilon.comp S.J = -(S.J.comp S.epsilon) := by
    have h := congrArg (fun T => -T) S.anticomm
    simpa using h.symm
  unfold symplecticFormOp lieBracket
  calc
    S.J.comp S.epsilon - S.epsilon.comp S.J
        = S.J.comp S.epsilon - (-(S.J.comp S.epsilon)) := by rw [hεJ]
    _ = (2 : ℝ) • (S.J.comp S.epsilon) := by
        simp [sub_eq_add_neg, two_smul]

end SuperKaehlerGeometry

section BosonFermionSplit

/-- Bosons commute with the grading involution. -/
def IsBosonic (J : End E) (A : End E) : Prop :=
  J.comp A = A.comp J

/-- Fermions anticommute with the grading involution. -/
def IsFermionic (J : End E) (A : End E) : Prop :=
  J.comp A = -(A.comp J)

/-- `epsilon` is fermionic by anticommutation. -/
theorem epsilon_is_fermionic (S : SuperKaehlerStructure (E := E)) :
    IsFermionic S.J S.epsilon :=
  S.anticomm

/-- Square of a fermion is bosonic. -/
theorem hamiltonian_is_bosonic (S : SuperKaehlerStructure (E := E)) :
    IsBosonic S.J (S.epsilon.comp S.epsilon) := by
  unfold IsBosonic
  rw [S.eps_sq]
  simp

end BosonFermionSplit

section KKT_Construction

theorem bracket_boson_boson_is_bosonic
    (S : SuperKaehlerStructure (E := E))
    {A B : End E}
    (hA : IsBosonic S.J A)
    (hB : IsBosonic S.J B) :
    IsBosonic S.J (lieBracket A B) := by
  unfold IsBosonic lieBracket at *
  calc
    S.J.comp (A.comp B - B.comp A)
        = S.J.comp (A.comp B) - S.J.comp (B.comp A) := by
            simp [ContinuousLinearMap.comp_sub]
    _ = (S.J.comp A).comp B - (S.J.comp B).comp A := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (A.comp S.J).comp B - (B.comp S.J).comp A := by
          rw [hA, hB]
    _ = A.comp (S.J.comp B) - B.comp (S.J.comp A) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = A.comp (B.comp S.J) - B.comp (A.comp S.J) := by
          rw [hB, hA]
    _ = (A.comp B).comp S.J - (B.comp A).comp S.J := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (A.comp B - B.comp A).comp S.J := by
          simp [ContinuousLinearMap.sub_comp]

/-- Even (`bosonic`) structure subalgebra. -/
def StructureGroupLieAlgebra (S : SuperKaehlerStructure (E := E)) :
    LieSubalgebra ℝ (End E) where
  carrier := {A | IsBosonic S.J A}
  zero_mem' := by
    simp [IsBosonic]
  add_mem' := by
    intro A B hA hB
    unfold IsBosonic at *
    calc
      S.J.comp (A + B) = S.J.comp A + S.J.comp B := by
        simp [ContinuousLinearMap.comp_add]
      _ = A.comp S.J + B.comp S.J := by rw [hA, hB]
      _ = (A + B).comp S.J := by
        simp [ContinuousLinearMap.add_comp]
  smul_mem' := by
    intro r A hA
    unfold IsBosonic at *
    calc
      S.J.comp (r • A) = r • (S.J.comp A) := by simp
      _ = r • (A.comp S.J) := by rw [hA]
      _ = (r • A).comp S.J := by simp [ContinuousLinearMap.smul_comp]
  lie_mem' := by
    intro A B hA hB
    change IsBosonic S.J (A * B - B * A)
    simpa [lieBracket] using
      (bracket_boson_boson_is_bosonic (S := S) hA hB)

/-- Odd (`fermionic`) linear subspace. -/
def SuperchargeSpace (S : SuperKaehlerStructure (E := E)) :
    Submodule ℝ (End E) where
  carrier := {A | IsFermionic S.J A}
  zero_mem' := by
    simp [IsFermionic]
  add_mem' := by
    intro A B hA hB
    unfold IsFermionic at *
    calc
      S.J.comp (A + B) = S.J.comp A + S.J.comp B := by
        simp [ContinuousLinearMap.comp_add]
      _ = -(A.comp S.J) + -(B.comp S.J) := by rw [hA, hB]
      _ = -((A.comp S.J) + (B.comp S.J)) := by
        simp [add_comm]
      _ = -((A + B).comp S.J) := by
        simp [ContinuousLinearMap.add_comp]
  smul_mem' := by
    intro r A hA
    unfold IsFermionic at *
    calc
      S.J.comp (r • A) = r • (S.J.comp A) := by simp
      _ = r • (-(A.comp S.J)) := by rw [hA]
      _ = -((r • A).comp S.J) := by simp [ContinuousLinearMap.smul_comp]

/-- KKT `ℤ`-grading rule: `[odd, odd] ⊆ even`. -/
theorem bracket_fermion_fermion_is_bosonic
    (S : SuperKaehlerStructure (E := E))
    {A B : End E}
    (hA : IsFermionic S.J A)
    (hB : IsFermionic S.J B) :
    IsBosonic S.J (lieBracket A B) := by
  unfold IsBosonic IsFermionic lieBracket at *
  calc
    S.J.comp (A.comp B - B.comp A)
        = S.J.comp (A.comp B) - S.J.comp (B.comp A) := by
            simp [ContinuousLinearMap.comp_sub]
    _ = (S.J.comp A).comp B - (S.J.comp B).comp A := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (-(A.comp S.J)).comp B - (-(B.comp S.J)).comp A := by
          rw [hA, hB]
    _ = -((A.comp S.J).comp B) + (B.comp S.J).comp A := by
          simp
    _ = -(A.comp (S.J.comp B)) + B.comp (S.J.comp A) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -(A.comp (-(B.comp S.J))) + B.comp (-(A.comp S.J)) := by
          rw [hB, hA]
    _ = A.comp (B.comp S.J) - B.comp (A.comp S.J) := by
          simp [sub_eq_add_neg]
    _ = (A.comp B).comp S.J - (B.comp A).comp S.J := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (A.comp B - B.comp A).comp S.J := by
          simp [ContinuousLinearMap.sub_comp]

/-- KKT `ℤ`-grading rule: `[even, odd] ⊆ odd`. -/
theorem bracket_boson_fermion_is_fermionic
    (S : SuperKaehlerStructure (E := E))
    {A B : End E}
    (hA : IsBosonic S.J A)
    (hB : IsFermionic S.J B) :
    IsFermionic S.J (lieBracket A B) := by
  unfold IsBosonic IsFermionic lieBracket at *
  calc
    S.J.comp (A.comp B - B.comp A)
        = S.J.comp (A.comp B) - S.J.comp (B.comp A) := by
            simp [ContinuousLinearMap.comp_sub]
    _ = (S.J.comp A).comp B - (S.J.comp B).comp A := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (A.comp S.J).comp B - (-(B.comp S.J)).comp A := by
          rw [hA, hB]
    _ = A.comp (-(B.comp S.J)) + B.comp (A.comp S.J) := by
          simp [ContinuousLinearMap.comp_assoc, hA, hB]
    _ = -(A.comp (B.comp S.J)) + B.comp (A.comp S.J) := by
          simp
    _ = -((A.comp B).comp S.J) + (B.comp A).comp S.J := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -((A.comp B - B.comp A).comp S.J) := by
          simp [sub_eq_add_neg, add_comm]

end KKT_Construction

end InfoGeometry.SuperUnified
