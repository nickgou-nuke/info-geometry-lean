import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.SupergradedBracket
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Data.ZMod.Basic
import InfoGeometry.Clifford.SplitClifford55ExteriorDegrees
import InfoGeometry.Clifford.SplitClifford55ExteriorFiniteGraded
import InfoGeometry.Clifford.ParaKahler55SUSYClosure
import InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge
import InfoGeometry.Clifford.Cl55CARSpinAutomorphism
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv
import InfoGeometry.Clifford.Cl55OperatorFiveGradeClosure
import InfoGeometry.Canonical.PositiveGrassmannianAmplituhedron
import InfoGeometry.Projective.ExteriorPowerPluckerBridge

noncomputable section
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Krein
open KreinSpace
open InfoGeometry.Algebra.SupergradedBracket
open ExteriorAlgebra
open CliffordAlgebra
open InfoGeometry.Clifford.SplitClifford55ExteriorDegrees

namespace InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure

/-! ### 1. The cyclic five-grading on the exterior spinor -/

abbrev Exterior55 := ExteriorAlgebra ℝ (Fin 5 → ℝ)

abbrev Exterior55Degree (d : Fin 6) : Type :=
  ⋀[ℝ]^(d : ℕ) (Fin 5 → ℝ)

abbrev Exterior55Graded := DirectSum (Fin 6) Exterior55Degree

/-- The degree index, reduced modulo five.  The degree-zero sector therefore
    contains both exterior degrees zero and five, as required by cyclic grading. -/
def grade5 (d : Fin 6) : ZMod 5 := d.val

@[simp] theorem grade5_zero : grade5 (0 : Fin 6) = 0 := by
  rfl

@[simp] theorem grade5_top : grade5 (5 : Fin 6) = 0 := by
  decide

noncomputable def exterior55GradedEquiv :
    Exterior55 ≃ₗ[ℝ] Exterior55Graded := by
  exact InfoGeometry.Clifford.SplitClifford55ExteriorDegrees.exteriorAlgebraFiniteGradedEquiv

/-- The homogeneous generators of cyclic degree `k`, assembled from the native
    Mathlib exterior-power decomposition. -/
def fiveGradedGenerators (k : ZMod 5) : Set Exterior55 :=
  {x | ∃ (d : Fin 6) (u : Exterior55Degree d),
    grade5 d = k ∧
      exterior55GradedEquiv x = DirectSum.of Exterior55Degree d u}

/-- The degree-`k` cyclic component is the span of all exterior-homogeneous
    components whose degree is congruent to `k` modulo five. -/
def fiveGradedPiece (k : ZMod 5) : Submodule ℝ Exterior55 :=
  Submodule.span ℝ (fiveGradedGenerators k)

theorem exterior55_homogeneous_mem_fiveGradedPiece
    (d : Fin 6) (u : Exterior55Degree d) :
    (exterior55GradedEquiv).symm (DirectSum.of Exterior55Degree d u) ∈
      fiveGradedPiece (grade5 d) := by
  apply Submodule.subset_span
  exact ⟨d, u, rfl, by simp⟩

/-! ### 2. The isotropic exterior-algebra map into Cl(5,5) -/

/-- The diagonal copy of the five-dimensional space is totally isotropic for
    `Q55`, so its Clifford generators satisfy the exterior square-zero relation. -/
def diagonalNull55 : (Fin 5 → ℝ) →ₗ[ℝ] V55 where
  toFun v := (v, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def twistorGeneratorMap : (Fin 5 → ℝ) →ₗ[ℝ] Cl55 :=
  ι55.comp diagonalNull55

theorem twistorGeneratorMap_sq_zero (v : Fin 5 → ℝ) :
    twistorGeneratorMap v * twistorGeneratorMap v = 0 := by
  change ι55 (diagonalNull55 v) * ι55 (diagonalNull55 v) = 0
  rw [CliffordAlgebra.ι_sq_scalar]
  simp [diagonalNull55, Q55_apply]

/-- The algebra homomorphism is obtained from Mathlib's universal property of
    the exterior algebra, using the five diagonal null generators in `Cl55`. -/
noncomputable def twistorMapAlgHom : Exterior55 →ₐ[ℝ] Cl55 :=
  ExteriorAlgebra.lift ℝ ⟨twistorGeneratorMap, twistorGeneratorMap_sq_zero⟩

/-- The induced linear map from the exterior algebra to the Clifford algebra.
    It is called a map rather than an embedding because injectivity is not
    asserted here. -/
noncomputable def twistorMap : Exterior55 →ₗ[ℝ] Cl55 :=
  twistorMapAlgHom.toLinearMap

@[simp] theorem twistorMap_ι (v : Fin 5 → ℝ) :
    twistorMap (ExteriorAlgebra.ι ℝ v) = ι55 (diagonalNull55 v) := by
  simp [twistorMap, twistorMapAlgHom, twistorGeneratorMap]

/-! ### 2a. Positive Grassmannian blades in the spinor representation -/

open InfoGeometry.Canonical
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge

/-- Coordinate order `(t,x,y,z)` for the four columns of the finite chart. -/
def grassmannianI4Index : I4 → Fin 4
  | .t => 0
  | .x => 1
  | .y => 2
  | .z => 3

/-- A row of a two-plane representative, in the Plücker coordinate order. -/
def grassmannianRow4 (C : Matrix (Fin 2) (Fin 4) ℝ) (i : Fin 2) : Vec4 :=
  fun j => C i (grassmannianI4Index j)

/-- The six Plücker coordinates of the oriented row plane. -/
def grassmannianPlucker (C : Matrix (Fin 2) (Fin 4) ℝ) :
    InfoGeometry.Algebra.FiniteSpin.Vec6R :=
  pluckerCoords (grassmannianRow4 C 0) (grassmannianRow4 C 1)

/-- Ordered column pairs corresponding to the six coordinates of `Vec6R`. -/
def grassmannianMinorSelector (k : Fin 6) : Fin 2 → Fin 4 := fun j =>
  if k = 0 then if j = 0 then 0 else 1
  else if k = 1 then if j = 0 then 0 else 2
  else if k = 2 then if j = 0 then 0 else 3
  else if k = 3 then if j = 0 then 1 else 2
  else if k = 4 then if j = 0 then 1 else 3
  else if j = 0 then 2 else 3

private theorem grassmannianMinor_det_formula
    (C : Matrix (Fin 2) (Fin 4) ℝ) (a b : Fin 4) :
    Matrix.det (fun i j : Fin 2 => C i (if j = 0 then a else b)) =
      C 0 a * C 1 b - C 0 b * C 1 a := by
  let M : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => C i (if j = 0 then a else b)
  change M.det = C 0 a * C 1 b - C 0 b * C 1 a
  rw [Matrix.det_fin_two]
  simp [M]

theorem grassmannianPlucker_eq_maximalMinor
    (C : Matrix (Fin 2) (Fin 4) ℝ) (k : Fin 6) :
    grassmannianPlucker C k =
      maximalMinor C (grassmannianMinorSelector k) := by
  fin_cases k <;>
    simp [grassmannianPlucker, grassmannianRow4, grassmannianI4Index,
      grassmannianMinorSelector, pluckerCoords, maximalMinor,
      grassmannianMinor_det_formula]

theorem grassmannianMinorSelector_strictMono (k : Fin 6) :
    StrictMono (grassmannianMinorSelector k) := by
  intro i j hij
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp_all [grassmannianMinorSelector]

/-- Every Plücker coordinate of a strictly positive chart is strictly positive. -/
theorem positiveChart_grassmannianPlucker_pos
    (C : Matrix (Fin 2) (Fin 4) ℝ)
    (hC : HasPositiveMaximalMinors C) (k : Fin 6) :
    0 < grassmannianPlucker C k := by
  rw [grassmannianPlucker_eq_maximalMinor]
  exact hC (grassmannianMinorSelector k)
    (grassmannianMinorSelector_strictMono k)

/-- Embed the chart rows into the first four modes of the five-mode exterior
spinor; the fifth mode is zero. -/
def grassmannianRow55 (C : Matrix (Fin 2) (Fin 4) ℝ) (i : Fin 2) :
    Fin 5 → ℝ := fun j =>
  if hj : j.val < 4 then C i ⟨j.val, hj⟩ else 0

/-- The exterior-algebra blade representing the chart's oriented two-plane. -/
def positiveGrassmannianBlade (C : Matrix (Fin 2) (Fin 4) ℝ) : Exterior55 :=
  ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0) *
    ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1)

/-- The existing isotropic Clifford map followed by the spinor algebra
equivalence gives a concrete representation of the exterior algebra. -/
noncomputable def twistorSpinorRepresentation : Exterior55 →ₐ[ℝ]
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  cl55SpinorAlgEquiv.toAlgHom.comp twistorMapAlgHom

theorem twistorSpinorRepresentation_positiveGrassmannianBlade
    (C : Matrix (Fin 2) (Fin 4) ℝ) :
    twistorSpinorRepresentation (positiveGrassmannianBlade C) =
      twistorSpinorRepresentation (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 0)) *
      twistorSpinorRepresentation (ExteriorAlgebra.ι ℝ (grassmannianRow55 C 1)) := by
  simp [positiveGrassmannianBlade, twistorSpinorRepresentation]

theorem twistorSpinorRepresentation_generator_sq_zero (v : Fin 5 → ℝ) :
    twistorSpinorRepresentation (ExteriorAlgebra.ι ℝ v) *
      twistorSpinorRepresentation (ExteriorAlgebra.ι ℝ v) = 0 := by
  have hι : twistorSpinorRepresentation (ExteriorAlgebra.ι ℝ v) =
      cl55SpinorAlgEquiv (twistorGeneratorMap v) := by
    change cl55SpinorAlgEquiv (twistorMap (ExteriorAlgebra.ι ℝ v)) = _
    rw [twistorMap_ι]
    rfl
  rw [hι]
  calc
    cl55SpinorAlgEquiv (twistorGeneratorMap v) *
        cl55SpinorAlgEquiv (twistorGeneratorMap v) =
        cl55SpinorAlgEquiv
          (twistorGeneratorMap v * twistorGeneratorMap v) := by rw [map_mul]
    _ = 0 := by rw [twistorGeneratorMap_sq_zero, map_zero]

theorem twistorMap_superBracket (px py : Bool) (x y : Exterior55) :
    twistorMapAlgHom
        (InfoGeometry.Algebra.SupergradedBracket.superBracket px py x y) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket px py
        (twistorMapAlgHom x) (twistorMapAlgHom y) := by
  exact InfoGeometry.Algebra.SupergradedBracket.map_superBracket
    twistorMapAlgHom.toRingHom px py x y

theorem twistorSpinorRepresentation_superBracket
    (px py : Bool) (x y : Exterior55) :
    twistorSpinorRepresentation
        (InfoGeometry.Algebra.SupergradedBracket.superBracket px py x y) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket px py
        (twistorSpinorRepresentation x) (twistorSpinorRepresentation y) := by
  exact InfoGeometry.Algebra.SupergradedBracket.map_superBracket
    twistorSpinorRepresentation.toRingHom px py x y

/-- Nested parity-controlled brackets form the represented graded triple
product, and the exterior-to-spinor representation preserves it. -/
theorem twistorSpinorRepresentation_superTriple
    (px py pz : Bool) (x y z : Exterior55) :
    twistorSpinorRepresentation
        (InfoGeometry.Algebra.SupergradedBracket.superBracket px py x
          (InfoGeometry.Algebra.SupergradedBracket.superBracket py pz y z)) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket px py
        (twistorSpinorRepresentation x)
        (InfoGeometry.Algebra.SupergradedBracket.superBracket py pz
          (twistorSpinorRepresentation y) (twistorSpinorRepresentation z)) := by
  rw [twistorSpinorRepresentation_superBracket, twistorSpinorRepresentation_superBracket]

/-- The represented Clifford associator is the image of the abstract
associator, and hence vanishes in the associative spinor matrix algebra. -/
theorem spinorRepresentation_cl55_associator_zero (x y z : Cl55) :
    (cl55SpinorAlgEquiv x * cl55SpinorAlgEquiv y) * cl55SpinorAlgEquiv z -
      cl55SpinorAlgEquiv x *
        (cl55SpinorAlgEquiv y * cl55SpinorAlgEquiv z) = 0 := by
  have h := congrArg cl55SpinorAlgEquiv (cl55_associator_zero x y z)
  simpa only [cl55Associator, map_sub, map_mul, map_zero] using h

/-- Annihilation and creation generators in the spinor representation. -/
def spinorAnnihilation55 (i : Fin 5) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  cl55SpinorAlgEquiv (annihilation55 i)

def spinorCreation55 (i : Fin 5) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  cl55SpinorAlgEquiv (creation55 i)

/-- The spinor matrix representation satisfies the same-site CAR
anticommutator `{aᵢ, aᵢ†} = 1`. -/
theorem spinorCAR_same_site (i : Fin 5) :
    spinorAnnihilation55 i * spinorCreation55 i +
      spinorCreation55 i * spinorAnnihilation55 i = 1 := by
  have h := congrArg cl55SpinorAlgEquiv
    (annihilation55_creation55_anticommutator i)
  simpa only [spinorAnnihilation55, spinorCreation55, map_add, map_mul, map_one] using h

/-- The five-mode mixed CAR relation in the represented algebra, including
vanishing off-diagonal anticommutators. -/
theorem spinorCAR_mixed_sites (i j : Fin 5) :
    spinorAnnihilation55 i * spinorCreation55 j +
      spinorCreation55 j * spinorAnnihilation55 i = if i = j then 1 else 0 := by
  have h := congrArg cl55SpinorAlgEquiv
    (annihilation55_creation55_anticommutator_eq i j)
  by_cases hij : i = j
  · subst j
    simpa [spinorAnnihilation55, spinorCreation55, map_add, map_mul,
      map_one, map_zero] using h
  · simpa [hij, spinorAnnihilation55, spinorCreation55, map_add, map_mul,
      map_one, map_zero] using h

/-- Annihilation generators anticommute in the represented spinor matrix
algebra, for every pair of modes. -/
theorem spinorCAR_annihilation_anticommutator (i j : Fin 5) :
    spinorAnnihilation55 i * spinorAnnihilation55 j +
      spinorAnnihilation55 j * spinorAnnihilation55 i = 0 := by
  have h := congrArg cl55SpinorAlgEquiv (annihilation55_anticommutator i j)
  simpa only [spinorAnnihilation55, map_add, map_mul, map_zero] using h

/-- Creation generators anticommute in the represented spinor matrix
algebra, for every pair of modes. -/
theorem spinorCAR_creation_anticommutator (i j : Fin 5) :
    spinorCreation55 i * spinorCreation55 j +
      spinorCreation55 j * spinorCreation55 i = 0 := by
  have h := congrArg cl55SpinorAlgEquiv (creation55_anticommutator i j)
  simpa only [spinorCreation55, map_add, map_mul, map_zero] using h

/-! ### 3. The induced five-grading on the embedded subalgebra -/

/-- The five-graded piece in `Cl55` is the image of the corresponding exterior
    component.  This defines a grading only on the isotropic exterior image;
    the full Clifford algebra has its native `ZMod 2` grading. -/
def fiveGradedClPiece (k : ZMod 5) : Submodule ℝ Cl55 :=
  Submodule.map twistorMap (fiveGradedPiece k)

theorem twistorMap_mem_fiveGradedClPiece
    {k : ZMod 5} {x : Exterior55} (hx : x ∈ fiveGradedPiece k) :
    twistorMap x ∈ fiveGradedClPiece k := by
    exact ⟨x, hx, rfl⟩

/-! ### 4. 5-graded SUSY symmetry -/

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]
abbrev EndH₂ := DoubledSpace E →L[ℝ] DoubledSpace E

/-- A symmetry of the para-Kähler 5-graded SUSY system.

    `toCLM` is a Krein-isometry on the doubled carrier.
    `commutes_paraKahler` intertwines the para-Kähler generator swap.
    The five-grading belongs to the isotropic exterior image and is not
    asserted to be a grading of the full nonzero-quadratic Clifford algebra. -/
structure ParaKahler55KreinSymmetry where
  /-- The underlying continuous linear map on the doubled carrier. -/
  toCLM : DoubledSpace E →L[ℝ] DoubledSpace E
  /-- Krein isometry. -/
  isKreinIsometry : IsKreinIsometry (H := DoubledSpace E) toCLM
  /-- Commutes with the para-Kähler swap on generators. -/
  commutes_paraKahler (ρ : Cl55 →+* (DoubledSpace E →L[ℝ] DoubledSpace E)) (v : V55) :
    toCLM.comp (ρ (CliffordAlgebra.ι Q55 (ParaKahler55SUSYClosure.paraKahlerK v))) =
      (ρ (CliffordAlgebra.ι Q55 (ParaKahler55SUSYClosure.paraKahlerK v))).comp toCLM

/-! ### 5. Identity and closure under composition -/

/-- The identity 5-graded SUSY symmetry. -/
noncomputable def idKreinSym : ParaKahler55KreinSymmetry (E := E) :=
  { toCLM := ContinuousLinearMap.id ℝ (DoubledSpace E),
    isKreinIsometry := IsKreinIsometry.id,
    commutes_paraKahler := by
      intro ρ v
      simp [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] }

/-- The composition of two 5-graded SUSY symmetries. -/
noncomputable def compKreinSym (S T : ParaKahler55KreinSymmetry (E := E)) :
    ParaKahler55KreinSymmetry (E := E) :=
  { toCLM := S.toCLM.comp T.toCLM,
    isKreinIsometry := IsKreinIsometry.comp S.isKreinIsometry T.isKreinIsometry,
    commutes_paraKahler := by
      intro ρ v
      calc
        (S.toCLM.comp T.toCLM).comp
            (ρ (CliffordAlgebra.ι Q55
              (ParaKahler55SUSYClosure.paraKahlerK v))) =
            S.toCLM.comp (T.toCLM.comp (ρ (CliffordAlgebra.ι Q55
              (ParaKahler55SUSYClosure.paraKahlerK v)))) :=
          ContinuousLinearMap.comp_assoc _ _ _
        _ = S.toCLM.comp ((ρ (CliffordAlgebra.ι Q55
              (ParaKahler55SUSYClosure.paraKahlerK v))).comp T.toCLM) := by
          rw [T.commutes_paraKahler ρ v]
        _ = (S.toCLM.comp (ρ (CliffordAlgebra.ι Q55
              (ParaKahler55SUSYClosure.paraKahlerK v)))).comp T.toCLM :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = ((ρ (CliffordAlgebra.ι Q55
              (ParaKahler55SUSYClosure.paraKahlerK v))).comp S.toCLM).comp T.toCLM := by
          rw [S.commutes_paraKahler ρ v]
        _ = (ρ (CliffordAlgebra.ι Q55
              (ParaKahler55SUSYClosure.paraKahlerK v))).comp (S.toCLM.comp T.toCLM) :=
          ContinuousLinearMap.comp_assoc _ _ _ }

/-! ### 5. Concrete odd charges and their closure -/

open InfoGeometry.Clifford.Cl55MasterOperatorEnvelopeBridge

/-- The first concrete odd charge, acting on the repository's 32-dimensional
    Fock carrier. -/
abbrev superchargeQ55 : Mat32 := superchargeQ

/-- The conjugate odd charge on the same Fock carrier. -/
abbrev superchargeQBar55 : Mat32 := superchargeQBar

/-- The first odd charge is nilpotent, by the native five-mode CAR relations. -/
theorem superchargeQ55_sq : superchargeQ55 * superchargeQ55 = 0 :=
  superchargeQ_sq

/-- The conjugate odd charge is nilpotent, by the native five-mode CAR relations. -/
theorem superchargeQBar55_sq : superchargeQBar55 * superchargeQBar55 = 0 :=
  superchargeQBar_sq

/-- The mixed odd-odd bracket closes on the scalar central operator `2 I`.
    This is the concrete finite-dimensional SUSY closure relation; it is
    separate from the exterior-image grading and the abstract symmetry type. -/
theorem supercharge55_odd_odd_closure :
    superchargeQ55 * superchargeQBar55 + superchargeQBar55 * superchargeQ55 =
      (2 : ℝ) • (1 : Mat32) := supercharge_anticomm_momentum

end InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
