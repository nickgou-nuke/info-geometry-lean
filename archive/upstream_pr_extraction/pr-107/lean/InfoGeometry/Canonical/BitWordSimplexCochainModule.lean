import InfoGeometry.Canonical.BitWordGraphDifferential
import InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
import InfoGeometry.Canonical.BitWordSimplexFaceCancellation
import InfoGeometry.Canonical.BitWordSimplexSignCancellation
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebraGeneral
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The native cosimplicial carrier of BitWord cochains

Simplex cochains are covariant in the simplex map: a monotone map is pulled
back by precomposition.  This is therefore a `CosimplicialObject`, matching
Mathlib's alternating coface-map complex.
-/

open CategoryTheory
open SimplexCategory

namespace InfoGeometry.Canonical.BitWordGraphDifferential

open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliBitWordStarInductiveSystemBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

abbrev simplexCochainModule (n : ℕ) (Δ : SimplexCategory) : ModuleCat ℂ :=
  ModuleCat.of ℂ (SimplexCochain n Δ.len)

/-- The canonical free coefficient module on the finite BitWord vertices. -/
abbrev bitWordVertexFreeModule (n : ℕ) := Vertex n →₀ ℂ

abbrev SimplexVertexTuple (n k : ℕ) := Fin (k + 1) → Vertex n

abbrev CoefficientSimplexCochain (n k : ℕ) (B : Type*) :=
  SimplexVertexTuple n k → B

/-- The multilinear extension of arbitrary coefficient data from the basis
vertices to their free modules.  `fromDFinsuppEquiv` is Mathlib's universal
property for multilinear maps on free modules. -/
noncomputable def coefficientSimplexMultilinearExtension
    {n k : ℕ} (f : SimplexVertexTuple n k → BitWordMatrixStage n) :
    MultilinearMap ℂ (fun _ : Fin (k + 1) => bitWordVertexFreeModule n)
      (BitWordMatrixStage n) :=
  MultilinearMap.fromDFinsuppEquiv
    (M := fun _ _ => ℂ) (N := BitWordMatrixStage n)
    (fun _ : Fin (k + 1) => Vertex n) ℂ
    (fun p =>
      (MultilinearMap.mkPiAlgebra ℂ (Fin (k + 1)) ℂ).smulRight (f p))
    |>.compLinearMap (fun _ =>
      (finsuppLequivDFinsupp ℂ).toLinearMap)

@[simp] theorem coefficientSimplexMultilinearExtension_single
    {n k : ℕ} (f : SimplexVertexTuple n k → BitWordMatrixStage n)
    (p : SimplexVertexTuple n k) :
    coefficientSimplexMultilinearExtension f
        (fun i => Finsupp.single (p i) (1 : ℂ)) = f p := by
  simp [coefficientSimplexMultilinearExtension]

noncomputable def coefficientSimplexAlternatingOpForm
    {n k : ℕ} (f : SimplexVertexTuple n k → BitWordMatrixStage n) :
    InfoGeometry.OperatorAlgebra.General.OpForm ℂ
      (bitWordVertexFreeModule n) (BitWordMatrixStage n) (k + 1) :=
  (coefficientSimplexMultilinearExtension f).alternatization

@[simp] theorem coefficientSimplexAlternatingOpForm_apply
    {n k : ℕ} (f : SimplexVertexTuple n k → BitWordMatrixStage n)
    (v : Fin (k + 1) → bitWordVertexFreeModule n) :
    coefficientSimplexAlternatingOpForm f v =
      (coefficientSimplexMultilinearExtension f).alternatization v := rfl

theorem coefficientSimplexAlternatingOpForm_basis
    {n k : ℕ} (f : SimplexVertexTuple n k → BitWordMatrixStage n)
    (p : SimplexVertexTuple n k) :
    coefficientSimplexAlternatingOpForm f
        (fun i => Finsupp.single (p i) (1 : ℂ)) =
      ∑ σ : Equiv.Perm (Fin (k + 1)),
        Equiv.Perm.sign σ • f (p ∘ σ) := by
  simp [coefficientSimplexAlternatingOpForm,
    coefficientSimplexMultilinearExtension,
    MultilinearMap.alternatization_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp [Function.comp_def]

theorem coefficientSimplexAlternatingOpForm_map_perm
    {n k : ℕ} (f : SimplexVertexTuple n k → BitWordMatrixStage n)
    (v : Fin (k + 1) → bitWordVertexFreeModule n)
    (σ : Equiv.Perm (Fin (k + 1))) :
    coefficientSimplexAlternatingOpForm f (v ∘ σ) =
      Equiv.Perm.sign σ •
        coefficientSimplexAlternatingOpForm f v := by
  simpa [coefficientSimplexAlternatingOpForm, Int.cast_smul_eq_zsmul] using
    (coefficientSimplexAlternatingOpForm f).map_perm v σ

theorem coefficientSimplexAlternatingOpForm_eq_factorial_smul
    {n k : ℕ} (f : SimplexVertexTuple n k → BitWordMatrixStage n)
    (hzero : ∀ (v : Fin (k + 1) → bitWordVertexFreeModule n)
      (i j : Fin (k + 1)), v i = v j → i ≠ j →
        coefficientSimplexMultilinearExtension f v = 0) :
    coefficientSimplexAlternatingOpForm f =
      (Fintype.card (Fin (k + 1))).factorial •
        (AlternatingMap.mk (coefficientSimplexMultilinearExtension f) hzero) := by
  exact AlternatingMap.coe_alternatization
    (AlternatingMap.mk (coefficientSimplexMultilinearExtension f) hzero)

/-- Canonical bridge from genuine multilinear data to the arbitrary-degree
operator-form carrier.  The multilinear input is explicit: no extension is
claimed for an arbitrary tuple-function. -/
noncomputable def multilinearOpFormOf {n k : ℕ}
    (m : MultilinearMap ℂ (fun _ : Fin k => bitWordVertexFreeModule n)
      (BitWordMatrixStage n)) :
    InfoGeometry.OperatorAlgebra.General.OpForm ℂ
      (bitWordVertexFreeModule n) (BitWordMatrixStage n) k :=
  m.alternatization

@[simp] theorem multilinearOpFormOf_apply {n k : ℕ}
    (m : MultilinearMap ℂ (fun _ : Fin k => bitWordVertexFreeModule n)
      (BitWordMatrixStage n)) (v : Fin k → bitWordVertexFreeModule n) :
    multilinearOpFormOf m v = m.alternatization v := rfl

/- The canonical linear extension of a vertex coefficient function. -/
noncomputable def vertexCochainLinearExtension {n : ℕ}
    (f : Vertex n → BitWordMatrixStage n) :
    bitWordVertexFreeModule n →ₗ[ℂ] BitWordMatrixStage n :=
  Finsupp.lsum ℂ (fun v =>
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (f v))

@[simp] theorem vertexCochainLinearExtension_single {n : ℕ}
    (f : Vertex n → BitWordMatrixStage n) (v : Vertex n) :
    vertexCochainLinearExtension f
        (Finsupp.single v (1 : ℂ)) = f v := by
  change (Finsupp.lsum ℂ (fun v =>
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (f v)))
      (Finsupp.single v (1 : ℂ)) = f v
  rw [Finsupp.lsum_single]
  simp

/- Degree-two coefficient data has a canonical curried bilinear extension. -/
noncomputable def pairCochainLinearExtension {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n) :
    bitWordVertexFreeModule n →ₗ[ℂ]
      bitWordVertexFreeModule n →ₗ[ℂ] BitWordMatrixStage n :=
  Finsupp.lsum ℂ (fun v =>
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight
      (Finsupp.lsum ℂ (fun w =>
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (f v w))))

@[simp] theorem pairCochainLinearExtension_single_single {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (v w : Vertex n) :
    pairCochainLinearExtension f (Finsupp.single v (1 : ℂ))
        (Finsupp.single w (1 : ℂ)) = f v w := by
  simp [pairCochainLinearExtension, Finsupp.lsum_single]

theorem pairCochainLinearExtension_add_left {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (x y z : bitWordVertexFreeModule n) :
    pairCochainLinearExtension f (x + y) z =
      pairCochainLinearExtension f x z +
        pairCochainLinearExtension f y z := by
  exact congrArg (fun L : bitWordVertexFreeModule n →ₗ[ℂ]
      BitWordMatrixStage n => L z)
    ((pairCochainLinearExtension f).map_add x y)

theorem pairCochainLinearExtension_smul_left {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (a : ℂ) (x z : bitWordVertexFreeModule n) :
    pairCochainLinearExtension f (a • x) z =
      a • pairCochainLinearExtension f x z := by
  exact congrArg (fun L : bitWordVertexFreeModule n →ₗ[ℂ]
      BitWordMatrixStage n => L z)
    ((pairCochainLinearExtension f).map_smul a x)

theorem pairCochainLinearExtension_add_right {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (x y z : bitWordVertexFreeModule n) :
    pairCochainLinearExtension f x (y + z) =
      pairCochainLinearExtension f x y +
        pairCochainLinearExtension f x z := by
  exact (pairCochainLinearExtension f x).map_add y z

theorem pairCochainLinearExtension_smul_right {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (a : ℂ) (x y : bitWordVertexFreeModule n) :
    pairCochainLinearExtension f x (a • y) =
      a • pairCochainLinearExtension f x y := by
  exact (pairCochainLinearExtension f x).map_smul a y

noncomputable def pairCochainMultilinearExtension {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n) :
    MultilinearMap ℂ (fun _ : Fin 2 => bitWordVertexFreeModule n)
      (BitWordMatrixStage n) :=
  { toFun := fun v =>
      pairCochainLinearExtension f (v 0) (v 1)
    map_update_add' := by
      intro m v i x y
      fin_cases i
      · simpa [Function.update] using
          pairCochainLinearExtension_add_left f x y (v 1)
      · simpa [Function.update] using
          pairCochainLinearExtension_add_right f (v 0) x y
    map_update_smul' := by
      intro m v i a x
      fin_cases i
      · simpa [Function.update] using
          pairCochainLinearExtension_smul_left f a x (v 1)
      · simpa [Function.update] using
          pairCochainLinearExtension_smul_right f a (v 0) x }

@[simp] theorem pairCochainMultilinearExtension_apply {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (v : Fin 2 → bitWordVertexFreeModule n) :
    pairCochainMultilinearExtension f v =
      pairCochainLinearExtension f (v 0) (v 1) := rfl

/- Antisymmetrization has diagonal zero by construction. -/
noncomputable def pairCochainAntisymmetrization {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n) :
    MultilinearMap ℂ (fun _ : Fin 2 => bitWordVertexFreeModule n)
      (BitWordMatrixStage n) :=
  { toFun := fun v =>
      pairCochainLinearExtension f (v 0) (v 1) -
        pairCochainLinearExtension f (v 1) (v 0)
    map_update_add' := by
      intro m v i x y
      fin_cases i
      · simp [Function.update]
        abel
      · simp [Function.update]
        abel
    map_update_smul' := by
      intro m v i a x
      fin_cases i
      · simp [Function.update]
        simp only [smul_sub]
      · simp [Function.update]
        simp only [smul_sub] }

@[simp] theorem pairCochainAntisymmetrization_apply {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (v : Fin 2 → bitWordVertexFreeModule n) :
    pairCochainAntisymmetrization f v =
      pairCochainLinearExtension f (v 0) (v 1) -
        pairCochainLinearExtension f (v 1) (v 0) := rfl

@[simp] theorem pairCochainAntisymmetrization_diagonal {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (x : bitWordVertexFreeModule n) :
    pairCochainAntisymmetrization f (fun _ => x) = 0 := by
  simp [pairCochainAntisymmetrization]

noncomputable def pairCochainAntisymmetricMap {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n) :
    bitWordVertexFreeModule n [⋀^ (Fin 2)]→ₗ[ℂ]
      BitWordMatrixStage n :=
  AlternatingMap.mk (pairCochainAntisymmetrization f) (by
    intro v i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have h : v 0 = v 1 := by simpa using hij
      have hv : v = (fun _ => v 0) := by
        funext q
        fin_cases q
        · rfl
        · exact h.symm
      rw [hv]
      exact pairCochainAntisymmetrization_diagonal f (v 0)
    · have h : v 1 = v 0 := by simpa using hij
      have hv : v = (fun _ => v 1) := by
        funext q
        fin_cases q
        · exact h.symm
        · rfl
      rw [hv]
      exact pairCochainAntisymmetrization_diagonal f (v 1)
    · exact (hne rfl).elim)

@[simp] theorem pairCochainAntisymmetricMap_apply {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (v : Fin 2 → bitWordVertexFreeModule n) :
    pairCochainAntisymmetricMap f v =
      pairCochainAntisymmetrization f v := rfl

/-- The canonical degree-two operator form obtained from antisymmetrized
pair-cochain data on the free BitWord vertex module. -/
noncomputable def pairCochainOp2Form {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n) :
    InfoGeometry.OperatorAlgebra.General.OpForm ℂ
      (bitWordVertexFreeModule n) (BitWordMatrixStage n) 2 :=
  pairCochainAntisymmetricMap f

@[simp] theorem pairCochainOp2Form_apply {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (v : Fin 2 → bitWordVertexFreeModule n) :
    pairCochainOp2Form f v = pairCochainAntisymmetrization f v := rfl

theorem pairCochainAntisymmetricMap_map_perm {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (v : Fin 2 → bitWordVertexFreeModule n)
    (σ : Equiv.Perm (Fin 2)) :
    pairCochainAntisymmetricMap f (v ∘ σ) =
      (Equiv.Perm.sign σ : ℤ) • pairCochainAntisymmetricMap f v := by
  exact (pairCochainAntisymmetricMap f).map_perm v σ

theorem pairCochainAntisymmetrization_single_single {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (v w : Vertex n) :
    pairCochainAntisymmetrization f (fun i => Finsupp.single (match i with
      | 0 => v
      | 1 => w) (1 : ℂ)) = f v w - f w v := by
  change pairCochainLinearExtension f
      (Finsupp.single v (1 : ℂ))
      (Finsupp.single w (1 : ℂ)) -
    pairCochainLinearExtension f
      (Finsupp.single w (1 : ℂ))
      (Finsupp.single v (1 : ℂ)) = f v w - f w v
  rw [pairCochainLinearExtension_single_single,
    pairCochainLinearExtension_single_single]

theorem pairCochainOp2Form_single_single {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (v w : Vertex n) :
    pairCochainOp2Form f
        (fun i => Finsupp.single (match i with
          | 0 => v
          | 1 => w) (1 : ℂ)) =
      f v w - f w v := by
  exact pairCochainAntisymmetrization_single_single f v w

theorem pairCochainAntisymmetrization_single_single_of_skew {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (hskew : ∀ v w, f w v = -f v w)
    (v w : Vertex n) :
    pairCochainAntisymmetrization f (fun i => Finsupp.single (match i with
      | 0 => v
      | 1 => w) (1 : ℂ)) = (2 : ℂ) • f v w := by
  rw [pairCochainAntisymmetrization_single_single, hskew]
  simp [sub_eq_add_neg, two_smul]

/- The alternating-map constructor is exposed with its exact native
   repeated-input obligation. -/
noncomputable def pairCochainAlternatingMap {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (hzero : ∀ (v : Fin 2 → bitWordVertexFreeModule n)
      (i j : Fin 2), i ≠ j → v i = v j →
        pairCochainMultilinearExtension f v = 0) :
    bitWordVertexFreeModule n [⋀^ (Fin 2)]→ₗ[ℂ]
      BitWordMatrixStage n :=
  AlternatingMap.mk (pairCochainMultilinearExtension f) (by
    intro v i j hij hne
    exact hzero v i j hne hij)

@[simp] theorem pairCochainAlternatingMap_apply {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (hzero : ∀ (v : Fin 2 → bitWordVertexFreeModule n)
      (i j : Fin 2), i ≠ j → v i = v j →
        pairCochainMultilinearExtension f v = 0)
    (v : Fin 2 → bitWordVertexFreeModule n) :
    pairCochainAlternatingMap f hzero v =
      pairCochainMultilinearExtension f v := rfl

@[simp] theorem pairCochainAlternatingMap_single_single {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (hzero : ∀ (v : Fin 2 → bitWordVertexFreeModule n)
      (i j : Fin 2), i ≠ j → v i = v j →
        pairCochainMultilinearExtension f v = 0)
    (v w : Vertex n) :
    pairCochainAlternatingMap f hzero
        (fun i => Finsupp.single (match i with
          | 0 => v
          | 1 => w) (1 : ℂ)) = f v w := by
  rw [pairCochainAlternatingMap_apply]
  change pairCochainLinearExtension f
      (Finsupp.single v (1 : ℂ))
      (Finsupp.single w (1 : ℂ)) = f v w
  exact pairCochainLinearExtension_single_single f v w

theorem pairCochainAlternatingMap_map_perm {n : ℕ}
    (f : Vertex n → Vertex n → BitWordMatrixStage n)
    (hzero : ∀ (v : Fin 2 → bitWordVertexFreeModule n)
      (i j : Fin 2), i ≠ j → v i = v j →
        pairCochainMultilinearExtension f v = 0)
    (v : Fin 2 → bitWordVertexFreeModule n)
    (σ : Equiv.Perm (Fin 2)) :
    pairCochainAlternatingMap f hzero (v ∘ σ) =
      (Equiv.Perm.sign σ : ℤ) •
        pairCochainAlternatingMap f hzero v := by
  exact (pairCochainAlternatingMap f hzero).map_perm v σ

/-- Coefficientwise transport along an algebra map, keeping the simplex index. -/
def simplexCochainMapCoefficients {n m k : ℕ}
    (F : BitWordMatrixStage n →ₐ[ℂ] BitWordMatrixStage m)
    (c : SimplexCochain n k) :
    (Fin (k + 1) → Vertex n) → BitWordMatrixStage m :=
  fun σ => F (c σ)

/-- A simplex cochain vanishes on tuples with a repeated vertex. -/
def IsAlternatingSimplexCochain {n k : ℕ}
    (c : SimplexCochain n k) : Prop :=
  ∀ (σ : Fin (k + 1) → Vertex n) (i j : Fin (k + 1)),
    i ≠ j → σ i = σ j → c σ = 0

def IsAlternatingCoefficientSimplexCochain {n k : ℕ} {B : Type*}
    [Zero B] (c : CoefficientSimplexCochain n k B) : Prop :=
  ∀ (σ : SimplexVertexTuple n k) (i j : Fin (k + 1)),
    i ≠ j → σ i = σ j → c σ = 0

def coefficientSimplexMap {n m k : ℕ} {B C : Type*}
    (e : Vertex n → Vertex m) (F : B → C)
    (c : CoefficientSimplexCochain m k B) :
    CoefficientSimplexCochain n k C :=
  fun σ => F (c (e ∘ σ))

theorem coefficientSimplexMap_comp
    {n m l k : ℕ} {B C D : Type*}
    (e : Vertex n → Vertex m) (e' : Vertex m → Vertex l)
    (F : C → D) (G : B → C)
    (c : CoefficientSimplexCochain l k B) :
    coefficientSimplexMap e F
        (coefficientSimplexMap e' G c) =
      coefficientSimplexMap (e' ∘ e) (F ∘ G) c := by
  funext σ
  rfl

theorem coefficientSimplexMap_preserves_alternating
    {n m k : ℕ} {B C : Type*} [Zero B] [Zero C]
    (e : Vertex n → Vertex m) (F : B → C) (hF : F 0 = 0)
    (c : CoefficientSimplexCochain m k B)
    (hc : IsAlternatingCoefficientSimplexCochain c) :
    IsAlternatingCoefficientSimplexCochain (coefficientSimplexMap e F c) := by
  intro σ i j hij hσ
  change F (c (e ∘ σ)) = 0
  rw [hc (e ∘ σ) i j hij (congrArg e hσ), hF]

/- The honest structural carrier for coefficient cochains satisfying the
repeated-vertex alternating condition.  Algebraic instances are introduced
only after the corresponding closure proofs are available. -/
def AlternatingCoefficientSimplexCochain (n k : ℕ) (B : Type*) [Zero B] :=
  {c : CoefficientSimplexCochain n k B //
    IsAlternatingCoefficientSimplexCochain c}

def coefficientSimplexMapAlternating
    {n m k : ℕ} {B C : Type*} [Zero B] [Zero C]
    (e : Vertex n → Vertex m) (F : B → C) (hF : F 0 = 0)
    (c : AlternatingCoefficientSimplexCochain m k B) :
    AlternatingCoefficientSimplexCochain n k C :=
  ⟨coefficientSimplexMap e F c.1,
    coefficientSimplexMap_preserves_alternating e F hF c.1 c.2⟩

theorem coefficientSimplexMapAlternating_comp
    {n m l k : ℕ} {B C D : Type*} [Zero B] [Zero C] [Zero D]
    (e : Vertex n → Vertex m) (e' : Vertex m → Vertex l)
    (F : C → D) (G : B → C) (hF : F 0 = 0) (hG : G 0 = 0)
    (c : AlternatingCoefficientSimplexCochain l k B) :
    coefficientSimplexMapAlternating e F hF
        (coefficientSimplexMapAlternating e' G hG c) =
      coefficientSimplexMapAlternating (e' ∘ e) (F ∘ G)
        (by simp [hF, hG] : (F ∘ G) 0 = 0) c := by
  apply Subtype.ext
  exact coefficientSimplexMap_comp e e' F G c.1

@[simp] theorem coefficientSimplexMapAlternating_apply
    {n m k : ℕ} {B C : Type*} [Zero B] [Zero C]
    (e : Vertex n → Vertex m) (F : B → C) (hF : F 0 = 0)
    (c : AlternatingCoefficientSimplexCochain m k B)
    (σ : SimplexVertexTuple n k) :
    (coefficientSimplexMapAlternating e F hF c).1 σ =
      F (c.1 (e ∘ σ)) := rfl

def coefficientSimplexCoboundary {n k : ℕ} {B : Type*}
    [AddCommGroup B]
    (c : CoefficientSimplexCochain n k B) :
    CoefficientSimplexCochain n (k + 1) B :=
  fun σ => ∑ i : Fin (k + 2),
    (-1 : ℤ) ^ i.1 • c (σ ∘ Fin.succAbove i)

@[simp] theorem coefficientSimplexCoboundary_apply
    {n k : ℕ} {B : Type*} [AddCommGroup B]
    (c : CoefficientSimplexCochain n k B)
    (σ : SimplexVertexTuple n (k + 1)) :
    coefficientSimplexCoboundary c σ =
      ∑ i : Fin (k + 2),
      (-1 : ℤ) ^ i.1 • c (σ ∘ Fin.succAbove i) := rfl

theorem coefficientSimplexCoboundary_isAlternating_zero
    {n : ℕ} {B : Type*} [AddCommGroup B]
    (c : CoefficientSimplexCochain n 0 B) :
    IsAlternatingCoefficientSimplexCochain
      (coefficientSimplexCoboundary c) := by
  intro σ i j hij hσ
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · have hfaces :=
      InfoGeometry.Canonical.BitWordSimplexFaceCancellation.repeated_pair_faces_eq
        σ hσ
    simp [coefficientSimplexCoboundary, Fin.sum_univ_succ]
    have hfirst : σ ∘ Fin.succ =
        σ ∘ Fin.succAbove (1 : Fin 2) := by
      calc
        σ ∘ Fin.succ = σ ∘ Fin.succAbove (0 : Fin 2) := by rfl
        _ = σ ∘ Fin.succAbove (1 : Fin 2) := hfaces
    rw [hfirst]
    abel
  · have hfaces :=
      InfoGeometry.Canonical.BitWordSimplexFaceCancellation.repeated_pair_faces_eq
        σ hσ.symm
    simp [coefficientSimplexCoboundary, Fin.sum_univ_succ]
    have hfirst : σ ∘ Fin.succ =
        σ ∘ Fin.succAbove (1 : Fin 2) := by
      calc
        σ ∘ Fin.succ = σ ∘ Fin.succAbove (0 : Fin 2) := by rfl
        _ = σ ∘ Fin.succAbove (1 : Fin 2) := hfaces
    rw [hfirst]
    abel
  · exact (hij rfl).elim

def coefficientSimplexCoboundaryAlternatingZero
    {n : ℕ} {B : Type*} [AddCommGroup B]
    (c : AlternatingCoefficientSimplexCochain n 0 B) :
    AlternatingCoefficientSimplexCochain n 1 B :=
  ⟨coefficientSimplexCoboundary c.1,
    coefficientSimplexCoboundary_isAlternating_zero c.1⟩

@[simp] theorem coefficientSimplexCoboundaryAlternatingZero_apply
    {n : ℕ} {B : Type*} [AddCommGroup B]
    (c : AlternatingCoefficientSimplexCochain n 0 B)
    (σ : SimplexVertexTuple n 1) :
    (coefficientSimplexCoboundaryAlternatingZero c).1 σ =
      coefficientSimplexCoboundary c.1 σ := rfl

theorem coefficientSimplexMap_coboundary
    {n m k : ℕ} {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (e : Vertex n → Vertex m) (F : B →+ C)
    (c : CoefficientSimplexCochain m k B)
    (σ : SimplexVertexTuple n (k + 1)) :
    F (coefficientSimplexCoboundary c (e ∘ σ)) =
      coefficientSimplexCoboundary (coefficientSimplexMap e F c) σ := by
  simp only [coefficientSimplexCoboundary, coefficientSimplexMap,
    Function.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul]
  rfl

theorem coefficientSimplexMap_coboundary_eq
    {n m k : ℕ} {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (e : Vertex n → Vertex m) (F : B →+ C)
    (c : CoefficientSimplexCochain m k B) :
    coefficientSimplexMap e F
        (coefficientSimplexCoboundary c) =
      coefficientSimplexCoboundary
        (coefficientSimplexMap e F c) := by
  funext σ
  exact coefficientSimplexMap_coboundary e F c σ

theorem coefficientSimplexMap_coboundary_preserves_alternating_zero
    {n m : ℕ} {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (e : Vertex n → Vertex m) (F : B →+ C)
    (c : CoefficientSimplexCochain m 0 B) :
    IsAlternatingCoefficientSimplexCochain
      (coefficientSimplexMap e F
        (coefficientSimplexCoboundary c)) := by
  exact coefficientSimplexMap_preserves_alternating e F F.map_zero
    (coefficientSimplexCoboundary c)
    (coefficientSimplexCoboundary_isAlternating_zero c)

abbrev coefficientSimplexModule (n : ℕ) (B : Type*) [AddCommGroup B]
    [Module ℂ B] (Δ : SimplexCategory) : ModuleCat ℂ :=
  ModuleCat.of ℂ (CoefficientSimplexCochain n Δ.len B)

noncomputable def coefficientSimplexCochains (n : ℕ) (B : Type*)
    [AddCommGroup B] [Module ℂ B] : CosimplicialObject (ModuleCat ℂ) where
  obj Δ := coefficientSimplexModule n B Δ
  map f := ModuleCat.ofHom
    { toFun := fun c σ => c (σ ∘ f.toOrderHom)
      map_add' := by intro c d; rfl
      map_smul' := by intro a c; rfl }
  map_id := by
    intro Δ
    apply ModuleCat.hom_ext
    ext c σ
    rfl
  map_comp := by
    intro Δ₁ Δ₂ Δ₃ f g
    apply ModuleCat.hom_ext
    ext c σ
    rfl

theorem coefficientSimplexCochains_d_squared
    (n : ℕ) (B : Type*) [AddCommGroup B] [Module ℂ B] (k : ℕ) :
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (coefficientSimplexCochains n B) k ≫
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (coefficientSimplexCochains n B) (k + 1) = 0 := by
  exact AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
    (coefficientSimplexCochains n B) k

theorem simplexCochainMapCoefficients_coboundary
    {n m k : ℕ}
    (F : BitWordMatrixStage n →ₐ[ℂ] BitWordMatrixStage m)
    (c : SimplexCochain n k) (σ : Fin (k + 2) → Vertex n) :
    F (simplexCoboundary c σ) =
      ∑ i : Fin (k + 2),
        (-1 : BitWordMatrixStage m) ^ i.1 •
          simplexCochainMapCoefficients F c (σ ∘ Fin.succAbove i) := by
  simp only [simplexCoboundary, simplexCochainMapCoefficients, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_eq_mul, map_mul, map_pow]
  simp only [map_neg, map_one]

/- Pullback of cochains along a vertex map, together with coefficient transport. -/
def simplexCochainPullback {n m k : ℕ}
    (e : Vertex n → Vertex m)
    (F : BitWordMatrixStage m →ₐ[ℂ] BitWordMatrixStage n)
    (c : SimplexCochain m k) : SimplexCochain n k :=
  fun σ => F (c (e ∘ σ))

theorem simplexCochainPullback_preserves_alternating
    {n m k : ℕ}
    (e : Vertex n → Vertex m)
    (F : BitWordMatrixStage m →ₐ[ℂ] BitWordMatrixStage n)
    (c : SimplexCochain m k)
    (hc : IsAlternatingSimplexCochain c) :
    IsAlternatingSimplexCochain (simplexCochainPullback e F c) := by
  exact fun σ i j hij hσ => by
    change F (c (e ∘ σ)) = 0
    rw [hc (e ∘ σ) i j hij (congrArg e hσ)]
    exact F.map_zero

theorem simplexCochainPullback_coboundary
    {n m k : ℕ}
    (e : Vertex n → Vertex m)
    (F : BitWordMatrixStage m →ₐ[ℂ] BitWordMatrixStage n)
    (c : SimplexCochain m k) (σ : Fin (k + 2) → Vertex n) :
    simplexCochainPullback e F (simplexCoboundary c) σ =
      simplexCoboundary (simplexCochainPullback e F c) σ := by
  simp only [simplexCochainPullback, simplexCoboundary, Function.comp_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_eq_mul, map_mul, map_pow, map_neg, map_one,
    Function.comp_assoc]

/- The native successor transport: truncate vertices and embed coefficients. -/
noncomputable def bitWordSimplexSuccMap {n k : ℕ} :
    SimplexCochain n k → SimplexCochain (n + 1) k :=
  simplexCochainPullback (prefixSucc n)
    (bitWordDyadicStarEmbedding n).toAlgHom

theorem bitWordSimplexSuccMap_coboundary
    {n k : ℕ} (c : SimplexCochain n k)
    (σ : Fin (k + 2) → Vertex (n + 1)) :
    bitWordSimplexSuccMap (simplexCoboundary c) σ =
      simplexCoboundary (bitWordSimplexSuccMap c) σ := by
  exact simplexCochainPullback_coboundary
    (prefixSucc n) (bitWordDyadicStarEmbedding n).toAlgHom c σ

/- Canonical truncation of a BitWord to a shorter finite stage. -/
def bitWordVertexTrunc {i j : ℕ} (hij : i ≤ j) : Vertex j → Vertex i :=
  fun w k => w ⟨k.1, lt_of_lt_of_le k.2 hij⟩

/- Cochain transport along the finite BitWord star-algebra system. -/
noncomputable def bitWordSimplexMap
    (T : BitWordStarData) {i j k : ℕ} (hij : i ≤ j) :
    SimplexCochain i k → SimplexCochain j k :=
  simplexCochainPullback (bitWordVertexTrunc hij)
    (bitWordStarMap T hij).toAlgHom

theorem bitWordSimplexMap_coboundary
    (T : BitWordStarData) {i j k : ℕ} (hij : i ≤ j)
    (c : SimplexCochain i k)
    (σ : Fin (k + 2) → Vertex j) :
    bitWordSimplexMap T hij (simplexCoboundary c) σ =
      simplexCoboundary (bitWordSimplexMap T hij c) σ := by
  exact simplexCochainPullback_coboundary
    (bitWordVertexTrunc hij) (bitWordStarMap T hij).toAlgHom c σ

theorem bitWordSimplexMap_coboundary_eq
    (T : BitWordStarData) {i j k : ℕ} (hij : i ≤ j)
    (c : SimplexCochain i k) :
    bitWordSimplexMap T hij (simplexCoboundary c) =
      simplexCoboundary (bitWordSimplexMap T hij c) := by
  funext σ
  exact bitWordSimplexMap_coboundary T hij c σ

theorem bitWordVertexTrunc_comp
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (w : Vertex k) :
    bitWordVertexTrunc hij (bitWordVertexTrunc hjk w) =
      bitWordVertexTrunc (le_trans hij hjk) w := by
  funext a
  rfl

theorem bitWordSimplexMap_comp
    (T : BitWordStarData) {i j k l : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) (c : SimplexCochain i l) :
    bitWordSimplexMap T hjk (bitWordSimplexMap T hij c) =
      bitWordSimplexMap T (le_trans hij hjk) c := by
  funext σ
  simp only [bitWordSimplexMap, simplexCochainPullback, Function.comp_apply]
  change ((bitWordStarMap T hjk).comp (bitWordStarMap T hij)).toAlgHom
      (c (bitWordVertexTrunc hij ∘ bitWordVertexTrunc hjk ∘ σ)) = _
  rw [bitWordStarMap_comp T hij hjk]
  have hσ :
      bitWordVertexTrunc hij ∘ bitWordVertexTrunc hjk ∘ σ =
        bitWordVertexTrunc (le_trans hij hjk) ∘ σ := by
    funext a
    exact bitWordVertexTrunc_comp hij hjk (σ a)
  rw [hσ]

@[simp] theorem bitWordVertexFreeModule_single_apply
    (n : ℕ) (v : Vertex n) (w : Vertex n) :
    (Finsupp.single v (1 : ℂ) : bitWordVertexFreeModule n) w =
      if v = w then 1 else 0 := by
  classical
  by_cases h : v = w <;> simp [h]

def simplexCochainTransport {n k l : ℕ} (h : k = l)
    (c : SimplexCochain n k) : SimplexCochain n l :=
  fun σ => c (fun i => σ (Fin.cast (congrArg Nat.succ h) i))

@[simp] theorem simplexCochainTransport_apply {n k l : ℕ} (h : k = l)
    (c : SimplexCochain n k) (σ : Fin (l + 1) → Vertex n) :
    simplexCochainTransport h c σ =
      c (fun i => σ (Fin.cast (congrArg Nat.succ h) i)) := rfl

@[simp] theorem simplexCochainTransport_refl {n k : ℕ}
    (c : SimplexCochain n k) :
    simplexCochainTransport rfl c = c := by
  funext σ
  simp [simplexCochainTransport]

theorem simplexCochainTransport_comp {n k l m : ℕ}
    (h : k = l) (h' : l = m) (c : SimplexCochain n k) :
    simplexCochainTransport h'
        (simplexCochainTransport h c) =
      simplexCochainTransport (h.trans h') c := by
  cases h
  cases h'
  rfl

theorem simplexCoboundary_sign_shift (p j : ℕ) :
    (-1 : ℂ) ^ (p + j) = (-1 : ℂ) ^ p * (-1 : ℂ) ^ j := by
  exact pow_add (-1 : ℂ) p j

theorem simplexCoboundary_sign_shift_succ (p j : ℕ) :
    (-1 : ℂ) ^ (p + 1 + j) =
      (-1 : ℂ) ^ p * (-1 : ℂ) ^ (j + 1) := by
  rw [show p + 1 + j = p + (j + 1) by omega, pow_add, pow_add]

/- The finite face sum used by the Alexander--Whitney differential splits
  canonically at the cup-product cut.  Naming this reindexing separately is
  important: later Leibniz proofs can rewrite the two blocks without
  expanding a sum or enumerating its indices. -/
theorem simplexCoboundary_face_sum_split
    {α : Type*} [AddCommMonoid α] (p q : ℕ)
    (f : Fin ((p + 1) + (q + 1)) → α) :
    (∑ i : Fin ((p + 1) + (q + 1)), f i) =
      (∑ i : Fin (p + 1), f (Fin.castAdd (q + 1) i)) +
        ∑ j : Fin (q + 1), f (Fin.natAdd (p + 1) j) := by
  exact Fin.sum_univ_add (f := f) (a := p + 1) (b := q + 1)

theorem simplexCoboundary_signed_face_sum_split
    {α : Type*} [AddCommGroup α] (p q : ℕ)
    (f : Fin ((p + 1) + (q + 1)) → α) :
    (∑ i : Fin ((p + 1) + (q + 1)),
        (-1 : ℤ) ^ i.1 • f i) =
      (∑ i : Fin (p + 1),
        (-1 : ℤ) ^ i.1 • f (Fin.castAdd (q + 1) i)) +
        (-1 : ℤ) ^ (p + 1) •
          (∑ j : Fin (q + 1),
            (-1 : ℤ) ^ j.1 • f (Fin.natAdd (p + 1) j)) := by
  rw [Fin.sum_univ_add]
  rw [Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (Fin.natAdd (p + 1) j).val = p + 1 + j.val by rfl,
    pow_add]
  simp [smul_smul, mul_assoc]

/-- Cochains whose simplex arguments transform with the permutation sign.

The vertices themselves are not a module, so Mathlib's `AlternatingMap` is
not the appropriate carrier here.  Alternation is instead imposed on the
finite simplex-index action. -/
structure AlternatingSimplexCochain (n k : ℕ) where
  toFun : SimplexCochain n k
  alternating : ∀ (σ : Fin (k + 1) → Vertex n) (p : Equiv.Perm (Fin (k + 1))),
    toFun (σ ∘ p) = (Equiv.Perm.sign p : ℤ) • toFun σ

instance : CoeFun (AlternatingSimplexCochain n k)
    (fun _ => SimplexCochain n k) := ⟨AlternatingSimplexCochain.toFun⟩

@[simp] theorem AlternatingSimplexCochain.coe_toFun
    (c : AlternatingSimplexCochain n k) : (c : SimplexCochain n k) = c.toFun := rfl

@[ext] theorem AlternatingSimplexCochain.ext {c d : AlternatingSimplexCochain n k}
    (h : (c : SimplexCochain n k) = d) : c = d := by
  cases c
  cases d
  cases h
  rfl

instance : Zero (AlternatingSimplexCochain n k) where
  zero :=
    { toFun := 0
      alternating := by
        intro σ p
        simp }

instance : Add (AlternatingSimplexCochain n k) where
  add c d :=
    { toFun := c.toFun + d.toFun
      alternating := by
        intro σ p
        simp only [Pi.add_apply]
        rw [c.alternating, d.alternating]
        rw [smul_add] }

instance : Neg (AlternatingSimplexCochain n k) where
  neg c :=
    { toFun := -c.toFun
      alternating := by
        intro σ p
        simp only [Pi.neg_apply]
        rw [c.alternating]
        simp }

@[simp] theorem AlternatingSimplexCochain.zero_apply
    (σ : Fin (k + 1) → Vertex n) :
    ((0 : AlternatingSimplexCochain n k) : SimplexCochain n k) σ = 0 := rfl

@[simp] theorem AlternatingSimplexCochain.add_apply
    (c d : AlternatingSimplexCochain n k)
    (σ : Fin (k + 1) → Vertex n) :
    ((c + d : AlternatingSimplexCochain n k) : SimplexCochain n k) σ =
      c σ + d σ := rfl

@[simp] theorem AlternatingSimplexCochain.neg_apply
    (c : AlternatingSimplexCochain n k)
    (σ : Fin (k + 1) → Vertex n) :
    ((-c : AlternatingSimplexCochain n k) : SimplexCochain n k) σ =
      -c σ := rfl

/- Stage transport preserves the alternating simplex-index action. -/
noncomputable def alternatingBitWordSimplexMap
    (T : BitWordStarData) {i j k : ℕ} (hij : i ≤ j)
    (c : AlternatingSimplexCochain i k) :
    AlternatingSimplexCochain j k where
  toFun := bitWordSimplexMap T hij c.toFun
  alternating := by
    intro σ p
    change (bitWordStarMap T hij).toAlgHom
        (c.toFun (bitWordVertexTrunc hij ∘ σ ∘ p)) = _
    rw [show bitWordVertexTrunc hij ∘ σ ∘ p =
        (bitWordVertexTrunc hij ∘ σ) ∘ p by rfl]
    rw [c.alternating]
    simp [bitWordSimplexMap, simplexCochainPullback]

theorem alternatingBitWordSimplexMap_comp
    (T : BitWordStarData) {i j k l : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k)
    (c : AlternatingSimplexCochain i l) :
    alternatingBitWordSimplexMap T hjk
        (alternatingBitWordSimplexMap T hij c) =
      alternatingBitWordSimplexMap T (le_trans hij hjk) c := by
  apply AlternatingSimplexCochain.ext
  exact bitWordSimplexMap_comp T hij hjk c.toFun

def simplexCochainOf0 {n : ℕ} (f : Cochain0 n) : SimplexCochain n 0 :=
  fun σ => f (σ 0)

def alternatingSimplexCochainOf0 {n : ℕ} (f : Cochain0 n) :
    AlternatingSimplexCochain n 0 where
  toFun := simplexCochainOf0 f
  alternating := by
    intro σ p
    have hp : p 0 = 0 := by
      exact Fin.eq_zero (p 0)
    have hp' : p = 1 := by
      apply Equiv.ext
      intro i
      fin_cases i
      exact hp
    simp [simplexCochainOf0, Function.comp_def, hp, hp']

def simplexCochainOf1 {n : ℕ} (g : Cochain1 n) : SimplexCochain n 1 :=
  fun σ => g (σ 0) (σ 1)

def simplexCochainOf2 {n : ℕ} (h : Cochain2 n) : SimplexCochain n 2 :=
  fun σ => h (σ 0) (σ 1) (σ 2)

def simplexCochainOf3 {n : ℕ} (k : Cochain3 n) : SimplexCochain n 3 :=
  fun σ => k (σ 0) (σ 1) (σ 2) (σ 3)

def simplexCochainOf4 {n : ℕ} (q : Cochain4 n) : SimplexCochain n 4 :=
  fun σ => q (σ 0) (σ 1) (σ 2) (σ 3) (σ 4)

def simplexFront (p q : ℕ) : Fin (p + 1) → Fin (p + q + 1) :=
  fun i => ⟨i, by omega⟩

def simplexBack (p q : ℕ) : Fin (q + 1) → Fin (p + q + 1) :=
  fun j => ⟨p + j, by omega⟩

@[simp] theorem simplexFront_apply (p q : ℕ) (i : Fin (p + 1)) :
    simplexFront p q i = ⟨i, by omega⟩ := rfl

@[simp] theorem simplexBack_apply (p q : ℕ) (j : Fin (q + 1)) :
    simplexBack p q j = ⟨p + j, by omega⟩ := rfl

def coefficientSimplexCup {n p q : ℕ} {B : Type*} [Mul B]
    (a : CoefficientSimplexCochain n p B)
    (b : CoefficientSimplexCochain n q B) :
    CoefficientSimplexCochain n (p + q) B :=
  fun σ => a (σ ∘ simplexFront p q) * b (σ ∘ simplexBack p q)

@[simp] theorem coefficientSimplexCup_apply
    {n p q : ℕ} {B : Type*} [Mul B]
    (a : CoefficientSimplexCochain n p B)
    (b : CoefficientSimplexCochain n q B)
    (σ : SimplexVertexTuple n (p + q)) :
    coefficientSimplexCup a b σ =
      a (σ ∘ simplexFront p q) * b (σ ∘ simplexBack p q) := rfl

theorem coefficientSimplexMap_cup
    {n m p q : ℕ} {B C : Type*} [MulOne B] [MulOne C]
    (e : Vertex n → Vertex m) (F : B →* C)
    (a : CoefficientSimplexCochain m p B)
    (b : CoefficientSimplexCochain m q B) :
    coefficientSimplexMap e F.toFun (coefficientSimplexCup a b) =
      coefficientSimplexCup
        (coefficientSimplexMap e F.toFun a)
        (coefficientSimplexMap e F.toFun b) := by
  funext σ
  simp only [coefficientSimplexMap, coefficientSimplexCup,
    Function.comp_apply, map_mul, Function.comp_def]
  exact F.map_mul _ _

theorem coefficientSimplexCup_assoc_zero
    {n : ℕ} {B : Type*} [Semigroup B]
    (a b c : CoefficientSimplexCochain n 0 B)
    (σ : SimplexVertexTuple n 0) :
    coefficientSimplexCup
        (coefficientSimplexCup a b) c σ =
      coefficientSimplexCup a
        (coefficientSimplexCup b c) σ := by
  simp only [coefficientSimplexCup]
  have hfront :
      (σ ∘ simplexFront 0 0) ∘ simplexFront 0 0 =
        σ ∘ simplexFront 0 0 := by
    funext i
    fin_cases i
    rfl
  have hback :
      (σ ∘ simplexBack 0 0) ∘ simplexBack 0 0 =
        σ ∘ simplexBack 0 0 := by
    funext i
    fin_cases i
    rfl
  have hmiddle :
      (σ ∘ simplexFront 0 0) ∘ simplexBack 0 0 =
        (σ ∘ simplexBack 0 0) ∘ simplexFront 0 0 := by
    funext i
    fin_cases i
    rfl
  rw [hfront, hback, hmiddle]
  exact mul_assoc _ _ _

theorem simplexFront_assoc_cast (p q r : ℕ) (i : Fin (p + 1)) :
    Fin.cast (by omega : p + (q + r) + 1 = (p + q) + r + 1)
        (simplexFront p (q + r) i) =
      simplexFront (p + q) r (simplexFront p q i) := by
  apply Fin.ext
  simp [simplexFront]

theorem simplexBack_assoc_cast (p q r : ℕ) (i : Fin (r + 1)) :
    Fin.cast (by omega : p + (q + r) + 1 = (p + q) + r + 1)
        (simplexBack p (q + r) (simplexBack q r i)) =
      simplexBack (p + q) r i := by
  apply Fin.ext
  simp [simplexBack]
  omega

theorem simplexMiddle_assoc_cast (p q r : ℕ) (i : Fin (q + 1)) :
    Fin.cast (by omega : p + (q + r) + 1 = (p + q) + r + 1)
        (simplexBack p (q + r) (simplexFront q r i)) =
      simplexFront (p + q) r (simplexBack p q i) := by
  apply Fin.ext
  simp [simplexFront, simplexBack]

/-- The Alexander--Whitney cup product on ordered simplex cochains. -/
noncomputable def simplexCup {n p q : ℕ} (a : SimplexCochain n p)
    (b : SimplexCochain n q) : SimplexCochain n (p + q) :=
  fun σ => a (σ ∘ simplexFront p q) * b (σ ∘ simplexBack p q)

@[simp] theorem simplexCup_apply {n p q : ℕ}
    (a : SimplexCochain n p) (b : SimplexCochain n q)
    (σ : Fin (p + q + 1) → Vertex n) :
    simplexCup a b σ =
      a (σ ∘ simplexFront p q) * b (σ ∘ simplexBack p q) := rfl

theorem bitWordSimplexMap_cup
    (T : BitWordStarData) {i j p q : ℕ} (hij : i ≤ j)
    (a : SimplexCochain i p) (b : SimplexCochain i q) :
    bitWordSimplexMap T hij (simplexCup a b) =
      simplexCup (bitWordSimplexMap T hij a)
        (bitWordSimplexMap T hij b) := by
  funext σ
  simp only [bitWordSimplexMap, simplexCochainPullback, simplexCup,
    Function.comp_apply, map_mul, Function.comp_def]

theorem simplexCup_add_left {n p q : ℕ}
    (a₁ a₂ : SimplexCochain n p) (b : SimplexCochain n q) :
    simplexCup (a₁ + a₂) b = simplexCup a₁ b + simplexCup a₂ b := by
  funext σ
  simp [simplexCup, add_mul]

theorem simplexCup_add_right {n p q : ℕ}
    (a : SimplexCochain n p) (b₁ b₂ : SimplexCochain n q) :
    simplexCup a (b₁ + b₂) = simplexCup a b₁ + simplexCup a b₂ := by
  funext σ
  simp [simplexCup, mul_add]

theorem simplexCup_smul_left {n p q : ℕ} (r : ℂ)
    (a : SimplexCochain n p) (b : SimplexCochain n q) :
    simplexCup (r • a) b = r • simplexCup a b := by
  funext σ
  simp [simplexCup, smul_eq_mul, mul_assoc]

theorem simplexCup_smul_right {n p q : ℕ} (r : ℂ)
    (a : SimplexCochain n p) (b : SimplexCochain n q) :
    simplexCup a (r • b) = r • simplexCup a b := by
  funext σ
  simp [simplexCup, smul_eq_mul, mul_assoc]

@[simp] theorem simplexCup_zero_left {n p q : ℕ}
    (b : SimplexCochain n q) :
    simplexCup (0 : SimplexCochain n p) b = 0 := by
  funext σ
  simp [simplexCup]

@[simp] theorem simplexCup_zero_right {n p q : ℕ}
    (a : SimplexCochain n p) :
    simplexCup a (0 : SimplexCochain n q) = 0 := by
  funext σ
  simp [simplexCup]

@[simp] theorem simplexCochainOf0_apply {n : ℕ} (f : Cochain0 n)
    (σ : Fin 1 → Vertex n) : simplexCochainOf0 f σ = f (σ 0) := rfl

@[simp] theorem simplexCochainOf1_apply {n : ℕ} (g : Cochain1 n)
    (σ : Fin 2 → Vertex n) : simplexCochainOf1 g σ = g (σ 0) (σ 1) := rfl

@[simp] theorem simplexCochainOf2_apply {n : ℕ} (h : Cochain2 n)
    (σ : Fin 3 → Vertex n) : simplexCochainOf2 h σ = h (σ 0) (σ 1) (σ 2) := rfl

@[simp] theorem simplexCochainOf3_apply {n : ℕ} (k : Cochain3 n)
    (σ : Fin 4 → Vertex n) : simplexCochainOf3 k σ = k (σ 0) (σ 1) (σ 2) (σ 3) := rfl

@[simp] theorem simplexCochainOf4_apply {n : ℕ} (q : Cochain4 n)
    (σ : Fin 5 → Vertex n) : simplexCochainOf4 q σ = q (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) := rfl

theorem simplexCup_zero_one {n : ℕ} (f : Cochain0 n) (g : Cochain1 n)
    (σ : Fin 2 → Vertex n) :
    simplexCup (simplexCochainOf0 f) (simplexCochainOf1 g) σ =
      cup01 f g (σ 0) (σ 1) := by
  rfl

theorem simplexCup_assoc_zero {n : ℕ}
    (f g h : SimplexCochain n 0) (σ : Fin 1 → Vertex n) :
    simplexCup (simplexCup f g) h σ =
      simplexCup f (simplexCup g h) σ := by
  simp only [simplexCup]
  have hfront :
      (σ ∘ simplexFront 0 0) ∘ simplexFront 0 0 =
        σ ∘ simplexFront 0 0 := by
    funext i
    fin_cases i
    rfl
  have hback :
      (σ ∘ simplexBack 0 0) ∘ simplexBack 0 0 =
        σ ∘ simplexBack 0 0 := by
    funext i
    fin_cases i
    rfl
  have hmiddle :
      (σ ∘ simplexFront 0 0) ∘ simplexBack 0 0 =
        (σ ∘ simplexBack 0 0) ∘ simplexFront 0 0 := by
    funext i
    fin_cases i
    rfl
  rw [hfront, hback, hmiddle]
  exact mul_assoc _ _ _

theorem simplexCup_assoc {n p q r : ℕ}
    (a : SimplexCochain n p) (b : SimplexCochain n q)
    (c : SimplexCochain n r) :
    simplexCup (simplexCup a b) c =
      simplexCochainTransport (Nat.add_assoc p q r).symm
        (simplexCup a (simplexCup b c)) := by
  funext σ
  simp [simplexCochainTransport, simplexCup, Function.comp_def, Nat.add_assoc]
  exact mul_assoc _ _ _

theorem simplexCup_assoc_eval {n p q r : ℕ}
    (a : SimplexCochain n p) (b : SimplexCochain n q)
    (c : SimplexCochain n r) (σ : Fin ((p + q) + r + 1) → Vertex n) :
    simplexCup (simplexCup a b) c σ =
      simplexCochainTransport (Nat.add_assoc p q r).symm
        (simplexCup a (simplexCup b c)) σ := by
  exact congrFun (simplexCup_assoc a b c) σ

theorem simplexCoboundary_cup_zero_zero_leibniz {n : ℕ}
    (f g : Cochain0 n) (σ : Fin 2 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf0 f) (simplexCochainOf0 g)) σ =
      simplexCup (simplexCochainOf1 (d0 f)) (simplexCochainOf0 g) σ +
        simplexCup (simplexCochainOf0 f) (simplexCochainOf1 (d0 g)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf0,
    simplexCochainOf1, d0, Fin.sum_univ_two, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_zero_one_leibniz {n : ℕ}
    (f : Cochain0 n) (g : Cochain1 n) (σ : Fin 3 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf0 f) (simplexCochainOf1 g)) σ =
      simplexCup (simplexCochainOf1 (d0 f)) (simplexCochainOf1 g) σ +
        simplexCup (simplexCochainOf0 f) (simplexCochainOf2 (d1 g)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf0,
    simplexCochainOf1, simplexCochainOf2, d0, d1,
    Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_zero_two_leibniz {n : ℕ}
    (f : Cochain0 n) (h : Cochain2 n) (σ : Fin 4 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf0 f) (simplexCochainOf2 h)) σ =
      simplexCup (simplexCochainOf1 (d0 f)) (simplexCochainOf2 h) σ +
        simplexCup (simplexCochainOf0 f) (simplexCochainOf3 (d2 h)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf0,
    simplexCochainOf1, simplexCochainOf2, simplexCochainOf3,
    d0, d2, Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_zero_three_leibniz {n : ℕ}
    (f : Cochain0 n) (k : Cochain3 n) (σ : Fin 5 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf0 f) (simplexCochainOf3 k)) σ =
      simplexCup (simplexCochainOf1 (d0 f)) (simplexCochainOf3 k) σ +
        simplexCup (simplexCochainOf0 f) (simplexCochainOf4 (d3 k)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf0,
    simplexCochainOf1, simplexCochainOf3, simplexCochainOf4,
    d0, d3, Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_zero_four_leibniz {n : ℕ}
    (f : Cochain0 n) (q : Cochain4 n) (σ : Fin 6 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf0 f) (simplexCochainOf4 q)) σ =
      simplexCup (simplexCochainOf1 (d0 f)) (simplexCochainOf4 q) σ +
        simplexCup (simplexCochainOf0 f)
          (simplexCoboundary (simplexCochainOf4 q)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf0,
    simplexCochainOf1, simplexCochainOf4, d0, d4,
    Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_one_zero_leibniz {n : ℕ}
    (a : Cochain1 n) (f : Cochain0 n) (σ : Fin 3 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf1 a) (simplexCochainOf0 f)) σ =
      simplexCup (simplexCoboundary (simplexCochainOf1 a))
          (simplexCochainOf0 f) σ -
        simplexCup (simplexCochainOf1 a)
          (simplexCoboundary (simplexCochainOf0 f)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf0,
    simplexCochainOf1, simplexCochainOf2, Fin.sum_univ_succ,
    sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_one_one_leibniz {n : ℕ}
    (a b : Cochain1 n) (σ : Fin 4 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf1 a) (simplexCochainOf1 b)) σ =
      simplexCup (simplexCochainOf2 (d1 a))
          (simplexCochainOf1 b) σ -
        simplexCup (simplexCochainOf1 a)
          (simplexCochainOf2 (d1 b)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf1,
    simplexCochainOf2, d1, Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_two_zero_leibniz {n : ℕ}
    (a : Cochain2 n) (f : Cochain0 n) (σ : Fin 4 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf2 a) (simplexCochainOf0 f)) σ =
      simplexCup (simplexCochainOf3 (d2 a))
          (simplexCochainOf0 f) σ +
        simplexCup (simplexCochainOf2 a)
          (simplexCoboundary (simplexCochainOf0 f)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf0,
    simplexCochainOf2, simplexCochainOf3, d2,
    Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_two_one_leibniz {n : ℕ}
    (a : Cochain2 n) (b : Cochain1 n) (σ : Fin 5 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf2 a) (simplexCochainOf1 b)) σ =
      simplexCup (simplexCochainOf3 (d2 a))
          (simplexCochainOf1 b) σ +
        simplexCup (simplexCochainOf2 a)
          (simplexCochainOf2 (d1 b)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf1,
    simplexCochainOf2, simplexCochainOf3, d1, d2,
    Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_two_two_leibniz {n : ℕ}
    (a b : Cochain2 n) (σ : Fin 6 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf2 a) (simplexCochainOf2 b)) σ =
      simplexCup (simplexCochainOf3 (d2 a))
          (simplexCochainOf2 b) σ +
        simplexCup (simplexCochainOf2 a)
          (simplexCochainOf3 (d2 b)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf2,
    simplexCochainOf3, d2, Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_three_zero_leibniz {n : ℕ}
    (a : Cochain3 n) (f : Cochain0 n) (σ : Fin 5 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf3 a) (simplexCochainOf0 f)) σ =
      simplexCup (simplexCochainOf4 (d3 a))
          (simplexCochainOf0 f) σ -
        simplexCup (simplexCochainOf3 a)
          (simplexCoboundary (simplexCochainOf0 f)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf0,
    simplexCochainOf3, simplexCochainOf4, d3,
    Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_three_one_leibniz {n : ℕ}
    (a : Cochain3 n) (b : Cochain1 n) (σ : Fin 6 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf3 a) (simplexCochainOf1 b)) σ =
      simplexCup (simplexCochainOf4 (d3 a))
          (simplexCochainOf1 b) σ -
        simplexCup (simplexCochainOf3 a)
          (simplexCochainOf2 (d1 b)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf1,
    simplexCochainOf2, simplexCochainOf3, simplexCochainOf4,
    d1, d3, Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_three_two_leibniz {n : ℕ}
    (a : Cochain3 n) (b : Cochain2 n) (σ : Fin 7 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf3 a) (simplexCochainOf2 b)) σ =
      simplexCup (simplexCochainOf4 (d3 a))
          (simplexCochainOf2 b) σ -
        simplexCup (simplexCochainOf3 a)
          (simplexCochainOf3 (d2 b)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf2,
    simplexCochainOf3, simplexCochainOf4, d2, d3,
    Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_cup_three_three_leibniz {n : ℕ}
    (a b : Cochain3 n) (σ : Fin 8 → Vertex n) :
    simplexCoboundary
        (simplexCup (simplexCochainOf3 a) (simplexCochainOf3 b)) σ =
      simplexCup (simplexCochainOf4 (d3 a))
          (simplexCochainOf3 b) σ -
        simplexCup (simplexCochainOf3 a)
          (simplexCochainOf4 (d3 b)) σ := by
  simp [simplexCoboundary, simplexCup, simplexCochainOf3,
    simplexCochainOf4, d3, Fin.sum_univ_succ, sub_eq_add_neg]
  noncomm_ring

theorem simplexCoboundary_of0 {n : ℕ} (f : Cochain0 n)
    (σ : Fin 2 → Vertex n) :
    simplexCoboundary (simplexCochainOf0 f) σ =
      d0 f (σ 0) (σ 1) := by
  simp [simplexCoboundary, simplexCochainOf0, d0, Fin.sum_univ_two,
    sub_eq_add_neg]

theorem simplexCoboundary_simplexCochainOf0 {n : ℕ} (f : Cochain0 n) :
    simplexCoboundary (simplexCochainOf0 f) =
      simplexCochainOf1 (d0 f) := by
  funext σ
  exact simplexCoboundary_of0 f σ

theorem simplexCoboundary_of1 {n : ℕ} (g : Cochain1 n)
    (σ : Fin 3 → Vertex n) :
    simplexCoboundary (simplexCochainOf1 g) σ =
      d1 g (σ 0) (σ 1) (σ 2) := by
  simp [simplexCoboundary, simplexCochainOf1, d1,
    Fin.sum_univ_succ, sub_eq_add_neg]
  abel

theorem simplexCoboundary_of2 {n : ℕ} (h : Cochain2 n)
    (σ : Fin 4 → Vertex n) :
    simplexCoboundary (simplexCochainOf2 h) σ =
      d2 h (σ 0) (σ 1) (σ 2) (σ 3) := by
  have h12 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := by rfl
  have h22 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := by rfl
  have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = (2 : Fin 4) := by rfl
  simp [simplexCoboundary, simplexCochainOf2, d2,
    Fin.sum_univ_succ, sub_eq_add_neg, h12, h22, h32]
  norm_num
  abel

theorem simplexCoboundary_simplexCochainOf1 {n : ℕ} (g : Cochain1 n) :
    simplexCoboundary (simplexCochainOf1 g) =
      simplexCochainOf2 (d1 g) := by
  funext σ
  exact simplexCoboundary_of1 g σ

theorem simplexCoboundary_of3 {n : ℕ} (k : Cochain3 n)
    (σ : Fin 5 → Vertex n) :
    simplexCoboundary (simplexCochainOf3 k) σ =
      d3 k (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) := by
  have h13 : Fin.succAbove (1 : Fin 5) (2 : Fin 4) = (3 : Fin 5) := by rfl
  have h23 : Fin.succAbove (2 : Fin 5) (2 : Fin 4) = (3 : Fin 5) := by rfl
  have h33 : Fin.succAbove (3 : Fin 5) (2 : Fin 4) = (2 : Fin 5) := by rfl
  have h43 : Fin.succAbove (4 : Fin 5) (2 : Fin 4) = (2 : Fin 5) := by rfl
  have h14 : Fin.succAbove (1 : Fin 5) (3 : Fin 4) = (4 : Fin 5) := by rfl
  have h24 : Fin.succAbove (2 : Fin 5) (3 : Fin 4) = (4 : Fin 5) := by rfl
  have h34 : Fin.succAbove (3 : Fin 5) (3 : Fin 4) = (4 : Fin 5) := by rfl
  have h44 : Fin.succAbove (4 : Fin 5) (3 : Fin 4) = (3 : Fin 5) := by rfl
  simp [simplexCoboundary, simplexCochainOf3, d3,
    Fin.sum_univ_succ, sub_eq_add_neg, h13, h23, h33, h43, h14, h24, h34, h44]
  norm_num
  abel

theorem simplexCoboundary_simplexCochainOf2 {n : ℕ} (h : Cochain2 n) :
    simplexCoboundary (simplexCochainOf2 h) =
      simplexCochainOf3 (d2 h) := by
  funext σ
  exact simplexCoboundary_of2 h σ

theorem simplexCoboundary_of4 {n : ℕ} (q : Cochain4 n)
    (σ : Fin 6 → Vertex n) :
    simplexCoboundary (simplexCochainOf4 q) σ =
      d4 q (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) := by
  simp [simplexCoboundary, simplexCochainOf4, d4,
    Fin.sum_univ_succ, sub_eq_add_neg]
  norm_num
  abel

theorem simplexCoboundary_simplexCochainOf3 {n : ℕ} (k : Cochain3 n) :
    simplexCoboundary (simplexCochainOf3 k) =
      simplexCochainOf4 (d3 k) := by
  funext σ
  exact simplexCoboundary_of3 k σ

def simplexCochainMap {Δ₁ Δ₂ : SimplexCategory} (n : ℕ) (f : Δ₁ ⟶ Δ₂) :
    simplexCochainModule n Δ₁ ⟶ simplexCochainModule n Δ₂ :=
  ModuleCat.ofHom
    { toFun := fun c σ => c (σ ∘ f.toOrderHom)
      map_add' := by intro c d; rfl
      map_smul' := by intro a c; rfl }

@[simp] theorem simplexCochainMap_apply
    {Δ₁ Δ₂ : SimplexCategory} (n : ℕ) (f : Δ₁ ⟶ Δ₂)
    (c : SimplexCochain n Δ₁.len)
    (σ : Fin (Δ₂.len + 1) → Vertex n) :
    (simplexCochainMap n f).hom c σ = c (σ ∘ f.toOrderHom) :=
  rfl

@[simp] theorem simplexCochainMap_id
    (n : ℕ) {Δ : SimplexCategory} :
    simplexCochainMap n (𝟙 Δ) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext c σ
  rfl

theorem simplexCochainMap_comp
    (n : ℕ) {Δ₁ Δ₂ Δ₃ : SimplexCategory}
    (f : Δ₁ ⟶ Δ₂) (g : Δ₂ ⟶ Δ₃) :
    simplexCochainMap n (f ≫ g) =
      simplexCochainMap n f ≫ simplexCochainMap n g := by
  apply ModuleCat.hom_ext
  ext c σ
  rfl

noncomputable def bitWordSimplexCochains (n : ℕ) :
    CosimplicialObject (ModuleCat ℂ) where
  obj Δ := simplexCochainModule n Δ
  map f := simplexCochainMap n f
  map_id := by
    intro Δ
    apply ModuleCat.hom_ext
    ext c σ
    rfl
  map_comp := by
    intro Δ₁ Δ₂ Δ₃ f g
    apply ModuleCat.hom_ext
    ext c σ
    rfl

@[simp] theorem bitWordSimplexCochains_δ_apply
    (n k : ℕ) (i : Fin (k + 2))
    (c : SimplexCochain n k)
    (σ : Fin (k + 2) → Vertex n) :
    ((bitWordSimplexCochains n).δ i).hom c σ =
      c (σ ∘ i.succAbove) := by
  rfl

theorem alternatingCofaceMap_apply
    (n k : ℕ) (c : SimplexCochain n k)
    (σ : Fin (k + 2) → Vertex n) :
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (bitWordSimplexCochains n) k).hom c σ =
      simplexCoboundary c σ := by
  have hface (i : Fin (k + 2)) :
      (⇑i.succAboveOrderEmb : Fin (k + 1) → Fin (k + 2)) = i.succAbove := by
    rfl
  simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    bitWordSimplexCochains, CosimplicialObject.δ, simplexCochainMap,
      simplexCoboundary, SimplexCategory.δ, Fin.succAbove,
    bitWordSimplexCochains_δ_apply, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, zsmul_eq_mul, hface]

theorem simplexCoboundary_squared
    (n k : ℕ) (c : SimplexCochain n k) :
    simplexCoboundary (simplexCoboundary c) = 0 := by
  funext σ
  have h := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
    (bitWordSimplexCochains n) k
  have h' := congrArg (fun f => f.hom c σ) h
  have hi : simplexCoboundary c =
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (bitWordSimplexCochains n) k).hom c := by
    funext τ
    exact (alternatingCofaceMap_apply n k c τ).symm
  rw [hi]
  rw [← alternatingCofaceMap_apply n (k + 1)
    ((AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (bitWordSimplexCochains n) k).hom c) σ]
  change ((AlgebraicTopology.AlternatingCofaceMapComplex.objD
    (bitWordSimplexCochains n) (k + 1)).hom
    ((AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (bitWordSimplexCochains n) k).hom c)) σ = 0 at h'
  exact h'

theorem d1_d0_generic {n : ℕ} (f : Cochain0 n)
    (σ : Fin 3 → Vertex n) :
    d1 (d0 f) (σ 0) (σ 1) (σ 2) = 0 := by
  have h := simplexCoboundary_squared n 0 (simplexCochainOf0 f)
  have hσ := congrFun h σ
  rw [simplexCoboundary_simplexCochainOf0] at hσ
  rw [simplexCoboundary_of1] at hσ
  exact hσ

theorem d2_d1_generic {n : ℕ} (g : Cochain1 n)
    (σ : Fin 4 → Vertex n) :
    d2 (d1 g) (σ 0) (σ 1) (σ 2) (σ 3) = 0 := by
  have h := simplexCoboundary_squared n 1 (simplexCochainOf1 g)
  have hσ := congrFun h σ
  rw [simplexCoboundary_simplexCochainOf1] at hσ
  rw [simplexCoboundary_of2] at hσ
  exact hσ

theorem d3_d2_generic {n : ℕ} (h : Cochain2 n)
    (σ : Fin 5 → Vertex n) :
    d3 (d2 h) (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) = 0 := by
  have hsq := simplexCoboundary_squared n 2 (simplexCochainOf2 h)
  have hσ := congrFun hsq σ
  rw [simplexCoboundary_simplexCochainOf2] at hσ
  rw [simplexCoboundary_of3] at hσ
  exact hσ

theorem d4_d3_generic {n : ℕ} (k : Cochain3 n)
    (σ : Fin 6 → Vertex n) :
    d4 (d3 k) (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) (σ 5) = 0 := by
  have hsq := simplexCoboundary_squared n 3 (simplexCochainOf3 k)
  have hσ := congrFun hsq σ
  rw [simplexCoboundary_simplexCochainOf3] at hσ
  rw [simplexCoboundary_of4] at hσ
  exact hσ

end InfoGeometry.Canonical.BitWordGraphDifferential
