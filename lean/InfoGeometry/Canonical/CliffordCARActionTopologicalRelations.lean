import InfoGeometry.Canonical.CliffordCARGeneratorTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological readout of the finite-stage CAR action profile

The Jordan--Wigner tower already proves the four cross-site CAR identities for
the matrix generators.  This owner transports those identities to left
multiplication operators, which are continuous linear maps on each finite
stage, and exposes the maps as `TopCat` morphisms.  Only cross-site relations
are asserted here; the same-site CAR relation belongs to the finite-stage
generator owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.CliffordCARActionTopologicalRelations

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
open InfoGeometry.Canonical.CliffordCARGeneratorTopological

abbrev TStage (n : ℕ) : Type := CliffordCARGeneratorTopological.TStage n

/-! ## TopCat action morphisms -/

def creationActionTopCat (n : ℕ) (k : Fin n) :
    TopCat.of (TStage n) ⟶ TopCat.of (TStage n) :=
  TopCat.ofHom
    { toFun := creationLeftAction n k
      continuous_toFun := (creationLeftAction n k).continuous }

def annihilationActionTopCat (n : ℕ) (k : Fin n) :
    TopCat.of (TStage n) ⟶ TopCat.of (TStage n) :=
  TopCat.ofHom
    { toFun := annihilationLeftAction n k
      continuous_toFun := (annihilationLeftAction n k).continuous }

/-! The bonding morphism used in the same `TopCat` diagram. -/

def bondTopCat (m n : ℕ) (h : m ≤ n) :
    TopCat.of (TStage m) ⟶ TopCat.of (TStage n) :=
  CliffordCARTopologicalColimit.topologicalDiagram.map (homOfLE h)

theorem bondAlgHom_jwCreation
    (m n : ℕ) (h : m ≤ n) (k : Fin m) :
    bondAlgHom m n h (jwCreation m k) =
      jwCreation n (Fin.castLE h k) := by
  induction h with
  | refl => simp [bondAlgHom_refl]
  | @step n h ih =>
    rw [bondAlgHom_succ]
    simp [ih, stageEmbed_apply, matStageEmbed_jwCreation]
    all_goals exact h

theorem bondAlgHom_jwAnnihilation
    (m n : ℕ) (h : m ≤ n) (k : Fin m) :
    bondAlgHom m n h (jwAnnihilation m k) =
      jwAnnihilation n (Fin.castLE h k) := by
  induction h with
  | refl => simp [bondAlgHom_refl]
  | @step n h ih =>
    rw [bondAlgHom_succ]
    simp [ih, stageEmbed_apply, matStageEmbed_jwAnnihilation]
    all_goals exact h

theorem creationLeftAction_bond_naturality
    (m n : ℕ) (h : m ≤ n) (k : Fin m) (A : TStage m) :
    bondCLM m n h (creationLeftAction m k A) =
      creationLeftAction n (Fin.castLE h k) (bondCLM m n h A) := by
  change bondAlgHom m n h (jwCreation m k * A) =
    jwCreation n (Fin.castLE h k) * bondAlgHom m n h A
  rw [map_mul, bondAlgHom_jwCreation m n h k]

theorem annihilationLeftAction_bond_naturality
    (m n : ℕ) (h : m ≤ n) (k : Fin m) (A : TStage m) :
    bondCLM m n h (annihilationLeftAction m k A) =
      annihilationLeftAction n (Fin.castLE h k) (bondCLM m n h A) := by
  change bondAlgHom m n h (jwAnnihilation m k * A) =
    jwAnnihilation n (Fin.castLE h k) * bondAlgHom m n h A
  rw [map_mul, bondAlgHom_jwAnnihilation m n h k]

@[simp] theorem creationActionTopCat_apply (n : ℕ) (k : Fin n) (A : TStage n) :
    creationActionTopCat n k A = creationLeftAction n k A := rfl

@[simp] theorem annihilationActionTopCat_apply (n : ℕ) (k : Fin n) (A : TStage n) :
    annihilationActionTopCat n k A = annihilationLeftAction n k A := rfl

theorem creationActionTopCat_naturality (n : ℕ) (k : Fin n) (A : TStage n) :
    creationActionTopCat (n + 1) k.castSucc
        (bondTopCat n (n + 1) (Nat.le_succ n) A) =
      bondTopCat n (n + 1) (Nat.le_succ n)
        (creationActionTopCat n k A) := by
  change creationLeftAction (n + 1) k.castSucc
      (bondCLM n (n + 1) (Nat.le_succ n) A) =
    bondCLM n (n + 1) (Nat.le_succ n)
      (creationLeftAction n k A)
  exact (creationLeftAction_transition n k A).symm

theorem annihilationActionTopCat_naturality (n : ℕ) (k : Fin n) (A : TStage n) :
    annihilationActionTopCat (n + 1) k.castSucc
        (bondTopCat n (n + 1) (Nat.le_succ n) A) =
      bondTopCat n (n + 1) (Nat.le_succ n)
        (annihilationActionTopCat n k A) := by
  change annihilationLeftAction (n + 1) k.castSucc
      (bondCLM n (n + 1) (Nat.le_succ n) A) =
    bondCLM n (n + 1) (Nat.le_succ n)
      (annihilationLeftAction n k A)
  exact (annihilationLeftAction_transition n k A).symm

theorem creationActionTopCat_naturality_hom (n : ℕ) (k : Fin n) :
    creationActionTopCat n k ≫ bondTopCat n (n + 1) (Nat.le_succ n) =
      bondTopCat n (n + 1) (Nat.le_succ n) ≫
        creationActionTopCat (n + 1) k.castSucc := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change bondCLM n (n + 1) (Nat.le_succ n)
      (creationLeftAction n k A) =
    creationLeftAction (n + 1) k.castSucc
      (bondCLM n (n + 1) (Nat.le_succ n) A)
  exact creationLeftAction_transition n k A

theorem annihilationActionTopCat_naturality_hom (n : ℕ) (k : Fin n) :
    annihilationActionTopCat n k ≫ bondTopCat n (n + 1) (Nat.le_succ n) =
      bondTopCat n (n + 1) (Nat.le_succ n) ≫
        annihilationActionTopCat (n + 1) k.castSucc := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change bondCLM n (n + 1) (Nat.le_succ n)
      (annihilationLeftAction n k A) =
    annihilationLeftAction (n + 1) k.castSucc
      (bondCLM n (n + 1) (Nat.le_succ n) A)
  exact annihilationLeftAction_transition n k A

/-! ## Upper-tail diagrams and descended TopCat actions -/

abbrev UpperNatIndex (m : ℕ) := {n : ℕ // m + 1 ≤ n}

def upperCARTopologicalDiagram (m : ℕ) :
    UpperNatIndex m ⥤ TopCat where
  obj j := TopCat.of (TStage j.1)
  map f := bondTopCat _ _ (leOfHom f)
  map_id j := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    change bondCLM j.1 j.1 (leOfHom (𝟙 j)) A = A
    rw [bondCLM_apply, bondAlgHom_refl]
    rfl
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    change bondCLM _ _ (leOfHom (f ≫ g)) A =
      bondCLM _ _ (leOfHom g)
        (bondCLM _ _ (leOfHom f) A)
    rw [bondCLM_apply, bondCLM_apply, bondCLM_apply]
    exact congrArg (fun e => e A)
      (bondAlgHom_trans _ _ _ (leOfHom f) (leOfHom g))

def upperCreationActionNatTrans (m : ℕ) :
    upperCARTopologicalDiagram m ⟶ upperCARTopologicalDiagram m where
  app j := creationActionTopCat j.1
    (Fin.castLE j.2 ⟨m, Nat.lt_succ_self m⟩)
  naturality := by
    intro j k f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    have h := creationLeftAction_bond_naturality
      j.1 k.1 (leOfHom f)
      (Fin.castLE j.2 ⟨m, Nat.lt_succ_self m⟩) A
    have hindex :
        Fin.castLE (leOfHom f)
            (Fin.castLE j.2 ⟨m, Nat.lt_succ_self m⟩) =
          Fin.castLE k.2 ⟨m, Nat.lt_succ_self m⟩ := by
      apply Fin.ext
      rfl
    simpa [upperCARTopologicalDiagram, bondTopCat, topologicalDiagram,
      creationActionTopCat, TopCat.ofHom, hindex] using h.symm

def upperAnnihilationActionNatTrans (m : ℕ) :
    upperCARTopologicalDiagram m ⟶ upperCARTopologicalDiagram m where
  app j := annihilationActionTopCat j.1
    (Fin.castLE j.2 ⟨m, Nat.lt_succ_self m⟩)
  naturality := by
    intro j k f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    have h := annihilationLeftAction_bond_naturality
      j.1 k.1 (leOfHom f)
      (Fin.castLE j.2 ⟨m, Nat.lt_succ_self m⟩) A
    have hindex :
        Fin.castLE (leOfHom f)
            (Fin.castLE j.2 ⟨m, Nat.lt_succ_self m⟩) =
          Fin.castLE k.2 ⟨m, Nat.lt_succ_self m⟩ := by
      apply Fin.ext
      rfl
    simpa [upperCARTopologicalDiagram, bondTopCat, topologicalDiagram,
      annihilationActionTopCat, TopCat.ofHom, hindex] using h.symm

abbrev upperCARTopologicalColimit (m : ℕ) : TopCat :=
  topologicalDirectColimit (upperCARTopologicalDiagram m)

noncomputable def upperCreationActionColimit (m : ℕ) :
    upperCARTopologicalColimit m ⟶ upperCARTopologicalColimit m :=
  colim.map (upperCreationActionNatTrans m)

noncomputable def upperAnnihilationActionColimit (m : ℕ) :
    upperCARTopologicalColimit m ⟶ upperCARTopologicalColimit m :=
  colim.map (upperAnnihilationActionNatTrans m)

def upperCARTopologicalInjection (m : ℕ) (j : UpperNatIndex m) :
    (upperCARTopologicalDiagram m).obj j ⟶ upperCARTopologicalColimit m :=
  topologicalDirectInjection (upperCARTopologicalDiagram m) j

theorem upperCreationActionColimit_stage (m : ℕ) (j : UpperNatIndex m) :
    upperCARTopologicalInjection m j ≫ upperCreationActionColimit m =
      (upperCreationActionNatTrans m).app j ≫
        upperCARTopologicalInjection m j := by
  exact colimit.ι_map (upperCreationActionNatTrans m) j

theorem upperAnnihilationActionColimit_stage (m : ℕ) (j : UpperNatIndex m) :
    upperCARTopologicalInjection m j ≫ upperAnnihilationActionColimit m =
      (upperAnnihilationActionNatTrans m).app j ≫
        upperCARTopologicalInjection m j := by
  exact colimit.ι_map (upperAnnihilationActionNatTrans m) j

theorem upperCreationActionColimit_stage_apply
    (m : ℕ) (j : UpperNatIndex m) (A : TStage j.1) :
    upperCreationActionColimit m (upperCARTopologicalInjection m j A) =
      upperCARTopologicalInjection m j
        (jwCreation j.1 (Fin.castLE j.2 ⟨m, Nat.lt_succ_self m⟩) * A) := by
  have h := upperCreationActionColimit_stage m j
  have hv := congrArg (fun f => f A) h
  simpa [upperCreationActionColimit, upperCARTopologicalInjection,
    upperCreationActionNatTrans, creationActionTopCat, TopCat.ofHom] using hv

theorem upperAnnihilationActionColimit_stage_apply
    (m : ℕ) (j : UpperNatIndex m) (A : TStage j.1) :
    upperAnnihilationActionColimit m (upperCARTopologicalInjection m j A) =
      upperCARTopologicalInjection m j
        (jwAnnihilation j.1 (Fin.castLE j.2 ⟨m, Nat.lt_succ_self m⟩) * A) := by
  have h := upperAnnihilationActionColimit_stage m j
  have hv := congrArg (fun f => f A) h
  simpa [upperAnnihilationActionColimit, upperCARTopologicalInjection,
    upperAnnihilationActionNatTrans, annihilationActionTopCat, TopCat.ofHom] using hv

/-! ## Continuous-linear cross-site CAR identities -/

theorem creation_creation_cross_site_action_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (creationLeftAction n i).comp (creationLeftAction n j) +
        (creationLeftAction n j).comp (creationLeftAction n i) = 0 := by
  apply ContinuousLinearMap.ext
  intro A
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  change jwCreation n i * (jwCreation n j * A) +
      jwCreation n j * (jwCreation n i * A) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    creation_cross_site_anticommute n i j hij, zero_mul]

theorem annihilation_annihilation_cross_site_action_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (annihilationLeftAction n i).comp (annihilationLeftAction n j) +
        (annihilationLeftAction n j).comp (annihilationLeftAction n i) = 0 := by
  apply ContinuousLinearMap.ext
  intro A
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  change jwAnnihilation n i * (jwAnnihilation n j * A) +
      jwAnnihilation n j * (jwAnnihilation n i * A) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    annihilation_cross_site_anticommute n i j hij, zero_mul]

theorem creation_annihilation_cross_site_action_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (creationLeftAction n i).comp (annihilationLeftAction n j) +
        (annihilationLeftAction n j).comp (creationLeftAction n i) = 0 := by
  apply ContinuousLinearMap.ext
  intro A
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  change jwCreation n i * (jwAnnihilation n j * A) +
      jwAnnihilation n j * (jwCreation n i * A) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    creation_annihilation_cross_site_anticommute n i j hij, zero_mul]

theorem annihilation_creation_cross_site_action_anticommute
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (annihilationLeftAction n i).comp (creationLeftAction n j) +
        (creationLeftAction n j).comp (annihilationLeftAction n i) = 0 := by
  apply ContinuousLinearMap.ext
  intro A
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  change jwAnnihilation n i * (jwCreation n j * A) +
      jwCreation n j * (jwAnnihilation n i * A) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul,
    annihilation_creation_cross_site_anticommute n i j hij, zero_mul]

/-! ## A reusable finite-stage profile -/

structure CrossSiteCARActionProfile (n : ℕ) where
  creation_creation : ∀ (i j : Fin n), i ≠ j →
    (creationLeftAction n i).comp (creationLeftAction n j) +
        (creationLeftAction n j).comp (creationLeftAction n i) = 0
  annihilation_annihilation : ∀ (i j : Fin n), i ≠ j →
    (annihilationLeftAction n i).comp (annihilationLeftAction n j) +
        (annihilationLeftAction n j).comp (annihilationLeftAction n i) = 0
  creation_annihilation : ∀ (i j : Fin n), i ≠ j →
    (creationLeftAction n i).comp (annihilationLeftAction n j) +
        (annihilationLeftAction n j).comp (creationLeftAction n i) = 0
  annihilation_creation : ∀ (i j : Fin n), i ≠ j →
    (annihilationLeftAction n i).comp (creationLeftAction n j) +
        (creationLeftAction n j).comp (annihilationLeftAction n i) = 0

def crossSiteCARActionProfile (n : ℕ) : CrossSiteCARActionProfile n where
  creation_creation := creation_creation_cross_site_action_anticommute n
  annihilation_annihilation := annihilation_annihilation_cross_site_action_anticommute n
  creation_annihilation := creation_annihilation_cross_site_action_anticommute n
  annihilation_creation := annihilation_creation_cross_site_action_anticommute n

end InfoGeometry.Canonical.CliffordCARActionTopologicalRelations
