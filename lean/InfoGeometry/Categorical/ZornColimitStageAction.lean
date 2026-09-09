import InfoGeometry.Categorical.ZornUHFColimit

/-! Concrete transport of stagewise endomorphisms to the Zorn colimit.

The action is supplied as a natural transformation of the existing
`zornStageFunctor`; no new colimit carrier or multiplication is introduced.
-/

noncomputable section

namespace InfoGeometry.Categorical.ZornUHFColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Physics.YangBaxterZornBridge

/-- The endomorphism of the concrete Zorn colimit induced by a compatible
stagewise linear transformation. -/
def zornColimitEnd (s : zornStageFunctor ⟶ zornStageFunctor) :
    Module.End ℂ ZornColimit :=
  (colim.map s).hom

/-- Apply an 8-dimensional linear operator independently at every finite
stage coordinate. -/
def zornStagePointwise (M : Matrix (Fin 8) (Fin 8) ℂ) (n : ℕ) :
    ZornStage n →ₗ[ℂ] ZornStage n where
  toFun x w := (Matrix.toLin' M) (x w)
  map_add' x y := by
    funext w
    exact (Matrix.toLin' M).map_add (x w) (y w)
  map_smul' c x := by
    funext w
    exact (Matrix.toLin' M).map_smul c (x w)

@[simp] theorem zornStagePointwise_apply
    (M : Matrix (Fin 8) (Fin 8) ℂ) (n : ℕ) (x : ZornStage n)
    (w : BitWord n) :
    zornStagePointwise M n x w = (Matrix.toLin' M) (x w) := rfl

theorem zornStagePointwise_comp
    (M N : Matrix (Fin 8) (Fin 8) ℂ) (n : ℕ) :
    zornStagePointwise M n ∘ₗ zornStagePointwise N n =
      zornStagePointwise (M * N) n := by
  ext x w
  simp [Matrix.toLin'_mul]

/-- The pointwise operator is compatible with every prefix bonding map. -/
theorem zornStagePointwise_natural
    (M : Matrix (Fin 8) (Fin 8) ℂ) {n m : ℕ} (f : n ⟶ m) :
    zornStageFunctor.map f ≫ ModuleCat.ofHom (zornStagePointwise M m) =
      ModuleCat.ofHom (zornStagePointwise M n) ≫ zornStageFunctor.map f := by
  ext x w
  rfl

/-- The pointwise operators form a natural transformation of the concrete
Zorn stage diagram. -/
def zornStagePointwiseNatTrans (M : Matrix (Fin 8) (Fin 8) ℂ) :
    zornStageFunctor ⟶ zornStageFunctor where
  app n := ModuleCat.ofHom (zornStagePointwise M n)
  naturality _ _ f := zornStagePointwise_natural M f

theorem zornStagePointwiseNatTrans_comp
    (M N : Matrix (Fin 8) (Fin 8) ℂ) :
    zornStagePointwiseNatTrans N ≫ zornStagePointwiseNatTrans M =
      zornStagePointwiseNatTrans (M * N) := by
  ext n x
  funext w
  exact congrArg (fun q => q w)
    (LinearMap.congr_fun (zornStagePointwise_comp M N n) x)

@[simp] theorem zornColimitEnd_on_stage
    (s : zornStageFunctor ⟶ zornStageFunctor) (n : ℕ) (x : ZornStage n) :
    zornColimitEnd s ((colimit.ι zornStageFunctor n).hom x) =
      (colimit.ι zornStageFunctor n).hom ((s.app n).hom x) := by
  exact congrArg (fun f => f x) (colimit.ι_map s n)

/-! The two concrete Yang--Baxter/Zorn generators now act on every stage. -/

def zornBraidGeneratorStage1 : zornStageFunctor ⟶ zornStageFunctor :=
  zornStagePointwiseNatTrans braidGen1.val

def zornBraidGeneratorStage2 : zornStageFunctor ⟶ zornStageFunctor :=
  zornStagePointwiseNatTrans braidGen2.val

def zornBraidGeneratorColimit1 : Module.End ℂ ZornColimit :=
  zornColimitEnd zornBraidGeneratorStage1

def zornBraidGeneratorColimit2 : Module.End ℂ ZornColimit :=
  zornColimitEnd zornBraidGeneratorStage2

theorem zornBraidStage_braid_relation :
    zornBraidGeneratorStage1 ≫ zornBraidGeneratorStage2 ≫
        zornBraidGeneratorStage1 =
      zornBraidGeneratorStage2 ≫ zornBraidGeneratorStage1 ≫
        zornBraidGeneratorStage2 := by
  have hmatrix : braidGen1.val * braidGen2.val * braidGen1.val =
      braidGen2.val * braidGen1.val * braidGen2.val := by
    exact congrArg Units.val braidGen_B3_braid
  ext n x
  funext w
  funext i
  change braidGen1.val.mulVec (braidGen2.val.mulVec
      (braidGen1.val.mulVec (x w))) i =
    braidGen2.val.mulVec (braidGen1.val.mulVec
      (braidGen2.val.mulVec (x w))) i
  have hlin := congrArg Matrix.toLin' hmatrix
  have hx := LinearMap.congr_fun hlin (x w)
  simpa [Matrix.toLin'_mul] using congrArg (fun q => q i) hx

@[simp] theorem zornBraidGeneratorColimit1_on_stage
    (n : ℕ) (x : ZornStage n) :
    zornBraidGeneratorColimit1 ((colimit.ι zornStageFunctor n).hom x) =
      (colimit.ι zornStageFunctor n).hom
        ((zornStagePointwise braidGen1.val n) x) := by
  exact zornColimitEnd_on_stage zornBraidGeneratorStage1 n x

@[simp] theorem zornBraidGeneratorColimit2_on_stage
    (n : ℕ) (x : ZornStage n) :
    zornBraidGeneratorColimit2 ((colimit.ι zornStageFunctor n).hom x) =
      (colimit.ι zornStageFunctor n).hom
        ((zornStagePointwise braidGen2.val n) x) := by
  exact zornColimitEnd_on_stage zornBraidGeneratorStage2 n x

theorem zornColimitEnd_comp
    (s t : zornStageFunctor ⟶ zornStageFunctor) :
    zornColimitEnd t * zornColimitEnd s = zornColimitEnd (s ≫ t) := by
  have hmap : colim.map s ≫ colim.map t = colim.map (s ≫ t) := by
    rw [← colim.map_comp]
  simpa [zornColimitEnd, Module.End.mul_apply] using
    congrArg ModuleCat.Hom.hom hmap

theorem zornBraidColimit_braid_relation :
    zornBraidGeneratorColimit1 * zornBraidGeneratorColimit2 *
        zornBraidGeneratorColimit1 =
      zornBraidGeneratorColimit2 * zornBraidGeneratorColimit1 *
        zornBraidGeneratorColimit2 := by
  change zornColimitEnd zornBraidGeneratorStage1 *
      zornColimitEnd zornBraidGeneratorStage2 *
        zornColimitEnd zornBraidGeneratorStage1 =
      zornColimitEnd zornBraidGeneratorStage2 *
        zornColimitEnd zornBraidGeneratorStage1 *
          zornColimitEnd zornBraidGeneratorStage2
  rw [zornColimitEnd_comp, zornColimitEnd_comp,
    zornColimitEnd_comp, zornColimitEnd_comp]
  exact congrArg zornColimitEnd zornBraidStage_braid_relation

@[simp] theorem zornColimitEnd_id :
    zornColimitEnd (𝟙 zornStageFunctor) = LinearMap.id := by
  have hmap : colim.map (𝟙 zornStageFunctor) = 𝟙 (colimit zornStageFunctor) :=
    colim.map_id zornStageFunctor
  simpa [zornColimitEnd] using congrArg ModuleCat.Hom.hom hmap

end InfoGeometry.Categorical.ZornUHFColimit
