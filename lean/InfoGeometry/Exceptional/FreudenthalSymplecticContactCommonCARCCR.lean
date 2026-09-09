import InfoGeometry.Exceptional.FreudenthalSymplecticContactGrading

noncomputable section
namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

abbrev SymplecticContactSheet :=
  SymplecticContactModule (J := J) × SymplecticContactModule (J := J)
abbrev SymplecticContactCommonCarrier := ℕ → SymplecticContactSheet (J := J)
abbrev SymplecticContactCommonEnd :=
  Module.End ℝ (SymplecticContactCommonCarrier (J := J))

def contactFermionAnnihilation : SymplecticContactCommonEnd (J := J) where
  toFun ψ n := ((ψ n).2, 0)
  map_add' := by intro ψ φ; funext n; simp
  map_smul' := by intro c ψ; funext n; simp

def contactFermionCreation : SymplecticContactCommonEnd (J := J) where
  toFun ψ n := (0, (ψ n).1)
  map_add' := by intro ψ φ; funext n; simp
  map_smul' := by intro c ψ; funext n; simp

@[simp] theorem contactFermionAnnihilation_sq :
    contactFermionAnnihilation (J := J) * contactFermionAnnihilation = 0 := by
  apply LinearMap.ext; intro ψ; funext n
  rfl

@[simp] theorem contactFermionCreation_sq :
    contactFermionCreation (J := J) * contactFermionCreation = 0 := by
  apply LinearMap.ext; intro ψ; funext n
  rfl

theorem contactFermion_CAR :
    contactFermionAnnihilation (J := J) * contactFermionCreation +
      contactFermionCreation * contactFermionAnnihilation = 1 := by
  apply LinearMap.ext; intro ψ; funext n
  rcases ψ n with ⟨x, y⟩
  simp [contactFermionAnnihilation, contactFermionCreation,
    Module.End.mul_apply]

def contactBosonCreation : SymplecticContactCommonEnd (J := J) where
  toFun ψ n := match n with | 0 => 0 | k + 1 => ψ k
  map_add' := by intro ψ φ; funext n; cases n <;> simp
  map_smul' := by intro c ψ; funext n; cases n <;> simp

def contactBosonAnnihilation : SymplecticContactCommonEnd (J := J) where
  toFun ψ n := ((n + 1 : ℕ) : ℝ) • ψ (n + 1)
  map_add' := by intro ψ φ; funext n; simp [smul_add]
  map_smul' := by
    intro c ψ; funext n
    simp only [Pi.smul_apply, smul_smul]
    simpa [mul_comm]

theorem contactBoson_CCR :
    contactBosonAnnihilation (J := J) * contactBosonCreation -
      contactBosonCreation * contactBosonAnnihilation = 1 := by
  apply LinearMap.ext; intro ψ; funext n
  simp only [LinearMap.sub_apply, Module.End.mul_apply]
  change contactBosonAnnihilation (contactBosonCreation ψ) n -
      contactBosonCreation (contactBosonAnnihilation ψ) n = ψ n
  cases n with
  | zero => simp [contactBosonAnnihilation, contactBosonCreation]
  | succ n =>
      change (((n + 2 : ℕ) : ℝ) • ψ (n + 1)) -
        (((n + 1 : ℕ) : ℝ) • ψ (n + 1)) = ψ (n + 1)
      rw [← sub_smul]
      have h : (((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) = 1 := by norm_num
      rw [h, one_smul]

theorem contactFermionAnnihilation_commutes_bosonCreation :
    contactFermionAnnihilation (J := J) * contactBosonCreation =
      contactBosonCreation * contactFermionAnnihilation := by
  apply LinearMap.ext; intro ψ; funext n; cases n <;>
    rfl

theorem contactFermionCreation_commutes_bosonCreation :
    contactFermionCreation (J := J) * contactBosonCreation =
      contactBosonCreation * contactFermionCreation := by
  apply LinearMap.ext; intro ψ; funext n; cases n <;> rfl

def symplecticContactCommonLift
    (T : SymplecticContactEnd (J := J)) :
    SymplecticContactCommonEnd (J := J) where
  toFun ψ n := (T (ψ n).1, T (ψ n).2)
  map_add' := by
    intro ψ φ; funext n
    exact Prod.ext (T.map_add _ _) (T.map_add _ _)
  map_smul' := by
    intro c ψ; funext n
    exact Prod.ext (T.map_smul c _) (T.map_smul c _)

@[simp] theorem symplecticContactCommonLift_apply
    (T : SymplecticContactEnd (J := J))
    (ψ : SymplecticContactCommonCarrier (J := J)) (n : ℕ) :
    symplecticContactCommonLift T ψ n =
      (T (ψ n).1, T (ψ n).2) := rfl

theorem symplecticContactCommonLift_mul
    (S T : SymplecticContactEnd (J := J)) :
    symplecticContactCommonLift (S * T) =
      symplecticContactCommonLift S * symplecticContactCommonLift T := by
  apply LinearMap.ext; intro ψ; funext n
  rfl

theorem symplecticContactCommonLift_injective :
    Function.Injective (symplecticContactCommonLift (J := J)) := by
  intro S T hST
  apply LinearMap.ext
  intro x
  let ψ : SymplecticContactCommonCarrier (J := J) := fun _ => (x, 0)
  have h0 := congrArg
    (fun F : SymplecticContactCommonEnd (J := J) => F ψ 0) hST
  simpa [symplecticContactCommonLift, ψ] using
    congrArg (fun q => q.1) h0

theorem symplecticContactCommonLift_commutes_fermionAnnihilation
    (T : SymplecticContactEnd (J := J)) :
    symplecticContactCommonLift T * contactFermionAnnihilation =
      contactFermionAnnihilation * symplecticContactCommonLift T := by
  apply LinearMap.ext; intro ψ; funext n
  simp [Module.End.mul_apply, symplecticContactCommonLift,
    contactFermionAnnihilation]

theorem symplecticContactCommonLift_commutes_fermionCreation
    (T : SymplecticContactEnd (J := J)) :
    symplecticContactCommonLift T * contactFermionCreation =
      contactFermionCreation * symplecticContactCommonLift T := by
  apply LinearMap.ext; intro ψ; funext n
  simp [Module.End.mul_apply, symplecticContactCommonLift,
    contactFermionCreation]

theorem symplecticContactCommonLift_commutes_bosonCreation
    (T : SymplecticContactEnd (J := J)) :
    symplecticContactCommonLift T * contactBosonCreation =
      contactBosonCreation * symplecticContactCommonLift T := by
  apply LinearMap.ext; intro ψ; funext n; cases n <;>
    simp [Module.End.mul_apply, symplecticContactCommonLift,
      contactBosonCreation]

theorem symplecticContactCommonLift_commutes_bosonAnnihilation
    (T : SymplecticContactEnd (J := J)) :
    symplecticContactCommonLift T * contactBosonAnnihilation =
      contactBosonAnnihilation * symplecticContactCommonLift T := by
  apply LinearMap.ext; intro ψ; funext n
  simp [Module.End.mul_apply, symplecticContactCommonLift,
      contactBosonAnnihilation]

def symplecticContactCommonLiftLinear :
    SymplecticContactEnd (J := J) →ₗ[ℝ]
      SymplecticContactCommonEnd (J := J) where
  toFun T := symplecticContactCommonLift T
  map_add' S T := by
    apply LinearMap.ext; intro ψ; funext n; rfl
  map_smul' c T := by
    apply LinearMap.ext; intro ψ; funext n; rfl

def symplecticContactCommonLiftLieHom :
    SymplecticContactEnd (J := J) →ₗ⁅ℝ⁆
      SymplecticContactCommonEnd (J := J) where
  toLinearMap := symplecticContactCommonLiftLinear (J := J)
  map_lie' := by
    intro S T
    change symplecticContactCommonLiftLinear (S * T - T * S) =
      symplecticContactCommonLift S * symplecticContactCommonLift T -
        symplecticContactCommonLift T * symplecticContactCommonLift S
    rw [map_sub]
    change symplecticContactCommonLift (S * T) -
      symplecticContactCommonLift (T * S) = _
    rw [symplecticContactCommonLift_mul,
      symplecticContactCommonLift_mul]

theorem symplecticContactCommonLiftLieHom_injective :
    Function.Injective (symplecticContactCommonLiftLieHom (J := J)) := by
  intro S T h
  apply symplecticContactCommonLift_injective (J := J)
  exact congrArg (fun L => L) h

end InfoGeometry.Exceptional.Freudenthal
