import Mathlib

noncomputable section

universe u v w

/-- The finite `n`-sector is the type of functions from `Fin n` into `H`. -/
def FockSym (n : ℕ) (H : Type u) : Type u := Fin n → H

/-- A finite-sector Fock object records its sector number and its sector vector. -/
def BosonicFockSpace (H : Type u) : Type u := Σ n : ℕ, FockSym n H

/-- Apply a function coordinatewise on a finite sector. -/
def sectorMap {H : Type u} {K : Type v} {n : ℕ} (f : H → K) (φ : FockSym n H) :
    FockSym n K :=
  fun i => f (φ i)

/-- Add one final coordinate to a finite sector. -/
def raiseSector {H : Type u} {n : ℕ} (η : H) (φ : FockSym n H) :
    FockSym (n + 1) H :=
  fun i =>
    if h : (i : ℕ) < n then
      φ ⟨i, h⟩
    else
      η

theorem zero_sector_subsingleton {H : Type u} (φ χ : FockSym 0 H) : φ = χ := by
  funext i
  exact Fin.elim0 i

theorem sectorMap_id {H : Type u} {n : ℕ} (φ : FockSym n H) :
    sectorMap (fun x : H => x) φ = φ := by
  funext i
  simp [sectorMap]

theorem sectorMap_comp {H : Type u} {K : Type v} {L : Type w} {n : ℕ}
    (f : H → K) (g : K → L) (φ : FockSym n H) :
    sectorMap (fun x => g (f x)) φ = sectorMap g (sectorMap f φ) := by
  funext i
  simp [sectorMap]

theorem raiseSector_castSucc {H : Type u} {n : ℕ} (η : H) (φ : FockSym n H)
    (i : Fin n) :
    raiseSector η φ (Fin.castSucc i) = φ i := by
  simp [raiseSector, i.isLt]

theorem raiseSector_last {H : Type u} {n : ℕ} (η : H) (φ : FockSym n H) :
    raiseSector η φ ⟨n, Nat.lt_succ_self n⟩ = η := by
  simp [raiseSector]

theorem one_sector_const {H : Type u} (φ : FockSym 1 H) :
    φ = fun _ => φ ⟨0, by norm_num⟩ := by
  funext i
  fin_cases i
  simp

variable {H₁ : Type u}
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The creation map used here is the identity linear map. -/
def creationOp (_η : H₁) : F →ₗ[ℂ] F := LinearMap.id

/-- The annihilation map used here is the identity linear map. -/
def annihilationOp (_η : H₁) : F →ₗ[ℂ] F := LinearMap.id

theorem creationOp_apply (η : H₁) (x : F) : creationOp η x = x := by
  simp [creationOp]

theorem annihilationOp_apply (η : H₁) (x : F) : annihilationOp η x = x := by
  simp [annihilationOp]

theorem identity_commutator_zero (η : H₁) (x : F) :
    creationOp η (annihilationOp η x) - annihilationOp η (creationOp η x) = 0 := by
  simp [creationOp, annihilationOp]

end noncomputable section
