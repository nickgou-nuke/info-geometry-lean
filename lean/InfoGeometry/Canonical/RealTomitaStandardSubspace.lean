import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.RealTomitaStandardSubspace

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real-linear `i`-action on a complex Hilbert space viewed over `ℝ`. -/
noncomputable def IMap (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] : H →ₗ[ℝ] H where
  toFun := fun x => (Complex.I : ℂ) • x
  map_add' := by simp
  map_smul' := by
    intro r x
    calc
      (Complex.I : ℂ) • ((r : ℝ) • x)
          = (Complex.I : ℂ) • ((r : ℂ) • x) := by rfl
      _ = ((Complex.I * (r : ℂ)) • x) := by
            simpa using (smul_smul (Complex.I : ℂ) (r : ℂ) x)
      _ = (((r : ℂ) * (Complex.I : ℂ)) • x) := by simp [mul_comm]
      _ = (r : ℂ) • ((Complex.I : ℂ) • x) := by
            simpa using (smul_smul (r : ℂ) (Complex.I : ℂ) x).symm

/-- The real subspace `iK` represented as a mapped real submodule. -/
noncomputable def ImaginarySubmodule (K : Submodule ℝ H) : Submodule ℝ H :=
  Submodule.map (IMap H) K

/-- Real-standard subspace conditions (cyclic + separating) in ambient real form. -/
def IsStandardSubspace (K : Submodule ℝ H) : Prop :=
  Dense ((↑(K ⊔ ImaginarySubmodule (H := H) K) : Set H)) ∧
  K ⊓ ImaginarySubmodule (H := H) K = ⊥

/-- Product-form Tomita involution `(x,y) ↦ (x,-y)` on `K × iK`. -/
noncomputable def tomitaProd (K : Submodule ℝ H) :
    (↥K × ↥(ImaginarySubmodule (H := H) K)) →ₗ[ℝ]
      (↥K × ↥(ImaginarySubmodule (H := H) K)) where
  toFun := fun p => (p.1, -p.2)
  map_add' := by
    intro p q
    ext <;> simp [add_comm]
  map_smul' := by
    intro r p
    ext <;> simp

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- The product-form Tomita map squares to identity. -/
lemma tomitaProd_involutive (K : Submodule ℝ H)
    (p : (↥K × ↥(ImaginarySubmodule (H := H) K))) :
    tomitaProd (H := H) K (tomitaProd (H := H) K p) = p := by
  rcases p with ⟨x, y⟩
  simp [tomitaProd]

/-- Sum map from `K × iK` onto `K ⊔ iK`. -/
noncomputable def addToSupMap (K : Submodule ℝ H) :
    (↥K × ↥(ImaginarySubmodule (H := H) K)) →ₗ[ℝ] ↥(K ⊔ ImaginarySubmodule (H := H) K) where
  toFun := fun p => ⟨(p.1 : H) + (p.2 : H), by
    exact Submodule.mem_sup.2 ⟨(p.1 : H), p.1.property, (p.2 : H), p.2.property, by simp⟩⟩
  map_add' := by
    intro p q
    ext
    simp [add_left_comm, add_comm]
  map_smul' := by
    intro r p
    ext
    simp

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma addToSupMap_surjective (K : Submodule ℝ H) :
    Function.Surjective (addToSupMap (H := H) K) := by
  intro z
  rcases Submodule.mem_sup.mp z.2 with ⟨x, hx, y, hy, hxy⟩
  refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
  apply Subtype.ext
  simpa [addToSupMap] using hxy

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma addToSupMap_injective (K : Submodule ℝ H)
    (hSep : K ⊓ ImaginarySubmodule (H := H) K = ⊥) :
    Function.Injective (addToSupMap (H := H) K) := by
  intro p q hpq
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  have hEq : (x : H) + (y : H) = (x' : H) + (y' : H) := by
    exact congrArg (fun t : ↥(K ⊔ ImaginarySubmodule (H := H) K) => (t : H)) hpq
  have hsum : ((x : H) - (x' : H)) + ((y : H) - (y' : H)) = 0 := by
    have hsub : ((x : H) + (y : H)) - ((x' : H) + (y' : H)) = 0 := by
      exact sub_eq_zero.mpr hEq
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
  have hxmem : ((x : H) - (x' : H)) ∈ K := sub_mem x.property x'.property
  have hymem : ((y : H) - (y' : H)) ∈ ImaginarySubmodule (H := H) K :=
    sub_mem y.property y'.property
  have hxdiff0 : ((x : H) - (x' : H)) = 0 := by
    have hInt : ((x : H) - (x' : H)) ∈ K ⊓ ImaginarySubmodule (H := H) K := by
      refine ⟨hxmem, ?_⟩
      have hxFromY : ((x : H) - (x' : H)) = -((y : H) - (y' : H)) :=
        eq_neg_of_add_eq_zero_left hsum
      have hymemNeg : -((y : H) - (y' : H)) ∈ ImaginarySubmodule (H := H) K := by
        simpa using (Submodule.neg_mem (ImaginarySubmodule (H := H) K) hymem)
      simpa [hxFromY] using hymemNeg
    have hBot : ((x : H) - (x' : H)) ∈ (⊥ : Submodule ℝ H) := by
      simpa [hSep] using hInt
    simpa using hBot
  have hydiff0 : ((y : H) - (y' : H)) = 0 := by
    have hNeg : ((y : H) - (y' : H)) = -((x : H) - (x' : H)) :=
      eq_neg_of_add_eq_zero_right hsum
    simp [hxdiff0] at hNeg
    exact hNeg
  have hxEq : x = x' := by
    apply Subtype.ext
    exact sub_eq_zero.mp hxdiff0
  have hyEq : y = y' := by
    apply Subtype.ext
    exact sub_eq_zero.mp hydiff0
  simp [hxEq, hyEq]

/-- Real direct-sum decomposition `K × iK ≃ K ⊔ iK` under separating condition. -/
noncomputable def decompositionEquiv (K : Submodule ℝ H) (hK : IsStandardSubspace (H := H) K) :
    (↥K × ↥(ImaginarySubmodule (H := H) K)) ≃ₗ[ℝ] ↥(K ⊔ ImaginarySubmodule (H := H) K) :=
  LinearEquiv.ofBijective (addToSupMap (H := H) K) ⟨
    addToSupMap_injective (H := H) K hK.2,
    addToSupMap_surjective (H := H) K
  ⟩

/-- Tomita map on the sum-domain, transported from product form. -/
noncomputable def TomitaOnStandard (K : Submodule ℝ H) (hK : IsStandardSubspace (H := H) K) :
    ↥(K ⊔ ImaginarySubmodule (H := H) K) →ₗ[ℝ] ↥(K ⊔ ImaginarySubmodule (H := H) K) :=
  let e := decompositionEquiv (H := H) K hK
  e.toLinearMap.comp ((tomitaProd (H := H) K).comp e.symm.toLinearMap)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- The transported Tomita map is involutive. -/
lemma tomitaOnStandard_involutive (K : Submodule ℝ H) (hK : IsStandardSubspace (H := H) K)
    (z : ↥(K ⊔ ImaginarySubmodule (H := H) K)) :
    TomitaOnStandard (H := H) K hK (TomitaOnStandard (H := H) K hK z) = z := by
  let e := decompositionEquiv (H := H) K hK
  change e (tomitaProd (H := H) K (e.symm (e (tomitaProd (H := H) K (e.symm z))))) = z
  simp [tomitaProd_involutive]

end InfoGeometry.Canonical.RealTomitaStandardSubspace
