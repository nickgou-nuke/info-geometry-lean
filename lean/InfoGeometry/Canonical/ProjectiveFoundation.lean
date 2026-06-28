/-
InfoGeometry/Canonical/ProjectiveFoundation.lean

Projective foundation for the modular bridge.

This file keeps the base symmetry / carrier / cocycle split explicit:
- symmetry acts on a base space;
- the quantum/Berry phase is a projective cocycle;
- stabilizers extract honest homomorphisms;
- cusp behavior is delegated to filter limits in a separate file.
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace InfoGeometry.Canonical.ProjectiveFoundation

open scoped LinearAlgebra.Projectivization

universe u v w

/--
A minimal Krein-style carrier.

The file keeps the carrier abstract. The projective modular bridge only needs
the existence of an indefinite quadratic form, not a concrete signature.
-/
class KreinSpace (V : Type u) [AddCommGroup V] [Module ℝ V] where
  form : QuadraticForm ℝ V

/--
A rotor-valued cocycle over a group action.

This is the projective/multiplier object, not a global homomorphism
`SL(2, ℝ) → R`.
-/
structure ProjectiveRotorCocycle
    (Γ X R : Type*)
    [Group Γ] [MulAction Γ X] [Group R] where
  toFun : Γ → X → R
  map_one : ∀ x, toFun 1 x = 1
  map_mul : ∀ γ δ x, toFun (γ * δ) x = toFun γ (δ • x) * toFun δ x

instance {Γ X R : Type*} [Group Γ] [MulAction Γ X] [Group R] :
    CoeFun (ProjectiveRotorCocycle Γ X R) (fun _ ↦ Γ → X → R) where
  coe := ProjectiveRotorCocycle.toFun

/--
A Lean-native projective linear representation.

The representation itself is linear, but composition is only defined up to a
scalar cocycle. This is the direct algebraic analogue of the usual projective
representation package on Wikipedia.
-/
structure ProjectiveRepresentation
    (k G V : Type*)
    [Group G] [Semiring k] [AddCommMonoid V] [Module k V] where
  /-- The underlying projective linear action. -/
  toLinearEquiv : G → V ≃ₗ[k] V
  /-- The scalar multiplier recording the projective defect. -/
  multiplier : G → G → kˣ
  /-- The identity acts strictly. -/
  map_one : toLinearEquiv 1 = LinearEquiv.refl k V
  /-- Composition is multiplicative up to the scalar multiplier. -/
  map_mul :
    ∀ g h : G,
      ∀ x : V,
        toLinearEquiv (g * h) x =
          (multiplier g h : k) • toLinearEquiv g (toLinearEquiv h x)
  /--
  The multiplier is a normalized 2-cocycle.

  This is the coherence condition that makes the projective defect associative.
  -/
  cocycle : ∀ g h l : G, multiplier g h * multiplier (g * h) l =
    multiplier h l * multiplier g (h * l)
  /-- Normalization on the left identity. -/
  one_left : ∀ g : G, multiplier 1 g = 1
  /-- Normalization on the right identity. -/
  one_right : ∀ g : G, multiplier g 1 = 1

namespace ProjectiveRepresentation

variable {k G V : Type*}
  [Group G] [Semiring k] [AddCommMonoid V] [Module k V]

@[simp] theorem multiplier_one_left (P : ProjectiveRepresentation k G V)
    (g : G) :
    P.multiplier 1 g = 1 :=
  P.one_left g

@[simp] theorem multiplier_one_right (P : ProjectiveRepresentation k G V)
    (g : G) :
    P.multiplier g 1 = 1 :=
  P.one_right g

instance : CoeFun (ProjectiveRepresentation k G V) (fun _ ↦ G → V → V) where
  coe P := fun g ↦ P.toLinearEquiv g

@[simp] theorem map_one_apply (P : ProjectiveRepresentation k G V) (x : V) :
    P 1 x = x := by
  simpa using congrArg (fun e : V ≃ₗ[k] V => e x) P.map_one

@[simp] theorem map_mul_apply (P : ProjectiveRepresentation k G V)
    (g h : G) (x : V) :
    P (g * h) x =
      (P.multiplier g h : k) • P g (P h x) :=
  P.map_mul g h x

theorem map_one_eq_id (P : ProjectiveRepresentation k G V) :
    P 1 = id := by
  ext x
  exact P.map_one_apply x

section CocycleBridge

local instance trivialUnitsMulDistribMulAction
    (G : Type*) [Group G] (K : Type*) [Field K] : MulDistribMulAction G Kˣ where
  smul := fun _ x => x
  mul_smul := by
    intro g h x
    rfl
  one_smul := by
    intro x
    rfl
  smul_mul := by
    intro g x y
    rfl
  smul_one := by
    intro g
    rfl

@[simp] theorem multiplierTrivialAction_smul
    {G : Type*} [Group G] {K : Type*} [Field K] (g : G) (x : Kˣ) :
    g • x = x :=
  rfl

/-- The projective multiplier is a normalized multiplicative 2-cocycle. -/
theorem multiplier_isMulCocycle₂
    {G : Type*} [Group G] {K : Type*} [Field K]
    {V : Type*} [AddCommMonoid V] [Module K V]
    (P : ProjectiveRepresentation K G V) :
    groupCohomology.IsMulCocycle₂ (fun p : G × G => (P.multiplier p.1 p.2 : Kˣ)) := by
  intro g h l
  rw [multiplierTrivialAction_smul]
  rw [mul_comm ((fun p : G × G => (P.multiplier p.1 p.2 : Kˣ)) (g * h, l))
    ((fun p : G × G => (P.multiplier p.1 p.2 : Kˣ)) (g, h))]
  exact P.cocycle g h l

end CocycleBridge

section CocycleBridgeLowDegree

variable (G : Type) [Group G]
variable (K : Type) [Field K]
variable (V : Type) [AddCommMonoid V] [Module K V]

local instance : MulDistribMulAction G Kˣ where
  smul := fun _ x => x
  mul_smul := by
    intro x y b
    rfl
  one_smul := by
    intro b
    rfl
  smul_mul := by
    intro r x y
    rfl
  smul_one := by
    intro r
    rfl

/-- The projective multiplier canonically defines a Mathlib 2-cocycle. -/
noncomputable def multiplierToCocycles₂ (P : ProjectiveRepresentation K G V) :
    groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction G Kˣ) := by
  exact groupCohomology.cocyclesOfIsMulCocycle₂ (G := G) (M := Kˣ)
    (f := fun p : G × G => (P.multiplier p.1 p.2 : Kˣ))
    (by simpa using (P.multiplier_isMulCocycle₂ (G := G) (V := V)))

@[simp] theorem multiplierToCocycles₂_apply (P : ProjectiveRepresentation K G V)
    (g h : G) :
    (multiplierToCocycles₂ (G := G) (K := K) (V := V) P) (g, h) = P.multiplier g h :=
  rfl

/-- The multiplier class in low-degree cohomology. -/
noncomputable def multiplierClass (P : ProjectiveRepresentation K G V) :
    groupCohomology.H2 (Rep.ofMulDistribMulAction G Kˣ) :=
  groupCohomology.H2π _ (P.multiplierToCocycles₂ (G := G) (K := K) (V := V))

@[simp] theorem multiplierClass_apply (P : ProjectiveRepresentation K G V) :
    groupCohomology.H2π (Rep.ofMulDistribMulAction G Kˣ) (P.multiplierToCocycles₂ (G := G)
      (K := K) (V := V)) = P.multiplierClass (G := G) (K := K) (V := V) :=
  rfl

/-- The projective class vanishes exactly when the cocycle is a coboundary. -/
theorem multiplierClass_eq_zero_iff_mem_coboundaries₂ (P : ProjectiveRepresentation K G V) :
    P.multiplierClass (G := G) (K := K) (V := V) = 0 ↔
      ⇑(P.multiplierToCocycles₂ (G := G) (K := K) (V := V)) ∈
        groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction G Kˣ) := by
  simpa [multiplierClass] using
    (groupCohomology.H2π_eq_zero_iff
      (A := Rep.ofMulDistribMulAction G Kˣ)
      (x := P.multiplierToCocycles₂ (G := G) (K := K) (V := V)))

/-- The projective class vanishes exactly when the multiplier is a multiplicative coboundary. -/
theorem multiplierClass_eq_zero_iff_isMulCoboundary₂ (P : ProjectiveRepresentation K G V) :
    P.multiplierClass (G := G) (K := K) (V := V) = 0 ↔
      groupCohomology.IsMulCoboundary₂
        (f := fun p : G × G => (P.multiplier p.1 p.2 : Kˣ)) := by
  constructor
  · intro h
    have hm :
        ⇑(P.multiplierToCocycles₂ (G := G) (K := K) (V := V)) ∈
          groupCohomology.coboundaries₂ (Rep.ofMulDistribMulAction G Kˣ) :=
      (multiplierClass_eq_zero_iff_mem_coboundaries₂ (P := P)).mp h
    exact groupCohomology.isMulCoboundary₂_of_mem_coboundaries₂
      (f := fun p : G × G => (P.multiplier p.1 p.2 : Kˣ))
      hm
  · intro h
    refine (multiplierClass_eq_zero_iff_mem_coboundaries₂ (P := P)).mpr ?_
    simpa [multiplierToCocycles₂] using
      (groupCohomology.coboundariesOfIsMulCoboundary₂
        (f := fun p : G × G => (P.multiplier p.1 p.2 : Kˣ)) h).2

end CocycleBridgeLowDegree

/-- A genuine representation is a projective representation with trivial multiplier. -/
def ofLinearHom (ρ : G →* (V ≃ₗ[k] V)) : ProjectiveRepresentation k G V where
  toLinearEquiv := ρ
  multiplier := fun _ _ ↦ 1
  map_one := by
    ext x
    exact congrArg (fun e : V ≃ₗ[k] V => e x) ρ.map_one
  map_mul := by
    intro g h x
    change (ρ (g * h)) x = (1 : k) • (ρ g) ((ρ h) x)
    rw [one_smul]
    exact congrArg (fun e : V ≃ₗ[k] V => e x) (ρ.map_mul g h)
  cocycle := by
    intro g h l
    simp
  one_left := by
    intro g
    simp
  one_right := by
    intro g
    simp

@[simp] theorem ofLinearHom_multiplier (ρ : G →* (V ≃ₗ[k] V)) (g h : G) :
    (ofLinearHom (k := k) (G := G) (V := V) ρ).multiplier g h = 1 :=
  rfl

@[simp] theorem ofLinearHom_toLinearEquiv (ρ : G →* (V ≃ₗ[k] V)) :
    (ofLinearHom (k := k) (G := G) (V := V) ρ).toLinearEquiv = ρ :=
  rfl

section CocycleBridgeLowDegree

variable {G : Type} [Group G]
variable {K : Type} [Field K]
variable {V : Type} [AddCommMonoid V] [Module K V]

@[simp] theorem ofLinearHom_multiplierToCocycles₂ (ρ : G →* (V ≃ₗ[K] V)) :
    multiplierToCocycles₂ (G := G) (K := K) (V := V) (ofLinearHom (k := K) (G := G) (V := V) ρ)
      = 0 := by
  ext g h
  change Additive.ofMul (1 : Kˣ) = 0
  simp

@[simp] theorem ofLinearHom_multiplierClass (ρ : G →* (V ≃ₗ[K] V)) :
    multiplierClass (G := G) (K := K) (V := V) (ofLinearHom (k := K) (G := G) (V := V) ρ) = 0 := by
  simp [multiplierClass, ofLinearHom_multiplierToCocycles₂]

end CocycleBridgeLowDegree

/-- A projective representation with trivial multiplier gives a genuine action on points. -/
def act (P : ProjectiveRepresentation k G V) : G → V → V :=
  fun g => P g

end ProjectiveRepresentation

namespace ProjectiveRepresentation

section ProjectivizationAction

variable {K G V : Type*}
  [Group G] [DivisionRing K] [AddCommGroup V] [Module K V]

/--
The induced action on projective space.

This is the key geometric output of a projective representation: the scalar
defect is invisible after passing to rays.
-/
def projectivizationMap (P : ProjectiveRepresentation K G V) :
    G → ℙ K V → ℙ K V :=
  fun g => Projectivization.map (K := K) (V := V) (L := K) (W := V)
    (σ := RingHom.id K) (P.toLinearEquiv g).toLinearMap
    (LinearEquiv.injective (P.toLinearEquiv g))

@[simp] theorem projectivizationMap_mk (P : ProjectiveRepresentation K G V)
    (g : G) (v : V) (hv : v ≠ 0) :
    P.projectivizationMap g (Projectivization.mk K v hv) =
      Projectivization.mk (K := K) (V := V) (P.toLinearEquiv g v)
        ((P.toLinearEquiv g).map_ne_zero_iff.mpr hv) := by
  rfl

theorem projectivizationMap_one (P : ProjectiveRepresentation K G V) :
    P.projectivizationMap 1 = id := by
  ext ⟨v, hv⟩
  simp [projectivizationMap, P.map_one]

theorem projectivizationMap_mul (P : ProjectiveRepresentation K G V)
    (g h : G) :
    P.projectivizationMap (g * h) =
      P.projectivizationMap g ∘ P.projectivizationMap h := by
  ext ⟨v, hv⟩
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨P.multiplier g h, ?_⟩
  exact (P.map_mul_apply g h v).symm

/-- The projective representation induces a genuine monoid action on projective space. -/
def projectivizationAction (P : ProjectiveRepresentation K G V) : G →* Function.End (ℙ K V) where
  toFun := P.projectivizationMap
  map_one' := by
    simpa [Function.End.one_def] using P.projectivizationMap_one
  map_mul' := P.projectivizationMap_mul

end ProjectivizationAction

section CentralExtension

variable {K G V : Type}
  [Group G] [Field K] [AddCommGroup V] [Module K V]

local instance : MulDistribMulAction G Kˣ where
  smul := fun _ x => x
  mul_smul := by
    intro g h x
    rfl
  one_smul := by
    intro x
    rfl
  smul_mul := by
    intro g x y
    rfl
  smul_one := by
    intro g
    rfl

/--
The cocycle extension attached to a projective representation.

-/
structure centralExtension (P : ProjectiveRepresentation K G V) where
  fst : G
  snd : Kˣ

namespace centralExtension

variable (P : ProjectiveRepresentation K G V)

instance (priority := 1001) : Mul (P.centralExtension) where
  mul x y := ⟨x.1 * y.1, x.2 * y.2 * P.multiplier x.1 y.1⟩

instance : One (P.centralExtension) where
  one := ⟨1, 1⟩

instance : Inhabited (P.centralExtension) := ⟨1⟩

@[simp] theorem mul_fst (x y : P.centralExtension) : (x * y).1 = x.1 * y.1 := rfl
@[simp] theorem mul_snd (x y : P.centralExtension) :
    (x * y).2 = x.2 * y.2 * P.multiplier x.1 y.1 := rfl
@[simp] theorem one_fst : (1 : P.centralExtension).1 = (1 : G) := rfl
@[simp] theorem one_snd : (1 : P.centralExtension).2 = (1 : Kˣ) := rfl

@[ext]
theorem ext {x y : P.centralExtension} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := by
  cases x
  cases y
  cases h1
  cases h2
  rfl

instance : Monoid (P.centralExtension) where
  mul := (· * ·)
  one := 1
  mul_assoc x y z := by
    cases x with
    | mk g a =>
    cases y with
    | mk h b =>
    cases z with
    | mk l c =>
      ext
      · change (g * h) * l = g * (h * l)
        exact mul_assoc g h l
      · have hunits :
          (({ fst := g, snd := a } : P.centralExtension) *
            ({ fst := h, snd := b } : P.centralExtension) *
            ({ fst := l, snd := c } : P.centralExtension)).snd =
          (({ fst := g, snd := a } : P.centralExtension) *
            (({ fst := h, snd := b } : P.centralExtension) *
              ({ fst := l, snd := c } : P.centralExtension))).snd := by
          simp [mul_snd, mul_assoc, mul_left_comm, mul_comm, P.cocycle]
        exact congrArg (fun u : Kˣ => (u : K)) hunits
  one_mul x := by
    cases x with
    | mk g a =>
      ext
      · change 1 * g = g
        exact one_mul g
      · simp
  mul_one x := by
    cases x with
    | mk g a =>
      ext
      · change g * 1 = g
        exact mul_one g
      · simp

/-- The extension projects to the original group. -/
def proj : P.centralExtension →* G where
  toFun := fun x => x.1
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- A projective representation lifts to an honest representation of the central extension. -/
def liftToCentralExtension : P.centralExtension →* (V ≃ₗ[K] V) where
  toFun := fun x => x.2⁻¹ • P.toLinearEquiv x.1
  map_one' := by
    ext v
    simp
  map_mul' := by
    intro x y
    cases x with
    | mk g a =>
    cases y with
    | mk h b =>
      ext v
      simp [P.map_mul_apply, smul_smul, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem liftToCentralExtension_apply (x : P.centralExtension) :
    centralExtension.liftToCentralExtension (P := P) x = x.2⁻¹ • P.toLinearEquiv x.1 := rfl

theorem liftToCentralExtension_proj (x : P.centralExtension) :
    centralExtension.proj (P := P) x = x.1 := rfl

theorem proj_surjective : Function.Surjective (centralExtension.proj (P := P)) := by
  intro g
  exact ⟨⟨g, 1⟩, rfl⟩

/-- The kernel of the projection consists exactly of the scalar units in the second coordinate. -/
theorem proj_eq_one_iff (x : P.centralExtension) :
    centralExtension.proj (P := P) x = 1 ↔ x.1 = 1 := by
  rfl

/-- Any element in the kernel of the projection is a scalar kernel generator. -/
theorem proj_eq_one_exists (x : P.centralExtension) (hx : centralExtension.proj (P := P) x = 1) :
    ∃ u : Kˣ, x = ⟨1, u⟩ := by
  cases x with
  | mk g a =>
    simp [centralExtension.proj] at hx
    subst hx
    exact ⟨a, rfl⟩

/-- Kernel generators commute with every element of the extension. -/
theorem kernel_isCentral (u : Kˣ) (x : P.centralExtension) :
    ⟨1, u⟩ * x = x * ⟨1, u⟩ := by
  cases x with
  | mk g a =>
    ext <;> simp [mul_comm]

/-- The honest linear case gives a split central extension. -/
def ofLinearHomSection (ρ : G →* (V ≃ₗ[K] V)) :
    G →* (centralExtension (P := ofLinearHom (k := K) (G := G) (V := V) ρ)) where
  toFun := fun g => ⟨g, 1⟩
  map_one' := rfl
  map_mul' := by
    intro g h
    ext <;> simp [ofLinearHom]

@[simp] theorem ofLinearHomSection_apply (ρ : G →* (V ≃ₗ[K] V)) (g : G) :
    ofLinearHomSection (G := G) (V := V) ρ g = ⟨g, 1⟩ :=
  rfl

@[simp] theorem ofLinearHomSection_proj (ρ : G →* (V ≃ₗ[K] V)) (g : G) :
    centralExtension.proj (P := ofLinearHom (k := K) (G := G) (V := V) ρ)
      (ofLinearHomSection (G := G) (V := V) ρ g) = g :=
  rfl

@[simp] theorem ofLinearHomSection_lift (ρ : G →* (V ≃ₗ[K] V)) (g : G) :
    centralExtension.liftToCentralExtension (P := ofLinearHom (k := K) (G := G) (V := V) ρ)
      (ofLinearHomSection (G := G) (V := V) ρ g) = ρ g := by
  ext v
  simp [ofLinearHomSection, centralExtension.liftToCentralExtension, ofLinearHom]

/-- The multiplier class vanishes when the cocycle extension admits a splitting section. -/
theorem multiplierClass_eq_zero_exists_splitSection
    (P : ProjectiveRepresentation K G V) :
    P.multiplierClass (G := G) (K := K) (V := V) = 0 →
      ∃ s : G →* P.centralExtension,
        Function.RightInverse s (centralExtension.proj (P := P)) := by
  intro h
  rcases (multiplierClass_eq_zero_iff_isMulCoboundary₂ (P := P)).mp h with ⟨x, hx⟩
  have hx1 : x 1 = 1 := by
    have h := hx 1 1
    simpa [ProjectiveRepresentation.one_left, ProjectiveRepresentation.one_right] using h
  refine ⟨
    { toFun := fun g => ⟨g, (x g)⁻¹⟩
      map_one' := by
        apply centralExtension.ext <;> simp [hx1]
      map_mul' := by
        intro g h
        apply centralExtension.ext
        · rfl
        · have h1 : x g * x h * (x (g * h))⁻¹ = P.multiplier g h := by
            have := hx g h
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
          have h2 : x g * x h = P.multiplier g h * x (g * h) := by
            exact (mul_inv_eq_iff_eq_mul).mp h1
          have h3 := congrArg Inv.inv h2
          have h4 := congrArg (fun z : Kˣ => z * P.multiplier g h) h3
          simpa [mul_comm, mul_left_comm, mul_assoc] using h4.symm }, ?_⟩
  intro g
  rfl

/-- A splitting section forces the multiplier class to vanish. -/
theorem multiplierClass_eq_zero_of_exists_splitSection
    (P : ProjectiveRepresentation K G V) :
    (∃ s : G →* P.centralExtension,
      Function.RightInverse s (centralExtension.proj (P := P))) →
    P.multiplierClass (G := G) (K := K) (V := V) = 0 := by
  intro h
  rcases h with ⟨s, hs⟩
  have hhx : ∀ g h : G,
      (s (g * h)).2 = (s g).2 * (s h).2 * P.multiplier (s g).1 (s h).1 := by
    intro g h
    have hmul := congrArg centralExtension.snd (s.map_mul g h)
    rw [centralExtension.mul_snd] at hmul
    exact hmul
  have hm : groupCohomology.IsMulCoboundary₂
      (f := fun p : G × G => (P.multiplier p.1 p.2 : Kˣ)) := by
    refine ⟨fun g => (s g).2⁻¹, ?_⟩
    intro g h
    have hg' : (s g).1 = g := by simpa [centralExtension.proj] using hs g
    have hh' : (s h).1 = h := by simpa [centralExtension.proj] using hs h
    have hsnd0 : (s (g * h)).2 = (s g).2 * (s h).2 * P.multiplier (s g).1 (s h).1 :=
      hhx g h
    have hsnd : (s (g * h)).2 = (s g).2 * (s h).2 * P.multiplier g h := by
      rwa [hg', hh'] at hsnd0
    have h1 : (s h).2⁻¹ * (s (g * h)).2 * (s g).2⁻¹ = P.multiplier g h := by
      rw [hsnd]
      simp [mul_comm, mul_assoc]
    simpa [div_eq_mul_inv, mul_comm, mul_assoc] using h1
  exact (multiplierClass_eq_zero_iff_isMulCoboundary₂ (P := P)).mpr hm

/-- The multiplier class vanishes exactly when the cocycle extension splits. -/
theorem multiplierClass_eq_zero_iff_exists_splitSection
    (P : ProjectiveRepresentation K G V) :
    P.multiplierClass (G := G) (K := K) (V := V) = 0 ↔
      ∃ s : G →* P.centralExtension,
        Function.RightInverse s (centralExtension.proj (P := P)) := by
  constructor
  · exact multiplierClass_eq_zero_exists_splitSection (P := P)
  · exact multiplierClass_eq_zero_of_exists_splitSection (P := P)

end centralExtension

end CentralExtension

end ProjectiveRepresentation

namespace ProjectiveRepresentation

section PGL

variable {K G V : Type*}
  [Group G]
  [Field K] [AddCommGroup V] [Module K V]

def scalarEquiv : Kˣ →* (V ≃ₗ[K] V) where
  toFun a := a • LinearEquiv.refl K V
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp [smul_smul, mul_comm]

/-- Two linear equivalences are projectively equivalent if they differ by a scalar. -/
def projectiveEquivSetoid : Setoid (V ≃ₗ[K] V) where
  r e f := ∃ a : Kˣ, f = a • e
  iseqv := by
    constructor
    · intro e
      refine ⟨1, ?_⟩
      ext v
      simp
    · intro e f h
      rcases h with ⟨a, rfl⟩
      refine ⟨a⁻¹, ?_⟩
      ext v
      simp [smul_smul]
    · intro e f g h₁ h₂
      rcases h₁ with ⟨a, rfl⟩
      rcases h₂ with ⟨b, rfl⟩
      refine ⟨b * a, ?_⟩
      ext v
      simp [smul_smul, mul_comm]

/-- The projective linear group as a quotient by scalar equivalence. -/
abbrev PGL := Quotient (projectiveEquivSetoid (K := K) (V := V))

/-- The identity projective linear map. -/
instance : One (PGL (K := K) (V := V)) where
  one := Quotient.mk _ (1 : V ≃ₗ[K] V)

/-- Projective linear maps compose. -/
instance : Mul (PGL (K := K) (V := V)) where
  mul := Quotient.map₂ (· * ·)
    (by
      intro e₁ e₂ he f₁ f₂ hf
      rcases he with ⟨a, rfl⟩
      rcases hf with ⟨b, rfl⟩
      refine ⟨b * a, ?_⟩
      ext v
      simp [smul_smul, mul_comm])

instance : MulOne (PGL (K := K) (V := V)) where
  mul := (· * ·)
  one := 1

instance : Monoid (PGL (K := K) (V := V)) where
  mul := (· * ·)
  one := 1
  mul_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro e f g
    rfl
  one_mul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro e
    rfl
  mul_one := by
    intro x
    refine Quotient.inductionOn x ?_
    intro e
    rfl

/-- The canonical quotient map to `PGL`. -/
def toPGL : (V ≃ₗ[K] V) → PGL (K := K) (V := V) :=
  Quotient.mk _

/-- The canonical quotient map into `PGL` is a monoid homomorphism. -/
def toPGLHom : (V ≃ₗ[K] V) →* PGL (K := K) (V := V) where
  toFun := toPGL (K := K) (V := V)
  map_one' := rfl
  map_mul' := by
    intro e f
    rfl

/-- The quotient acts on projective space. -/
def pglAction : PGL (K := K) (V := V) → ℙ K V → ℙ K V :=
  Quotient.lift
    (fun e => Projectivization.map e.toLinearMap e.injective)
    (by
      intro e f h
      rcases h with ⟨a, rfl⟩
      funext p
      refine Quotient.inductionOn p ?_
      intro v
      delta Projectivization.map
      apply Quotient.sound
      refine ⟨a⁻¹, ?_⟩
      dsimp
      have hmul : ((a⁻¹ : K) * (a : K)) = 1 := by
        simp
      rw [Units.smul_def, smul_smul]
      simp)

/-- The quotient action agrees with the usual action of a chosen representative. -/
theorem pglAction_mk (e : V ≃ₗ[K] V) :
    pglAction (K := K) (V := V) (toPGL (K := K) (V := V) e)
      = Projectivization.map e.toLinearMap e.injective :=
  rfl

/-- Scalar representatives act trivially on projective space. -/
theorem pglAction_scalar (a : Kˣ) :
    pglAction (K := K) (V := V) (toPGL (K := K) (V := V) (a • LinearEquiv.refl K V)) = id := by
  funext p
  refine Quotient.inductionOn p ?_
  intro v
  simp
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  refine ⟨a, ?_⟩
  simp

/-- Composition of representatives is reflected by the quotient action. -/
theorem pglAction_comp (e f : V ≃ₗ[K] V) :
    pglAction (K := K) (V := V) (toPGL (K := K) (V := V) (e.trans f))
      = pglAction (K := K) (V := V) (toPGL (K := K) (V := V) f) ∘
          pglAction (K := K) (V := V) (toPGL (K := K) (V := V) e) := by
  funext p
  refine Quotient.inductionOn p ?_
  intro v
  simpa [Function.comp] using
    congrArg (fun q => q ⟦v⟧)
      (Projectivization.map_comp (f := e.toLinearMap) (hf := e.injective)
        (g := f.toLinearMap) (hg := f.injective))

/-- Honest linear equivalences act on projective space through their `PGL` image. -/
theorem pglAction_toPGLHom (e : V ≃ₗ[K] V) :
    pglAction (K := K) (V := V) (toPGLHom (K := K) (V := V) e)
      = Projectivization.map e.toLinearMap e.injective :=
  rfl

end PGL

end ProjectiveRepresentation

/-- Rotor cocycles are ordinary projective cocycles with rotor-valued target. -/
abbrev RotorCocycle
    (Γ X R : Type*)
    [Group Γ] [MulAction Γ X] [Group R] :=
  ProjectiveRotorCocycle Γ X R

/-- The lifted state/carrier action is projective over a genuine base action. -/
abbrev ProjectiveModularActionLift
    (Γ X R : Type*)
    [Group Γ] [MulAction Γ X] [Group R] :=
  ProjectiveRotorCocycle Γ X R

/--
The base action is genuine.

This is the only place where the group law acts on the base space directly.
The projective anomaly belongs to the lifted carrier, not to the base action.
-/
theorem baseAction_is_genuine
    {Γ X : Type*} [Group Γ] [MulAction Γ X]
    (g h : Γ) (x : X) :
    (g * h) • x = g • (h • x) := by
  simpa using mul_smul g h x

/--
At a fixed point of the action, a cocycle restricts to an honest homomorphism
from the stabilizer subgroup into the rotor group.
-/
def extractStabilizerHom
    {Γ X R : Type*}
    [Group Γ] [MulAction Γ X] [Group R]
    (C : ProjectiveRotorCocycle Γ X R)
    (x : X)
    (stab : Subgroup Γ)
    (h_stab : ∀ γ ∈ stab, γ • x = x) :
    stab →* R where
  toFun γ := C (γ : Γ) x
  map_one' := by
    exact C.map_one x
  map_mul' γ δ := by
    have h_fixed : ((δ : Γ) • x) = x := h_stab (δ : Γ) δ.property
    simp only [Subgroup.coe_mul, C.map_mul (γ : Γ) (δ : Γ) x, h_fixed]

/--
A projective Krein-style carrier.

`Op` is the carrier operator monoid.
`R` is the phase/rotor group.
The cocycle records the anomaly in the lifted action.
-/
structure KreinProjectiveCarrier
    (Γ X R Op : Type*)
    [Group Γ] [MulAction Γ X] [Group R] [Monoid Op] where
  cocycle : ProjectiveRotorCocycle Γ X R
  phase : R →* Units Op
  op : Γ → X → Op
  KreinPreserving : Op → Prop
  op_preserves : ∀ g x, KreinPreserving (op g x)
  op_one : ∀ x, op 1 x = 1
  op_mul :
    ∀ g h x,
      op (g * h) x =
        (((phase (cocycle g (h • x)) : Units Op) : Op)
          * op g (h • x) * op h x)

namespace KreinProjectiveCarrier

variable
    {Γ X R Op : Type*}
    [Group Γ] [MulAction Γ X] [Group R] [Monoid Op]

theorem projective_comp
    (K : KreinProjectiveCarrier Γ X R Op)
    (g h : Γ) (x : X) :
    K.op (g * h) x =
      (((K.phase (K.cocycle g (h • x)) : Units Op) : Op)
        * K.op g (h • x) * K.op h x) :=
  K.op_mul g h x

end KreinProjectiveCarrier

end InfoGeometry.Canonical.ProjectiveFoundation
