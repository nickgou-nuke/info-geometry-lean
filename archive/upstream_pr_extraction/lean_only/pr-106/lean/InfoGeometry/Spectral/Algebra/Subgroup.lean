import Mathlib

/-!
# Subgroups and homomorphism factorisations

The reference uses a proposition-valued subgroup predicate and a custom
subtype group.  Mathlib's `Subgroup` is the native carrier, so this module
ports the reusable inclusion, kernel, image, and image-factorisation API.
-/

namespace InfoGeometry.Spectral.Algebra.Subgroup

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]

abbrev Carrier (S : Subgroup G) := S

def inclusion (S : Subgroup G) : S →* G := S.subtype

@[simp] theorem inclusion_apply (S : Subgroup G) (x : S) : inclusion S x = x := rfl

def kernel (f : G →* H) : Subgroup G := f.ker

def image (f : G →* H) : Subgroup H := f.range

@[simp] theorem mem_kernel_iff (f : G →* H) (x : G) :
    x ∈ kernel f ↔ f x = 1 := by
  rfl

@[simp] theorem mem_image_iff (f : G →* H) (y : H) :
    y ∈ image f ↔ ∃ x, f x = y := by
  rfl

theorem kernel_mul_mem (f : G →* H) {x y : G}
    (hx : x ∈ kernel f) (hy : y ∈ kernel f) : x * y ∈ kernel f := by
  exact (kernel f).mul_mem hx hy

theorem kernel_inv_mem (f : G →* H) {x : G}
    (hx : x ∈ kernel f) : x⁻¹ ∈ kernel f := by
  exact (kernel f).inv_mem hx

def imageInclusion (f : G →* H) : image f →* H := (image f).subtype

def imageLift (f : G →* H) : G →* image f :=
  f.codRestrict (image f) (fun x => ⟨x, rfl⟩)

@[simp] theorem imageLift_apply (f : G →* H) (x : G) :
    imageLift f x = ⟨f x, ⟨x, rfl⟩⟩ := rfl

theorem imageFactor (f : G →* H) :
    (imageInclusion f).comp (imageLift f) = f := by
  ext x
  rfl

theorem imageInclusion_injective (f : G →* H) :
    Function.Injective (imageInclusion f) := by
  exact (image f).subtype_injective

def map (f : G →* H) (S : Subgroup G) : Subgroup H := S.map f

def comap (f : G →* H) (T : Subgroup H) : Subgroup G := T.comap f

theorem map_mono (f : G →* H) {S T : Subgroup G} (hST : S ≤ T) :
    map f S ≤ map f T := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, hST hx, rfl⟩

theorem comap_mono (f : G →* H) {S T : Subgroup H} (hST : S ≤ T) :
    comap f S ≤ comap f T := by
  intro x hx
  exact hST hx

@[simp] theorem mem_map_iff (f : G →* H) (S : Subgroup G) (y : H) :
    y ∈ map f S ↔ ∃ x, x ∈ S ∧ f x = y := by
  rfl

@[simp] theorem mem_comap_iff (f : G →* H) (T : Subgroup H) (x : G) :
    x ∈ comap f T ↔ f x ∈ T := by
  rfl

end InfoGeometry.Spectral.Algebra.Subgroup
