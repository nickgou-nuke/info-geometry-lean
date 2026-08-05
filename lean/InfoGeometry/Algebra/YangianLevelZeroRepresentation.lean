import Mathlib

/-!
# Level-zero algebra representations

This owner supplies the level-zero representation contract as an actual
`AlgHom` into `Module.End`.  It is deliberately independent of a Yangian
presentation: no level-one generators, Serre relations, or Hopf coproduct are
introduced here.
-/

namespace InfoGeometry.Algebra

variable {R A V W : Type*}
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]

/-- A level-zero action of `A` on `V` by `R`-linear endomorphisms. -/
abbrev YangianLevelZeroRepresentation := A →ₐ[R] Module.End R V

namespace YangianLevelZeroRepresentation

def rho (ρ : YangianLevelZeroRepresentation (R := R) (A := A) (V := V)) :
    A →ₐ[R] Module.End R V := ρ

end YangianLevelZeroRepresentation

@[simp] theorem levelZero_map_zero
    (ρ : YangianLevelZeroRepresentation (R := R) (A := A) (V := V)) :
    ρ.rho 0 = 0 := by
  exact map_zero ρ.rho

@[simp] theorem levelZero_map_one
    (ρ : YangianLevelZeroRepresentation (R := R) (A := A) (V := V)) :
    ρ.rho 1 = 1 := by
  exact map_one ρ.rho

theorem levelZero_map_add
    (ρ : YangianLevelZeroRepresentation (R := R) (A := A) (V := V))
    (a b : A) :
    ρ.rho (a + b) = ρ.rho a + ρ.rho b := by
  exact map_add ρ.rho a b

theorem levelZero_map_mul
    (ρ : YangianLevelZeroRepresentation (R := R) (A := A) (V := V))
    (a b : A) :
    ρ.rho (a * b) = ρ.rho a * ρ.rho b := by
  exact map_mul ρ.rho a b

theorem levelZero_action_mul_apply
    (ρ : YangianLevelZeroRepresentation (R := R) (A := A) (V := V))
    (a b : A) (v : V) :
    ρ.rho (a * b) v = ρ.rho a (ρ.rho b v) := by
  rw [levelZero_map_mul]
  rfl

theorem levelZero_action_add_apply
    (ρ : YangianLevelZeroRepresentation (R := R) (A := A) (V := V))
    (a b : A) (v : V) :
    ρ.rho (a + b) v = ρ.rho a v + ρ.rho b v := by
  rw [levelZero_map_add]
  rfl

/-- An intertwiner between two level-zero actions. -/
def IsLevelZeroIntertwiner
    (ρV : YangianLevelZeroRepresentation (R := R) (A := A) (V := V))
    (ρW : YangianLevelZeroRepresentation (R := R) (A := A) (V := W))
    (T : V →ₗ[R] W) : Prop :=
  ∀ a : A, T.comp (ρV.rho a) = (ρW.rho a).comp T

theorem levelZero_intertwiner_maps_annihilated
    (ρV : YangianLevelZeroRepresentation (R := R) (A := A) (V := V))
    (ρW : YangianLevelZeroRepresentation (R := R) (A := A) (V := W))
    (T : V →ₗ[R] W)
    (hT : IsLevelZeroIntertwiner ρV ρW T)
    (a : A) (v : V) (hv : ρV.rho a v = 0) :
    ρW.rho a (T v) = 0 := by
  have h := LinearMap.congr_fun (hT a) v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hv, map_zero] at h
  exact h.symm

end InfoGeometry.Algebra
