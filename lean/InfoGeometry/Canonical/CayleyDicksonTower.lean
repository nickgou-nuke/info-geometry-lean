import InfoGeometry.Canonical.CayleyDicksonEmbedding
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open AlbertCayleyDickson
open AlbertStep

variable {F A : Type*} [CommRing F] [Ring A] [Algebra F A] [StarRing A] {γ : F}

noncomputable def coordEquiv (γ : F) : AlbertStep F A γ ≃ A × A where
  toFun x := (x.p, x.q)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

noncomputable def coordAddEquiv (γ : F) : AlbertStep F A γ ≃+ A × A where
  toEquiv := coordEquiv (F := F) (A := A) γ
  map_add' x y := rfl

noncomputable instance : AddCommGroup (AlbertStep F A γ) :=
  Equiv.addCommGroup (coordEquiv (F := F) (A := A) γ)

noncomputable instance : Module F (AlbertStep F A γ) :=
  AddEquiv.module F (coordAddEquiv (F := F) (A := A) γ)

end InfoGeometry.Canonical
