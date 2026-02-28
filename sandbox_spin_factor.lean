import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Jordan.Core

namespace InfoGeometry.Jordan

open scoped InfoGeometryJordan

/--
The Spin Factor Jordan algebra J(V) = ℝ ⊕ V.
V is a real inner product space.
Multiplication: (a, u) ⊙ (b, v) = (ab + ⟨u,v⟩, av + bu).
-/
def SpinFactor (V : Type*) := ℝ × V

namespace SpinFactor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

instance : AddCommGroup (SpinFactor V) := by
  change AddCommGroup (ℝ × V)
  infer_instance

instance : Module ℝ (SpinFactor V) := by
  change Module ℝ (ℝ × V)
  infer_instance

/-- Jordan product on the spin factor. -/
noncomputable def jordanProd (x y : SpinFactor V) : SpinFactor V :=
  (x.1 * y.1 + inner ℝ x.2 y.2, x.1 • y.2 + y.1 • x.2)

noncomputable instance : JordanAlgebra (SpinFactor V) where
  jordanProd := jordanProd
  add_left := by
    intro x y z
    apply Prod.ext
    · simp [jordanProd, inner_add_left]
      ring
    · simp [jordanProd, smul_add, add_smul]
      abel
  smul_left := by
    intro a x y
    apply Prod.ext
    · simp [jordanProd, inner_smul_left]
      ring
    · simp [jordanProd, smul_add, smul_smul]
      ring
  comm := by
    intro x y
    apply Prod.ext
    · simp [jordanProd, real_inner_comm]
      ring
    · simp [jordanProd]
      rw [add_comm]
  jordan_identity := by
    intro x y
    apply Prod.ext
    · simp [jordanProd, real_inner_comm, inner_add_right, inner_smul_right]
      ring
    · simp [jordanProd, real_inner_comm, inner_add_right, inner_smul_right, smul_add, smul_smul, add_smul]
      abel

/-- The Lorentz cone (Self-Dual Inner Cone) in the spin factor. -/
def LorentzCone : Set (SpinFactor V) :=
  {x | ∥x.2∥ < x.1}

/-- The boundary of the Lorentz cone (Causal Lightcone). -/
def Lightcone : Set (SpinFactor V) :=
  {x | ∥x.2∥ = x.1}

end SpinFactor

end InfoGeometry.Jordan
