/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LinearAlgebra.DirectLimitEndomorphism
import InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore

/-!
# The existing reflection theorems on a real directed limit

This is a consumer of the native descended endomorphisms and the existing
`ZetaDihedralWeilKreinCore` reflection theorems. A stage eigen-equation always
descends. To obtain a native `HasEigenvector` statement, the image of the stage
vector is explicitly required to be nonzero. Transition-map injectivity is
not assumed, and reflection alone is not claimed to constrain spectral support.
-/

noncomputable section

namespace InfoGeometry.LinearAlgebra.DirectLimitReflection

open InfoGeometry.LinearAlgebra.DirectLimitEndomorphism

variable {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {V : I → Type*}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
variable (f : ∀ i j, i ≤ j → V i →ₗ[ℝ] V j)
variable [DirectedSystem V (fun i j h x => f i j h x)]
variable (J D : ∀ i, V i →ₗ[ℝ] V i)
variable (hJ : ∀ i j (h : i ≤ j) (x : V i),
  J j (f i j h x) = f i j h (J i x))
variable (hD : ∀ i j (h : i ≤ j) (x : V i),
  D j (f i j h x) = f i j h (D i x))
variable (hInv : ∀ i, Function.Involutive (J i))
variable (hReflection : ∀ i x, J i (D i (J i x)) = -D i x)

private theorem reflection_relations :
    descendEnd f J hJ * descendEnd f J hJ = 1 ∧
      descendEnd f J hJ * descendEnd f D hD * descendEnd f J hJ =
        -(descendEnd f D hD) := by
  constructor
  · apply LinearMap.ext
    intro z
    exact descendEnd_involutive f J hJ hInv z
  · apply LinearMap.ext
    intro z
    exact congrArg
      (fun T : Module.End ℝ (_root_.DirectLimit V f) => T z)
      (descendEnd_reflection f J D hJ hD hReflection)

/-- The existing reflection eigen-equation theorem applies to each descended
stage eigen-equation, whether or not its limit image is nonzero. -/
theorem reflected_stage_eigen_equation (i : I) (x : V i) (w : ℝ)
    (hEigen : D i x = w • x) :
    descendEnd f D hD
        (descendEnd f J hJ (DirectLimit.Module.of ℝ I V f i x)) =
      (-w) • descendEnd f J hJ (DirectLimit.Module.of ℝ I V f i x) := by
  obtain ⟨hJLimit, hDLimit⟩ :=
    reflection_relations f J D hJ hD hInv hReflection
  exact InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.reflection_eigen_equation
    (descendEnd f J hJ) (descendEnd f D hD) hJLimit hDLimit
    (descendEnd_eigen_equation_of_stage f D hD i x w hEigen)

/-- The existing native reflection-eigenvector theorem gives the reflected
limit eigenvector once the original stage image is explicitly nonzero. -/
theorem reflected_stage_hasEigenvector (i : I) (x : V i) (w : ℝ)
    (hEigen : D i x = w • x)
    (hNonzero : DirectLimit.Module.of ℝ I V f i x ≠ 0) :
    (descendEnd f D hD).HasEigenvector (-w)
      (descendEnd f J hJ (DirectLimit.Module.of ℝ I V f i x)) := by
  obtain ⟨hJLimit, hDLimit⟩ :=
    reflection_relations f J D hJ hD hInv hReflection
  have hEigenLimit : (descendEnd f D hD).HasEigenvector w
      (DirectLimit.Module.of ℝ I V f i x) := by
    refine ⟨?_, hNonzero⟩
    rw [Module.End.mem_eigenspace_iff]
    exact descendEnd_eigen_equation_of_stage f D hD i x w hEigen
  exact InfoGeometry.Arithmetic.ZetaDihedralWeilKreinCore.reflection_hasEigenvector
    (descendEnd f J hJ) (descendEnd f D hD) hJLimit hDLimit hEigenLimit

end InfoGeometry.LinearAlgebra.DirectLimitReflection

end
