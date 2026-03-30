import InfoGeometry.Quantum.AnticommutingInvolutionCore
import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Quantum.SplitCliffordAtom

/-!
# Krein Doubled Atom

Canonical owner-level wrapper for the real doubled split `Cl(1,1)` atom.

This file introduces no primitive complex scalars and no coordinates. It
re-exports the minimal real algebra of two anticommuting involutions and the
derived square-minus-one generator `K := J ∘ ε`.
-/

namespace InfoGeometry.Canonical

universe u

/-- Canonical owner-level name for the real doubled split `Cl(1,1)` atom. -/
abbrev KreinDoubledAtom := InfoGeometry.Quantum.AnticommutingInvolutionCore

namespace KreinDoubledAtom


abbrev Core := InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore
abbrev Atom := InfoGeometry.Quantum.SplitCliffordAtom.Atom

namespace Core

variable (X : Core)

def oneOp : X →ₗ[ℝ] X := LinearMap.id

def jOp : X →ₗ[ℝ] X := X.J

def epsOp : X →ₗ[ℝ] X := X.eps

def piOp : X →ₗ[ℝ] X := X.Pi

noncomputable def kOp : X →ₗ[ℝ] X := X.K

@[simp] theorem j_sq :
    (jOp X).comp (jOp X) = oneOp X := by
  simpa [jOp, oneOp] using InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.J_sq X

@[simp] theorem eps_sq :
    (epsOp X).comp (epsOp X) = oneOp X := by
  simpa [epsOp, oneOp] using InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.eps_sq X

@[simp] theorem pi_sq :
    (piOp X).comp (piOp X) = oneOp X := by
  simpa [piOp, oneOp] using InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.Pi_sq X

@[simp] theorem j_eps_anticomm :
    (jOp X).comp (epsOp X) = -((epsOp X).comp (jOp X)) := by
  simpa [jOp, epsOp] using InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.J_eps_anticomm X

@[simp] theorem k_eq_j_comp_eps :
    kOp X = (jOp X).comp (epsOp X) := by
  rfl

@[simp] theorem k_sq :
    (kOp X).comp (kOp X) = -(oneOp X) := by
  simpa [kOp, oneOp] using InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.K_sq X

end Core

namespace Atom

variable (X : Atom)

def oneOp : X →ₗ[ℝ] X := InfoGeometry.Quantum.SplitCliffordAtom.Atom.oneOp X

def jOp : X →ₗ[ℝ] X := InfoGeometry.Quantum.SplitCliffordAtom.Atom.jOp X

def epsOp : X →ₗ[ℝ] X := InfoGeometry.Quantum.SplitCliffordAtom.Atom.epsOp X

noncomputable def kOp : X →ₗ[ℝ] X := InfoGeometry.Quantum.SplitCliffordAtom.Atom.kOp X

@[simp] theorem j_sq :
    (jOp X).comp (jOp X) = oneOp X := by
  simpa [jOp, oneOp] using InfoGeometry.Quantum.SplitCliffordAtom.Atom.j_sq X

@[simp] theorem eps_sq :
    (epsOp X).comp (epsOp X) = oneOp X := by
  simpa [epsOp, oneOp] using InfoGeometry.Quantum.SplitCliffordAtom.Atom.eps_sq X

@[simp] theorem j_eps_anticomm :
    (jOp X).comp (epsOp X) = -((epsOp X).comp (jOp X)) := by
  simpa [jOp, epsOp] using InfoGeometry.Quantum.SplitCliffordAtom.Atom.j_eps_anticomm X

@[simp] theorem k_eq_j_comp_eps :
    kOp X = (jOp X).comp (epsOp X) := by
  simpa [kOp, jOp, epsOp] using InfoGeometry.Quantum.SplitCliffordAtom.Atom.k_eq_j_comp_eps X

@[simp] theorem k_sq :
    (kOp X).comp (kOp X) = -(oneOp X) := by
  simpa [kOp, oneOp] using InfoGeometry.Quantum.SplitCliffordAtom.Atom.k_sq X

end Atom

@[simp] theorem J_sq (X : KreinDoubledAtom) :
    X.J.comp X.J = (LinearMap.id : X →ₗ[ℝ] X) :=
  X.toInvolutionCore.J_sq

@[simp] theorem eps_sq (X : KreinDoubledAtom) :
    X.eps.comp X.eps = (LinearMap.id : X →ₗ[ℝ] X) :=
  X.toInvolutionCore.eps_sq

@[simp] theorem J_eps_anti (X : KreinDoubledAtom) :
    X.J.comp X.eps = -(X.eps.comp X.J) :=
  X.J_eps_anticomm

/-- Derived geometric complex-like structure `K := J ∘ ε`. -/
noncomputable def K (X : KreinDoubledAtom) : X →ₗ[ℝ] X :=
  InfoGeometry.Quantum.AnticommutingInvolutionCore.K X

@[simp] theorem K_eq_J_comp_eps (X : KreinDoubledAtom) :
    X.K = X.J.comp X.eps := by
  simpa [K] using (InfoGeometry.Quantum.AnticommutingInvolutionCore.K_def X)

lemma eps_comp_J (X : KreinDoubledAtom) :
    X.eps.comp X.J = -(X.J.comp X.eps) := by
  simpa using (InfoGeometry.Quantum.AnticommutingInvolutionCore.eps_comp_J X)

/-- Foundational emergent-phase theorem: `K² = -Id`. -/
@[simp] theorem K_sq_eq_neg_id (X : KreinDoubledAtom) :
    X.K.comp X.K = -((LinearMap.id : X →ₗ[ℝ] X)) := by
  simpa [K] using (InfoGeometry.Quantum.AnticommutingInvolutionCore.K_sq X)

/-- Ring-style form of `K² = -1` in the endomorphism algebra. -/
@[simp] theorem K_sq_eq_neg_one (X : KreinDoubledAtom) :
    (X.K : Module.End ℝ X) * (X.K : Module.End ℝ X) = -(1 : Module.End ℝ X) := by
  ext x
  change (X.K.comp X.K) x = (-((LinearMap.id : X →ₗ[ℝ] X))) x
  simpa using congrArg (fun f : X →ₗ[ℝ] X => f x) (K_sq_eq_neg_id X)

@[simp] theorem j_comp_k (X : KreinDoubledAtom) :
    X.J.comp X.K = X.eps := by
  simpa [K] using (InfoGeometry.Quantum.AnticommutingInvolutionCore.j_comp_k X)

@[simp] theorem k_comp_j (X : KreinDoubledAtom) :
    X.K.comp X.J = -X.eps := by
  simpa [K] using (InfoGeometry.Quantum.AnticommutingInvolutionCore.k_comp_j X)

@[simp] theorem eps_comp_k (X : KreinDoubledAtom) :
    X.eps.comp X.K = -X.J := by
  simpa [K] using (InfoGeometry.Quantum.AnticommutingInvolutionCore.eps_comp_k X)

@[simp] theorem k_comp_eps (X : KreinDoubledAtom) :
    X.K.comp X.eps = X.J := by
  simpa [K] using (InfoGeometry.Quantum.AnticommutingInvolutionCore.k_comp_eps X)

end KreinDoubledAtom

/-- Forget a real Majorana core to the canonical doubled-atom surface. -/
noncomputable def ofCore
    (X : KreinDoubledAtom.Core) : KreinDoubledAtom :=
  X.toAnticommutingInvolutionCore

/-- Forget a packaged split-Clifford atom to the canonical doubled-atom surface. -/
noncomputable def ofAtom
    (X : KreinDoubledAtom.Atom) : KreinDoubledAtom :=
  X.core.toAnticommutingInvolutionCore

/-- Concrete doubled-space realization of the canonical split `Cl(1,1)` atom. -/
noncomputable def cl11DoubledAtom (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : KreinDoubledAtom :=
  (InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E).toAnticommutingInvolutionCore

end InfoGeometry.Canonical
