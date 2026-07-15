import InfoGeometry.Canonical.KreinDoubledAtom
import InfoGeometry.Clifford.RealMod8Classification

/-!
# Varlamov discrete symmetry facade for the split modular atom

The repo's split doubled atom realizes the local Varlamov triple

  W = epsilon,
  E = J,
  C = E W = J epsilon = K,

with signature `(+, +, -)`.
-/

namespace InfoGeometry.Canonical

namespace KreinDoubledAtom

open RealMod8Classification

/-- Varlamov grade involution `W`, realized by `epsilon`. -/
def varlamovW (X : KreinDoubledAtom) : X →ₗ[ℝ] X :=
  X.eps

/-- Varlamov reversion operator `E`, realized by `J`. -/
def varlamovE (X : KreinDoubledAtom) : X →ₗ[ℝ] X :=
  X.J

/-- Varlamov conjugation `C = E W`, realized by `K = J epsilon`. -/
noncomputable def varlamovC (X : KreinDoubledAtom) : X →ₗ[ℝ] X :=
  X.K

@[simp] theorem varlamovW_sq (X : KreinDoubledAtom) :
    (varlamovW X).comp (varlamovW X)
      =
    (LinearMap.id : X →ₗ[ℝ] X) := by
  exact eps_sq X

@[simp] theorem varlamovE_sq (X : KreinDoubledAtom) :
    (varlamovE X).comp (varlamovE X)
      =
    (LinearMap.id : X →ₗ[ℝ] X) := by
  exact J_sq X

@[simp] theorem varlamovC_eq_E_comp_W (X : KreinDoubledAtom) :
    varlamovC X = (varlamovE X).comp (varlamovW X) := by
  exact K_eq_J_comp_eps X

@[simp] theorem varlamovE_W_anticomm (X : KreinDoubledAtom) :
    (varlamovE X).comp (varlamovW X)
      =
    -((varlamovW X).comp (varlamovE X)) := by
  exact J_eps_anti X

@[simp] theorem varlamovC_sq_neg_id (X : KreinDoubledAtom) :
    (varlamovC X).comp (varlamovC X)
      =
    -((LinearMap.id : X →ₗ[ℝ] X)) := by
  exact K_sq_eq_neg_id X

/--
The repo's split modular atom has Varlamov signature `(+, +, -)`.
-/
def varlamovSignatureOfSplitAtom : VarlamovSignature :=
  VarlamovSignature.ppm

@[simp] theorem coverGroupKind_varlamovSignatureOfSplitAtom :
    coverGroupKind varlamovSignatureOfSplitAtom = DiscreteCoverGroupKind.D4 := by
  rfl

@[simp] theorem cliffordianKind_varlamovSignatureOfSplitAtom :
    cliffordianKind varlamovSignatureOfSplitAtom = CliffordianKind.cliffordian := by
  rfl

/--
Constructive Varlamov signature theorem for the split modular atom:

`W² = +1`, `E² = +1`, `C² = -1`.
-/
theorem varlamov_signature_plus_plus_minus (X : KreinDoubledAtom) :
    ((varlamovW X).comp (varlamovW X)
        =
      (LinearMap.id : X →ₗ[ℝ] X))
    ∧
    ((varlamovE X).comp (varlamovE X)
        =
      (LinearMap.id : X →ₗ[ℝ] X))
    ∧
    ((varlamovC X).comp (varlamovC X)
        =
      -((LinearMap.id : X →ₗ[ℝ] X))) := by
  exact ⟨varlamovW_sq X, varlamovE_sq X, varlamovC_sq_neg_id X⟩

end KreinDoubledAtom

end InfoGeometry.Canonical
