import InfoGeometry.Canonical.KreinDoubledAtom

/-!
# `K`-Linear Representation

Owner-level real representation theory for the canonical doubled split `Cl(1,1)`
atom.

The internal complex-like axis is the derived endomorphism `K := J ∘ ε` with
`K² = -Id`. Operators commuting with `K` play the role of complex-linear maps,
while operators anticommuting with `K` play the role of complex-antilinear maps,
but entirely over `ℝ`.
-/

namespace InfoGeometry.Canonical.KLinearRepresentation

open InfoGeometry.Canonical

/-- Endomorphisms commuting with the internal axis `K`. -/
def IsKLinear (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) : Prop :=
  f.comp X.K = X.K.comp f

/-- Endomorphisms anticommuting with the internal axis `K`. -/
def IsKAntilinear (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) : Prop :=
  f.comp X.K = -(X.K.comp f)

/-- Conjugation of an endomorphism by the internal axis `K`. -/
noncomputable def kConjugate (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) : X →ₗ[ℝ] X :=
  X.K.comp (f.comp X.K)

/-- The `K`-linear projection of a real endomorphism. -/
noncomputable def kLinearPart (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) : X →ₗ[ℝ] X :=
  (1 / 2 : ℝ) • (f - kConjugate X f)

/-- The `K`-antilinear projection of a real endomorphism. -/
noncomputable def kAntilinearPart (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) : X →ₗ[ℝ] X :=
  (1 / 2 : ℝ) • (f + kConjugate X f)

@[simp] theorem kLinearPart_add_kAntilinearPart
    (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) :
    kLinearPart X f + kAntilinearPart X f = f := by
  unfold kLinearPart kAntilinearPart
  calc
    (1 / 2 : ℝ) • (f - kConjugate X f) +
        (1 / 2 : ℝ) • (f + kConjugate X f)
      = ((1 / 2 : ℝ) • f - (1 / 2 : ℝ) • kConjugate X f) +
          ((1 / 2 : ℝ) • f + (1 / 2 : ℝ) • kConjugate X f) := by
            simp [smul_sub, smul_add]
    _ = (1 / 2 : ℝ) • f + (1 / 2 : ℝ) • f := by
          abel
    _ = (2 : ℝ) • ((1 / 2 : ℝ) • f) := by
          simpa [two_smul] using (two_smul ℝ ((1 / 2 : ℝ) • f)).symm
    _ = ((2 : ℝ) * (1 / 2 : ℝ)) • f := by
          simp [smul_smul]
    _ = f := by
          norm_num

@[simp] theorem id_isKLinear
    (X : KreinDoubledAtom) :
    IsKLinear X (LinearMap.id : X →ₗ[ℝ] X) := by
  simp [IsKLinear]

@[simp] theorem K_isKLinear
    (X : KreinDoubledAtom) :
    IsKLinear X X.K := by
  simp [IsKLinear]

@[simp] theorem J_isKAntilinear
    (X : KreinDoubledAtom) :
    IsKAntilinear X X.J := by
  unfold IsKAntilinear
  rw [X.j_comp_k, X.k_comp_j]
  simp

@[simp] theorem eps_isKAntilinear
    (X : KreinDoubledAtom) :
    IsKAntilinear X X.eps := by
  unfold IsKAntilinear
  rw [X.eps_comp_k, X.k_comp_eps]

lemma kConjugate_comp_K
    (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) :
    (kConjugate X f).comp X.K = -((X.K).comp f) := by
  calc
    (kConjugate X f).comp X.K
        = X.K.comp ((f.comp X.K).comp X.K) := by
            simp [kConjugate, LinearMap.comp_assoc]
    _ = X.K.comp (f.comp (X.K.comp X.K)) := by
          simp [LinearMap.comp_assoc]
    _ = X.K.comp (f.comp (-(LinearMap.id : X →ₗ[ℝ] X))) := by
          rw [X.K_sq_eq_neg_id]
    _ = -((X.K).comp (f.comp (LinearMap.id : X →ₗ[ℝ] X))) := by
          simp
    _ = -((X.K).comp f) := by
          simp

lemma K_comp_kConjugate
    (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) :
    X.K.comp (kConjugate X f) = -(f.comp X.K) := by
  calc
    X.K.comp (kConjugate X f)
        = (X.K.comp X.K).comp (f.comp X.K) := by
            simp [kConjugate, LinearMap.comp_assoc]
    _ = (-(LinearMap.id : X →ₗ[ℝ] X)).comp (f.comp X.K) := by
          rw [X.K_sq_eq_neg_id]
    _ = -(f.comp X.K) := by
          simp

lemma neg_kConjugate_comp_K
    (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) :
    -((kConjugate X f).comp X.K) = X.K.comp f := by
  simpa using congrArg Neg.neg (kConjugate_comp_K X f)

lemma neg_K_comp_kConjugate
    (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) :
    -(X.K.comp (kConjugate X f)) = f.comp X.K := by
  simpa using congrArg Neg.neg (K_comp_kConjugate X f)

theorem kLinearPart_isKLinear
    (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) :
    IsKLinear X (kLinearPart X f) := by
  ext x
  change kLinearPart X f (X.K x) = X.K (kLinearPart X f x)
  have hK2x : X.K (X.K x) = -x := by
    simpa using congrArg (fun g : X →ₗ[ℝ] X => g x) (X.K_sq_eq_neg_id)
  have hK2fKx : X.K (X.K (f (X.K x))) = -(f (X.K x)) := by
    simpa using congrArg (fun g : X →ₗ[ℝ] X => g (f (X.K x))) (X.K_sq_eq_neg_id)
  have hKfK2x : X.K (f (X.K (X.K x))) = -(X.K (f x)) := by
    rw [hK2x]
    simp
  unfold kLinearPart kConjugate
  calc
    (1 / 2 : ℝ) • (f (X.K x) - X.K (f (X.K (X.K x))))
        = (1 / 2 : ℝ) • (f (X.K x) + X.K (f x)) := by
            rw [hKfK2x]
            abel_nf
    _ = (1 / 2 : ℝ) • (X.K (f x) + f (X.K x)) := by
          abel_nf
    _ = (1 / 2 : ℝ) • (X.K (f x) - X.K (X.K (f (X.K x)))) := by
          rw [hK2fKx]
          abel_nf
    _ = (1 / 2 : ℝ) • X.K (f x - X.K (f (X.K x))) := by
          simp [map_sub]
    _ = X.K ((1 / 2 : ℝ) • (f x - X.K (f (X.K x)))) := by
          simp

theorem kAntilinearPart_isKAntilinear
    (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) :
    IsKAntilinear X (kAntilinearPart X f) := by
  ext x
  change kAntilinearPart X f (X.K x) = -(X.K (kAntilinearPart X f x))
  have hK2x : X.K (X.K x) = -x := by
    simpa using congrArg (fun g : X →ₗ[ℝ] X => g x) (X.K_sq_eq_neg_id)
  have hK2fKx : X.K (X.K (f (X.K x))) = -(f (X.K x)) := by
    simpa using congrArg (fun g : X →ₗ[ℝ] X => g (f (X.K x))) (X.K_sq_eq_neg_id)
  have hKfK2x : X.K (f (X.K (X.K x))) = -(X.K (f x)) := by
    rw [hK2x]
    simp
  unfold kAntilinearPart kConjugate
  calc
    (1 / 2 : ℝ) • (f (X.K x) + X.K (f (X.K (X.K x))))
        = (1 / 2 : ℝ) • (f (X.K x) - X.K (f x)) := by
            rw [hKfK2x]
            abel_nf
    _ = (1 / 2 : ℝ) • (-(X.K (f x) - f (X.K x))) := by
          congr 1
          abel_nf
    _ = -((1 / 2 : ℝ) • (X.K (f x) - f (X.K x))) := by
          simp [smul_neg]
    _ = -((1 / 2 : ℝ) • (X.K (f x) + X.K (X.K (f (X.K x))))) := by
          rw [hK2fKx]
          abel_nf
    _ = -((1 / 2 : ℝ) • X.K (f x + X.K (f (X.K x)))) := by
          simp [map_add]
    _ = -(X.K ((1 / 2 : ℝ) • (f x + X.K (f (X.K x))))) := by
          simp

/-- Bundled `K`-linear / `K`-antilinear decomposition of an endomorphism. -/
structure PolarizedDecomposition
    (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) where
  lin : X →ₗ[ℝ] X
  anti : X →ₗ[ℝ] X
  h_lin : IsKLinear X lin
  h_anti : IsKAntilinear X anti
  h_sum : f = lin + anti

/-- Canonical `K`-polarized decomposition of a real endomorphism. -/
noncomputable def polarizedDecomposition
    (X : KreinDoubledAtom) (f : X →ₗ[ℝ] X) :
    PolarizedDecomposition X f where
  lin := kLinearPart X f
  anti := kAntilinearPart X f
  h_lin := kLinearPart_isKLinear X f
  h_anti := kAntilinearPart_isKAntilinear X f
  h_sum := (kLinearPart_add_kAntilinearPart X f).symm

end InfoGeometry.Canonical.KLinearRepresentation
