/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Cartan.Involution
import Mathlib.Tactic.NoncommRing

/-!
# Dimensionless overlap operators and mixed chiral transport

The algebraic input is a pair of involutions `gamma` and `sigma` in an
arbitrary associative ring. They need not commute or anticommute. The
dimensionless overlap operator is `d = 1 + gamma * sigma`; its modified
chirality is `gamma * (1 - d) = -sigma`. The Ginsparg--Wilson relation and
the mixed intertwining law follow with their multiplication order intact.

This formalizes the finite algebra of Craig, *A gauge-invariant measure for
lattice chiral fermions*, arXiv:2610.09093v1, equations (1.3)--(1.7), after
absorbing the lattice spacing into `d`. The involution `sigma` is supplied;
no spectral sign, lattice operator, locality estimate, determinant-line
connection, or global fermion integration measure is constructed here.

The specialization uses native `Module.End ℝ V` and the existing
`InfoGeometry.Cartan.Pplus` and `Pminus`, without introducing another
projector definition or an external imaginary scalar. Kernel statements
identify the actual zero-mode chirality on this real carrier.
-/

namespace InfoGeometry.OperatorAlgebra.OverlapChirality

section Ring

variable {A : Type*} [Ring A]

/-- The overlap operator with lattice spacing absorbed into its normalization. -/
def overlap (gamma sigma : A) : A := 1 + gamma * sigma

/-- The modified chirality associated with a dimensionless operator. -/
def modifiedChirality (gamma d : A) : A := gamma * (1 - d)

/-- The square defect of modified chirality is the ordered
Ginsparg--Wilson defect multiplied by the original chirality. -/
theorem modifiedChirality_square_defect {gamma : A}
    (hgamma : gamma * gamma = 1) (d : A) :
    modifiedChirality gamma d * modifiedChirality gamma d - 1 =
      -(gamma * (gamma * d + d * gamma - d * gamma * d)) := by
  calc
    modifiedChirality gamma d * modifiedChirality gamma d - 1 =
        (gamma * gamma - 1) -
          gamma * (gamma * d + d * gamma - d * gamma * d) := by
            unfold modifiedChirality
            noncomm_ring
    _ = -(gamma * (gamma * d + d * gamma - d * gamma * d)) := by
      rw [hgamma, sub_self, zero_sub]

/-- For involutive `gamma`, modified chirality is involutive exactly when
the dimensionless Ginsparg--Wilson relation holds. -/
theorem modifiedChirality_sq_iff_ginspargWilson {gamma : A}
    (hgamma : gamma * gamma = 1) (d : A) :
    modifiedChirality gamma d * modifiedChirality gamma d = 1 ↔
      gamma * d + d * gamma = d * gamma * d := by
  constructor
  · intro hmodified
    apply sub_eq_zero.mp
    have hzero : gamma * (gamma * d + d * gamma - d * gamma * d) = 0 := by
      have hdefect := modifiedChirality_square_defect hgamma d
      rw [hmodified, sub_self] at hdefect
      exact neg_eq_zero.mp hdefect.symm
    calc
      gamma * d + d * gamma - d * gamma * d =
          (gamma * gamma) * (gamma * d + d * gamma - d * gamma * d) := by
            rw [hgamma, one_mul]
      _ = gamma * (gamma * (gamma * d + d * gamma - d * gamma * d)) := by
        rw [mul_assoc]
      _ = 0 := by rw [hzero, mul_zero]
  · intro hgw
    apply sub_eq_zero.mp
    rw [modifiedChirality_square_defect hgamma d, hgw, sub_self,
      mul_zero, neg_zero]

/-- The overlap modification is the negative of the supplied sign involution.
Only the square law of `gamma` is needed for this identity. -/
theorem modifiedChirality_overlap {gamma : A}
    (hgamma : gamma * gamma = 1) (sigma : A) :
    modifiedChirality gamma (overlap gamma sigma) = -sigma := by
  unfold modifiedChirality overlap
  calc
    gamma * (1 - (1 + gamma * sigma)) = -((gamma * gamma) * sigma) := by
      noncomm_ring
    _ = -sigma := by rw [hgamma, one_mul]

/-- Both involution square laws give an actual involutive modified chirality. -/
theorem modifiedChirality_overlap_sq {gamma sigma : A}
    (hgamma : gamma * gamma = 1) (hsigma : sigma * sigma = 1) :
    modifiedChirality gamma (overlap gamma sigma) *
      modifiedChirality gamma (overlap gamma sigma) = 1 := by
  simp only [modifiedChirality_overlap hgamma sigma, neg_mul_neg, hsigma]

/-- Two possibly noncommuting involutions produce the dimensionless
Ginsparg--Wilson operator. -/
theorem overlap_ginspargWilson {gamma sigma : A}
    (hgamma : gamma * gamma = 1) (hsigma : sigma * sigma = 1) :
    gamma * overlap gamma sigma + overlap gamma sigma * gamma =
      overlap gamma sigma * gamma * overlap gamma sigma :=
  (modifiedChirality_sq_iff_ginspargWilson hgamma (overlap gamma sigma)).mp
    (modifiedChirality_overlap_sq hgamma hsigma)

/-- The mixed chirality intertwining law is another exact formulation of
Ginsparg--Wilson. This equivalence itself does not need a square law. -/
theorem ginspargWilson_iff_intertwines (gamma d : A) :
    gamma * d + d * gamma = d * gamma * d ↔
      d * modifiedChirality gamma d = -(gamma * d) := by
  rw [eq_neg_iff_add_eq_zero]
  have hexpand : d * modifiedChirality gamma d + gamma * d =
      gamma * d + d * gamma - d * gamma * d := by
    unfold modifiedChirality
    noncomm_ring
  rw [hexpand, sub_eq_zero]

/-- Original chirality on the output is minus modified chirality on the input. -/
theorem gamma_mul_of_ginspargWilson {gamma d : A}
    (hgw : gamma * d + d * gamma = d * gamma * d) :
    gamma * d = -(d * modifiedChirality gamma d) := by
  rw [(ginspargWilson_iff_intertwines gamma d).mp hgw, neg_neg]

section Star

variable [StarRing A]

/-- Self-adjoint input involutions give gamma-Hermiticity of the overlap
operator. The square law of `sigma` is not required for this star identity. -/
theorem star_overlap {gamma sigma : A}
    (hgamma : gamma * gamma = 1)
    (hgammaStar : star gamma = gamma) (hsigmaStar : star sigma = sigma) :
    star (overlap gamma sigma) = gamma * overlap gamma sigma * gamma := by
  unfold overlap
  rw [star_add, star_one, star_mul, hgammaStar, hsigmaStar]
  symm
  calc
    gamma * (1 + gamma * sigma) * gamma =
        gamma * gamma + (gamma * gamma) * sigma * gamma := by
          noncomm_ring
    _ = 1 + sigma * gamma := by simp only [hgamma, one_mul]

/-- Modified overlap chirality is self-adjoint whenever the supplied
sign involution is self-adjoint. -/
theorem star_modifiedChirality_overlap {gamma sigma : A}
    (hgamma : gamma * gamma = 1) (hsigmaStar : star sigma = sigma) :
    star (modifiedChirality gamma (overlap gamma sigma)) =
      modifiedChirality gamma (overlap gamma sigma) := by
  simp only [modifiedChirality_overlap hgamma sigma, star_neg, hsigmaStar]

end Star
end Ring

section RealEndomorphisms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The existing negative modified projector is intertwined with the
existing positive original projector. The two chiralities need not agree. -/
theorem mul_Pminus_modifiedChirality {gamma d : Module.End ℝ V}
    (hgw : gamma * d + d * gamma = d * gamma * d) :
    d * Cartan.Pminus (modifiedChirality gamma d) = Cartan.Pplus gamma * d := by
  dsimp [Cartan.Pminus, Cartan.Pplus]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  calc
    d * (1 - modifiedChirality gamma d) =
        d - d * modifiedChirality gamma d := by noncomm_ring
    _ = d + gamma * d := by
      rw [(ginspargWilson_iff_intertwines gamma d).mp hgw, sub_neg_eq_add]
    _ = (1 + gamma) * d := by noncomm_ring

/-- The opposite mixed projector transport follows with the opposite sign. -/
theorem mul_Pplus_modifiedChirality {gamma d : Module.End ℝ V}
    (hgw : gamma * d + d * gamma = d * gamma * d) :
    d * Cartan.Pplus (modifiedChirality gamma d) = Cartan.Pminus gamma * d := by
  dsimp [Cartan.Pminus, Cartan.Pplus]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  calc
    d * (1 + modifiedChirality gamma d) =
        d + d * modifiedChirality gamma d := by noncomm_ring
    _ = d - gamma * d := by
      rw [(ginspargWilson_iff_intertwines gamma d).mp hgw, sub_eq_add_neg]
    _ = (1 - gamma) * d := by noncomm_ring

/-- The constructed overlap operator transports the negative modified
chiral sector to the positive original sector. -/
theorem overlap_Pminus_intertwines {gamma sigma : Module.End ℝ V}
    (hgamma : gamma * gamma = 1) (hsigma : sigma * sigma = 1) :
    overlap gamma sigma * Cartan.Pminus (modifiedChirality gamma (overlap gamma sigma)) =
      Cartan.Pplus gamma * overlap gamma sigma :=
  mul_Pminus_modifiedChirality (overlap_ginspargWilson hgamma hsigma)

/-- The constructed overlap operator transports the positive modified
chiral sector to the negative original sector. -/
theorem overlap_Pplus_intertwines {gamma sigma : Module.End ℝ V}
    (hgamma : gamma * gamma = 1) (hsigma : sigma * sigma = 1) :
    overlap gamma sigma * Cartan.Pplus (modifiedChirality gamma (overlap gamma sigma)) =
      Cartan.Pminus gamma * overlap gamma sigma :=
  mul_Pplus_modifiedChirality (overlap_ginspargWilson hgamma hsigma)

/-- On the actual kernel, modified chirality agrees with original chirality. -/
theorem modifiedChirality_apply_of_mem_ker {gamma d : Module.End ℝ V} {x : V}
    (hx : x ∈ LinearMap.ker d) : modifiedChirality gamma d x = gamma x := by
  rw [LinearMap.mem_ker] at hx
  simp only [modifiedChirality, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, hx, sub_zero]

/-- The Ginsparg--Wilson relation makes the native kernel invariant under
original chirality, even though the full operator need not anticommute with it. -/
theorem gamma_apply_mem_ker {gamma d : Module.End ℝ V}
    (hgw : gamma * d + d * gamma = d * gamma * d) {x : V}
    (hx : x ∈ LinearMap.ker d) : gamma x ∈ LinearMap.ker d := by
  rw [LinearMap.mem_ker] at hx ⊢
  have h := congrArg (fun T : Module.End ℝ V => T x) hgw
  simpa only [LinearMap.add_apply, Module.End.mul_apply, hx, map_zero, zero_add] using h

/-- Zero modes of the overlap operator are precisely the vectors on which
the supplied sign operator acts as negative original chirality. -/
theorem mem_ker_overlap_iff {gamma sigma : Module.End ℝ V}
    (hgamma : gamma * gamma = 1) (x : V) :
    x ∈ LinearMap.ker (overlap gamma sigma) ↔ sigma x = -(gamma x) := by
  have hgammaApply (v : V) : gamma (gamma v) = v := by
    simpa only [Module.End.mul_apply, Module.End.one_apply] using
      congrArg (fun T : Module.End ℝ V => T v) hgamma
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    have hsum : gamma x + sigma x = 0 := by
      have h := congrArg (fun v : V => gamma v) hx
      simpa only [overlap, LinearMap.add_apply, Module.End.one_apply,
        Module.End.mul_apply, map_add, hgammaApply, map_zero] using h
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hsum
  · intro hx
    simp only [overlap, LinearMap.add_apply, Module.End.one_apply,
      Module.End.mul_apply, hx, map_neg, hgammaApply, add_neg_cancel]

end RealEndomorphisms

end InfoGeometry.OperatorAlgebra.OverlapChirality
