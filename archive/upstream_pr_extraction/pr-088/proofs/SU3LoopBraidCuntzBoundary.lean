import proofs.GellMannSU3
import proofs.BogoliubovBraidGraphWeld
import proofs.GellMannParafermionSolder
import proofs.CantorBoundaryCuntzFamily

/-!
# Finite loop-mode and braid relations for `SU(3)` data

This file records finite algebraic equalities used by downstream files:

* selected Gell--Mann commutators inserted into Laurent modes;
* mode addition for the corresponding current-algebra bracket without central
  extension;
* the `S₃` Artin relation induced by the two adjacent transpositions;
* the same Artin relation for q-scaled color braid operators on four lanes.
-/

noncomputable section

namespace SU3LoopBraidCuntzBoundary

open GellMannSU3
open BogoliubovBraidGraphWeld
open BogoliubovSU3ParafermionProofChain
open CantorBoundaryCuntzFamily

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ

/-- A single Laurent/loop mode `A z^m` with integer mode and matrix coefficient. -/
structure SU3LoopMode where
  mode : ℤ
  coeff : M3C

/-- Current-algebra bracket without central extension: `[A z^m, B z^n] = [A,B] z^(m+n)`. -/
def loopBracket (X Y : SU3LoopMode) : SU3LoopMode where
  mode := X.mode + Y.mode
  coeff := X.coeff * Y.coeff - Y.coeff * X.coeff

/-- Scalar multiplication of loop modes. -/
def loopSmul (c : ℂ) (X : SU3LoopMode) : SU3LoopMode where
  mode := X.mode
  coeff := c • X.coeff

/-- Gell--Mann matrix inserted as a loop mode. -/
def gellMannLoopMode (m : ℤ) (A : M3C) : SU3LoopMode where
  mode := m
  coeff := A

/-- The seed `su(3)` commutator lifts to loop modes by adding mode numbers. -/
theorem loop_gl1_gl2_commutator (m n : ℤ) :
    loopBracket (gellMannLoopMode m gl1) (gellMannLoopMode n gl2) =
      loopSmul (2 * Complex.I) (gellMannLoopMode (m + n) gl3) := by
  unfold loopBracket loopSmul gellMannLoopMode
  simp [gl1_comm_gl2]

/-- The second seed commutator also lifts to loop modes. -/
theorem loop_gl1_gl3_commutator (m n : ℤ) :
    loopBracket (gellMannLoopMode m gl1) (gellMannLoopMode n gl3) =
      loopSmul (-2 * Complex.I) (gellMannLoopMode (m + n) gl2) := by
  unfold loopBracket loopSmul gellMannLoopMode
  simp [gl1_comm_gl3]



/-- The two adjacent transpositions in `S₃` satisfy the Artin relation. -/
theorem braid_shadow_s3_artin :
    B3RepresentationBridge.s3_rep.σ0 * B3RepresentationBridge.s3_rep.σ1 *
      B3RepresentationBridge.s3_rep.σ0 =
    B3RepresentationBridge.s3_rep.σ1 * B3RepresentationBridge.s3_rep.σ0 *
      B3RepresentationBridge.s3_rep.σ1 :=
  color_braid_underlying_s3_artin

/-- q-scaled color braid operators satisfy Artin on three color lanes plus one singlet lane. -/
theorem q_color_braid_loop_boundary_artin {V : Type*}
    [AddCommMonoid V] [Module ℂ V] (q : ℂ) (ψ : ColorSpinor4 V) :
    qColorSigma0 q (qColorSigma1 q (qColorSigma0 q ψ)) =
      qColorSigma1 q (qColorSigma0 q (qColorSigma1 q ψ)) :=
  qColorBraid4_artin q ψ

/-- The two loop-mode commutator identities and the two Artin identities hold together. -/
theorem su3_loop_braid_cuntz_boundary_synthesis {V : Type*}
    [AddCommMonoid V] [Module ℂ V]
    (m n : ℤ) (q : ℂ) (ψ : ColorSpinor4 V) :
    loopBracket (gellMannLoopMode m gl1) (gellMannLoopMode n gl2) =
      loopSmul (2 * Complex.I) (gellMannLoopMode (m + n) gl3) ∧
    loopBracket (gellMannLoopMode m gl1) (gellMannLoopMode n gl3) =
      loopSmul (-2 * Complex.I) (gellMannLoopMode (m + n) gl2) ∧
    B3RepresentationBridge.s3_rep.σ0 * B3RepresentationBridge.s3_rep.σ1 *
        B3RepresentationBridge.s3_rep.σ0 =
      B3RepresentationBridge.s3_rep.σ1 * B3RepresentationBridge.s3_rep.σ0 *
        B3RepresentationBridge.s3_rep.σ1 ∧
    qColorSigma0 q (qColorSigma1 q (qColorSigma0 q ψ)) =
      qColorSigma1 q (qColorSigma0 q (qColorSigma1 q ψ)) := by
  exact ⟨loop_gl1_gl2_commutator m n,
    loop_gl1_gl3_commutator m n,
    braid_shadow_s3_artin,
    q_color_braid_loop_boundary_artin q ψ⟩

end SU3LoopBraidCuntzBoundary

end noncomputable section
