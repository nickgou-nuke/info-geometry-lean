import InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameEquivariance
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.B3PresentedGroup

/-!
# Jones braid monodromy does not factor through the permutation shadow

The native presented `B₃` has both a finite permutation shadow in `S₃` and
the Jones/Temperley--Lieb representation in `GL₈(ℂ)`.  This owner proves
that the latter does not factor through the former: an adjacent transposition
squares to `1`, whereas its Jones generator squares to `-I`.

Consequently the finite deck-permutation monodromy of unordered
configurations cannot by itself recover the Jones/Yang--Baxter phase.  No
claim about the nonexistence of a richer local-system monodromy is made.
-/

noncomputable section

namespace InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction

open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance
open InfoGeometry.Topology.ArtinBraidS3Quotient
open PresentedGroup

/-- The first presented `B₃` generator maps to the first adjacent
transposition under the native permutation shadow. -/
@[simp] theorem braidPermutation_sig0 :
    braidPermutation (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) =
      sigma1 := by
  change PresentedGroup.toGroup (f := permutationGenerator)
      (rels := b3Relations) _ (PresentedGroup.of B3Gen.sig0) = sigma1
  rw [PresentedGroup.toGroup.of]
  rfl

/-- The second presented `B₃` generator maps to the second adjacent
transposition under the native permutation shadow. -/
@[simp] theorem braidPermutation_sig1 :
    braidPermutation (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) =
      sigma2 := by
  change PresentedGroup.toGroup (f := permutationGenerator)
      (rels := b3Relations) _ (PresentedGroup.of B3Gen.sig1) = sigma2
  rw [PresentedGroup.toGroup.of]
  rfl

/-- The square of the first braid generator lies in the kernel of the finite
permutation shadow. -/
@[simp] theorem braidPermutation_sig0_sq :
    braidPermutation
        ((PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) *
          PresentedGroup.of B3Gen.sig0) = 1 := by
  rw [map_mul, braidPermutation_sig0, sigma1_sq]

/-- A concrete pure element of the presented braid group: the square of the
first Artin generator.  "Pure" here means kernel of the native permutation
shadow; no configuration-space identification is asserted. -/
def firstGeneratorSquare : BoundaryBraidGroup :=
  (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) *
    PresentedGroup.of B3Gen.sig0

/-- The first-generator square belongs to the kernel of the finite
permutation shadow. -/
@[simp] theorem firstGeneratorSquare_permutation :
    braidPermutation firstGeneratorSquare = 1 := by
  exact braidPermutation_sig0_sq

/-- The Jones representation retains the exact central phase `-I` on the
first-generator square that the permutation shadow kills. -/
theorem jonesBraidRepresentation_firstGeneratorSquare_val :
    (phi firstGeneratorSquare : Matrix (Fin 8) (Fin 8) ℂ) =
      -(1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  rw [firstGeneratorSquare, map_mul, phi_sig0]
  exact s0_sq_eq_neg_one

/-- The same square is not killed by the Jones representation: its matrix is
`-I`, not `I`. -/
theorem jonesBraidRepresentation_sig0_sq_ne_one :
    phi ((PresentedGroup.of B3Gen.sig0 : B3) *
      PresentedGroup.of B3Gen.sig0) ≠ 1 := by
  intro h
  rw [map_mul, phi_sig0] at h
  have hmatrix := congrArg Units.val h
  change InfoGeometry.Physics.JonesBraidB3.s0 *
      InfoGeometry.Physics.JonesBraidB3.s0 = 1 at hmatrix
  rw [s0_sq_eq_neg_one] at hmatrix
  have hentry := congrArg
    (fun M : Matrix (Fin 8) (Fin 8) ℂ => M 0 0) hmatrix
  norm_num at hentry

/-- The Jones/Temperley--Lieb `B₃ → GL₈(ℂ)` representation does not
factor through the finite permutation shadow `B₃ → S₃`.

This is the precise obstruction to identifying finite covering-permutation
monodromy with the native Jones/Yang--Baxter representation. -/
theorem jonesBraidRepresentation_not_factor_through_permutation :
    ¬ ∃ psi : Equiv.Perm (Fin 3) →* GL8,
      psi.comp braidPermutation = phi := by
  rintro ⟨psi, hpsi⟩
  let g0 : BoundaryBraidGroup := PresentedGroup.of B3Gen.sig0
  apply jonesBraidRepresentation_sig0_sq_ne_one
  calc
    phi (g0 * g0) = (psi.comp braidPermutation) (g0 * g0) :=
      congrArg (fun f : B3 →* GL8 => f (g0 * g0)) hpsi.symm
    _ = psi (braidPermutation (g0 * g0)) := rfl
    _ = psi 1 := by rw [braidPermutation_sig0_sq]
    _ = 1 := map_one psi

end InfoGeometry.Projective.ProjectiveNullBoundaryJonesPermutationObstruction
