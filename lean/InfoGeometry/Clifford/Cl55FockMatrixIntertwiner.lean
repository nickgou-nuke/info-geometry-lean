import InfoGeometry.Clifford.Cl55ExteriorSpinorCoordinateReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55NeutralFockFaithfulness

/-!
# Fock-to-coordinate matrix transport for the neutral Clifford module

This owner records the representation-level transport supplied by the
coordinate basis of `Λ• (ℝ⁵)`.  It deliberately does not identify this
coordinate matrix representation with the separate recursive `Cl(5,5)` gamma
realisation: that identification requires the generator-by-generator
wedge/contraction calculation and belongs to the next comparison layer.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55FockMatrixIntertwiner

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.Cl55NeutralFockFaithfulness

abbrev A := CliffordAlgebra (canonicalNeutralFormUnscaled (E := V5))
abbrev S := Spinor
abbrev SCoord := InfoGeometry.Algebra.FiniteSpin.Vec32R

/-- A generator-level equality of Clifford algebra homomorphisms extends to the
whole Clifford algebra.  This is the reusable universal-property wrapper used
by concrete Fock/gamma comparisons. -/
theorem cliffordAlgHom_ext_of_ι
    {R M B : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Semiring B] [Algebra R B]
    (Q : QuadraticForm R M)
    (f g : CliffordAlgebra Q →ₐ[R] B)
    (h : ∀ x, f (CliffordAlgebra.ι Q x) = g (CliffordAlgebra.ι Q x)) :
    f = g := by
  apply CliffordAlgebra.hom_ext
  ext x
  exact h x

/-! The coordinate matrix representation is faithful because it is the
composition of the faithful Fock representation with two algebra
equivalences (conjugation by the coordinate linear equivalence and the
Mathlib basis-to-matrix equivalence). -/

theorem neutralCliffordRepCoordinate_injective :
    Function.Injective neutralCliffordRepCoordinate := by
  exact (spinorCoordinateEquiv.conjAlgEquiv ℝ).injective.comp
    neutralCliffordRep_injective

theorem neutralCliffordCoordinateMatrixRep_injective :
    Function.Injective
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.neutralCliffordCoordinateMatrixRep := by
  exact (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32))).injective.comp
    neutralCliffordRepCoordinate_injective

/-! The coordinate conjugation is an actual intertwiner on vectors, not merely
an equality of algebra homomorphisms. -/

theorem spinorCoordinateEquiv_intertwines
    (a : A) (ψ : S) :
    spinorCoordinateEquiv (neutralCliffordRep a ψ) =
      neutralCliffordRepCoordinate a (spinorCoordinateEquiv ψ) := by
  simp [neutralCliffordRepCoordinate,
    LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]

theorem spinorCoordinateEquiv_intertwines_generator
    (w : NeutralSpace) (ψ : S) :
    spinorCoordinateEquiv (neutralCliffordRep
      (CliffordAlgebra.ι (canonicalNeutralFormUnscaled (E := V5)) w) ψ) =
      (spinorCoordinateEquiv.conjAlgEquiv ℝ (neutralAction w))
        (spinorCoordinateEquiv ψ) := by
  rw [neutralCliffordRep_ι]
  simp [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]

/-! Since the source Clifford algebra and the coordinate endomorphism algebra
have the same finite dimension, faithfulness upgrades to an algebra
equivalence.  This is the concrete `Cl(W) ≃ End(Λ•V)` statement; comparison
with the separately defined recursive gamma algebra equivalence is a later
generator-calibration theorem. -/

theorem neutralCliffordRepCoordinate_surjective :
    Function.Surjective neutralCliffordRepCoordinate := by
  letI : FiniteDimensional ℝ (InfoGeometry.Clifford.Clifford55.Cl55) :=
    LinearEquiv.finiteDimensional
      InfoGeometry.Clifford.Clifford55.cl55SpinorAlgEquiv.toLinearEquiv.symm
  letI : FiniteDimensional ℝ A :=
    LinearEquiv.finiteDimensional
      Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.toLinearEquiv.symm
  letI : FiniteDimensional ℝ SCoord := inferInstance
  have hdim : Module.finrank ℝ A =
      Module.finrank ℝ (Module.End ℝ SCoord) := by
    rw [Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.toLinearEquiv.finrank_eq]
    rw [InfoGeometry.Clifford.Clifford55.cl55_finrank]
    simp [Module.finrank_linearMap, SCoord]
  have hinj : Function.Injective neutralCliffordRepCoordinate.toLinearMap :=
    neutralCliffordRepCoordinate_injective
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

theorem neutralCliffordRepCoordinate_bijective :
    Function.Bijective neutralCliffordRepCoordinate :=
  ⟨neutralCliffordRepCoordinate_injective,
    neutralCliffordRepCoordinate_surjective⟩

noncomputable def neutralCliffordFockAlgEquiv :
    A ≃ₐ[ℝ] Module.End ℝ SCoord :=
  AlgEquiv.ofBijective neutralCliffordRepCoordinate
    neutralCliffordRepCoordinate_bijective

theorem neutralCliffordFockAlgEquiv_toAlgHom :
    neutralCliffordFockAlgEquiv.toAlgHom = neutralCliffordRepCoordinate := by
  apply AlgHom.ext
  intro a
  exact AlgEquiv.ofBijective_apply neutralCliffordRepCoordinate
    neutralCliffordRepCoordinate_bijective a

theorem neutralCliffordFockAlgEquiv_ι (w : NeutralSpace) :
    neutralCliffordFockAlgEquiv
        (CliffordAlgebra.ι (canonicalNeutralFormUnscaled (E := V5)) w) =
      spinorCoordinateEquiv.conjAlgEquiv ℝ (neutralAction w) := by
  change neutralCliffordFockAlgEquiv.toAlgHom
      (CliffordAlgebra.ι (canonicalNeutralFormUnscaled (E := V5)) w) = _
  rw [neutralCliffordFockAlgEquiv_toAlgHom]
  exact neutralCliffordRepCoordinate_ι w

/-! The usual matrix algebra is obtained by the kernel-owned basis
equivalence, with no new matrix carrier. -/

noncomputable def neutralCliffordFockMatrixAlgEquiv :
    A ≃ₐ[ℝ] Matrix (Fin 32) (Fin 32) ℝ :=
  neutralCliffordFockAlgEquiv.trans
    (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32)))

theorem neutralCliffordFockMatrixAlgEquiv_injective :
    Function.Injective neutralCliffordFockMatrixAlgEquiv :=
  neutralCliffordFockMatrixAlgEquiv.injective

@[simp] theorem neutralCliffordFockMatrixAlgEquiv_ι (w : NeutralSpace) :
    neutralCliffordFockMatrixAlgEquiv
        (CliffordAlgebra.ι (canonicalNeutralFormUnscaled (E := V5)) w) =
      (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32)))
        (spinorCoordinateEquiv.conjAlgEquiv ℝ (neutralAction w)) := by
  change (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32)))
      (neutralCliffordFockAlgEquiv
        (CliffordAlgebra.ι (canonicalNeutralFormUnscaled (E := V5)) w)) = _
  rw [neutralCliffordFockAlgEquiv_ι]

theorem neutralCliffordFockMatrixAlgEquiv_toAlgHom :
    neutralCliffordFockMatrixAlgEquiv.toAlgHom =
      (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32))).toAlgHom.comp
        neutralCliffordRepCoordinate := by
  apply AlgHom.ext
  intro a
  change (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32)))
      (neutralCliffordFockAlgEquiv a) = _
  have h := congrArg (fun f => f a)
    neutralCliffordFockAlgEquiv_toAlgHom
  simpa using congrArg
    (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32))) h

/-! The two faithful matrix realisations are therefore related by a canonical
algebra automorphism of the matrix algebra.  This records the comparison
without falsely identifying matrices written in different spinor bases. -/

noncomputable def fockToRecursiveMatrixAlgEquiv :
    Matrix (Fin 32) (Fin 32) ℝ ≃ₐ[ℝ]
      InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  neutralCliffordFockMatrixAlgEquiv.symm.trans
    Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixAlgEquiv

@[simp] theorem fockToRecursiveMatrixAlgEquiv_fock (a : A) :
    fockToRecursiveMatrixAlgEquiv
        (neutralCliffordFockMatrixAlgEquiv a) =
      Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixAlgEquiv a := by
  simp [fockToRecursiveMatrixAlgEquiv]

/-! The pointwise comparison is equivalently an equality of algebra
homomorphisms out of the neutral Clifford algebra.  This is the universal-
property closure of the comparison; no matrix-entry calculation is needed. -/
theorem fockToRecursiveMatrixAlgEquiv_comp_fock :
    fockToRecursiveMatrixAlgEquiv.toAlgHom.comp
        neutralCliffordFockMatrixAlgEquiv.toAlgHom =
      Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixAlgEquiv.toAlgHom := by
  apply AlgHom.ext
  intro a
  exact fockToRecursiveMatrixAlgEquiv_fock a

/-! Mathlib's endomorphism-algebra theorem now turns the matrix-algebra
comparison into an actual spinor-space intertwiner.  This is an existence
statement for the change of spinor coordinates; it does not pretend that the
two independently chosen standard bases have identical entries. -/
noncomputable def fockRecursiveEndAlgEquiv :
    Module.End ℝ SCoord ≃ₐ[ℝ] Module.End ℝ SCoord :=
  (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32))).trans
    (fockToRecursiveMatrixAlgEquiv.trans
      (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32))).symm)

theorem exists_fockRecursiveIntertwiner :
    ∃ T : SCoord ≃ₗ[ℝ] SCoord,
      fockRecursiveEndAlgEquiv = T.conjAlgEquiv ℝ := by
  exact fockRecursiveEndAlgEquiv.eq_linearEquivConjAlgEquiv

noncomputable def recursiveMatrixAsCoordinateEnd :
    A →ₐ[ℝ] Module.End ℝ SCoord :=
  (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32))).symm.toAlgHom.comp
    Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixRep

theorem fockToRecursiveMatrixAlgEquiv_generator (w : NeutralSpace) :
    fockToRecursiveMatrixAlgEquiv
        (neutralCliffordFockMatrixAlgEquiv
          (CliffordAlgebra.ι (canonicalNeutralFormUnscaled (E := V5)) w)) =
      Clifford55.cl55SpinorRepresentation
        (Clifford55.ι55
          (Cl55NeutralHyperbolicIsometry.neutralToV55 w)) := by
  rw [fockToRecursiveMatrixAlgEquiv_fock]
  exact Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixAlgEquiv_ι w

/-! The recursive spinor carrier is indexed by `Fin (2 ^ 5)`, whereas the
coordinate exterior carrier above is indexed by `Fin 32`.  The following
explicit reindexing is the honest bridge between these definitionally
different, but numerically equal, finite carriers. -/

noncomputable def spinorIndexEquiv : Fin 32 ≃ Fin (2 ^ 5) :=
  finCongr (by norm_num)

noncomputable def recursiveMatrixCoordinateAlgEquiv :
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 ≃ₐ[ℝ]
      Matrix (Fin 32) (Fin 32) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ spinorIndexEquiv.symm

noncomputable def fockToRecursiveCoordinateMatrixAlgEquiv :
    Matrix (Fin 32) (Fin 32) ℝ ≃ₐ[ℝ] Matrix (Fin 32) (Fin 32) ℝ :=
  fockToRecursiveMatrixAlgEquiv.trans
    recursiveMatrixCoordinateAlgEquiv

@[simp] theorem fockToRecursiveCoordinateMatrixAlgEquiv_fock (a : A) :
    fockToRecursiveCoordinateMatrixAlgEquiv
        (neutralCliffordFockMatrixAlgEquiv a) =
      recursiveMatrixCoordinateAlgEquiv
        (Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixRep a) := by
  change fockToRecursiveCoordinateMatrixAlgEquiv
      (neutralCliffordFockMatrixAlgEquiv a) =
    recursiveMatrixCoordinateAlgEquiv
      (Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixAlgEquiv a)
  simp [fockToRecursiveCoordinateMatrixAlgEquiv]

noncomputable def fockRecursiveCoordinateEndAlgEquiv :
    Module.End ℝ SCoord ≃ₐ[ℝ] Module.End ℝ SCoord :=
  (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32))).trans
    (fockToRecursiveCoordinateMatrixAlgEquiv.trans
      (Matrix.toLinAlgEquiv (Pi.basisFun ℝ (Fin 32))))

noncomputable def recursiveCoordinateMatrixAsEnd :
    A →ₐ[ℝ] Module.End ℝ SCoord :=
  (Matrix.toLinAlgEquiv (Pi.basisFun ℝ (Fin 32))).toAlgHom.comp
    (recursiveMatrixCoordinateAlgEquiv.toAlgHom.comp
      Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixRep)

theorem fockRecursiveCoordinateEndAlgEquiv_apply (a : A) :
    fockRecursiveCoordinateEndAlgEquiv
        (neutralCliffordRepCoordinate a) =
      recursiveCoordinateMatrixAsEnd a := by
  apply (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32))).injective
  simp only [fockRecursiveCoordinateEndAlgEquiv, AlgEquiv.trans_apply,
    recursiveCoordinateMatrixAsEnd]
  rw [LinearMap.toMatrixAlgEquiv_toLinAlgEquiv
    (Pi.basisFun ℝ (Fin 32))]
  have hF :
      (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32)))
          (neutralCliffordRepCoordinate a) =
        neutralCliffordFockMatrixAlgEquiv a := by
    have h := congrArg (fun f => f a)
      neutralCliffordFockMatrixAlgEquiv_toAlgHom
    simpa [Function.comp_apply] using h
  rw [hF]
  have hR :
      (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32)))
          (((Matrix.toLinAlgEquiv (Pi.basisFun ℝ (Fin 32))).toAlgHom.comp
            (recursiveMatrixCoordinateAlgEquiv.toAlgHom.comp
              Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixRep)) a) =
        recursiveMatrixCoordinateAlgEquiv
          (Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixAlgEquiv a) := by
    change (LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 32)))
        (Matrix.toLinAlgEquiv (Pi.basisFun ℝ (Fin 32))
          (recursiveMatrixCoordinateAlgEquiv
            (Cl55NeutralHyperbolicIsometry.neutralCliffordMatrixAlgEquiv a))) = _
    exact LinearMap.toMatrixAlgEquiv_toLinAlgEquiv
      (Pi.basisFun ℝ (Fin 32)) _
  rw [hR]
  exact fockToRecursiveCoordinateMatrixAlgEquiv_fock a

theorem exists_fockRecursiveCoordinateIntertwiner_conjugates :
    ∃ T : SCoord ≃ₗ[ℝ] SCoord, ∀ a ψ,
      T (neutralCliffordRepCoordinate a (T.symm ψ)) =
        recursiveCoordinateMatrixAsEnd a ψ := by
  obtain ⟨T, hT⟩ :=
    fockRecursiveCoordinateEndAlgEquiv.eq_linearEquivConjAlgEquiv
  refine ⟨T, ?_⟩
  intro a ψ
  rw [← fockRecursiveCoordinateEndAlgEquiv_apply a, hT,
    LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]
  simp

theorem exists_fockRecursiveSpinorIntertwiner :
    ∃ C : S ≃ₗ[ℝ] SCoord, ∀ a ψ,
      C (neutralCliffordRep a (C.symm ψ)) =
        recursiveCoordinateMatrixAsEnd a ψ := by
  obtain ⟨T, hT⟩ := exists_fockRecursiveCoordinateIntertwiner_conjugates
  refine ⟨spinorCoordinateEquiv.trans T, ?_⟩
  intro a ψ
  change T (spinorCoordinateEquiv
      (neutralCliffordRep a
        (spinorCoordinateEquiv.symm (T.symm ψ)))) = _
  rw [spinorCoordinateEquiv_intertwines]
  simpa using hT a ψ

theorem exists_fockRecursiveSpinorIntertwiner_generators :
    ∃ C : S ≃ₗ[ℝ] SCoord, ∀ w ψ,
      C (neutralCliffordRep
          (CliffordAlgebra.ι
            (canonicalNeutralFormUnscaled (E := V5)) w)
          (C.symm ψ)) =
        recursiveCoordinateMatrixAsEnd
          (CliffordAlgebra.ι
            (canonicalNeutralFormUnscaled (E := V5)) w) ψ := by
  obtain ⟨C, hC⟩ := exists_fockRecursiveSpinorIntertwiner
  refine ⟨C, ?_⟩
  intro w ψ
  exact hC (CliffordAlgebra.ι
    (canonicalNeutralFormUnscaled (E := V5)) w) ψ

end InfoGeometry.Clifford.Cl55FockMatrixIntertwiner
