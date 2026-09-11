import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
import InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm
import InfoGeometry.Algebra.Zorn.G2WeylDihedralEquiv
import InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge
import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.CanonicalZornG2UnificationBridge
import InfoGeometry.Lie.CanonicalZornRootWittBlockBridge

/-!
# Native G₂ root/Weyl/adjoint and character interfaces

This owner does not introduce another root or Weyl carrier.  It packages the
existing signed coordinate-root action, the existing derivation bracket, and
the associated finite permutation character into one reusable interface.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2RootWeylNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornRootWittBlockBridge
open InfoGeometry.Lie.CanonicalZornG2UnificationBridge
open InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
open InfoGeometry.Lie.CanonicalZornCartanAdjointAction

abbrev RootCarrier := G2CoordinateRoot

def rootWeylAction (p : WeylG2) : Equiv.Perm RootCarrier :=
  rootWeylNF p

@[simp] theorem rootWeylAction_one :
    rootWeylAction (0, false) = 1 := by
  simp [rootWeylAction]

@[simp] theorem rootWeylAction_cyclic_generator :
    rootWeylAction (1, false) = cRoot := by
  simp [rootWeylAction]

theorem rootWeylAction_simple_reflection_sq :
    (rootWeylAction (0, true)) ^ 2 = 1 := by
  simpa [rootWeylAction, rootWeylNF] using s1Root_sq

theorem rootWeylAction_cyclic_generator_pow_six :
    (rootWeylAction (1, false)) ^ 6 = 1 := by
  simpa [rootWeylAction] using cRoot_pow_six

/-! The concrete root-automorphism system uses the same Coxeter generators. -/

theorem c_conjugates_concrete_root (r : G2Root) :
    G2ConcreteWeylG2.c * rootAut r * G2ConcreteWeylG2.c⁻¹ =
      rootAut (cAction r) :=
  c_rootAut_c r

theorem s_conjugates_concrete_root (r : G2Root) :
    G2ConcreteWeylG2.s * rootAut r * G2ConcreteWeylG2.s =
      rootAut (sAction r) :=
  s_rootAut_s r

theorem longest_conjugates_concrete_root (r : G2Root) :
    rootAut (negAction r) = G2ConcreteWeylG2.c ^ 3 * rootAut r *
      (G2ConcreteWeylG2.c ^ 3)⁻¹ :=
  rootAut_neg r

theorem concrete_root_subgroup_add (r : G2Root) (a b : Bool) :
    xRoot r (a ^^ b) = xRoot r a * xRoot r b :=
  xRoot_add r a b

theorem rootWeylAction_preserves_root_carrier
    (p : WeylG2) (r : RootCarrier) :
    (rootWeylAction p r).1 ∈ (phi : Finset (ℤ × ℤ)) :=
  (rootWeylAction p r).property

def rootFixedPoints (p : WeylG2) : Finset RootCarrier :=
  Finset.univ.filter (fun r => rootWeylAction p r = r)

def rootPermutationCharacter (p : WeylG2) : ℕ :=
  (rootFixedPoints p).card

theorem rootFixedPoints_one :
    rootFixedPoints (0, false) = Finset.univ := by
  ext r
  simp [rootFixedPoints, rootWeylAction]

theorem rootPermutationCharacter_one :
    rootPermutationCharacter (0, false) = Fintype.card RootCarrier := by
  rw [rootPermutationCharacter, rootFixedPoints_one, Finset.card_univ]

theorem rootCarrier_card : Fintype.card RootCarrier = 12 := by
  classical
  have hcard := Fintype.card_congr signedRootCoordinateEquiv
  exact hcard.trans (by decide)

theorem rootPermutationCharacter_one_eq_12 :
    rootPermutationCharacter (0, false) = 12 := by
  rw [rootPermutationCharacter_one, rootCarrier_card]

/-! The native characteristic-zero Weyl generators preserve the pair-generated
derivation sector.  This is the adjoint-sector transport boundary; individual
root-vector signs are deliberately not assumed here. -/

theorem realWeylCycle_innerPairSpan_iff
    (D : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)) :
    _root_.InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation.conjugateNativeDerivation
        _root_.InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation.realWeylCycle D ∈
        Submodule.span ℝ (Set.range
          (fun p : InfoGeometry.Algebra.ZornVectorMatrix ℝ ×
              InfoGeometry.Algebra.ZornVectorMatrix ℝ =>
            InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
              p.1 p.2)) ↔
      D ∈ Submodule.span ℝ (Set.range
        (fun p : InfoGeometry.Algebra.ZornVectorMatrix ℝ ×
            InfoGeometry.Algebra.ZornVectorMatrix ℝ =>
          InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
            p.1 p.2)) := by
  exact _root_.InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation.conjugateNativeDerivation_mem_innerPairSpan_iff
    _root_.InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation.realWeylCycle D

theorem realWeylReflection_innerPairSpan_iff
    (D : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)) :
    _root_.InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation.conjugateNativeDerivation
        _root_.InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation.realWeylReflection D ∈
        Submodule.span ℝ (Set.range
          (fun p : InfoGeometry.Algebra.ZornVectorMatrix ℝ ×
              InfoGeometry.Algebra.ZornVectorMatrix ℝ =>
            InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
              p.1 p.2)) ↔
      D ∈ Submodule.span ℝ (Set.range
        (fun p : InfoGeometry.Algebra.ZornVectorMatrix ℝ ×
            InfoGeometry.Algebra.ZornVectorMatrix ℝ =>
          InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
            p.1 p.2)) := by
  exact _root_.InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation.conjugateNativeDerivation_mem_innerPairSpan_iff
    _root_.InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation.realWeylReflection D

/-! The same character readout on the concrete finite root carrier used by
the `G2(2)` root automorphisms.  This is a readout, not a second root model:
the carrier and its Coxeter action are imported from the native owner. -/

instance : Fintype InfoGeometry.Algebra.Zorn.G2TwoRootSystem.RootLength where
  elems := {InfoGeometry.Algebra.Zorn.G2TwoRootSystem.RootLength.Short,
    InfoGeometry.Algebra.Zorn.G2TwoRootSystem.RootLength.Long}
  complete := by
    intro r
    cases r <;> simp

def finiteRootFixedPoints (p : WeylG2) : Finset G2Root :=
  Finset.univ.filter (fun r => weylRootAction p r = r)

def finiteRootPermutationCharacter (p : WeylG2) : ℕ :=
  (finiteRootFixedPoints p).card

theorem cAction_bijective :
    Function.Bijective cAction := by
  native_decide

theorem sAction_bijective :
    Function.Bijective sAction := by
  native_decide

theorem weylRootAction_bijective (p : WeylG2) :
    Function.Bijective (weylRootAction p) := by
  rcases p with ⟨k, b⟩
  fin_cases k <;> cases b <;> native_decide

noncomputable def weylRootActionEquiv (p : WeylG2) :
    G2Root ≃ G2Root :=
  Equiv.ofBijective (weylRootAction p) (weylRootAction_bijective p)

@[simp] theorem weylRootActionEquiv_apply (p : WeylG2) (r : G2Root) :
    weylRootActionEquiv p r = weylRootAction p r := rfl

theorem weylRootActionEquiv_rootAut_conj (p : WeylG2) (r : G2Root) :
    weylNF p.1 p.2 * rootAut r * (weylNF p.1 p.2)⁻¹ =
      rootAut (weylRootActionEquiv p r) := by
  simpa only [weylRootActionEquiv_apply, rootWeylAction] using
    weylNF_rootAut_conj p r

theorem finiteRootFixedPoints_one :
    finiteRootFixedPoints (0, false) = Finset.univ := by
  ext r
  simp [finiteRootFixedPoints, weylRootAction, cActionPow, cActionPowNat]

theorem finiteRootPermutationCharacter_one :
    finiteRootPermutationCharacter (0, false) = Fintype.card G2Root := by
  rw [finiteRootPermutationCharacter, finiteRootFixedPoints_one, Finset.card_univ]

theorem finiteRootCarrier_card : Fintype.card G2Root = 12 := by
  rw [Fintype.card_prod]
  decide

theorem finiteRootPermutationCharacter_one_eq_12 :
    finiteRootPermutationCharacter (0, false) = 12 := by
  rw [finiteRootPermutationCharacter_one, finiteRootCarrier_card]

/-! The finite Weyl action preserves the short/long component.  This is the
structural separation needed when transporting the two root hexagons to the
native characteristic-zero root coordinates; it is stronger than merely
knowing that the action is a permutation of the twelve-element carrier. -/

theorem weylRootAction_preserves_rootLength
    (p : WeylG2) (r : G2Root) :
    (weylRootAction p r).1 = r.1 := by
  rcases p with ⟨k, b⟩
  rcases r with ⟨l, j⟩
  have hpow : ∀ n : ℕ, (cActionPowNat n (l, j)).1 = l := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simpa [cActionPowNat, cAction] using ih
  cases b
  · exact hpow k.val
  · simp only [weylRootAction, ↓reduceIte]
    have hcp : (cActionPow k (l, j)).1 = l := hpow k.val
    rcases hroot : cActionPow k (l, j) with ⟨l', j'⟩
    have hl : l' = l := by simpa [hroot] using hcp
    subst l'
    cases l <;> rfl

/-! A concrete carrier alignment.  The indexing is explicit: the two root
lengths give the sign bit, while the six `ZMod 6` positions enumerate the
positive-root labels in the repository's canonical order. -/

def signedShortRootAt : ZMod 6 → Bool × G2PositiveRoot
  | k => match k.val with
    | 0 => (false, .alpha)
    | 1 => (false, .alpha_add_beta)
    | 2 => (false, .two_alpha_beta)
    | 3 => (true, .alpha)
    | 4 => (true, .alpha_add_beta)
    | 5 => (true, .two_alpha_beta)
    | _ => (false, .alpha)

def signedLongRootAt : ZMod 6 → Bool × G2PositiveRoot
  | k => match k.val with
    | 0 => (false, .beta)
    | 1 => (false, .three_alpha_beta)
    | 2 => (false, .three_alpha_two_beta)
    | 3 => (true, .beta)
    | 4 => (true, .three_alpha_beta)
    | 5 => (true, .three_alpha_two_beta)
    | _ => (false, .beta)

def finiteRootToSignedLabel : G2Root → Bool × G2PositiveRoot
  | (.Short, k) => signedShortRootAt k
  | (.Long, k) => signedLongRootAt k

theorem finiteRootToSignedLabel_bijective :
    Function.Bijective finiteRootToSignedLabel := by
  classical
  decide

noncomputable def finiteRootSignedEquiv :
    G2Root ≃ Bool × G2PositiveRoot :=
  Equiv.ofBijective finiteRootToSignedLabel finiteRootToSignedLabel_bijective

noncomputable def finiteRootCoordinateEquiv :
    G2Root ≃ G2CoordinateRoot :=
  finiteRootSignedEquiv.trans signedRootCoordinateEquiv

@[simp] theorem finiteRootCoordinateEquiv_apply (r : G2Root) :
    finiteRootCoordinateEquiv r =
      signedRootCoordinateEquiv (finiteRootSignedEquiv r) := rfl

def finiteRootCyclotomicLabel (r : G2Root) : Root :=
  signedCyclotomic (finiteRootToSignedLabel r)

theorem finiteRootCyclotomicLabel_bijective :
    Function.Bijective finiteRootCyclotomicLabel := by
  native_decide

noncomputable def finiteRootCyclotomicEquiv : G2Root ≃ Root :=
  Equiv.ofBijective finiteRootCyclotomicLabel
    finiteRootCyclotomicLabel_bijective

@[simp] theorem finiteRootCyclotomicEquiv_apply (r : G2Root) :
    finiteRootCyclotomicEquiv r = finiteRootCyclotomicLabel r := rfl

theorem finiteRootCoordinateEquiv_eq_signedRootCoordinate (r : G2Root) :
    finiteRootCoordinateEquiv r =
      signedRootCoordinate (finiteRootToSignedLabel r) := rfl

theorem signedRootCyclotomicEquiv_finiteRootCoordinate (r : G2Root) :
    signedRootCyclotomicEquiv (finiteRootCoordinateEquiv r) =
      finiteRootCyclotomicLabel r := by
  rw [finiteRootCoordinateEquiv_eq_signedRootCoordinate,
    signedRootCyclotomicEquiv_apply]
  rfl

def finiteCoxeterPhase : Root → Root
  | (b, k) => (b, match k.val with
    | 0 => 2
    | 1 => 3
    | 2 => 1
    | 3 => 5
    | 4 => 0
    | 5 => 4
    | _ => 0)

def finiteReflectionPhase : Root → Root
  | (false, k) => (false, match k.val with
    | 0 => 3
    | 1 => 2
    | 2 => 1
    | 3 => 0
    | 4 => 5
    | 5 => 4
    | _ => 0)
  | (true, k) => (true, match k.val with
    | 0 => 0
    | 1 => 5
    | 2 => 4
    | 3 => 3
    | 4 => 2
    | 5 => 1
    | _ => 0)

/-! The finite and concrete cyclotomic reflections use different axes in the
    long sector.  The canonical comparison is the sector-dependent shift
    `k ↦ k + 1` there, while the short sector is unchanged. -/

def finiteToConcretePhaseCalibration : Root → Root
  | (false, k) => (false, k)
  | (true, k) => (true, k + 1)

theorem finiteToConcretePhaseCalibration_bijective :
    Function.Bijective finiteToConcretePhaseCalibration := by
  native_decide

noncomputable def finiteToConcretePhaseEquiv : Root ≃ Root :=
  Equiv.ofBijective finiteToConcretePhaseCalibration
    finiteToConcretePhaseCalibration_bijective

theorem finiteToConcretePhaseCalibration_reflection_conjugacy (r : Root) :
    finiteToConcretePhaseCalibration (finiteReflectionPhase r) =
      InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge.cyclotomicS1Fun
        (finiteToConcretePhaseCalibration r) := by
  rcases r with ⟨b, k⟩
  cases b <;> fin_cases k <;> decide

theorem finiteToConcretePhaseEquiv_reflection_conjugacy (r : Root) :
    finiteToConcretePhaseEquiv (finiteReflectionPhase r) =
      InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge.cyclotomicS1Perm
        (finiteToConcretePhaseEquiv r) := by
  exact finiteToConcretePhaseCalibration_reflection_conjugacy r

theorem finiteReflectionPhase_bijective :
    Function.Bijective finiteReflectionPhase := by
  native_decide

theorem finiteCoxeterPhase_bijective :
    Function.Bijective finiteCoxeterPhase := by
  native_decide

theorem finiteRootCyclotomicLabel_cAction (r : G2Root) :
    finiteRootCyclotomicLabel (cAction r) =
      finiteCoxeterPhase (finiteRootCyclotomicLabel r) := by
  rcases r with ⟨l, k⟩
  cases l <;> fin_cases k <;> decide

theorem finiteRootCyclotomicLabel_sAction (r : G2Root) :
    finiteRootCyclotomicLabel (sAction r) =
      finiteReflectionPhase (finiteRootCyclotomicLabel r) := by
  rcases r with ⟨l, k⟩
  cases l <;> fin_cases k <;> decide

theorem finiteRootCyclotomicEquiv_cAction (r : G2Root) :
    finiteRootCyclotomicEquiv (cAction r) =
      finiteCoxeterPhase (finiteRootCyclotomicEquiv r) := by
  exact finiteRootCyclotomicLabel_cAction r

theorem finiteRootCyclotomicEquiv_sAction (r : G2Root) :
    finiteRootCyclotomicEquiv (sAction r) =
      finiteReflectionPhase (finiteRootCyclotomicEquiv r) := by
  exact finiteRootCyclotomicLabel_sAction r

def finiteCoxeterPhasePowNat : ℕ → Root → Root
  | 0, r => r
  | n + 1, r => finiteCoxeterPhase (finiteCoxeterPhasePowNat n r)

def finitePhaseWeylAction (p : WeylG2) : Root → Root :=
  if p.2 then
    fun r => finiteReflectionPhase (finiteCoxeterPhasePowNat p.1.val r)
  else
    finiteCoxeterPhasePowNat p.1.val

theorem finitePhaseWeylAction_mul_semidirect (p q : WeylG2) :
    finitePhaseWeylAction (weylMul p q) =
      finitePhaseWeylAction p ∘ finitePhaseWeylAction q := by
  rw [weylMul_eq_weylSemidirectMul]
  rcases p with ⟨kp, bp⟩
  rcases q with ⟨kq, bq⟩
  fin_cases kp <;> fin_cases kq <;> cases bp <;> cases bq <;>
    native_decide

theorem finitePhaseWeylAction_bijective (p : WeylG2) :
    Function.Bijective (finitePhaseWeylAction p) := by
  rcases p with ⟨k, b⟩
  fin_cases k <;> cases b <;> native_decide

noncomputable def finitePhaseWeylActionEquiv (p : WeylG2) :
    Root ≃ Root :=
  Equiv.ofBijective (finitePhaseWeylAction p)
    (finitePhaseWeylAction_bijective p)

@[simp] theorem finitePhaseWeylActionEquiv_apply
    (p : WeylG2) (r : Root) :
    finitePhaseWeylActionEquiv p r = finitePhaseWeylAction p r := rfl

theorem finiteReflectionPhase_involutive (r : Root) :
    finiteReflectionPhase (finiteReflectionPhase r) = r := by
  rcases r with ⟨b, k⟩
  cases b <;> fin_cases k <;> rfl

theorem finiteCoxeterPhasePowNat_six (r : Root) :
    finiteCoxeterPhasePowNat 6 r = r := by
  rcases r with ⟨b, k⟩
  cases b <;> fin_cases k <;> rfl

theorem finiteRootCyclotomicEquiv_cActionPowNat
    (n : ℕ) (r : G2Root) :
    finiteRootCyclotomicEquiv (cActionPowNat n r) =
      finiteCoxeterPhasePowNat n (finiteRootCyclotomicEquiv r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        finiteRootCyclotomicEquiv (cActionPowNat (n + 1) r) =
            finiteRootCyclotomicEquiv (cAction (cActionPowNat n r)) := by
              rfl
        _ = finiteCoxeterPhase
            (finiteRootCyclotomicEquiv (cActionPowNat n r)) :=
              finiteRootCyclotomicEquiv_cAction _
        _ = finiteCoxeterPhase
            (finiteCoxeterPhasePowNat n (finiteRootCyclotomicEquiv r)) :=
              congrArg finiteCoxeterPhase ih
        _ = finiteCoxeterPhasePowNat (n + 1)
            (finiteRootCyclotomicEquiv r) := by
              rfl

theorem finiteRootCyclotomicEquiv_weylRootAction
    (p : WeylG2) (r : G2Root) :
    finiteRootCyclotomicEquiv (weylRootAction p r) =
      finitePhaseWeylAction p (finiteRootCyclotomicEquiv r) := by
  rcases p with ⟨k, b⟩
  by_cases hb : b
  · simp only [weylRootAction, hb, ↓reduceIte, finitePhaseWeylAction]
    rw [cActionPow]
    rw [finiteRootCyclotomicEquiv_sAction,
      finiteRootCyclotomicEquiv_cActionPowNat]
  · simp only [weylRootAction, hb, Bool.false_eq_true, ↓reduceIte,
      finitePhaseWeylAction]
    rw [cActionPow]
    exact finiteRootCyclotomicEquiv_cActionPowNat k.val r

theorem weylRootAction_mul_semidirect (p q : WeylG2) :
    weylRootAction (weylMul p q) =
      weylRootAction p ∘ weylRootAction q := by
  funext r
  apply finiteRootCyclotomicEquiv.injective
  simp only [Function.comp_apply]
  rw [finiteRootCyclotomicEquiv_weylRootAction,
    finiteRootCyclotomicEquiv_weylRootAction,
    finiteRootCyclotomicEquiv_weylRootAction]
  rw [finitePhaseWeylAction_mul_semidirect]
  rfl

def finitePhaseFixed (p : WeylG2) (q : Root) : Prop :=
  finitePhaseWeylAction p q = q

theorem finiteRootFixed_iff_phaseFixed (p : WeylG2) (r : G2Root) :
    r ∈ finiteRootFixedPoints p ↔
      finitePhaseFixed p (finiteRootCyclotomicEquiv r) := by
  simp only [finiteRootFixedPoints, Finset.mem_filter, Finset.mem_univ,
    true_and, finitePhaseFixed]
  rw [← finiteRootCyclotomicEquiv_weylRootAction]
  exact (finiteRootCyclotomicEquiv.injective.eq_iff).symm

noncomputable def finitePhaseFixedPoints (p : WeylG2) : Finset Root :=
  by classical exact Finset.univ.filter (finitePhaseFixed p)

noncomputable def finitePhasePermutationCharacter (p : WeylG2) : ℕ :=
  (finitePhaseFixedPoints p).card

theorem finiteRootPermutationCharacter_eq_finitePhasePermutationCharacter
    (p : WeylG2) :
    finiteRootPermutationCharacter p =
      finitePhasePermutationCharacter p := by
  unfold finiteRootPermutationCharacter finitePhasePermutationCharacter
  apply Finset.card_bijective finiteRootCyclotomicEquiv
    finiteRootCyclotomicLabel_bijective
  intro r
  rw [finiteRootFixed_iff_phaseFixed]
  simp [finitePhaseFixedPoints]

theorem finitePhasePermutationCharacter_one_eq_12 :
    finitePhasePermutationCharacter (0, false) = 12 := by
  rw [← finiteRootPermutationCharacter_eq_finitePhasePermutationCharacter]
  exact finiteRootPermutationCharacter_one_eq_12

/-! The finite root labels and the native characteristic-zero derivation
carrier use the same parameter coordinate. -/

theorem finiteRoot_derivation_readout (r : G2Root) :
    G2ZornDerivationRootRepresentation.zornDerivationRootRepresentation r =
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation
        (rootDerivation (G2ZornDerivationRootRepresentation.rootCoordinate r)) := by
  apply InfoGeometry.Algebra.ZornVectorMatrix.Derivation.ext
  intro X
  change parameterAction
      (parameterUnit (G2ZornDerivationRootRepresentation.rootCoordinate r)) X =
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv
      ((rootDerivation (G2ZornDerivationRootRepresentation.rootCoordinate r)).1
        (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.symm X))
  rw [← rootDerivation_vectorAction]

/-! The characteristic-zero adjoint/root readout uses the canonical Zorn owner.
It is deliberately stated at the existing carrier, so the finite root action
above and the characteristic-zero root decomposition cannot drift apart by
introducing a second derivation model. -/

theorem canonical_derivation_finrank_14 :
    Module.finrank ℝ
        InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations = 14 :=
  InfoGeometry.Lie.CanonicalZornG2UnificationBridge.derivation_finrank_14

theorem canonical_cartan_root_space_dimensions :
    Module.finrank ℝ cartanRootSpan = 2 ∧
      Module.finrank ℝ rootSpaceSum = 12 :=
  derivation_cartan_rootSpace_two_add_twelve

theorem canonical_adjoint_root_space_total_dimension :
    Module.finrank ℝ cartanRootSpan +
        Module.finrank ℝ rootSpaceSum = 14 :=
  derivation_cartan_rootSpace_finrank_add

theorem canonical_adjoint_basis_is_root_eigenbasis :
    ∀ j k,
      adCartan k (rootDerivationBasis j) =
        ((rootWeight j k : ℝ) •
          (rootDerivationBasis j :
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der) :
            InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der) :=
  rootDerivationBasis_is_simultaneous_eigenbasis

theorem canonical_nonzero_root_index_card :
    Fintype.card nonzeroIndex = 12 :=
  nonzeroIndex_card

theorem canonical_root_weight_zero_iff (j : Fin 14) :
    rootWeight j = 0 ↔ j = 6 ∨ j = 13 :=
  rootWeight_eq_zero_iff j

theorem canonical_root_weight_range_is_g2 :
    Set.range (rootWeight : Fin 14 → Weight) =
      {(0 : Weight)} ∪ shortRootWeights ∪ longRootWeights :=
  rootWeight_range_eq_zero_union_short_long

/-! The Lie-algebra adjoint operator is the existing commutator bracket. -/

def adjoint
    (D E : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)) :
    InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ) :=
  InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket D E

theorem adjoint_apply_apply
    (D E : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ))
    (X : InfoGeometry.Algebra.ZornVectorMatrix ℝ) :
    adjoint D E X =
      InfoGeometry.Algebra.ZornVectorMatrix.sub (D (E X)) (E (D X)) := rfl

theorem adjoint_map_add
    (D E : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ))
    (X Y : InfoGeometry.Algebra.ZornVectorMatrix ℝ) :
    adjoint D E (InfoGeometry.Algebra.ZornVectorMatrix.add X Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.add (adjoint D E X)
        (adjoint D E Y) := by
  exact (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket D E).map_add' X Y

theorem adjoint_map_smul
    (D E : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ))
    (r : ℝ) (X : InfoGeometry.Algebra.ZornVectorMatrix ℝ) :
    adjoint D E (InfoGeometry.Algebra.ZornVectorMatrix.smul r X) =
      InfoGeometry.Algebra.ZornVectorMatrix.smul r (adjoint D E X) := by
  exact (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket D E).map_smul' r X

theorem adjoint_map_mul
    (D E : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ))
    (X Y : InfoGeometry.Algebra.ZornVectorMatrix ℝ) :
    adjoint D E (InfoGeometry.Algebra.ZornVectorMatrix.mul X Y) =
      InfoGeometry.Algebra.ZornVectorMatrix.add
        (InfoGeometry.Algebra.ZornVectorMatrix.mul (adjoint D E X) Y)
        (InfoGeometry.Algebra.ZornVectorMatrix.mul X (adjoint D E Y)) := by
  exact (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket D E).map_mul' X Y

theorem adjoint_skew
    (D E : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)) :
    adjoint D E = -adjoint E D := by
  exact InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket_skew D E

theorem adjoint_self_zero
    (D : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)) :
    adjoint D D = 0 := by
  exact InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket_self D

theorem adjoint_jacobi
    (D E F : InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)) :
    InfoGeometry.Algebra.ZornVectorMatrix.Derivation.add
        (adjoint D (adjoint E F))
        (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.add
          (adjoint E (adjoint F D))
          (adjoint F (adjoint D E))) = 0 := by
  exact InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket_jacobi D E F

end InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
