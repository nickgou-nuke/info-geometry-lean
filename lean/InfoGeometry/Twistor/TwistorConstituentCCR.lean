import InfoGeometry.Twistor.PenrosePolynomialCCR
import Mathlib

/-!
# Constituent CCR on the full polynomial carrier

Perjes (6.13), realized without finite-dimensional Heisenberg surrogates.
The old one-twistor representation embeds through a native polynomial renaming.
No Hilbert adjoint, self-adjoint domain or particle spectrum is inferred.
-/
noncomputable section
namespace InfoGeometry.Twistor.TwistorConstituentCCR
open scoped BigOperators

abbrev Coordinate (n : ℕ) := Fin n × Fin 4
abbrev Wave (n : ℕ) := MvPolynomial (Coordinate n) ℂ
abbrev Operator (n : ℕ) := Module.End ℂ (Wave n)

variable {n : ℕ}

def position (a : Coordinate n) : Operator n where
  toFun f := MvPolynomial.X a * f
  map_add' f g := mul_add _ _ _
  map_smul' c f := by simp [Algebra.mul_smul_comm]

def derivative (a : Coordinate n) : Operator n := (MvPolynomial.pderiv a).toLinearMap

def conjugateCoordinate (h : ℂ) (a : Coordinate n) : Operator n := -h • derivative a

@[simp] theorem position_apply (a : Coordinate n) (f : Wave n) :
    position a f = MvPolynomial.X a * f := rfl

@[simp] theorem derivative_apply (a : Coordinate n) (f : Wave n) :
    derivative a f = MvPolynomial.pderiv a f := rfl

@[simp] theorem conjugateCoordinate_apply (h : ℂ) (a : Coordinate n) (f : Wave n) :
    conjugateCoordinate h a f = -h • MvPolynomial.pderiv a f := rfl

theorem derivative_position (a b : Coordinate n) :
    derivative a * position b = position b * derivative a +
      (if a=b then (1 : ℂ) else 0) • (1 : Operator n) := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply, LinearMap.add_apply, position_apply, derivative_apply,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  by_cases hab : a=b
  · subst b
    simp [Pi.single_apply, Algebra.smul_def]
    ring
  · simp [hab, Ne.symm hab, Pi.single_apply]

theorem constituent_CCR (h : ℂ) (i j : Fin n) (a b : Fin 4) :
    position (i,a) * conjugateCoordinate h (j,b) -
      conjugateCoordinate h (j,b) * position (i,a) =
        (if i=j ∧ a=b then h else 0) • (1 : Operator n) := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply, LinearMap.sub_apply, position_apply,
    conjugateCoordinate_apply, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
  by_cases hix : (i,a)=(j,b)
  · have hi : i=j := congrArg Prod.fst hix
    have ha : a=b := congrArg Prod.snd hix
    subst j; subst b
    simp [Algebra.smul_def, Pi.single_apply]
    ring
  · have hne : ¬(i=j ∧ a=b) := by rintro ⟨rfl,rfl⟩; exact hix rfl
    simp [hne, hix, Ne.symm hix, Algebra.smul_def, Pi.single_apply]
    ring

theorem position_commute (a b : Coordinate n) : position a * position b = position b * position a := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply, position_apply]
  ring

theorem derivative_commute (a b : Coordinate n) : derivative a * derivative b = derivative b * derivative a := by
  have hd : ⁅MvPolynomial.pderiv a, MvPolynomial.pderiv b⁆ =
      (0 : Derivation ℂ (Wave n) (Wave n)) := by
    apply MvPolynomial.derivation_ext
    intro c
    simp [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply]
  apply LinearMap.ext
  intro f
  have h := Derivation.congr_fun hd f
  exact sub_eq_zero.mp (by simpa [Derivation.commutator_apply] using h)

theorem conjugate_commute (h : ℂ) (a b : Coordinate n) :
    conjugateCoordinate h a * conjugateCoordinate h b =
      conjugateCoordinate h b * conjugateCoordinate h a := by
  simp only [conjugateCoordinate, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [derivative_commute]

/-- Actual embedding of a single constituent's polynomial algebra. -/
def singleEmbedding (i : Fin n) : PenrosePolynomialCCR.WavePolynomial →ₐ[ℂ] Wave n :=
  MvPolynomial.rename (fun a => (i,a))

theorem singleEmbedding_position (i : Fin n) (a : Fin 4) (f : PenrosePolynomialCCR.WavePolynomial) :
    singleEmbedding i (PenrosePolynomialCCR.Z a f) = position (i,a) (singleEmbedding i f) := by
  rw [PenrosePolynomialCCR.Z_apply]
  simp [singleEmbedding]

theorem singleEmbedding_derivative (i : Fin n) (a : Fin 4)
    (f : PenrosePolynomialCCR.WavePolynomial) :
    derivative (i,a) (singleEmbedding i f) = singleEmbedding i (MvPolynomial.pderiv a f) := by
  exact MvPolynomial.pderiv_rename (fun _ _ h => congrArg Prod.snd h) a f

theorem singleEmbedding_conjugate (i : Fin n) (h : ℂ) (a : Fin 4)
    (f : PenrosePolynomialCCR.WavePolynomial) :
    singleEmbedding i (PenrosePolynomialCCR.W h a f) =
      conjugateCoordinate h (i,a) (singleEmbedding i f) := by
  rw [PenrosePolynomialCCR.W_apply, map_smul]
  exact congrArg (fun x => -h • x) (singleEmbedding_derivative i a f).symm

/-- Quadratic generators act on the same polynomial representation. -/
def quadraticGenerator (a b : Coordinate n) : Operator n := position a * derivative b

theorem quadraticGenerator_X (a b c : Coordinate n) :
    quadraticGenerator a b (MvPolynomial.X c) =
      if b=c then MvPolynomial.X a else 0 := by
  simp [quadraticGenerator, Module.End.mul_apply, MvPolynomial.pderiv_X, Pi.single_apply]

/-- Matrix-unit Lie closure, not an associative matrix-unit identification. -/
theorem quadraticGenerator_bracket (a b c d : Coordinate n) :
    quadraticGenerator a b * quadraticGenerator c d -
      quadraticGenerator c d * quadraticGenerator a b =
        (if b=c then quadraticGenerator a d else 0) -
        (if d=a then quadraticGenerator c b else 0) := by
  unfold quadraticGenerator
  calc
    (position a*derivative b)*(position c*derivative d) -
        (position c*derivative d)*(position a*derivative b) =
      position a*(derivative b*position c)*derivative d -
        position c*(derivative d*position a)*derivative b := by noncomm_ring
    _ = position a*(position c*derivative b+(if b=c then (1 : ℂ) else 0) • 1)*derivative d -
        position c*(position a*derivative d+(if d=a then (1 : ℂ) else 0) • 1)*derivative b := by
          rw [derivative_position, derivative_position]
    _ = _ := by
      have hz := position_commute a c
      have hd := derivative_commute b d
      split_ifs <;> simp only [one_smul, zero_smul] <;> noncomm_ring [hz,hd]

/-- Translation generators X_lower partial_upper commute in the actual representation. -/
def translationGenerator (i : Fin n) (a b : Fin 2) : Operator n :=
  quadraticGenerator (i, ⟨b.val+2, by omega⟩) (i, ⟨a.val, by omega⟩)

theorem translations_commute (i j : Fin n) (a b c d : Fin 2) :
    translationGenerator i a b * translationGenerator j c d =
      translationGenerator j c d * translationGenerator i a b := by
  apply sub_eq_zero.mp
  rw [translationGenerator, translationGenerator, quadraticGenerator_bracket]
  have h1 : (i, (⟨a.val, by omega⟩ : Fin 4)) ≠ (j, ⟨d.val+2, by omega⟩) := by
    intro h; have hh := congrArg (fun p : Fin n × Fin 4 => p.2.val) h; omega
  have h2 : (j, (⟨c.val, by omega⟩ : Fin 4)) ≠ (i, ⟨b.val+2, by omega⟩) := by
    intro h; have hh := congrArg (fun p : Fin n × Fin 4 => p.2.val) h; omega
  simp [h1,h2]

end InfoGeometry.Twistor.TwistorConstituentCCR
