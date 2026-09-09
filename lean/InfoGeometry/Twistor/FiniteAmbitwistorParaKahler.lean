import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
import InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction
import InfoGeometry.Canonical.FiniteHeisenbergGroup
import InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

/-! Finite algebraic ambitwistor carrier.

This file deliberately stops at the native finite spinor/projective level.  It
does not assert an analytic ambitwistor manifold or a sheaf-cohomological
Penrose transform.
-/
namespace InfoGeometry.Twistor.FiniteAmbitwistorParaKahler

noncomputable section

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Canonical
open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

abbrev DualTwistor4 := Twistor4

def spinorPairing (u v : Spinor2) : ℂ :=
  ∑ i : Fin 2, star (u i) * v i

def ambitwistorPairing (W : DualTwistor4) (Z : Twistor4) : ℂ :=
  spinorPairing W.1 Z.1 + spinorPairing W.2 Z.2

def IsAmbitwistor (W : DualTwistor4) (Z : Twistor4) : Prop :=
  ambitwistorPairing W Z = 0

theorem ambitwistorPairing_zero_left (Z : Twistor4) :
    ambitwistorPairing
      ((fun _ : Fin 2 => 0, fun _ : Fin 2 => 0) : DualTwistor4) Z = 0 := by
  classical
  simp only [ambitwistorPairing, spinorPairing, Prod.fst, Prod.snd,
    Pi.zero_apply, star_zero, zero_mul, add_zero, Finset.sum_const_zero]

theorem ambitwistorPairing_zero_right (W : DualTwistor4) :
    ambitwistorPairing W
      ((fun _ : Fin 2 => 0, fun _ : Fin 2 => 0) : Twistor4) = 0 := by
  classical
  simp only [ambitwistorPairing, spinorPairing, Prod.fst, Prod.snd,
    Pi.zero_apply, map_zero, mul_zero, add_zero, Finset.sum_const_zero]

def scaleTwistor (c : ℂ) (Z : Twistor4) : Twistor4 := (c • Z.1, c • Z.2)

theorem ambitwistorPairing_smul_left (c : ℂ) (W : DualTwistor4) (Z : Twistor4) :
    ambitwistorPairing (scaleTwistor c W) Z = star c * ambitwistorPairing W Z := by
  classical
  simp [scaleTwistor, ambitwistorPairing, spinorPairing, Pi.smul_apply,
    smul_eq_mul, star_mul, map_mul, Finset.mul_sum]
  ring

theorem ambitwistorPairing_smul_right (c : ℂ) (W : DualTwistor4) (Z : Twistor4) :
    ambitwistorPairing W (scaleTwistor c Z) = c * ambitwistorPairing W Z := by
  classical
  simp [scaleTwistor, ambitwistorPairing, spinorPairing, Pi.smul_apply,
    smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
  <;> ring

theorem isAmbitwistor_rescaling {W : DualTwistor4} {Z : Twistor4}
    (h : IsAmbitwistor W Z) (c d : ℂ) :
    IsAmbitwistor (scaleTwistor c W) (scaleTwistor d Z) := by
  unfold IsAmbitwistor at h ⊢
  rw [ambitwistorPairing_smul_left, ambitwistorPairing_smul_right, h]
  simp

abbrev FiniteCorrespondence :=
  ComplexSpacetime × ProjectiveSpinorLine × ProjectiveSpinorLine

def correspondenceTwistor (q : FiniteCorrespondence) : ProjectiveTwistor3 :=
  projectiveIncidenceMap q.1 q.2.1

@[simp] theorem correspondenceTwistor_mk
    (x : ComplexSpacetime) (p q : ProjectiveSpinorLine) :
    correspondenceTwistor (x, p, q) = projectiveIncidenceMap x p := by
  rfl

/-! A finite para-Kähler structure attached to an ambitwistor carrier.  The
metric and para-complex operator are supplied by the existing owner; this
structure records only their association with the finite correspondence. -/
structure Datum (V : Type*)
    [AddCommGroup V] [Module ℝ V] where
  paraKahler : InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT.ParaKahlerDatum ℝ V

/-! Finite hyper-para-Kähler algebraic carrier.  The three endomorphisms are
the split-quaternion generators; geometric parallelness and integrability are
intentionally not part of this finite datum. -/
structure ParaHyperkahlerDatum (V : Type*)
    [AddCommGroup V] [Module ℝ V] where
  paraKahler : InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT.ParaKahlerDatum ℝ V
  opA : V →ₗ[ℝ] V
  opB : V →ₗ[ℝ] V
  opC : V →ₗ[ℝ] V
  opA_sq : ∀ u, opA (opA u) = -u
  opB_sq : ∀ u, opB (opB u) = u
  opC_sq : ∀ u, opC (opC u) = u
  opA_mul_opB : ∀ u, opA (opB u) = opC u
  opB_mul_opA : ∀ u, opB (opA u) = -opC u

theorem paraHyperkahler_I1_mul_I2
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : ParaHyperkahlerDatum V) (u : V) :
    D.opA (D.opB u) = D.opC u := by
  exact D.opA_mul_opB u

theorem paraHyperkahler_I2_mul_I1
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : ParaHyperkahlerDatum V) (u : V) :
    D.opB (D.opA u) = -D.opC u := by
  exact D.opB_mul_opA u

def paraBerryForm {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Datum V) (u v : V) : ℝ :=
  D.paraKahler.paraBerryTwoForm u v

theorem paraBerryForm_skew {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Datum V) (u v : V) :
    paraBerryForm D v u = -paraBerryForm D u v := by
  exact D.paraKahler.paraBerryTwoForm_skew u v

def paraProjectorPlus {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Datum V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id + D.paraKahler.para.K)

def paraProjectorMinus {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Datum V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id - D.paraKahler.para.K)

theorem paraProjectorPlus_add_minus {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : Datum V) :
    paraProjectorPlus D + paraProjectorMinus D = LinearMap.id := by
  ext u
  dsimp [paraProjectorPlus, paraProjectorMinus]
  module

/-! Finite quantization is inherited from the existing truncated twistor
operator model.  The boundary defect is retained explicitly: finite matrices
cannot satisfy an exact canonical commutator with the identity. -/
abbrev QuantizedTwistorOperator :=
  InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.TwistorOperator

abbrev QuantizedPhasePoint :=
  InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.PhasePoint

def quantizedCoordinate : QuantizedTwistorOperator :=
  InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.twistorCoordinate

def quantizedDerivative : QuantizedTwistorOperator :=
  InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.twistorDerivative

theorem quantized_coordinate_commutator_boundary_defect :
    InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.commutator
        quantizedCoordinate quantizedDerivative =
      !![1, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, -1] := by
  exact InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.finite_twistor_commutator

theorem quantized_shear_preserves_phase_form
    (c : ℂ) (x y : QuantizedPhasePoint) :
    InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.finiteSymplecticForm
        (InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.canonicalShear c x)
        (InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.canonicalShear c y) =
      InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.finiteSymplecticForm x y := by
  exact InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.canonicalShear_preserves_symplectic c x y

/-! The finite Heisenberg carrier is owned by the canonical Heisenberg module;
this alias keeps the ambitwistor packet on that same carrier. -/
abbrev AmbitwistorHeisenberg (n : ℕ) :=
  InfoGeometry.Canonical.FiniteHeisenbergCore.FiniteHeisenberg n

theorem ambitwistorHeisenberg_center_commutes {n : ℕ} (c : ZMod n)
    (x : AmbitwistorHeisenberg n) :
    Commute
      (InfoGeometry.Canonical.FiniteHeisenbergCore.finiteHeisenbergCenterElement c)
      x := by
  exact InfoGeometry.Canonical.FiniteHeisenbergCore.finiteHeisenberg_center_commutes c x

abbrev AmbitwistorVector := Fin 4 → ℂ

def ambitwistorRankOne (Z W : AmbitwistorVector) : AmbitwistorVector →ₗ[ℂ] AmbitwistorVector where
  toFun x := (∑ j : Fin 4, W j * x j) • Z
  map_add' x y := by
    ext i
    simp only [Finset.sum_add_distrib, mul_add, add_smul, Pi.add_apply]
  map_smul' c x := by
    ext i
    change (∑ j : Fin 4, W j * (c * x j)) * Z i =
      c * ((∑ j : Fin 4, W j * x j) * Z i)
    calc
      (∑ j : Fin 4, W j * (c * x j)) * Z i =
          (∑ j : Fin 4, c * (W j * x j)) * Z i := by
            apply congrArg (fun z => z * Z i)
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = c * ((∑ j : Fin 4, W j * x j) * Z i) := by
            rw [← Finset.mul_sum]
            ring

def traceFour (T : AmbitwistorVector →ₗ[ℂ] AmbitwistorVector) : ℂ :=
  ∑ i : Fin 4, T (fun j => if j = i then 1 else 0) i

theorem traceFour_ambitwistorRankOne (Z W : AmbitwistorVector) :
    traceFour (ambitwistorRankOne Z W) = ∑ i : Fin 4, W i * Z i := by
  classical
  dsimp [traceFour, ambitwistorRankOne]
  have h : ∀ i : Fin 4,
      (∑ j : Fin 4, W j * (if j = i then (1 : ℂ) else 0)) * Z i = W i * Z i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  simp_rw [h]

theorem isAmbitwistor_rankOne_nilpotent (Z W : AmbitwistorVector)
    (h : ∑ i : Fin 4, W i * Z i = 0) :
    (ambitwistorRankOne Z W).comp (ambitwistorRankOne Z W) = 0 := by
  apply LinearMap.ext
  intro y
  funext i
  dsimp [ambitwistorRankOne]
  have hinner :
      (∑ j : Fin 4, W j * ((∑ k : Fin 4, W k * y k) * Z j)) = 0 := by
    calc
      (∑ j : Fin 4, W j * ((∑ k : Fin 4, W k * y k) * Z j)) =
          (∑ k : Fin 4, W k * y k) * (∑ j : Fin 4, W j * Z j) := by
            calc
              (∑ j : Fin 4, W j * ((∑ k : Fin 4, W k * y k) * Z j)) =
                  ∑ j : Fin 4, (∑ k : Fin 4, W k * y k) * (W j * Z j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = (∑ k : Fin 4, W k * y k) * (∑ j : Fin 4, W j * Z j) := by
                    rw [Finset.mul_sum]
      _ = 0 := by rw [h, mul_zero]
  simp [hinner]

/-! The Aharonov readout is reused verbatim on the finite four-component
twistor operator space. -/
abbrev AmbitwistorOperator := Operator (Fin 4)
abbrev AmbitwistorBoundary := RegularBoundaryPair (Fin 4)

def ambitwistorReadout (p : AmbitwistorBoundary) (A : AmbitwistorOperator) : ℂ :=
  weakValue p A

theorem ambitwistorReadout_add (p : AmbitwistorBoundary)
    (A B : AmbitwistorOperator) :
    ambitwistorReadout p (A + B) =
      ambitwistorReadout p A + ambitwistorReadout p B := by
  exact weakValue_add p A B

theorem ambitwistorReadout_one (p : AmbitwistorBoundary) :
    ambitwistorReadout p (1 : AmbitwistorOperator) = 1 := by
  exact weakValue_one p

theorem ambitwistorReadout_rescalePre (p : AmbitwistorBoundary)
    (c : ℂ) (hc : c ≠ 0) (A : AmbitwistorOperator) :
    ambitwistorReadout (rescalePre p c hc) A = ambitwistorReadout p A := by
  exact weakValue_rescalePre p c hc A

theorem ambitwistorReadout_rescalePost (p : AmbitwistorBoundary)
    (c : ℂ) (hc : c ≠ 0) (A : AmbitwistorOperator) :
    ambitwistorReadout (rescalePost p c hc) A = ambitwistorReadout p A := by
  exact weakValue_rescalePost p c hc A

def correspondenceProjection (q : FiniteCorrespondence) : ComplexSpacetime := q.1

@[simp] theorem correspondenceProjection_mk
    (x : ComplexSpacetime) (p q : ProjectiveSpinorLine) :
    correspondenceProjection (x, p, q) = x := rfl

end
end InfoGeometry.Twistor.FiniteAmbitwistorParaKahler
