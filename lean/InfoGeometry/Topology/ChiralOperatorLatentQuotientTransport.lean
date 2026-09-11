import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ChiralOperatorBraidZornTopologicalEquivariance
import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationTopCat

/-!
# Quotient transport for the operator-valued chiral latent chart

The cyclic action descends through the observational quotient because it
preserves the observation relation.  Zorn multiplication is exposed on the
quotient as a continuous operator-valued readout; no quotient algebra is
claimed without a separately proved multiplication congruence.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

abbrev ChiralOperatorObservationalQuotient
    (A : Type) [NormedRing A] [NormedAlgebra ℝ A] :=
  OperatorObservationalQuotient (operatorSageLatentSystem (A := A))

def chiralOperatorCycleQuotientMap :
    ChiralOperatorObservationalQuotient A →
      ChiralOperatorObservationalQuotient A :=
  Quotient.lift
    (fun X => Quotient.mk _ (chiralOperatorCycle X))
    (by
      intro X Y hXY
      change (operatorSageLatentSystem (A := A)).operatorObservationMap X =
        (operatorSageLatentSystem (A := A)).operatorObservationMap Y at hXY
      apply Quotient.sound
      change (operatorSageLatentSystem (A := A)).operatorObservationMap
          (chiralOperatorCycle X) =
        (operatorSageLatentSystem (A := A)).operatorObservationMap
          (chiralOperatorCycle Y)
      rw [show (operatorSageLatentSystem (A := A)).operatorObservationMap
          (chiralOperatorCycle X) = operatorSageObservationMap
            (chiralOperatorCycle X) by rfl,
        show (operatorSageLatentSystem (A := A)).operatorObservationMap
          (chiralOperatorCycle Y) = operatorSageObservationMap
            (chiralOperatorCycle Y) by rfl,
        operatorSageObservation_cycle_intertwines_map,
        operatorSageObservation_cycle_intertwines_map]
      exact congrArg
        (fun f : OperatorSageFeatureSpace A =>
          fun i => f (operatorSageFeatureCycle i)) hXY)

@[simp] theorem chiralOperatorCycleQuotientMap_mk
    (X : OperatorSageTopologicalCarrier A) :
    chiralOperatorCycleQuotientMap
        (Quotient.mk _ X) =
      Quotient.mk _ (chiralOperatorCycle X) := rfl

theorem continuous_chiralOperatorCycleQuotientMap :
    Continuous (chiralOperatorCycleQuotientMap (A := A)) := by
  apply Continuous.quotient_lift
  exact (continuous_operatorObservationQuotientMap
      (operatorSageLatentSystem (A := A))).comp
      continuous_chiralOperatorCycle

@[simp] theorem chiralOperatorCycleQuotientMap_three
    (q : ChiralOperatorObservationalQuotient A) :
    chiralOperatorCycleQuotientMap
        (chiralOperatorCycleQuotientMap
          (chiralOperatorCycleQuotientMap q)) = q := by
  refine Quotient.inductionOn q ?_
  intro X
  change Quotient.mk _ (chiralOperatorCycle
    (chiralOperatorCycle (chiralOperatorCycle X))) = Quotient.mk _ X
  rw [chiralOperatorCycle_three]

def chiralOperatorQuotientZornMulReadout
    (q r : ChiralOperatorObservationalQuotient A) :
  OperatorSageFeatureSpace A :=
  operatorSageObservationMap
    (operatorSageTopologicalMul
      (operatorSageObservationInverse
        (operatorObservationQuotientReadout
          (operatorSageLatentSystem (A := A)) q))
      (operatorSageObservationInverse
        (operatorObservationQuotientReadout
          (operatorSageLatentSystem (A := A)) r)))

theorem continuous_chiralOperatorQuotientZornMulReadout :
    Continuous (fun p :
      ChiralOperatorObservationalQuotient A ×
        ChiralOperatorObservationalQuotient A =>
      chiralOperatorQuotientZornMulReadout p.1 p.2) := by
  unfold chiralOperatorQuotientZornMulReadout
  let S := operatorSageLatentSystem (A := A)
  have hReadout : Continuous (operatorObservationQuotientReadout S) :=
    continuous_operatorObservationQuotientReadout S
  have hInverse : Continuous (operatorSageObservationInverse (A := A)) :=
    (operatorSageFeatureHomeomorph (A := A)).continuous_invFun
  exact continuous_operatorSageObservationMap.comp
    (continuous_operatorSageTopologicalMul.comp
      ((hInverse.comp (hReadout.comp continuous_fst)).prodMk
       (hInverse.comp (hReadout.comp continuous_snd))))

@[simp] theorem chiralOperatorQuotientZornMulReadout_mk
    (X Y : OperatorSageTopologicalCarrier A) :
    chiralOperatorQuotientZornMulReadout
        (Quotient.mk _ X) (Quotient.mk _ Y) =
      operatorSageObservationMap
        (operatorSageTopologicalMul X Y) := by
  change operatorSageObservationMap
      (operatorSageTopologicalMul
        (operatorSageObservationInverse
          (operatorObservationQuotientReadout
            (operatorSageLatentSystem (A := A)) (Quotient.mk _ X)))
        (operatorSageObservationInverse
          (operatorObservationQuotientReadout
            (operatorSageLatentSystem (A := A)) (Quotient.mk _ Y)))) = _
  change operatorSageObservationMap
      (operatorSageTopologicalMul
        (operatorSageObservationInverse
          (operatorObservationQuotientReadout
            (operatorSageLatentSystem (A := A))
            (operatorObservationQuotientMap
              (operatorSageLatentSystem (A := A)) X)))
        (operatorSageObservationInverse
          (operatorObservationQuotientReadout
            (operatorSageLatentSystem (A := A))
            (operatorObservationQuotientMap
              (operatorSageLatentSystem (A := A)) Y)))) = _
  rw [operatorObservationQuotientReadout_mk,
    operatorObservationQuotientReadout_mk]
  change operatorSageObservationMap
      (operatorSageTopologicalMul
        (operatorSageObservationInverse (operatorSageObservationMap X))
        (operatorSageObservationInverse (operatorSageObservationMap Y))) = _
  rw [show operatorSageObservationInverse
      (operatorSageObservationMap X) = X by
        exact (operatorSageFeatureHomeomorph (A := A)).left_inv X,
    show operatorSageObservationInverse
      (operatorSageObservationMap Y) = Y by
        exact (operatorSageFeatureHomeomorph (A := A)).left_inv Y]

theorem chiralOperatorCycleQuotientReadout_intertwines
    (q : ChiralOperatorObservationalQuotient A) :
    operatorObservationQuotientReadout
        (operatorSageLatentSystem (A := A))
        (chiralOperatorCycleQuotientMap q) =
      fun i =>
        operatorObservationQuotientReadout
          (operatorSageLatentSystem (A := A)) q
          (operatorSageFeatureCycle i) := by
  refine Quotient.inductionOn q ?_
  intro X
  simp only [chiralOperatorCycleQuotientMap_mk,
    operatorObservationQuotientReadout_mk]
  exact operatorSageObservation_cycle_intertwines_map X

theorem chiralOperatorQuotientZornMulReadout_cycle_equivariant
    (q r : ChiralOperatorObservationalQuotient A) :
    chiralOperatorQuotientZornMulReadout
        (chiralOperatorCycleQuotientMap q)
        (chiralOperatorCycleQuotientMap r) =
      fun i =>
        chiralOperatorQuotientZornMulReadout q r
          (operatorSageFeatureCycle i) := by
  refine Quotient.inductionOn q ?_
  intro X
  refine Quotient.inductionOn r ?_
  intro Y
  simp only [chiralOperatorCycleQuotientMap_mk,
    chiralOperatorQuotientZornMulReadout_mk]
  rw [← chiralOperatorCycle_zornMul_equivariant X Y]
  exact operatorSageObservation_cycle_intertwines_map
    (operatorSageTopologicalMul X Y)

end
end InfoGeometry.Topology
