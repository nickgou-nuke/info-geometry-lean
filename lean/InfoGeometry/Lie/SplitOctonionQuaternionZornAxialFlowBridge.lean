import InfoGeometry.Canonical.SplitOctonionQuaternionZornPolarBridge
import InfoGeometry.Lie.SplitOctonionAxialCartanFlow
import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionQuaternionZornAxialFlowBridge

open SplitOctonion
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.SplitOctonionQuaternionZornPolarBridge
open InfoGeometry.Lie.SplitOctonionAxialCartanFlow
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

def splitOctonionAxialCartanTransport
    (k : Fin 3 → ℝ) (t : ℝ) : SplitOctonion ≃ SplitOctonion :=
  splitOctonionCanonicalZornEquiv.trans
    ((axialCartanFlow k t).toEquiv.trans
      splitOctonionCanonicalZornEquiv.symm)

@[simp] theorem splitOctonionAxialCartanTransport_apply
    (k : Fin 3 → ℝ) (t : ℝ) (X : SplitOctonion) :
    splitOctonionAxialCartanTransport k t X =
      splitOctonionCanonicalZornEquiv.symm
        (axialCartanFlow k t
          (splitOctonionCanonicalZornEquiv X)) :=
  rfl

theorem splitOctonionAxialCartanTransport_intertwines_canonical_product
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X Y : SplitOctonion) :
    splitOctonionAxialCartanTransport k t
        (splitOctonionCanonicalZornEquiv.symm
          (splitOctonionCanonicalZornEquiv X *
            splitOctonionCanonicalZornEquiv Y)) =
      splitOctonionCanonicalZornEquiv.symm
        (axialCartanFlow k t (splitOctonionCanonicalZornEquiv X) *
          axialCartanFlow k t (splitOctonionCanonicalZornEquiv Y)) := by
  rw [splitOctonionAxialCartanTransport_apply,
    Equiv.apply_symm_apply, axialCartanFlow_map_mul k hk t]

@[simp] theorem splitOctonionAxialCartanTransport_zero
    (k : Fin 3 → ℝ) :
    splitOctonionAxialCartanTransport k 0 = Equiv.refl SplitOctonion := by
  apply Equiv.ext
  intro X
  rw [splitOctonionAxialCartanTransport_apply, axialCartanFlow_zero]
  exact splitOctonionCanonicalZornEquiv.symm_apply_apply X

theorem splitOctonionAxialCartanTransport_add
    (k : Fin 3 → ℝ) (s t : ℝ) (X : SplitOctonion) :
    splitOctonionAxialCartanTransport k (s + t) X =
      splitOctonionAxialCartanTransport k s
        (splitOctonionAxialCartanTransport k t X) := by
  simp only [splitOctonionAxialCartanTransport_apply,
    Equiv.apply_symm_apply, axialCartanFlow_add]

theorem splitOctonionAxialCartanTransport_neg
    (k : Fin 3 → ℝ) (t : ℝ) :
    splitOctonionAxialCartanTransport k (-t) =
      (splitOctonionAxialCartanTransport k t).symm := by
  apply Equiv.ext
  intro X
  simp [splitOctonionAxialCartanTransport, axialCartanFlow_neg_apply]

theorem splitOctonionAxialCartanTransport_add_equiv
    (k : Fin 3 → ℝ) (s t : ℝ) :
    splitOctonionAxialCartanTransport k (s + t) =
      (splitOctonionAxialCartanTransport k t).trans
        (splitOctonionAxialCartanTransport k s) := by
  apply Equiv.ext
  intro X
  exact splitOctonionAxialCartanTransport_add k s t X

theorem splitOctonionAxialCartanTransport_preserves_norm
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : SplitOctonion) :
    normSQ (splitOctonionAxialCartanTransport k t X) = normSQ X := by
  rw [← splitOctonionCanonicalZornEquiv_norm,
    ← splitOctonionCanonicalZornEquiv_norm]
  simp only [splitOctonionAxialCartanTransport_apply,
    Equiv.apply_symm_apply]
  exact axialCartanCompositionAut_preserves_det k hk t
    (splitOctonionCanonicalZornEquiv X)

theorem splitOctonionAxialCartanTransport_preserves_hyperbolic
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : SplitOctonion) :
    isHyperbolic (splitOctonionAxialCartanTransport k t X) ↔
      isHyperbolic X := by
  unfold isHyperbolic
  rw [splitOctonionAxialCartanTransport_preserves_norm k hk t X]

theorem splitOctonionAxialCartanTransport_preserves_canonicalZorn_null
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (X : SplitOctonion) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (splitOctonionCanonicalZornEquiv
          (splitOctonionAxialCartanTransport k t X)) = 0 ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (splitOctonionCanonicalZornEquiv X) = 0 := by
  rw [splitOctonionCanonicalZornEquiv_norm,
    splitOctonionCanonicalZornEquiv_norm,
    splitOctonionAxialCartanTransport_preserves_norm k hk t X]

def splitOctonionCanonicalNullTransportEquiv
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    {X : SplitOctonion //
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
          (splitOctonionCanonicalZornEquiv X) = 0} ≃
      {X : SplitOctonion //
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
          (splitOctonionCanonicalZornEquiv X) = 0} where
  toFun X :=
    ⟨splitOctonionAxialCartanTransport k t X.1,
      (splitOctonionAxialCartanTransport_preserves_canonicalZorn_null
        k hk t X.1).2 X.2⟩
  invFun X :=
    ⟨splitOctonionAxialCartanTransport k (-t) X.1,
      (splitOctonionAxialCartanTransport_preserves_canonicalZorn_null
        k hk (-t) X.1).2 X.2⟩
  left_inv X := by
    apply Subtype.ext
    change splitOctonionAxialCartanTransport k (-t)
        (splitOctonionAxialCartanTransport k t X.1) = X.1
    rw [← splitOctonionAxialCartanTransport_add]
    simp
  right_inv X := by
    apply Subtype.ext
    change splitOctonionAxialCartanTransport k t
        (splitOctonionAxialCartanTransport k (-t) X.1) = X.1
    rw [← splitOctonionAxialCartanTransport_add]
    simp

theorem splitOctonionCanonicalNullTransportEquiv_add
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (s t : ℝ) :
    splitOctonionCanonicalNullTransportEquiv k hk (s + t) =
      (splitOctonionCanonicalNullTransportEquiv k hk t).trans
        (splitOctonionCanonicalNullTransportEquiv k hk s) := by
  apply Equiv.ext
  intro X
  apply Subtype.ext
  exact splitOctonionAxialCartanTransport_add k s t X.1

theorem splitOctonionAxialCartanTransport_preserves_polarRho
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X : SplitOctonion) (h : isHyperbolic X) :
    polarRho (splitOctonionAxialCartanTransport k t X)
        ((splitOctonionAxialCartanTransport_preserves_hyperbolic k hk t X).2 h) =
      polarRho X h := by
  unfold polarRho
  rw [splitOctonionAxialCartanTransport_preserves_norm k hk t X]

theorem splitOctonionAxialCartanTransport_preserves_canonicalZorn_polar
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X Y : SplitOctonion) :
    polarZ realCrossProduct3
        (splitOctonionCanonicalZornEquiv
          (splitOctonionAxialCartanTransport k t X))
        (splitOctonionCanonicalZornEquiv
          (splitOctonionAxialCartanTransport k t Y)) =
      polarZ realCrossProduct3
        (splitOctonionCanonicalZornEquiv X)
        (splitOctonionCanonicalZornEquiv Y) := by
  simp only [splitOctonionAxialCartanTransport_apply,
    Equiv.apply_symm_apply]
  exact axialCartanFlow_preserves_polar k hk t
    (splitOctonionCanonicalZornEquiv X)
    (splitOctonionCanonicalZornEquiv Y)

theorem splitOctonionAxialCartanTransport_preserves_canonicalZorn_incident
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (X Y : SplitOctonion) :
    IncidentRep realCrossProduct3
        (splitOctonionCanonicalZornEquiv
          (splitOctonionAxialCartanTransport k t X))
        (splitOctonionCanonicalZornEquiv
          (splitOctonionAxialCartanTransport k t Y)) ↔
      IncidentRep realCrossProduct3 (splitOctonionCanonicalZornEquiv X)
        (splitOctonionCanonicalZornEquiv Y) := by
  simp only [splitOctonionAxialCartanTransport_apply,
    Equiv.apply_symm_apply]
  exact axialCartanFlow_preserves_incident k hk t
    (splitOctonionCanonicalZornEquiv X)
    (splitOctonionCanonicalZornEquiv Y)

end InfoGeometry.Lie.SplitOctonionQuaternionZornAxialFlowBridge
