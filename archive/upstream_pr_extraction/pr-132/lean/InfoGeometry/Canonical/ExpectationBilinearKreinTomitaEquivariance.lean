import InfoGeometry.Canonical.FiniteKreinTomitaSixState
import InfoGeometry.Physics.Algebra.KreinBilinearCommutant

/-!
# Krein/Tomita equivariance of expectation readouts

This owner separates two facts.  The finite matrix identities are proved
unconditionally by the existing native owners.  A readout descends through a
kernel only when its equivariance is explicitly witnessed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExpectationBilinearKreinTomitaEquivariance

open InfoGeometry.Canonical.FiniteKreinTomitaSixState
open InfoGeometry.Physics.Algebra

/-! ## Native finite Krein/Tomita identities -/

theorem sixState_tomita_kreinAdjoint_intertwines
    (beta A : SixStateOperator) (hbeta_star : star beta = beta) :
    tomita (kreinAdjoint beta A) =
      kreinAdjoint beta (tomita A) :=
  FiniteKreinTomitaSixState.tomita_kreinAdjoint_intertwines beta A hbeta_star

theorem kreinAdjoint_commutant_closed
    {n : ℕ} (eta A C : Matrix (Fin n) (Fin n) ℂ)
    (h_eta_sq : eta * eta = 1)
    (hcomm : InfoGeometry.Physics.Algebra.comm A C = 0) :
    InfoGeometry.Physics.Algebra.comm
      (InfoGeometry.Physics.Algebra.kreinAdjoint eta A)
      (InfoGeometry.Physics.Algebra.kreinAdjoint eta C) = 0 :=
  InfoGeometry.Physics.Algebra.kreinAdjoint_comm eta A C h_eta_sq hcomm

/-! ## Kernel invariance from a genuine equivariance witness -/

structure EquivariantReadout (Obs Y : Type*) where
  origin : Obs
  readout : Obs → Y
  krein : Obs → Obs
  tomita : Obs → Obs
  krein_readout : ∀ A, readout (krein A) = readout A
  tomita_readout : ∀ A, readout (tomita A) = readout A

def readoutKernel {Obs Y : Type*} (R : EquivariantReadout Obs Y) : Set Obs :=
  {A | R.readout A = R.readout R.origin}

theorem readoutKernel_krein_invariant
    {Obs Y : Type*} (R : EquivariantReadout Obs Y) {A : Obs}
    (hA : A ∈ readoutKernel R) : R.krein A ∈ readoutKernel R := by
  change R.readout (R.krein A) = R.readout R.origin
  rw [R.krein_readout, hA]

theorem readoutKernel_tomita_invariant
    {Obs Y : Type*} (R : EquivariantReadout Obs Y) {A : Obs}
    (hA : A ∈ readoutKernel R) : R.tomita A ∈ readoutKernel R := by
  change R.readout (R.tomita A) = R.readout R.origin
  rw [R.tomita_readout, hA]

/-! ## Quotient by equal readouts -/

/-- Two observables are equivalent exactly when the chosen readout cannot
distinguish them. -/
def readoutSetoid {Obs Y : Type*} (f : Obs → Y) : Setoid Obs where
  r A B := f A = f B
  iseqv :=
    (show Equivalence (fun A B : Obs => f A = f B) from
      ⟨(fun A => Eq.refl (f A)),
        (fun h => Eq.symm h),
        (fun hAB hBC => Eq.trans hAB hBC)⟩)

abbrev readoutQuotient {Obs Y : Type*} (f : Obs → Y) :=
  Quotient (readoutSetoid f)

def readoutQuotientMk {Obs Y : Type*} (f : Obs → Y) (A : Obs) :
    readoutQuotient f :=
  Quotient.mk (readoutSetoid f) A

/-- The quotient class is sent to its measured value together with the proof
that this value lies in the readout range. -/
def readoutQuotientRange {Obs Y : Type*} (f : Obs → Y) :
    readoutQuotient f → Set.range f :=
  @Quotient.lift Obs (Set.range f) (readoutSetoid f)
    (fun A => (⟨f A, ⟨A, rfl⟩⟩ : Set.range f))
    (by
      intro A B h
      apply Subtype.ext
      exact h)

theorem readoutQuotientRange_mk {Obs Y : Type*} (f : Obs → Y) (A : Obs) :
    readoutQuotientRange f (readoutQuotientMk f A) =
      (⟨f A, ⟨A, rfl⟩⟩ : Set.range f) := by
  rfl

/-- Equal-readout quotient and readout range are canonically equivalent. -/
def readoutQuotientRangeEquiv {Obs Y : Type*} (f : Obs → Y) :
    readoutQuotient f ≃ Set.range f where
  toFun := readoutQuotientRange f
  invFun := fun y => readoutQuotientMk f (Classical.choose y.2)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro A
    apply @Quotient.sound Obs (readoutSetoid f)
    exact Classical.choose_spec (show ∃ B, f B = f A from ⟨A, rfl⟩)
  right_inv := by
    rintro ⟨y, ⟨A, hA⟩⟩
    apply Subtype.ext
    simpa using (Classical.choose_spec (show ∃ B, f B = y from ⟨A, hA⟩))

theorem readoutQuotientRangeEquiv_bijective {Obs Y : Type*} (f : Obs → Y) :
    Function.Bijective (readoutQuotientRange f) :=
  (readoutQuotientRangeEquiv f).bijective

end InfoGeometry.Canonical.ExpectationBilinearKreinTomitaEquivariance

end noncomputable section
