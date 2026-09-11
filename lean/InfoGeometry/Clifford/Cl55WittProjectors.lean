import InfoGeometry.Clifford.Cl55WittCircularAxes
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution

/-!
# Hyperbolic spectral projectors in `Cl(5,5)`

These are projectors in the noncommutative Clifford algebra itself.  No
diagonal or scalar model is used: the grading is the CAR-derived element
`creation55 i + annihilation55 i`.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.OperatorAlgebra

def hyperbolicInvolution55 (i : Fin 5) : ChiralInvolution Cl55 where
  chi := hyperbolicAxis55 i
  chi_sq := hyperbolicAxis55_sq i

def hyperbolicProjector55Plus (i : Fin 5) : Cl55 :=
  (hyperbolicInvolution55 i).Pleft

def hyperbolicProjector55Minus (i : Fin 5) : Cl55 :=
  (hyperbolicInvolution55 i).Pright

def hyperbolicCircularPolarization55 (i : Fin 5) :
    CircularPolarization Cl55 :=
  (hyperbolicInvolution55 i).toCircularPolarization

def hyperbolicChiralStage55 (i : Fin 5) :
    TomitaCartanSplit.ChiralStage Cl55 :=
  (hyperbolicInvolution55 i).toChiralStage

@[simp] theorem hyperbolicProjector55Plus_idem (i : Fin 5) :
    hyperbolicProjector55Plus i * hyperbolicProjector55Plus i =
      hyperbolicProjector55Plus i := by
  exact (hyperbolicInvolution55 i).Pleft_idem

@[simp] theorem hyperbolicProjector55Minus_idem (i : Fin 5) :
    hyperbolicProjector55Minus i * hyperbolicProjector55Minus i =
      hyperbolicProjector55Minus i := by
  exact (hyperbolicInvolution55 i).Pright_idem

@[simp] theorem hyperbolicProjector55Plus_mul_minus (i : Fin 5) :
    hyperbolicProjector55Plus i * hyperbolicProjector55Minus i = 0 := by
  exact (hyperbolicInvolution55 i).Pleft_mul_Pright

@[simp] theorem hyperbolicProjector55Minus_mul_plus (i : Fin 5) :
    hyperbolicProjector55Minus i * hyperbolicProjector55Plus i = 0 := by
  exact (hyperbolicInvolution55 i).Pright_mul_Pleft

theorem hyperbolicProjector55_complement (i : Fin 5) :
    hyperbolicProjector55Plus i + hyperbolicProjector55Minus i = 1 := by
  exact (hyperbolicInvolution55 i).Pleft_add_Pright

theorem hyperbolicProjector55_difference (i : Fin 5) :
    hyperbolicProjector55Plus i - hyperbolicProjector55Minus i =
      hyperbolicAxis55 i := by
  exact (hyperbolicInvolution55 i).Pleft_sub_Pright

@[simp] theorem hyperbolicAxis55_mul_projectorPlus (i : Fin 5) :
    hyperbolicAxis55 i * hyperbolicProjector55Plus i =
      hyperbolicProjector55Plus i := by
  exact (hyperbolicInvolution55 i).chi_mul_Pleft

@[simp] theorem hyperbolicAxis55_mul_projectorMinus (i : Fin 5) :
    hyperbolicAxis55 i * hyperbolicProjector55Minus i =
      -hyperbolicProjector55Minus i := by
  exact (hyperbolicInvolution55 i).chi_mul_Pright

@[simp] theorem hyperbolicProjector55Plus_mul_axis (i : Fin 5) :
    hyperbolicProjector55Plus i * hyperbolicAxis55 i =
      hyperbolicProjector55Plus i := by
  exact (hyperbolicInvolution55 i).Pleft_mul_chi

@[simp] theorem hyperbolicProjector55Minus_mul_axis (i : Fin 5) :
    hyperbolicProjector55Minus i * hyperbolicAxis55 i =
      -hyperbolicProjector55Minus i := by
  exact (hyperbolicInvolution55 i).Pright_mul_chi

theorem spinTransported_hyperbolicProjector55Plus_idem
    (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (hyperbolicProjector55Plus i) *
        spinCliffordRingEquiv g (hyperbolicProjector55Plus i) =
      spinCliffordRingEquiv g (hyperbolicProjector55Plus i) := by
  simpa only [map_mul] using
    congrArg (spinCliffordRingEquiv g) (hyperbolicProjector55Plus_idem i)

theorem spinTransported_hyperbolicProjector55_complement
    (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (hyperbolicProjector55Plus i) +
        spinCliffordRingEquiv g (hyperbolicProjector55Minus i) = 1 := by
  simpa only [map_add, map_one] using
    congrArg (spinCliffordRingEquiv g) (hyperbolicProjector55_complement i)

@[simp] theorem spinTransported_hyperbolicProjector55Minus_idem
    (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (hyperbolicProjector55Minus i) *
        spinCliffordRingEquiv g (hyperbolicProjector55Minus i) =
      spinCliffordRingEquiv g (hyperbolicProjector55Minus i) := by
  simpa only [map_mul] using
    congrArg (spinCliffordRingEquiv g) (hyperbolicProjector55Minus_idem i)

theorem spinTransported_hyperbolicProjector55Plus_mul_minus
    (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (hyperbolicProjector55Plus i) *
        spinCliffordRingEquiv g (hyperbolicProjector55Minus i) = 0 := by
  simpa only [map_mul, map_zero] using
    congrArg (spinCliffordRingEquiv g) (hyperbolicProjector55Plus_mul_minus i)

theorem spinTransported_hyperbolicProjector55Minus_mul_plus
    (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (hyperbolicProjector55Minus i) *
        spinCliffordRingEquiv g (hyperbolicProjector55Plus i) = 0 := by
  simpa only [map_mul, map_zero] using
    congrArg (spinCliffordRingEquiv g) (hyperbolicProjector55Minus_mul_plus i)

theorem spinTransported_hyperbolicProjector55_difference
    (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (hyperbolicProjector55Plus i) -
        spinCliffordRingEquiv g (hyperbolicProjector55Minus i) =
      spinCliffordRingEquiv g (hyperbolicAxis55 i) := by
  simpa only [map_sub] using
    congrArg (spinCliffordRingEquiv g) (hyperbolicProjector55_difference i)

end InfoGeometry.Clifford.Clifford55
