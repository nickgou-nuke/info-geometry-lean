import InfoGeometry.Arithmetic.CantorDiracOperator
import InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
import InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator
import InfoGeometry.Algebra.FiniteInductiveSUSY
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

noncomputable section

namespace LatticeHilbertPolyaPipeline

universe u

open InfoGeometry.Arithmetic.PrimeBitWittenIndex (PrimeRegister)

abbrev PrimeCutoff :=
  InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeCutoff

abbrev PrimeMode (P : PrimeCutoff) :=
  InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.PrimeMode P

abbrev CantorField (P : PrimeCutoff) :=
  InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.CantorField P

abbrev Vertex (P : PrimeCutoff) :=
  InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.Vertex P

structure FiniteMajoranaLattice
    (Op : Type*) [Ring Op] [Algebra ℝ Op] [StarRing Op] [StarModule ℝ Op] where
  register : PrimeRegister
  gamma : ℕ → Op
  clifford :
    InfoGeometry.Arithmetic.CantorDiracOperator.IsMajoranaCliffordRepresentation
      register gamma
  gamma_selfAdjoint : ∀ p ∈ register.primes, star (gamma p) = gamma p

namespace FiniteMajoranaLattice

variable {Op : Type*} [Ring Op] [Algebra ℝ Op] [StarRing Op] [StarModule ℝ Op]

def D (M : FiniteMajoranaLattice Op) : Op :=
  InfoGeometry.Arithmetic.CantorDiracOperator.cantorDiracOperator M.register M.gamma

def H (M : FiniteMajoranaLattice Op) : Op :=
  InfoGeometry.Arithmetic.CantorDiracOperator.cantorDiracHamiltonian (Op := Op) M.register

theorem D_selfAdjoint (M : FiniteMajoranaLattice Op) :
    IsSelfAdjoint M.D := by
  exact InfoGeometry.Arithmetic.CantorDiracOperator.cantorDirac_selfAdjoint_of_generator_selfAdjoint
    M.register M.gamma M.gamma_selfAdjoint

theorem D_sq_eq_H (M : FiniteMajoranaLattice Op) :
    M.D ^ 2 = M.H := by
  exact InfoGeometry.Arithmetic.CantorDiracOperator.cantorDirac_sq_eq_hamiltonian_of_clifford
    M.register M.gamma M.clifford

end FiniteMajoranaLattice

structure FiniteZetaDiracLattice (P : PrimeCutoff) where
  packet : InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.FiniteCantorZetaDirac P
  amplitude_selfAdjoint :
    ∀ p : PrimeMode P, star (packet.amplitude p) = packet.amplitude p

namespace FiniteZetaDiracLattice

variable {P : PrimeCutoff}

def D (Z : FiniteZetaDiracLattice P) (s : ℂ) : CantorField P → CantorField P :=
  Z.packet.op s

def Q (Z : FiniteZetaDiracLattice P) (s : ℂ) : CantorField P → CantorField P :=
  Z.packet.Q s

def Qsharp (Z : FiniteZetaDiracLattice P) (s : ℂ) : CantorField P → CantorField P :=
  Z.packet.Qsharp s

theorem D_eq_Q_add_Qsharp
    (Z : FiniteZetaDiracLattice P) (s : ℂ) (f : CantorField P) (S : Vertex P) :
    Z.D s f S = Z.Q s f S + Z.Qsharp s f S := by
  rfl

theorem D_selfAdjoint_of_unitary
    (Z : FiniteZetaDiracLattice P) (s : ℂ)
    (hU : Z.packet.HolonomyUnitaryAt s) :
    InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.FiniteCantorZetaDirac.IsAdjointPair
      (P := P) (Z.D s) (Z.D s) := by
  exact Z.packet.op_isSelfAdjoint_of_unitary_data s Z.amplitude_selfAdjoint hU

theorem D_selfAdjoint_of_zetaCriticalLine
    (Z : FiniteZetaDiracLattice P) (hP : P.primes.Nonempty) (s : ℂ)
    (hhol :
      Z.packet.holonomy s =
        InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2) :
    InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.FiniteCantorZetaDirac.IsAdjointPair
      (P := P) (Z.D s) (Z.D s) := by
  exact
    Z.packet.op_isSelfAdjoint_of_unitary_data_of_zetaHolonomy
      hP s hhol hs Z.amplitude_selfAdjoint

end FiniteZetaDiracLattice

structure FiniteSuperchargeInduction
    (Stage : ℕ → Type u) [∀ n : ℕ, Ring (Stage n)] where
  bond : ∀ n : ℕ, Stage n →+* Stage (n + 1)
  Q : ∀ n : ℕ, Stage n
  Qsharp : ∀ n : ℕ, Stage n
  H : ∀ n : ℕ, Stage n
  Z : ∀ n : ℕ, Stage n
  Q_sq_zero_zero : Q 0 * Q 0 = 0
  Qsharp_sq_zero_zero : Qsharp 0 * Qsharp 0 = 0
  closure_zero :
    InfoGeometry.Algebra.FiniteInductiveSUSY.anticomm (Q 0) (Qsharp 0) = H 0 + Z 0
  bond_Q : ∀ n : ℕ, bond n (Q n) = Q (n + 1)
  bond_Qsharp : ∀ n : ℕ, bond n (Qsharp n) = Qsharp (n + 1)
  bond_H : ∀ n : ℕ, bond n (H n) = H (n + 1)
  bond_Z : ∀ n : ℕ, bond n (Z n) = Z (n + 1)

namespace FiniteSuperchargeInduction

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

variable {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]

def inductionDiracSeries (S : FiniteSuperchargeInduction Stage) (n : ℕ) : Stage n :=
  S.Q n + S.Qsharp n

def inductionHamiltonianSeries (S : FiniteSuperchargeInduction Stage) (n : ℕ) : Stage n :=
  S.H n + S.Z n

theorem bond_inductionDiracSeries
    (S : FiniteSuperchargeInduction Stage) (n : ℕ) :
    S.bond n (S.inductionDiracSeries n) = S.inductionDiracSeries (n + 1) := by
  unfold inductionDiracSeries
  rw [map_add, S.bond_Q n, S.bond_Qsharp n]

theorem bond_inductionHamiltonianSeries
    (S : FiniteSuperchargeInduction Stage) (n : ℕ) :
    S.bond n (S.inductionHamiltonianSeries n) =
      S.inductionHamiltonianSeries (n + 1) := by
  unfold inductionHamiltonianSeries
  rw [map_add, S.bond_H n, S.bond_Z n]

theorem inductionSeries_square_closure
    (S : FiniteSuperchargeInduction Stage) (n : ℕ) :
    S.inductionDiracSeries n * S.inductionDiracSeries n =
      S.inductionHamiltonianSeries n := by
  simpa [inductionDiracSeries, inductionHamiltonianSeries] using
    InfoGeometry.Algebra.FiniteInductiveSUSY.dirac_square_closure_chain
      (A := Stage) S.bond S.Q S.Qsharp S.H S.Z
      S.Q_sq_zero_zero S.Qsharp_sq_zero_zero S.closure_zero
      (fun n => (S.bond_Q n).symm)
      (fun n => (S.bond_Qsharp n).symm)
      (fun n => (S.bond_H n).symm)
      (fun n => (S.bond_Z n).symm)
      n

theorem directLimit_inductionDiracSeries_constant
    (S : FiniteSuperchargeInduction Stage) (n : ℕ) :
    directLimitOf (Stage := Stage) S.bond n (S.inductionDiracSeries n) =
      directLimitOf (Stage := Stage) S.bond 0 (S.inductionDiracSeries 0) := by
  exact
    directLimitOf_eq_zero_stage (Stage := Stage) S.bond
      (fun n => S.inductionDiracSeries n)
      (S.bond_inductionDiracSeries)
      n

theorem directLimit_inductionHamiltonianSeries_constant
    (S : FiniteSuperchargeInduction Stage) (n : ℕ) :
    directLimitOf (Stage := Stage) S.bond n (S.inductionHamiltonianSeries n) =
      directLimitOf (Stage := Stage) S.bond 0 (S.inductionHamiltonianSeries 0) := by
  exact
    directLimitOf_eq_zero_stage (Stage := Stage) S.bond
      (fun n => S.inductionHamiltonianSeries n)
      (S.bond_inductionHamiltonianSeries)
      n

theorem directLimit_inductionSeries_square_closure
    (S : FiniteSuperchargeInduction Stage) (n : ℕ) :
    directLimitOf (Stage := Stage) S.bond n (S.inductionDiracSeries n) *
        directLimitOf (Stage := Stage) S.bond n (S.inductionDiracSeries n) =
      directLimitOf (Stage := Stage) S.bond n (S.inductionHamiltonianSeries n) := by
  rw [← map_mul]
  exact
    congrArg
      (directLimitOf (Stage := Stage) S.bond n)
      (S.inductionSeries_square_closure n)

theorem directLimit_inductionSeries_square_closure_zeroStage
    (S : FiniteSuperchargeInduction Stage) (n : ℕ) :
    directLimitOf (Stage := Stage) S.bond n (S.inductionDiracSeries n) *
        directLimitOf (Stage := Stage) S.bond n (S.inductionDiracSeries n) =
      directLimitOf (Stage := Stage) S.bond 0 (S.inductionHamiltonianSeries 0) := by
  rw [S.directLimit_inductionSeries_square_closure n,
    S.directLimit_inductionHamiltonianSeries_constant n]

theorem cone_inductionDiracSeries_constant
    {Limit : Type u} [Semiring Limit]
    (S : FiniteSuperchargeInduction Stage)
    (toLimit : ∀ n : ℕ, Stage n →+* Limit)
    (hcone :
      InfoGeometry.Algebra.InfiniteSuperClosureLemmas.CompatibleCone S.bond toLimit)
    (n : ℕ) :
    toLimit n (S.inductionDiracSeries n) =
      toLimit 0 (S.inductionDiracSeries 0) := by
  exact
    InfoGeometry.Canonical.CategoricalRecursiveClosureBridge.cone_stageImage_constant
      S.bond toLimit hcone
      (fun n => S.inductionDiracSeries n)
      (S.bond_inductionDiracSeries)
      n

theorem cone_inductionHamiltonianSeries_constant
    {Limit : Type u} [Semiring Limit]
    (S : FiniteSuperchargeInduction Stage)
    (toLimit : ∀ n : ℕ, Stage n →+* Limit)
    (hcone :
      InfoGeometry.Algebra.InfiniteSuperClosureLemmas.CompatibleCone S.bond toLimit)
    (n : ℕ) :
    toLimit n (S.inductionHamiltonianSeries n) =
      toLimit 0 (S.inductionHamiltonianSeries 0) := by
  exact
    InfoGeometry.Canonical.CategoricalRecursiveClosureBridge.cone_stageImage_constant
      S.bond toLimit hcone
      (fun n => S.inductionHamiltonianSeries n)
      (S.bond_inductionHamiltonianSeries)
      n

theorem cone_inductionSeries_square_closure
    {Limit : Type u} [Semiring Limit]
    (S : FiniteSuperchargeInduction Stage)
    (toLimit : ∀ n : ℕ, Stage n →+* Limit)
    (n : ℕ) :
    toLimit n (S.inductionDiracSeries n) * toLimit n (S.inductionDiracSeries n) =
      toLimit n (S.inductionHamiltonianSeries n) := by
  rw [← map_mul]
  exact congrArg (toLimit n) (S.inductionSeries_square_closure n)

theorem cone_inductionSeries_square_closure_zeroStage
    {Limit : Type u} [Semiring Limit]
    (S : FiniteSuperchargeInduction Stage)
    (toLimit : ∀ n : ℕ, Stage n →+* Limit)
    (hcone :
      InfoGeometry.Algebra.InfiniteSuperClosureLemmas.CompatibleCone S.bond toLimit)
    (n : ℕ) :
    toLimit n (S.inductionDiracSeries n) * toLimit n (S.inductionDiracSeries n) =
      toLimit 0 (S.inductionHamiltonianSeries 0) := by
  rw [S.cone_inductionSeries_square_closure toLimit n,
    S.cone_inductionHamiltonianSeries_constant toLimit hcone n]

end FiniteSuperchargeInduction

structure FiniteHestenesKreinLattice (P : PrimeCutoff) where
  packet :
    InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.FiniteBerryKeatingCantorDirac P
  amplitude_selfAdjoint :
    ∀ p : PrimeMode P, star (packet.amplitude p) = packet.amplitude p
  zeta_holonomy :
    ∀ s : ℂ,
      packet.holonomy s =
        InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.zetaHolonomy (P := P) s

namespace FiniteHestenesKreinLattice

variable {P : PrimeCutoff}

def toZetaDiracLattice (L : FiniteHestenesKreinLattice P) :
    FiniteZetaDiracLattice P :=
  { packet := L.packet.toCantorZetaDirac
    amplitude_selfAdjoint := L.amplitude_selfAdjoint }

theorem D_eq_Q_add_Qsharp
    (L : FiniteHestenesKreinLattice P) (s : ℂ) (f : CantorField P) (S : Vertex P) :
    L.packet.D s f S = L.packet.Q s f S + L.packet.Qsharp s f S := by
  rfl

theorem D_selfAdjoint_of_zetaCriticalLine
    (L : FiniteHestenesKreinLattice P) (hP : P.primes.Nonempty) (s : ℂ)
    (hs : s.re = 1 / 2) :
    InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.FiniteCantorZetaDirac.IsAdjointPair
      (P := P) (L.packet.D s) (L.packet.D s) := by
  have hhol :
      L.packet.toCantorZetaDirac.holonomy s =
        InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.zetaHolonomy (P := P) s := by
    simpa
      [InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.FiniteBerryKeatingCantorDirac.toCantorZetaDirac]
      using L.zeta_holonomy s
  have hself :
      InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.FiniteCantorZetaDirac.IsAdjointPair
        (P := P)
        ((L.toZetaDiracLattice).D s)
        ((L.toZetaDiracLattice).D s) :=
    (L.toZetaDiracLattice).D_selfAdjoint_of_zetaCriticalLine hP s hhol hs
  simpa
    [FiniteZetaDiracLattice.D,
      toZetaDiracLattice,
      InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator.FiniteBerryKeatingCantorDirac.D]
    using hself

end FiniteHestenesKreinLattice

namespace HilbertPolyaLemmaSeries

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

def FiniteCriticalLineSelfAdjointLemma
    {P : PrimeCutoff} (L : FiniteHestenesKreinLattice P) : Prop :=
  P.primes.Nonempty →
    ∀ s : ℂ, s.re = 1 / 2 →
      InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.FiniteCantorZetaDirac.IsAdjointPair
        (P := P) (L.packet.D s) (L.packet.D s)

theorem finiteCriticalLineSelfAdjoint
    {P : PrimeCutoff} (L : FiniteHestenesKreinLattice P) :
    FiniteCriticalLineSelfAdjointLemma L := by
  intro hP s hs
  exact L.D_selfAdjoint_of_zetaCriticalLine hP s hs

def InductionSeriesSquareClosureLemma
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    (S : FiniteSuperchargeInduction Stage) : Prop :=
  ∀ n : ℕ,
    S.inductionDiracSeries n * S.inductionDiracSeries n =
      S.inductionHamiltonianSeries n

theorem inductionSeriesSquareClosure
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    (S : FiniteSuperchargeInduction Stage) :
    InductionSeriesSquareClosureLemma S :=
  S.inductionSeries_square_closure

def DirectLimitReadbackLemma
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    (S : FiniteSuperchargeInduction Stage) : Prop :=
  ∀ n : ℕ,
    directLimitOf (Stage := Stage) S.bond n (S.inductionDiracSeries n) =
      directLimitOf (Stage := Stage) S.bond 0 (S.inductionDiracSeries 0)

theorem directLimitReadback
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    (S : FiniteSuperchargeInduction Stage) :
    DirectLimitReadbackLemma S :=
  S.directLimit_inductionDiracSeries_constant

def DirectLimitHamiltonianReadbackLemma
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    (S : FiniteSuperchargeInduction Stage) : Prop :=
  ∀ n : ℕ,
    directLimitOf (Stage := Stage) S.bond n (S.inductionHamiltonianSeries n) =
      directLimitOf (Stage := Stage) S.bond 0 (S.inductionHamiltonianSeries 0)

theorem directLimitHamiltonianReadback
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    (S : FiniteSuperchargeInduction Stage) :
    DirectLimitHamiltonianReadbackLemma S :=
  S.directLimit_inductionHamiltonianSeries_constant

def DirectLimitSquareClosureReadbackLemma
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    (S : FiniteSuperchargeInduction Stage) : Prop :=
  ∀ n : ℕ,
    directLimitOf (Stage := Stage) S.bond n (S.inductionDiracSeries n) *
        directLimitOf (Stage := Stage) S.bond n (S.inductionDiracSeries n) =
      directLimitOf (Stage := Stage) S.bond 0 (S.inductionHamiltonianSeries 0)

theorem directLimitSquareClosureReadback
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    (S : FiniteSuperchargeInduction Stage) :
    DirectLimitSquareClosureReadbackLemma S :=
  S.directLimit_inductionSeries_square_closure_zeroStage

def ConeReadbackLemma
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    {Limit : Type u} [Semiring Limit]
    (S : FiniteSuperchargeInduction Stage)
    (toLimit : ∀ n : ℕ, Stage n →+* Limit) : Prop :=
  InfoGeometry.Algebra.InfiniteSuperClosureLemmas.CompatibleCone S.bond toLimit →
    ∀ n : ℕ,
      toLimit n (S.inductionDiracSeries n) =
        toLimit 0 (S.inductionDiracSeries 0)

theorem coneReadback
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    {Limit : Type u} [Semiring Limit]
    (S : FiniteSuperchargeInduction Stage)
    (toLimit : ∀ n : ℕ, Stage n →+* Limit) :
    ConeReadbackLemma S toLimit := by
  intro hcone n
  exact S.cone_inductionDiracSeries_constant toLimit hcone n

def ConeHamiltonianReadbackLemma
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    {Limit : Type u} [Semiring Limit]
    (S : FiniteSuperchargeInduction Stage)
    (toLimit : ∀ n : ℕ, Stage n →+* Limit) : Prop :=
  InfoGeometry.Algebra.InfiniteSuperClosureLemmas.CompatibleCone S.bond toLimit →
    ∀ n : ℕ,
      toLimit n (S.inductionHamiltonianSeries n) =
        toLimit 0 (S.inductionHamiltonianSeries 0)

theorem coneHamiltonianReadback
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    {Limit : Type u} [Semiring Limit]
    (S : FiniteSuperchargeInduction Stage)
    (toLimit : ∀ n : ℕ, Stage n →+* Limit) :
    ConeHamiltonianReadbackLemma S toLimit := by
  intro hcone n
  exact S.cone_inductionHamiltonianSeries_constant toLimit hcone n

def ConeSquareClosureReadbackLemma
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    {Limit : Type u} [Semiring Limit]
    (S : FiniteSuperchargeInduction Stage)
    (toLimit : ∀ n : ℕ, Stage n →+* Limit) : Prop :=
  InfoGeometry.Algebra.InfiniteSuperClosureLemmas.CompatibleCone S.bond toLimit →
    ∀ n : ℕ,
      toLimit n (S.inductionDiracSeries n) * toLimit n (S.inductionDiracSeries n) =
        toLimit 0 (S.inductionHamiltonianSeries 0)

theorem coneSquareClosureReadback
    {Stage : ℕ → Type u} [∀ n : ℕ, Ring (Stage n)]
    {Limit : Type u} [Semiring Limit]
    (S : FiniteSuperchargeInduction Stage)
    (toLimit : ∀ n : ℕ, Stage n →+* Limit) :
    ConeSquareClosureReadbackLemma S toLimit := by
  intro hcone n
  exact S.cone_inductionSeries_square_closure_zeroStage toLimit hcone n

def hilbertPolyaEigenparameter (s : ℂ) : ℂ :=
  -Complex.I * (s - (((1 / 2 : ℝ) : ℂ)))

theorem hilbertPolyaEigenparameter_im (s : ℂ) :
    (hilbertPolyaEigenparameter s).im = (1 / 2 : ℝ) - s.re := by
  simp [hilbertPolyaEigenparameter, Complex.mul_im]

theorem criticalLine_of_hilbertPolyaEigenparameter_real
    {s : ℂ} (hreal : (hilbertPolyaEigenparameter s).im = 0) :
    s.re = 1 / 2 := by
  rw [hilbertPolyaEigenparameter_im] at hreal
  linarith

theorem hilbertPolyaEigenparameter_real_of_criticalLine
    {s : ℂ} (hs : s.re = 1 / 2) :
    (hilbertPolyaEigenparameter s).im = 0 := by
  rw [hilbertPolyaEigenparameter_im, hs]
  norm_num

theorem hilbertPolyaEigenparameter_real_iff_criticalLine (s : ℂ) :
    (hilbertPolyaEigenparameter s).im = 0 ↔ s.re = 1 / 2 :=
  ⟨criticalLine_of_hilbertPolyaEigenparameter_real,
    hilbertPolyaEigenparameter_real_of_criticalLine⟩

def EigenvalueEquation
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (T : Carrier → Carrier) (lambda : ℂ) : Prop :=
  ∃ psi : Carrier, psi ≠ 0 ∧ T psi = lambda • psi

def HestenesKreinSymmetricOperator
    {Carrier : Type*}
    (pairing : Carrier → Carrier → ℂ)
    (T : Carrier → Carrier) : Prop :=
  ∀ x y : Carrier, pairing (T x) y = pairing x (T y)

def HestenesKreinRealSpectrumLemma
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (pairing : Carrier → Carrier → ℂ)
    (T : Carrier → Carrier) : Prop :=
  HestenesKreinSymmetricOperator pairing T →
    ∀ lambda : ℂ, EigenvalueEquation T lambda → lambda.im = 0

def AvoidsDefinitizingZeros
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (q : Polynomial ℂ) (T : Carrier → Carrier) : Prop :=
  ∀ lambda : ℂ, EigenvalueEquation T lambda → q.eval lambda ≠ 0

def RealSpectrumAwayFromDefinitizingZeros
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (q : Polynomial ℂ) (T : Carrier → Carrier) : Prop :=
  ∀ lambda : ℂ, EigenvalueEquation T lambda → q.eval lambda ≠ 0 → lambda.im = 0

structure KreinDefinitizableRealSpectrumPacket
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (pairing : Carrier → Carrier → ℂ)
    (T : Carrier → Carrier) where
  symmetric : HestenesKreinSymmetricOperator pairing T
  definitizingPolynomial : Polynomial ℂ
  definitizingPolynomial_nonzero : definitizingPolynomial ≠ 0
  avoidsDefinitizingZeros : AvoidsDefinitizingZeros definitizingPolynomial T
  realAwayFromDefinitizingZeros :
    RealSpectrumAwayFromDefinitizingZeros definitizingPolynomial T

namespace KreinDefinitizableRealSpectrumPacket

variable {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
variable {pairing : Carrier → Carrier → ℂ} {T : Carrier → Carrier}

theorem eigen_im_eq_zero
    (P : KreinDefinitizableRealSpectrumPacket pairing T)
    (lambda : ℂ) (hEigen : EigenvalueEquation T lambda) :
    lambda.im = 0 :=
  P.realAwayFromDefinitizingZeros lambda hEigen
    (P.avoidsDefinitizingZeros lambda hEigen)

theorem toHestenesKreinRealSpectrumLemma
    (P : KreinDefinitizableRealSpectrumPacket pairing T) :
    HestenesKreinRealSpectrumLemma pairing T := by
  intro _ lambda hEigen
  exact P.eigen_im_eq_zero lambda hEigen

end KreinDefinitizableRealSpectrumPacket

theorem kreinDefinitizableRealSpectrum_of_packet
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (pairing : Carrier → Carrier → ℂ)
    (T : Carrier → Carrier)
    (P : KreinDefinitizableRealSpectrumPacket pairing T) :
    HestenesKreinRealSpectrumLemma pairing T :=
  P.toHestenesKreinRealSpectrumLemma

def HilbertSelfAdjointRealSpectrumLemma
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier]
    (T : Carrier →L[ℂ] Carrier) : Prop :=
  IsSelfAdjoint T →
    ∀ lambda : ℂ, EigenvalueEquation (fun x => T x) lambda → lambda.im = 0

theorem hilbertSelfAdjointRealSpectrum
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier]
    (T : Carrier →L[ℂ] Carrier) :
    HilbertSelfAdjointRealSpectrumLemma T := by
  intro hSelf lambda hEigen
  rcases hEigen with ⟨psi, hpsi, hTpsi⟩
  have hSymmetric : (T : Carrier →ₗ[ℂ] Carrier).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSelf)
  have hEigenvector :
      Module.End.HasEigenvector (T : Carrier →ₗ[ℂ] Carrier) lambda psi := by
    exact ⟨Module.End.mem_eigenspace_iff.mpr hTpsi, hpsi⟩
  have hConj :=
    hSymmetric.conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector hEigenvector)
  exact Complex.conj_eq_iff_im.mp hConj

def finiteCharacteristicDeterminant
    {Carrier : Type*} [AddCommGroup Carrier] [Module ℂ Carrier]
    [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (T : Module.End ℂ Carrier) : ℂ → ℂ :=
  fun lambda => T.charpoly.eval lambda

theorem finiteCharacteristicDeterminant_eq_det
    {Carrier : Type*} [AddCommGroup Carrier] [Module ℂ Carrier]
    [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (T : Module.End ℂ Carrier) (lambda : ℂ) :
    finiteCharacteristicDeterminant T lambda =
      LinearMap.det (algebraMap ℂ (Module.End ℂ Carrier) lambda - T) := by
  simpa [finiteCharacteristicDeterminant] using
    (LinearMap.eval_charpoly (f := T) lambda)

theorem finiteCharacteristicDeterminant_zero_to_eigen
    {Carrier : Type*} [AddCommGroup Carrier] [Module ℂ Carrier]
    [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (T : Module.End ℂ Carrier) (lambda : ℂ)
    (hDet : finiteCharacteristicDeterminant T lambda = 0) :
    EigenvalueEquation (fun x => T x) lambda := by
  have hRoot : T.charpoly.IsRoot lambda := by
    simpa [finiteCharacteristicDeterminant, Polynomial.IsRoot] using hDet
  have hEigenvalue : T.HasEigenvalue lambda :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly T lambda).mpr hRoot
  rcases hEigenvalue.exists_hasEigenvector with ⟨psi, hpsi⟩
  exact ⟨psi, hpsi.2, Module.End.mem_eigenspace_iff.mp hpsi.1⟩

theorem finiteCharacteristicDeterminant_zero_iff_eigen
    {Carrier : Type*} [AddCommGroup Carrier] [Module ℂ Carrier]
    [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (T : Module.End ℂ Carrier) (lambda : ℂ) :
    finiteCharacteristicDeterminant T lambda = 0 ↔
      EigenvalueEquation (fun x => T x) lambda := by
  constructor
  · exact finiteCharacteristicDeterminant_zero_to_eigen T lambda
  · intro hEigen
    rcases hEigen with ⟨psi, hpsi, hTpsi⟩
    have hEigenvector : Module.End.HasEigenvector T lambda psi := by
      exact ⟨Module.End.mem_eigenspace_iff.mpr hTpsi, hpsi⟩
    have hEigenvalue : T.HasEigenvalue lambda :=
      Module.End.hasEigenvalue_of_hasEigenvector hEigenvector
    have hRoot : T.charpoly.IsRoot lambda :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly T lambda).mp hEigenvalue
    simpa [finiteCharacteristicDeterminant, Polynomial.IsRoot] using hRoot

theorem finiteCharacteristicDeterminant_ne_zero_iff_no_eigen
    {Carrier : Type*} [AddCommGroup Carrier] [Module ℂ Carrier]
    [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (T : Module.End ℂ Carrier) (lambda : ℂ) :
    finiteCharacteristicDeterminant T lambda ≠ 0 ↔
      ¬ EigenvalueEquation (fun x => T x) lambda :=
  not_congr (finiteCharacteristicDeterminant_zero_iff_eigen T lambda)

theorem finiteCharacteristicDeterminant_zero_to_real_of_hilbertSelfAdjoint
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier] [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (T : Carrier →L[ℂ] Carrier) (hSelf : IsSelfAdjoint T)
    (lambda : ℂ)
    (hDet :
      finiteCharacteristicDeterminant (T : Carrier →ₗ[ℂ] Carrier) lambda = 0) :
    lambda.im = 0 :=
  hilbertSelfAdjointRealSpectrum T hSelf lambda
    (finiteCharacteristicDeterminant_zero_to_eigen
      (T : Carrier →ₗ[ℂ] Carrier) lambda hDet)

def CompletedXiSpectralDeterminantLemma
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (Xi : ℂ → ℂ) (T : Carrier → Carrier) : Prop :=
  ∀ s : ℂ, Xi s = 0 → EigenvalueEquation T (hilbertPolyaEigenparameter s)

structure CompletedXiSpectralDeterminantPacket
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (Xi : ℂ → ℂ) (T : Carrier → Carrier) where
  spectralDeterminant : ℂ → ℂ
  normalizingUnit : ℂ → ℂ
  normalizingUnit_nonzero : ∀ s : ℂ, normalizingUnit s ≠ 0
  xi_eq_unit_mul_det :
    ∀ s : ℂ, Xi s = normalizingUnit s * spectralDeterminant s
  determinant_zero_to_eigen :
    ∀ s : ℂ, spectralDeterminant s = 0 →
      EigenvalueEquation T (hilbertPolyaEigenparameter s)

namespace CompletedXiSpectralDeterminantPacket

variable {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
variable {Xi : ℂ → ℂ} {T : Carrier → Carrier}

theorem spectralDeterminant_zero_of_xi_zero
    (P : CompletedXiSpectralDeterminantPacket Xi T)
    {s : ℂ} (hXi : Xi s = 0) :
    P.spectralDeterminant s = 0 := by
  have hUnitDet : P.normalizingUnit s * P.spectralDeterminant s = 0 := by
    simpa [hXi] using (P.xi_eq_unit_mul_det s).symm
  exact Or.resolve_left (mul_eq_zero.mp hUnitDet) (P.normalizingUnit_nonzero s)

theorem xi_zero_of_spectralDeterminant_zero
    (P : CompletedXiSpectralDeterminantPacket Xi T)
    {s : ℂ} (hDet : P.spectralDeterminant s = 0) :
    Xi s = 0 := by
  rw [P.xi_eq_unit_mul_det s, hDet, mul_zero]

theorem xi_zero_iff_spectralDeterminant_zero
    (P : CompletedXiSpectralDeterminantPacket Xi T) (s : ℂ) :
    Xi s = 0 ↔ P.spectralDeterminant s = 0 :=
  ⟨P.spectralDeterminant_zero_of_xi_zero, P.xi_zero_of_spectralDeterminant_zero⟩

theorem spectralDeterminant_ne_zero_of_xi_ne_zero
    (P : CompletedXiSpectralDeterminantPacket Xi T)
    {s : ℂ} (hXi : Xi s ≠ 0) :
    P.spectralDeterminant s ≠ 0 := by
  intro hDet
  exact hXi (P.xi_zero_of_spectralDeterminant_zero hDet)

theorem xi_ne_zero_of_spectralDeterminant_ne_zero
    (P : CompletedXiSpectralDeterminantPacket Xi T)
    {s : ℂ} (hDet : P.spectralDeterminant s ≠ 0) :
    Xi s ≠ 0 := by
  intro hXi
  exact hDet (P.spectralDeterminant_zero_of_xi_zero hXi)

theorem xi_ne_zero_iff_spectralDeterminant_ne_zero
    (P : CompletedXiSpectralDeterminantPacket Xi T) (s : ℂ) :
    Xi s ≠ 0 ↔ P.spectralDeterminant s ≠ 0 :=
  ⟨P.spectralDeterminant_ne_zero_of_xi_ne_zero,
    P.xi_ne_zero_of_spectralDeterminant_ne_zero⟩

theorem eigen_of_xi_zero
    (P : CompletedXiSpectralDeterminantPacket Xi T)
    {s : ℂ} (hXi : Xi s = 0) :
    EigenvalueEquation T (hilbertPolyaEigenparameter s) :=
  P.determinant_zero_to_eigen s (P.spectralDeterminant_zero_of_xi_zero hXi)

theorem spectralDeterminant_ne_zero_of_not_eigen
    (P : CompletedXiSpectralDeterminantPacket Xi T)
    {s : ℂ}
    (hNoEigen : ¬ EigenvalueEquation T (hilbertPolyaEigenparameter s)) :
    P.spectralDeterminant s ≠ 0 := by
  intro hDet
  exact hNoEigen (P.determinant_zero_to_eigen s hDet)

theorem xi_ne_zero_of_not_eigen
    (P : CompletedXiSpectralDeterminantPacket Xi T)
    {s : ℂ}
    (hNoEigen : ¬ EigenvalueEquation T (hilbertPolyaEigenparameter s)) :
    Xi s ≠ 0 :=
  P.xi_ne_zero_of_spectralDeterminant_ne_zero
    (P.spectralDeterminant_ne_zero_of_not_eigen hNoEigen)

end CompletedXiSpectralDeterminantPacket

theorem completedXiSpectralDeterminant_of_packet
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (Xi : ℂ → ℂ) (T : Carrier → Carrier)
    (P : CompletedXiSpectralDeterminantPacket Xi T) :
    CompletedXiSpectralDeterminantLemma Xi T := by
  intro s hXi
  exact P.eigen_of_xi_zero hXi

def completedXiSpectralDeterminantPacket_of_finiteCharacteristicDeterminant
    {Carrier : Type*} [AddCommGroup Carrier] [Module ℂ Carrier]
    [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (Xi : ℂ → ℂ)
    (T : Module.End ℂ Carrier)
    (normalizingUnit : ℂ → ℂ)
    (normalizingUnit_nonzero : ∀ s : ℂ, normalizingUnit s ≠ 0)
    (xi_eq_unit_mul_finiteCharacteristicDeterminant :
      ∀ s : ℂ,
        Xi s =
          normalizingUnit s *
            finiteCharacteristicDeterminant T (hilbertPolyaEigenparameter s)) :
    CompletedXiSpectralDeterminantPacket Xi (fun x => T x) where
  spectralDeterminant s :=
    finiteCharacteristicDeterminant T (hilbertPolyaEigenparameter s)
  normalizingUnit := normalizingUnit
  normalizingUnit_nonzero := normalizingUnit_nonzero
  xi_eq_unit_mul_det := xi_eq_unit_mul_finiteCharacteristicDeterminant
  determinant_zero_to_eigen s hDet :=
    finiteCharacteristicDeterminant_zero_to_eigen T (hilbertPolyaEigenparameter s) hDet

theorem completedXiSpectralDeterminant_of_finiteCharacteristicDeterminant
    {Carrier : Type*} [AddCommGroup Carrier] [Module ℂ Carrier]
    [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (Xi : ℂ → ℂ)
    (T : Module.End ℂ Carrier)
    (normalizingUnit : ℂ → ℂ)
    (normalizingUnit_nonzero : ∀ s : ℂ, normalizingUnit s ≠ 0)
    (xi_eq_unit_mul_finiteCharacteristicDeterminant :
      ∀ s : ℂ,
        Xi s =
          normalizingUnit s *
            finiteCharacteristicDeterminant T (hilbertPolyaEigenparameter s)) :
    CompletedXiSpectralDeterminantLemma Xi (fun x => T x) :=
  completedXiSpectralDeterminant_of_packet Xi (fun x => T x)
    (completedXiSpectralDeterminantPacket_of_finiteCharacteristicDeterminant
      Xi T normalizingUnit normalizingUnit_nonzero
      xi_eq_unit_mul_finiteCharacteristicDeterminant)

def HilbertPolyaCriticalLineConclusion
    (Xi : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, Xi s = 0 → s.re = 1 / 2

def HilbertPolyaNoOffCriticalZerosConclusion
    (Xi : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, s.re ≠ 1 / 2 → Xi s ≠ 0

theorem criticalLine_of_hilbertSelfAdjoint_finiteCharacteristicDeterminant_zero
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier] [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (T : Carrier →L[ℂ] Carrier) (hSelf : IsSelfAdjoint T)
    {s : ℂ}
    (hDet :
      finiteCharacteristicDeterminant
        (T : Carrier →ₗ[ℂ] Carrier) (hilbertPolyaEigenparameter s) = 0) :
    s.re = 1 / 2 :=
  criticalLine_of_hilbertPolyaEigenparameter_real
    (finiteCharacteristicDeterminant_zero_to_real_of_hilbertSelfAdjoint
      T hSelf (hilbertPolyaEigenparameter s) hDet)

def FiniteCharacteristicDeterminantNoOffCriticalZeros
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier] [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (T : Carrier →L[ℂ] Carrier) : Prop :=
  ∀ s : ℂ, s.re ≠ 1 / 2 →
    finiteCharacteristicDeterminant
      (T : Carrier →ₗ[ℂ] Carrier) (hilbertPolyaEigenparameter s) ≠ 0

theorem noEigenvalue_hilbertPolyaEigenparameter_of_hilbertSelfAdjoint_offCritical
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier]
    (T : Carrier →L[ℂ] Carrier) (hSelf : IsSelfAdjoint T)
    {s : ℂ} (hOff : s.re ≠ 1 / 2) :
    ¬ EigenvalueEquation (fun x => T x) (hilbertPolyaEigenparameter s) := by
  intro hEigen
  have hReal : (hilbertPolyaEigenparameter s).im = 0 :=
    hilbertSelfAdjointRealSpectrum T hSelf (hilbertPolyaEigenparameter s) hEigen
  exact hOff (criticalLine_of_hilbertPolyaEigenparameter_real hReal)

theorem finiteCharacteristicDeterminant_ne_zero_of_hilbertSelfAdjoint_offCritical
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier] [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (T : Carrier →L[ℂ] Carrier) (hSelf : IsSelfAdjoint T)
    {s : ℂ} (hOff : s.re ≠ 1 / 2) :
    finiteCharacteristicDeterminant
      (T : Carrier →ₗ[ℂ] Carrier) (hilbertPolyaEigenparameter s) ≠ 0 :=
  (finiteCharacteristicDeterminant_ne_zero_iff_no_eigen
    (T : Carrier →ₗ[ℂ] Carrier) (hilbertPolyaEigenparameter s)).mpr
    (noEigenvalue_hilbertPolyaEigenparameter_of_hilbertSelfAdjoint_offCritical
      T hSelf hOff)

theorem finiteCharacteristicDeterminantNoOffCriticalZeros_of_hilbertSelfAdjoint
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier] [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (T : Carrier →L[ℂ] Carrier) (hSelf : IsSelfAdjoint T) :
    FiniteCharacteristicDeterminantNoOffCriticalZeros T := by
  intro s hOff
  exact finiteCharacteristicDeterminant_ne_zero_of_hilbertSelfAdjoint_offCritical
    T hSelf hOff

theorem hilbertPolyaNoOffCriticalZerosConclusion_of_criticalLine
    (Xi : ℂ → ℂ)
    (hCritical : HilbertPolyaCriticalLineConclusion Xi) :
    HilbertPolyaNoOffCriticalZerosConclusion Xi := by
  intro s hOff hXi
  exact hOff (hCritical s hXi)

theorem hilbertPolyaCriticalLineConclusion_of_lemmaSeries
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (Xi : ℂ → ℂ)
    (pairing : Carrier → Carrier → ℂ)
    (T : Carrier → Carrier)
    (hSymmetric : HestenesKreinSymmetricOperator pairing T)
    (hRealSpectrum : HestenesKreinRealSpectrumLemma pairing T)
    (hDeterminant : CompletedXiSpectralDeterminantLemma Xi T) :
    HilbertPolyaCriticalLineConclusion Xi := by
  intro s hzero
  have hEigen : EigenvalueEquation T (hilbertPolyaEigenparameter s) :=
    hDeterminant s hzero
  have hReal : (hilbertPolyaEigenparameter s).im = 0 :=
    hRealSpectrum hSymmetric (hilbertPolyaEigenparameter s) hEigen
  exact criticalLine_of_hilbertPolyaEigenparameter_real hReal

theorem hilbertPolyaNoOffCriticalZerosConclusion_of_lemmaSeries
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (Xi : ℂ → ℂ)
    (pairing : Carrier → Carrier → ℂ)
    (T : Carrier → Carrier)
    (hSymmetric : HestenesKreinSymmetricOperator pairing T)
    (hRealSpectrum : HestenesKreinRealSpectrumLemma pairing T)
    (hDeterminant : CompletedXiSpectralDeterminantLemma Xi T) :
    HilbertPolyaNoOffCriticalZerosConclusion Xi :=
  hilbertPolyaNoOffCriticalZerosConclusion_of_criticalLine Xi
    (hilbertPolyaCriticalLineConclusion_of_lemmaSeries
      Xi pairing T hSymmetric hRealSpectrum hDeterminant)

theorem hilbertPolyaCriticalLineConclusion_of_kreinDefinitizable_packet
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (Xi : ℂ → ℂ)
    (pairing : Carrier → Carrier → ℂ)
    (T : Carrier → Carrier)
    (K : KreinDefinitizableRealSpectrumPacket pairing T)
    (D : CompletedXiSpectralDeterminantPacket Xi T) :
    HilbertPolyaCriticalLineConclusion Xi :=
  hilbertPolyaCriticalLineConclusion_of_lemmaSeries
    Xi pairing T K.symmetric
    (kreinDefinitizableRealSpectrum_of_packet pairing T K)
    (completedXiSpectralDeterminant_of_packet Xi T D)

theorem hilbertPolyaNoOffCriticalZerosConclusion_of_kreinDefinitizable_packet
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (Xi : ℂ → ℂ)
    (pairing : Carrier → Carrier → ℂ)
    (T : Carrier → Carrier)
    (K : KreinDefinitizableRealSpectrumPacket pairing T)
    (D : CompletedXiSpectralDeterminantPacket Xi T) :
    HilbertPolyaNoOffCriticalZerosConclusion Xi :=
  hilbertPolyaNoOffCriticalZerosConclusion_of_criticalLine Xi
    (hilbertPolyaCriticalLineConclusion_of_kreinDefinitizable_packet Xi pairing T K D)

theorem xi_ne_zero_of_kreinDefinitizable_packet_offCritical
    {Carrier : Type*} [Zero Carrier] [SMul ℂ Carrier]
    (Xi : ℂ → ℂ)
    (pairing : Carrier → Carrier → ℂ)
    (T : Carrier → Carrier)
    (K : KreinDefinitizableRealSpectrumPacket pairing T)
    (D : CompletedXiSpectralDeterminantPacket Xi T)
    {s : ℂ} (hOff : s.re ≠ 1 / 2) :
    Xi s ≠ 0 :=
  (hilbertPolyaNoOffCriticalZerosConclusion_of_kreinDefinitizable_packet
    Xi pairing T K D) s hOff

theorem hilbertPolyaCriticalLineConclusion_of_hilbertSelfAdjoint
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier]
    (Xi : ℂ → ℂ)
    (T : Carrier →L[ℂ] Carrier)
    (hSelf : IsSelfAdjoint T)
    (hDeterminant : CompletedXiSpectralDeterminantLemma Xi (fun x => T x)) :
    HilbertPolyaCriticalLineConclusion Xi := by
  exact
    hilbertPolyaCriticalLineConclusion_of_lemmaSeries
      (Xi := Xi)
      (pairing := fun x y => inner ℂ x y)
      (T := fun x => T x)
      (by
        intro x y
        exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSelf) x y)
      (by
        intro _ lambda hEigen
        exact hilbertSelfAdjointRealSpectrum T hSelf lambda hEigen)
      hDeterminant

theorem hilbertPolyaNoOffCriticalZerosConclusion_of_hilbertSelfAdjoint
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier]
    (Xi : ℂ → ℂ)
    (T : Carrier →L[ℂ] Carrier)
    (hSelf : IsSelfAdjoint T)
    (hDeterminant : CompletedXiSpectralDeterminantLemma Xi (fun x => T x)) :
    HilbertPolyaNoOffCriticalZerosConclusion Xi :=
  hilbertPolyaNoOffCriticalZerosConclusion_of_criticalLine Xi
    (hilbertPolyaCriticalLineConclusion_of_hilbertSelfAdjoint Xi T hSelf hDeterminant)

theorem xi_ne_zero_of_hilbertSelfAdjoint_offCritical
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier]
    (Xi : ℂ → ℂ)
    (T : Carrier →L[ℂ] Carrier)
    (hSelf : IsSelfAdjoint T)
    (hDeterminant : CompletedXiSpectralDeterminantLemma Xi (fun x => T x))
    {s : ℂ} (hOff : s.re ≠ 1 / 2) :
    Xi s ≠ 0 :=
  (hilbertPolyaNoOffCriticalZerosConclusion_of_hilbertSelfAdjoint
    Xi T hSelf hDeterminant) s hOff

theorem hilbertPolyaCriticalLineConclusion_of_hilbertSelfAdjoint_packet
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier]
    (Xi : ℂ → ℂ)
    (T : Carrier →L[ℂ] Carrier)
    (hSelf : IsSelfAdjoint T)
    (P : CompletedXiSpectralDeterminantPacket Xi (fun x => T x)) :
    HilbertPolyaCriticalLineConclusion Xi :=
  hilbertPolyaCriticalLineConclusion_of_hilbertSelfAdjoint
    Xi T hSelf (completedXiSpectralDeterminant_of_packet Xi (fun x => T x) P)

theorem hilbertPolyaNoOffCriticalZerosConclusion_of_hilbertSelfAdjoint_packet
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier]
    (Xi : ℂ → ℂ)
    (T : Carrier →L[ℂ] Carrier)
    (hSelf : IsSelfAdjoint T)
    (P : CompletedXiSpectralDeterminantPacket Xi (fun x => T x)) :
    HilbertPolyaNoOffCriticalZerosConclusion Xi :=
  hilbertPolyaNoOffCriticalZerosConclusion_of_criticalLine Xi
    (hilbertPolyaCriticalLineConclusion_of_hilbertSelfAdjoint_packet Xi T hSelf P)

theorem xi_ne_zero_of_hilbertSelfAdjoint_packet_offCritical
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier]
    (Xi : ℂ → ℂ)
    (T : Carrier →L[ℂ] Carrier)
    (hSelf : IsSelfAdjoint T)
    (P : CompletedXiSpectralDeterminantPacket Xi (fun x => T x))
    {s : ℂ} (hOff : s.re ≠ 1 / 2) :
    Xi s ≠ 0 :=
  (hilbertPolyaNoOffCriticalZerosConclusion_of_hilbertSelfAdjoint_packet
    Xi T hSelf P) s hOff

theorem hilbertPolyaCriticalLineConclusion_of_hilbertSelfAdjoint_finiteCharacteristicDeterminant
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier] [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (Xi : ℂ → ℂ)
    (T : Carrier →L[ℂ] Carrier)
    (hSelf : IsSelfAdjoint T)
    (normalizingUnit : ℂ → ℂ)
    (normalizingUnit_nonzero : ∀ s : ℂ, normalizingUnit s ≠ 0)
    (xi_eq_unit_mul_finiteCharacteristicDeterminant :
      ∀ s : ℂ,
        Xi s =
          normalizingUnit s *
            finiteCharacteristicDeterminant
              (T : Carrier →ₗ[ℂ] Carrier) (hilbertPolyaEigenparameter s)) :
    HilbertPolyaCriticalLineConclusion Xi :=
  hilbertPolyaCriticalLineConclusion_of_hilbertSelfAdjoint
    Xi T hSelf
    (completedXiSpectralDeterminant_of_finiteCharacteristicDeterminant
      Xi (T : Carrier →ₗ[ℂ] Carrier)
      normalizingUnit normalizingUnit_nonzero
      xi_eq_unit_mul_finiteCharacteristicDeterminant)

theorem hilbertPolyaNoOffCriticalZerosConclusion_of_hilbertSelfAdjoint_finiteCharacteristicDeterminant
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier] [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (Xi : ℂ → ℂ)
    (T : Carrier →L[ℂ] Carrier)
    (hSelf : IsSelfAdjoint T)
    (normalizingUnit : ℂ → ℂ)
    (normalizingUnit_nonzero : ∀ s : ℂ, normalizingUnit s ≠ 0)
    (xi_eq_unit_mul_finiteCharacteristicDeterminant :
      ∀ s : ℂ,
        Xi s =
          normalizingUnit s *
            finiteCharacteristicDeterminant
              (T : Carrier →ₗ[ℂ] Carrier) (hilbertPolyaEigenparameter s)) :
    HilbertPolyaNoOffCriticalZerosConclusion Xi :=
  hilbertPolyaNoOffCriticalZerosConclusion_of_criticalLine Xi
    (hilbertPolyaCriticalLineConclusion_of_hilbertSelfAdjoint_finiteCharacteristicDeterminant
      Xi T hSelf normalizingUnit normalizingUnit_nonzero
      xi_eq_unit_mul_finiteCharacteristicDeterminant)

theorem xi_ne_zero_of_hilbertSelfAdjoint_finiteCharacteristicDeterminant_offCritical
    {Carrier : Type*} [NormedAddCommGroup Carrier] [InnerProductSpace ℂ Carrier]
    [CompleteSpace Carrier] [Module.Free ℂ Carrier] [Module.Finite ℂ Carrier]
    (Xi : ℂ → ℂ)
    (T : Carrier →L[ℂ] Carrier)
    (hSelf : IsSelfAdjoint T)
    (normalizingUnit : ℂ → ℂ)
    (normalizingUnit_nonzero : ∀ s : ℂ, normalizingUnit s ≠ 0)
    (xi_eq_unit_mul_finiteCharacteristicDeterminant :
      ∀ s : ℂ,
        Xi s =
          normalizingUnit s *
            finiteCharacteristicDeterminant
              (T : Carrier →ₗ[ℂ] Carrier) (hilbertPolyaEigenparameter s))
    {s : ℂ} (hOff : s.re ≠ 1 / 2) :
    Xi s ≠ 0 :=
  (hilbertPolyaNoOffCriticalZerosConclusion_of_hilbertSelfAdjoint_finiteCharacteristicDeterminant
    Xi T hSelf normalizingUnit normalizingUnit_nonzero
    xi_eq_unit_mul_finiteCharacteristicDeterminant) s hOff

end HilbertPolyaLemmaSeries

end LatticeHilbertPolyaPipeline
