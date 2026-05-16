import Mathlib.LinearAlgebra.JordanChevalley

/-!
# InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanChevalleyBridge

Module-theoretic Jordan-Chevalley façade for the existing Jordan-normal-form
surface.

This file does not reprove the full theorem stack. It packages the mathlib
Jordan-Chevalley decomposition in the native `Module.End` language and exposes
the commuting readout coming from the singleton `adjoin` witness. A local
matrix-facing endomorphism readout is included for the standard complex
coordinate carrier.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanChevalleyBridge

open Algebra Polynomial

section Core

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Nilpotent endomorphisms in the Jordan-Chevalley corridor. -/
def IsNilpotentEnd (f : Module.End K V) : Prop :=
  IsNilpotent f

/-- Semisimple endomorphisms in the Jordan-Chevalley corridor. -/
def IsSemisimpleEnd (f : Module.End K V) : Prop :=
  f.IsSemisimple

/-- Polynomial evaluation at an endomorphism commutes with every endomorphism commuting with the
original endomorphism. -/
theorem commute_aeval {f g : Module.End K V} (hfg : Commute f g) (p : K[X]) :
    Commute (Polynomial.aeval f p) g := by
  induction p using Polynomial.induction_on with
  | C a =>
      simpa [Polynomial.aeval_C] using (Algebra.commute_algebraMap_left a g)
  | add p q hp hq =>
      simpa [Polynomial.aeval_add] using hp.add_left hq
  | monomial n a hp =>
      simpa [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, mul_assoc] using
        (Commute.mul_left (Algebra.commute_algebraMap_left a g) (hfg.pow_left (n + 1)))

/-- Any element of the singleton-generated algebra `adjoin K {f}` commutes with every operator
that commutes with `f`. -/
theorem commute_of_mem_adjoin_singleton {f g : Module.End K V} (hfg : Commute f g)
    {a : Module.End K V} (ha : a ∈ Algebra.adjoin K {f}) :
    Commute a g := by
  rcases Algebra.adjoin_mem_exists_aeval (R := K) (x := f) ha with ⟨p, hp⟩
  rw [← hp]
  exact commute_aeval (f := f) (g := g) hfg p

/-- A packaged Jordan-Chevalley splitting. -/
structure JordanChevalleySplit (f : Module.End K V) where
  semisimple : Module.End K V
  nilpotent : Module.End K V
  commute : Commute semisimple nilpotent
  semisimpleMem : semisimple ∈ Algebra.adjoin K {f}
  nilpotentMem : nilpotent ∈ Algebra.adjoin K {f}
  sum_eq : f = semisimple + nilpotent
  semisimpleLaw : IsSemisimpleEnd semisimple
  nilpotentLaw : IsNilpotentEnd nilpotent

namespace JordanChevalleySplit

variable (f : Module.End K V)

/-- The native Jordan-Chevalley theorem yields a packaged split. -/
theorem split_exists [PerfectField K] : Nonempty (JordanChevalleySplit (f := f)) := by
  rcases Module.End.exists_isNilpotent_isSemisimple (f := f) with
    ⟨n, hn, s, hs, hnil, hss, hsum⟩
  have hscomm_f : Commute f s :=
    Algebra.commute_of_mem_adjoin_self (R := K) (a := f) (b := s) hs
  have hscomm_n : Commute s n :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute
      (R := K) (a := s) (b := n) (s := ({f} : Set (Module.End K V))) hn
      (by
        intro b hb
        have hb' : b = f := by
          simpa [Set.mem_singleton_iff] using hb
        subst hb'
        exact hscomm_f.symm)
  refine ⟨{ semisimple := s
          , nilpotent := n
          , commute := hscomm_n
          , semisimpleMem := hs
          , nilpotentMem := hn
          , sum_eq := ?_
          , semisimpleLaw := hss
          , nilpotentLaw := hnil }⟩
  simpa [add_comm] using hsum

/-- Readback: the nilpotent part is nilpotent. -/
theorem nilpotentLaw_readback [PerfectField K] :
    Nonempty (JordanChevalleySplit (f := f)) →
      ∃ B : JordanChevalleySplit (f := f), IsNilpotentEnd B.nilpotent := by
  intro h
  rcases h with ⟨B⟩
  exact ⟨B, B.nilpotentLaw⟩

/-- Readback: the semisimple part is semisimple. -/
theorem semisimpleLaw_readback [PerfectField K] :
    Nonempty (JordanChevalleySplit (f := f)) →
      ∃ B : JordanChevalleySplit (f := f), IsSemisimpleEnd B.semisimple := by
  intro h
  rcases h with ⟨B⟩
  exact ⟨B, B.semisimpleLaw⟩

/-- Readback: the split components commute. -/
theorem commute_readback [PerfectField K] :
    Nonempty (JordanChevalleySplit (f := f)) →
      ∃ B : JordanChevalleySplit (f := f), Commute B.semisimple B.nilpotent := by
  intro h
  rcases h with ⟨B⟩
  exact ⟨B, B.commute⟩

/-- Readback: the semisimple and nilpotent parts commute with any symmetry commuting with `f`. -/
theorem parts_commute_with_of_commute [PerfectField K] {g : Module.End K V} (hfg : Commute f g)
    (B : JordanChevalleySplit (f := f)) :
    Commute B.semisimple g ∧ Commute B.nilpotent g := by
  constructor
  · exact commute_of_mem_adjoin_singleton (f := f) (g := g) hfg B.semisimpleMem
  · exact commute_of_mem_adjoin_singleton (f := f) (g := g) hfg B.nilpotentMem

end JordanChevalleySplit

/-- The matrix endomorphism associated to a square matrix on the standard basis. -/
def matrixEnd {n : Nat} (A : Matrix (Fin n) (Fin n) K) : Module.End K (Fin n → K) :=
  Matrix.toLin (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) A

/--
Matrix-side Jordan-Chevalley witness on the standard complex carrier.
-/
theorem matrixEnd_jordanChevalleySplit [PerfectField K] {n : Nat} (A : Matrix (Fin n) (Fin n) K) :
    Nonempty (JordanChevalleySplit (f := matrixEnd A)) := by
  exact JordanChevalleySplit.split_exists (f := matrixEnd A)

end Core

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanChevalleyBridge
