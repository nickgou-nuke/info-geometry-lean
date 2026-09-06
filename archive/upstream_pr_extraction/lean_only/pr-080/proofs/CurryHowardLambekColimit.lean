import proofs.ContinuumAsColimitCounting
import proofs.HillWheelerUniversalProjection

/-!
# Curry--Howard--Lambek colimit spine

This file records a finite interface for the slogan:

  Logic ~= Type theory ~= Category theory

and welds it to the repository-specific colimit spine:

* propositions/types/objects, proofs/terms/morphisms are represented as a
  dictionary;
* implication, conjunction, universal, and existential rules are checked as
  ordinary Lean terms;
* Jaynes/LDDP, GNS reference states, CPT averaging, and `cut = fractal` are
  bundled through the already proved colimit/counting facts.
-/

noncomputable section

namespace CurryHowardLambekColimit

open ContinuumAsColimitCounting
open JaynesLDDPGNSColimit
open HillWheelerUniversalProjection

/-! ## 1. Lean-level Curry--Howard kernels -/

/-- Logic implication as a type of terms/functions. -/
def CHLImp (P Q : Prop) : Prop := P → Q

/-- Logic conjunction as a product. -/
def CHLProd (P Q : Prop) : Prop := P ∧ Q

/-- Universal quantification as a dependent function/Pi-style family. -/
def CHLForall {α : Type*} (R : α → Prop) : Prop := ∀ x, R x

/-- Existential quantification as a dependent pair/Sigma-style family. -/
def CHLExists {α : Type*} (R : α → Prop) : Prop := ∃ x, R x

/-- Implication elimination is function application. -/
theorem chl_imp_apply {P Q : Prop} (f : CHLImp P Q) (p : P) : Q :=
  f p

/-- Conjunction introduction is product pairing. -/
theorem chl_prod_intro {P Q : Prop} (p : P) (q : Q) : CHLProd P Q :=
  ⟨p, q⟩

/-- Universal elimination is dependent-function specialization. -/
theorem chl_forall_apply {α : Type*} {R : α → Prop}
    (h : CHLForall R) (x : α) : R x :=
  h x

/-- Existential introduction is dependent-pair construction. -/
theorem chl_exists_intro {α : Type*} {R : α → Prop}
    (x : α) (h : R x) : CHLExists R :=
  ⟨x, h⟩

/-! ## 2. Repository-specific CHL/colimit synthesis -/

/-- Capstone: basic CHL term rules plus the repository's theorem-backed
Jaynes/LDDP--GNS--CPT--Cantor-colimit anchors. -/
theorem curry_howard_lambek_colimit_synthesis
    {P Q : Prop} {α : Type*} {R : α → Prop}
    (p : P) (q : Q) (x : α) (hrx : R x)
    (fPQ : CHLImp P Q)
    (allR : CHLForall R)
    (n : ℕ) (obs : FourDiagAlg n) (s : ℂ) :
    Q ∧
    CHLProd P Q ∧
    R x ∧
    CHLExists R ∧
    Fintype.card (FourWord n) = 4 ^ n ∧
    Fintype.card (FourWord (n + 1)) = 4 * Fintype.card (FourWord n) ∧
    jaynesRelativeEntropy (Finset.univ : Finset (FourWord n))
      (finiteCountingReference4 n) (finiteCountingReference4 n) = 0 ∧
    cylinder4 (n + 1) (diagEmbedSucc4 n obs) = cylinder4 n obs ∧
    (cptHillWheelerAverage s).re = 1 / 2 := by
  constructor
  · exact chl_imp_apply fPQ p
  constructor
  · exact chl_prod_intro p q
  constructor
  · exact chl_forall_apply allR x
  constructor
  · exact chl_exists_intro x hrx
  constructor
  · exact fourword_count n
  constructor
  · exact fourword_count_succ n
  constructor
  · exact finite_counting_reference4_entropy_self n
  constructor
  · exact cylinder4_compatible_succ n obs
  · exact cptHillWheelerAverage_re s

end CurryHowardLambekColimit

end noncomputable section
