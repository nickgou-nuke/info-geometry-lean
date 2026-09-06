import proofs.GellMannParafermionSolder
import proofs.WeylSU3ColorSymmetry

/-!
# Weyl-transported SU(3) commutators on soldered parafermion lanes

This module welds the structural `S₃` Weyl transport layer to the explicit
Gell-Mann → parafermion soldering map.

A seed matrix commutator identity

`A * B - B * A = c • C`

is transported by Weyl conjugation and then represented on the realized
parafermion `3+1` color spinor.  Thus transported SU(3) commutator identities
remain valid on the soldered parafermion color lanes without reproving the full
Gell-Mann table at the parafermion level.
-/

noncomputable section

namespace WeylSolderedParafermionSymmetry

open GellMannParafermionSolder
open WeylSU3ColorSymmetry
open BogoliubovSU3ParafermionProofChain
open GellMannSU3

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ

/-- Weyl-transported commutator identities act correctly on the soldered
parafermion spinor.  This is the direct weld:

`WeylSU3ColorSymmetry.weyl_transport_to_colorAction`
+
`GellMannParafermionSolder.gellMannParafermionSolder`. -/
theorem weyl_soldered_parafermion_transport
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V)
    (σ : Equiv.Perm (Fin 3)) (A B C : M3C) (c : ℂ)
    (h : A * B - B * A = c • C)
    (h_sq : WeylSU3ColorSymmetry.permMatrix σ * WeylSU3ColorSymmetry.permMatrix σ = 1) :
    colorLieAction4 (WeylSU3ColorSymmetry.weylAct σ A)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct σ B)) -
      colorLieAction4 (WeylSU3ColorSymmetry.weylAct σ B)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct σ A)) =
        c • gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct σ C) := by
  exact WeylSU3ColorSymmetry.weyl_transport_to_colorAction σ A B C c h h_sq
    (GellMannParafermionSolder.realizedParafermionColorSpinor4 R)

/-- Specialization to the first Weyl generator `swap12`. -/
theorem swap12_soldered_parafermion_transport
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) (A B C : M3C) (c : ℂ)
    (h : A * B - B * A = c • C) :
    colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 A)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 B)) -
      colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 B)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 A)) =
        c • gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 C) := by
  exact weyl_soldered_parafermion_transport R WeylSU3ColorSymmetry.swap12 A B C c h
    WeylSU3ColorSymmetry.permMatrix_swap12_sq

/-- Specialization to the second Weyl generator `swap23`. -/
theorem swap23_soldered_parafermion_transport
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) (A B C : M3C) (c : ℂ)
    (h : A * B - B * A = c • C) :
    colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 A)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 B)) -
      colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 B)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 A)) =
        c • gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 C) := by
  exact weyl_soldered_parafermion_transport R WeylSU3ColorSymmetry.swap23 A B C c h
    WeylSU3ColorSymmetry.permMatrix_swap23_sq

/-- Concrete transported seed: the `swap12` Weyl image of
`[λ₁,λ₂]=2iλ₃` acts correctly on the soldered parafermion color lanes. -/
theorem swap12_soldered_gl1_gl2
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) :
    colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 gl1)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 gl2)) -
      colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 gl2)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 gl1)) =
        (2 * Complex.I) • gellMannParafermionSolder R
          (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 gl3) := by
  exact swap12_soldered_parafermion_transport R gl1 gl2 gl3 (2 * Complex.I) gl1_comm_gl2

/-- Concrete transported seed: the `swap23` Weyl image of
`[λ₁,λ₂]=2iλ₃` acts correctly on the soldered parafermion color lanes. -/
theorem swap23_soldered_gl1_gl2
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) :
    colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 gl1)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 gl2)) -
      colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 gl2)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 gl1)) =
        (2 * Complex.I) • gellMannParafermionSolder R
          (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 gl3) := by
  exact swap23_soldered_parafermion_transport R gl1 gl2 gl3 (2 * Complex.I) gl1_comm_gl2

/-- Synthesis: both Weyl generators transport a seed SU(3) commutator identity
through the explicit Gell-Mann-to-parafermion soldering map. -/
theorem weyl_soldered_parafermion_symmetry_synthesis
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) (A B C : M3C) (c : ℂ)
    (h : A * B - B * A = c • C) :
    colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 A)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 B)) -
      colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 B)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 A)) =
        c • gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap12 C) ∧
    colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 A)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 B)) -
      colorLieAction4 (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 B)
        (gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 A)) =
        c • gellMannParafermionSolder R (WeylSU3ColorSymmetry.weylAct WeylSU3ColorSymmetry.swap23 C) := by
  exact ⟨swap12_soldered_parafermion_transport R A B C c h,
    swap23_soldered_parafermion_transport R A B C c h⟩

end WeylSolderedParafermionSymmetry

end noncomputable section
