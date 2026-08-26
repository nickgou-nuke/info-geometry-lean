import InfoGeometry.Canonical.BoundaryBraidRepresentation
import InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction
import InfoGeometry.Physics.Algebra.FibonacciHorizonBraidBridge

/-!
# The finite intertwiner problem for the two braid carriers

The repository has two honest `B₃` actions: the eight-dimensional Jones--
Temperley--Lieb boundary action and the two-dimensional Fibonacci action on the
tripotent horizon carrier.  This file records their actual intertwiner space.

No nonzero intertwiner is assumed here.  The kernel below is the finite linear
system whose nontriviality is the remaining representation-theoretic question.
In particular, this owner does not identify the two carriers merely because
both satisfy the Artin relation.
-/

noncomputable section

namespace InfoGeometry.Canonical.BoundaryFibonacciHorizonIntertwiner

open InfoGeometry.Canonical.BoundaryBraidRepresentation
open InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction
open InfoGeometry.Physics.Algebra.FibonacciHorizonBraidBridge
open InfoGeometry.Physics.B3PresentedGroup

def boundarySig0 : Module.End ℂ BoundaryBraidState :=
  (boundaryBraidLinearRepresentation
    (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) :
      BoundaryBraidState →ₗ[ℂ] BoundaryBraidState)

def boundarySig1 : Module.End ℂ BoundaryBraidState :=
  (boundaryBraidLinearRepresentation
    (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) :
      BoundaryBraidState →ₗ[ℂ] BoundaryBraidState)

/-- The pair of generator defects of a candidate boundary-to-horizon map. -/
def intertwinerDefect (Φ : BoundaryBraidState →ₗ[ℂ] HorizonSpace) :
    (BoundaryBraidState →ₗ[ℂ] HorizonSpace) ×
      (BoundaryBraidState →ₗ[ℂ] HorizonSpace) :=
  (Φ.comp boundarySig0 - horizonLinR.comp Φ,
    Φ.comp boundarySig1 - horizonLinB.comp Φ)

/-- The simultaneous linear system defining `B₃`-intertwiners. -/
def boundaryFibonacciIntertwinerOperator :
    (BoundaryBraidState →ₗ[ℂ] HorizonSpace) →ₗ[ℂ]
      ((BoundaryBraidState →ₗ[ℂ] HorizonSpace) ×
        (BoundaryBraidState →ₗ[ℂ] HorizonSpace)) where
  toFun := intertwinerDefect
  map_add' Φ Ψ := by
    apply Prod.ext
    · apply LinearMap.ext
      intro v
      change ((Φ + Ψ).comp boundarySig0 - horizonLinR.comp (Φ + Ψ)) v =
        ((Φ.comp boundarySig0 - horizonLinR.comp Φ) +
          (Ψ.comp boundarySig0 - horizonLinR.comp Ψ)) v
      simp only [LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.comp_apply, map_add]
      module
    · apply LinearMap.ext
      intro v
      change ((Φ + Ψ).comp boundarySig1 - horizonLinB.comp (Φ + Ψ)) v =
        ((Φ.comp boundarySig1 - horizonLinB.comp Φ) +
          (Ψ.comp boundarySig1 - horizonLinB.comp Ψ)) v
      simp only [LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.comp_apply, map_add]
      module
  map_smul' c Φ := by
    change intertwinerDefect (c • Φ) = c • intertwinerDefect Φ
    apply Prod.ext
    · apply LinearMap.ext
      intro v
      change ((c • Φ).comp boundarySig0 - horizonLinR.comp (c • Φ)) v =
        c • ((Φ.comp boundarySig0 - horizonLinR.comp Φ) v)
      simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, map_smul, smul_sub]
    · apply LinearMap.ext
      intro v
      change ((c • Φ).comp boundarySig1 - horizonLinB.comp (c • Φ)) v =
        c • ((Φ.comp boundarySig1 - horizonLinB.comp Φ) v)
      simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, map_smul, smul_sub]

/-- The exact finite-dimensional intertwiner space for the two generator actions. -/
def boundaryFibonacciIntertwinerSpace :
    Submodule ℂ (BoundaryBraidState →ₗ[ℂ] HorizonSpace) :=
  LinearMap.ker boundaryFibonacciIntertwinerOperator

theorem mem_boundaryFibonacciIntertwinerSpace_iff
    (Φ : BoundaryBraidState →ₗ[ℂ] HorizonSpace) :
    Φ ∈ boundaryFibonacciIntertwinerSpace ↔
      Φ.comp boundarySig0 = horizonLinR.comp Φ ∧
      Φ.comp boundarySig1 = horizonLinB.comp Φ := by
  constructor
  · intro h
    have hzero := h
    change boundaryFibonacciIntertwinerOperator Φ = 0 at hzero
    have h0 := congrArg Prod.fst hzero
    have h1 := congrArg Prod.snd hzero
    exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩
  · rintro ⟨h0, h1⟩
    change boundaryFibonacciIntertwinerOperator Φ = 0
    apply Prod.ext
    · exact sub_eq_zero.mpr h0
    · exact sub_eq_zero.mpr h1

theorem boundaryFibonacciIntertwinerSpace_eq_bot_iff :
    boundaryFibonacciIntertwinerSpace = ⊥ ↔
      ∀ Φ : BoundaryBraidState →ₗ[ℂ] HorizonSpace,
        Φ.comp boundarySig0 = horizonLinR.comp Φ ∧
        Φ.comp boundarySig1 = horizonLinB.comp Φ →
        Φ = 0 := by
  constructor
  · intro h Φ hΦ
    have hmem : Φ ∈ boundaryFibonacciIntertwinerSpace :=
      (mem_boundaryFibonacciIntertwinerSpace_iff Φ).mpr hΦ
    have hzero : Φ ∈ (⊥ : Submodule ℂ
        (BoundaryBraidState →ₗ[ℂ] HorizonSpace)) := h ▸ hmem
    simpa using hzero
  · intro h
    apply le_antisymm
    · intro Φ hΦ
      have hzero := h Φ ((mem_boundaryFibonacciIntertwinerSpace_iff Φ).mp hΦ)
      simpa [hzero]
    · exact bot_le

/-! The matrix obstruction transports to the native linear-map carrier. -/

theorem boundarySig0_eq_toLin :
    boundarySig0 = Matrix.toLin'
      (_root_.InfoGeometry.Physics.JonesBraidB3.s0) := by
  change Matrix.toLinAlgEquiv'
      (boundaryBraidRepresentation
        (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup)) =
    Matrix.toLin'
      (_root_.InfoGeometry.Physics.JonesBraidB3.s0)
  rw [boundaryBraidRepresentation_first_generator]
  apply LinearMap.ext
  intro x
  rfl

theorem horizonLinR_eq_toLin :
    horizonLinR = Matrix.toLin'
      InfoGeometry.Canonical.YangBaxterProof.R := by
  rfl

theorem boundaryFibonacciIntertwinerSpace_eq_bot :
    boundaryFibonacciIntertwinerSpace = ⊥ := by
  apply le_antisymm
  · intro Φ hΦ
    have hgen := (mem_boundaryFibonacciIntertwinerSpace_iff Φ).mp hΦ |>.1
    let M : Matrix (Fin 2) (Fin 8) ℂ := (Matrix.toLin').symm Φ
    have hM : Matrix.toLin' M = Φ := by
      dsimp [M]
      exact (Matrix.toLin').apply_symm_apply Φ
    have hmat : M * _root_.InfoGeometry.Physics.JonesBraidB3.s0 =
        InfoGeometry.Canonical.YangBaxterProof.R * M := by
      apply (Matrix.toLin').injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
      rw [hM]
      have hgen' := hgen
      rw [boundarySig0_eq_toLin, horizonLinR_eq_toLin] at hgen'
      exact hgen'
    have hzero : M = 0 :=
      direct_intertwiner_eq_zero M hmat
    rw [← hM, hzero]
    simpa using
      (Submodule.zero_mem
        (⊥ : Submodule ℂ (BoundaryBraidState →ₗ[ℂ] HorizonSpace)))
  · exact bot_le

theorem boundaryFibonacciIntertwinerSpace_finrank_eq_zero :
    Module.finrank ℂ boundaryFibonacciIntertwinerSpace = 0 := by
  rw [boundaryFibonacciIntertwinerSpace_eq_bot, finrank_bot]

/-- Genuine negative Hom theorem for the two finite `B₃` representations.

The native linear-map Hom-space is zero: every map intertwining both Artin
generators is the zero map.  This is the representation-level readout of the
spectral obstruction, not an identification of the two carriers.
-/
theorem boundaryFibonacciIntertwiner_eq_zero
    (Φ : BoundaryBraidState →ₗ[ℂ] HorizonSpace)
    (hΦ : Φ ∈ boundaryFibonacciIntertwinerSpace) :
    Φ = 0 := by
  have hbot : Φ ∈ (⊥ : Submodule ℂ
      (BoundaryBraidState →ₗ[ℂ] HorizonSpace)) := by
    rw [← boundaryFibonacciIntertwinerSpace_eq_bot]
    exact hΦ
  simpa using hbot

/-- Every simultaneous generator intertwiner is zero. -/
theorem boundaryFibonacciIntertwiner_eq_zero_of_generators
    (Φ : BoundaryBraidState →ₗ[ℂ] HorizonSpace)
    (h0 : Φ.comp boundarySig0 = horizonLinR.comp Φ)
    (h1 : Φ.comp boundarySig1 = horizonLinB.comp Φ) :
    Φ = 0 := by
  apply boundaryFibonacciIntertwiner_eq_zero Φ
  exact (mem_boundaryFibonacciIntertwinerSpace_iff Φ).2 ⟨h0, h1⟩

end InfoGeometry.Canonical.BoundaryFibonacciHorizonIntertwiner
