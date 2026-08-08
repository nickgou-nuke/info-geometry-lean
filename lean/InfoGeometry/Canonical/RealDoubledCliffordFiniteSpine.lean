import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine

Projection surface for the finite real doubled Clifford spine.

This file introduces no new ontology and no property gates.  It only re-exports
the already-owned finite theorem data:

* `DoubledSpace` with `J`, `ε`, and `K = Jε`;
* the real split `Cl(1,1) ≃ M₂(ℝ)` matrix model;
* the recursive real split `Cl(n,n)` tower;
* the one-step split Bott factorization.

Infinite CAR/UHF limits, GNS closure, Fredholm stabilization, and RH-facing
operator limits remain outside this finite spine.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine

open scoped TensorProduct
open InfoGeometry.Krein
open InfoGeometry.Clifford

section Doubled

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The finite real doubled carrier, projected from `Krein.DoubledSpace`. -/
@[rep_depth krein]
abbrev Carrier := DoubledSpace E

/-- Hestenes/Tomita reflection `J`, projected from `Krein.DoubledSpace`. -/
@[rep_depth krein]
noncomputable abbrev J : Carrier (E := E) →L[ℝ] Carrier (E := E) :=
  modular_j (E := E)

/-- Fundamental sign involution `ε`, projected from `Krein.DoubledSpace`. -/
@[rep_depth krein]
noncomputable abbrev epsilon : Carrier (E := E) →L[ℝ] Carrier (E := E) :=
  spectral_epsilon (E := E)

/-- Real Hestenes phase axis `K = Jε`, projected from `Krein.DoubledSpace`. -/
@[rep_depth krein]
noncomputable abbrev K : Carrier (E := E) →L[ℝ] Carrier (E := E) :=
  complex_i (E := E)

/-- Compatibility alias for the clock-axis name. -/
@[rep_depth krein]
noncomputable abbrev clock : Carrier (E := E) →L[ℝ] Carrier (E := E) :=
  clockAxis (E := E)

/-- `J² = 1` on the doubled real carrier. -/
@[rep_depth krein]
theorem J_sq :
    (J (E := E)).comp (J (E := E)) =
      ContinuousLinearMap.id ℝ (Carrier (E := E)) :=
  modular_j_involution E

/-- `ε² = 1` on the doubled real carrier. -/
@[rep_depth krein]
theorem epsilon_sq :
    (epsilon (E := E)).comp (epsilon (E := E)) =
      ContinuousLinearMap.id ℝ (Carrier (E := E)) :=
  spectral_epsilon_involution E

/-- `Jε = -εJ` on the doubled real carrier. -/
@[rep_depth krein]
theorem J_epsilon_anticommute :
    (J (E := E)).comp (epsilon (E := E)) =
      -((epsilon (E := E)).comp (J (E := E))) :=
  modular_j_spectral_epsilon_anticommute E

/-- The real Hestenes axis is exactly `K = Jε`. -/
@[rep_depth krein]
theorem K_eq_J_comp_epsilon :
    K (E := E) = (J (E := E)).comp (epsilon (E := E)) :=
  rfl

/-- `K² = -1` on the doubled real carrier. -/
@[rep_depth krein]
theorem K_sq :
    (K (E := E)).comp (K (E := E)) =
      -(ContinuousLinearMap.id ℝ (Carrier (E := E))) :=
  complex_i_sq E

/-- The clock axis is the Hestenes phase axis. -/
@[rep_depth krein]
theorem clock_eq_K :
    clock (E := E) = K (E := E) :=
  rfl

/-- The clock axis squares to `-1`. -/
@[rep_depth krein]
theorem clock_sq :
    (clock (E := E)).comp (clock (E := E)) =
      -(ContinuousLinearMap.id ℝ (Carrier (E := E))) :=
  clockAxis_sq E

/-- The doubled-space `J,ε` pair satisfies the split `Cl(1,1)` relations. -/
@[rep_depth krein]
theorem doubled_cl11_relations :
    cl11_relations (J (E := E)) (epsilon (E := E)) :=
  modular_j_spectral_epsilon_has_cl11_relations E

end Doubled

/-- Split `(1,1)` vector carrier used by the matrix model. -/
@[rep_depth krein]
abbrev Cl11Vec := Cl11Matrix.Vec11

/-- Real `2 × 2` matrix carrier. -/
@[rep_depth krein]
abbrev Mat2R := Cl11Matrix.Mat2

/-- Split quadratic form for `Cl(1,1)`. -/
@[rep_depth krein]
noncomputable abbrev q11 := Cl11Matrix.q11

/-- Real matrix model `Cl(1,1) ≃ M₂(ℝ)`, projected from `Cl11Matrix`. -/
@[rep_depth krein]
noncomputable abbrev cl11EquivMat :
    CliffordAlgebra q11 ≃ₐ[ℝ] Mat2R :=
  Cl11Matrix.cl11EquivMat

/-- The real matrix model is exactly the owner equivalence. -/
@[rep_depth krein]
theorem cl11EquivMat_eq_owner :
    cl11EquivMat = Cl11Matrix.cl11EquivMat :=
  rfl

/-- Split `Cl(n,n)` carrier, projected from `Clifford.ClNN`. -/
@[rep_depth krein]
abbrev SplitCarrier (n : ℕ) := ClNN.Carrier n

/-- Split `Cl(n,n)` quadratic form, projected from `Clifford.ClNN`. -/
@[rep_depth krein]
noncomputable abbrev SplitQuad (n : ℕ) := ClNN.Quad n

/-- Split `Cl(n,n)` algebra, projected from `Clifford.ClNN`. -/
@[rep_depth krein]
abbrev SplitClifford (n : ℕ) := ClNN.Alg n

/-- Head null mode `u_-` in the recursive split tower. -/
@[rep_depth krein]
noncomputable abbrev headNullMinus (n : ℕ) :=
  ClNN.headNullMinus n

/-- Head null mode `u_+` in the recursive split tower. -/
@[rep_depth krein]
noncomputable abbrev headNullPlus (n : ℕ) :=
  ClNN.headNullPlus n

/-- The `u_-` head mode is isotropic. -/
@[rep_depth krein]
theorem headNullMinus_isotropic (n : ℕ) :
    SplitQuad (n + 1) (headNullMinus n) = 0 :=
  ClNN.headNullMinus_isotropic n

/-- The `u_+` head mode is isotropic. -/
@[rep_depth krein]
theorem headNullPlus_isotropic (n : ℕ) :
    SplitQuad (n + 1) (headNullPlus n) = 0 :=
  ClNN.headNullPlus_isotropic n

/-- The recursive split head null modes satisfy the CAR normalization. -/
@[rep_depth krein]
theorem gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap (n : ℕ) :
    ClNN.gammaHeadNullMinus n *
        ClNN.gammaHeadNullPlus n
      + ClNN.gammaHeadNullPlus n *
        ClNN.gammaHeadNullMinus n = 1 :=
  ClNN.gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap n

/-- Split Bott carrier alias. -/
@[rep_depth krein]
abbrev SplitBottCarrier (n : ℕ) :=
  BottPeriodicity.SplitBottCarrier n

/-- Split Bott Clifford algebra alias. -/
@[rep_depth krein]
abbrev SplitBottClifford (n : ℕ) :=
  BottPeriodicity.SplitBottClifford n

/-- One-step split Bott factorization. -/
@[rep_depth krein]
noncomputable abbrev splitBottStep (n : ℕ) :
    SplitBottClifford (n + 1)
      ≃ₐ[ℝ]
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 ᵍ⊗[ℝ]
          CliffordAlgebra.evenOdd
            (BottPeriodicity.SplitBottQuad n)) :=
  BottPeriodicity.splitBottStep n

/-- The split Bott step is exactly the tower owner theorem. -/
@[rep_depth krein]
theorem splitBottStep_eq_owner (n : ℕ) :
    BottPeriodicity.splitBottStep n = InfoGeometry.CliffordTower.clsplit_succ_equiv n :=
  BottPeriodicity.splitBottStep_eq_clsplit_succ_equiv n

/-- The repo's split `Cl(4,4)` object. -/
@[rep_depth krein]
abbrev Cl44 := BottPeriodicity.Cl44

/-- `Cl(4,4)` as one split Bott step over `Cl(3,3)`. -/
@[rep_depth krein]
noncomputable abbrev cl44_as_splitBottStep :
    Cl44
      ≃ₐ[ℝ]
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 ᵍ⊗[ℝ]
          CliffordAlgebra.evenOdd
            (BottPeriodicity.SplitBottQuad 3)) :=
  BottPeriodicity.cl44_as_splitBottStep

/-- The `Cl(4,4)` split Bott projection is exactly the owner theorem. -/
@[rep_depth krein]
theorem cl44_as_splitBottStep_eq_owner :
    BottPeriodicity.cl44_as_splitBottStep = InfoGeometry.CliffordTower.clsplit_succ_equiv 3 :=
  BottPeriodicity.cl44_as_splitBottStep_eq_owner

end InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine
