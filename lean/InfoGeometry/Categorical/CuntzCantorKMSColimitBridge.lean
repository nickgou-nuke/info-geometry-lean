import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Canonical.CuntzGeneratorKMSLogThree

/-!
# Finite Cuntz/Cantor/UHF compatibility

This owner records only finite algebraic consequences: prefixing of binary
words, cylinder projections, the diagonal UHF successor map, and the word
length weight.  No C*-completion or KMS state is asserted here.
-/

noncomputable section
namespace InfoGeometry.Categorical.CuntzCantorKMSColimitBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

def prefixBoundary (b : Bool) (x : (ℕ → Bool)) : (ℕ → Bool)
  | 0 => b
  | n + 1 => x n

@[simp] theorem prefixBoundary_zero (b : Bool) (x : (ℕ → Bool)) :
    prefixBoundary b x 0 = b := rfl

@[simp] theorem prefixBoundary_succ (b : Bool) (x : (ℕ → Bool)) (n : ℕ) :
    prefixBoundary b x (n + 1) = x n := rfl

def prefixWord (b : Bool) (w : BitWord n) : BitWord (n + 1) :=
  extendSucc n w b

@[simp] theorem prefixWord_restrict (b : Bool) (w : BitWord n) :
    prefixSucc n (prefixWord b w) = w := by
  exact prefixSucc_extendSucc n w b

def cylinderProjectionStage (n : ℕ) (w : BitWord n) : DiagAlg n :=
  fun u => if u = w then 1 else 0

def cylinderProjection (n : ℕ) (w : BitWord n) : (ℕ → Bool) → ℂ :=
  cylinder n (cylinderProjectionStage n w)

@[simp] theorem cylinderProjection_apply (n : ℕ) (w : BitWord n) (x : (ℕ → Bool)) :
    cylinderProjection n w x = if boundaryPrefix n x = w then 1 else 0 := rfl

theorem cylinderProjection_idempotent (n : ℕ) (w : BitWord n) :
    cylinderProjection n w * cylinderProjection n w = cylinderProjection n w := by
  funext x
  by_cases h : boundaryPrefix n x = w <;>
    simp [cylinderProjection, cylinder, cylinderProjectionStage, h]

theorem cylinderProjection_orthogonal {n : ℕ} {w w' : BitWord n} (h : w ≠ w') :
    cylinderProjection n w * cylinderProjection n w' = 0 := by
  funext x
  by_cases h₁ : boundaryPrefix n x = w
  · simp [cylinderProjection, cylinder, cylinderProjectionStage, h₁, h]
  · simp [cylinderProjection, cylinder, cylinderProjectionStage, h₁]

theorem cylinderProjection_mem_colimit (n : ℕ) (w : BitWord n) :
    cylinderProjection n w ∈ CylinderColimit := by
  exact cylinder_mem_colimit n (cylinderProjectionStage n w)

def wordLengthWeight (q : ℂ) (n : ℕ) : ℂ := q ^ n

@[simp] theorem wordLengthWeight_zero (q : ℂ) : wordLengthWeight q 0 = 1 := by
  simp [wordLengthWeight]

theorem wordLengthWeight_succ (q : ℂ) (n : ℕ) :
    wordLengthWeight q (n + 1) = q * wordLengthWeight q n := by
  simp [wordLengthWeight, pow_succ']

theorem cylinder_compatible_prefix (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f :=
  cylinder_compatible_succ n f

theorem embedded_cylinder_projection (n : ℕ) (w : BitWord n) :
    cylinder (n + 1) (diagEmbedSucc n (cylinderProjectionStage n w)) =
      cylinder n (cylinderProjectionStage n w) :=
  cylinder_compatible_succ n (cylinderProjectionStage n w)

/-- The parent cylinder projection splits into its two one-bit children. -/
theorem cylinderProjection_child_sum (n : ℕ) (w : BitWord n) :
    cylinderProjection (n + 1) (prefixWord false w) +
        cylinderProjection (n + 1) (prefixWord true w) =
      cylinderProjection n w := by
  funext x
  change cylinderProjection (n + 1) (prefixWord false w) x +
      cylinderProjection (n + 1) (prefixWord true w) x =
    cylinderProjection n w x
  rw [cylinderProjection_apply, cylinderProjection_apply,
    cylinderProjection_apply]
  have hboundary :
      boundaryPrefix (n + 1) x =
        extendSucc n (boundaryPrefix n x) (x n) := by
    ext i
    by_cases hi : i.1 < n
    · simp [boundaryPrefix, prefixBoundary, extendSucc, hi]
    · have hi' : i.1 = n := by omega
      have hi_eq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi'
      subst i
      simp [boundaryPrefix, prefixBoundary, extendSucc]
  rw [hboundary]
  cases hb : x n with
  | false =>
      have hfalse :
          extendSucc n (boundaryPrefix n x) false = extendSucc n w false ↔
            boundaryPrefix n x = w := by
        constructor
        · intro h
          have hp := congrArg (prefixSucc n) h
          rw [prefixSucc_extendSucc, prefixSucc_extendSucc] at hp
          exact hp
        · intro h
          subst w
          rfl
      have hcross :
          extendSucc n (boundaryPrefix n x) false ≠ extendSucc n w true := by
        intro h
        have hp := congrFun h ⟨n, Nat.lt_succ_self n⟩
        simp [extendSucc] at hp
      simp [prefixWord, hfalse, hcross]
  | true =>
      have htrue :
          extendSucc n (boundaryPrefix n x) true = extendSucc n w true ↔
            boundaryPrefix n x = w := by
        constructor
        · intro h
          have hp := congrArg (prefixSucc n) h
          rw [prefixSucc_extendSucc, prefixSucc_extendSucc] at hp
          exact hp
        · intro h
          subst w
          rfl
      have hcross :
          extendSucc n (boundaryPrefix n x) true ≠ extendSucc n w false := by
        intro h
        have hp := congrFun h ⟨n, Nat.lt_succ_self n⟩
        simp [extendSucc] at hp
      simp [prefixWord, htrue, hcross]

theorem finite_cylinder_packet (n : ℕ) (w w' : BitWord n) :
    cylinderProjection n w * cylinderProjection n w = cylinderProjection n w ∧
    (w ≠ w' → cylinderProjection n w * cylinderProjection n w' = 0) ∧
    cylinderProjection n w ∈ CylinderColimit := by
  exact ⟨cylinderProjection_idempotent n w,
    fun h => cylinderProjection_orthogonal h,
    cylinderProjection_mem_colimit n w⟩

/-!
This is the finite bridge between the diagonal Cantor/UHF layer and the
noncommutative Cuntz generator layer.  It deliberately stops before any
C*-completion or global KMS-state construction.
-/
theorem finite_cuntz_cantor_kms_packet
    {φ : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3 →ₗ[ℂ] ℂ}
    {β : ℝ}
    (hKMS : InfoGeometry.Canonical.GeneratorKMSAt φ β)
    (n : ℕ) (w w' : BitWord n) :
    β = Real.log 3 ∧
      (∀ i j : Fin 3,
        φ (InfoGeometry.Algebra.CuntzTensorQuotient.cuntzS 3 i *
            InfoGeometry.Algebra.CuntzTensorQuotient.cuntzSdag 3 j) =
          if i = j then (1 / 3 : ℂ) else 0) ∧
      cylinderProjection n w * cylinderProjection n w = cylinderProjection n w ∧
      (w ≠ w' → cylinderProjection n w * cylinderProjection n w' = 0) ∧
      cylinderProjection n w ∈ CylinderColimit := by
  have hgen := InfoGeometry.Canonical.cuntzGeneratorKMS_log_three_synthesis hKMS
  refine ⟨hgen.1, hgen.2, ?_⟩
  exact finite_cylinder_packet n w w'

end InfoGeometry.Categorical.CuntzCantorKMSColimitBridge
end noncomputable section
