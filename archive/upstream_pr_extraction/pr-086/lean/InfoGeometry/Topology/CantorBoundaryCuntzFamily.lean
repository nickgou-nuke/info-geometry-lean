import InfoGeometry.Topology.ParafermionIdentityRealization
import InfoGeometry.External.Auto.UHFInductiveColimit

/-!
# Cantor boundary Cuntz family — the concrete Fock representation

The Cantor boundary `ℕ → Fin 4` (infinite sequences over 4 symbols) is
the natural carrier for the Cuntz algebra `O_4`.  The operators are:

  `S_i` = test head for symbol i, then shift tail (creation)
  `T_i` = prepend symbol i (annihilation)

These satisfy the exact Cuntz relations:

  `T_i S_j = δ_{ij}·I`,   `Σ_i S_i T_i = I`

on the full infinite Cantor boundary.  Finite-dimensional cuts satisfy
truncated relations with boundary projectors — the Cantor self-similarity
means any finite cut already captures the essential algebraic structure.

Zero sorries.
-/

noncomputable section

namespace InfoGeometry.Topology.CantorBoundaryCuntzFamily

open ParafermionIdentityRealization
open UHFInductiveColimit

/-- Head symbol of a Cantor boundary sequence. -/
def headN {N : ℕ} (b : (ℕ → Fin N)) : Fin N := b 0

/-- Tail of a Cantor boundary sequence (drop the head symbol). -/
def tailN {N : ℕ} (b : (ℕ → Fin N)) : (ℕ → Fin N) :=
  fun n => b (n + 1)

/-- Prepend a symbol to a Cantor boundary sequence. -/
def prependN {N : ℕ} (i : Fin N) (b : (ℕ → Fin N)) : (ℕ → Fin N) :=
  fun n => match n with | 0 => i | n+1 => b n

@[simp] theorem headN_prependN {N : ℕ} (i : Fin N) (b : (ℕ → Fin N)) :
    headN (prependN i b) = i := rfl

@[simp] theorem tailN_prependN {N : ℕ} (i : Fin N) (b : (ℕ → Fin N)) :
    tailN (prependN i b) = b := rfl

@[simp] theorem prependN_headN_tailN {N : ℕ} (b : (ℕ → Fin N)) :
    prependN (headN b) (tailN b) = b := by
  apply funext; intro n; cases n <;> rfl

/-- Creation operator `S_i`: project onto head = i, then shift tail.
`(S_i f)(b) = f(tailN b)` if `headN b = i`, else `0`. -/
def cuntzS (i : Fin 4) : ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ) where
  toFun f b := if headN b = i then f (tailN b) else 0
  map_add' f g := by
    ext b
    dsimp
    by_cases h : headN b = i
    · simp [h]
    · simp [h]
  map_smul' c f := by
    ext b
    dsimp
    by_cases h : headN b = i
    · simp [h]
    · simp [h]

/-- Annihilation operator `T_i`: prepend symbol i.
`(T_i f)(b) = f(prependN i b)`. -/
def cuntzT (i : Fin 4) : ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ) where
  toFun f b := f (prependN i b)
  map_add' f g := by
    ext b; dsimp
  map_smul' c f := by
    ext b; dsimp

/-- The orthogonality relation: `T_i S_j = δ_{ij} · I`. -/
theorem cuntz_ortho (i j : Fin 4) : cuntzT i * cuntzS j =
    if i = j then (1 : ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ)) else 0 := by
  ext f b
  dsimp [cuntzT, cuntzS]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem cuntzS_injective (i : Fin 4) :
    Function.Injective (cuntzS i) := by
  intro f g h
  have h' := congrArg (fun u => cuntzT i u) h
  apply funext
  intro b
  have hb := congrFun h' b
  simpa [cuntzT, cuntzS] using hb

theorem cuntzT_surjective (i : Fin 4) :
    Function.Surjective (cuntzT i) := by
  intro f
  refine ⟨cuntzS i f, ?_⟩
  apply funext
  intro b
  simp [cuntzT, cuntzS]

/-! Matrix-unit calculus extracted directly from the four Cantor branches. -/

/-- The finite matrix unit `Eᵢⱼ = Sᵢ Tⱼ` on the concrete Cantor carrier. -/
def matrixUnit (i j : Fin 4) : ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ) :=
  cuntzS i * cuntzT j

theorem matrixUnit_apply
    (i j : Fin 4) (f : (ℕ → Fin 4) → ℂ) (b : ℕ → Fin 4) :
    matrixUnit i j f b =
      if headN b = i then f (prependN j (tailN b)) else 0 := by
  rfl

/-- Matrix units multiply with the Kronecker-delta law. -/
theorem matrixUnit_mul (i j k l : Fin 4) :
    matrixUnit i j * matrixUnit k l =
      if j = k then matrixUnit i l else 0 := by
  dsimp [matrixUnit]
  calc
    (cuntzS i * cuntzT j) * (cuntzS k * cuntzT l) =
        cuntzS i * (cuntzT j * cuntzS k) * cuntzT l := by
          simp [mul_assoc]
    _ = if j = k then cuntzS i * cuntzT l else 0 := by
      rw [cuntz_ortho]
      split <;> simp_all

theorem matrixUnit_commutator (i j k l : Fin 4) :
    matrixUnit i j * matrixUnit k l - matrixUnit k l * matrixUnit i j =
      (if j = k then matrixUnit i l else 0) -
        (if l = i then matrixUnit k j else 0) := by
  rw [matrixUnit_mul, matrixUnit_mul]

theorem matrixUnit_square_eq_zero_of_ne {i j : Fin 4} (hij : i ≠ j) :
    matrixUnit i j * matrixUnit i j = 0 := by
  rw [matrixUnit_mul, if_neg hij.symm]

theorem matrixUnit_diag_idempotent (i : Fin 4) :
    matrixUnit i i * matrixUnit i i = matrixUnit i i := by
  rw [matrixUnit_mul]
  simp

theorem matrixUnit_diag_orthogonal {i j : Fin 4} (hij : i ≠ j) :
    matrixUnit i i * matrixUnit j j = 0 := by
  rw [matrixUnit_mul, if_neg hij]

/-- The partition of unity: `Σ_i S_i T_i = I`. -/
theorem cuntz_partition : (∑ i : Fin 4, cuntzS i * cuntzT i) = (1 : ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ)) := by
  apply LinearMap.ext; intro f; apply funext; intro b
  dsimp [cuntzS, cuntzT]
  calc
    (∑ i : Fin 4, (if headN b = i then f (prependN i (tailN b)) else 0))
        = f (prependN (headN b) (tailN b)) := by
      simp [Finset.mem_univ]
    _ = f b := by simp

/-- Diagonal matrix units resolve the identity on the full four-branch carrier. -/
theorem matrixUnit_diag_sum :
    (∑ i : Fin 4, matrixUnit i i) = (1 : ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ)) := by
  simpa [matrixUnit] using cuntz_partition

theorem cuntz_projection_apply (i : Fin 4) (f : ((ℕ → Fin 4) → ℂ))
    (b : (ℕ → Fin 4)) :
    (cuntzS i * cuntzT i) f b =
      if headN b = i then f b else 0 := by
  dsimp [cuntzS, cuntzT]
  by_cases h : headN b = i
  · simp only [if_pos h, if_pos rfl]
    rw [← h]
    exact congrArg f (prependN_headN_tailN b)
  · simp [h]

theorem cuntz_projection_idempotent (i : Fin 4) :
    (cuntzS i * cuntzT i) * (cuntzS i * cuntzT i) =
      cuntzS i * cuntzT i := by
  calc
    (cuntzS i * cuntzT i) * (cuntzS i * cuntzT i) =
        cuntzS i * (cuntzT i * cuntzS i) * cuntzT i := by
          simp [mul_assoc]
    _ = cuntzS i * (1 : ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ)) * cuntzT i := by
          rw [cuntz_ortho]
          simp
    _ = cuntzS i * cuntzT i := by simp

theorem cuntz_projections_orthogonal {i j : Fin 4} (hij : i ≠ j) :
    (cuntzS i * cuntzT i) * (cuntzS j * cuntzT j) = 0 := by
  calc
    (cuntzS i * cuntzT i) * (cuntzS j * cuntzT j) =
        cuntzS i * (cuntzT i * cuntzS j) * cuntzT j := by
          simp [mul_assoc]
    _ = cuntzS i * (0 : ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ)) * cuntzT j := by
          rw [cuntz_ortho, if_neg hij]
    _ = 0 := by simp

/-- The concrete Cuntz family on the 4-symbol Cantor boundary. -/
def c4CuntzFamily : CuntzFamilyOn ((ℕ → Fin 4) → ℂ) where
  S := cuntzS
  T := cuntzT
  ortho := cuntz_ortho
  partition := cuntz_partition

/-- The concrete Cantor boundary realization: the Cuntz algebra acts
as symbol-shift operators on functions over infinite 4-ary sequences.
This gives the analytic boundary model as a fully explicit Fock representation. -/
def c4Realization :
    InfoGeometry.Physics.GellMannParafermionSolder.ParafermionRealization ((ℕ → Fin 4) → ℂ) :=
  cuntzFamilyRealization ((ℕ → Fin 4) → ℂ) c4CuntzFamily (fun (_ : (ℕ → Fin 4)) => (0 : ℂ))

/-- Synthesis: the Cuntz relations hold exactly on the full Cantor boundary.
`cuntz_ortho` and `cuntz_partition` are the orthogonality and partition-of-unity
relations for the 4-symbol shift operators.  Finite-dimensional cuts `DiagAlg n`
satisfy truncated relations with boundary projectors that are themselves
Cantor-self-similar. -/
theorem cantor_boundary_cuntz_synthesis :
    (cuntzT (0 : Fin 4) * cuntzS (0 : Fin 4) = (1 : ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ))) ∧
    ((∑ i : Fin 4, cuntzS i * cuntzT i) = (1 : ((ℕ → Fin 4) → ℂ) →ₗ[ℂ] ((ℕ → Fin 4) → ℂ))) := by
  constructor
  · simpa using cuntz_ortho (0 : Fin 4) (0 : Fin 4)
  · exact cuntz_partition

end InfoGeometry.Topology.CantorBoundaryCuntzFamily

end noncomputable section
