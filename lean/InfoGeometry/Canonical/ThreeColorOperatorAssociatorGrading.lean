import InfoGeometry.Canonical.ThreeColorOperatorZ3Grading

/-!
# Associator grading of the native three-colour operator carrier

The native Zorn carrier is not made into a Lie or associative algebra here.
This owner records the genuine consequence of the existing `ZMod 3` sector
table: the associator of three homogeneous elements lies in the sum of their
three grades.

No scalar associator cocycle is postulated.  Such a cocycle would be a further
theorem about the explicit multiplication, not a consequence of grading alone.
-/

namespace InfoGeometry.Canonical

variable {A : Type*} [Ring A]

def operatorSub (X Y : OperatorZornMatrix A) : OperatorZornMatrix A :=
  ⟨X.n_plus - Y.n_plus, X.n_minus - Y.n_minus,
    fun i => X.sigma_plus i - Y.sigma_plus i,
    fun i => X.sigma_minus i - Y.sigma_minus i⟩

def operatorAssociator
    (X Y Z : OperatorZornMatrix A) : OperatorZornMatrix A :=
  operatorSub (operatorZornMul (operatorZornMul X Y) Z)
    (operatorZornMul X (operatorZornMul Y Z))

def sectorAdd : ChiralSector → ChiralSector → ChiralSector
  | .diagonal, p => p
  | p, .diagonal => p
  | .plus, .plus => .minus
  | .plus, .minus => .diagonal
  | .minus, .plus => .diagonal
  | .minus, .minus => .plus

@[simp] theorem chiralDegree_sectorAdd (p q : ChiralSector) :
    chiralDegree (sectorAdd p q) = chiralDegree p + chiralDegree q := by
  cases p <;> cases q <;> rfl

@[simp] theorem sectorAdd_assoc (p q r : ChiralSector) :
    sectorAdd (sectorAdd p q) r = sectorAdd p (sectorAdd q r) := by
  cases p <;> cases q <;> cases r <;> rfl

theorem operatorSub_mem_sector
    {p : ChiralSector} {X Y : OperatorZornMatrix A}
    (hX : InSector p X) (hY : InSector p Y) :
    InSector p (operatorSub X Y) := by
  cases p
  · rcases hX with ⟨hXp, hXm⟩
    rcases hY with ⟨hYp, hYm⟩
    constructor
    · funext i
      simp [InSector, operatorSub, hXp, hYp]
    · funext i
      simp [InSector, operatorSub, hXm, hYm]
  · rcases hX with ⟨hXp, hXm, hXminus⟩
    rcases hY with ⟨hYp, hYm, hYminus⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [operatorSub, hXp, hYp]
    · simp [operatorSub, hXm, hYm]
    · funext i
      simp [InSector, operatorSub, hXminus, hYminus]
  · rcases hX with ⟨hXp, hXm, hXplus⟩
    rcases hY with ⟨hYp, hYm, hYplus⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [operatorSub, hXp, hYp]
    · simp [operatorSub, hXm, hYm]
    · funext i
      simp [InSector, operatorSub, hXplus, hYplus]

theorem operatorMul_mem_sector_add
    {p q : ChiralSector} {X Y : OperatorZornMatrix A}
    (hX : InSector p X) (hY : InSector q Y) :
    InSector (sectorAdd p q) (operatorZornMul X Y) := by
  cases p <;> cases q
  · simpa [sectorAdd] using diagonal_mul_diagonal hX hY
  · simpa [sectorAdd] using diagonal_mul_plus hX hY
  · simpa [sectorAdd] using diagonal_mul_minus hX hY
  · simpa [sectorAdd] using plus_mul_diagonal hX hY
  · simpa [sectorAdd] using plus_mul_plus hX hY
  · simpa [sectorAdd] using plus_mul_minus hX hY
  · simpa [sectorAdd] using minus_mul_diagonal hX hY
  · simpa [sectorAdd] using minus_mul_plus hX hY
  · simpa [sectorAdd] using minus_mul_minus hX hY

theorem operatorAssociator_mem_sector_sum
    {p q r : ChiralSector}
    {X Y Z : OperatorZornMatrix A}
    (hX : InSector p X) (hY : InSector q Y) (hZ : InSector r Z) :
    InSector (sectorAdd (sectorAdd p q) r)
      (operatorAssociator X Y Z) := by
  have hXY : InSector (sectorAdd p q) (operatorZornMul X Y) :=
    operatorMul_mem_sector_add hX hY
  have hXYZ : InSector (sectorAdd (sectorAdd p q) r)
      (operatorZornMul (operatorZornMul X Y) Z) :=
    operatorMul_mem_sector_add hXY hZ
  have hYZ : InSector (sectorAdd q r) (operatorZornMul Y Z) :=
    operatorMul_mem_sector_add hY hZ
  have hX_YZ : InSector (sectorAdd p (sectorAdd q r))
      (operatorZornMul X (operatorZornMul Y Z)) :=
    operatorMul_mem_sector_add hX hYZ
  rw [← sectorAdd_assoc p q r] at hX_YZ
  exact operatorSub_mem_sector hXYZ hX_YZ

end InfoGeometry.Canonical
