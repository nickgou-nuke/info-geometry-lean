import InfoGeometry.Clifford.ClNNSuperGrassmannianBridge
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Canonical.SplitCliffordExteriorTowerBridge
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.Projection

/-!
# Super-grade involution on the symmetric split Clifford colimit

The finite `Cl(N,N)` stages carry Mathlib's even/odd Clifford grading, while
`SplitCliffordInfinity` is the repository's canonical algebraic direct limit.
This file lifts the native Clifford grade involution to that colimit and shows
that the recursive CAR generators and the exterior super-grades are respected.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordSuperGradeColimit

open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ClNNSuperGrassmannianBridge
open InfoGeometry.CliffordTower
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Algebra.SuperGrassmannianClifford

/-- Over `ℝ`, the fixed points of Mathlib's Clifford grade involution are
exactly its even submodule. The converse uses the native even/odd complement
and the fact that multiplication by `2` is injective on a real vector space. -/
theorem clifford_involute_eq_self_iff_mem_even
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (x : CliffordAlgebra Q) :
    CliffordAlgebra.involute x = x ↔
      x ∈ CliffordAlgebra.evenOdd Q 0 := by
  constructor
  · intro hfix
    obtain ⟨e, o, heo, _⟩ :=
      Submodule.existsUnique_add_of_isCompl
        (CliffordAlgebra.evenOdd_isCompl (Q := Q)) x
    have hinvol : CliffordAlgebra.involute x = (e : CliffordAlgebra Q) - o := by
      rw [← heo, map_add,
        CliffordAlgebra.involute_eq_of_mem_even e.property,
        CliffordAlgebra.involute_eq_of_mem_odd o.property]
      simp only [sub_eq_add_neg]
    have hsum : (e : CliffordAlgebra Q) + o = (e : CliffordAlgebra Q) - o := by
      calc
        (e : CliffordAlgebra Q) + o = x := heo
        _ = CliffordAlgebra.involute x := hfix.symm
        _ = (e : CliffordAlgebra Q) - o := hinvol
    have honeg : (o : CliffordAlgebra Q) = -o :=
      add_left_cancel (by simpa only [sub_eq_add_neg] using hsum)
    have htwo : (o : CliffordAlgebra Q) + o = 0 := by
      calc
        (o : CliffordAlgebra Q) + o =
            (o : CliffordAlgebra Q) + (-(o : CliffordAlgebra Q)) :=
          congrArg (fun z : CliffordAlgebra Q => (o : CliffordAlgebra Q) + z) honeg
        _ = 0 := add_neg_cancel _
    have hozero : (o : CliffordAlgebra Q) = 0 := by
      have hscalar : (2 : ℝ) • (o : CliffordAlgebra Q) = 0 := by
        simpa [two_smul] using htwo
      exact (smul_eq_zero.mp hscalar).resolve_left (by norm_num)
    have hx : x = (e : CliffordAlgebra Q) := by
      calc
        x = (e : CliffordAlgebra Q) + o := heo.symm
        _ = e := by rw [hozero, add_zero]
    rw [hx]
    exact e.property
  · exact CliffordAlgebra.involute_eq_of_mem_even

/-- The canonical one-step split-Clifford bond commutes with Mathlib's grade
involution. The proof is checked on the recursively embedded tail generators. -/
theorem splitCliffordStep_involute (n : ℕ) (x : Alg n) :
    CliffordAlgebra.involute (splitCliffordStep n x) =
      splitCliffordStep n (CliffordAlgebra.involute x) := by
  have hgen (v : Carrier n) :
      splitCliffordStep n (CliffordAlgebra.ι (Qsplit n) v) =
        CliffordAlgebra.ι (Qsplit (n + 1)) (tailLift n v) := by
    rw [← InfoGeometry.Canonical.SplitCliffordExteriorTowerBridge.stageCliffordMap_eq_canonicalStep,
      splitStageCliffordMap_generator_eq_gammaTail]
    rfl
  have hhom :
      (CliffordAlgebra.involute (Q := Qsplit (n + 1))).comp
          (splitCliffordStep n) =
        (splitCliffordStep n).comp
          (CliffordAlgebra.involute (Q := Qsplit n)) := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change CliffordAlgebra.involute
        (splitCliffordStep n (CliffordAlgebra.ι (Qsplit n) v)) =
      splitCliffordStep n
        (CliffordAlgebra.involute (CliffordAlgebra.ι (Qsplit n) v))
    calc
      CliffordAlgebra.involute
          (splitCliffordStep n (CliffordAlgebra.ι (Qsplit n) v)) =
        CliffordAlgebra.involute
          (CliffordAlgebra.ι (Qsplit (n + 1)) (tailLift n v)) :=
            congrArg CliffordAlgebra.involute (hgen v)
      _ = -CliffordAlgebra.ι (Qsplit (n + 1)) (tailLift n v) :=
        CliffordAlgebra.involute_ι _
      _ = splitCliffordStep n (-CliffordAlgebra.ι (Qsplit n) v) := by
        rw [map_neg, hgen]
      _ = splitCliffordStep n
          (CliffordAlgebra.involute (CliffordAlgebra.ι (Qsplit n) v)) := by
        rw [CliffordAlgebra.involute_ι]
  exact congrArg (fun f : Alg n →ₐ[ℝ] Alg (n + 1) => f x) hhom

/-- Iterated transition maps commute with grade involution. -/
theorem splitCliffordMap_involute (m n : ℕ) (h : m ≤ n) (x : Alg m) :
    CliffordAlgebra.involute (splitCliffordMap m n h x) =
      splitCliffordMap m n h (CliffordAlgebra.involute x) := by
  induction n, h using Nat.le_induction with
  | base =>
      simp [splitCliffordMap_refl]
  | succ n hmn ih =>
      rw [splitCliffordMap_succ (m := m) (n := n) hmn]
      change CliffordAlgebra.involute
          (splitCliffordStep n (splitCliffordMap m n hmn x)) =
        splitCliffordStep n
          (splitCliffordMap m n hmn (CliffordAlgebra.involute x))
      rw [splitCliffordStep_involute, ih]

/-- Every canonical tower transition preserves the finite even submodule.
This follows from compatibility with the lifted grade involution and the
real fixed-point characterization above. -/
theorem splitCliffordMap_mem_even_of_mem_even
    (m n : ℕ) (h : m ≤ n) {x : Alg m}
    (hx : x ∈ CliffordAlgebra.evenOdd (Qsplit m) 0) :
    splitCliffordMap m n h x ∈ CliffordAlgebra.evenOdd (Qsplit n) 0 := by
  apply (clifford_involute_eq_self_iff_mem_even (Qsplit n) _).1
  rw [splitCliffordMap_involute,
    CliffordAlgebra.involute_eq_of_mem_even hx]

private theorem splitCliffordInvolute_compatible
    (m n : ℕ) (h : m ≤ n) (x : Alg m) :
    (DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) n).comp
        (CliffordAlgebra.involute (Q := Qsplit n))
        (splitCliffordMap m n h x) =
      (DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) m)
        (CliffordAlgebra.involute (Q := Qsplit m) x) := by
  rw [AlgHom.comp_apply, splitCliffordMap_involute]
  exact DirectLimit.Algebra.of_f
    (f := fun i j hij => splitCliffordMap i j hij) h (CliffordAlgebra.involute x)

/-- The stagewise Mathlib grade involutions induce an algebra endomorphism on
the canonical direct limit of the symmetric split Clifford tower. -/
noncomputable def splitCliffordInfinityInvolute :
    SplitCliffordInfinity →ₐ[ℝ] SplitCliffordInfinity :=
  DirectLimit.Algebra.lift SplitClNNAlg
    (fun i j hij => splitCliffordMap i j hij) SplitCliffordInfinity
    (fun n =>
      (DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) n).comp
        (CliffordAlgebra.involute (Q := Qsplit n)))
    (by
      intro m n h x
      exact splitCliffordInvolute_compatible m n h x)

@[simp] theorem splitCliffordInfinityInvolute_ofStage
    (n : ℕ) (x : Alg n) :
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) n x) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij)
        n (CliffordAlgebra.involute x) := by
  rfl

/-- The lifted grade involution is involutive on the direct-limit algebra. -/
theorem splitCliffordInfinityInvolute_involutive (x : SplitCliffordInfinity) :
    splitCliffordInfinityInvolute
        (splitCliffordInfinityInvolute x) = x := by
  induction x using DirectLimit.induction with
  | _ n a =>
      change splitCliffordInfinityInvolute
          (splitCliffordInfinityInvolute
            (DirectLimit.Algebra.of SplitClNNAlg
              (fun i j hij => splitCliffordMap i j hij) n a)) =
        DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) n a
      rw [splitCliffordInfinityInvolute_ofStage,
        splitCliffordInfinityInvolute_ofStage,
        CliffordAlgebra.involute_involute]

/-- Every finite even Clifford element maps to a fixed point of the colimit
grade involution. -/
theorem directLimit_of_even_fixed (n : ℕ) {x : Alg n}
    (hx : x ∈ CliffordAlgebra.evenOdd (Qsplit n) 0) :
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) n x) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) n x := by
  rw [splitCliffordInfinityInvolute_ofStage,
    CliffordAlgebra.involute_eq_of_mem_even hx]

/-- Every finite odd Clifford element maps to a negative eigenvector of the
colimit grade involution. -/
theorem directLimit_of_odd_negated (n : ℕ) {x : Alg n}
    (hx : x ∈ CliffordAlgebra.evenOdd (Qsplit n) 1) :
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) n x) =
      -DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) n x := by
  rw [splitCliffordInfinityInvolute_ofStage,
    CliffordAlgebra.involute_eq_of_mem_odd hx, map_neg]

/-- The transported exterior super-grade-zero component maps to the fixed
eigenspace of the canonical split-Clifford colimit involution. -/
theorem directLimit_of_superGrade_zero_fixed
    (n : ℕ) (x : SplitExteriorStage n)
    (hx : x ∈ superGrade (Qsplit n) (0 : ZMod 2)) :
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) n
          ((cliffordExteriorEquiv (Qsplit n)).symm x)) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) n
          ((cliffordExteriorEquiv (Qsplit n)).symm x) := by
  apply directLimit_of_even_fixed
  change (cliffordExteriorEquiv (Qsplit n)).symm x ∈
    CliffordAlgebra.evenOdd (Qsplit n) 0 at hx
  exact hx

/-- The transported exterior super-grade-one component maps to the negative
eigenspace of the canonical split-Clifford colimit involution. -/
theorem directLimit_of_superGrade_one_negated
    (n : ℕ) (x : SplitExteriorStage n)
    (hx : x ∈ superGrade (Qsplit n) (1 : ZMod 2)) :
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) n
          ((cliffordExteriorEquiv (Qsplit n)).symm x)) =
      -DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) n
          ((cliffordExteriorEquiv (Qsplit n)).symm x) := by
  apply directLimit_of_odd_negated
  change (cliffordExteriorEquiv (Qsplit n)).symm x ∈
    CliffordAlgebra.evenOdd (Qsplit n) 1 at hx
  exact hx

/-- The recursive head null generators remain odd under the grade involution
after passage to the canonical `Cl(N,N)` colimit. -/
theorem headNull_generators_colimit_odd (n : ℕ) :
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) (n + 1)
          (gammaHeadNullMinus n)) =
      -DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) (n + 1)
          (gammaHeadNullMinus n) ∧
    splitCliffordInfinityInvolute
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) (n + 1)
          (gammaHeadNullPlus n)) =
      -DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) (n + 1)
          (gammaHeadNullPlus n) := by
  constructor
  · apply directLimit_of_odd_negated
    simpa [gammaHeadNullMinus] using
      CliffordAlgebra.ι_mem_evenOdd_one (Q := Qsplit (n + 1)) (headNullMinus n)
  · apply directLimit_of_odd_negated
    simpa [gammaHeadNullPlus] using
      CliffordAlgebra.ι_mem_evenOdd_one (Q := Qsplit (n + 1)) (headNullPlus n)

/-- The head CAR relation of the recursive split tower is retained by its
canonical algebraic direct-limit stage maps. -/
theorem headNull_pair_CAR_in_colimit (n : ℕ) :
    DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) (n + 1)
          (gammaHeadNullMinus n) *
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) (n + 1)
          (gammaHeadNullPlus n) +
    DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) (n + 1)
          (gammaHeadNullPlus n) *
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) (n + 1)
          (gammaHeadNullMinus n) = 1 := by
  have h := congrArg
    (DirectLimit.Algebra.of SplitClNNAlg
      (fun i j hij => splitCliffordMap i j hij) (n + 1))
    (gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap n)
  simpa only [map_add, map_mul, map_one] using h

end InfoGeometry.Canonical.SplitCliffordSuperGradeColimit

end noncomputable section
