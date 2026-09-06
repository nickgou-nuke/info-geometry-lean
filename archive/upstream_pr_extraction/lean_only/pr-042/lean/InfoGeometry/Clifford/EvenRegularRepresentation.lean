 import Mathlib.LinearAlgebra.CliffordAlgebra.Even

 /-! Algebraic regular representations of the native even Clifford algebra. -/

 noncomputable section
 namespace InfoGeometry.Clifford.EvenRegularRepresentation

 open CliffordAlgebra
 variable {R M : Type*} [CommRing R]
 variable [AddCommGroup M] [Module R M]
 variable (Q : QuadraticForm R M)
 local notation "EvenQ" => CliffordAlgebra.even Q

 def leftRegularLinearMap (a : EvenQ) : EvenQ →ₗ[R] EvenQ :=
   LinearMap.mulLeft R a

 def rightRegularLinearMap (a : EvenQ) : EvenQ →ₗ[R] EvenQ :=
   LinearMap.mulRight R a

 @[simp] theorem leftRegularLinearMap_apply (a x : EvenQ) :
     leftRegularLinearMap Q a x = a * x := rfl
 @[simp] theorem rightRegularLinearMap_apply (a x : EvenQ) :
     rightRegularLinearMap Q a x = x * a := rfl

 theorem leftRegularLinearMap_mul (a b : EvenQ) :
     (leftRegularLinearMap Q a).comp (leftRegularLinearMap Q b) =
       leftRegularLinearMap Q (a * b) := by
   ext x; simp [mul_assoc]
 theorem rightRegularLinearMap_mul (a b : EvenQ) :
     (rightRegularLinearMap Q a).comp (rightRegularLinearMap Q b) =
       rightRegularLinearMap Q (b * a) := by
   ext x; simp [mul_assoc]
 theorem leftRegularLinearMap_comm_rightRegularLinearMap (a b : EvenQ) :
     (leftRegularLinearMap Q a).comp (rightRegularLinearMap Q b) =
       (rightRegularLinearMap Q b).comp (leftRegularLinearMap Q a) := by
   ext x; simp [mul_assoc]

 def leftRegularCommutant : Set (EvenQ →ₗ[R] EvenQ) :=
   {T | ∀ a x, T (leftRegularLinearMap Q a x) =
     leftRegularLinearMap Q a (T x)}

 theorem rightRegularLinearMap_mem_leftRegularCommutant (b : EvenQ) :
     rightRegularLinearMap Q b ∈ leftRegularCommutant Q := by
   intro a x
   simp [leftRegularCommutant, mul_assoc]

 theorem leftRegularCommutant_eq_rightRegularLinearMap_range :
     leftRegularCommutant Q =
       {T | ∃ b : EvenQ, T = rightRegularLinearMap Q b} := by
   ext T
   constructor
   · intro hT
     refine ⟨T 1, ?_⟩
     apply LinearMap.ext
     intro x
     have hx := hT x 1
     simpa only [leftRegularLinearMap_apply, rightRegularLinearMap_apply, one_mul, mul_one] using hx
   · rintro ⟨b, rfl⟩
     exact rightRegularLinearMap_mem_leftRegularCommutant Q b

 theorem coe_mem_evenOdd_zero (a : EvenQ) :
     (a : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q 0 := by
   simpa [CliffordAlgebra.even_toSubmodule] using a.2

 noncomputable def evenEquivEvenOddZero :
     CliffordAlgebra.even Q ≃ₗ[R] CliffordAlgebra.evenOdd Q 0 where
   toFun a := ⟨a.1, coe_mem_evenOdd_zero Q a⟩
   invFun x := ⟨x.1, by
     simpa only [CliffordAlgebra.even_toSubmodule] using x.2⟩
   left_inv a := by rfl
   right_inv x := by rfl
   map_add' a b := by rfl
   map_smul' c a := by rfl

 end InfoGeometry.Clifford.EvenRegularRepresentation
 end
