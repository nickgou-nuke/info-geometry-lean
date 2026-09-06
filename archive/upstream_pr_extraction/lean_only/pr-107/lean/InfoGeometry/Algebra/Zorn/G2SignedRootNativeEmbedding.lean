import InfoGeometry.Algebra.Zorn.G2SignedRootReflections
import InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment

namespace InfoGeometry.Algebra.Zorn.G2SignedRootNativeEmbedding

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
open InfoGeometry.Algebra.Zorn.G2SignedRootReflections
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation

def signedRootToG2Root : SignedPositiveRoot → G2Root
  | (true, .alpha) => (RootLength.Short, 0)
  | (true, .beta) => (RootLength.Long, 0)
  | (true, .alpha_add_beta) => (RootLength.Short, 1)
  | (true, .two_alpha_beta) => (RootLength.Short, 2)
  | (true, .three_alpha_beta) => (RootLength.Long, 1)
  | (true, .three_alpha_two_beta) => (RootLength.Long, 2)
  | (false, .alpha) => (RootLength.Short, 3)
  | (false, .beta) => (RootLength.Long, 3)
  | (false, .alpha_add_beta) => (RootLength.Short, 4)
  | (false, .two_alpha_beta) => (RootLength.Short, 5)
  | (false, .three_alpha_beta) => (RootLength.Long, 4)
  | (false, .three_alpha_two_beta) => (RootLength.Long, 5)

theorem signedRootToG2Root_injective :
    Function.Injective signedRootToG2Root := by
  decide

theorem signedRootToG2Root_surjective :
    Function.Surjective signedRootToG2Root := by
  decide

noncomputable def signedRootEquivG2Root :
    SignedPositiveRoot ≃ G2Root :=
  Equiv.ofBijective signedRootToG2Root
    ⟨signedRootToG2Root_injective, signedRootToG2Root_surjective⟩

noncomputable def simpleReflectionOneOnG2Root : G2Root → G2Root :=
  fun r => signedRootEquivG2Root
    (simpleReflectionOne (signedRootEquivG2Root.symm r))

noncomputable def simpleReflectionTwoOnG2Root : G2Root → G2Root :=
  fun r => signedRootEquivG2Root
    (simpleReflectionTwo (signedRootEquivG2Root.symm r))

theorem simpleReflectionOneOnG2Root_involutive (r : G2Root) :
    simpleReflectionOneOnG2Root (simpleReflectionOneOnG2Root r) = r := by
  apply signedRootEquivG2Root.symm.injective
  simp only [simpleReflectionOneOnG2Root, Equiv.symm_apply_apply,
    simpleReflectionOne_involutive, Equiv.apply_symm_apply]

theorem simpleReflectionTwoOnG2Root_involutive (r : G2Root) :
    simpleReflectionTwoOnG2Root (simpleReflectionTwoOnG2Root r) = r := by
  apply signedRootEquivG2Root.symm.injective
  simp only [simpleReflectionTwoOnG2Root, Equiv.symm_apply_apply,
    simpleReflectionTwo_involutive, Equiv.apply_symm_apply]

def simpleReflectionOneRootTable : G2Root → G2Root
  | (RootLength.Short, 0) => (RootLength.Short, 3)
  | (RootLength.Short, 1) => (RootLength.Short, 2)
  | (RootLength.Short, 2) => (RootLength.Short, 1)
  | (RootLength.Short, 3) => (RootLength.Short, 0)
  | (RootLength.Short, 4) => (RootLength.Short, 5)
  | (RootLength.Short, 5) => (RootLength.Short, 4)
  | (RootLength.Long, 0) => (RootLength.Long, 1)
  | (RootLength.Long, 1) => (RootLength.Long, 0)
  | (RootLength.Long, 2) => (RootLength.Long, 2)
  | (RootLength.Long, 3) => (RootLength.Long, 4)
  | (RootLength.Long, 4) => (RootLength.Long, 3)
  | (RootLength.Long, 5) => (RootLength.Long, 5)

def simpleReflectionTwoRootTable : G2Root → G2Root
  | (RootLength.Short, 0) => (RootLength.Short, 1)
  | (RootLength.Short, 1) => (RootLength.Short, 0)
  | (RootLength.Short, 2) => (RootLength.Short, 2)
  | (RootLength.Short, 3) => (RootLength.Short, 4)
  | (RootLength.Short, 4) => (RootLength.Short, 3)
  | (RootLength.Short, 5) => (RootLength.Short, 5)
  | (RootLength.Long, 0) => (RootLength.Long, 3)
  | (RootLength.Long, 1) => (RootLength.Long, 2)
  | (RootLength.Long, 2) => (RootLength.Long, 1)
  | (RootLength.Long, 3) => (RootLength.Long, 0)
  | (RootLength.Long, 4) => (RootLength.Long, 5)
  | (RootLength.Long, 5) => (RootLength.Long, 4)

theorem simpleReflectionOneRootTable_involutive (r : G2Root) :
    simpleReflectionOneRootTable (simpleReflectionOneRootTable r) = r := by
  cases r with
  | mk l j => cases l <;> fin_cases j <;> rfl

theorem simpleReflectionTwoRootTable_involutive (r : G2Root) :
    simpleReflectionTwoRootTable (simpleReflectionTwoRootTable r) = r := by
  cases r with
  | mk l j => cases l <;> fin_cases j <;> rfl

theorem simpleReflectionOneRootTable_bijective :
    Function.Bijective simpleReflectionOneRootTable := by
  exact ⟨fun x y h => by
    simpa [simpleReflectionOneRootTable_involutive x,
      simpleReflectionOneRootTable_involutive y] using
      congrArg simpleReflectionOneRootTable h,
    fun y => ⟨simpleReflectionOneRootTable y,
      simpleReflectionOneRootTable_involutive y⟩⟩

theorem simpleReflectionTwoRootTable_bijective :
    Function.Bijective simpleReflectionTwoRootTable := by
  exact ⟨fun x y h => by
    simpa [simpleReflectionTwoRootTable_involutive x,
      simpleReflectionTwoRootTable_involutive y] using
      congrArg simpleReflectionTwoRootTable h,
    fun y => ⟨simpleReflectionTwoRootTable y,
      simpleReflectionTwoRootTable_involutive y⟩⟩

theorem simpleReflectionOneRootTable_preserves_length (r : G2Root) :
    (simpleReflectionOneRootTable r).1 = r.1 := by
  cases r with
  | mk l j => cases l <;> fin_cases j <;> rfl

theorem simpleReflectionTwoRootTable_preserves_length (r : G2Root) :
    (simpleReflectionTwoRootTable r).1 = r.1 := by
  cases r with
  | mk l j => cases l <;> fin_cases j <;> rfl

noncomputable def simpleReflectionOneRootEquiv : G2Root ≃ G2Root :=
  Equiv.ofBijective simpleReflectionOneRootTable
    simpleReflectionOneRootTable_bijective

noncomputable def simpleReflectionTwoRootEquiv : G2Root ≃ G2Root :=
  Equiv.ofBijective simpleReflectionTwoRootTable
    simpleReflectionTwoRootTable_bijective

@[simp] theorem simpleReflectionOneRootEquiv_apply (r : G2Root) :
    simpleReflectionOneRootEquiv r = simpleReflectionOneRootTable r := rfl

@[simp] theorem simpleReflectionTwoRootEquiv_apply (r : G2Root) :
    simpleReflectionTwoRootEquiv r = simpleReflectionTwoRootTable r := rfl

@[simp] theorem simpleReflectionOneRootEquiv_symm_apply (r : G2Root) :
    simpleReflectionOneRootEquiv.symm r = simpleReflectionOneRootTable r := by
  apply simpleReflectionOneRootEquiv.injective
  simp [simpleReflectionOneRootTable_involutive]

@[simp] theorem simpleReflectionTwoRootEquiv_symm_apply (r : G2Root) :
    simpleReflectionTwoRootEquiv.symm r = simpleReflectionTwoRootTable r := by
  apply simpleReflectionTwoRootEquiv.injective
  simp [simpleReflectionTwoRootTable_involutive]
