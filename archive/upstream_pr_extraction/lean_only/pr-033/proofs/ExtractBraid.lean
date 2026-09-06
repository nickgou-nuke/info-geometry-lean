import Lean
import Mathlib

open Lean
open Lean.Meta
open Lean.Elab.Command

/-- 
  A simple Lean 4 Metaprogramming tool to extract AST nodes and dependency edges 
  from the environment and dump them as JSON for ArangoDB ingestion.
-/

structure Node where
  name : String
  type : String
  kind : String
  deriving ToJson

structure Edge where
  from_node : String
  to_node   : String
  relation  : String
  deriving ToJson

structure GraphData where
  nodes : Array Node
  edges : Array Edge
  deriving ToJson



/-- Command to extract the dependency graph of a specific module prefix -/
elab "#extract_graph " prefixName:ident : command => do
  let env ← getEnv
  let prefixStr := prefixName.getId.toString
  
  let mut nodes : Array Node := #[]
  let mut edges : Array Edge := #[]
  
  for (name, cinfo) in env.constants.toList do
    let nameStr := name.toString
    -- Filter out Mathlib and Lean core library nodes to only capture the 5-layer topology
    if nameStr.startsWith prefixStr && !nameStr.startsWith "Mathlib" &&
        !nameStr.startsWith "Lean" && !nameStr.startsWith "Init" then
      let kind := match cinfo with
        | ConstantInfo.thmInfo _ => "Theorem"
        | ConstantInfo.defnInfo _ => "Definition"
        | ConstantInfo.axiomInfo _ => "Axiom"
        | ConstantInfo.inductInfo _ => "Inductive"
        | ConstantInfo.ctorInfo _ => "Constructor"
        | _ => "Other"

      nodes := nodes.push { name := nameStr, type := toString cinfo.type, kind := kind }
      
      -- Extract edges by looking at the body of definitions and theorems
      let valOpt := cinfo.value?
      if let some val := valOpt then
        let deps := val.getUsedConstants
        for dep in deps do
          let depStr := dep.toString
          -- Create an edge if it depends on something
          edges := edges.push { from_node := nameStr, to_node := depStr, relation := "depends_on" }

  let graph : GraphData := { nodes := nodes, edges := edges }
  let jsonStr := toJson graph |>.pretty
  
  -- We output to a file that our Python pipeline can pick up
  let path : System.FilePath := ⟨"ast_graph.json"⟩
  IO.FS.writeFile path jsonStr
  logInfo s!"Graph extracted! Nodes: {nodes.size}, Edges: {edges.size}. Saved to ast_graph.json"

open Matrix
open Complex

section TemperleyLieb

variable {F : Type*} [Field F]
variable (A : F)

/-- The Temperley-Lieb loop value -/
def d : F := - A^2 - (A⁻¹)^2

variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (e : ℕ → A_alg)

/-- Temperley-Lieb Algebra relations on generators e i -/
class TemperleyLieb (d_val : F) (e : ℕ → A_alg) : Prop where
  e_sq : ∀ i, e i * e i = d_val • e i
  e_comm : ∀ i j, i + 1 < j ∨ j + 1 < i → e i * e j = e j * e i
  e_adj : ∀ i j, (i = j + 1 ∨ j = i + 1) → e i * e j * e i = e i

variable [TemperleyLieb (d A) e]

-- Wrappers to bypass typeclass inference quirks
lemma TL_e_sq {F : Type*} [Field F] (A : F) {A_alg : Type*} [Ring A_alg] [Algebra F A_alg] (e : ℕ → A_alg) [TemperleyLieb (d A) e] (i : ℕ) : e i * e i = (d A) • e i := @TemperleyLieb.e_sq F _ A_alg _ _ (d A) e _ i
lemma TL_e_comm {F : Type*} [Field F] (A : F) {A_alg : Type*} [Ring A_alg] [Algebra F A_alg] (e : ℕ → A_alg) [TemperleyLieb (d A) e] (i j : ℕ) (h : i + 1 < j ∨ j + 1 < i) : e i * e j = e j * e i := @TemperleyLieb.e_comm F _ A_alg _ _ (d A) e _ i j h
lemma TL_e_adj {F : Type*} [Field F] (A : F) {A_alg : Type*} [Ring A_alg] [Algebra F A_alg] (e : ℕ → A_alg) [TemperleyLieb (d A) e] (i j : ℕ) (h : i = j + 1 ∨ j = i + 1) : e i * e j * e i = e i := @TemperleyLieb.e_adj F _ A_alg _ _ (d A) e _ i j h

/-- The Jones representation of the Braid Group generators -/
def σ (i : ℕ) : A_alg := (A:F) • (1:A_alg) + (A⁻¹:F) • e i

/-- Inverse of the Braid Group generators -/
def σ_inv (i : ℕ) : A_alg := (A⁻¹:F) • (1:A_alg) + (A:F) • e i

@[simp] lemma tl_smul_mul_smul_comm (c1 c2 : F) (x1 x2 : A_alg) : 
  (c1 • x1) * (c2 • x2) = (c1 * c2) • (x1 * x2) := by
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]

macro "tl_expand" : tactic => `(tactic| simp only [add_mul, mul_add, tl_smul_mul_smul_comm, add_assoc, one_mul, mul_one])
macro "abel_simp" : tactic => `(tactic| simp only [add_assoc, add_left_comm, add_comm])

lemma add_smul3 (c1 c2 c3 : F) (x : A_alg) : 
  c1 • x + c2 • x + c3 • x = (c1 + c2 + c3) • x := by
  rw [← add_smul, ← add_smul]

lemma add_smul4 (c1 c2 c3 c4 : F) (x : A_alg) : 
  c1 • x + c2 • x + c3 • x + c4 • x = (c1 + c2 + c3 + c4) • x := by
  calc c1 • x + c2 • x + c3 • x + c4 • x
     = c1 • x + c2 • x + c3 • x + c4 • x := by abel_simp
   _ = (c1 + c2 + c3 + c4) • x := by rw [← add_smul, ← add_smul, ← add_smul]

-- Prove that σ and σ_inv are inverses
lemma sigma_mul_sigma_inv (i : ℕ) (hA : A ≠ 0) : σ A e i * σ_inv A e i = 1 := by
  calc
    ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) * ((A⁻¹:F) • (1:A_alg) + (A:F) • e i)
      = ((A * A⁻¹):F) • (1:A_alg) + ((A * A):F) • e i + (((A⁻¹ * A⁻¹):F) • e i + ((A⁻¹ * A):F) • (e i * e i)) := by tl_expand; abel_simp
    _ = (1:F) • (1:A_alg) + (A^2:F) • e i + (((A⁻¹)^2:F) • e i + (1:F) • (e i * e i)) := by
        have h1 : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
        have h2 : A⁻¹ * A = 1 := inv_mul_cancel₀ hA
        have h3 : A * A = A^2 := by ring
        have h4 : A⁻¹ * A⁻¹ = (A⁻¹)^2 := by ring
        rw [h1, h2, h3, h4]
    _ = (1:A_alg) + (A^2:F) • e i + (((A⁻¹)^2:F) • e i + (d A) • e i) := by
        have h_sq : e i * e i = (d A) • e i := TL_e_sq A e i
        rw [h_sq]
        simp only [one_smul]
    _ = (1:A_alg) + (A^2:F) • e i + (((A⁻¹)^2:F) • e i + ((- A^2 - (A⁻¹)^2):F) • e i) := by
        dsimp [d]
    _ = (1:A_alg) + ((A^2:F) • e i + ((A⁻¹)^2:F) • e i + ((- A^2 - (A⁻¹)^2):F) • e i) := by abel_simp
    _ = (1:A_alg) + (A^2 + (A⁻¹)^2 + (- A^2 - (A⁻¹)^2)) • e i := by rw [add_smul3]
    _ = (1:A_alg) + (0:F) • e i := by
        congr 2
        ring
    _ = 1 := by rw [zero_smul, add_zero]

-- Prove far commutation
lemma braid_comm (i j : ℕ) (h : i + 1 < j ∨ j + 1 < i) : σ A e i * σ A e j = σ A e j * σ A e i := by
  calc
    ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e j)
      = ((A * A):F) • (1:A_alg) + ((A * A⁻¹):F) • e j + (((A⁻¹ * A):F) • e i + ((A⁻¹ * A⁻¹):F) • (e i * e j)) := by tl_expand; abel_simp
    _ = ((A * A):F) • (1:A_alg) + ((A * A⁻¹):F) • e j + (((A⁻¹ * A):F) • e i + ((A⁻¹ * A⁻¹):F) • (e j * e i)) := by
        have h_comm : e i * e j = e j * e i := TL_e_comm A e i j h
        rw [h_comm]
    _ = ((A * A):F) • (1:A_alg) + ((A⁻¹ * A):F) • e j + (((A * A⁻¹):F) • e i + ((A⁻¹ * A⁻¹):F) • (e j * e i)) := by
        have hc1 : A * A⁻¹ = A⁻¹ * A := by ring
        have hc2 : A⁻¹ * A = A * A⁻¹ := by ring
        nth_rw 1 [hc1]
        nth_rw 2 [hc2]
    _ = ((A * A):F) • (1:A_alg) + ((A * A⁻¹):F) • e i + (((A⁻¹ * A):F) • e j + ((A⁻¹ * A⁻¹):F) • (e j * e i)) := by abel_simp
    _ = ((A:F) • (1:A_alg) + (A⁻¹:F) • e j) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) := by tl_expand; abel_simp

lemma TL_coef_reduce (hA : A ≠ 0) : A + A + A⁻¹ * (d A) + A⁻¹^3 = A := by
  dsimp [d]
  calc A + A + A⁻¹ * (-A^2 - (A⁻¹)^2) + A⁻¹^3
     = A + A - A⁻¹ * A^2 - A⁻¹ * (A⁻¹)^2 + A⁻¹^3 := by ring
   _ = A + A - A - A⁻¹^3 + A⁻¹^3 := by
       congr 2
       congr 1
       · calc A⁻¹ * A^2 = (A⁻¹ * A) * A := by ring
              _ = 1 * A := by rw [inv_mul_cancel₀ hA]
              _ = A := by ring
       · ring
   _ = A := by ring

lemma hc1 : A * A * A = A^3 := by ring
lemma hc2 (hA : A ≠ 0) : A * A * A⁻¹ = A := by 
  calc A * A * A⁻¹ = A * (A * A⁻¹) := by ring
       _ = A * 1 := by rw [mul_inv_cancel₀ hA]
       _ = A := by ring
lemma hc3 (hA : A ≠ 0) : A * A⁻¹ * A = A := by 
  calc A * A⁻¹ * A = (A * A⁻¹) * A := by ring
       _ = 1 * A := by rw [mul_inv_cancel₀ hA]
       _ = A := by ring
lemma hc4 (hA : A ≠ 0) : A * A⁻¹ * A⁻¹ = A⁻¹ := by 
  calc A * A⁻¹ * A⁻¹ = (A * A⁻¹) * A⁻¹ := by ring
       _ = 1 * A⁻¹ := by rw [mul_inv_cancel₀ hA]
       _ = A⁻¹ := by ring
lemma hc5 (hA : A ≠ 0) : A⁻¹ * A * A = A := by 
  calc A⁻¹ * A * A = (A⁻¹ * A) * A := by ring
       _ = 1 * A := by rw [inv_mul_cancel₀ hA]
       _ = A := by ring
lemma hc6 (hA : A ≠ 0) : A⁻¹ * A * A⁻¹ = A⁻¹ := by 
  calc A⁻¹ * A * A⁻¹ = (A⁻¹ * A) * A⁻¹ := by ring
       _ = 1 * A⁻¹ := by rw [inv_mul_cancel₀ hA]
       _ = A⁻¹ := by ring
lemma hc7 (hA : A ≠ 0) : A⁻¹ * A⁻¹ * A = A⁻¹ := by 
  calc A⁻¹ * A⁻¹ * A = A⁻¹ * (A⁻¹ * A) := by ring
       _ = A⁻¹ * 1 := by rw [inv_mul_cancel₀ hA]
       _ = A⁻¹ := by ring
lemma hc8 : A⁻¹ * A⁻¹ * A⁻¹ = A⁻¹^3 := by ring

-- Prove the Braid Relation for adjacent generators
lemma braid_adj (i j : ℕ) (h : i = j + 1 ∨ j = i + 1) (hA : A ≠ 0) : 
  σ A e i * σ A e j * σ A e i = σ A e j * σ A e i * σ A e j := by
  have h_LHS : ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e j) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) =
               (A^3:F) • (1:A_alg) + (A:F) • e i + ((A:F) • e j + (((A⁻¹):F) • (e i * e j) + ((A⁻¹):F) • (e j * e i))) := by
    calc
      ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e j) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e i)
        = ((A * A * A):F) • (1:A_alg) + ((A * A * A⁻¹):F) • e i + (((A * A⁻¹ * A):F) • e j + (((A * A⁻¹ * A⁻¹):F) • (e j * e i) + 
          (((A⁻¹ * A * A):F) • e i + (((A⁻¹ * A * A⁻¹):F) • (e i * e i) + (((A⁻¹ * A⁻¹ * A):F) • (e i * e j) + ((A⁻¹ * A⁻¹ * A⁻¹):F) • (e i * e j * e i)))))) := by tl_expand; abel_simp
      _ = (A^3:F) • (1:A_alg) + (A:F) • e i + ((A:F) • e j + (((A⁻¹):F) • (e j * e i) + 
          ((A:F) • e i + (((A⁻¹):F) • (e i * e i) + (((A⁻¹):F) • (e i * e j) + ((A⁻¹^3):F) • (e i * e j * e i)))))) := by
          rw [hc1 A, hc2 A hA, hc3 A hA, hc4 A hA, hc5 A hA, hc6 A hA, hc7 A hA, hc8 A]
      _ = (A^3:F) • (1:A_alg) + (A:F) • e i + ((A:F) • e j + (((A⁻¹):F) • (e j * e i) + 
          ((A:F) • e i + (((A⁻¹):F) • ((d A) • e i) + (((A⁻¹):F) • (e i * e j) + ((A⁻¹^3):F) • e i))))) := by
          have h_sq : e i * e i = (d A) • e i := TL_e_sq A e i
          have h_adj : e i * e j * e i = e i := TL_e_adj A e i j h
          rw [h_sq, h_adj]
      _ = (A^3:F) • (1:A_alg) + (A:F) • e i + ((A:F) • e j + (((A⁻¹):F) • (e j * e i) + 
          ((A:F) • e i + (((A⁻¹ * d A):F) • e i + (((A⁻¹):F) • (e i * e j) + ((A⁻¹^3):F) • e i))))) := by rw [smul_smul]
      _ = (A^3:F) • (1:A_alg) + (A:F) • e j + (((A⁻¹):F) • (e i * e j) + (((A⁻¹):F) • (e j * e i) + 
          ((A:F) • e i + (A:F) • e i + ((A⁻¹ * d A):F) • e i + ((A⁻¹^3):F) • e i))) := by abel_simp
      _ = (A^3:F) • (1:A_alg) + (A:F) • e j + (((A⁻¹):F) • (e i * e j) + (((A⁻¹):F) • (e j * e i) + 
          ((A + A + A⁻¹ * d A + A⁻¹^3):F) • e i)) := by
          have hadd : (A:F) • e i + (A:F) • e i + ((A⁻¹ * d A):F) • e i + ((A⁻¹^3):F) • e i = ((A + A + A⁻¹ * d A + A⁻¹^3):F) • e i := add_smul4 A A (A⁻¹ * d A) (A⁻¹^3) (e i)
          rw [hadd]
      _ = (A^3:F) • (1:A_alg) + (A:F) • e j + (((A⁻¹):F) • (e i * e j) + (((A⁻¹):F) • (e j * e i) + (A:F) • e i)) := by
          have hcoef : A + A + A⁻¹ * d A + A⁻¹^3 = A := TL_coef_reduce A hA
          rw [hcoef]
      _ = (A^3:F) • (1:A_alg) + (A:F) • e i + ((A:F) • e j + (((A⁻¹):F) • (e i * e j) + ((A⁻¹):F) • (e j * e i))) := by abel_simp

  have h_RHS : ((A:F) • (1:A_alg) + (A⁻¹:F) • e j) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e j) =
               (A^3:F) • (1:A_alg) + (A:F) • e j + ((A:F) • e i + (((A⁻¹):F) • (e j * e i) + ((A⁻¹):F) • (e i * e j))) := by
    calc
      ((A:F) • (1:A_alg) + (A⁻¹:F) • e j) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e i) * ((A:F) • (1:A_alg) + (A⁻¹:F) • e j)
        = ((A * A * A):F) • (1:A_alg) + ((A * A * A⁻¹):F) • e j + (((A * A⁻¹ * A):F) • e i + (((A * A⁻¹ * A⁻¹):F) • (e i * e j) + 
          (((A⁻¹ * A * A):F) • e j + (((A⁻¹ * A * A⁻¹):F) • (e j * e j) + (((A⁻¹ * A⁻¹ * A):F) • (e j * e i) + ((A⁻¹ * A⁻¹ * A⁻¹):F) • (e j * e i * e j)))))) := by tl_expand; abel_simp
      _ = (A^3:F) • (1:A_alg) + (A:F) • e j + ((A:F) • e i + (((A⁻¹):F) • (e i * e j) + 
          ((A:F) • e j + (((A⁻¹):F) • (e j * e j) + (((A⁻¹):F) • (e j * e i) + ((A⁻¹^3):F) • (e j * e i * e j)))))) := by
          rw [hc1 A, hc2 A hA, hc3 A hA, hc4 A hA, hc5 A hA, hc6 A hA, hc7 A hA, hc8 A]
      _ = (A^3:F) • (1:A_alg) + (A:F) • e j + ((A:F) • e i + (((A⁻¹):F) • (e i * e j) + 
          ((A:F) • e j + (((A⁻¹):F) • ((d A) • e j) + (((A⁻¹):F) • (e j * e i) + ((A⁻¹^3):F) • e j))))) := by
          have h_sq : e j * e j = (d A) • e j := TL_e_sq A e j
          have h_adj : e j * e i * e j = e j := TL_e_adj A e j i (Or.symm h)
          rw [h_sq, h_adj]
      _ = (A^3:F) • (1:A_alg) + (A:F) • e j + ((A:F) • e i + (((A⁻¹):F) • (e i * e j) + 
          ((A:F) • e j + (((A⁻¹ * d A):F) • e j + (((A⁻¹):F) • (e j * e i) + ((A⁻¹^3):F) • e j))))) := by rw [smul_smul]
      _ = (A^3:F) • (1:A_alg) + (A:F) • e i + (((A⁻¹):F) • (e j * e i) + (((A⁻¹):F) • (e i * e j) + 
          ((A:F) • e j + (A:F) • e j + ((A⁻¹ * d A):F) • e j + ((A⁻¹^3):F) • e j))) := by abel_simp
      _ = (A^3:F) • (1:A_alg) + (A:F) • e i + (((A⁻¹):F) • (e j * e i) + (((A⁻¹):F) • (e i * e j) + 
          ((A + A + A⁻¹ * d A + A⁻¹^3):F) • e j)) := by
          have hadd : (A:F) • e j + (A:F) • e j + ((A⁻¹ * d A):F) • e j + ((A⁻¹^3):F) • e j = ((A + A + A⁻¹ * d A + A⁻¹^3):F) • e j := add_smul4 A A (A⁻¹ * d A) (A⁻¹^3) (e j)
          rw [hadd]
      _ = (A^3:F) • (1:A_alg) + (A:F) • e i + (((A⁻¹):F) • (e j * e i) + (((A⁻¹):F) • (e i * e j) + (A:F) • e j)) := by
          have hcoef : A + A + A⁻¹ * d A + A⁻¹^3 = A := TL_coef_reduce A hA
          rw [hcoef]
      _ = (A^3:F) • (1:A_alg) + (A:F) • e j + ((A:F) • e i + (((A⁻¹):F) • (e j * e i) + ((A⁻¹):F) • (e i * e j))) := by abel_simp

  -- Combine LHS and RHS via canonical form
  dsimp [σ]
  rw [h_LHS, h_RHS]
  abel_simp

end TemperleyLieb
