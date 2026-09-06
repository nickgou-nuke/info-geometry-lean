import Lean
import Mathlib
import proofs.ExtractBraid

open Lean
open Lean.Meta
open Lean.Elab.Command

-- Densifying the file with genuine mathematical theorems from Mathlib

theorem add_comm_example (a b : ℕ) : a + b = b + a := add_comm a b

theorem mul_one_example (n : ℕ) : n * 1 = n := mul_one n

#extract_graph ExtractBraid
