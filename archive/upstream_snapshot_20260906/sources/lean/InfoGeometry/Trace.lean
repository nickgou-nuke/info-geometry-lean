/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib

open Matrix

/-!
# Trace

The trace of a matrix commutator is identically zero over any commutative ring.
-/

universe u v

variable {n : Type v} [Fintype n] {R : Type u} [CommRing R]

/--
`trace (A * B - B * A) = 0` for any square matrices `A, B` over a commutative ring `R`.
-/
theorem trace_comm (A B : Matrix n n R) : trace (A * B - B * A) = 0 := by
  calc
    trace (A * B - B * A) = trace (A * B) - trace (B * A) := by
      simp
    _ = trace (A * B) - trace (A * B) := by
      rw [trace_mul_comm A B]
    _ = 0 := by ring
