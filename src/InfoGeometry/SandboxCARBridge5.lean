/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SandboxCARBridge
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open Matrix

abbrev Mat8Z := Matrix Dim8 Dim8 ℤ

def eps0Z : Mat8Z :=
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0]]

theorem eps0Z_sq : eps0Z * eps0Z = 0 := by decide
