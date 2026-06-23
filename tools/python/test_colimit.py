import os
import subprocess

lean_code = """
import Mathlib
import InfoGeometry.Canonical.CPTDirectLimitGNS
import InfoGeometry.Canonical.InfiniteCARColimit
import InfoGeometry.Clifford.JordanWignerBridge
import InfoGeometry.Clifford.JordanWignerCAR
import InfoGeometry.Canonical.GNSHilbertColimit

noncomputable section

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.CPTDirectLimitGNS
open InfoGeometry.Canonical.InfiniteCARColimit
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.JordanWignerCAR

def limit_u (k : ℕ) : Limit := ofStage (k + 1) (jw_u_new k)
def limit_v (k : ℕ) : Limit := ofStage (k + 1) (jw_v_new k)

lemma anticomm_uu (i : ℕ) : limit_u i * limit_u i = 0 := by
  unfold limit_u
  rw [← map_mul (ofStage (i + 1))]
  rw [jw_u_new_sq i]
  exact map_zero (ofStage (i + 1))

lemma anticomm_vv (i : ℕ) : limit_v i * limit_v i = 0 := by
  unfold limit_v
  rw [← map_mul (ofStage (i + 1))]
  rw [jw_v_new_sq i]
  exact map_zero (ofStage (i + 1))

lemma anticomm_uv (i : ℕ) : limit_u i * limit_v i + limit_v i * limit_u i = 1 := by
  unfold limit_u limit_v
  rw [← map_mul (ofStage (i + 1)), ← map_mul (ofStage (i + 1))]
  rw [← map_add (ofStage (i + 1))]
  rw [jw_uv_anticomm_new i]
  exact map_one (ofStage (i + 1))
"""

with open("/home/goutev/repos/info-geometry-lean/test_car.lean", "w") as f:
    f.write(lean_code)

res = subprocess.run(["lake", "env", "lean", "test_car.lean"], cwd="/home/goutev/repos/info-geometry-lean", capture_output=True, text=True)
print("OUT:", res.stdout)
print("ERR:", res.stderr)
