import sandbox.ZornMatrixCore_subagent
open InfoGeometry.Physics.ZornMatrixSU3

theorem test_ha (M N P : ZornMatrix) : 
  M.a * P.a + N.a * P.a +
      (M.x 0 * P.y 0 + N.x 0 * P.y 0 + (M.x 1 * P.y 1 + N.x 1 * P.y 1) + (M.x 2 * P.y 2 + N.x 2 * P.y 2)) =
    M.a * P.a + (M.x 0 * P.y 0 + M.x 1 * P.y 1 + M.x 2 * P.y 2) +
      (N.a * P.a + (N.x 0 * P.y 0 + N.x 1 * P.y 1 + N.x 2 * P.y 2)) := by
  ring
