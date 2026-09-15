import InfoGeometry.Krein.State

namespace InfoGeometry.Krein.KreinStateSpace

open KreinSpace

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
variable [CompleteSpace Space] [metric : KreinSpace Space]

theorem mem_nullCone_mk_iff (state : Space) (nonzero : state ≠ 0) :
    Projectivization.mk ℝ state nonzero ∈ NullCone Space ↔ kreinInner state state = 0 := by
  change (if 0 < kreinQuad state then (1 : ℝ)
    else if kreinQuad state < 0 then -1 else 0) = 0 ↔ _
  rw [kreinQuad_apply]
  split_ifs with positive negative
  · constructor <;> intro equality <;> linarith
  · constructor <;> intro equality <;> linarith
  · constructor <;> intro equality <;> linarith

theorem mem_nullCone_iff_rep (ray : KreinStateSpace Space) :
    ray ∈ NullCone Space ↔ kreinInner ray.rep ray.rep = 0 := by
  simpa only [Projectivization.mk_rep] using mem_nullCone_mk_iff ray.rep ray.rep_nonzero

end InfoGeometry.Krein.KreinStateSpace
