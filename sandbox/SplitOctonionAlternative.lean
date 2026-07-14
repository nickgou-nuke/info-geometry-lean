import Mathlib
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

namespace InfoGeometry.Algebra.Sandbox

lemma left_alternative_cancellation (X Y : SplitOct) : 
  mulZ (conjZ X) (mulZ X Y) = mulZ (scalarZ (detZ X)) Y := by
  ext <;> simp [mulZ, conjZ, scalarZ, detZ] <;> ring

lemma moufang_identity (X Y Z : SplitOct) : 
  mulZ (mulZ X Y) (mulZ Z X) = mulZ X (mulZ (mulZ Y Z) X) := by
  ext <;> simp [mulZ, conjZ, scalarZ, detZ] <;> ring

end InfoGeometry.Algebra.Sandbox
