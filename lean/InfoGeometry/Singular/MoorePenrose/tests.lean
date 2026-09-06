import InfoGeometry.Singular.MoorePenrose.ClosedRange
import InfoGeometry.Singular.MoorePenrose

/-! ## Moore-Penrose existence: basic compile-time check -/

open InfoGeometry.Singular.MoorePenrose

-- The existence theorem compiles and is accessible.
#check @exists_moorePenroseInverse_of_closedRange
