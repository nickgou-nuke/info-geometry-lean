import Omega.HyperKernel.SetStructure
import Omega.HyperKernel.Enum

namespace Omega.HyperKernel
namespace SetStructureChecksLite

open SetStructure

/-- rank-1 idempotents for n=3 and n=4 -/
theorem pointCount_n3 : (pointObjects 3).length = 3 := by
  decide

theorem pointCount_n4 : (pointObjects 4).length = 4 := by
  decide

/-- idempotents for n=3 and n=4 -/
theorem setObjCount_n3 : (setObjects 3).length = 10 := by
  decide

theorem setObjCount_n4 : (setObjects 4).length = 41 := by
  decide

end SetStructureChecksLite
end Omega.HyperKernel
