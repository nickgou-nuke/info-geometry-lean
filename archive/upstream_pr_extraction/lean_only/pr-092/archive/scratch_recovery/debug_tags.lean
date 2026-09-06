import InfoGeometry.Canonical.CasimirWeylDrazinContext
import InfoGeometry.Meta.Architecture

open InfoGeometry.Meta
open InfoGeometry.Canonical.CasimirWeylDrazinContext

#eval show CoreM Unit from do
  let env ← getEnv
  let name := `InfoGeometry.Canonical.CasimirWeylDrazinContext.CasimirWeylDrazinData
  if let some depth := repDepth? env name then
    IO.println s!"depth of {name}: {depth.toNat}"
  else
    IO.println s!"no depth for {name}"
