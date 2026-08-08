import Lean

/-!
# Defect Registry Attributes

Lightweight semantic tags for auditing theorem quality and identifying "hollow" or "inflated" declarations.
These attributes allow the Pauli Auditor to distinguish between genuine mathematical derivations and
pedagogical wrappers or legacy bridges.
-/

open Lean

namespace InfoGeometry.Meta

/--
A theorem is hollow if its formal conclusion is already obtainable from strictly weaker local data,
or if the advertised domain layer appears only through unused, dead, or property-carried hypotheses.
-/
initialize hollowAttr : TagAttribute ←
  registerTagAttribute `hollow
    "Mark a theorem as hollow — redundant or missing advertised derivation."

/--
A declaration carries semantic name inflation if its formal proposition is significantly weaker
than the natural-language claim implied by its name.
-/
initialize inflatedAttr : TagAttribute ←
  registerTagAttribute `inflated
    "Mark a declaration as carrying semantic name inflation."

/--
A theorem where the primary bridge or equality is assumed as a property rather than derived.
-/
initialize assumedBridgeAttr : TagAttribute ←
  registerTagAttribute `assumed_bridge
    "Mark a theorem where the bridge relation is assumed rather than derived."

end InfoGeometry.Meta
