import InfoGeometry.All

/-!
# InfoGeometry.auto_blueprints

Temporary stub.

The previous generated `[blueprint]` registry referenced many declarations that have
since been renamed/removed, so this file is intentionally reduced to a minimal
compilable surface until the blueprint graph is regenerated.

Regeneration path (repo tooling):
- `python3 tools/refresh_decl_graph.py`
- `python3 tools/refresh_blueprint_tags.py`
- `lake build InfoGeometry.BlueprintTags:blueprint`
- `lake build InfoGeometry.BlueprintTags:blueprintJson`
-/

namespace InfoGeometry

end InfoGeometry
