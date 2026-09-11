import Architect
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.auto_blueprints

/-!
# InfoGeometry.BlueprintTags

LeanArchitect-facing blueprint surface.

This module imports the generated bulk `[blueprint]` coverage layer without pulling it
into the main `InfoGeometry.All` publication surface by default.

Refresh path:
- `python3 tools/refresh_decl_graph.py`
- `python3 tools/refresh_blueprint_tags.py`
- `lake build InfoGeometry.BlueprintTags:blueprint`
- `lake build InfoGeometry.BlueprintTags:blueprintJson`
-/

namespace InfoGeometry.BlueprintTags

-- declarations are registered in `InfoGeometry.auto_blueprints`
-- and exposed through this dedicated LeanArchitect-facing module.

end InfoGeometry.BlueprintTags
