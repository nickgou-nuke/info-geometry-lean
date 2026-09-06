import Docs.auto_blueprints
import Docs.generated_blueprints

/-!
# Docs

Umbrella module for documentation-generation library code.

Executable helpers such as `Docs.AutoTag` and `Docs.emit_blueprint_tex`
are intentionally not imported here because each defines a top-level `main`
for `lake env lean --run`.
-/
