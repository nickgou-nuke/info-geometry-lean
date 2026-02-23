# Lean-specific helper scripts

This folder holds small helpers that operate on the Lean sources inside the
`lean/` subtree.  They are mostly shell wrappers invoked from the project
root; they assume `lake` is available and that current directory is the
repository root.

Common categories:

* **Build checks** (`strict-check.sh`, `profile-build.sh`) – run `lake build`
  with special flags or perform additional validation on canonical modules.
* **Import auditing** (`audit-imports.sh`, `clean-unused-imports.sh`) –
  detect and optionally remove unused `import` declarations in Lean files.
* **Maintenance** (`orphaned-check.sh`) – find stray files or broken
  references.
* **Miscellaneous** (`catastrophe_surface.py`) – experimental scripts that
  happen to live here; these can be moved out to `notes/` or another
  appropriate location as the project matures.

Invoke them directly with bash, e.g.

```sh
bash lean/scripts/strict-check.sh
``` 

or (for Python scripts) using the workspace’s Python interpreter:

```sh
python -m lean.scripts.catastrophe_surface --help
```

