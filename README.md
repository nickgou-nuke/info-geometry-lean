# InfoGeometry Lean Project

This repository contains a large Lean project along with a set of
supporting Python and shell scripts used for analysis, documentation,
and tooling.

## Packaging the utility code

The Python helpers are organized as two packages:

* `scripts` – the main collection of command-line tools, and the
  `scripts/cli.py` entry point provides a `infogeometry` console script.
* `tools` – shared utility modules used by the scripts.

A minimal `pyproject.toml` is provided so that you can install the
packages into your Python environment for easier reuse:

```sh
# from the project root
python -m pip install -e .
```

After installation you can run any of the scripts via the `infogeometry`
command, for example:

```sh
infogeometry make-graph --help
```

Note that the graph-exporting code is now part of the core Lean library
(`InfoGeometry.GraphExport`), so there is no Lean source remaining in the
`python` portion of the repository; the Python wrapper simply invokes the
Lean module via `lake env lean --run lean/InfoGeometry/GraphExport.lean`.

Lean-specific helpers (previously in `lean/scripts`) remain under
`scripts/lean` and are included as package data.  Shell scripts still
live alongside the Lean source tree.

## Development notes

* The `scripts/` package is meant to be fairly stable; new tools should
  be added there along with tests if appropriate.
* `tools/` contains low-level helpers and may be imported from any
  script.

Feel free to open an issue or pull request if you need new functionality
or want to reorganize further.

### Graph→Blueprint autolabeling

The `scripts/graph_to_blueprint.py` utility (also available via
`python -m scripts graph-to-blueprint`) reads the exported dependency
graph (`docs-map/graph.json`).  It can operate in two modes:

* **tag file mode** (the default) generates a standalone Lean module
  containing `attribute [blueprint] …` lines, e.g.:  

  ```lean
  attribute [blueprint] InfoGeometry.Core.someLemma
  ```

  This is useful for quick experimentation or when you simply want a
  compact list of tags.

* **patch mode** (`--patch`) copies or edits the original Lean sources
  and inserts the attributes directly into each file.  By default the
  files are modified in place, but you can provide `--out-root`
  to write patched copies under a separate directory while keeping your
  sources untouched.  The patcher also adds `import Architect` where
  needed.  This results in files that are identical to the originals
  except for the inserted tags, which is required for full compatibility
  with LeanArchitect workflows.

Filtering options (`--modules`, `--clusters`) still apply in patch
mode, so you can generate tags for a subset of the graph.

Either mode understands both simple string nodes and the richer dict
objects produced by `scripts/make_graph.py` and will report statistics
on the number of nodes processed.

### Block‑level export and coarse‑grained DAG

For finer analysis we now support splitting a Lean file into *blocks*
(top-level commands) and recording which constants each block produces.
The new Lean module `DAG.BlockExport` exposes a small script executable
via `lake env lean --run`:

```sh
lake env lean --run lean/DAG/BlockExport.lean path/to/file.lean > blocks.ndjson
```

Each output line is a JSON object with the block text range and the list
of names it introduced.  That incidence information can be used to build

* a bipartite incidence graph (`Block → Const`), and
* a coarse‑grained block DAG via constant dependencies (see
  `DAG.buildBlockGraph`).

The latter function lives in the same `DAG` library; given a
`Graph Name` and a map from names to their producing block index it
returns a `Graph Nat` whose nodes are block indices.  You can then run
hydration, reachability, dominators, etc., on the block graph exactly as
on the raw constant graph.

Together with the `graph_to_blueprint` tooling this forms the backbone of
a full kernel‑aware map pipeline: export the constant graph, slice by
block, coarse‑grain to blocks, and finally generate blueprint annotations
on the original source files or in a separate tag module.
