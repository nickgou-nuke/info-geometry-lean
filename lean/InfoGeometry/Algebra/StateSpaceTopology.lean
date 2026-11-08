/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-!
# State-space topology formalization boundary

The former declarations used `True` fields and theorem conclusions to stand in
for weak-* and norm topologies, Banach--Alaoglu compactness, Krein--Milman,
pure-state extremality, spectral gaps, connectedness, and Kähler structure.
They did not define a topological state space or prove those results, so the
placeholder API has been removed.

This module makes no claim about C*-algebra state spaces or the topology of
superselection sectors. A formalization needs an actual topological algebra,
its state space, and the corresponding continuous evaluation maps before
those theorems can be stated in their intended scope.
-/
