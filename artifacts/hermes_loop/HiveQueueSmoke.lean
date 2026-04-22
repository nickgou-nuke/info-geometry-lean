import Mathlib
import InfoGeometry.Meta.HiveLogos

example (P Q : Prop) : P -> P := by
  hive_probe
  intro h
  exact h

#hive_index_decl And.intro
