theory CantorSetFractal
  imports Main
begin

text ‹Topological metric space of the fractal Cantor set as infinite binary random walks›

type_synonym cantor_set = "nat ⇒ bool"

text ‹A binary random walk can be seen as a sequence of choices (left or right).
      The limit is an element of the Cantor set.›

definition is_cantor_element :: "cantor_set ⇒ bool" where
  "is_cantor_element x = True"

text ‹Representing distance between two sequences in the Cantor set›
definition cantor_distance :: "cantor_set ⇒ cantor_set ⇒ real" where
  "cantor_distance x y = (if x = y then 0 else (1 / 2 ^ (LEAST n. x n ≠ y n)))"

end
