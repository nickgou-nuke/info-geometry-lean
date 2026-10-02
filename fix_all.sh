# Fix E10ProperSubdiagrams: remove set_option from line 1 and put it after imports
sed -i '1d' lean/InfoGeometry/Lie/E10ProperSubdiagrams.lean
sed -i '/^import/!b;:a;n;/^import/ba;i\set_option maxHeartbeats 1000000' lean/InfoGeometry/Lie/E10ProperSubdiagrams.lean

# Fix E10RootHeightColimit
sed -i 's/Mathlib.CategoryTheory.Limits.ConcreteCategory/Mathlib.CategoryTheory.Limits.Types/g' lean/InfoGeometry/Lie/E10RootHeightColimit.lean
