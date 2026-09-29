sed -i 's/generalize hy/generalize hy/g' lean/InfoGeometry/Lie/E10ProperSubdiagrams.lean
sed -i 's/generalize hy\(.*\) : A9_c\(.*\) x = y\(.*\)/generalize hy\1 : A9_c\2 x = y\3 at heq/g' lean/InfoGeometry/Lie/E10ProperSubdiagrams.lean
sed -i 's/generalize hy\(.*\) : D9_c\(.*\) x = y\(.*\)/generalize hy\1 : D9_c\2 x = y\3 at heq/g' lean/InfoGeometry/Lie/E10ProperSubdiagrams.lean
sed -i '1s/^/set_option maxHeartbeats 1000000\n/' lean/InfoGeometry/Lie/E10ProperSubdiagrams.lean
