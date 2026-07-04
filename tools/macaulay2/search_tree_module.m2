R = QQ[x,y,z,w]
-- Free module for MCTS branches
F = R^4
-- Submodule representing type errors (invalid branches)
M = image matrix {{x^2, 0, 0, 0}, {0, y^2, 0, 0}, {0, 0, z^2, 0}, {0, 0, 0, w^2}}
-- Pruning invalid branches
Q = F / M
print "Module quotient (pruned search space):"
print Q
exit
