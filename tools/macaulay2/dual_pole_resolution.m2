R = QQ[x,y,z]
I = ideal(x^2 + y^2 - z^2, x^3, y^3, z^3)
C = res I
print "=== Betti Diagram ==="
print betti C
print "=== Syzygy module maps ==="
print C.dd
