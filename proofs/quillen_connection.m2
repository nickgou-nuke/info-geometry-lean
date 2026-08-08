-- quillen_connection.m2
-- Bismut's formula for the curvature of the Quillen connection

R = QQ[c1, c2, c3, p1, p2, p3] -- Chern and Pontryagin classes

-- Hat A genus components
A_hat_0 = 1
A_hat_1 = -p1/24
A_hat_2 = (7*p1^2 - 4*p2)/5760
A_hat_3 = (-31*p1^3 + 44*p1*p2 - 16*p3)/967680

-- Chern character components of bundle E
ch_0 = 2 -- Rank
ch_1 = c1
ch_2 = (c1^2 - 2*c2)/2
ch_3 = (c1^3 - 3*c1*c2 + 3*c3)/6

-- Bismut's formula for the curvature of the determinant line bundle
-- c1(det(ind D_E)) = [ \hat{A}(X) ch(E) ]_{2}
-- The degree 2 component in characteristic classes corresponds to dimension 4 integration

-- Degree 1 component of the product (dimension 2)
curv_det_1 = A_hat_0 * ch_1 + A_hat_1 * ch_0

-- Degree 2 component of the product (dimension 4)
curv_det_2 = A_hat_0 * ch_2 + A_hat_1 * ch_1 + A_hat_2 * ch_0

-- Degree 3 component of the product (dimension 6)
curv_det_3 = A_hat_0 * ch_3 + A_hat_1 * ch_2 + A_hat_2 * ch_1 + A_hat_3 * ch_0

print("Bismut's curvature components:")
print("Dim 2: ", curv_det_1)
print("Dim 4: ", curv_det_2)
print("Dim 6: ", curv_det_3)
