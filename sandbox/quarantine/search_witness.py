import numpy as np

def dot(u, v):
    return np.dot(u, v)

def cross(u, v):
    return np.cross(u, v)

def zmul(z1, z2):
    a1, b1, x1, y1 = z1
    a2, b2, x2, y2 = z2
    return (
        a1 * a2 + dot(x1, y2),
        b1 * b2 + dot(y1, x2),
        a1 * x2 + b2 * x1 - cross(y1, y2),
        b1 * y2 + a2 * y1 + cross(x1, x2)
    )

z1 = (-1, 1, np.array([1, 0, 0]), np.array([1, 0, 0]))
z2 = (0, 0, np.array([0, 1, 0]), np.array([0, 1, 0]))
z3 = (0, 0, np.array([0, 0, 1]), np.array([0, 0, 0]))

prod1 = zmul(zmul(z1, z2), z3)
prod2 = zmul(z1, zmul(z2, z3))
assoc = (
    prod1[0] - prod2[0],
    prod1[1] - prod2[1],
    prod1[2] - prod2[2],
    prod1[3] - prod2[3]
)
print("Associator:", assoc)
