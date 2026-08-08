import sympy as sp


M = sp.Matrix([[1, 1], [1, 0]])
v = sp.Matrix([1, 0])

def fib(n):
    return sp.fibonacci(n)


for n in range(12):
    dim = M**n * v
    assert dim[0] == fib(n + 1)
    assert dim[1] == fib(n)

print("PenroseAF.py: finite Fibonacci Bratteli dimensions verified")
