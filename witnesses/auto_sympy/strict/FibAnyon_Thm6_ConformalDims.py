def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a

expected = {4: 2, 5: 3, 6: 5, 7: 8, 8: 13}
for n, dim in expected.items():
    value = fib(n - 1)
    print(f"V_{n} = {value}")
    assert value == dim, (n, value, dim)

print("strict_fibonacci_conformal_dimensions_witness = ok")
