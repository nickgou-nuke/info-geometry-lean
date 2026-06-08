def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


for n in range(4, 9):
    print(f"V_{n} = {fib(n - 1)}")
