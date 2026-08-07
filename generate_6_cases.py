def gen():
    out = ""
    # We want to reduce (a b) (0 1 2 3)
    # The pseudoscalar is 0 1 2 3
    cases = [
        (0, 1, 3), # 0: 01 * 0123 -> 23 (basis 3 is 23)
        (0, 2, 4), # 1: 02 * 0123 -> 31 (basis 4 is 31)
        (0, 3, 5), # 2: 03 * 0123 -> 12 (basis 5 is 12)
        (2, 3, 0), # 3: 23 * 0123 -> 01 (basis 0 is 01)
        (3, 1, 1), # 4: 31 * 0123 -> 02 (basis 1 is 02)
        (1, 2, 2)  # 5: 12 * 0123 -> 03 (basis 2 is 03)
    ]
    # Actually wait. 
    # For (a, b) * (0, 1, 2, 3)
    # We can just write out the manual rewrites for a and b.
    pass
