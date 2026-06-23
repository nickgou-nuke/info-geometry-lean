print("=== SageMath Weyl Witness ===")
W = WeylGroup(["D", 5])
print(f"Weyl Group Order: {W.cardinality()}")
if W.cardinality() == 1920:
    print("D5 Weyl exact matching: 1920")
