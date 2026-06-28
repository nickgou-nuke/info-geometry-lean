import sys

def model_a39_mirror_states():
    print("=== A=39 Mirror Pair (39Ca and 39K) High-Spin States Model ===")
    print("Core: 40Ca (1h configuration)")
    
    # Ex (MeV) and J^pi for different configurations
    states = [
        {"config": "0p-1h", "J_pi": "3/2+", "Ex": 0.0, "parity": 1},
        {"config": "0p-1h", "J_pi": "1/2+", "Ex": 2.5, "parity": 1},
        {"config": "1p-2h", "J_pi": "7/2-", "Ex": 3.0, "parity": -1},
        {"config": "1p-2h", "J_pi": "13/2-", "Ex": 5.0, "parity": -1},
        {"config": "2p-3h", "J_pi": "15/2+", "Ex": 6.5, "parity": 1},
        {"config": "2p-3h", "J_pi": "21/2+", "Ex": 8.0, "parity": 1},
        {"config": "3p-4h", "J_pi": "23/2-", "Ex": 9.5, "parity": -1},
        {"config": "3p-4h", "J_pi": "27/2-", "Ex": 11.0, "parity": -1},
    ]
    
    # CED = a * Ex^2 + b * Ex + c
    # Negative parity: stronger decrease
    var('x')
    ced_model_neg = -15 * x - 10
    ced_model_pos = -2 * x + 50
    
    print("\nStates and CED predictions:")
    print(f"{'Config':<10} {'J^pi':<10} {'Ex (MeV)':<15} {'Parity':<10} {'CED (keV)':<15}")
    print("-" * 65)
    
    results = []
    for s in states:
        Ex = s["Ex"]
        parity = s["parity"]
        
        if parity == 1:
            ced = float(ced_model_pos(x=Ex))
        else:
            ced = float(ced_model_neg(x=Ex))
            
        s["CED"] = ced
        results.append(s)
        print(f"{s['config']:<10} {s['J_pi']:<10} {Ex:<15.1f} {parity:<10} {ced:<15.1f}")
        
    return results

def run_tests(results):
    passed = True
    
    # Test 1: CED for negative parity states should decrease with Ex
    neg_states = [s for s in results if s["parity"] == -1]
    for i in range(1, len(neg_states)):
        if neg_states[i]["CED"] >= neg_states[i-1]["CED"]:
            print(f"FAIL: CED did not decrease for negative parity states between Ex={neg_states[i-1]['Ex']} and Ex={neg_states[i]['Ex']}")
            passed = False
            
    # Test 2: Check configurations presence
    configs_found = {s["config"] for s in results}
    expected_configs = {"0p-1h", "1p-2h", "2p-3h", "3p-4h"}
    if not expected_configs.issubset(configs_found):
        print(f"FAIL: Missing expected configurations. Found: {configs_found}")
        passed = False
        
    # Test 3: Check max J for configs
    max_j = {"1p-2h": "13/2-", "2p-3h": "21/2+", "3p-4h": "27/2-"}
    for config, j in max_j.items():
        j_list = [s["J_pi"] for s in results if s["config"] == config]
        if j not in j_list:
            print(f"FAIL: Configuration {config} missing max J_pi {j}")
            passed = False

    if passed:
        print("\nPASS")
    else:
        print("\nFAIL")
        sys.exit(1)


res = model_a39_mirror_states()
run_tests(res)
