import json
import os

def calculate_ced_systematics():
    # Mirror pairs and their phenomenological parameters
    # CED ~ a * Ex + b * Ex^2 (simple phenomenological model)
    systematics = {
        17:  {"core": "16O",  "config": "1d5/2 particle", "max_spin": 5, "a": -0.010, "b": 0.002, "max_Ex": 5.0},
        39:  {"core": "40Ca", "config": "1d3/2 hole",     "max_spin": 7, "a": 0.015,  "b": -0.001, "max_Ex": 6.0},
        55:  {"core": "56Ni", "config": "1f7/2 hole",     "max_spin": 11,"a": 0.025,  "b": -0.002, "max_Ex": 8.0},
        71:  {"core": "72Kr", "config": "1g9/2 hole",     "max_spin": 15,"a": 0.035,  "b": -0.003, "max_Ex": 10.0},
        102: {"core": "100Sn", "config": "1g9/2 2-particle", "max_spin": 20, "a": 0.045, "b": -0.004, "max_Ex": 12.0}
    }

    results = {}

    for A, params in systematics.items():
        core = params["core"]
        config = params["config"]
        max_spin = params["max_spin"]
        a = params["a"]
        b = params["b"]
        max_Ex = params["max_Ex"]
        
        ced_data = []
        # Generate Ex values from 0 to max_Ex in steps of 1.0 MeV
        # and map spin from ground state to max_spin
        steps = int(max_Ex) + 1
        for i in range(steps):
            Ex = float(i)
            # Spin is roughly proportional to Ex in this simple model
            spin = (Ex / max_Ex) * max_spin
            
            # Phenomenological CED calculation
            ced = a * Ex + b * (Ex ** 2)
            
            ced_data.append({
                "Ex": Ex,
                "spin": round(spin, 1),
                "CED_keV": round(ced * 1000, 1)  # convert MeV to keV
            })
            
        results[f"A={A}"] = {
            "core": core,
            "config": config,
            "max_spin": max_spin,
            "data": ced_data
        }

    # Ensure artifacts directory exists in the repo root or current directory
    repo_root = '/home/goutev/repos/info-geometry-lean'
    artifacts_dir = os.path.join(repo_root, 'artifacts')
    os.makedirs(artifacts_dir, exist_ok=True)
    
    # Export to JSON
    output_file = os.path.join(artifacts_dir, 'mirror_systematics_A17_A102.json')
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=4)
        
    print(f"Exported CED systematics to {output_file}")

if __name__ == "__main__":
    calculate_ced_systematics()
