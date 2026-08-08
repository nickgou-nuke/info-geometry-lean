import sys

def fix_lean_file(filepath):
    with open(filepath, 'r') as f:
        lines = f.readlines()
    
    out = []
    in_by = False
    buffer = ""
    
    for line in lines:
        stripped = line.strip()
        if "by" in stripped and stripped.endswith("by"):
            out.append(line)
            in_by = True
            continue
        
        if stripped == "end FibAnyonTrueHexagon":
            in_by = False
            out.append(line)
            continue
            
        if in_by and not stripped.startswith("end") and not stripped.startswith("lemma") and not stripped.startswith("theorem") and not stripped.startswith("def") and not stripped.startswith("structure"):
            if stripped == "":
                out.append("\n")
                in_by = False
            elif stripped.startswith("linear_combination"):
                buffer = "  " + stripped
            elif buffer != "":
                buffer += " " + stripped
                if not stripped.endswith("+") and not stripped.endswith("-") and not stripped.endswith("*"):
                    out.append(buffer + "\n")
                    buffer = ""
            elif stripped.startswith("|"):
                out.append("  " + stripped + "\n")
            else:
                out.append("  " + stripped + "\n")
        else:
            in_by = False
            out.append(line)
            
    with open(filepath, 'w') as f:
        f.writelines(out)

if __name__ == "__main__":
    fix_lean_file("proofs/FibAnyonTrueHexagon.lean")
