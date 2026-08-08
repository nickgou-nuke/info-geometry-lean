import os
import subprocess
import sys

def find_lean_files(root_dir):
    lean_files = []
    for dirpath, dirnames, filenames in os.walk(root_dir):
        if '.lake' in dirnames:
            dirnames.remove('.lake')
        if 'tools' in dirnames:
            dirnames.remove('tools')
        if 'external_repos' in dirnames:
            dirnames.remove('external_repos')
            
        for filename in filenames:
            if filename.endswith('.lean'):
                lean_files.append(os.path.join(dirpath, filename))
    return lean_files

def extract_all():
    root_dir = '/home/goutev/auto/proofs'
    lean_files = find_lean_files(root_dir)
    output_file = os.path.join(root_dir, 'tactic_states.jsonl')
    extractor_script = 'tools/lean_graph/ExtractInfoTree.lean'
    
    print(f"Found {len(lean_files)} Lean files to process.")
    
    with open(output_file, 'w') as f_out:
        print(f"Executing sequential batch extraction...")
        for idx, f in enumerate(lean_files):
            print(f"[{idx+1}/{len(lean_files)}] Extracting {f}...", end='', flush=True)
            rel_f = os.path.relpath(f, root_dir)
            try:
                result = subprocess.run(
                    ['lake', 'env', 'lean', '--run', extractor_script, rel_f],
                    cwd=root_dir,
                    capture_output=True,
                    text=True
                )
                if result.stdout:
                    for line in result.stdout.splitlines():
                        if line.strip().startswith('{'):
                            f_out.write(line + '\n')
                            f_out.flush()
                if result.returncode == 0:
                    print(" Done.")
                else:
                    print(f" Failed (RC={result.returncode}). Stderr: {repr(result.stderr[:500])}")
            except Exception as e:
                print(f" Error: {e}")

if __name__ == '__main__':
    extract_all()
