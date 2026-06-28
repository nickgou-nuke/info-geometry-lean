import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DATA = json.loads((ROOT / 'wallpaper17_repdata.json').read_text())
CASES = json.loads((ROOT / 'wallpaper17_cases.json').read_text())['cases']
ORDER_MAP = {c['name']: c['point_group_order'] for c in CASES}
TOKEN_GAP = {'0':'0','1':'1','-1':'-1','2':'2','-2':'-2','i':'E(4)','-i':'-E(4)','w3':'E(3)','w3^2':'E(3)^2','z6':'E(6)','z6^2':'E(6)^2','z6^4':'E(6)^4','z6^5':'E(6)^5'}


def run(cmd, cwd=None):
    p = subprocess.run(cmd, text=True, capture_output=True, cwd=cwd)
    return {'cmd': cmd, 'exit_code': p.returncode, 'stdout': p.stdout.strip(), 'stderr': p.stderr.strip()}


def build_gap_script():
    lines = []
    for name, info in DATA['point_groups'].items():
        classes = info['class_sizes']
        chars = info['characters']
        lines.append(f'classes_{name} := {classes};;')
        for i, row in enumerate(chars):
            vals = '[' + ','.join(TOKEN_GAP[x] for x in row) + ']'
            lines.append(f'char_{name}_{i} := {vals};;')
        lines.append(f'if Sum(classes_{name}) <> {info["order"]} then Error("{name} order failed"); fi;')
        for i, row in enumerate(chars):
            lines.append(f'if Sum(List([1..Length(classes_{name})], k -> classes_{name}[k] * char_{name}_{i}[k] * ComplexConjugate(char_{name}_{i}[k]))) <> {info["order"]} then Error("{name} norm failed"); fi;')
    for g, orbits in DATA['orbit_samples'].items():
        order = ORDER_MAP[g]
        for o in orbits:
            lines.append(f'if {o["stabilizer_order"]} * {o["orbit_size"]} <> {order} then Error("{g} orbit-stabilizer failed"); fi;')
    lines.append('Print("WALLPAPER17_REP_GAP_OK", "\\n");')
    lines.append('QUIT;')
    return '\n'.join(lines)


def main():
    repo = str(ROOT.parent.parent)
    results = {}
    results['sympy'] = run(['python3', str(ROOT / 'wallpaper_rep_sympy.py')], cwd=repo)
    results['sage'] = run(['/home/goutev/miniforge3/envs/sage/bin/python3', str(ROOT / 'wallpaper_rep_sage.py')], cwd=repo)
    with tempfile.TemporaryDirectory() as td:
        gap_path = Path(td) / 'wallpaper17_rep_generated.g'
        gap_path.write_text(build_gap_script())
        results['gap'] = run(['gap', '-q', str(gap_path)], cwd=repo)
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
