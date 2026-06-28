import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CASES = json.loads((ROOT / 'wallpaper17_cases.json').read_text())['cases']


def run(cmd, cwd=None):
    p = subprocess.run(cmd, text=True, capture_output=True, cwd=cwd)
    return {'cmd': cmd, 'exit_code': p.returncode, 'stdout': p.stdout.strip(), 'stderr': p.stderr.strip()}


def symmetry_keys(mc):
    return [k for k in mc if (k == 'symmetry' or (k.startswith('symmetry') and k[8:].isdigit())) and mc[k] is not None]


def matrix_cases():
    return [c for c in CASES if 'matrix_case' in c]


def gap_literal(rows):
    return '[' + ','.join('[' + ','.join(str(x) for x in row) + ']' for row in rows) + ']'


def m2_num(x):
    s = str(x)
    if '/' in s:
        a, b = s.split('/')
        return f'({a}/{b})'
    return s


def m2_matrix(rows):
    return 'matrix(QQ, {' + ','.join('{' + ','.join(m2_num(x) for x in row) + '}' for row in rows) + '})'


def build_gap_script():
    lines = ['id3 := IdentityMat(3, Rationals);;']
    for case in matrix_cases():
        name = case['name']
        mc = case['matrix_case']
        lines.append(f'tx_{name} := {gap_literal(mc["translation_x"])};;')
        lines.append(f'ty_{name} := {gap_literal(mc["translation_y"])};;')
        if 'translation_c' in mc:
            lines.append(f'tc_{name} := {gap_literal(mc["translation_c"])};;')
        for key in symmetry_keys(mc):
            lines.append(f'{key}_{name} := {gap_literal(mc[key])};;')
        for key in symmetry_keys(mc):
            idx = key[8:]
            target = mc.get('symmetry_square' + idx)
            sym = f'{key}_{name}'
            if target == 'identity':
                lines.append(f'if {sym} * {sym} <> id3 then Error("{name} {key} square failed"); fi;')
            elif target == 'tx':
                lines.append(f'if {sym} * {sym} <> tx_{name} then Error("{name} {key} square failed"); fi;')
            elif target == 'ty':
                lines.append(f'if {sym} * {sym} <> ty_{name} then Error("{name} {key} square failed"); fi;')
            elif target == 'tc' and 'translation_c' in mc:
                lines.append(f'if {sym} * {sym} <> tc_{name} then Error("{name} {key} square failed"); fi;')
            elif target == 'minus_identity_linear':
                lines.append(f'if {sym} * {sym} <> [[-1,0,0],[0,-1,0],[0,0,1]] then Error("{name} {key} square failed"); fi;')
            elif target == 'cube_identity':
                lines.append(f'if {sym}^3 <> id3 then Error("{name} {key} cube failed"); fi;')
            elif target == 'six_identity':
                lines.append(f'if {sym}^6 <> id3 then Error("{name} {key} sixth failed"); fi;')
            conj = mc.get('conjugation_target' + idx)
            if conj == 'tx_inv':
                lines.append(f'if {sym} * tx_{name} * {sym}^-1 <> tx_{name}^-1 then Error("{name} {key} conjugation failed"); fi;')
            elif conj == 'ty_inv':
                lines.append(f'if {sym} * ty_{name} * {sym}^-1 <> ty_{name}^-1 then Error("{name} {key} conjugation failed"); fi;')
            elif conj == 'swap' or conj == 'hex_mix':
                lines.append(f'if {sym} * tx_{name} * {sym}^-1 <> ty_{name} then Error("{name} {key} conjugation failed"); fi;')
        
    lines.append('Print("WALLPAPER17_GAP_OK", "\\n");')
    lines.append('QUIT;')
    return '\n'.join(lines)


def build_m2_script():
    lines = ['loadPackage "Dmodules";', 'I3 = id_(QQ^3);']
    for case in matrix_cases():
        name = case['name']
        mc = case['matrix_case']
        lines.append(f'tx{name} = {m2_matrix(mc["translation_x"])};')
        lines.append(f'ty{name} = {m2_matrix(mc["translation_y"])};')
        if 'translation_c' in mc:
            lines.append(f'tc{name} = {m2_matrix(mc["translation_c"])};')
        for key in symmetry_keys(mc):
            lines.append(f'{key}{name} = {m2_matrix(mc[key])};')
        for key in symmetry_keys(mc):
            idx = key[8:]
            target = mc.get('symmetry_square' + idx)
            sym = f'{key}{name}'
            if target == 'identity':
                lines.append(f'if {sym}*{sym} != I3 then error "{name} {key} square failed";')
            elif target == 'tx':
                lines.append(f'if {sym}*{sym} != tx{name} then error "{name} {key} square failed";')
            elif target == 'ty':
                lines.append(f'if {sym}*{sym} != ty{name} then error "{name} {key} square failed";')
            elif target == 'tc' and 'translation_c' in mc:
                lines.append(f'if {sym}*{sym} != tc{name} then error "{name} {key} square failed";')
            elif target == 'minus_identity_linear':
                lines.append('if ' + sym + '*' + sym + ' != matrix(QQ, {{-1,0,0},{0,-1,0},{0,0,1}}) then error "' + name + ' ' + key + ' square failed";')
            elif target == 'cube_identity':
                lines.append(f'if {sym}^3 != I3 then error "{name} {key} cube failed";')
            elif target == 'six_identity':
                lines.append(f'if {sym}^6 != I3 then error "{name} {key} sixth failed";')
            conj = mc.get('conjugation_target' + idx)
            if conj == 'tx_inv':
                lines.append(f'if {sym}*tx{name}*inverse {sym} != inverse tx{name} then error "{name} {key} conjugation failed";')
            elif conj == 'ty_inv':
                lines.append(f'if {sym}*ty{name}*inverse {sym} != inverse ty{name} then error "{name} {key} conjugation failed";')
            elif conj == 'swap' or conj == 'hex_mix':
                lines.append(f'if {sym}*tx{name}*inverse {sym} != ty{name} then error "{name} {key} conjugation failed";')
    lines.extend([
        'W = QQ[t, dt, WeylAlgebra => {t => dt}];',
        'N = cokernel matrix{{t*dt - dt*t - 1_W}};',
        'if numgens source presentation N != 1 then error "Dmodule sanity failed";',
        'print "WALLPAPER17_M2_OK";'
    ])
    return '\n'.join(lines)


def main():
    results = {}
    repo = str(ROOT.parent.parent)
    results['lean_source'] = run(['python3', str(ROOT / 'check_wallpaper_repr_source.py')], cwd=repo)
    results['sympy'] = run(['python3', str(ROOT / 'wallpaper_sympy.py')], cwd=repo)
    results['sage'] = run(['/home/goutev/miniforge3/envs/sage/bin/python3', str(ROOT / 'wallpaper_sage.py')], cwd=repo)
    results['rep_sympy'] = run(['python3', str(ROOT / 'wallpaper_rep_sympy.py')], cwd=repo)
    results['rep_sage'] = run(['/home/goutev/miniforge3/envs/sage/bin/python3', str(ROOT / 'wallpaper_rep_sage.py')], cwd=repo)
    results['rep_crosscheck'] = run(['python3', str(ROOT / 'run_wallpaper17_rep_harness.py')], cwd=repo)
    with tempfile.TemporaryDirectory() as td:
        gap_path = Path(td) / 'wallpaper17_generated.g'
        gap_path.write_text(build_gap_script())
        results['gap'] = run(['gap', '-q', str(gap_path)], cwd=repo)
    with tempfile.TemporaryDirectory() as td:
        m2_path = Path(td) / 'wallpaper17_generated.m2'
        m2_path.write_text(build_m2_script())
        results['m2'] = run(['M2', '--script', str(m2_path)], cwd=repo)
    summary = {
        'total_groups': len(CASES),
        'matrix_case_groups': [c['name'] for c in matrix_cases()],
        'tools': {k: {'exit_code': v['exit_code'], 'ok': v['exit_code'] == 0} for k, v in results.items()}
    }
    print(json.dumps({'summary': summary, 'results': results}, indent=2))


if __name__ == '__main__':
    main()
