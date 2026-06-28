import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CASES = json.loads((ROOT / 'tools/wallpaper/wallpaper17_cases.json').read_text())['cases']
TEXT = (ROOT / 'lean/InfoGeometry/Topology/WallpaperRepresentations.lean').read_text()


def expect(snippet):
    assert snippet in TEXT, snippet


def main():
    expect('inductive WallpaperGroup')
    expect('theorem wallpaperGroup_card : Fintype.card WallpaperGroup = 17 := by')
    for case in CASES:
        expect(f'| .{case["name"]}')
    expect('| .p1 => .C1')
    expect('| .p2 => .C2')
    expect('| .pm | .pg | .cm => .D1')
    expect('| .pmm | .pmg | .pgg | .cmm => .V4')
    expect('| .p4 => .C4')
    expect('| .p4m | .p4g => .D4')
    expect('| .p3 => .C3')
    expect('| .p3m1 | .p31m => .D3')
    expect('| .p6 => .C6')
    expect('| .p6m => .D6')
    expect('| .C1 => ⟨1, 0, 1⟩')
    expect('| .C2 | .D1 => ⟨2, 0, 2⟩')
    expect('| .V4 | .C4 => ⟨4, 0, 4⟩')
    expect('| .D4 => ⟨4, 1, 5⟩')
    expect('| .C3 => ⟨3, 0, 3⟩')
    expect('| .D3 => ⟨2, 1, 3⟩')
    expect('| .C6 => ⟨6, 0, 6⟩')
    expect('| .D6 => ⟨4, 2, 6⟩')
    print({'total_groups': len(CASES), 'lean_source_audit': 'ok'})
    print('WALLPAPER17_LEAN_SOURCE_OK')


if __name__ == '__main__':
    main()
