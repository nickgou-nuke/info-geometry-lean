#!/usr/bin/env python3
"""4D Klein-bottle shadow sampler.

This script samples the smooth 4D immersion

    X = (R + r cos v) cos u
    Y = (R + r cos v) sin u
    Z = r sin v cos(u/2)
    W = r sin v sin(u/2)

and projects it into 3D.  It also exposes the Klein four-group actions used by
`KleinFourProjection.py`, then writes animation-style CSV frames or a simple OBJ
mesh when requested.

No plotting dependency is required; the output is deliberately plain data.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, List, Optional, Tuple


Vec4 = Tuple[float, float, float, float]
Vec3 = Tuple[float, float, float]
V4Action = Callable[[Vec4], Vec4]


@dataclass(frozen=True)
class Sample:
    i: int
    j: int
    u: float
    v: float
    p4: Vec4
    p3: Vec3


def klein4(u: float, v: float, radius: float = 3.0, tube: float = 1.0) -> Vec4:
    """Smooth 4D Klein-type immersion."""
    return (
        (radius + tube * math.cos(v)) * math.cos(u),
        (radius + tube * math.cos(v)) * math.sin(u),
        tube * math.sin(v) * math.cos(u / 2.0),
        tube * math.sin(v) * math.sin(u / 2.0),
    )


def v4_id(p: Vec4) -> Vec4:
    return p


def v4_a(p: Vec4) -> Vec4:
    x, y, z, w = p
    return (x, y, -z, -w)


def v4_b(p: Vec4) -> Vec4:
    x, y, z, w = p
    return (-x, -y, z, w)


def v4_c(p: Vec4) -> Vec4:
    x, y, z, w = p
    return (-x, -y, -z, -w)


V4_ACTIONS = {
    "id": v4_id,
    "a": v4_a,
    "b": v4_b,
    "c": v4_c,
}


def project_orthographic(p: Vec4) -> Vec3:
    x, y, z, _w = p
    return (x, y, z)


def project_perspective(p: Vec4, depth: float = 4.0) -> Vec3:
    x, y, z, w = p
    scale = depth + w
    if abs(scale) < 1e-12:
        raise ZeroDivisionError("projection depth crosses W = -depth")
    return (x / scale, y / scale, z / scale)


def sample_grid(
    u_steps: int,
    v_steps: int,
    radius: float,
    tube: float,
    action: V4Action,
    projection: Callable[[Vec4], Vec3],
) -> List[Sample]:
    samples: List[Sample] = []
    for i in range(u_steps):
        u = 2.0 * math.pi * i / u_steps
        for j in range(v_steps):
            v = 2.0 * math.pi * j / v_steps
            p4 = action(klein4(u, v, radius, tube))
            samples.append(Sample(i=i, j=j, u=u, v=v, p4=p4, p3=projection(p4)))
    return samples


def mesh_faces(u_steps: int, v_steps: int) -> Iterable[Tuple[int, int, int, int]]:
    """Quad faces using OBJ 1-based indexing."""
    for i in range(u_steps):
        for j in range(v_steps):
            a = i * v_steps + j + 1
            b = ((i + 1) % u_steps) * v_steps + j + 1
            c = ((i + 1) % u_steps) * v_steps + ((j + 1) % v_steps) + 1
            d = i * v_steps + ((j + 1) % v_steps) + 1
            yield (a, b, c, d)


def write_csv(path: Path, samples: List[Sample]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["i", "j", "u", "v", "x4", "y4", "z4", "w4", "x3", "y3", "z3"])
        for s in samples:
            writer.writerow([s.i, s.j, s.u, s.v, *s.p4, *s.p3])


def write_obj(path: Path, samples: List[Sample], u_steps: int, v_steps: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        handle.write("# 3D shadow of the 4D Klein-bottle immersion\n")
        for s in samples:
            handle.write(f"v {s.p3[0]:.12g} {s.p3[1]:.12g} {s.p3[2]:.12g}\n")
        for face in mesh_faces(u_steps, v_steps):
            handle.write("f " + " ".join(str(idx) for idx in face) + "\n")


def write_frames(
    out_dir: Path,
    frames: int,
    u_steps: int,
    v_steps: int,
    radius: float,
    tube: float,
    perspective_depth: Optional[float],
) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    for frame in range(frames):
        angle = 2.0 * math.pi * frame / max(frames, 1)
        ca, sa = math.cos(angle), math.sin(angle)

        def rotate_w_shadow(p: Vec4) -> Vec4:
            x, y, z, w = p
            return (x, y, ca * z - sa * w, sa * z + ca * w)

        projection = (
            project_orthographic
            if perspective_depth is None
            else lambda p, d=perspective_depth: project_perspective(p, d)
        )
        samples = sample_grid(u_steps, v_steps, radius, tube, rotate_w_shadow, projection)
        write_csv(out_dir / f"frame_{frame:04d}.csv", samples)


def verify_v4_relations() -> None:
    p = (1.25, -2.0, 0.5, -0.75)
    assert v4_a(v4_a(p)) == p
    assert v4_b(v4_b(p)) == p
    assert v4_c(v4_c(p)) == p
    assert v4_a(v4_b(p)) == v4_b(v4_a(p)) == v4_c(p)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--u-steps", type=int, default=48)
    parser.add_argument("--v-steps", type=int, default=24)
    parser.add_argument("--radius", type=float, default=3.0)
    parser.add_argument("--tube", type=float, default=1.0)
    parser.add_argument("--action", choices=sorted(V4_ACTIONS), default="id")
    parser.add_argument("--perspective-depth", type=float, default=None)
    parser.add_argument("--csv", type=Path, default=None)
    parser.add_argument("--obj", type=Path, default=None)
    parser.add_argument("--frames-dir", type=Path, default=None)
    parser.add_argument("--frames", type=int, default=0)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.u_steps < 3 or args.v_steps < 3:
        raise SystemExit("u-steps and v-steps must both be at least 3")
    verify_v4_relations()

    projection = (
        project_orthographic
        if args.perspective_depth is None
        else lambda p: project_perspective(p, args.perspective_depth)
    )
    samples = sample_grid(
        args.u_steps,
        args.v_steps,
        args.radius,
        args.tube,
        V4_ACTIONS[args.action],
        projection,
    )

    if args.csv is not None:
        write_csv(args.csv, samples)
    if args.obj is not None:
        write_obj(args.obj, samples, args.u_steps, args.v_steps)
    if args.frames_dir is not None and args.frames > 0:
        write_frames(
            args.frames_dir,
            args.frames,
            args.u_steps,
            args.v_steps,
            args.radius,
            args.tube,
            args.perspective_depth,
        )

    xs = [s.p3[0] for s in samples]
    ys = [s.p3[1] for s in samples]
    zs = [s.p3[2] for s in samples]
    print("Klein shadow pipeline OK")
    print(f"samples={len(samples)} action={args.action}")
    print(f"x=[{min(xs):.6g}, {max(xs):.6g}]")
    print(f"y=[{min(ys):.6g}, {max(ys):.6g}]")
    print(f"z=[{min(zs):.6g}, {max(zs):.6g}]")


if __name__ == "__main__":
    main()
