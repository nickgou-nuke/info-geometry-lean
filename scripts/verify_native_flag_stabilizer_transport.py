"""Independent check of the GAP stabilizer-to-PC transport certificate."""

import subprocess


def main() -> None:
    p = subprocess.run(
        ["/home/goutev/miniforge3/envs/sage/bin/gap", "-b", "-q",
         "scripts/verify_native_flag_stabilizer_transport.g"],
        check=True, capture_output=True, text=True,
    )
    out = p.stdout
    required = (
        "TRANSPORT_STABILIZER_EQUALS_PC=PASS",
        "TRANSPORT_STABILIZER_SIZE=64",
        "TRANSPORT_ALL_64_WITNESSES=PASS",
    )
    for marker in required:
        if marker not in out:
            raise SystemExit(f"missing GAP marker: {marker}")
    witnesses = [line for line in out.splitlines()
                 if line.startswith("TRANSPORT_WITNESS ")]
    if len(witnesses) != 64:
        raise SystemExit(f"expected 64 witnesses, got {len(witnesses)}")
    if len(set(witnesses)) != 64:
        raise SystemExit("witness list is not injective")
    print("PYTHON_TRANSPORT_CERTIFICATE=PASS")
    print("PYTHON_WITNESS_COUNT=64")


if __name__ == "__main__":
    main()
