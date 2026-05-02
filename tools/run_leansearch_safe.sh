#!/bin/bash
# run_leansearch_safe.sh - Hardened startup for LeanSearch-PS-inference

# Safe defaults based on hardening pass
export LEANSEARCH_DEVICE=${LEANSEARCH_DEVICE:-cpu}
export LEANSEARCH_MAX_LENGTH=${LEANSEARCH_MAX_LENGTH:-1024}
export LEANSEARCH_MAX_NUM=${LEANSEARCH_MAX_NUM:-8}
export LEANSEARCH_THREADED=${LEANSEARCH_THREADED:-0}
export LEANSEARCH_MAX_QUERY_CHARS=${LEANSEARCH_MAX_QUERY_CHARS:-8000}
export LEANSEARCH_DEFAULT_NUM=${LEANSEARCH_DEFAULT_NUM:-5}
export LEANSEARCH_HOST=${LEANSEARCH_HOST:-0.0.0.0}

# Paths to the sibling repository components
PYTHON_BIN="/home/goutev/repos/info-geometry-lean/REAL-Prover/.venv/bin/python"
SERVER_PY="/home/goutev/repos/info-geometry-lean/REAL-Prover/LeanSearch-PS-inference/server.py"

if [ ! -f "$PYTHON_BIN" ]; then
    echo "Error: Python binary not found at $PYTHON_BIN"
    exit 1
fi

if [ ! -f "$SERVER_PY" ]; then
    echo "Error: Server script not found at $SERVER_PY"
    exit 1
fi

echo "--------------------------------------------------------"
echo "Starting LeanSearch Inference Server (Hardened Profile)"
echo "--------------------------------------------------------"
echo "Host:       $LEANSEARCH_HOST"
echo "Device:     $LEANSEARCH_DEVICE"
echo "Max Length: $LEANSEARCH_MAX_LENGTH"
echo "Max Num:    $LEANSEARCH_MAX_NUM"
echo "Threaded:   $LEANSEARCH_THREADED"
echo "--------------------------------------------------------"

# Launch the server with the hardened profile
exec "$PYTHON_BIN" "$SERVER_PY" "$@"
