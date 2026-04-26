#!/bin/bash
# 🎭 THE PAULI AUDITOR: HF PERMISSION RECLAMATION SCRIPT
# This script reclaims the 79GB root-locked HuggingFace cache for the goutev user.

set -e

CACHE_DIR="/home/goutev/.cache/huggingface"
USER_NAME="goutev"
GROUP_NAME="goutev"

echo "[pauli-fix] Analyzing permissions for $CACHE_DIR..."

if [ ! -d "$CACHE_DIR" ]; then
    echo "[pauli-fix] ERROR: Cache directory $CACHE_DIR not found."
    exit 1
fi

echo "[pauli-fix] REQUISITION: Please run the following command as root or with sudo:"
echo "----------------------------------------------------------------"
echo "sudo chown -R $USER_NAME:$GROUP_NAME $CACHE_DIR"
echo "sudo chmod -R 755 $CACHE_DIR"
echo "----------------------------------------------------------------"

# Optional Cleanup
if [ "$1" == "--clean" ]; then
    echo "[pauli-fix] Cleaning stale artifacts and partial downloads..."
    find "$CACHE_DIR/hub" -name "*.incomplete" -delete
    find "$CACHE_DIR/hub" -name "tmp*" -delete
    echo "[pauli-fix] Cleanup complete."
fi

echo "[pauli-fix] Once permissions are fixed, run 'sparkrun status' to verify residency."
