#!/bin/bash
set -e

echo "======================================"
echo "1. Running Python RFS Compiler..."
echo "======================================"
python3 scratch/generate_m2_pipeline.py

echo ""
echo "======================================"
echo "2. Running Macaulay2 Engine Validation..."
echo "======================================"
M2 --script scratch/generated_pipeline.m2

echo ""
echo "======================================"
echo "3. Pipeline Complete"
echo "======================================"
