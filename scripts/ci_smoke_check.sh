#!/usr/bin/env bash
# CI Smoke Check for Projective and Topology Import Spikes
set -e

echo "Running CI smoke check on projective and topology import spikes..."

echo "Building InfoGeometry.Projective.All..."
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Projective.All

echo "Building InfoGeometry.Topology.All..."
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Topology.All

echo "Smoke check passed successfully!"
