#!/usr/bin/env bash
# CI Smoke Check for Projective and Topology Import Spikes
set -e

echo "Running CI smoke check on projective and topology import spikes..."

echo "Building InfoGeometry.Projective.All..."
lake build InfoGeometry.Projective.All

echo "Building InfoGeometry.Topology.All..."
lake build InfoGeometry.Topology.All

echo "Smoke check passed successfully!"
