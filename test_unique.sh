#!/bin/bash
while ps aux | grep -v grep | grep "lake build InfoGeometry"; do
  sleep 2
done
lean lean/InfoGeometry/Canonical/Archetypes/UniqueMaximum.lean
