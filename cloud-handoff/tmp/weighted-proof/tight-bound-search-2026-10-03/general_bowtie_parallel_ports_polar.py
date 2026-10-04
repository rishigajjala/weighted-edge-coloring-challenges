"""Bowtie with one extra parallel port type on each center spoke branch."""

import json
import sys

import general_c5_chord_mixed_polar as core

core.EDGES = [(0, 1), (1, 2), (2, 0),
              (0, 3), (3, 4), (4, 0),
              (0, 1), (0, 3)]
core.D = len(core.EDGES)

if __name__ == "__main__":
    for arg in sys.argv[1:]:
        weights = [int(t) for t in arg.split(",")]
        assert len(weights) == core.D and min(weights) > 0
        print(json.dumps(core.score(weights)), flush=True)
