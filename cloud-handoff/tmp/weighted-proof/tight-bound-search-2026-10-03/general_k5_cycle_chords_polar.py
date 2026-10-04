"""Full-profit polar on a K5 with cycle edges and diagonal chords."""

import json
import sys

import general_c5_chord_mixed_polar as core

core.EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
              (0, 2), (1, 3), (2, 4), (3, 0), (4, 1)]
core.D = len(core.EDGES)

if __name__ == "__main__":
    for arg in sys.argv[1:]:
        weights = [int(t) for t in arg.split(",")]
        assert len(weights) == core.D and min(weights) > 0
        print(json.dumps(core.score(weights)), flush=True)
