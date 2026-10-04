"""Full-profit polar for two triangles sharing a mixed-type base edge."""

import json
import sys

import general_c5_chord_mixed_polar as core

core.EDGES = [(0, 1), (0, 1), (0, 2), (1, 2),
              (0, 3), (1, 3), (0, 2), (1, 3)]
core.NV = 4
core.D = len(core.EDGES)

if __name__ == "__main__":
    for arg in sys.argv[1:]:
        weights = [int(t) for t in arg.split(",")]
        assert len(weights) == core.D and min(weights) > 0
        print(json.dumps(core.score(weights)), flush=True)
