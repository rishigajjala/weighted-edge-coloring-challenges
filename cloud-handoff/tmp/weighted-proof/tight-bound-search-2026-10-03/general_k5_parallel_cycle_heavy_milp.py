"""Finite-profit separation for K5 with two heavy types on cycle sides."""

import sys

import general_k5_parallel_chords_milp as search

search.core.EDGES = [(0, 1), (0, 1), (1, 2), (1, 2),
                     (2, 3), (2, 3), (3, 4), (3, 4),
                     (4, 0), (4, 0),
                     (0, 2), (1, 3), (2, 4), (3, 0), (4, 1)]
search.core.D = len(search.core.EDGES)

if __name__ == "__main__":
    weights = [int(t) for t in sys.argv[1].split(",")]
    search.run(weights, int(sys.argv[2]), int(sys.argv[3]))
