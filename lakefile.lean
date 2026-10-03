import Lake
open Lake DSL

package «weighted-edge-coloring-challenges» where
  version := v!"0.2.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "a3a10db0e9d66acbebf76c5e6a135066525ac900"

lean_lib WeightedEdgeColoring where
lean_lib Challenge where
  roots := #[`Challenge]

@[default_target]
lean_lib Solutions where
  roots := #[`Solutions, `Verification]
