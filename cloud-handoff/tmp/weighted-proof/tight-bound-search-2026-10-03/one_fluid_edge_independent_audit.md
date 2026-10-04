# Independent audit: one fluid edge, arbitrary bipartite heavy support

2026-10-03. This is a scoped scratch result, not a new unrestricted weighted
edge-coloring bound. The five-hour active exploration requirement is still
in progress.

The root agent independently checked
`two_matching_midpoint_single_fluid_edge_five_color_lemma.md` and
`arbitrary_heavy_bip_fluid_forest_extreme_face_reduction.md`.

The following steps check out:

1. With one positive fluid edge, a local extreme heavy vector lies on a face
   of the bipartite matching polytope of dimension at most one. Active load
   rows outside the fluid support are redundant along that face. The two
   endpoint load rows impose at most one compatibility condition after the
   one fluid variable is eliminated.
2. For a mixture with parameter p in [1/4,3/4], the scaled law has mass at
   least 1/5 on each original matching and on the empty matching. The
   three-color exchange therefore uses nonnegative masses and preserves
   every individual heavy-edge marginal, including a type common to both
   original matchings.
3. If a direct heavy uv edge occurs in a state, the two-state fluid Jensen
   gap is zero. Otherwise the prescribed endpoint colors extend along each
   connecting path, since u,v are on opposite shores and each such path has
   length at least three. Three colors permit arbitrary endpoint colors.
4. In the opposite-sign case, write A0-B0=d>0 and B1-A1=e>0. The Jensen gap
   is C_p=min(pd,(1-p)e). Thus C_p <= de/(d+e) <= (d+e)/4.
   The sorted-pairing gain obeys G >= max(0,d+e-1), by the two elementary
   bounds on absolute differences. Consequently 1+G >= 4 C_p.
5. For p outside [1/4,3/4], C_p <= min(p,1-p) <= 1/4, so the unmodified
   full-plus-empty law suffices. Convexity then extends the extreme-point
   result to the whole one-fluid-edge local polytope.

No gap was found in this restricted uncapped, divisible-edge statement.
It supplies neither a many-fluid-edge theorem nor a physical-edge palette.

## A failed interpolation, for future reference

Mixing the midpoint five-row law with an endpoint full-plus-empty law does
not prove the arbitrary-p result. For p=17/40 and residuals
(A0,A1,B0,B1)=(0,17/23,1,0), the fluid target is D=17/40. The proposed
interpolation gives five times the recourse

    1 + 2p*(17/23) = 749/460,

whereas 4D=782/460. The deficit is 33/460. This refutes only that
interpolation; the direct mass-1/5 exchange above repairs it.
