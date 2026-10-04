# Correlated blocker laws need not lift to mean-preserving physical heavy laws

**Status (2026-10-03):** exact obstruction to one proposed reduction, not a counterexample to the heterogeneous heavy-plus-fluid transfer itself.

One might split each proposed physical heavy marginal `t_e` of weight `w_e` into a binary full-blocker marginal `z_e=w_e t_e` and a nonblocker marginal `(1-w_e)t_e`. The colored-copy bipartite matching polytope is integral, so any such aggregate marginals have a nested matching law `(B⊆M)` with physical matching `M` and blocker matching `B`. However, to use concavity of fluid recourse to infer a physical lower bound from binary blocker recourse, the stronger **conditional mean-preserving** property is required:

`P(e∈B | M)=w_e` for every full physical matching state `M` containing edge `e`.

Blocker colors may be arbitrarily correlated within `M`; conditional independence is not required. Even with that freedom, **not every** blocker law with edge marginals `z` has a conditional mean-preserving extension.

Take two disjoint physical heavy edges with scaled marginals `t_1=0.675`, `t_2=0.375`, weights `w_1=0.51`, `w_2=1`. Their blocker marginals are `z_1=0.34425`, `z_2=0.375`. The following is a feasible binary blocker matching law:

`P(B={1,2})=0.34425`, `P(B={2})=0.03075`, `P(B=∅)=0.625`.

Suppose it lifted to `(B⊆M)` with physical marginals `t` and the conditional property. Whenever both blocker edges are present, both physical edges are present. Conditioning on the full physical matching state containing both gives

`P(B={1,2})≤P(1∈B,\,1,2∈M)=w_1 P(1,2∈M)≤w_1 P(2∈M)=0.51*0.375=0.19125`,

contradicting `0.34425`. (The first inequality is equality if there are only these two edges.) Thus matching-polytope integrality of colored blocker copies does not by itself provide the martingale coupling needed for Jensen. This does not rule out finding a different, q-specific blocker law that *does* lift and has enough fluid recourse.
