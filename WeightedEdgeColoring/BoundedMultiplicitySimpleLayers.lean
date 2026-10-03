import WeightedEdgeColoring.FiniteHarmonicPackets
import WeightedEdgeColoring.BPEdgeRestriction
import WeightedEdgeColoring.SimpleRoundingReduction

/-!
# Splitting a bounded-multiplicity bipartite multigraph into simple layers

This file records the exact lossless part of a possible reduction from
bounded-multiplicity multigraph rounding to simple-graph rounding.  Parallel
edges can be ranked inside each oriented endpoint pair, giving a bounded
family of weighted simple graphs.  The layers partition the indexed edges,
and arbitrary edge sums (in particular star weights and proposal loads) split
exactly over them.

The final example records the obstruction to finishing the reduction by
rounding the layers independently: feasible same-palette colorings of the
individual layers need not remain feasible after the layers are reunited.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}}

namespace Bipartition

/-- The ordered endpoint pair, from the `false` shore to the `true` shore. -/
def orientedPairKey (b : G.Bipartition) (e : G.E) : G.V × G.V :=
  (b.leftEndpoint e, b.rightEndpoint e)

/-- Edges with one fixed oriented endpoint pair. -/
abbrev OrientedPairFiber (b : G.Bipartition) (k : G.V × G.V) :=
  {e : G.E // b.orientedPairKey e = k}

/-- The same fiber represented as a finite set of original edge indices. -/
def orientedPairCell (b : G.Bipartition) (k : G.V × G.V) : Finset G.E :=
  Finset.univ.filter fun e ↦ b.orientedPairKey e = k

/-- Equal unordered endpoint pairs have equal oriented endpoint pairs in a
bipartite graph. -/
theorem orientedPair_eq_of_endpoints_eq (b : G.Bipartition) {e f : G.E}
    (hends : s(G.fst e, G.snd e) = s(G.fst f, G.snd f)) :
    b.leftEndpoint e = b.leftEndpoint f ∧
      b.rightEndpoint e = b.rightEndpoint f := by
  have hinc (x : G.V) (hx : G.Inc x e) : G.Inc x f := by
    rcases Sym2.eq_iff.mp hends with hdirect | hswap
    · rcases hx with hx | hx
      · exact Or.inl (hdirect.1.symm.trans hx)
      · exact Or.inr (hdirect.2.symm.trans hx)
    · rcases hx with hx | hx
      · exact Or.inr (hswap.1.symm.trans hx)
      · exact Or.inl (hswap.2.symm.trans hx)
  have hleft := b.leftEndpoint_eq_of_inc_of_side_eq_false
    (hinc (b.leftEndpoint e) (b.leftEndpoint_inc e))
    (b.side_leftEndpoint e)
  have hright := b.rightEndpoint_eq_of_inc_of_side_eq_true
    (hinc (b.rightEndpoint e) (b.rightEndpoint_inc e))
    (b.side_rightEndpoint e)
  exact ⟨hleft.symm, hright.symm⟩

end Bipartition

/-- A partition of the indexed edges into `L` layers, injective inside every
oriented endpoint-pair fiber. -/
structure BoundedPairSimpleLayering (G : WeightedMultigraph.{u})
    (b : G.Bipartition) (L : ℕ) where
  layer : G.E → Fin L
  eq_of_same_orientedPair_of_layer_eq : ∀ {e f : G.E},
    b.orientedPairKey e = b.orientedPairKey f →
    layer e = layer f → e = f

namespace BoundedPairSimpleLayering

variable {b : G.Bipartition} {L : ℕ}

/-- The fixed-pair embedding used to rank parallel edges. -/
def pairEmbedding
    (hmult : ∀ k, (b.orientedPairCell k).card ≤ L)
    (k : G.V × G.V) : b.OrientedPairFiber k ↪ Fin L :=
  (Fintype.equivFin (b.OrientedPairFiber k)).toEmbedding.trans
    (Fin.castLEEmb (by
      rw [Fintype.card_subtype]
      simpa [Bipartition.orientedPairCell] using hmult k))

/-- The layer index obtained by ranking an edge in its endpoint-pair fiber. -/
def rankedLayer
    (hmult : ∀ k, (b.orientedPairCell k).card ≤ L)
    (e : G.E) : Fin L :=
  pairEmbedding hmult (b.orientedPairKey e) ⟨e, rfl⟩

private theorem pairEmbedding_eq_val_of_key_eq
    (hmult : ∀ k, (b.orientedPairCell k).card ≤ L)
    {k l : G.V × G.V} (hkl : k = l)
    (e : b.OrientedPairFiber k) (f : b.OrientedPairFiber l)
    (hEq : pairEmbedding hmult k e = pairEmbedding hmult l f) :
    e.1 = f.1 := by
  subst l
  exact congrArg Subtype.val ((pairEmbedding hmult k).injective hEq)

/-- Every bipartite multigraph of oriented pair multiplicity at most `L`
has an exact decomposition into `L` simple layers. -/
def of_pairMultiplicity
    (hmult : ∀ k, (b.orientedPairCell k).card ≤ L) :
    G.BoundedPairSimpleLayering b L where
  layer := rankedLayer hmult
  eq_of_same_orientedPair_of_layer_eq := by
    intro e f hkey hlayer
    apply pairEmbedding_eq_val_of_key_eq hmult hkey
      (⟨e, rfl⟩ : b.OrientedPairFiber (b.orientedPairKey e))
      (⟨f, rfl⟩ : b.OrientedPairFiber (b.orientedPairKey f))
    simpa only [rankedLayer] using hlayer

variable (D : G.BoundedPairSimpleLayering b L)

/-- The original edge set in one layer. -/
def edgeSet (i : Fin L) : Finset G.E :=
  Finset.univ.filter fun e ↦ D.layer e = i

@[simp] theorem mem_edgeSet_iff (i : Fin L) (e : G.E) :
    e ∈ D.edgeSet i ↔ D.layer e = i := by
  simp [edgeSet]

/-- Distinct layers are disjoint. -/
theorem edgeSet_disjoint {i j : Fin L} (hij : i ≠ j) :
    Disjoint (D.edgeSet i) (D.edgeSet j) := by
  rw [Finset.disjoint_left]
  intro e hei hej
  exact hij ((D.mem_edgeSet_iff i e).mp hei |>.symm.trans
    ((D.mem_edgeSet_iff j e).mp hej))

/-- The union of all layers is the full indexed edge set. -/
theorem biUnion_edgeSet :
    (Finset.univ : Finset (Fin L)).biUnion D.edgeSet = Finset.univ := by
  ext e
  simp [edgeSet]

/-- One layer, retaining the original vertices, endpoints, and weights. -/
abbrev simpleLayer (i : Fin L) : WeightedSimpleGraph where
  V := G.V
  E := {e : G.E // D.layer e = i}
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst e := G.fst e.1
  snd e := G.snd e.1
  noLoop e := G.noLoop e.1
  simple := by
    intro e f hends
    apply Subtype.ext
    have horiented := b.orientedPair_eq_of_endpoints_eq hends
    exact D.eq_of_same_orientedPair_of_layer_eq
      (Prod.ext horiented.1 horiented.2) (e.2.trans f.2.symm)
  weight e := G.weight e.1
  weight_pos e := G.weight_pos e.1
  weight_le_one e := G.weight_le_one e.1

/-- Arbitrary edge sums split exactly over the simple layers. -/
theorem sum_simpleLayers (f : G.E → ℝ) :
    (∑ i : Fin L, ∑ e : (D.simpleLayer i).E, f e.1) =
      ∑ e : G.E, f e := by
  classical
  calc
    (∑ i : Fin L, ∑ e : (D.simpleLayer i).E, f e.1) =
        ∑ i : Fin L, ∑ e : G.E,
          if D.layer e = i then f e else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.sum_filter]
      symm
      exact Finset.sum_subtype
        ((Finset.univ : Finset G.E).filter fun e ↦ D.layer e = i)
        (by simp) f
    _ = ∑ e : G.E, ∑ i : Fin L,
          if D.layer e = i then f e else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e : G.E, f e := by
      apply Finset.sum_congr rfl
      intro e _he
      simp

/-- Star weights split exactly over the simple layers. -/
theorem sum_simpleLayer_starWeight (v : G.V) :
    (∑ i : Fin L, (D.simpleLayer i).starWeight v) = G.starWeight v := by
  classical
  have hlayer (i : Fin L) :
      (D.simpleLayer i).starWeight v =
        ∑ e : (D.simpleLayer i).E,
          if G.Inc v e.1 then G.weight e.1 else 0 := by
    simpa [WeightedSimpleGraph.asMultigraph] using
      ((D.simpleLayer i).asMultigraph.starWeight_eq_inc_sum v)
  have hG :
      G.starWeight v =
        ∑ e : G.E, if G.Inc v e then G.weight e else 0 :=
    G.starWeight_eq_inc_sum v
  rw [hG]
  simpa only [hlayer] using
    D.sum_simpleLayers (fun e ↦ if G.Inc v e then G.weight e else 0)

/-- The same exact decomposition applies to a color-dependent proposal load. -/
theorem sum_simpleLayer_proposalLoad {C : Type*} [Fintype C]
    (x : G.E → C → ℝ) (v : G.V) (c : C) :
    (∑ i : Fin L, ∑ e : (D.simpleLayer i).E,
      if G.Inc v e.1 then G.weight e.1 * x e.1 c else 0) =
      ∑ e : G.E,
        if G.Inc v e then G.weight e * x e c else 0 := by
  exact D.sum_simpleLayers
    (fun e ↦ if G.Inc v e then G.weight e * x e c else 0)

end BoundedPairSimpleLayering

namespace FiniteClassPacketDecomposition

variable {T : ℕ} {b : G.Bipartition} {classOf : G.E → Fin T}
    (D : G.FiniteClassPacketDecomposition b classOf)

/-- The residual graph supplied by finite harmonic packets has a canonical
bounded simple-layer decomposition. -/
def residualSimpleLayering :
    (G.edgeRestriction D.residualEdges).BoundedPairSimpleLayering
      (Bipartition.edgeRestriction G b D.residualEdges)
      (∑ a : Fin T, a.1) := by
  apply BoundedPairSimpleLayering.of_pairMultiplicity
  rintro ⟨u, v⟩
  have h := D.residual_pair_multiplicity_le u v
  let H := G.edgeRestriction D.residualEdges
  let bH := Bipartition.edgeRestriction G b D.residualEdges
  let embed : H.E ↪ G.E := ⟨Subtype.val, Subtype.val_injective⟩
  let F := bH.orientedPairCell (u, v)
  have hmap : F.map embed =
      D.residualEdges.filter fun e ↦
        b.leftEndpoint e = u ∧ b.rightEndpoint e = v := by
    ext e
    simp [F, embed, bH, H, Bipartition.orientedPairCell,
      Bipartition.orientedPairKey, Bipartition.edgeRestriction,
      Bipartition.leftEndpoint, Bipartition.rightEndpoint,
      and_comm, and_left_comm]
  calc
    (bH.orientedPairCell (u, v)).card = F.card := rfl
    _ = (F.map embed).card := (Finset.card_map _).symm
    _ = (D.residualEdges.filter fun e ↦
          b.leftEndpoint e = u ∧ b.rightEndpoint e = v).card :=
      congrArg Finset.card hmap
    _ ≤ ∑ a : Fin T, a.1 := h

end FiniteClassPacketDecomposition

/-! ## Why independent same-palette rounding cannot finish the reduction -/

/-- Two parallel edges of weight `3/5`. -/
def twoParallelThreeFifths : WeightedMultigraph where
  V := Bool
  E := Fin 2
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst _ := false
  snd _ := true
  noLoop _ := by decide
  weight _ := 3 / 5
  weight_pos _ := by norm_num
  weight_le_one _ := by norm_num

/-- Each singleton simple layer is feasible in the unique one-color palette,
but their union is not.  Thus independently rounded simple layers cannot in
general be merged without new coordination or extra colors. -/
theorem simpleLayer_samePalette_merge_obstruction :
    let color : twoParallelThreeFifths.E → Fin 1 := fun _ ↦ 0
    twoParallelThreeFifths.IsFeasibleOn {(0 : Fin 2)} color ∧
      twoParallelThreeFifths.IsFeasibleOn {(1 : Fin 2)} color ∧
      ¬ twoParallelThreeFifths.IsFeasibleOn
        ({(0 : Fin 2)} ∪ {(1 : Fin 2)}) color := by
  dsimp [twoParallelThreeFifths]
  constructor
  · intro v c
    fin_cases v <;> fin_cases c <;>
      norm_num [IsFeasibleOn, colorLoadOn, Inc]
  constructor
  · intro v c
    fin_cases v <;> fin_cases c <;>
      norm_num [IsFeasibleOn, colorLoadOn, Inc]
  · intro h
    have hload := h false (0 : Fin 1)
    norm_num [IsFeasibleOn, colorLoadOn, Inc] at hload

end

end WeightedMultigraph
end WeightedEdgeColoring
