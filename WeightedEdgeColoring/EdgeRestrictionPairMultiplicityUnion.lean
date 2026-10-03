import WeightedEdgeColoring.BoundedMultiplicityWholeEdgeRounding
import WeightedEdgeColoring.BPEdgeRestriction

/-!
# Pair multiplicity for a union of two edge restrictions

The joint residual used in the bipartite `bp(G)` proof is the disjoint union
of a finite-harmonic residual and an endpoint-simple tiny remainder.  This
file records the elementary fact that the endpoint multiplicities add.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}}

/-- Splitting a restricted edge set into two disjoint parts adds their
unordered endpoint-pair multiplicity bounds. -/
theorem edgeRestriction_union_pairMultiplicityAtMost
    (A B : Finset G.E) (hdisj : Disjoint A B) {L₁ L₂ : ℕ}
    (hA : (G.edgeRestriction A).PairMultiplicityAtMost L₁)
    (hB : (G.edgeRestriction B).PairMultiplicityAtMost L₂) :
    (G.edgeRestriction (A ∪ B)).PairMultiplicityAtMost (L₁ + L₂) := by
  classical
  intro u v
  let H := G.edgeRestriction (A ∪ B)
  let F : Finset H.E := H.endpointPairCell u v
  let FA : Finset H.E := F.filter fun e ↦ e.1 ∈ A
  let FB : Finset H.E := F.filter fun e ↦ e.1 ∈ B
  have hF : F = FA ∪ FB := by
    ext e
    have heAB : e.1 ∈ A ∪ B := e.2
    constructor
    · intro heF
      rcases Finset.mem_union.mp heAB with heA | heB
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heF, heA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heF, heB⟩)
    · intro he
      rcases Finset.mem_union.mp he with heA | heB
      · exact (Finset.mem_filter.mp heA).1
      · exact (Finset.mem_filter.mp heB).1
  have hFAB : Disjoint FA FB := by
    rw [Finset.disjoint_left]
    intro e heA heB
    have heA' : e.1 ∈ A := (Finset.mem_filter.mp heA).2
    have heB' : e.1 ∈ B := (Finset.mem_filter.mp heB).2
    exact Finset.disjoint_left.mp hdisj heA' heB'
  have hFAcard : FA.card =
      ((G.edgeRestriction A).endpointPairCell u v).card := by
    apply Finset.card_bij (fun e he ↦
      (⟨e.1, (Finset.mem_filter.mp he).2⟩ : (G.edgeRestriction A).E))
    · intro e he
      have heF : e ∈ F := (Finset.mem_filter.mp he).1
      have hends : H.endpoints e = s(u, v) :=
        (H.mem_endpointPairCell_iff u v e).mp heF
      apply (G.edgeRestriction A).mem_endpointPairCell_iff u v _ |>.mpr
      simpa [H, WeightedMultigraph.endpoints] using hends
    · intro e he f hf hef
      apply Subtype.ext
      exact congrArg (fun z : (G.edgeRestriction A).E ↦ z.1) hef
    · intro e he
      let eH : H.E := ⟨e.1, Finset.mem_union_left B e.2⟩
      refine ⟨eH, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, e.2⟩
        have hends : (G.edgeRestriction A).endpoints e = s(u, v) :=
          ((G.edgeRestriction A).mem_endpointPairCell_iff u v e).mp he
        apply H.mem_endpointPairCell_iff u v eH |>.mpr
        simpa [H, eH, WeightedMultigraph.endpoints] using hends
      · rfl
  have hFBcard : FB.card =
      ((G.edgeRestriction B).endpointPairCell u v).card := by
    apply Finset.card_bij (fun e he ↦
      (⟨e.1, (Finset.mem_filter.mp he).2⟩ : (G.edgeRestriction B).E))
    · intro e he
      have heF : e ∈ F := (Finset.mem_filter.mp he).1
      have hends : H.endpoints e = s(u, v) :=
        (H.mem_endpointPairCell_iff u v e).mp heF
      apply (G.edgeRestriction B).mem_endpointPairCell_iff u v _ |>.mpr
      simpa [H, WeightedMultigraph.endpoints] using hends
    · intro e he f hf hef
      apply Subtype.ext
      exact congrArg (fun z : (G.edgeRestriction B).E ↦ z.1) hef
    · intro e he
      let eH : H.E := ⟨e.1, Finset.mem_union_right A e.2⟩
      refine ⟨eH, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, e.2⟩
        have hends : (G.edgeRestriction B).endpoints e = s(u, v) :=
          ((G.edgeRestriction B).mem_endpointPairCell_iff u v e).mp he
        apply H.mem_endpointPairCell_iff u v eH |>.mpr
        simpa [H, eH, WeightedMultigraph.endpoints] using hends
      · rfl
  change F.card ≤ L₁ + L₂
  rw [hF, Finset.card_union_of_disjoint hFAB, hFAcard, hFBcard]
  exact Nat.add_le_add (hA u v) (hB u v)

/-- The oriented endpoint-pair form used by the bipartite rounder follows
from an unordered pair-multiplicity bound. -/
theorem Bipartition.orientedPairCell_card_le_of_pairMultiplicityAtMost
    (b : G.Bipartition) {L : ℕ} (hmult : G.PairMultiplicityAtMost L)
    (k : G.V × G.V) :
    (b.orientedPairCell k).card ≤ L := by
  let F := b.orientedPairCell k
  have hsubset : F ⊆ G.endpointPairCell k.1 k.2 := by
    intro e he
    have hkey : b.orientedPairKey e = k := (Finset.mem_filter.mp he).2
    have hleft : b.leftEndpoint e = k.1 := congrArg Prod.fst hkey
    have hright : b.rightEndpoint e = k.2 := congrArg Prod.snd hkey
    apply (G.mem_endpointPairCell_iff_endpointPairMatches k.1 k.2 e).2
    by_cases hside : b.side (G.fst e) = false
    · left
      simpa [Bipartition.orientedPairKey, Bipartition.leftEndpoint,
        Bipartition.rightEndpoint, hside] using
          And.intro hleft.symm hright.symm
    · right
      have htrue : b.side (G.fst e) = true := by
        cases h : b.side (G.fst e) <;> simp_all
      have hsnd : b.side (G.snd e) = false := by
        cases hs : b.side (G.snd e) with
        | false => rfl
        | true =>
            have hop := b.opposite e
            exfalso
            exact hop (by rw [htrue, hs])
      simpa [Bipartition.orientedPairKey, Bipartition.leftEndpoint,
        Bipartition.rightEndpoint, htrue, hsnd] using
          And.intro hleft.symm hright.symm
  exact (Finset.card_le_card hsubset).trans (hmult k.1 k.2)

end

end WeightedMultigraph
end WeightedEdgeColoring
