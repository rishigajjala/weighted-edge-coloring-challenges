import WeightedEdgeColoring.SubtwoContraction
import WeightedEdgeColoring.BoundedMultiplicityPairCodegree

/-!
# Fixed pair multiplicity survives bounded block contraction

If residual objects have at most `L` indices on each original vertex pair,
contracting blocks of at most `B` original vertices gives at most `B²L`
objects on each quotient pair.  This is the finite counting bridge needed
after per-original-pair packetization.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

theorem subtwoQuotient_pairMultiplicityAtMost
    (block : G.V → Q) {B L : ℕ}
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ B)
    (hmult : G.PairMultiplicityAtMost L) :
    (G.subtwoQuotient block).PairMultiplicityAtMost (B * B * L) := by
  classical
  intro q r
  let H := G.subtwoQuotient block
  let emb : H.E ↪ G.E := ⟨Subtype.val, Subtype.val_injective⟩
  let F := H.endpointPairCell q r
  let U := (G.subtwoFiber block q).product (G.subtwoFiber block r)
  let V := U.biUnion fun p ↦ G.endpointPairCell p.1 p.2
  have hsub : F.map emb ⊆ V := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    have hends : s(block (G.fst f.1), block (G.snd f.1)) = s(q, r) := by
      simpa [H, WeightedMultigraph.endpoints] using
        ((H.mem_endpointPairCell_iff q r f).mp hf)
    rcases (Sym2.eq_iff).mp hends with hd | hs
    · apply Finset.mem_biUnion.mpr
      refine ⟨(G.fst f.1, G.snd f.1), ?_, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨(G.mem_subtwoFiber block q _).mpr hd.1,
            (G.mem_subtwoFiber block r _).mpr hd.2⟩
      · exact (G.mem_endpointPairCell_iff _ _ _).mpr rfl
    · apply Finset.mem_biUnion.mpr
      refine ⟨(G.snd f.1, G.fst f.1), ?_, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨(G.mem_subtwoFiber block q _).mpr hs.2,
            (G.mem_subtwoFiber block r _).mpr hs.1⟩
      · exact (G.mem_endpointPairCell_iff _ _ _).mpr (by
          change s(G.fst f.1, G.snd f.1) =
            s(G.snd f.1, G.fst f.1)
          exact Sym2.eq_swap)
  have hcardV : V.card ≤ U.card * L := by
    calc
      V.card ≤ ∑ p ∈ U, (G.endpointPairCell p.1 p.2).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ U, L := by
        apply Finset.sum_le_sum
        intro p hp
        exact hmult p.1 p.2
      _ = U.card * L := by simp
  have hcardU : U.card ≤ B * B := by
    dsimp [U]
    rw [Finset.card_product]
    exact Nat.mul_le_mul (hfiber q) (hfiber r)
  change F.card ≤ B * B * L
  calc
    F.card = (F.map emb).card := (Finset.card_map emb).symm
    _ ≤ V.card := Finset.card_le_card hsub
    _ ≤ U.card * L := hcardV
    _ ≤ B * B * L := Nat.mul_le_mul_right L hcardU

theorem edgeRestriction_subtwoQuotient_pairMultiplicityAtMost
    (R : Finset G.E) (block : G.V → Q) {B L : ℕ}
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ B)
    (hresidual : (G.edgeRestriction R).PairMultiplicityAtMost L) :
    ((G.edgeRestriction R).subtwoQuotient block).PairMultiplicityAtMost
      (B * B * L) := by
  have hfiber' : ∀ q,
      ((G.edgeRestriction R).subtwoFiber block q).card ≤ B := by
    intro q
    simpa [WeightedMultigraph.subtwoFiber] using hfiber q
  exact (G.edgeRestriction R).subtwoQuotient_pairMultiplicityAtMost
    block hfiber' hresidual

theorem edgeRestriction_subtwoQuotient_pairMultiplicityAtMost_five
    (R : Finset G.E) (block : G.V → Q) {L : ℕ}
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    (hresidual : (G.edgeRestriction R).PairMultiplicityAtMost L) :
    ((G.edgeRestriction R).subtwoQuotient block).PairMultiplicityAtMost
      (25 * L) := by
  simpa using
    (G.edgeRestriction_subtwoQuotient_pairMultiplicityAtMost
      R block hfiber hresidual)

end WeightedEdgeColoring.WeightedMultigraph
