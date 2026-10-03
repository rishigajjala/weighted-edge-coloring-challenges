import WeightedEdgeColoring.PartialCompletion

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u v

variable (G : WeightedMultigraph.{u})
variable {ι : Type v} [DecidableEq ι]

/-!
# Merging a finite family of disjoint palettes

The first-difference reduction colors several pairwise disjoint edge layers
with separate palettes.  This file packages the repeated use of
`merge_feasibleOn`.  One unused color is carried through the induction so
that the empty family has a total coloring function; the resulting additive
one is harmless in every asymptotic application.
-/

/-- The empty edge set is feasible with the one-color fallback palette. -/
theorem empty_isFeasibleOn_one :
    G.IsFeasibleOn ∅ (fun _e : G.E ↦ (0 : Fin 1)) := by
  intro v i
  simp [colorLoadOn]

/-- Pairwise disjoint edge sets indexed by `S` can be colored with the sum of
their separate palette sizes, plus one fallback color. -/
theorem exists_merge_feasibleOn_finset
    (S : Finset ι) (part : ι → Finset G.E) (q : ι → ℕ)
    (color : ∀ i, G.E → Fin (q i))
    (hfeasible : ∀ i ∈ S, G.IsFeasibleOn (part i) (color i))
    (hdisjoint : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (part i) (part j)) :
    ∃ merged : G.E → Fin (1 + ∑ i ∈ S, q i),
      G.IsFeasibleOn (S.biUnion part) merged := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨fun _e ↦ (0 : Fin 1), G.empty_isFeasibleOn_one⟩
  | @insert a S ha ih =>
      have hfeasibleS : ∀ i ∈ S, G.IsFeasibleOn (part i) (color i) := by
        intro i hi
        exact hfeasible i (Finset.mem_insert_of_mem hi)
      have hdisjointS :
          ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (part i) (part j) := by
        intro i hi j hj hij
        exact hdisjoint i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij
      obtain ⟨left, hleft⟩ := ih hfeasibleS hdisjointS
      have haFeasible : G.IsFeasibleOn (part a) (color a) :=
        hfeasible a (by simp)
      have hfamilyDisjoint : Disjoint (S.biUnion part) (part a) := by
        rw [Finset.disjoint_left]
        intro e heS hea
        rw [Finset.mem_biUnion] at heS
        obtain ⟨i, hiS, hei⟩ := heS
        have hai : a ≠ i := by
          intro hai
          subst i
          exact ha hiS
        exact Finset.disjoint_left.mp
          (hdisjoint i (Finset.mem_insert_of_mem hiS) a (by simp) hai.symm)
          hei hea
      obtain ⟨merged, hmerged⟩ :=
        G.merge_feasibleOn (S.biUnion part) (part a) hfamilyDisjoint
          left hleft (color a) haFeasible
      have hpalette :
          (1 + ∑ i ∈ S, q i) + q a =
            1 + ∑ i ∈ insert a S, q i := by
        simp [ha]
        omega
      let merged' : G.E → Fin (1 + ∑ i ∈ insert a S, q i) :=
        fun e ↦ Fin.cast hpalette (merged e)
      refine ⟨merged', ?_⟩
      have hload (v : G.V) (c : Fin ((1 + ∑ i ∈ S, q i) + q a)) :
          G.colorLoadOn ((insert a S).biUnion part) merged' v
              (Fin.cast hpalette c) =
            G.colorLoadOn ((S.biUnion part) ∪ part a) merged v c := by
        unfold colorLoadOn merged'
        rw [Finset.biUnion_insert]
        rw [Finset.union_comm (part a) (S.biUnion part)]
        apply Finset.sum_congr rfl
        intro e he
        simp only [Fin.cast_inj]
      intro v c
      let c' : Fin ((1 + ∑ i ∈ S, q i) + q a) := Fin.cast hpalette.symm c
      have hc : Fin.cast hpalette c' = c := by
        simp [c']
      rw [← hc, hload]
      exact hmerged v c'

/-- Full colorings of pairwise disjoint restrictions merge into a feasible
coloring of their union, with one additive fallback color. -/
theorem exists_merge_restrictedColorings_finset
    (S : Finset ι) (part : ι → Finset G.E) (q : ι → ℕ)
    (hq : ∀ i, 0 < q i)
    (color : ∀ i, (G.edgeRestriction (part i)).E → Fin (q i))
    (hcolor : ∀ i ∈ S,
      (G.edgeRestriction (part i)).IsWeightedColoring (color i))
    (hdisjoint : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (part i) (part j)) :
    ∃ merged : G.E → Fin (1 + ∑ i ∈ S, q i),
      G.IsFeasibleOn (S.biUnion part) merged := by
  classical
  let lifted : ∀ i, G.E → Fin (q i) := fun i ↦
    G.liftRestrictedColor (hq i) (part i) (color i)
  have hlifted : ∀ i ∈ S, G.IsFeasibleOn (part i) (lifted i) := by
    intro i hi
    simp only [lifted]
    exact G.feasibleOn_liftRestrictedColor (hq i) (part i) (color i)
      (hcolor i hi)
  exact G.exists_merge_feasibleOn_finset S part q lifted hlifted hdisjoint

end WeightedMultigraph
end WeightedEdgeColoring
