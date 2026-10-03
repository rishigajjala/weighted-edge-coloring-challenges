import WeightedEdgeColoring.BoundedMultiplicityWholeEdgeRounding
import WeightedEdgeColoring.DeficitAwareBoundedMultiplicityWholeEdgeRounding
import WeightedEdgeColoring.BipartitePackets
import WeightedEdgeColoring.PartialCompletion

/-!
# Same-palette residual rounding in an ambient graph

The bounded-multiplicity rounder is naturally applied to an edge restriction:
the restriction can contain a finite harmonic residual together with an
endpoint-simple tiny remainder, while the packet core has already been
colored.  This file transfers the rounded restriction back to the ambient
edge type, merges it into the old palette using common missing colors, and
then pays only the displayed residual weight in fresh colors.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})

/-- The image in the ambient edge type of a finite set in an edge
restriction. -/
def liftRestrictionFinset (R : Finset G.E)
    (P : Finset (G.edgeRestriction R).E) : Finset G.E :=
  P.image Subtype.val

@[simp] theorem mem_liftRestrictionFinset_iff
    (R : Finset G.E) (P : Finset (G.edgeRestriction R).E) (e : G.E) :
    e ∈ G.liftRestrictionFinset R P ↔
      ∃ he : e ∈ R, (⟨e, he⟩ : (G.edgeRestriction R).E) ∈ P := by
  classical
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨f, hf, hfe⟩
    subst e
    exact ⟨f.2, hf⟩
  · rintro ⟨he, hP⟩
    exact Finset.mem_image.mpr ⟨⟨e, he⟩, hP, rfl⟩

theorem liftRestrictionFinset_subset
    (R : Finset G.E) (P : Finset (G.edgeRestriction R).E) :
    G.liftRestrictionFinset R P ⊆ R := by
  intro e he
  exact (G.mem_liftRestrictionFinset_iff R P e).mp he |>.choose

/-- Restricted color load is unchanged when both the selected set and its
coloring are lifted to the ambient edge type. -/
theorem colorLoadOn_liftRestrictionFinset
    {q : ℕ} (hq : 0 < q) (R : Finset G.E)
    (P : Finset (G.edgeRestriction R).E)
    (color : (G.edgeRestriction R).E → Fin q)
    (v : G.V) (c : Fin q) :
    G.colorLoadOn (G.liftRestrictionFinset R P)
        (G.liftRestrictedColor hq R color) v c =
      (G.edgeRestriction R).colorLoadOn P color v c := by
  classical
  unfold colorLoadOn liftRestrictionFinset
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e he
    simp [liftRestrictedColor, e.2]
  · intro e he f hf hef
    exact Subtype.ext hef

/-- A feasible partial coloring of an edge restriction remains feasible on
the corresponding ambient set. -/
theorem feasibleOn_liftRestrictionFinset
    {q : ℕ} (hq : 0 < q) (R : Finset G.E)
    (P : Finset (G.edgeRestriction R).E)
    (color : (G.edgeRestriction R).E → Fin q)
    (hcolor : (G.edgeRestriction R).IsFeasibleOn P color) :
    G.IsFeasibleOn (G.liftRestrictionFinset R P)
      (G.liftRestrictedColor hq R color) := by
  intro v c
  rw [G.colorLoadOn_liftRestrictionFinset hq R P color v c]
  exact hcolor v c

/-- The unselected weight in a restriction is exactly the ambient weight in
`R` outside the lifted selected set. -/
theorem residualWeight_liftRestrictionFinset
    (R : Finset G.E) (P : Finset (G.edgeRestriction R).E) (v : G.V) :
    (∑ e ∈ R \ G.liftRestrictionFinset R P,
        if G.Inc v e then G.weight e else 0) =
      ∑ e ∈ (Finset.univ \ P),
        if (G.edgeRestriction R).Inc v e then
          (G.edgeRestriction R).weight e else 0 := by
  classical
  let Q : Finset G.E := G.liftRestrictionFinset R P
  have himage : R \ Q =
      (Finset.univ \ P).image
        (fun e : (G.edgeRestriction R).E ↦ e.1) := by
    ext e
    constructor
    · intro he
      have heR : e ∈ R := (Finset.mem_sdiff.mp he).1
      have heQ : e ∉ Q := (Finset.mem_sdiff.mp he).2
      apply Finset.mem_image.mpr
      refine ⟨⟨e, heR⟩, ?_, rfl⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro heP
      exact heQ (Finset.mem_image.mpr ⟨⟨e, heR⟩, heP, rfl⟩)
    · intro he
      rcases Finset.mem_image.mp he with ⟨f, hf, hfe⟩
      subst e
      apply Finset.mem_sdiff.mpr
      refine ⟨f.2, ?_⟩
      intro hfQ
      rcases Finset.mem_image.mp hfQ with ⟨g, hg, hgf⟩
      have hgf' : g = f := Subtype.ext hgf
      subst g
      exact (Finset.mem_sdiff.mp hf).2 hg
  change (∑ e ∈ R \ Q, if G.Inc v e then G.weight e else 0) = _
  rw [himage, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e he
    rfl
  · intro e he f hf hef
    exact Subtype.ext hef

/-- Coordinated residual rounding, same-palette insertion, and fresh cleanup.

`F` is the already colored core and `R` is the joint residual.  In the
intended harmonic application `R` contains both the bounded-multiplicity
finite-class residual and the endpoint-simple tiny packets.  The rounder sees
them in one graph, so feasibility is coordinated across the two parts.  Its
selected edges use colors missing from `F`; consequently they merge into the
same palette.  Only proposal deficit plus rounding loss is sent to fresh
colors. -/
theorem hasWeightedColoring_add_fresh_of_jointResidualRounding
    (hround : BoundedMultiplicityWholeEdgeUniformRounding.{u})
    (L : ℕ) (C0 C1 eta eps : ℝ)
    (hC0 : 0 < C0) (hC1 : 0 < C1)
    (heta : 0 < eta) (heps : 0 ≤ eps) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (b : G.Bipartition)
      (F R : Finset G.E) (n q : ℕ) (base : G.E → Fin q)
      (x : (G.edgeRestriction R).E → Fin q → ℝ),
      N ≤ n →
      0 < q →
      Disjoint F R →
      F ∪ R = Finset.univ →
      G.IsFeasibleOn F base →
      (∀ k,
        ((Bipartition.edgeRestriction G b R).orientedPairCell k).card ≤ L) →
      (∀ v, (G.edgeRestriction R).starWeight v ≤ n) →
      (q : ℝ) ≤ C1 * n →
      (∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n) →
      (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, (G.edgeRestriction R).IsAverageOfStarFeasibleSets v
        (fun se ↦ x se.1 c)) →
      (∀ e c, 0 < x e c →
        c ∈ G.missingColorsAt F base (G.fst e.1) ∧
          c ∈ G.missingColorsAt F base (G.snd e.1)) →
      (∀ v, (G.edgeRestriction R).proposalDeficit x v ≤ eps * n) →
      G.HasWeightedColoring
        (q + (4 * Nat.ceil ((eps + eta) * n) + 1)) := by
  rcases exists_missingSupported_partialColoring_of_boundedMultiplicityWholeEdge
      hround L C0 C1 eta hC0 hC1 heta with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro G b F R n q base x hn hq hdisj hcover hbase hmult hstar hpalette
    hx hmass havg hsupport hdeficit
  let H : WeightedMultigraph.{u} := G.edgeRestriction R
  let bH : H.Bipartition := Bipartition.edgeRestriction G b R
  let missing : H.V → Finset (Fin q) := fun v ↦
    G.missingColorsAt F base v
  rcases hN H bH n q missing x hn hq hmult hstar hpalette hx hmass havg
      hsupport with ⟨P, residual, hresidual, hselectedSupport, hloss⟩
  let Q : Finset G.E := G.liftRestrictionFinset R P
  let liftedResidual : G.E → Fin q :=
    G.liftRestrictedColor hq R residual
  have hQsub : Q ⊆ R := G.liftRestrictionFinset_subset R P
  have hFQ : Disjoint F Q := by
    rw [Finset.disjoint_left]
    intro e heF heQ
    exact Finset.disjoint_left.mp hdisj heF (hQsub heQ)
  have hQfeasible : G.IsFeasibleOn Q liftedResidual := by
    exact G.feasibleOn_liftRestrictionFinset hq R P residual hresidual
  have hQmissing : G.UsesOnlyCommonMissing F Q base liftedResidual := by
    intro e heQ
    rcases (G.mem_liftRestrictionFinset_iff R P e).mp heQ with
      ⟨heR, heP⟩
    have hs := hselectedSupport ⟨e, heR⟩ heP
    simpa [liftedResidual, liftRestrictedColor, heR, missing, H] using hs
  rcases G.merge_feasibleOn_samePalette_of_commonMissing
      F Q hFQ base liftedResidual hbase hQfeasible hQmissing with
    ⟨combinedColor, hcombined⟩
  let loss : ℝ := (eps + eta) * n
  have hloss0 : 0 ≤ loss :=
    mul_nonneg (add_nonneg heps heta.le) (Nat.cast_nonneg n)
  have hremaining : ∀ v,
      (∑ e ∈ Finset.univ \ (F ∪ Q),
        if G.Inc v e then G.weight e else 0) ≤ loss := by
    intro v
    have hset : (Finset.univ : Finset G.E) \ (F ∪ Q) = R \ Q := by
      ext e
      have hpartition : e ∈ F ∨ e ∈ R := by
        have : e ∈ F ∪ R := by simpa [hcover]
        exact Finset.mem_union.mp this
      constructor
      · intro he
        have hnot : e ∉ F ∪ Q := (Finset.mem_sdiff.mp he).2
        have heF : e ∉ F := fun heF ↦ hnot (Finset.mem_union_left _ heF)
        have heR : e ∈ R := hpartition.resolve_left heF
        have heQ : e ∉ Q := fun heQ ↦ hnot (Finset.mem_union_right _ heQ)
        exact Finset.mem_sdiff.mpr ⟨heR, heQ⟩
      · intro he
        have heR : e ∈ R := (Finset.mem_sdiff.mp he).1
        have heQ : e ∉ Q := (Finset.mem_sdiff.mp he).2
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro heUnion
        rcases Finset.mem_union.mp heUnion with heF | heQ'
        · exact Finset.disjoint_left.mp hdisj heF heR
        · exact heQ heQ'
    rw [hset, G.residualWeight_liftRestrictionFinset R P v]
    calc
      _ ≤ H.proposalDeficit x v + eta * n := hloss v
      _ ≤ loss := by
        have hd := hdeficit v
        dsimp [loss]
        linarith
  simpa [loss] using
    G.complete_partial_with_four_ceil (F ∪ Q) combinedColor hcombined loss hloss0
      hremaining

/-- Deficit-aware same-palette insertion.  Only the trimmed proposal deficit
and retained-core rounding loss are paid in fresh colors. -/
theorem hasWeightedColoring_add_fresh_of_jointResidualDeficitAwareRounding
    (hround : DeficitAwareBoundedMultiplicityWholeEdgeUniformRounding.{u})
    (L : ℕ) (C0 C1 trim eta eps : ℝ)
    (hC0 : 0 < C0) (hC1 : 0 < C1) (hC1four : C1 < 4)
    (htrim0 : 0 < trim) (htrim1 : trim < 1)
    (htrimEta : 64 * trim < eta)
    (heta : 0 < eta) (heps : 0 ≤ eps) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (b : G.Bipartition)
      (F R : Finset G.E) (n q : ℕ) (base : G.E → Fin q)
      (x : (G.edgeRestriction R).E → Fin q → ℝ),
      N ≤ n →
      0 < q →
      Disjoint F R →
      F ∪ R = Finset.univ →
      G.IsFeasibleOn F base →
      (∀ k,
        ((Bipartition.edgeRestriction G b R).orientedPairCell k).card ≤ L) →
      (∀ v, (G.edgeRestriction R).starWeight v ≤ n) →
      (q : ℝ) ≤ C1 * n →
      (∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n) →
      (∀ e, ∑ c, x e c ≤ 1) →
      (∀ v c, (G.edgeRestriction R).IsAverageOfStarFeasibleSets v
        (fun se ↦ x se.1 c)) →
      (∀ e c, 0 < x e c →
        c ∈ G.missingColorsAt F base (G.fst e.1) ∧
          c ∈ G.missingColorsAt F base (G.snd e.1)) →
      (∀ v, (G.edgeRestriction R).proposalDeficit x v ≤ eps * n) →
      G.HasWeightedColoring
        (q + (4 * Nat.ceil ((eps / trim + eta) * n) + 1)) := by
  rcases exists_missingSupported_partialColoring_of_deficitAwareBoundedMultiplicity
      hround L C0 C1 trim eta hC0 hC1 hC1four htrim0 htrim1 htrimEta heta with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro G b F R n q base x hn hq hdisj hcover hbase hmult hstar hpalette
    hx hmass havg hsupport hdeficit
  let H : WeightedMultigraph.{u} := G.edgeRestriction R
  let bH : H.Bipartition := Bipartition.edgeRestriction G b R
  let missing : H.V → Finset (Fin q) := fun v ↦
    G.missingColorsAt F base v
  rcases hN H bH n q missing x hn hq hmult hstar hpalette hx hmass havg
      hsupport with ⟨P, residual, hresidual, hselectedSupport, hloss⟩
  let Q : Finset G.E := G.liftRestrictionFinset R P
  let liftedResidual : G.E → Fin q :=
    G.liftRestrictedColor hq R residual
  have hQsub : Q ⊆ R := G.liftRestrictionFinset_subset R P
  have hFQ : Disjoint F Q := by
    rw [Finset.disjoint_left]
    intro e heF heQ
    exact Finset.disjoint_left.mp hdisj heF (hQsub heQ)
  have hQfeasible : G.IsFeasibleOn Q liftedResidual := by
    exact G.feasibleOn_liftRestrictionFinset hq R P residual hresidual
  have hQmissing : G.UsesOnlyCommonMissing F Q base liftedResidual := by
    intro e heQ
    rcases (G.mem_liftRestrictionFinset_iff R P e).mp heQ with
      ⟨heR, heP⟩
    have hs := hselectedSupport ⟨e, heR⟩ heP
    simpa [liftedResidual, liftRestrictedColor, heR, missing, H] using hs
  rcases G.merge_feasibleOn_samePalette_of_commonMissing
      F Q hFQ base liftedResidual hbase hQfeasible hQmissing with
    ⟨combinedColor, hcombined⟩
  let loss : ℝ := (eps / trim + eta) * n
  have hloss0 : 0 ≤ loss :=
    mul_nonneg (add_nonneg (div_nonneg heps htrim0.le) heta.le)
      (Nat.cast_nonneg n)
  have hremaining : ∀ v,
      (∑ e ∈ Finset.univ \ (F ∪ Q),
        if G.Inc v e then G.weight e else 0) ≤ loss := by
    intro v
    have hset : (Finset.univ : Finset G.E) \ (F ∪ Q) = R \ Q := by
      ext e
      have hpartition : e ∈ F ∨ e ∈ R := by
        have : e ∈ F ∪ R := by simpa [hcover]
        exact Finset.mem_union.mp this
      constructor
      · intro he
        have hnot : e ∉ F ∪ Q := (Finset.mem_sdiff.mp he).2
        have heF : e ∉ F := fun heF ↦ hnot (Finset.mem_union_left _ heF)
        have heR : e ∈ R := hpartition.resolve_left heF
        have heQ : e ∉ Q := fun heQ ↦ hnot (Finset.mem_union_right _ heQ)
        exact Finset.mem_sdiff.mpr ⟨heR, heQ⟩
      · intro he
        have heR : e ∈ R := (Finset.mem_sdiff.mp he).1
        have heQ : e ∉ Q := (Finset.mem_sdiff.mp he).2
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro heUnion
        rcases Finset.mem_union.mp heUnion with heF | heQ'
        · exact Finset.disjoint_left.mp hdisj heF heR
        · exact heQ heQ'
    rw [hset, G.residualWeight_liftRestrictionFinset R P v]
    calc
      _ ≤ H.proposalDeficit x v / trim + eta * n := hloss v
      _ ≤ loss := by
        have hd := hdeficit v
        have hddiv := div_le_div_of_nonneg_right hd htrim0.le
        dsimp [loss]
        calc
          H.proposalDeficit x v / trim + eta * n ≤
              (eps * n) / trim + eta * n := by
            simpa [add_comm] using add_le_add_right hddiv (eta * n)
          _ = (eps / trim + eta) * n := by ring
  simpa [loss] using
    G.complete_partial_with_four_ceil (F ∪ Q) combinedColor hcombined loss hloss0
      hremaining

end WeightedMultigraph

end

end WeightedEdgeColoring
