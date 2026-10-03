import WeightedEdgeColoring.MultigraphRetainedCorePalettePadding
import WeightedEdgeColoring.DeficitAwareBoundedMultiplicityWholeEdgeRounding
import WeightedEdgeColoring.VariableSlackIterationScalars

/-!
# Unconditional deficit-aware bounded-multiplicity rounding

This composes palette padding, the retained-core selector/iteration/decoder,
and the low-proposal-mass deficit charge.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

universe u

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})

/-- Multigraph version of the deterministic low-mass/high-mass split. -/
theorem residualWeight_le_deficit_div_add_of_retained_loss
    {q : ℕ} (x : G.E → Fin q → ℝ) (trim loss : ℝ)
    (htrim : 0 < trim) (hmass : ∀ e, G.proposalMass x e ≤ 1)
    (P : Finset G.E)
    (hretainedLoss : ∀ v,
      (∑ e ∈ (Finset.univ \ G.lowProposalMassEdges x trim) \ P,
        if G.Inc v e then G.weight e else 0) ≤ loss) :
    ∀ v,
      (∑ e ∈ Finset.univ \ P,
        if G.Inc v e then G.weight e else 0) ≤
          G.proposalDeficit x v / trim + loss := by
  intro v
  let L := G.lowProposalMassEdges x trim
  let H : Finset G.E := Finset.univ \ L
  let f : G.E → ℝ := fun e ↦ if G.Inc v e then G.weight e else 0
  have hdecomp : (Finset.univ : Finset G.E) \ P =
      (L \ P) ∪ (H \ P) := by
    ext e
    by_cases heL : e ∈ L <;> simp [H, heL]
  have hdisj : Disjoint (L \ P) (H \ P) := by
    rw [Finset.disjoint_left]
    intro e heLP heHP
    have heL : e ∈ L := (Finset.mem_sdiff.mp heLP).1
    have heH : e ∈ H := (Finset.mem_sdiff.mp heHP).1
    have heNotL : e ∉ L := by simpa [H] using heH
    exact heNotL heL
  have hlowRestricted : (∑ e ∈ L \ P, f e) ≤ ∑ e ∈ L, f e := by
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun e _ _ ↦ by
        unfold f
        split
        · exact G.weight_nonneg e
        · exact le_rfl)
  have hlow : (∑ e ∈ L, f e) ≤ G.proposalDeficit x v / trim := by
    simpa [L, f] using
      G.lowProposalMassWeight_le_deficit_div x trim htrim hmass v
  have hhigh : (∑ e ∈ H \ P, f e) ≤ loss := by
    simpa [H, L, f] using hretainedLoss v
  rw [hdecomp, Finset.sum_union hdisj]
  exact (add_le_add hlowRestricted hhigh).trans (add_le_add hlow le_rfl)

end WeightedMultigraph

set_option maxHeartbeats 1000000 in
/-- The proposal-preserving fixed-multiplicity construction proves the
application-facing deficit-aware whole-edge interface. -/
theorem deficitAwareBoundedMultiplicityWholeEdgeUniformRounding_proved :
    DeficitAwareBoundedMultiplicityWholeEdgeUniformRounding.{u} := by
  intro L C0 C1 trim eta hC0 hC1 hC1four htrim0 htrim1 htrimEta heta
  by_cases hL0 : L = 0
  · refine ⟨0, ?_⟩
    intro G b n q x _hn hq hmult _hstar _hpalette _hx _hmass _hlocal
    classical
    let noEdge : ∀ e : G.E, False := fun e ↦ by
      have hcell := hmult (b.orientedPairKey e)
      have hemem : e ∈ b.orientedPairCell (b.orientedPairKey e) := by
        simp [WeightedMultigraph.Bipartition.orientedPairCell]
      have hpos := Finset.card_pos.mpr ⟨e, hemem⟩
      omega
    letI : IsEmpty G.E := ⟨noEdge⟩
    have huniv : (Finset.univ : Finset G.E) = ∅ := Finset.univ_eq_empty
    let fallback : Fin q := ⟨0, hq⟩
    refine ⟨∅, (fun _ ↦ fallback), ?_, ?_, ?_⟩
    · intro v c
      simp [WeightedMultigraph.colorLoadOn]
    · simp
    · intro v
      rw [huniv]
      simp
      exact add_nonneg (div_nonneg (G.proposalDeficit_nonneg x _hmass v) htrim0.le)
        (mul_nonneg heta.le (Nat.cast_nonneg n))
  · have hL : 0 < L := Nat.pos_of_ne_zero hL0
    obtain ⟨Ncore, k, hk, hcore⟩ :=
      WeightedMultigraph.boundedMultiplicityRetainedProposalCoreRounding_proved
        L hL C0 trim eta hC0 htrim0 htrim1 htrimEta
    have hgap : 0 < 4 - C1 := sub_pos.mpr hC1four
    have hpadEventually := eventually_const_le_pos_mul_nat (k : ℝ) (4 - C1) hgap
    rcases Filter.eventually_atTop.1 hpadEventually with ⟨Npad, hNpad⟩
    refine ⟨max Ncore (max Npad 1), ?_⟩
    intro G b n q x hn hq hmult hstar hpalette hx hmass hlocal
    have hnCore : Ncore ≤ n :=
      (le_max_left Ncore (max Npad 1)).trans hn
    have hnPad : Npad ≤ n :=
      ((Nat.le_max_left Npad 1).trans
        (Nat.le_max_right Ncore (max Npad 1))).trans hn
    have hn1 : 1 ≤ n :=
      (Nat.le_max_right Npad 1 |>.trans
        (Nat.le_max_right Ncore (max Npad 1))).trans hn
    have hkGap : (k : ℝ) ≤ (4 - C1) * n := hNpad n hnPad
    let B := q / k + 1
    let Q := B * k
    have hk0 : 0 < k := hk
    have hB : 0 < B := by
      dsimp [B]
      exact Nat.zero_lt_succ _
    have hqQ : q ≤ Q := by
      dsimp [Q, B]
      calc
        q = k * (q / k) + q % k := (Nat.div_add_mod q k).symm
        _ ≤ k * (q / k) + k := by
          gcongr
          exact (Nat.mod_lt q hk0).le
        _ = (q / k + 1) * k := by ring
    have hQqk : Q ≤ q + k := by
      dsimp [Q, B]
      calc
        (q / k + 1) * k = q / k * k + k := by ring
        _ ≤ q + k := Nat.add_le_add_right (Nat.div_mul_le_self q k) k
    have hQfour : ((Q : ℕ) : ℝ) ≤ 4 * n := by
      have hqk : (Q : ℝ) ≤ q + k := by exact_mod_cast hQqk
      have hqbound : (q : ℝ) ≤ C1 * n := hpalette
      calc
        (Q : ℝ) ≤ q + k := hqk
        _ ≤ C1 * n + (4 - C1) * n := add_le_add hqbound hkGap
        _ = 4 * n := by ring
    let xpad : G.E → Fin Q → ℝ := G.padProposal hqQ x
    have hxpad : ∀ e c, 0 ≤ xpad e c ∧ xpad e c ≤ C0 / n := by
      intro e c
      cases hc : (WeightedMultigraph.palettePadEquiv hqQ).symm c with
      | inl d => simpa [xpad, WeightedMultigraph.padProposal, hc] using hx e d
      | inr d => simp [xpad, WeightedMultigraph.padProposal, hc, (div_nonneg hC0.le (Nat.cast_nonneg n))]
    have hmassPad : ∀ e, ∑ c, xpad e c ≤ 1 := by
      intro e
      simpa [xpad] using hmass e
    have hlocalPad : ∀ v c, G.IsAverageOfStarFeasibleSets v
        (fun se ↦ xpad se.1 c) := by
      exact G.padProposal_isAverageOfStarFeasibleSets hqQ x hlocal
    have hpair : G.PairMultiplicityAtMost L :=
      b.pairMultiplicityAtMost_of_orientedPair hmult
    rcases hcore G n B xpad hnCore hpair hB hstar hQfour hxpad hmassPad hlocalPad with
      ⟨P, paddedColor, hfeasible, hsupport, hretained⟩
    rcases G.exists_unpad_partialColoring hq hqQ x hfeasible hsupport with
      ⟨color, hfeasible', hsupport'⟩
    refine ⟨P, color, hfeasible', hsupport', ?_⟩
    have hlowEq : G.lowProposalMassEdges xpad trim =
        G.lowProposalMassEdges x trim := by
      ext e
      simp [WeightedMultigraph.lowProposalMassEdges,
        WeightedMultigraph.proposalMass, xpad]
    have hretained' : ∀ v,
        (∑ e ∈ (Finset.univ \ G.lowProposalMassEdges x trim) \ P,
          if G.Inc v e then G.weight e else 0) ≤ eta * n := by
      simpa [hlowEq] using hretained
    exact G.residualWeight_le_deficit_div_add_of_retained_loss
      x trim (eta * n) htrim0 hmass P hretained'

end

end WeightedEdgeColoring
