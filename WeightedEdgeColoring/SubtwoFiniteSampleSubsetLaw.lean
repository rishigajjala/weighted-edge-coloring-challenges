import WeightedEdgeColoring.SubtwoSingleClassLocalPolytope
import WeightedEdgeColoring.MultigraphLocalPolytope
import WeightedEdgeColoring.SubtwoLabelConditionalLaw

/-! Push a finite sample law forward to a law on finite subsets. -/

namespace WeightedEdgeColoring

open scoped BigOperators
noncomputable section

theorem subsetLaw_of_finiteSamples
    {I Ω Label : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]
    [Fintype Label] [DecidableEq Label]
    (w : I → ℝ) (edgeLabel : I → Label)
    (prob : Ω → ℝ) (outcome : Ω → Finset I)
    (hprob0 : ∀ o, 0 ≤ prob o)
    (hprobSum : ∑ o, prob o = 1)
    (hfeas : ∀ o, prob o ≠ 0 → ∑ i ∈ outcome o, w i ≤ 1)
    (hlabel : ∀ o, prob o ≠ 0 → outcome o ≠ ∅ →
      ∃ l, ∀ i ∈ outcome o, edgeLabel i = l) :
    ∃ q : Finset I → ℝ,
      (∀ S, 0 ≤ q S) ∧ (∑ S, q S = 1) ∧
      (∀ S, q S ≠ 0 → ∑ i ∈ S, w i ≤ 1) ∧
      (∀ i, (∑ S, if i ∈ S then q S else 0) =
        ∑ o, if i ∈ outcome o then prob o else 0) ∧
      (∀ S, q S ≠ 0 → S ≠ ∅ →
        ∃ l, ∀ i ∈ S, edgeLabel i = l) ∧
      (∀ l : Label, subsetLabelMass edgeLabel q l =
        ∑ o, if outcome o ≠ ∅ ∧
          (∀ i ∈ outcome o, edgeLabel i = l) then prob o else 0) := by
  classical
  let q : Finset I → ℝ := fun S =>
    ∑ o : Ω, if outcome o = S then prob o else 0
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S
    exact Finset.sum_nonneg (fun o _ => by
      by_cases h : outcome o = S
      · simpa [h] using hprob0 o
      · simp [h])
  · calc
      (∑ S, q S) = ∑ o : Ω, ∑ S : Finset I,
          if outcome o = S then prob o else 0 := Finset.sum_comm
      _ = ∑ o, prob o := by simp
      _ = 1 := hprobSum
  · intro S hq
    have hex : ∃ o, outcome o = S ∧ prob o ≠ 0 := by
      by_contra h
      push_neg at h
      apply hq
      apply Finset.sum_eq_zero
      intro o _
      by_cases ho : outcome o = S
      · simp [ho, h o ho]
      · simp [ho]
    obtain ⟨o, rfl, hp⟩ := hex
    exact hfeas o hp
  · intro i
    calc
      (∑ S, if i ∈ S then q S else 0) =
          ∑ o : Ω, ∑ S : Finset I,
            if i ∈ S then (if outcome o = S then prob o else 0) else 0 := by
        calc
          _ = ∑ S : Finset I, ∑ o : Ω,
              if i ∈ S then (if outcome o = S then prob o else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro S _
            by_cases hi : i ∈ S <;> simp [q, hi]
          _ = _ := Finset.sum_comm
      _ = ∑ o, if i ∈ outcome o then prob o else 0 := by
        apply Finset.sum_congr rfl
        intro o _
        have hswap :
            (∑ S : Finset I,
              if i ∈ S then (if outcome o = S then prob o else 0) else 0) =
            ∑ S : Finset I,
              if outcome o = S then (if i ∈ S then prob o else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro S _
          split_ifs <;> rfl
        rw [hswap]
        simp
  · intro S hq hS
    have hex : ∃ o, outcome o = S ∧ prob o ≠ 0 := by
      by_contra h
      push_neg at h
      apply hq
      apply Finset.sum_eq_zero
      intro o _
      by_cases ho : outcome o = S
      · simp [ho, h o ho]
      · simp [ho]
    obtain ⟨o, ho, hp⟩ := hex
    subst S
    exact hlabel o hp hS
  · intro l
    unfold subsetLabelMass
    calc
      (∑ S : Finset I,
        if S ≠ ∅ ∧ (∀ i ∈ S, edgeLabel i = l) then q S else 0) =
          ∑ o : Ω, ∑ S : Finset I,
            if S ≠ ∅ ∧ (∀ i ∈ S, edgeLabel i = l) then
              (if outcome o = S then prob o else 0) else 0 := by
        calc
          _ = ∑ S : Finset I, ∑ o : Ω,
              if S ≠ ∅ ∧ (∀ i ∈ S, edgeLabel i = l) then
                (if outcome o = S then prob o else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro S _
            by_cases hS : S ≠ ∅ ∧ ∀ i ∈ S, edgeLabel i = l <;>
              simp [q, hS]
          _ = _ := Finset.sum_comm
      _ = ∑ o : Ω, if outcome o ≠ ∅ ∧
          (∀ i ∈ outcome o, edgeLabel i = l) then prob o else 0 := by
        apply Finset.sum_congr rfl
        intro o _
        have hswap :
            (∑ S : Finset I,
              if S ≠ ∅ ∧ (∀ i ∈ S, edgeLabel i = l) then
                (if outcome o = S then prob o else 0) else 0) =
              ∑ S : Finset I,
                if outcome o = S then
                  (if S ≠ ∅ ∧ (∀ i ∈ S, edgeLabel i = l) then prob o else 0)
                  else 0 := by
          apply Finset.sum_congr rfl
          intro S _
          split_ifs <;> rfl
        rw [hswap]
        simp

end

namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- If the average vector vanishes off one original endpoint label, every
positive sample can be taken entirely within that label. -/
theorem singleLabelSubsetLaw_of_average
    {v : G.V} {Label : Type*} [Fintype Label] [DecidableEq Label]
    (edgeLabel : G.StarEdge v → Label) (label : Label)
    (x : G.StarEdge v → ℝ)
    (haverage : G.IsAverageOfStarFeasibleSets v x)
    (hzero : ∀ e, edgeLabel e ≠ label → x e = 0) :
    ∃ q : Finset (G.StarEdge v) → ℝ,
      (∀ S, 0 ≤ q S) ∧ (∑ S, q S = 1) ∧
      (∀ S, q S ≠ 0 → G.StarFeasible v S) ∧
      (∀ e, (∑ S, if e ∈ S then q S else 0) = x e) ∧
      (∀ S, q S ≠ 0 → S ≠ ∅ →
        ∀ e ∈ S, edgeLabel e = label) := by
  classical
  rcases haverage with ⟨n, p, outcome, hp0, hpsum, hfeas, hmarg⟩
  have hsampleLabel : ∀ j : Fin n, p j ≠ 0 →
      ∀ e ∈ outcome j, edgeLabel e = label := by
    intro j hj e he
    by_contra hne
    have hz := hzero e hne
    have hm := hmarg e
    rw [hz] at hm
    have hle : p j ≤ ∑ k : Fin n, if e ∈ outcome k then p k else 0 := by
      have hterm : ∀ k : Fin n, 0 ≤ if e ∈ outcome k then p k else 0 := by
        intro k
        split
        · exact hp0 k
        · exact le_rfl
      have hs := Finset.single_le_sum
        (fun k _ => hterm k) (Finset.mem_univ j)
      simpa [he] using hs
    have hpzero : p j = 0 := le_antisymm (hm ▸ hle) (hp0 j)
    exact hj hpzero
  obtain ⟨q, hq0, hqsum, hqfeas, hqmarg, hqsingle, _hqlabelmass⟩ :=
    subsetLaw_of_finiteSamples
      (fun e : G.StarEdge v => G.weight e.1) edgeLabel p outcome
      hp0 hpsum (fun j _ => hfeas j)
      (fun j hj hne => ⟨label, hsampleLabel j hj⟩)
  refine ⟨q, hq0, hqsum,
    (fun S hS => hqfeas S hS),
    (fun e => (hqmarg e).trans (hmarg e)), ?_⟩
  intro S hS _ e he
  by_contra hne
  have hz := hzero e hne
  have hm : (∑ T, if e ∈ T then q T else 0) = 0 := by
    rw [(hqmarg e).trans (hmarg e), hz]
  have hle : q S ≤ ∑ T, if e ∈ T then q T else 0 := by
    have hterm : ∀ T : Finset (G.StarEdge v),
        0 ≤ if e ∈ T then q T else 0 := by
      intro T
      split
      · exact hq0 T
      · exact le_rfl
    have hs := Finset.single_le_sum
      (fun T _ => hterm T) (Finset.mem_univ S)
    simpa [he] using hs
  exact hS (le_antisymm (hm ▸ hle) (hq0 S))

/-- Mix one-label laws using reserved masses, retaining every marginal. -/
theorem mix_singleLabelSubsetLaws
    {v : G.V} {Label : Type*} [Fintype Label] [DecidableEq Label]
    (edgeLabel : G.StarEdge v → Label)
    (x : G.StarEdge v → ℝ)
    (mass : Label → ℝ) (hmass : ∀ l, 0 < mass l)
    (hmassSum : ∑ l, mass l ≤ 1)
    (qLabel : Label → Finset (G.StarEdge v) → ℝ)
    (hq0 : ∀ l S, 0 ≤ qLabel l S)
    (hqsum : ∀ l, ∑ S, qLabel l S = 1)
    (hqfeas : ∀ l S, qLabel l S ≠ 0 → G.StarFeasible v S)
    (hqmarg : ∀ l e,
      (∑ S, if e ∈ S then qLabel l S else 0) =
        if edgeLabel e = l then x e / mass l else 0)
    (hqsingle : ∀ l S, qLabel l S ≠ 0 → S ≠ ∅ →
      ∀ e ∈ S, edgeLabel e = l) :
    ∃ q : Finset (G.StarEdge v) → ℝ,
      (∀ S, 0 ≤ q S) ∧ (∑ S, q S = 1) ∧
      (∀ S, q S ≠ 0 → G.StarFeasible v S) ∧
      (∀ e, (∑ S, if e ∈ S then q S else 0) = x e) ∧
      (∀ S, q S ≠ 0 → S ≠ ∅ →
        ∃ l, ∀ e ∈ S, edgeLabel e = l) ∧
      (∀ l, subsetLabelMass edgeLabel q l ≤ mass l) := by
  classical
  let Ω := Option (Σ l : Label, Finset (G.StarEdge v))
  let prob : Ω → ℝ
    | none => 1 - ∑ l, mass l
    | some ⟨l, S⟩ => mass l * qLabel l S
  let outcome : Ω → Finset (G.StarEdge v)
    | none => ∅
    | some ⟨_, S⟩ => S
  have hp0 : ∀ o, 0 ≤ prob o := by
    intro o
    cases o with
    | none => dsimp [prob]; linarith
    | some a => exact mul_nonneg (hmass a.1).le (hq0 a.1 a.2)
  have hpsum : ∑ o : Ω, prob o = 1 := by
    change (∑ o : Option (Σ l : Label, Finset (G.StarEdge v)), prob o) = 1
    rw [Fintype.sum_option, Fintype.sum_sigma]
    change (1 - ∑ l, mass l) +
      ∑ l : Label, ∑ S : Finset (G.StarEdge v), mass l * qLabel l S = 1
    simp_rw [← Finset.mul_sum, hqsum, mul_one]
    ring
  have hpfeas : ∀ o, prob o ≠ 0 →
      ∑ e ∈ outcome o, G.weight e.1 ≤ 1 := by
    intro o ho
    cases o with
    | none => simp [outcome]
    | some a =>
      have hq : qLabel a.1 a.2 ≠ 0 := right_ne_zero_of_mul ho
      exact hqfeas a.1 a.2 hq
  have hplabel : ∀ o, prob o ≠ 0 → outcome o ≠ ∅ →
      ∃ l, ∀ e ∈ outcome o, edgeLabel e = l := by
    intro o ho hne
    cases o with
    | none => exact (hne rfl).elim
    | some a =>
      have hq : qLabel a.1 a.2 ≠ 0 := right_ne_zero_of_mul ho
      exact ⟨a.1, hqsingle a.1 a.2 hq hne⟩
  obtain ⟨q, hq0', hqsum', hqfeas', hqmarg', hqsingle', hqmass'⟩ :=
    subsetLaw_of_finiteSamples
      (fun e : G.StarEdge v => G.weight e.1) edgeLabel prob outcome
      hp0 hpsum hpfeas hplabel
  refine ⟨q, hq0', hqsum', hqfeas', ?_, hqsingle', ?_⟩
  intro e
  rw [hqmarg' e]
  change (∑ o : Option (Σ l : Label, Finset (G.StarEdge v)),
    if e ∈ outcome o then prob o else 0) = x e
  rw [Fintype.sum_option, Fintype.sum_sigma]
  change (if e ∈ (∅ : Finset (G.StarEdge v)) then prob none else 0) +
    (∑ l : Label, ∑ S : Finset (G.StarEdge v),
      if e ∈ S then mass l * qLabel l S else 0) = x e
  have hnot : e ∉ (∅ : Finset (G.StarEdge v)) := by simp
  rw [if_neg hnot, zero_add]
  calc
    (∑ l : Label, ∑ S : Finset (G.StarEdge v),
      if e ∈ S then mass l * qLabel l S else 0) =
        ∑ l : Label, mass l *
          (∑ S : Finset (G.StarEdge v),
            if e ∈ S then qLabel l S else 0) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      by_cases he : e ∈ S <;> simp [he]
    _ = ∑ l : Label,
        if edgeLabel e = l then mass l * (x e / mass l) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [hqmarg]
      split <;> ring
    _ = x e := by
      rw [Finset.sum_eq_single (edgeLabel e)]
      · simp only [↓reduceIte]
        field_simp [ne_of_gt (hmass (edgeLabel e))]
      · intro l _ hl
        simp [Ne.symm hl]
      · intro hn
        exact (hn (Finset.mem_univ _)).elim
  intro l
  rw [hqmass' l]
  change (∑ o : Option (Σ a : Label, Finset (G.StarEdge v)),
    if outcome o ≠ ∅ ∧ (∀ e ∈ outcome o, edgeLabel e = l)
      then prob o else 0) ≤ mass l
  rw [Fintype.sum_option, Fintype.sum_sigma]
  have hnone :
      (if outcome (none : Ω) ≠ ∅ ∧
          (∀ e ∈ outcome (none : Ω), edgeLabel e = l)
        then prob none else 0) = 0 := by simp [outcome]
  rw [hnone, zero_add]
  calc
    (∑ a : Label, ∑ S : Finset (G.StarEdge v),
      if outcome (some ⟨a, S⟩ : Ω) ≠ ∅ ∧
          (∀ e ∈ outcome (some ⟨a, S⟩ : Ω), edgeLabel e = l)
        then prob (some ⟨a, S⟩ : Ω) else 0) ≤
        ∑ S : Finset (G.StarEdge v), mass l * qLabel l S := by
      calc
        _ ≤ ∑ a : Label,
            if a = l then
              ∑ S : Finset (G.StarEdge v), mass a * qLabel a S
            else 0 := by
          apply Finset.sum_le_sum
          intro a _
          by_cases ha : a = l
          · subst a
            simp only [if_true]
            apply Finset.sum_le_sum
            intro S _
            by_cases hS : S ≠ ∅ ∧ ∀ e ∈ S, edgeLabel e = l
            · change (if S ≠ ∅ ∧ ∀ e ∈ S, edgeLabel e = l
                then mass l * qLabel l S else 0) ≤ mass l * qLabel l S
              rw [if_pos hS]
            · change (if S ≠ ∅ ∧ ∀ e ∈ S, edgeLabel e = l
                then mass l * qLabel l S else 0) ≤ mass l * qLabel l S
              rw [if_neg hS]
              exact mul_nonneg (hmass l).le (hq0 l S)
          · simp only [ha, if_false]
            apply le_of_eq
            apply Finset.sum_eq_zero
            intro S _
            by_cases hS : S ≠ ∅ ∧ ∀ e ∈ S, edgeLabel e = l
            · have hzero : qLabel a S = 0 := by
                by_contra hq
                obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hS.1
                exact ha ((hqsingle a S hq hS.1 e he).symm.trans (hS.2 e he))
              simp [outcome, prob, hS, hzero]
            · have hzero :
                (if outcome (some ⟨a, S⟩ : Ω) ≠ ∅ ∧
                    (∀ e ∈ outcome (some ⟨a, S⟩ : Ω), edgeLabel e = l)
                  then prob (some ⟨a, S⟩ : Ω) else 0) = 0 := by
                apply if_neg
                intro h
                exact hS ⟨h.1, h.2⟩
              exact hzero
        _ = ∑ S : Finset (G.StarEdge v), mass l * qLabel l S := by
          rw [Finset.sum_eq_single l]
          · simp
          · intro a _ ha
            simp [ha]
          · intro hn
            exact (hn (Finset.mem_univ l)).elim
    _ = mass l := by rw [← Finset.mul_sum, hqsum l, mul_one]

end WeightedMultigraph
end WeightedEdgeColoring
