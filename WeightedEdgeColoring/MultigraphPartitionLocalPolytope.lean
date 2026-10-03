import WeightedEdgeColoring.MultigraphLocalPolytope

/-!
# Mixing two disjoint local subset distributions

This is the local bookkeeping needed when a residual star consists of a
finite harmonic-class part and an arbitrarily tiny part.  We choose one of
the two parts, then sample a feasible subset inside that part.  The unused
probability selects the empty set.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- Two normalized feasible-subset distributions on a partition of one star
can be mixed with masses `p` and `q`. -/
theorem isAverageOfStarFeasibleSets_of_partition
    {v : G.V} (isLeft : G.StarEdge v → Prop) [DecidablePred isLeft]
    (x : G.StarEdge v → ℝ) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 1)
    (hleft : IsAverageOfFeasibleSubsets
      (fun e : {e : G.StarEdge v // isLeft e} => G.weight e.1.1) 1
      (fun e => x e.1 / p))
    (hright : IsAverageOfFeasibleSubsets
      (fun e : {e : G.StarEdge v // ¬isLeft e} => G.weight e.1.1) 1
      (fun e => x e.1 / q)) :
    G.IsAverageOfStarFeasibleSets v x := by
  classical
  let L := {e : G.StarEdge v // isLeft e}
  let R := {e : G.StarEdge v // ¬isLeft e}
  rcases hleft with ⟨massL, hmassL0, hmassLtotal, hmassLsupport, hmargL⟩
  rcases hright with ⟨massR, hmassR0, hmassRtotal, hmassRsupport, hmargR⟩
  let embL : L ↪ G.StarEdge v := ⟨Subtype.val, Subtype.val_injective⟩
  let embR : R ↪ G.StarEdge v := ⟨Subtype.val, Subtype.val_injective⟩
  let Ω := Option (Finset L ⊕ Finset R)
  let prob : Ω → ℝ
    | none => 1 - p - q
    | some (Sum.inl S) => p * massL S
    | some (Sum.inr S) => q * massR S
  let rawOutcome : Ω → Finset (G.StarEdge v)
    | none => ∅
    | some (Sum.inl S) => S.map embL
    | some (Sum.inr S) => S.map embR
  let outcome : Ω → Finset (G.StarEdge v) := fun o =>
    if prob o = 0 then ∅ else rawOutcome o
  have hprob0 : ∀ o, 0 ≤ prob o := by
    intro o
    rcases o with _ | o
    · dsimp [prob]
      linarith
    · rcases o with S | S
      · exact mul_nonneg hp.le (hmassL0 S)
      · exact mul_nonneg hq.le (hmassR0 S)
  have hprobTotal : ∑ o : Ω, prob o = 1 := by
    rw [Fintype.sum_option, Fintype.sum_sum_type]
    change (1 - p - q) +
        ((∑ S : Finset L, p * massL S) +
          ∑ S : Finset R, q * massR S) = 1
    rw [← Finset.mul_sum, ← Finset.mul_sum, hmassLtotal, hmassRtotal]
    ring
  have hfeasible : ∀ o, G.StarFeasible v (outcome o) := by
    intro o
    by_cases hz : prob o = 0
    · simp [outcome, hz, StarFeasible]
    · dsimp [outcome]
      rw [if_neg hz]
      rcases o with _ | o
      · simp [rawOutcome, StarFeasible]
      · rcases o with S | S
        · have hm : massL S ≠ 0 := by
            intro h
            exact hz (by simp [prob, h])
          have hs := hmassLsupport S hm
          unfold StarFeasible
          rw [Finset.sum_map]
          simpa [rawOutcome, embL, L] using hs
        · have hm : massR S ≠ 0 := by
            intro h
            exact hz (by simp [prob, h])
          have hs := hmassRsupport S hm
          unfold StarFeasible
          rw [Finset.sum_map]
          simpa [rawOutcome, embR, R] using hs
  have hmarginal : ∀ e : G.StarEdge v,
      (∑ o : Ω, if e ∈ outcome o then prob o else 0) = x e := by
    intro e
    rw [Fintype.sum_option, Fintype.sum_sum_type]
    by_cases he : isLeft e
    · let eL : L := ⟨e, he⟩
      change
        (if e ∈ outcome none then prob none else 0) +
          ((∑ S : Finset L,
              if e ∈ outcome (some (Sum.inl S))
              then prob (some (Sum.inl S)) else 0) +
            ∑ S : Finset R,
              if e ∈ outcome (some (Sum.inr S))
              then prob (some (Sum.inr S)) else 0) = x e
      have hnone : e ∉ outcome none := by simp [outcome, rawOutcome]
      have hrightZero :
          (∑ S : Finset R,
            if e ∈ outcome (some (Sum.inr S))
            then prob (some (Sum.inr S)) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro S _hS
        have hnot : e ∉ S.map embR := by
          intro hmem
          rcases Finset.mem_map.mp hmem with ⟨f, _hf, hfe⟩
          have : f.1 = e := hfe
          exact f.2 (this ▸ he)
        by_cases hz : prob (some (Sum.inr S)) = 0
        · simp [outcome, hz]
        · simp [outcome, hz, rawOutcome, hnot]
      rw [if_neg hnone, hrightZero, zero_add, add_zero]
      calc
        (∑ S : Finset L,
            if e ∈ outcome (some (Sum.inl S))
            then prob (some (Sum.inl S)) else 0) =
            p * ∑ S : Finset L, if eL ∈ S then massL S else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro S _hS
              by_cases hm : massL S = 0
              · simp [outcome, prob, hm]
              · have hpM : prob (some (Sum.inl S)) ≠ 0 :=
                  mul_ne_zero hp.ne' hm
                by_cases hmem : eL ∈ S
                · have hem : e ∈ S.map embL :=
                    Finset.mem_map.mpr ⟨eL, hmem, rfl⟩
                  simp [outcome, hpM, rawOutcome, prob, hem, hmem]
                · have hnot : e ∉ S.map embL := by
                    intro hem
                    rcases Finset.mem_map.mp hem with ⟨f, hf, hfe⟩
                    have hfe' : f = eL := Subtype.ext hfe
                    exact hmem (hfe' ▸ hf)
                  simp [outcome, hpM, rawOutcome, prob, hnot, hmem]
        _ = p * (x e / p) := by rw [hmargL eL]
        _ = x e := by field_simp
    · let eR : R := ⟨e, he⟩
      change
        (if e ∈ outcome none then prob none else 0) +
          ((∑ S : Finset L,
              if e ∈ outcome (some (Sum.inl S))
              then prob (some (Sum.inl S)) else 0) +
            ∑ S : Finset R,
              if e ∈ outcome (some (Sum.inr S))
              then prob (some (Sum.inr S)) else 0) = x e
      have hnone : e ∉ outcome none := by simp [outcome, rawOutcome]
      have hleftZero :
          (∑ S : Finset L,
            if e ∈ outcome (some (Sum.inl S))
            then prob (some (Sum.inl S)) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro S _hS
        have hnot : e ∉ S.map embL := by
          intro hmem
          rcases Finset.mem_map.mp hmem with ⟨f, _hf, hfe⟩
          have : f.1 = e := hfe
          exact he (this ▸ f.2)
        by_cases hz : prob (some (Sum.inl S)) = 0
        · simp [outcome, hz]
        · simp [outcome, hz, rawOutcome, hnot]
      rw [if_neg hnone, hleftZero, zero_add, zero_add]
      calc
        (∑ S : Finset R,
            if e ∈ outcome (some (Sum.inr S))
            then prob (some (Sum.inr S)) else 0) =
            q * ∑ S : Finset R, if eR ∈ S then massR S else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro S _hS
              by_cases hm : massR S = 0
              · simp [outcome, prob, hm]
              · have hqM : prob (some (Sum.inr S)) ≠ 0 :=
                  mul_ne_zero hq.ne' hm
                by_cases hmem : eR ∈ S
                · have hem : e ∈ S.map embR :=
                    Finset.mem_map.mpr ⟨eR, hmem, rfl⟩
                  simp [outcome, hqM, rawOutcome, prob, hem, hmem]
                · have hnot : e ∉ S.map embR := by
                    intro hem
                    rcases Finset.mem_map.mp hem with ⟨f, hf, hfe⟩
                    have hfe' : f = eR := Subtype.ext hfe
                    exact hmem (hfe' ▸ hf)
                  simp [outcome, hqM, rawOutcome, prob, hnot, hmem]
        _ = q * (x e / q) := by rw [hmargR eR]
        _ = x e := by field_simp
  let equiv := Fintype.equivFin Ω
  let m := Fintype.card Ω
  let pFin : Fin m → ℝ := fun i => prob (equiv.symm i)
  let outcomeFin : Fin m → Finset (G.StarEdge v) := fun i =>
    outcome (equiv.symm i)
  refine ⟨m, pFin, outcomeFin, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hprob0 (equiv.symm i)
  · simpa [pFin, equiv, m] using equiv.symm.sum_comp prob |>.trans hprobTotal
  · intro i
    exact hfeasible (equiv.symm i)
  · intro e
    simpa [pFin, outcomeFin, equiv, m] using
      equiv.symm.sum_comp (fun o => if e ∈ outcome o then prob o else 0)
        |>.trans (hmarginal e)

end

end WeightedMultigraph
end WeightedEdgeColoring
