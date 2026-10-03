import WeightedEdgeColoring.GreedyCleanup

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

private theorem natAdd_ne_castAdd {q r : ℕ} (a : Fin r) (b : Fin q) :
    Fin.natAdd q a ≠ Fin.castAdd r b := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv
  omega

private theorem castAdd_ne_natAdd {q r : ℕ} (a : Fin q) (b : Fin r) :
    Fin.castAdd r a ≠ Fin.natAdd q b :=
  ne_comm.mp (natAdd_ne_castAdd b a)

/-- Merge feasible colorings of two disjoint edge sets, using disjoint palettes.
This is the deterministic completion operation used after partial rounding. -/
theorem merge_feasibleOn
    {q r : ℕ} (P R : Finset G.E) (hdisj : Disjoint P R)
    (left : G.E → Fin q) (hleft : G.IsFeasibleOn P left)
    (right : G.E → Fin r) (hright : G.IsFeasibleOn R right) :
    ∃ color : G.E → Fin (q + r), G.IsFeasibleOn (P ∪ R) color := by
  classical
  let color : G.E → Fin (q + r) := fun e =>
    if e ∈ P then Fin.castAdd r (left e) else Fin.natAdd q (right e)
  refine ⟨color, ?_⟩
  intro v i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have hload :
        G.colorLoadOn (P ∪ R) color v (Fin.castAdd r j) =
          G.colorLoadOn P left v j := by
      unfold colorLoadOn
      rw [Finset.sum_union hdisj]
      have hleftsum :
          (∑ e ∈ P, if G.Inc v e ∧ color e = Fin.castAdd r j
            then G.weight e else 0) =
          ∑ e ∈ P, if G.Inc v e ∧ left e = j then G.weight e else 0 := by
        apply Finset.sum_congr rfl
        intro e heP
        simp [color, heP]
      rw [hleftsum]
      have hrightzero :
          (∑ e ∈ R, if G.Inc v e ∧ color e = Fin.castAdd r j
            then G.weight e else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro e heR
        have heP : e ∉ P := fun heP => Finset.disjoint_left.mp hdisj heP heR
        have hne : Fin.natAdd q (right e) ≠ Fin.castAdd r j :=
          natAdd_ne_castAdd (right e) j
        simp [color, heP, hne]
      rw [hrightzero, add_zero]
    rw [hload]
    exact hleft v j
  · intro j
    have hload :
        G.colorLoadOn (P ∪ R) color v (Fin.natAdd q j) =
          G.colorLoadOn R right v j := by
      unfold colorLoadOn
      rw [Finset.sum_union hdisj]
      have hleftzero :
          (∑ e ∈ P, if G.Inc v e ∧ color e = Fin.natAdd q j
            then G.weight e else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro e heP
        have hne : Fin.castAdd r (left e) ≠ Fin.natAdd q j :=
          castAdd_ne_natAdd (left e) j
        simp [color, heP, hne]
      rw [hleftzero, zero_add]
      apply Finset.sum_congr rfl
      intro e heR
      have heP : e ∉ P := fun heP => Finset.disjoint_left.mp hdisj heP heR
      simp [color, heP]
    rw [hload]
    exact hright v j

/-- Restrict a weighted multigraph to a finite set of edge indices. -/
abbrev edgeRestriction (R : Finset G.E) : WeightedMultigraph where
  V := G.V
  E := {e : G.E // e ∈ R}
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst e := G.fst e.1
  snd e := G.snd e.1
  noLoop e := G.noLoop e.1
  weight e := G.weight e.1
  weight_pos e := G.weight_pos e.1
  weight_le_one e := G.weight_le_one e.1

@[simp] theorem edgeRestriction_inc (R : Finset G.E) (v : G.V)
    (e : (G.edgeRestriction R).E) :
    (G.edgeRestriction R).Inc v e ↔ G.Inc v e.1 := by
  rfl

/-- The star weight in an edge restriction is the corresponding restricted
sum in the original graph. -/
theorem edgeRestriction_starWeight (R : Finset G.E) (v : G.V) :
    (G.edgeRestriction R).starWeight v =
      ∑ e ∈ R, if G.Inc v e then G.weight e else 0 := by
  classical
  change
    (∑ e : {e : (G.edgeRestriction R).E // G.Inc v e.1}, G.weight e.1.1) = _
  calc
    _ = ∑ e ∈ (Finset.univ : Finset {e : G.E // e ∈ R}).filter
          (fun e => G.Inc v e.1), G.weight e.1 := by
      symm
      exact Finset.sum_subtype (p := fun e : {e : G.E // e ∈ R} => G.Inc v e.1)
        ((Finset.univ : Finset {e : G.E // e ∈ R}).filter
          (fun e => G.Inc v e.1)) (by simp) (fun e => G.weight e.1)
    _ = ∑ e : {e : G.E // e ∈ R},
        if G.Inc v e.1 then G.weight e.1 else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ e ∈ R, if G.Inc v e then G.weight e else 0 := by
      symm
      exact Finset.sum_subtype (p := fun e : G.E => e ∈ R) R (by simp)
        (fun e => if G.Inc v e then G.weight e else 0)

/-- A vertex-wise bound on a restricted edge set gives the same bound on the
weighted maximum degree of the restricted graph. -/
theorem edgeRestriction_deltaW_le
    (R : Finset G.E) (x : ℝ) (hx : 0 ≤ x)
    (hstar : ∀ v, (∑ e ∈ R, if G.Inc v e then G.weight e else 0) ≤ x) :
    (G.edgeRestriction R).deltaW ≤ x := by
  rw [(G.edgeRestriction R).deltaW_le_iff]
  refine ⟨hx, ?_⟩
  intro v
  rw [G.edgeRestriction_starWeight R v]
  exact hstar v

/-- Lift a coloring of an edge restriction back to the original edge type.
The fallback value is never used on an edge in `R`. -/
def liftRestrictedColor {r : ℕ} (hr : 0 < r) (R : Finset G.E)
    (color : (G.edgeRestriction R).E → Fin r) : G.E → Fin r := fun e =>
  if he : e ∈ R then color ⟨e, he⟩ else ⟨0, hr⟩

/-- Feasibility of a coloring of an edge restriction, expressed on the
original edge type. -/
theorem feasibleOn_liftRestrictedColor
    {r : ℕ} (hr : 0 < r) (R : Finset G.E)
    (color : (G.edgeRestriction R).E → Fin r)
    (hcolor : (G.edgeRestriction R).IsWeightedColoring color) :
    G.IsFeasibleOn R (G.liftRestrictedColor hr R color) := by
  classical
  intro v i
  have hload :
      G.colorLoadOn R (G.liftRestrictedColor hr R color) v i =
        (G.edgeRestriction R).colorLoad color v i := by
    unfold colorLoadOn
    change
      (∑ e ∈ R,
        if G.Inc v e ∧ G.liftRestrictedColor hr R color e = i
        then G.weight e else 0) =
      ∑ e : {e : (G.edgeRestriction R).E // G.Inc v e.1},
        if color e.1 = i then G.weight e.1.1 else 0
    have hstar :
        (∑ e : {e : (G.edgeRestriction R).E // G.Inc v e.1},
          if color e.1 = i then G.weight e.1.1 else 0) =
        ∑ e : {e : G.E // e ∈ R},
          if G.Inc v e.1 then
            (if color e = i then G.weight e.1 else 0) else 0 := by
      calc
        _ = ∑ e ∈ (Finset.univ : Finset {e : G.E // e ∈ R}).filter
              (fun e => G.Inc v e.1),
              if color e = i then G.weight e.1 else 0 := by
          symm
          exact Finset.sum_subtype
            (p := fun e : {e : G.E // e ∈ R} => G.Inc v e.1)
            ((Finset.univ : Finset {e : G.E // e ∈ R}).filter
              (fun e => G.Inc v e.1)) (by simp)
              (fun e => if color e = i then G.weight e.1 else 0)
        _ = _ := by
          rw [Finset.sum_filter]
    calc
      _ = ∑ e : {e : G.E // e ∈ R},
          if G.Inc v e.1 ∧ G.liftRestrictedColor hr R color e.1 = i
          then G.weight e.1 else 0 := by
        exact Finset.sum_subtype (p := fun e : G.E => e ∈ R) R (by simp)
          (fun e => if G.Inc v e ∧ G.liftRestrictedColor hr R color e = i
            then G.weight e else 0)
      _ = ∑ e : {e : G.E // e ∈ R},
          if G.Inc v e.1 then
            (if color e = i then G.weight e.1 else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro e _he
        by_cases hinc : G.Inc v e.1 <;>
          by_cases hc : color e = i <;>
          simp [liftRestrictedColor, e.property, hinc, hc]
      _ = _ := hstar.symm
  rw [hload]
  exact hcolor v i

/-- Complete any feasible partial coloring with fresh colors.  If the
uncolored edges have total incident weight at most `x`, descending-weight
greedy cleanup uses at most `4 * ceil x + 1` new colors. -/
theorem complete_partial_with_four_ceil
    {q : ℕ} (P : Finset G.E) (left : G.E → Fin q)
    (hleft : G.IsFeasibleOn P left) (x : ℝ) (_hx : 0 ≤ x)
    (hresidual : ∀ v,
      (∑ e ∈ Finset.univ \ P, if G.Inc v e then G.weight e else 0) ≤ x) :
    G.HasWeightedColoring (q + (4 * Nat.ceil x + 1)) := by
  classical
  let R : Finset G.E := Finset.univ \ P
  let H := G.edgeRestriction R
  let r : ℕ := 4 * Nat.ceil x + 1
  have hr : 0 < r := by simp [r]
  have hdelta : H.deltaW ≤ Nat.ceil x := by
    apply G.edgeRestriction_deltaW_le R (Nat.ceil x)
    · exact_mod_cast Nat.zero_le (Nat.ceil x)
    · intro v
      exact (hresidual v).trans (Nat.le_ceil x)
  rcases H.hasWeightedColoring_four_add_one (Nat.ceil x) hdelta with
    ⟨rightSub, hrightSub⟩
  let right : G.E → Fin r := G.liftRestrictedColor hr R rightSub
  have hright : G.IsFeasibleOn R right := by
    exact G.feasibleOn_liftRestrictedColor hr R rightSub hrightSub
  have hdisj : Disjoint P R := by
    simp [R, Finset.disjoint_left]
  rcases G.merge_feasibleOn P R hdisj left hleft right hright with
    ⟨color, hcolor⟩
  refine ⟨color, (G.isWeightedColoring_iff_feasibleOn_univ color).2 ?_⟩
  have hunion : P ∪ R = Finset.univ := by
    ext e
    simp [R]
  rw [hunion] at hcolor
  exact hcolor

end WeightedMultigraph
end WeightedEdgeColoring
