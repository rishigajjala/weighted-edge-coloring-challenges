import WeightedEdgeColoring.WeightedInsertion
import Mathlib.Data.Finset.Max

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- Colors that cannot receive `e` at `v` in the current partial coloring. -/
noncomputable def forbiddenColors {q : ℕ} (P : Finset G.E)
    (color : G.E → Fin q) (v : G.V) (e : G.E) : Finset (Fin q) :=
  Finset.univ.filter fun i => 1 < G.colorLoadOn P color v i + G.weight e

/-- If all previously colored edges are at least as heavy as `e`, then every
color forbidden for `e` has current load at least one half.  This is the key
observation in the descending-weight cleanup argument. -/
theorem half_le_load_of_mem_forbidden
    {q : ℕ} (P : Finset G.E) (color : G.E → Fin q)
    (e : G.E) (horder : ∀ f ∈ P, G.weight e ≤ G.weight f)
    (v : G.V) (i : Fin q) (hi : i ∈ G.forbiddenColors P color v e) :
    1 / 2 ≤ G.colorLoadOn P color v i := by
  classical
  have hbad : 1 < G.colorLoadOn P color v i + G.weight e :=
    (Finset.mem_filter.mp hi).2
  by_cases hsmall : G.weight e ≤ 1 / 2
  · linarith
  · have hehalf : 1 / 2 < G.weight e := lt_of_not_ge hsmall
    let Q := P.filter fun f => G.Inc v f ∧ color f = i
    have hload : G.colorLoadOn P color v i = ∑ f ∈ Q, G.weight f := by
      unfold colorLoadOn
      rw [← Finset.sum_filter]
    have hloadpos : 0 < G.colorLoadOn P color v i := by
      have heone := G.weight_le_one e
      linarith
    have hQ : Q.Nonempty := by
      by_contra hQempty
      have hQeq : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQempty
      rw [hload, hQeq] at hloadpos
      simp at hloadpos
    rcases hQ with ⟨f, hfQ⟩
    have hfP : f ∈ P := (Finset.mem_filter.mp hfQ).1
    have hfle : G.weight e ≤ G.weight f := horder f hfP
    have hfsum : G.weight f ≤ ∑ x ∈ Q, G.weight x := by
      exact Finset.single_le_sum (fun x _hx => G.weight_nonneg x) hfQ
    rw [hload]
    exact (hehalf.le.trans hfle).trans hfsum

/-- At one endpoint, at most `2n` colors are forbidden while descending by
weight, provided the total star weight is at most `n`. -/
theorem card_forbiddenColors_le_two
    {q n : ℕ} (P : Finset G.E) (color : G.E → Fin q)
    (hdelta : G.deltaW ≤ n) (e : G.E)
    (horder : ∀ f ∈ P, G.weight e ≤ G.weight f) (v : G.V) :
    (G.forbiddenColors P color v e).card ≤ 2 * n := by
  classical
  let B := G.forbiddenColors P color v e
  have hhalf : ∀ i ∈ B, (1 / 2 : ℝ) ≤ G.colorLoadOn P color v i := by
    intro i hi
    exact G.half_le_load_of_mem_forbidden P color e horder v i hi
  have hsumB :
      ∑ i ∈ B, (1 / 2 : ℝ) ≤
        ∑ i ∈ B, G.colorLoadOn P color v i :=
    Finset.sum_le_sum hhalf
  have hsubset : B ⊆ Finset.univ := Finset.subset_univ B
  have hsumsub :
      ∑ i ∈ B, G.colorLoadOn P color v i ≤
        ∑ i : Fin q, G.colorLoadOn P color v i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _hi _hiB => G.colorLoadOn_nonneg P color v i)
  have htotal : ∑ i : Fin q, G.colorLoadOn P color v i ≤ n :=
    (G.sum_colorLoadOn_le_starWeight P color v).trans
      ((G.starWeight_le_deltaW v).trans hdelta)
  have hreal : ((B.card : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    have hconst : (∑ _i ∈ B, (1 / 2 : ℝ)) = (B.card : ℝ) / 2 := by
      simp [div_eq_mul_inv, mul_comm]
    rw [hconst] at hsumB
    nlinarith [hsumB.trans (hsumsub.trans htotal)]
  exact_mod_cast hreal

/-- One descending-weight greedy step using a palette of `4n+1` colors. -/
theorem extend_feasibleOn_four
    (n : ℕ) (P : Finset G.E) (color : G.E → Fin (4 * n + 1))
    (hfeas : G.IsFeasibleOn P color) (e : G.E) (heP : e ∉ P)
    (hdelta : G.deltaW ≤ n)
    (horder : ∀ f ∈ P, G.weight e ≤ G.weight f) :
    ∃ color' : G.E → Fin (4 * n + 1),
      G.IsFeasibleOn (insert e P) color' ∧
      ∀ f ∈ P, color' f = color f := by
  classical
  let Bfst := G.forbiddenColors P color (G.fst e) e
  let Bsnd := G.forbiddenColors P color (G.snd e) e
  have hfst : Bfst.card ≤ 2 * n :=
    G.card_forbiddenColors_le_two P color hdelta e horder (G.fst e)
  have hsnd : Bsnd.card ≤ 2 * n :=
    G.card_forbiddenColors_le_two P color hdelta e horder (G.snd e)
  have hcard : (Bfst ∪ Bsnd).card < (Finset.univ : Finset (Fin (4 * n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hunion := Finset.card_union_le Bfst Bsnd
    omega
  have hne : Bfst ∪ Bsnd ≠ (Finset.univ : Finset (Fin (4 * n + 1))) := by
    intro heq
    rw [heq] at hcard
    exact (Nat.lt_irrefl _ hcard)
  have hssub : Bfst ∪ Bsnd ⊂ (Finset.univ : Finset (Fin (4 * n + 1))) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩
  rcases Finset.exists_of_ssubset hssub with ⟨i, _hiuniv, hi⟩
  have hiFst : G.colorLoadOn P color (G.fst e) i + G.weight e ≤ 1 := by
    have : i ∉ Bfst := fun h => hi (Finset.mem_union_left _ h)
    simpa [Bfst, forbiddenColors] using this
  have hiSnd : G.colorLoadOn P color (G.snd e) i + G.weight e ≤ 1 := by
    have : i ∉ Bsnd := fun h => hi (Finset.mem_union_right _ h)
    simpa [Bsnd, forbiddenColors] using this
  let color' : G.E → Fin (4 * n + 1) := Function.update color e i
  refine ⟨color', ?_, ?_⟩
  · intro v j
    dsimp only [color']
    rw [G.colorLoadOn_insert_update P color e i heP v j]
    by_cases hinc : G.Inc v e
    · rcases hinc with hve | hve
      · subst v
        by_cases hij : i = j
        · subst j
          simpa [Inc] using hiFst
        · simp [hij]
          exact hfeas _ _
      · subst v
        by_cases hij : i = j
        · subst j
          simpa [Inc] using hiSnd
        · simp [hij]
          exact hfeas _ _
    · simp [hinc]
      exact hfeas _ _
  · intro f hf
    dsimp only [color']
    apply Function.update_of_ne
    intro hfe
    exact heP (hfe ▸ hf)

/-- Descending-weight greedy cleanup: if every star has total weight at most
`n`, the whole weighted multigraph can be colored with `4n+1` colors. -/
theorem hasWeightedColoring_four_add_one
    (n : ℕ) (hdelta : G.deltaW ≤ n) :
    G.HasWeightedColoring (4 * n + 1) := by
  classical
  have hsub : ∀ S : Finset G.E,
      ∃ color : G.E → Fin (4 * n + 1), G.IsFeasibleOn S color := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
        by_cases hS : S.Nonempty
        · rcases Finset.exists_min_image S G.weight hS with ⟨e, heS, hemin⟩
          let P := S.erase e
          have hPsub : P ⊂ S := Finset.erase_ssubset heS
          rcases ih P hPsub with ⟨color, hcolor⟩
          have heP : e ∉ P := by simp [P]
          have horder : ∀ f ∈ P, G.weight e ≤ G.weight f := by
            intro f hf
            exact hemin f (Finset.mem_of_mem_erase hf)
          rcases G.extend_feasibleOn_four n P color hcolor e heP hdelta horder with
            ⟨color', hcolor', _hpreserve⟩
          refine ⟨color', ?_⟩
          simpa [P, Finset.insert_erase heS] using hcolor'
        · have hSeq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
          subst S
          let color : G.E → Fin (4 * n + 1) := fun _ => ⟨0, by omega⟩
          refine ⟨color, ?_⟩
          intro v i
          simp [colorLoadOn]
  rcases hsub Finset.univ with ⟨color, hcolor⟩
  exact ⟨color, (G.isWeightedColoring_iff_feasibleOn_univ color).2 hcolor⟩

/-- The optimum form of the cleanup bound. -/
theorem chiW_le_four_ceil_add_one :
    G.chiW ≤ 4 * Nat.ceil G.deltaW + 1 := by
  apply G.chiW_le_of_hasWeightedColoring
  exact G.hasWeightedColoring_four_add_one (Nat.ceil G.deltaW)
    (Nat.le_ceil G.deltaW)

end WeightedMultigraph
end WeightedEdgeColoring
