import WeightedEdgeColoring.NumericInsertion

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- Load of a color contributed by a chosen finite set of edges. -/
def colorLoadOn {q : ℕ} (P : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (i : Fin q) : ℝ :=
  ∑ e ∈ P, if G.Inc v e ∧ color e = i then G.weight e else 0

/-- Feasibility restricted to the edges in `P`. -/
def IsFeasibleOn {q : ℕ} (P : Finset G.E) (color : G.E → Fin q) : Prop :=
  ∀ v i, G.colorLoadOn P color v i ≤ 1

/-- Properness of an ordinary edge coloring on the selected edge set. -/
def IsProperOn {q : ℕ} (F : Finset G.E) (color : G.E → Fin q) : Prop :=
  ∀ v, Set.InjOn color (F.filter (G.Inc v) : Set G.E)

/-- An ordinary proper coloring is automatically feasible for weights at most
one: each vertex-color pair contains at most one selected edge. -/
theorem isFeasibleOn_of_isProperOn {q : ℕ} (F : Finset G.E)
    (color : G.E → Fin q) (hproper : G.IsProperOn F color) :
    G.IsFeasibleOn F color := by
  classical
  intro v i
  rw [colorLoadOn, ← Finset.sum_filter]
  let Q := F.filter fun e => G.Inc v e ∧ color e = i
  have hcard : Q.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply hproper v
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨ha'.1, ha'.2.1⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hb'.1, hb'.2.1⟩)
    · exact ha'.2.2.trans hb'.2.2.symm
  calc
    (∑ e ∈ Q, G.weight e) ≤ ∑ _e ∈ Q, (1 : ℝ) := by
      exact Finset.sum_le_sum fun e _ => G.weight_le_one e
    _ = (Q.card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hcard

/-- Skeleton edges at `v` that were processed no later than `e`. -/
noncomputable def heavyWitnessEdges (F : Finset G.E) (v : G.V) (e : G.E) : Finset G.E :=
  F.filter fun f => G.Inc v f ∧ G.weight e ≤ G.weight f

/-- One endpoint of every edge outside the skeleton has `2n` earlier
skeleton edges. -/
noncomputable def HasHeavySkeletonWitnesses (F : Finset G.E) (n : ℕ) : Prop :=
  ∀ e ∉ F,
    2 * n ≤ (G.heavyWitnessEdges F (G.fst e) e).card ∨
    2 * n ≤ (G.heavyWitnessEdges F (G.snd e) e).card

theorem colorLoadOn_nonneg {q : ℕ} (P : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (i : Fin q) : 0 ≤ G.colorLoadOn P color v i := by
  classical
  exact Finset.sum_nonneg fun e _ => by
    split <;> simp [G.weight_nonneg]

/-- A proper skeleton turns `2n` earlier incident edges into `2n` distinct
colors whose present loads are at least the new edge weight. -/
theorem exists_witnessColors_of_heavyWitnessEdges
    {q n : ℕ} (F P : Finset G.E) (base color : G.E → Fin q)
    (hproper : G.IsProperOn F base) (hFP : F ⊆ P)
    (hagree : ∀ f ∈ F, color f = base f)
    (v : G.V) (e : G.E)
    (hheavy : 2 * n ≤ (G.heavyWitnessEdges F v e).card) :
    ∃ W : Finset (Fin q),
      2 * n ≤ W.card ∧
      ∀ i ∈ W, G.weight e ≤ G.colorLoadOn P color v i := by
  classical
  let A := G.heavyWitnessEdges F v e
  let W : Finset (Fin q) := A.image base
  have hAinc : (A : Set G.E) ⊆ (F.filter (G.Inc v) : Set G.E) := by
    intro f hf
    simp only [A, heavyWitnessEdges, Finset.mem_coe, Finset.mem_filter] at hf ⊢
    exact ⟨hf.1, hf.2.1⟩
  have hinj : Set.InjOn base (A : Set G.E) := (hproper v).mono hAinc
  have hcard : A.card = W.card := by
    exact (Finset.card_image_iff.mpr hinj).symm
  refine ⟨W, hcard ▸ hheavy, ?_⟩
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨f, hfA, rfl⟩
  have hf := Finset.mem_filter.mp hfA
  have hfP : f ∈ P := hFP hf.1
  have hcf : color f = base f := hagree f hf.1
  calc
    G.weight e ≤ G.weight f := hf.2.2
    _ = (if G.Inc v f ∧ color f = base f then G.weight f else 0) := by
      simp [hf.2.1, hcf]
    _ ≤ ∑ x ∈ P, if G.Inc v x ∧ color x = base f then G.weight x else 0 := by
      exact Finset.single_le_sum
        (s := P)
        (f := fun x => if G.Inc v x ∧ color x = base f then G.weight x else 0)
        (fun x _hx => by
          by_cases hx : G.Inc v x ∧ color x = base f
          · simp [hx, G.weight_nonneg]
          · simp [hx]) hfP
    _ = G.colorLoadOn P color v (base f) := rfl

theorem sum_colorLoadOn {q : ℕ} (P : Finset G.E) (color : G.E → Fin q)
    (v : G.V) :
    ∑ i, G.colorLoadOn P color v i =
      ∑ e ∈ P, if G.Inc v e then G.weight e else 0 := by
  classical
  simp only [colorLoadOn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hinc : G.Inc v e
  · simp [hinc]
  · simp [hinc]

theorem restrictedStarWeight_le_starWeight (P : Finset G.E) (v : G.V) :
    (∑ e ∈ P, if G.Inc v e then G.weight e else 0) ≤ G.starWeight v := by
  classical
  rw [starWeight, ← Finset.sum_subtype (Finset.univ.filter (G.Inc v)) (by simp)]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact he.2
  · intro e _hefull heP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heP
    exact G.weight_nonneg e

theorem weight_le_starWeight_fst (e : G.E) :
    G.weight e ≤ G.starWeight (G.fst e) := by
  have h := G.restrictedStarWeight_le_starWeight ({e} : Finset G.E) (G.fst e)
  simpa [Inc] using h

/-- A rejected edge with `2n` no-lighter skeleton witnesses has weight below
`1/2` whenever every star has total weight at most `n`. -/
theorem weight_lt_half_of_heavyWitnessEdges
    (n : ℕ) (F : Finset G.E) (e : G.E) (heF : e ∉ F)
    (v : G.V) (hve : G.Inc v e) (hdelta : G.deltaW ≤ n)
    (hheavy : 2 * n ≤ (G.heavyWitnessEdges F v e).card) :
    G.weight e < 1 / 2 := by
  classical
  let A := G.heavyWitnessEdges F v e
  have heA : e ∉ A := by
    intro he
    exact heF (Finset.mem_filter.mp he).1
  have hAweight :
      ((A.card : ℕ) : ℝ) * G.weight e ≤ ∑ f ∈ A, G.weight f := by
    calc
      ((A.card : ℕ) : ℝ) * G.weight e = ∑ _f ∈ A, G.weight e := by
        simp
      _ ≤ ∑ f ∈ A, G.weight f := by
        exact Finset.sum_le_sum fun f hf => (Finset.mem_filter.mp hf).2.2
  have hrestricted :
      G.weight e + ∑ f ∈ A, G.weight f ≤ G.starWeight v := by
    have hsub := G.restrictedStarWeight_le_starWeight (insert e A) v
    have hAinc : ∀ f ∈ A, G.Inc v f := by
      intro f hf
      exact (Finset.mem_filter.mp hf).2.1
    have hsumA :
        (∑ f ∈ A, if G.Inc v f then G.weight f else 0) =
          ∑ f ∈ A, G.weight f := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [hAinc f hf]
    rw [Finset.sum_insert heA] at hsub
    simp only [hve, if_true] at hsub
    rwa [hsumA] at hsub
  have hstar : G.starWeight v ≤ n := (G.starWeight_le_deltaW v).trans hdelta
  have hcardR : (2 * (n : ℝ)) ≤ (A.card : ℝ) := by
    exact_mod_cast hheavy
  have hwpos : 0 < G.weight e := G.weight_pos e
  nlinarith

theorem outside_weight_lt_half_of_heavySkeleton
    (n : ℕ) (F : Finset G.E) (hdelta : G.deltaW ≤ n)
    (hwitness : G.HasHeavySkeletonWitnesses F n) :
    ∀ e ∉ F, G.weight e < 1 / 2 := by
  intro e heF
  rcases hwitness e heF with hfst | hsnd
  · exact G.weight_lt_half_of_heavyWitnessEdges n F e heF (G.fst e)
      (Or.inl rfl) hdelta hfst
  · exact G.weight_lt_half_of_heavyWitnessEdges n F e heF (G.snd e)
      (Or.inr rfl) hdelta hsnd

theorem sum_colorLoadOn_le_starWeight {q : ℕ} (P : Finset G.E)
    (color : G.E → Fin q) (v : G.V) :
    ∑ i, G.colorLoadOn P color v i ≤ G.starWeight v := by
  rw [G.sum_colorLoadOn]
  exact G.restrictedStarWeight_le_starWeight P v

theorem colorLoadOn_insert_update {q : ℕ} (P : Finset G.E) (color : G.E → Fin q)
    (e : G.E) (i : Fin q) (he : e ∉ P) (v : G.V) (j : Fin q) :
    G.colorLoadOn (insert e P) (Function.update color e i) v j =
      G.colorLoadOn P color v j +
        (if G.Inc v e ∧ i = j then G.weight e else 0) := by
  classical
  unfold colorLoadOn
  rw [Finset.sum_insert he]
  have htail :
      (∑ x ∈ P, if G.Inc v x ∧ Function.update color e i x = j
        then G.weight x else 0) =
      ∑ x ∈ P, if G.Inc v x ∧ color x = j then G.weight x else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxe : x ≠ e := by
      intro h
      exact he (h ▸ hx)
    rw [Function.update_of_ne hxe]
  rw [htail]
  simp [add_comm]

theorem isWeightedColoring_iff_feasibleOn_univ {q : ℕ} (color : G.E → Fin q) :
    G.IsWeightedColoring color ↔ G.IsFeasibleOn Finset.univ color := by
  classical
  have hload (v : G.V) (i : Fin q) :
      G.colorLoadOn Finset.univ color v i = G.colorLoad color v i := by
    calc
      G.colorLoadOn Finset.univ color v i =
          ∑ e ∈ Finset.univ.filter (G.Inc v),
            if color e = i then G.weight e else 0 := by
              unfold colorLoadOn
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro e _he
              by_cases hinc : G.Inc v e <;> simp [hinc]
      _ = ∑ e : G.StarEdge v, if color e.1 = i then G.weight e.1 else 0 := by
            exact Finset.sum_subtype _ (by simp) _
      _ = G.colorLoad color v i := rfl
  constructor
  · intro h v i
    rw [hload]
    exact h v i
  · intro h v i
    rw [← hload]
    exact h v i

/-- Insert one edge into a feasible partial coloring.  The witness colors are
the `2n` distinct skeleton colors at one endpoint in the Shannon argument. -/
theorem extend_feasibleOn_three
    (n : ℕ) (hn : 1 ≤ n) (P : Finset G.E)
    (color : G.E → Fin (3 * n)) (hfeas : G.IsFeasibleOn P color)
    (e : G.E) (he : e ∉ P) (hdelta : G.deltaW ≤ n)
    (hhalf : G.weight e < 1 / 2)
    (hwitness :
      (∃ W : Finset (Fin (3 * n)),
        2 * n ≤ W.card ∧
        ∀ i ∈ W, G.weight e ≤ G.colorLoadOn P color (G.fst e) i) ∨
      (∃ W : Finset (Fin (3 * n)),
        2 * n ≤ W.card ∧
        ∀ i ∈ W, G.weight e ≤ G.colorLoadOn P color (G.snd e) i)) :
    ∃ color' : G.E → Fin (3 * n),
      G.IsFeasibleOn (insert e P) color' ∧
      ∀ x ∈ P, color' x = color x := by
  classical
  have hsum (v : G.V) : ∑ i, G.colorLoadOn P color v i ≤ n :=
    (G.sum_colorLoadOn_le_starWeight P color v).trans
      ((G.starWeight_le_deltaW v).trans hdelta)
  have hnonneg (v : G.V) (i : Fin (3 * n)) :
      0 ≤ G.colorLoadOn P color v i := G.colorLoadOn_nonneg P color v i
  have hroom : ∃ i,
      G.colorLoadOn P color (G.fst e) i + G.weight e ≤ 1 ∧
      G.colorLoadOn P color (G.snd e) i + G.weight e ≤ 1 := by
    rcases hwitness with ⟨W, hWcard, hWload⟩ | ⟨W, hWcard, hWload⟩
    · exact exists_common_room_of_two_thirds_witness n hn (G.weight e)
        (G.weight_pos e) hhalf
        (fun i => G.colorLoadOn P color (G.fst e) i)
        (fun i => G.colorLoadOn P color (G.snd e) i)
        (hnonneg _) (hnonneg _) (hsum _) (hsum _) W hWcard hWload
    · rcases exists_common_room_of_two_thirds_witness n hn (G.weight e)
          (G.weight_pos e) hhalf
          (fun i => G.colorLoadOn P color (G.snd e) i)
          (fun i => G.colorLoadOn P color (G.fst e) i)
          (hnonneg _) (hnonneg _) (hsum _) (hsum _) W hWcard hWload with
        ⟨i, hiSnd, hiFst⟩
      exact ⟨i, hiFst, hiSnd⟩
  rcases hroom with ⟨i, hiFst, hiSnd⟩
  let color' : G.E → Fin (3 * n) := Function.update color e i
  refine ⟨color', ?_, ?_⟩
  · intro v j
    dsimp only [color']
    rw [G.colorLoadOn_insert_update P color e i he v j]
    by_cases hinc : G.Inc v e
    · rcases hinc with hfst | hsnd
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
  · intro x hx
    dsimp only [color']
    apply Function.update_of_ne
    intro hxe
    exact he (hxe ▸ hx)

/-- Once a properly colored Shannon skeleton has the heavy-witness property,
all remaining edges can be inserted into the same `3n` colors. -/
theorem hasWeightedColoring_three_of_skeleton
    (n : ℕ) (hn : 1 ≤ n) (F : Finset G.E)
    (base : G.E → Fin (3 * n))
    (hproper : G.IsProperOn F base)
    (hfeas : G.IsFeasibleOn F base)
    (hdelta : G.deltaW ≤ n)
    (hwitness : G.HasHeavySkeletonWitnesses F n)
    (hhalf : ∀ e ∉ F, G.weight e < 1 / 2) :
    G.HasWeightedColoring (3 * n) := by
  classical
  have extend_set : ∀ R : Finset G.E, R ⊆ Finset.univ \ F →
      ∃ color : G.E → Fin (3 * n),
        G.IsFeasibleOn (F ∪ R) color ∧
        ∀ f ∈ F, color f = base f := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
        intro _hsub
        exact ⟨base, by simpa using hfeas, fun _ hf => rfl⟩
    | @insert e R heR ih =>
        intro hsub
        have heComp : e ∈ Finset.univ \ F := hsub (Finset.mem_insert_self e R)
        have heF : e ∉ F := (Finset.mem_sdiff.mp heComp).2
        have hRsub : R ⊆ Finset.univ \ F := fun x hx => hsub (Finset.mem_insert_of_mem hx)
        rcases ih hRsub with ⟨color, hcolorFeas, hagree⟩
        let P : Finset G.E := F ∪ R
        have hFP : F ⊆ P := Finset.subset_union_left
        have heP : e ∉ P := by
          simp [P, heF, heR]
        have hcolors :
            (∃ W : Finset (Fin (3 * n)),
              2 * n ≤ W.card ∧
              ∀ i ∈ W, G.weight e ≤ G.colorLoadOn P color (G.fst e) i) ∨
            (∃ W : Finset (Fin (3 * n)),
              2 * n ≤ W.card ∧
              ∀ i ∈ W, G.weight e ≤ G.colorLoadOn P color (G.snd e) i) := by
          rcases hwitness e heF with hfirst | hsecond
          · exact Or.inl (G.exists_witnessColors_of_heavyWitnessEdges
              F P base color hproper hFP hagree (G.fst e) e hfirst)
          · exact Or.inr (G.exists_witnessColors_of_heavyWitnessEdges
              F P base color hproper hFP hagree (G.snd e) e hsecond)
        rcases G.extend_feasibleOn_three n hn P color hcolorFeas e heP hdelta
            (hhalf e heF) hcolors with ⟨color', hcolor'Feas, hpreserve⟩
        refine ⟨color', ?_, ?_⟩
        · simpa [P, Finset.union_insert] using hcolor'Feas
        · intro f hf
          exact (hpreserve f (hFP hf)).trans (hagree f hf)
  rcases extend_set (Finset.univ \ F) (by simp) with ⟨color, hcolor, _hagree⟩
  refine ⟨color, (G.isWeightedColoring_iff_feasibleOn_univ color).2 ?_⟩
  simpa [Finset.union_sdiff_of_subset (Finset.subset_univ F)] using hcolor

/-- The heavy-witness condition itself forces every outside edge below one
half, so the insertion theorem needs no separate weight hypothesis. -/
theorem hasWeightedColoring_three_of_heavySkeleton
    (n : ℕ) (hn : 1 ≤ n) (F : Finset G.E)
    (base : G.E → Fin (3 * n))
    (hproper : G.IsProperOn F base)
    (hfeas : G.IsFeasibleOn F base)
    (hdelta : G.deltaW ≤ n)
    (hwitness : G.HasHeavySkeletonWitnesses F n) :
    G.HasWeightedColoring (3 * n) :=
  G.hasWeightedColoring_three_of_skeleton n hn F base hproper hfeas hdelta
    hwitness (G.outside_weight_lt_half_of_heavySkeleton n F hdelta hwitness)

end WeightedMultigraph
end WeightedEdgeColoring
