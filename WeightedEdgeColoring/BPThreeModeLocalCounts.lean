import WeightedEdgeColoring.BPThreeModeData

/-!
# Local packing counts for the three compatible modes

The rounded three-mode construction needs two local degree bounds.  Heavy
edges use at most one place in each local bin.  The combined heavy/light
count has the scaled bound

`k * dH + r * dS ≤ r * k * bp`,

where `r = 2` and `k` is the mode class.  For the third mode this is the
nontrivial integer inequality `3*dH + 2*dS ≤ 6*bp`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- A local degree is the sum of its counts in the bins of any explicit
star packing. -/
theorem degreeOn_eq_sum_bin_card (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) :
    G.degreeOn F v =
      ∑ i : Fin n,
        ((Finset.univ.filter fun e : G.StarEdge v => e.1 ∈ F).filter
          fun e => bin e = i).card := by
  classical
  let T : Finset (G.StarEdge v) :=
    Finset.univ.filter fun e => e.1 ∈ F
  have hcard : T.card = G.degreeOn F v := by
    let emb : G.StarEdge v ↪ G.E :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hmap : T.map emb = F.filter (G.Inc v) := by
      ext e
      simp [T, emb]
    rw [degreeOn, ← hmap, Finset.card_map]
  change G.degreeOn F v =
    ∑ i : Fin n, (T.filter fun e => bin e = i).card
  rw [← hcard]
  calc
    T.card = ∑ e ∈ T, 1 := by simp
    _ = ∑ e ∈ T, ∑ i : Fin n, if bin e = i then 1 else 0 := by simp
    _ = ∑ i : Fin n, ∑ e ∈ T, if bin e = i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, (T.filter fun e => bin e = i).card := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp

/-- The local integer estimate behind mode 3.  A heavy item has size above
`1/2` and a light item has size above `1/4`.  In one bin, if their counts are
`h,s`, then `2h+s≤3`, and hence `3h+2s≤6`. -/
theorem three_mul_degree_add_two_mul_degree_le_six_mul_of_packsStarInto
    (H S : Finset G.E) (hdisj : Disjoint H S)
    {v : G.V} {n : ℕ} (hpack : G.PacksStarInto v n)
    (hheavy : ∀ e ∈ H, (1 / 2 : ℝ) < G.weight e)
    (hlight : ∀ e ∈ S, (1 / 4 : ℝ) < G.weight e) :
    3 * G.degreeOn H v + 2 * G.degreeOn S v ≤ 6 * n := by
  classical
  rcases hpack with ⟨bin, hbin⟩
  let TH : Finset (G.StarEdge v) :=
    Finset.univ.filter fun e => e.1 ∈ H
  let TS : Finset (G.StarEdge v) :=
    Finset.univ.filter fun e => e.1 ∈ S
  let FH : Fin n → Finset (G.StarEdge v) := fun i =>
    TH.filter fun e => bin e = i
  let FS : Fin n → Finset (G.StarEdge v) := fun i =>
    TS.filter fun e => bin e = i
  have hlocal (i : Fin n) :
      3 * (FH i).card + 2 * (FS i).card ≤ 6 := by
    have hHFdisj : Disjoint (FH i) (FS i) := by
      rw [Finset.disjoint_left]
      intro e heH heS
      exact Finset.disjoint_left.mp hdisj
        (Finset.mem_filter.mp (Finset.mem_filter.mp heH).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp heS).1).2
    have hHle :
        ∑ _e ∈ FH i, (1 / 2 : ℝ) ≤
          ∑ e ∈ FH i, G.weight e.1 := by
      exact Finset.sum_le_sum fun e he =>
        (hheavy e.1
          (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2).le
    have hSle :
        ∑ _e ∈ FS i, (1 / 4 : ℝ) ≤
          ∑ e ∈ FS i, G.weight e.1 := by
      exact Finset.sum_le_sum fun e he =>
        (hlight e.1
          (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2).le
    by_cases hU : (FH i ∪ FS i).Nonempty
    · have hstrict :
          (FH i).card * (1 / 2 : ℝ) +
              (FS i).card * (1 / 4 : ℝ) <
            (∑ e ∈ FH i, G.weight e.1) +
              ∑ e ∈ FS i, G.weight e.1 := by
        rcases hU with ⟨e, he⟩
        rcases Finset.mem_union.mp he with heH | heS
        · have hHlt :
              ∑ _e ∈ FH i, (1 / 2 : ℝ) <
                ∑ e ∈ FH i, G.weight e.1 :=
            Finset.sum_lt_sum_of_nonempty ⟨e, heH⟩ (by
              intro f hf
              exact hheavy f.1
                (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
          simpa using add_lt_add_of_lt_of_le hHlt hSle
        · have hSlt :
              ∑ _e ∈ FS i, (1 / 4 : ℝ) <
                ∑ e ∈ FS i, G.weight e.1 :=
            Finset.sum_lt_sum_of_nonempty ⟨e, heS⟩ (by
              intro f hf
              exact hlight f.1
                (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2)
          simpa using add_lt_add_of_le_of_lt hHle hSlt
      have hload :
          (∑ e ∈ FH i, G.weight e.1) +
              ∑ e ∈ FS i, G.weight e.1 ≤ 1 := by
        calc
          (∑ e ∈ FH i, G.weight e.1) +
                ∑ e ∈ FS i, G.weight e.1 =
              ∑ e ∈ FH i ∪ FS i, G.weight e.1 := by
            rw [Finset.sum_union hHFdisj]
          _ ≤ ∑ e : G.StarEdge v,
                if bin e = i then G.weight e.1 else 0 := by
            rw [← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro e he
              rcases Finset.mem_union.mp he with heH | heS
              · exact Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, (Finset.mem_filter.mp heH).2⟩
              · exact Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, (Finset.mem_filter.mp heS).2⟩
            · intro e _he _hne
              exact G.weight_nonneg e.1
          _ ≤ 1 := hbin i
      have hreal :
          (((2 * (FH i).card + (FS i).card : ℕ) : ℝ)) < 4 := by
        push_cast
        norm_num only [Nat.cast_ofNat] at hstrict
        nlinarith
      have hnat : 2 * (FH i).card + (FS i).card < 4 := by
        exact_mod_cast hreal
      omega
    · have hempty : FH i ∪ FS i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      have hFH : FH i = ∅ := by
        apply Finset.Subset.antisymm
        · intro e he
          have heu : e ∈ FH i ∪ FS i := Finset.mem_union_left _ he
          rw [hempty] at heu
          exact heu
        · exact Finset.empty_subset _
      have hFS : FS i = ∅ := by
        apply Finset.Subset.antisymm
        · intro e he
          have heu : e ∈ FH i ∪ FS i := Finset.mem_union_right _ he
          rw [hempty] at heu
          exact heu
        · exact Finset.empty_subset _
      simp [hFH, hFS]
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hlocal i)
  have hHpartition :
      G.degreeOn H v = ∑ i : Fin n, (FH i).card := by
    simpa [TH, FH] using G.degreeOn_eq_sum_bin_card H bin
  have hSpartition :
      G.degreeOn S v = ∑ i : Fin n, (FS i).card := by
    simpa [TS, FS] using G.degreeOn_eq_sum_bin_card S bin
  rw [Finset.sum_add_distrib] at hsum
  simp only [← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  simpa [hHpartition, hSpartition, Nat.mul_comm] using hsum

/-- Every three-mode heavy degree is at most the local bin-packing number. -/
theorem threeModeHeavy_degree_le_bp (m : ThreeMode) (v : G.V) :
    G.degreeOn (G.threeModeHeavyEdges m) v ≤ G.bp := by
  simpa using
    (G.degreeOn_le_mul_of_packsStarInto (G.threeModeHeavyEdges m)
      (G.locallyPacksInto_bp v) (k := 1) (by
        intro e he
        norm_num
        exact (Finset.mem_filter.mp he).2.1))

/-- Exact natural-number scaled count for every mode. -/
theorem threeMode_scaled_local_count_le (m : ThreeMode) (v : G.V) :
    threeModeClassK m * G.degreeOn (G.threeModeHeavyEdges m) v +
        threeModeCopies m * G.degreeOn (G.threeModeLightEdges m) v ≤
      threeModeCopies m * threeModeClassK m * G.bp := by
  fin_cases m
  · have hdisj := G.threeModeHeavy_light_disjoint (0 : ThreeMode)
    have hcount := G.degreeOn_le_mul_of_packsStarInto
      (G.threeModeHeavyEdges (0 : ThreeMode) ∪
        G.threeModeLightEdges (0 : ThreeMode))
      (G.locallyPacksInto_bp v) (k := 2) (by
        intro e he
        rcases Finset.mem_union.mp he with heH | heS
        · have h := (Finset.mem_filter.mp heH).2.1
          norm_num at h ⊢
          linarith
        · norm_num [threeModeClassK]
          exact (Finset.mem_filter.mp heS).2.1)
    rw [G.degreeOn_union_of_disjoint hdisj v] at hcount
    norm_num [threeModeClassK, threeModeCopies] at ⊢
    omega
  · have hdisj := G.threeModeHeavy_light_disjoint (1 : ThreeMode)
    have hcount := G.degreeOn_le_mul_of_packsStarInto
      (G.threeModeHeavyEdges (1 : ThreeMode) ∪
        G.threeModeLightEdges (1 : ThreeMode))
      (G.locallyPacksInto_bp v) (k := 2) (by
        intro e he
        rcases Finset.mem_union.mp he with heH | heS
        · have h := (Finset.mem_filter.mp heH).2.1
          norm_num at h ⊢
          linarith
        · norm_num [threeModeClassK]
          exact (Finset.mem_filter.mp heS).2.1)
    rw [G.degreeOn_union_of_disjoint hdisj v] at hcount
    norm_num [threeModeClassK, threeModeCopies] at ⊢
    omega
  · have hdisj := G.threeModeHeavy_light_disjoint (2 : ThreeMode)
    have hcount :=
      G.three_mul_degree_add_two_mul_degree_le_six_mul_of_packsStarInto
        (G.threeModeHeavyEdges (2 : ThreeMode))
        (G.threeModeLightEdges (2 : ThreeMode)) hdisj
        (G.locallyPacksInto_bp v)
        (by
          intro e he
          exact (Finset.mem_filter.mp he).2.1)
        (by
          intro e he
          simpa [threeModeClassK] using
            (Finset.mem_filter.mp he).2.1)
    simpa [threeModeClassK, threeModeCopies] using hcount

/-- Cast/division form of the scaled local count. -/
theorem threeMode_compatible_local_count_le (m : ThreeMode) (v : G.V) :
    (G.degreeOn (G.threeModeHeavyEdges m) v : ℝ) +
        ((threeModeCopies m : ℝ) / threeModeClassK m) *
          (G.degreeOn (G.threeModeLightEdges m) v : ℝ) ≤
      (threeModeCopies m : ℝ) * G.bp := by
  have h := G.threeMode_scaled_local_count_le m v
  have hk : (0 : ℝ) < threeModeClassK m := by
    exact_mod_cast threeModeClassK_pos m
  have hreal :
      (threeModeClassK m : ℝ) *
          (G.degreeOn (G.threeModeHeavyEdges m) v : ℝ) +
        (threeModeCopies m : ℝ) *
          (G.degreeOn (G.threeModeLightEdges m) v : ℝ) ≤
        (threeModeCopies m : ℝ) * threeModeClassK m * G.bp := by
    exact_mod_cast h
  calc
    (G.degreeOn (G.threeModeHeavyEdges m) v : ℝ) +
          ((threeModeCopies m : ℝ) / threeModeClassK m) *
            (G.degreeOn (G.threeModeLightEdges m) v : ℝ) =
        ((threeModeClassK m : ℝ) *
              (G.degreeOn (G.threeModeHeavyEdges m) v : ℝ) +
            (threeModeCopies m : ℝ) *
              (G.degreeOn (G.threeModeLightEdges m) v : ℝ)) /
          threeModeClassK m := by
      field_simp
    _ ≤ ((threeModeCopies m : ℝ) * threeModeClassK m * G.bp) /
          threeModeClassK m := by
      exact div_le_div_of_nonneg_right hreal hk.le
    _ = (threeModeCopies m : ℝ) * G.bp := by
      field_simp

/-- The mode probabilities are tuned exactly to the scaled local count. -/
theorem threeMode_probability_local_count_le (m : ThreeMode) (v : G.V) :
    threeModeHeavyProbability m *
          (G.degreeOn (G.threeModeHeavyEdges m) v : ℝ) +
        threeModeLightProbability m *
          (G.degreeOn (G.threeModeLightEdges m) v : ℝ) ≤
      (threeModeCopies m : ℝ) * threeModeHeavyProbability m * G.bp := by
  have h := G.threeMode_compatible_local_count_le m v
  fin_cases m <;>
    norm_num [threeModeHeavyProbability, threeModeLightProbability,
      threeModeClassK, threeModeCopies] at h ⊢ <;> linarith

/-- Palette size assigned to one rounded compatible mode. -/
noncomputable def threeModePaletteSize (m : ThreeMode) : ℕ :=
  Nat.ceil (threeModeHeavyProbability m * (G.bp : ℝ)) + 2

/-- The exact degree bounds consumed by the compatible-copy coloring lemma
after the heavy and light rows have each been rounded with additive error
two. -/
theorem threeMode_rounded_local_degree_bounds
    (m : ThreeMode) (v : G.V) (selectedHeavy selectedLight : Finset G.E)
    (hselectedHeavy :
      (G.degreeOn selectedHeavy v : ℝ) ≤
        threeModeHeavyProbability m *
          (G.degreeOn (G.threeModeHeavyEdges m) v : ℝ) + 2)
    (hselectedLight :
      (G.degreeOn selectedLight v : ℝ) ≤
        threeModeLightProbability m *
          (G.degreeOn (G.threeModeLightEdges m) v : ℝ) + 2) :
    G.degreeOn selectedHeavy v ≤ G.threeModePaletteSize m ∧
      G.degreeOn selectedHeavy v + G.degreeOn selectedLight v ≤
        threeModeCopies m * G.threeModePaletteSize m := by
  have hp : 0 ≤ threeModeHeavyProbability m :=
    threeModeHeavyProbability_nonneg m
  have hbase := G.threeModeHeavy_degree_le_bp m v
  have hbaseR :
      (G.degreeOn (G.threeModeHeavyEdges m) v : ℝ) ≤ G.bp := by
    exact_mod_cast hbase
  have hheavyFrac :
      threeModeHeavyProbability m *
          (G.degreeOn (G.threeModeHeavyEdges m) v : ℝ) ≤
        threeModeHeavyProbability m * G.bp :=
    mul_le_mul_of_nonneg_left hbaseR hp
  have hceil :
      threeModeHeavyProbability m * (G.bp : ℝ) ≤
        (Nat.ceil (threeModeHeavyProbability m * (G.bp : ℝ)) : ℕ) :=
    Nat.le_ceil _
  constructor
  · have hreal :
        (G.degreeOn selectedHeavy v : ℝ) ≤
          (G.threeModePaletteSize m : ℕ) := by
      dsimp [threeModePaletteSize]
      push_cast
      linarith
    exact_mod_cast hreal
  · have hprob := G.threeMode_probability_local_count_le m v
    have hcopy : threeModeCopies m = 2 := threeModeCopies_eq_two m
    rw [hcopy] at hprob
    norm_num only [Nat.cast_ofNat] at hprob
    have hreal :
        ((G.degreeOn selectedHeavy v + G.degreeOn selectedLight v : ℕ) : ℝ) ≤
          ((threeModeCopies m * G.threeModePaletteSize m : ℕ) : ℝ) := by
      push_cast
      dsimp [threeModePaletteSize]
      push_cast
      rw [hcopy]
      norm_num only [Nat.cast_ofNat]
      nlinarith
    exact_mod_cast hreal

end WeightedMultigraph
end WeightedEdgeColoring
