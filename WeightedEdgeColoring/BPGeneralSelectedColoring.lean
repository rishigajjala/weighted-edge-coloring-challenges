import WeightedEdgeColoring.BPCompatibleColoring
import WeightedEdgeColoring.ShannonBridge

/-!
# Coloring the selected part of the general-multigraph construction

This file proves the finite coloring lemma used for the selected edges in
the general `bp` bound.  Edges in `A` have weight at most `3/5`, edges in
`B` have weight at most `2/5`, and the two sets are disjoint.  At every
vertex, the `A`-degree is at most `K` and the total degree is at most `2K`.

We put all `A` incidences in copy zero of a vertex and distribute the `B`
incidences between its two copies, each of degree at most `K`.  Shannon's
ordinary construction colors the split multigraph with
`3 * ((K + 1) / 2)` colors.  When the copies are identified again, one
color contains at most two edges at a vertex and at most one of them lies
in `A`; its weighted load is therefore at most one.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable {G : WeightedMultigraph.{u}}

/-- The selected `A ∪ B` part has a weighted coloring with
`3 * ceil(K/2)` colors.  For natural `K`, `ceil(K/2) = (K+1)/2`. -/
theorem exists_feasibleOn_union_three_half_of_degree
    (A B : Finset G.E) (hdisj : Disjoint A B)
    (K : ℕ) (hK : 0 < K)
    (hAweight : ∀ e ∈ A, G.weight e ≤ (3 : ℝ) / 5)
    (hBweight : ∀ e ∈ B, G.weight e ≤ (2 : ℝ) / 5)
    (hAdegree : ∀ v, G.degreeOn A v ≤ K)
    (htotalDegree : ∀ v, G.degreeOn A v + G.degreeOn B v ≤ 2 * K) :
    ∃ color : G.E → Fin (3 * ((K + 1) / 2)),
      G.IsFeasibleOn (A ∪ B) color := by
  classical
  let n : ℕ := (K + 1) / 2
  have hn : 0 < n := by
    dsimp [n]
    omega
  have hKn : K ≤ 2 * n := by
    dsimp [n]
    omega
  have hcopyExists : ∀ v : G.V,
      ∃ copy : G.E → Fin 2,
        (∀ e ∉ B.filter (G.Inc v), (copy e).1 = 0) ∧
        ((B.filter (G.Inc v)).filter fun e ↦ (copy e).1 = 0).card ≤
          K - G.degreeOn A v ∧
        ∀ k : Fin 2, k.1 ≠ 0 →
          ((B.filter (G.Inc v)).filter fun e ↦ copy e = k).card ≤ K := by
    intro v
    apply exists_compatibleCopyAssignment
    · omega
    · exact hAdegree v
    · have hv := htotalDegree v
      simp only [degreeOn] at hv ⊢
      omega
  choose copyAt hcopyOutside hcopyZero hcopyNonzero using hcopyExists
  have hlocalCopyDegree : ∀ v (k : Fin 2),
      ((A ∪ B).filter fun e ↦ G.Inc v e ∧ copyAt v e = k).card ≤ K := by
    intro v k
    let FA := A.filter fun e ↦ G.Inc v e ∧ copyAt v e = k
    let FB := B.filter fun e ↦ G.Inc v e ∧ copyAt v e = k
    have hsplit :
        ((A ∪ B).filter fun e ↦ G.Inc v e ∧ copyAt v e = k) = FA ∪ FB := by
      ext e
      simp only [FA, FB, Finset.mem_filter, Finset.mem_union]
      aesop
    have hABdisj : Disjoint FA FB := by
      exact hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [hsplit, Finset.card_union_of_disjoint hABdisj]
    by_cases hk : k.1 = 0
    · have hFA : FA.card ≤ G.degreeOn A v := by
        exact Finset.card_le_card (by
          intro e he
          have he' := Finset.mem_filter.mp he
          exact Finset.mem_filter.mpr ⟨he'.1, he'.2.1⟩)
      have hFB : FB.card ≤ K - G.degreeOn A v := by
        have hEq : FB =
            (B.filter (G.Inc v)).filter (fun e ↦ (copyAt v e).1 = 0) := by
          ext e
          simp only [FB, Finset.mem_filter]
          constructor
          · rintro ⟨heB, heInc, heCopy⟩
            exact ⟨⟨heB, heInc⟩, by simpa [heCopy] using hk⟩
          · rintro ⟨⟨heB, heInc⟩, heZero⟩
            refine ⟨heB, heInc, Fin.ext ?_⟩
            simpa [hk] using heZero
        rw [hEq]
        exact hcopyZero v
      have hd := hAdegree v
      omega
    · have hFA0 : FA = ∅ := by
        apply Finset.Subset.antisymm
        · intro e he
          have he' := Finset.mem_filter.mp he
          have heNB : e ∉ B := fun heB ↦
            Finset.disjoint_left.mp hdisj he'.1 heB
          have heNFB : e ∉ B.filter (G.Inc v) := by simp [heNB]
          have hz := hcopyOutside v e heNFB
          have hkEq := congrArg Fin.val he'.2.2
          exact (hk (hkEq.symm.trans hz)).elim
        · exact Finset.empty_subset _
      have hFB : FB.card ≤ K := by
        have hEq : FB =
            (B.filter (G.Inc v)).filter (fun e ↦ copyAt v e = k) := by
          ext e
          simp [FB, and_assoc]
        rw [hEq]
        exact hcopyNonzero v k hk
      simp [hFA0, hFB]
  let left : G.E → G.V × Fin 2 := fun e ↦
    (G.fst e, copyAt (G.fst e) e)
  let right : G.E → G.V × Fin 2 := fun e ↦
    (G.snd e, copyAt (G.snd e) e)
  have hsplitDegree : ∀ x : G.V × Fin 2,
      OrdinaryEdgeColoring.DegreeOn left right (A ∪ B) x ≤ K := by
    rintro ⟨v, k⟩
    apply (Finset.card_le_card ?_).trans (hlocalCopyDegree v k)
    intro e he
    have he' := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨he'.1, ?_⟩
    rcases he'.2 with heLeft | heRight
    · have hv : G.fst e = v := by
        simpa [left] using congrArg Prod.fst heLeft
      have hk' : copyAt (G.fst e) e = k := by
        simpa [left] using congrArg Prod.snd heLeft
      refine ⟨Or.inl hv, ?_⟩
      simpa [hv] using hk'
    · have hv : G.snd e = v := by
        simpa [right] using congrArg Prod.fst heRight
      have hk' : copyAt (G.snd e) e = k := by
        simpa [right] using congrArg Prod.snd heRight
      refine ⟨Or.inr hv, ?_⟩
      simpa [hv] using hk'
  have hloop : ∀ e ∈ A ∪ B, left e ≠ right e := by
    intro e _he hEq
    exact G.noLoop e (congrArg Prod.fst hEq)
  obtain ⟨color, hproper⟩ :=
    OrdinaryEdgeColoring.exists_endpointProper_fin_three_mul_of_degreeOn_le_two_mul
      left right (A ∪ B) n hn hloop (fun x ↦
        (hsplitDegree x).trans hKn)
  refine ⟨color, ?_⟩
  intro v i
  let Q := (A ∪ B).filter fun e ↦ G.Inc v e ∧ color e = i
  let QA := A.filter fun e ↦ G.Inc v e ∧ color e = i
  let QB := B.filter fun e ↦ G.Inc v e ∧ color e = i
  have hQsplit : Q = QA ∪ QB := by
    ext e
    simp only [Q, QA, QB, Finset.mem_filter, Finset.mem_union]
    aesop
  have hQdisj : Disjoint QA QB := by
    exact hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcopyInj : Set.InjOn (copyAt v) (Q : Set G.E) := by
    intro e heQ f hfQ hcopies
    have he := Finset.mem_filter.mp (Finset.mem_coe.mp heQ)
    have hf := Finset.mem_filter.mp (Finset.mem_coe.mp hfQ)
    by_contra hef
    have hconflict :
        left f = left e ∨ right f = left e ∨
        left f = right e ∨ right f = right e := by
      rcases he.2.1 with heInc | heInc <;>
        rcases hf.2.1 with hfInc | hfInc
      · apply Or.inl
        apply Prod.ext
        · exact hfInc.trans heInc.symm
        · simpa [left, hfInc, heInc] using hcopies.symm
      · apply Or.inr; apply Or.inl
        apply Prod.ext
        · exact hfInc.trans heInc.symm
        · simpa [right, left, hfInc, heInc] using hcopies.symm
      · apply Or.inr; apply Or.inr; apply Or.inl
        apply Prod.ext
        · exact hfInc.trans heInc.symm
        · simpa [left, right, hfInc, heInc] using hcopies.symm
      · apply Or.inr; apply Or.inr; apply Or.inr
        apply Prod.ext
        · exact hfInc.trans heInc.symm
        · simpa [right, hfInc, heInc] using hcopies.symm
    have hneColor := hproper e he.1 f hf.1 hef hconflict
    exact hneColor (he.2.2.trans hf.2.2.symm)
  have hQcard : Q.card ≤ 2 := by
    have himage : Q.card = (Q.image (copyAt v)).card := by
      exact (Finset.card_image_iff.mpr hcopyInj).symm
    rw [himage]
    simpa using Finset.card_le_card
      (Finset.subset_univ (Q.image (copyAt v)))
  have hQAcard : QA.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro e he f hf
    apply hcopyInj
    · apply Finset.mem_coe.mpr
      rw [hQsplit]
      exact Finset.mem_union_left _ he
    · apply Finset.mem_coe.mpr
      rw [hQsplit]
      exact Finset.mem_union_left _ hf
    · apply Fin.ext
      have he' := Finset.mem_filter.mp he
      have hf' := Finset.mem_filter.mp hf
      have heNB : e ∉ B := fun heB ↦
        Finset.disjoint_left.mp hdisj he'.1 heB
      have hfNB : f ∉ B := fun hfB ↦
        Finset.disjoint_left.mp hdisj hf'.1 hfB
      have heNFB : e ∉ B.filter (G.Inc v) := by simp [heNB]
      have hfNFB : f ∉ B.filter (G.Inc v) := by simp [hfNB]
      exact (hcopyOutside v e heNFB).trans
        (hcopyOutside v f hfNFB).symm
  have hcards : Q.card = QA.card + QB.card := by
    rw [hQsplit, Finset.card_union_of_disjoint hQdisj]
  have hloadA :
      G.colorLoadOn A color v i ≤ (QA.card : ℝ) * ((3 : ℝ) / 5) := by
    rw [colorLoadOn, ← Finset.sum_filter]
    change (∑ e ∈ QA, G.weight e) ≤ _
    calc
      (∑ e ∈ QA, G.weight e) ≤ ∑ _e ∈ QA, ((3 : ℝ) / 5) := by
        exact Finset.sum_le_sum fun e he ↦
          hAweight e (Finset.mem_filter.mp he).1
      _ = (QA.card : ℝ) * ((3 : ℝ) / 5) := by simp
  have hloadB :
      G.colorLoadOn B color v i ≤ (QB.card : ℝ) * ((2 : ℝ) / 5) := by
    rw [colorLoadOn, ← Finset.sum_filter]
    change (∑ e ∈ QB, G.weight e) ≤ _
    calc
      (∑ e ∈ QB, G.weight e) ≤ ∑ _e ∈ QB, ((2 : ℝ) / 5) := by
        exact Finset.sum_le_sum fun e he ↦
          hBweight e (Finset.mem_filter.mp he).1
      _ = (QB.card : ℝ) * ((2 : ℝ) / 5) := by simp
  have hloadSplit :
      G.colorLoadOn (A ∪ B) color v i =
        G.colorLoadOn A color v i + G.colorLoadOn B color v i := by
    unfold colorLoadOn
    rw [Finset.sum_union hdisj]
  rw [hloadSplit]
  calc
    G.colorLoadOn A color v i + G.colorLoadOn B color v i ≤
        (QA.card : ℝ) * ((3 : ℝ) / 5) +
          (QB.card : ℝ) * ((2 : ℝ) / 5) :=
      add_le_add hloadA hloadB
    _ ≤ 1 := by
      have hQtwo : QA.card + QB.card ≤ 2 := hcards ▸ hQcard
      have hAcases : QA.card = 0 ∨ QA.card = 1 := by omega
      rcases hAcases with hAc | hAc
      · have hBtwo : QB.card ≤ 2 := by omega
        have hBtwoReal : (QB.card : ℝ) ≤ 2 := by exact_mod_cast hBtwo
        rw [hAc]
        norm_num
        linarith
      · have hBone : QB.card ≤ 1 := by omega
        have hBoneReal : (QB.card : ℝ) ≤ 1 := by exact_mod_cast hBone
        rw [hAc]
        norm_num
        linarith

/-- A named-set version of `exists_feasibleOn_union_three_half_of_degree`. -/
theorem exists_feasibleOn_selected_three_half_of_degree
    (J A B : Finset G.E) (hsplit : J = A ∪ B) (hdisj : Disjoint A B)
    (K : ℕ) (hK : 0 < K)
    (hAweight : ∀ e ∈ A, G.weight e ≤ (3 : ℝ) / 5)
    (hBweight : ∀ e ∈ B, G.weight e ≤ (2 : ℝ) / 5)
    (hAdegree : ∀ v, G.degreeOn A v ≤ K)
    (htotalDegree : ∀ v, G.degreeOn A v + G.degreeOn B v ≤ 2 * K) :
    ∃ color : G.E → Fin (3 * ((K + 1) / 2)),
      G.IsFeasibleOn J color := by
  rw [hsplit]
  exact exists_feasibleOn_union_three_half_of_degree A B hdisj K hK
    hAweight hBweight hAdegree htotalDegree

end WeightedMultigraph
end WeightedEdgeColoring
