import WeightedEdgeColoring.SubtwoPhysicalPatternSlots

/-!
# Restoring physical edges from integral pattern capacities

Pick the physical objects that fit, assign each to a distinct slot of its
type, and bound the unfilled objects of every type. Color capacities are
checked at the original vertices. Nothing in this finite step assumes a
bound on the number of blocks or vertices.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo
noncomputable section
universe u v

variable {E : Type u} {I : Type v} [Fintype E] [DecidableEq E]
  [Fintype I] [DecidableEq I]

/-- Keep exactly as many objects of each type as its slot budget permits. -/
theorem exists_typeTrim (F : Finset E) (typeOf : E → I) (capacity : I → ℕ) :
    ∃ P ⊆ F, ∀ i,
      (P.filter fun e => typeOf e = i).card =
        min (F.filter fun e => typeOf e = i).card (capacity i) ∧
      ((F \ P).filter fun e => typeOf e = i).card =
        (F.filter fun e => typeOf e = i).card - capacity i := by
  classical
  have hselect : ∀ i, ∃ S : Finset E,
      S ⊆ F.filter (fun e => typeOf e = i) ∧
      S.card = min (F.filter fun e => typeOf e = i).card (capacity i) := by
    intro i
    exact Finset.exists_subset_card_eq (Nat.min_le_left _ _)
  choose S hsub hcard using hselect
  let P : Finset E := Finset.univ.biUnion S
  have hPF : P ⊆ F := by
    intro e he
    obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp (hsub i hei)).1
  have hfiber (i : I) : P.filter (fun e => typeOf e = i) = S i := by
    ext e
    constructor
    · intro he
      obtain ⟨heP, hei⟩ := Finset.mem_filter.mp he
      obtain ⟨j, _, hej⟩ := Finset.mem_biUnion.mp heP
      have hejtype := (Finset.mem_filter.mp (hsub j hej)).2
      have hji : j = i := hejtype.symm.trans hei
      simpa [hji] using hej
    · intro he
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, he⟩,
          (Finset.mem_filter.mp (hsub i he)).2⟩
  refine ⟨P, hPF, fun i => ⟨by rw [hfiber, hcard], ?_⟩⟩
  have hrem : (F \ P).filter (fun e => typeOf e = i) =
      (F.filter fun e => typeOf e = i) \ S i := by
    rw [← hfiber]
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [hrem, Finset.card_sdiff, Finset.inter_eq_left.mpr (hsub i), hcard]
  omega

/-- Every assigned physical object consumes a positive slot of its type. -/
theorem positive_slot_of_colored
    (F : Finset E) (typeOf : E → I) {q : ℕ} (color : E → Fin q)
    (slots : Fin q → I → ℕ)
    (hcount : ∀ c i,
      (F.filter fun e => typeOf e = i ∧ color e = c).card ≤ slots c i)
    {e : E} (he : e ∈ F) : 0 < slots (color e) (typeOf e) := by
  have hpos : 0 < (F.filter fun f => typeOf f = typeOf e ∧ color f = color e).card :=
    Finset.card_pos.mpr ⟨e, by simp [he]⟩
  exact hpos.trans_le (hcount _ _)

/-- A bounded shortage of integer pattern slots gives a partial coloring
of actual edges with the same bounded shortage in each physical type. -/
theorem exists_partialColoring_of_type_slots
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} (F : Finset G.E)
    (typeOf : G.E → I) (q : ℕ) (hq : 0 < q)
    (typeInc : G.V → I → Prop) [DecidableRel typeInc]
    (typeWeight : I → ℝ) (hweight0 : ∀ i, 0 ≤ typeWeight i)
    (slots : Fin q → I → ℕ) (error : I → ℕ)
    (hinc : ∀ e ∈ F, ∀ v, G.Inc v e → typeInc v (typeOf e))
    (hweight : ∀ e ∈ F, G.weight e ≤ typeWeight (typeOf e))
    (hslots : ∀ i,
      (F.filter fun e => typeOf e = i).card ≤ (∑ c, slots c i) + error i)
    (hcapacity : ∀ v c,
      (∑ i, if typeInc v i then (slots c i : ℝ) * typeWeight i else 0) ≤ 1) :
    ∃ P ⊆ F, ∃ color : G.E → Fin q,
      G.IsFeasibleOn P color ∧
      (∀ c i, (P.filter fun e => typeOf e = i ∧ color e = c).card ≤ slots c i) ∧
      (∀ i, ((F \ P).filter fun e => typeOf e = i).card ≤ error i) := by
  obtain ⟨P, hPF, hP⟩ := exists_typeTrim F typeOf (fun i => ∑ c, slots c i)
  obtain ⟨color, hfeasible, hcount⟩ := exists_feasibleOn_of_type_slots P typeOf q hq
    typeInc typeWeight hweight0 slots (fun e he => hinc e (hPF he))
    (fun e he => hweight e (hPF he))
    (fun i => (hP i).1.le.trans (Nat.min_le_right _ _)) hcapacity
  refine ⟨P, hPF, color, hfeasible, hcount, ?_⟩
  intro i
  rw [(hP i).2]
  have hi := hslots i
  omega

/-- Turn per-type leftover counts into a weighted error at an original
vertex. This is a local bound, independent of the number of other blocks. -/
theorem residualStarWeight_le_type_error
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} (F P : Finset G.E)
    (typeOf : G.E → I) (typeInc : G.V → I → Prop) [DecidableRel typeInc]
    (typeWeight : I → ℝ) (hweight0 : ∀ i, 0 ≤ typeWeight i)
    (error : I → ℕ)
    (hinc : ∀ e ∈ F, ∀ v, G.Inc v e → typeInc v (typeOf e))
    (hweight : ∀ e ∈ F, G.weight e ≤ typeWeight (typeOf e))
    (herror : ∀ i, ((F \ P).filter fun e => typeOf e = i).card ≤ error i)
    (v : G.V) :
    (∑ e ∈ F \ P, if G.Inc v e then G.weight e else 0) ≤
      ∑ i, if typeInc v i then (error i : ℝ) * typeWeight i else 0 := by
  classical
  rw [← Finset.sum_fiberwise (F \ P) typeOf]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : typeInc v i
  · rw [if_pos hi]
    calc
      (∑ e ∈ F \ P with typeOf e = i,
          if G.Inc v e then G.weight e else 0) ≤
          ∑ _e ∈ (F \ P).filter (fun e => typeOf e = i), typeWeight i := by
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨heFP, hei⟩ := Finset.mem_filter.mp he
        have heF := (Finset.mem_sdiff.mp heFP).1
        by_cases hv : G.Inc v e
        · simpa [hv, hei] using hweight e heF
        · simp [hv, hweight0]
      _ = (((F \ P).filter fun e => typeOf e = i).card : ℝ) * typeWeight i := by simp
      _ ≤ (error i : ℝ) * typeWeight i :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast herror i) (hweight0 i)
  · rw [if_neg hi]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro e he
    obtain ⟨heFP, hei⟩ := Finset.mem_filter.mp he
    have heF := (Finset.mem_sdiff.mp heFP).1
    have hv : ¬ G.Inc v e := fun h => hi (hei ▸ hinc e heF v h)
    simp [hv]

end
end WeightedEdgeColoring.Subtwo
