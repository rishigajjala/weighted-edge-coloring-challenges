import WeightedEdgeColoring.SubtwoLabelRounding

/-!
# Physical edges in rounded pattern slots

An integer pattern menu can be filled by distinct physical edges of each
specified type. The type-wise count bounds imply the real vertex-load
bounds. This is the finite restoration step; it does not assert the global
asymptotic theorem.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo

noncomputable section
universe u v

variable {E : Type u} {I : Type v} [Fintype E] [DecidableEq E]
  [Fintype I] [DecidableEq I]

/-- Fill any integral type demand that fits in the available color slots.
The resulting physical color names respect every color/type capacity. -/
theorem exists_color_of_type_slots
    (F : Finset E) (typeOf : E → I) (q : ℕ) (hq : 0 < q)
    (slots : Fin q → I → ℕ)
    (hslots : ∀ i, (F.filter fun e => typeOf e = i).card ≤ ∑ c, slots c i) :
    ∃ color : E → Fin q, ∀ c i,
      (F.filter fun e => typeOf e = i ∧ color e = c).card ≤ slots c i := by
  classical
  let Fiber (i : I) := {e : E // e ∈ F ∧ typeOf e = i}
  let Slots (i : I) := Σ c : Fin q, Fin (slots c i)
  have hemb : ∀ i, Nonempty (Fiber i ↪ Slots i) := by
    intro i
    apply Function.Embedding.nonempty_of_card_le
    have hfcard : Fintype.card (Fiber i) = (F.filter fun e => typeOf e = i).card := by
      rw [show Fintype.card (Fiber i) =
        (Finset.univ.filter fun e => e ∈ F ∧ typeOf e = i).card from
        Fintype.card_subtype _]
      congr 1
      ext e
      simp
    rw [hfcard]
    simpa [Slots, Fintype.card_sigma] using hslots i
  let assign : ∀ i, Fiber i ↪ Slots i := fun i => Classical.choice (hemb i)
  let color : E → Fin q := fun e =>
    if he : e ∈ F then (assign (typeOf e) ⟨e, he, rfl⟩).1 else ⟨0, hq⟩
  refine ⟨color, ?_⟩
  intro c i
  have hcolor (e : Fiber i) : color e.val = (assign i e).1 := by
    rcases e with ⟨e, he, hi⟩
    subst i
    simp [color, he]
  have hsum :
      (∑ e : Fiber i, if (assign i e).1 = c then (1 : ℕ) else 0) ≤ slots c i := by
    calc
      (∑ e : Fiber i, if (assign i e).1 = c then (1 : ℕ) else 0) =
          ∑ z ∈ Finset.univ.image (assign i), if z.1 = c then 1 else 0 :=
        (Finset.sum_image (s := Finset.univ)
          (f := fun z : Slots i => if z.1 = c then (1 : ℕ) else 0)
          (assign i).injective.injOn).symm
      _ ≤ ∑ z : Slots i, if z.1 = c then 1 else 0 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
      _ = slots c i := by
        change (∑ z : (Σ d : Fin q, Fin (slots d i)), if z.1 = c then (1 : ℕ) else 0) = _
        rw [Fintype.sum_sigma, Finset.sum_eq_single c]
        · simp
        · intro d _ hdc
          simp [hdc]
        · simp
  have heq :
      (F.filter fun e => typeOf e = i ∧ color e = c).card =
        ∑ e : Fiber i, if (assign i e).1 = c then (1 : ℕ) else 0 := by
    calc
      _ = ∑ e ∈ F.filter (fun e => typeOf e = i),
          if color e = c then (1 : ℕ) else 0 := by
        rw [← Finset.sum_filter]
        simp only [Finset.filter_filter, Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ e : Fiber i, if color e.val = c then (1 : ℕ) else 0 := by
        exact Finset.sum_subtype (p := fun e => e ∈ F ∧ typeOf e = i)
          (F.filter fun e => typeOf e = i) (fun e => by simp)
          (fun e => if color e = c then (1 : ℕ) else 0)
      _ = _ := by simp_rw [hcolor]
  rw [heq]
  exact hsum

/-- A physical type keeps its endpoint incidence and upper weight. Hence
integer color/type capacities give the actual weighted color capacity. -/
theorem feasibleOn_of_type_slot_counts
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} (F : Finset G.E)
    {q : ℕ} (color : G.E → Fin q) (typeOf : G.E → I)
    (typeInc : G.V → I → Prop) [DecidableRel typeInc]
    (typeWeight : I → ℝ) (hweight0 : ∀ i, 0 ≤ typeWeight i)
    (slots : Fin q → I → ℕ)
    (hinc : ∀ e ∈ F, ∀ v, G.Inc v e → typeInc v (typeOf e))
    (hweight : ∀ e ∈ F, G.weight e ≤ typeWeight (typeOf e))
    (hcount : ∀ c i,
      (F.filter fun e => typeOf e = i ∧ color e = c).card ≤ slots c i)
    (hcapacity : ∀ v c,
      (∑ i, if typeInc v i then (slots c i : ℝ) * typeWeight i else 0) ≤ 1) :
    G.IsFeasibleOn F color := by
  classical
  intro v c
  unfold WeightedEdgeColoring.WeightedMultigraph.colorLoadOn
  rw [← Finset.sum_fiberwise F typeOf]
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) (hcapacity v c)
  by_cases hi : typeInc v i
  · rw [if_pos hi]
    calc
      (∑ e ∈ F with typeOf e = i,
        if G.Inc v e ∧ color e = c then G.weight e else 0) ≤
          ∑ e ∈ F with typeOf e = i, if color e = c then typeWeight i else 0 := by
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨heF, hei⟩ := Finset.mem_filter.mp he
        by_cases hc : color e = c
        · by_cases hv : G.Inc v e
          · simpa [hc, hv, hei] using hweight e heF
          · simp [hc, hv, hweight0]
        · simp [hc]
      _ = ((F.filter fun e => typeOf e = i ∧ color e = c).card : ℝ) *
          typeWeight i := by
        rw [← Finset.sum_filter]
        simp [Finset.filter_filter, and_assoc]
      _ ≤ (slots c i : ℝ) * typeWeight i := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount c i) (hweight0 i)
  · rw [if_neg hi]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro e he
    obtain ⟨heF, hei⟩ := Finset.mem_filter.mp he
    have hv : ¬ G.Inc v e := fun h => hi (hei ▸ hinc e heF v h)
    simp [hv]

/-- Integer pattern capacities produce a coloring of the physical selected
edges, without a separate assignment assumption. -/
theorem exists_feasibleOn_of_type_slots
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} (F : Finset G.E)
    (typeOf : G.E → I) (q : ℕ) (hq : 0 < q)
    (typeInc : G.V → I → Prop) [DecidableRel typeInc]
    (typeWeight : I → ℝ) (hweight0 : ∀ i, 0 ≤ typeWeight i)
    (slots : Fin q → I → ℕ)
    (hinc : ∀ e ∈ F, ∀ v, G.Inc v e → typeInc v (typeOf e))
    (hweight : ∀ e ∈ F, G.weight e ≤ typeWeight (typeOf e))
    (hslots : ∀ i, (F.filter fun e => typeOf e = i).card ≤ ∑ c, slots c i)
    (hcapacity : ∀ v c,
      (∑ i, if typeInc v i then (slots c i : ℝ) * typeWeight i else 0) ≤ 1) :
    ∃ color : G.E → Fin q, G.IsFeasibleOn F color ∧
      ∀ c i, (F.filter fun e => typeOf e = i ∧ color e = c).card ≤ slots c i := by
  obtain ⟨color, hc⟩ := exists_color_of_type_slots F typeOf q hq slots hslots
  exact ⟨color, feasibleOn_of_type_slot_counts F color typeOf typeInc
    typeWeight hweight0 slots hinc hweight hc hcapacity, hc⟩

end
end WeightedEdgeColoring.Subtwo
