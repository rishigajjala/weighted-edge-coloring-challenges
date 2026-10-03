import WeightedEdgeColoring.OrdinarySlotOptions
import WeightedEdgeColoring.QuantizedMatchingProjection
import WeightedEdgeColoring.WeightedInsertion

/-!
# Extracting a weighted multigraph partial coloring from ordinary slot options

This is the indexed-edge version of `OrdinaryMatchingExtraction`.  Parallel
edges remain distinct jobs; the argument only uses looplessness and the
partial-matching disjointness of concrete endpoint places.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Edges represented by a finite set of ordinary options. -/
def ordinarySelectedEdges {q K : ℕ}
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K)) : Finset G.E :=
  M.image OrdinarySlotChoice.job

@[simp] theorem mem_ordinarySelectedEdges_iff {q K : ℕ}
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K)) (e : G.E) :
    e ∈ G.ordinarySelectedEdges M ↔ ∃ o ∈ M, o.job = e := by
  simp [ordinarySelectedEdges]

/-- In a partial matching, a selected edge has a unique ordinary option. -/
theorem existsUnique_ordinaryOption_of_mem
    {q K : ℕ} {M : Finset (OrdinarySlotChoice G.E (Fin q) K)}
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    {e : G.E} (he : e ∈ G.ordinarySelectedEdges M) :
    ∃! o, o ∈ M ∧ o.job = e := by
  rcases (G.mem_ordinarySelectedEdges_iff M e).mp he with ⟨o, hoM, rfl⟩
  refine ⟨o, ⟨hoM, rfl⟩, ?_⟩
  intro p hp
  exact hM.2 hp.1 hoM hp.2

/-- The unique ordinary option selected for one selected edge. -/
def selectedOrdinaryOption {q K : ℕ}
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (e : G.E) (he : e ∈ G.ordinarySelectedEdges M) :
    OrdinarySlotChoice G.E (Fin q) K :=
  Finset.choose (fun o ↦ o.job = e) M
    (G.existsUnique_ordinaryOption_of_mem hM he)

theorem selectedOrdinaryOption_mem {q K : ℕ}
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (e : G.E) (he : e ∈ G.ordinarySelectedEdges M) :
    G.selectedOrdinaryOption M hM e he ∈ M := by
  exact Finset.choose_mem _ _ (G.existsUnique_ordinaryOption_of_mem hM he)

@[simp] theorem selectedOrdinaryOption_job {q K : ℕ}
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (e : G.E) (he : e ∈ G.ordinarySelectedEdges M) :
    (G.selectedOrdinaryOption M hM e he).job = e := by
  exact (Finset.choose_spec _ _
    (G.existsUnique_ordinaryOption_of_mem hM he)).2

/-- The color carried by the unique selected option. -/
def selectedOrdinaryColor {q K : ℕ}
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (e : {e // e ∈ G.ordinarySelectedEdges M}) : Fin q :=
  (G.selectedOrdinaryOption M hM e.1 e.2).color

/-- The concrete place used by a selected edge at an incident vertex. -/
def selectedOrdinaryPlaceAt {q K : ℕ}
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (v : G.V) (e : {e // e ∈ G.ordinarySelectedEdges M}) : Fin K :=
  if G.fst e.1 = v then
    (G.selectedOrdinaryOption M hM e.1 e.2).leftPlace
  else
    (G.selectedOrdinaryOption M hM e.1 e.2).rightPlace

/-- Distinct selected incident edges of one color use distinct places. -/
theorem selectedOrdinaryPlaceAt_injective_on
    {q K : ℕ} {M : Finset (OrdinarySlotChoice G.E (Fin q) K)}
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (v : G.V) (c : Fin q) :
    Set.InjOn (G.selectedOrdinaryPlaceAt M hM v)
      {e | G.Inc v e.1 ∧ G.selectedOrdinaryColor M hM e = c} := by
  intro e he f hf hplace
  apply Subtype.ext
  by_contra hef
  let oe := G.selectedOrdinaryOption M hM e.1 e.2
  let of := G.selectedOrdinaryOption M hM f.1 f.2
  have hoeM : oe ∈ M := G.selectedOrdinaryOption_mem M hM e.1 e.2
  have hofM : of ∈ M := G.selectedOrdinaryOption_mem M hM f.1 f.2
  have hoene : oe ≠ of := by
    intro hop
    apply hef
    have hjob := congrArg OrdinarySlotChoice.job hop
    simpa [oe, of] using hjob
  have hcompat :
      Disjoint
        ((OrdinarySlotChoice.system G.fst G.snd K).slots oe)
        ((OrdinarySlotChoice.system G.fst G.snd K).slots of) :=
    hM.1 hoeM hofM hoene
  let s : OrdinarySlot G.V (Fin q) K :=
    ⟨v, c, G.selectedOrdinaryPlaceAt M hM v e⟩
  have hse : s ∈ (OrdinarySlotChoice.system G.fst G.snd K).slots oe := by
    rcases he.1 with hev | hev
    · simp [s, oe, selectedOrdinaryPlaceAt, hev, selectedOrdinaryColor,
        OrdinarySlotChoice.system, OrdinarySlotChoice.leftSlot, he.2.symm]
    · have hne : G.fst e.1 ≠ v := by
        intro h
        exact G.noLoop e.1 (h.trans hev.symm)
      simp [s, oe, selectedOrdinaryPlaceAt, hne, hev,
        selectedOrdinaryColor, OrdinarySlotChoice.system,
        OrdinarySlotChoice.rightSlot, he.2.symm]
  have hsf : s ∈ (OrdinarySlotChoice.system G.fst G.snd K).slots of := by
    dsimp [s]
    rw [hplace]
    rcases hf.1 with hfv | hfv
    · simp [s, of, selectedOrdinaryPlaceAt, hfv, selectedOrdinaryColor,
        OrdinarySlotChoice.system, OrdinarySlotChoice.leftSlot, hf.2.symm]
    · have hne : G.fst f.1 ≠ v := by
        intro h
        exact G.noLoop f.1 (h.trans hfv.symm)
      simp [s, of, selectedOrdinaryPlaceAt, hne, hfv,
        selectedOrdinaryColor, OrdinarySlotChoice.system,
        OrdinarySlotChoice.rightSlot, hf.2.symm]
  exact (Finset.disjoint_left.mp hcompat hse hsf).elim

/-- Safe places imply the selected-edge load bound. -/
theorem selectedOrdinaryColor_load_le
    {q K : ℕ} {M : Finset (OrdinarySlotChoice G.E (Fin q) K)}
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (slotSize : G.V → Fin q → Fin K → ℝ)
    (hslot0 : ∀ v c i, 0 ≤ slotSize v c i)
    (hsafe : ∀ v c, (∑ i, slotSize v c i) ≤ 1)
    (hleft : ∀ o ∈ M,
      G.weight o.job ≤ slotSize (G.fst o.job) o.color o.leftPlace)
    (hright : ∀ o ∈ M,
      G.weight o.job ≤ slotSize (G.snd o.job) o.color o.rightPlace) :
    ∀ v c,
      (∑ e : {e // e ∈ G.ordinarySelectedEdges M},
        if G.Inc v e.1 ∧ G.selectedOrdinaryColor M hM e = c then
          G.weight e.1 else 0) ≤ 1 := by
  intro v c
  let T : Finset {e // e ∈ G.ordinarySelectedEdges M} :=
    Finset.univ.filter fun e ↦
      G.Inc v e.1 ∧ G.selectedOrdinaryColor M hM e = c
  have hfit : ∀ e ∈ T,
      G.weight e.1 ≤
        slotSize v c (G.selectedOrdinaryPlaceAt M hM v e) := by
    intro e heT
    have heData : G.Inc v e.1 ∧
        G.selectedOrdinaryColor M hM e = c := by
      simpa [T] using (Finset.mem_filter.mp heT).2
    let oe := G.selectedOrdinaryOption M hM e.1 e.2
    have hoeM : oe ∈ M := G.selectedOrdinaryOption_mem M hM e.1 e.2
    have hcolor : oe.color = c := by
      simpa [oe, selectedOrdinaryColor] using heData.2
    rcases heData.1 with hev | hev
    · simpa [oe, selectedOrdinaryPlaceAt, hev, hcolor] using hleft oe hoeM
    · have hne : G.fst e.1 ≠ v := by
        intro h
        exact G.noLoop e.1 (h.trans hev.symm)
      simpa [oe, selectedOrdinaryPlaceAt, hne, hev, hcolor] using
        hright oe hoeM
  have hinj : Set.InjOn (G.selectedOrdinaryPlaceAt M hM v) (T : Set _) := by
    intro e he f hf
    apply G.selectedOrdinaryPlaceAt_injective_on hM v c
    · simpa [T] using (Finset.mem_filter.mp he).2
    · simpa [T] using (Finset.mem_filter.mp hf).2
  calc
    (∑ e : {e // e ∈ G.ordinarySelectedEdges M},
        if G.Inc v e.1 ∧ G.selectedOrdinaryColor M hM e = c then
          G.weight e.1 else 0) = ∑ e ∈ T, G.weight e.1 := by
      rw [Finset.sum_filter]
    _ ≤ ∑ e ∈ T,
        slotSize v c (G.selectedOrdinaryPlaceAt M hM v e) :=
      Finset.sum_le_sum hfit
    _ = ∑ i ∈ T.image (G.selectedOrdinaryPlaceAt M hM v),
        slotSize v c i := by
      symm
      exact Finset.sum_image hinj
    _ ≤ ∑ i : Fin K, slotSize v c i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ ↦ hslot0 v c i)
    _ ≤ 1 := hsafe v c

/-- Extend the selected-edge coloring arbitrarily to all graph edges. -/
def extendSelectedOrdinaryColor {q K : ℕ} (hq : 0 < q)
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (e : G.E) : Fin q :=
  if he : e ∈ G.ordinarySelectedEdges M then
    G.selectedOrdinaryColor M hM ⟨e, he⟩
  else ⟨0, hq⟩

@[simp] theorem extendSelectedOrdinaryColor_of_mem
    {q K : ℕ} (hq : 0 < q)
    (M : Finset (OrdinarySlotChoice G.E (Fin q) K))
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    {e : G.E} (he : e ∈ G.ordinarySelectedEdges M) :
    G.extendSelectedOrdinaryColor hq M hM e =
      G.selectedOrdinaryColor M hM ⟨e, he⟩ := by
  simp [extendSelectedOrdinaryColor, he]

/-- Pack-safe ordinary slots give a feasible multigraph partial coloring. -/
theorem ordinaryMatching_isFeasibleOn
    {q K : ℕ} (hq : 0 < q)
    {M : Finset (OrdinarySlotChoice G.E (Fin q) K)}
    (hM : (OrdinarySlotChoice.system G.fst G.snd K).IsPartialMatching M)
    (slotSize : G.V → Fin q → Fin K → ℝ)
    (hslot0 : ∀ v c i, 0 ≤ slotSize v c i)
    (hsafe : ∀ v c, (∑ i, slotSize v c i) ≤ 1)
    (hleft : ∀ o ∈ M,
      G.weight o.job ≤ slotSize (G.fst o.job) o.color o.leftPlace)
    (hright : ∀ o ∈ M,
      G.weight o.job ≤ slotSize (G.snd o.job) o.color o.rightPlace) :
    G.IsFeasibleOn (G.ordinarySelectedEdges M)
      (G.extendSelectedOrdinaryColor hq M hM) := by
  intro v c
  have hload := G.selectedOrdinaryColor_load_le hM slotSize hslot0 hsafe
    hleft hright v c
  calc
    G.colorLoadOn (G.ordinarySelectedEdges M)
        (G.extendSelectedOrdinaryColor hq M hM) v c =
      ∑ e : {e // e ∈ G.ordinarySelectedEdges M},
        if G.Inc v e.1 ∧ G.selectedOrdinaryColor M hM e = c then
          G.weight e.1 else 0 := by
      unfold WeightedMultigraph.colorLoadOn
      rw [show
        (∑ e ∈ G.ordinarySelectedEdges M,
          if G.Inc v e ∧
              G.extendSelectedOrdinaryColor hq M hM e = c then
            G.weight e else 0) =
          ∑ e : {e // e ∈ G.ordinarySelectedEdges M},
            if G.Inc v e.1 ∧
                G.extendSelectedOrdinaryColor hq M hM e.1 = c then
              G.weight e.1 else 0 by
        exact Finset.sum_subtype
          (p := fun e : G.E ↦ e ∈ G.ordinarySelectedEdges M)
          (G.ordinarySelectedEdges M) (by intro e; simp) _]
      apply Finset.sum_congr rfl
      intro e _he
      simp [G.extendSelectedOrdinaryColor_of_mem hq M hM e.2]
    _ ≤ 1 := hload

end WeightedMultigraph

end

end WeightedEdgeColoring
