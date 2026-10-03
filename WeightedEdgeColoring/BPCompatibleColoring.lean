import WeightedEdgeColoring.BipartitePackets

/-!
# A compatible-copy coloring lemma

This file records the elementary bipartite coloring step used by the
bin-packing arguments.  Heavy edges must be alone among the heavy edges of
their color at either endpoint.  A color may contain at most `r` edges in
total at an endpoint.  The two local degree inequalities are exactly the
available-copy inequalities.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

/-- Slots available for light edges at one vertex.  Copy zero has the space
left after the heavy edges; every other copy has `L` slots. -/
abbrev CompatibleCopySlot (r L d : ℕ) :=
  Fin (L - d) ⊕ (Fin (r - 1) × Fin L)

theorem card_compatibleCopySlot
    {r L d : ℕ} (hr : 1 ≤ r) (hd : d ≤ L) :
    Fintype.card (CompatibleCopySlot r L d) = r * L - d := by
  simp only [CompatibleCopySlot, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_prod]
  rw [Nat.sub_mul]
  simp only [one_mul]
  have hL : L ≤ r * L := by
    simpa [one_mul] using Nat.mul_le_mul_right L hr
  omega

/-- A finite set of at most `rL-d` objects can be put into `r` copies so
that copy zero has at most `L-d` objects and every other copy has at most
`L` objects. -/
theorem exists_compatibleCopyAssignment
    {α : Type*} [DecidableEq α] (A : Finset α)
    (r L d : ℕ) (hr : 2 ≤ r) (hd : d ≤ L)
    (hcard : A.card ≤ r * L - d) :
    ∃ copy : α → Fin r,
      (∀ a ∉ A, (copy a).1 = 0) ∧
      (A.filter fun a ↦ (copy a).1 = 0).card ≤ L - d ∧
      ∀ k : Fin r, k.1 ≠ 0 →
        (A.filter fun a ↦ copy a = k).card ≤ L := by
  classical
  let C := r * L - d
  let slotEquiv : Fin C ≃ CompatibleCopySlot r L d :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_fin]
      exact (card_compatibleCopySlot (by omega) hd).symm)
  let slot : {a // a ∈ A} → CompatibleCopySlot r L d := fun a ↦
    slotEquiv (Fin.castLE hcard (A.equivFin a))
  have hslot : Function.Injective slot := by
    exact slotEquiv.injective.comp
      ((Fin.castLE_injective hcard).comp A.equivFin.injective)
  let copy : α → Fin r := fun a ↦
    if ha : a ∈ A then
      match slot ⟨a, ha⟩ with
      | Sum.inl _ => ⟨0, by omega⟩
      | Sum.inr p => ⟨p.1.1 + 1, by omega⟩
    else
      ⟨0, by omega⟩
  refine ⟨copy, ?_, ?_, ?_⟩
  · intro a ha
    simp [copy, ha]
  · let Z := A.filter fun a ↦ (copy a).1 = 0
    let leftEmbedding : Fin (L - d) ↪ CompatibleCopySlot r L d :=
      ⟨Sum.inl, Sum.inl_injective⟩
    let leftSlots : Finset (CompatibleCopySlot r L d) :=
      Finset.univ.map leftEmbedding
    let zslot : {a // a ∈ Z} → CompatibleCopySlot r L d := fun a ↦
      slot ⟨a.1, (Finset.mem_filter.mp a.2).1⟩
    have hzmem : ∀ a, zslot a ∈ leftSlots := by
      intro a
      have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
      have hacopy : (copy a.1).1 = 0 := (Finset.mem_filter.mp a.2).2
      cases hs : slot ⟨a.1, haA⟩ with
      | inl z =>
          exact Finset.mem_map.mpr ⟨z, Finset.mem_univ _, by
            simp only [leftEmbedding, zslot]
            exact hs.symm⟩
      | inr p =>
          have : (p.1.1 + 1 : ℕ) = 0 := by
            simpa [copy, haA, hs] using hacopy
          omega
    let intoLeft : {a // a ∈ Z} → {s // s ∈ leftSlots} := fun a ↦
      ⟨zslot a, hzmem a⟩
    have hinj : Function.Injective intoLeft := by
      intro a b hab
      apply Subtype.ext
      have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
      have hbA : b.1 ∈ A := (Finset.mem_filter.mp b.2).1
      have hsEq : slot ⟨a.1, haA⟩ = slot ⟨b.1, hbA⟩ := by
        exact congrArg Subtype.val hab
      exact congrArg (fun x : {a // a ∈ A} ↦ x.1) (hslot hsEq)
    have h := Fintype.card_le_of_injective intoLeft hinj
    have hleftCard : leftSlots.card = L - d := by
      simp [leftSlots, leftEmbedding]
    rw [Fintype.card_coe, Fintype.card_coe, hleftCard] at h
    simpa [Z] using h
  · intro k hk
    let K := A.filter fun a ↦ copy a = k
    let ki : Fin (r - 1) := ⟨k.1 - 1, by omega⟩
    let rightEmbedding : Fin L ↪ CompatibleCopySlot r L d :=
      ⟨fun j ↦ Sum.inr (ki, j), by
        intro x y h
        simpa using h⟩
    let rightSlots : Finset (CompatibleCopySlot r L d) :=
      Finset.univ.map rightEmbedding
    let kslot : {a // a ∈ K} → CompatibleCopySlot r L d := fun a ↦
      slot ⟨a.1, (Finset.mem_filter.mp a.2).1⟩
    have hkmem : ∀ a, kslot a ∈ rightSlots := by
      intro a
      have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
      have hacopy : copy a.1 = k := (Finset.mem_filter.mp a.2).2
      cases hs : slot ⟨a.1, haA⟩ with
      | inl z =>
          have hk0 : k.1 = 0 := by
            simpa [copy, haA, hs] using congrArg Fin.val hacopy.symm
          exact (hk hk0).elim
      | inr p =>
          have hp : p.1 = ki := by
            apply Fin.ext
            have hv := congrArg Fin.val hacopy
            simp only [copy, haA, hs, dite_true] at hv
            simp only [ki]
            omega
          exact Finset.mem_map.mpr ⟨p.2, Finset.mem_univ _, by
            change Sum.inr (ki, p.2) = slot ⟨a.1, haA⟩
            have hpair : (ki, p.2) = p := Prod.ext hp.symm rfl
            rw [hpair]
            exact hs.symm⟩
    let intoRight : {a // a ∈ K} → {s // s ∈ rightSlots} := fun a ↦
      ⟨kslot a, hkmem a⟩
    have hinj : Function.Injective intoRight := by
      intro a b hab
      apply Subtype.ext
      have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
      have hbA : b.1 ∈ A := (Finset.mem_filter.mp b.2).1
      have hsEq : slot ⟨a.1, haA⟩ = slot ⟨b.1, hbA⟩ := by
        exact congrArg Subtype.val hab
      exact congrArg (fun x : {a // a ∈ A} ↦ x.1) (hslot hsEq)
    have h := Fintype.card_le_of_injective intoRight hinj
    have hrightCard : rightSlots.card = L := by
      simp [rightSlots, rightEmbedding]
    rw [Fintype.card_coe, Fintype.card_coe, hrightCard] at h
    simpa [K] using h

namespace WeightedMultigraph

universe u

variable {G : WeightedMultigraph.{u}}

/-- Compatible-copy lemma for a heavy/light split of a bipartite weighted
multigraph.  At each vertex the heavy edges fit in `L` distinguished slots,
and all selected edges fit in `rL` slots.  Splitting every vertex into `r`
copies reduces the statement to Kőnig's ordinary edge-coloring theorem.

The resulting color has at most `r` incident selected edges at a vertex and
at most one of them is heavy.  The two displayed weight inequalities then
give unit load. -/
theorem exists_feasibleOn_union_of_compatible_copies
    (bip : G.Bipartition) (H S : Finset G.E) (hdisj : Disjoint H S)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (heavyCap lightCap : ℝ) (hlight_nonneg : 0 ≤ lightCap)
    (hheavy : ∀ e ∈ H, G.weight e ≤ heavyCap)
    (hlight : ∀ e ∈ S, G.weight e ≤ lightCap)
    (hsmall : (r : ℝ) * lightCap ≤ 1)
    (hmixed : heavyCap + ((r - 1 : ℕ) : ℝ) * lightCap ≤ 1)
    (hheavyDegree : ∀ v, G.degreeOn H v ≤ L)
    (htotalDegree : ∀ v, G.degreeOn H v + G.degreeOn S v ≤ r * L) :
    ∃ color : G.E → Fin L, G.IsFeasibleOn (H ∪ S) color := by
  classical
  have hcopyExists : ∀ v : G.V,
      ∃ copy : G.E → Fin r,
        (∀ e ∉ S.filter (G.Inc v), (copy e).1 = 0) ∧
        ((S.filter (G.Inc v)).filter fun e ↦ (copy e).1 = 0).card ≤
          L - G.degreeOn H v ∧
        ∀ k : Fin r, k.1 ≠ 0 →
          ((S.filter (G.Inc v)).filter fun e ↦ copy e = k).card ≤ L := by
    intro v
    apply exists_compatibleCopyAssignment
    · exact hr
    · exact hheavyDegree v
    · have hv := htotalDegree v
      simp only [degreeOn] at hv ⊢
      omega
  choose copyAt hcopyOutside hcopyZero hcopyNonzero using hcopyExists
  have hlocalCopyDegree : ∀ v (k : Fin r),
      ((H ∪ S).filter fun e ↦ G.Inc v e ∧ copyAt v e = k).card ≤ L := by
    intro v k
    let FH := H.filter fun e ↦ G.Inc v e ∧ copyAt v e = k
    let FS := S.filter fun e ↦ G.Inc v e ∧ copyAt v e = k
    have hsplit :
        ((H ∪ S).filter fun e ↦ G.Inc v e ∧ copyAt v e = k) = FH ∪ FS := by
      ext e
      simp only [FH, FS, Finset.mem_filter, Finset.mem_union]
      aesop
    have hHFdisj : Disjoint FH FS := by
      exact hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [hsplit, Finset.card_union_of_disjoint hHFdisj]
    by_cases hk : k.1 = 0
    · have hFH : FH.card ≤ G.degreeOn H v := by
        exact Finset.card_le_card (by
          intro e he
          have he' := Finset.mem_filter.mp he
          exact Finset.mem_filter.mpr ⟨he'.1, he'.2.1⟩)
      have hFS : FS.card ≤ L - G.degreeOn H v := by
        have hEq : FS =
            (S.filter (G.Inc v)).filter (fun e ↦ (copyAt v e).1 = 0) := by
          ext e
          simp only [FH, FS, Finset.mem_filter]
          constructor
          · rintro ⟨heS, heInc, heCopy⟩
            exact ⟨⟨heS, heInc⟩, by simpa [heCopy] using hk⟩
          · rintro ⟨⟨heS, heInc⟩, heZero⟩
            refine ⟨heS, heInc, Fin.ext ?_⟩
            simpa [hk] using heZero
        rw [hEq]
        exact hcopyZero v
      have hd := hheavyDegree v
      omega
    · have hFH0 : FH = ∅ := by
        apply Finset.Subset.antisymm
        · intro e he
          have he' := Finset.mem_filter.mp he
          have heNS : e ∉ S := fun heS ↦
            Finset.disjoint_left.mp hdisj he'.1 heS
          have heNA : e ∉ S.filter (G.Inc v) := by simp [heNS]
          have hz := hcopyOutside v e heNA
          have hkEq := congrArg Fin.val he'.2.2
          exact (hk (hkEq.symm.trans hz)).elim
        · exact Finset.empty_subset _
      have hFS : FS.card ≤ L := by
        have hEq : FS =
            (S.filter (G.Inc v)).filter (fun e ↦ copyAt v e = k) := by
          ext e
          simp [FS, and_assoc]
        rw [hEq]
        exact hcopyNonzero v k hk
      simp [hFH0, hFS]
  let left : G.E → G.V × Fin r := fun e ↦
    (bip.leftEndpoint e, copyAt (bip.leftEndpoint e) e)
  let right : G.E → G.V × Fin r := fun e ↦
    (bip.rightEndpoint e, copyAt (bip.rightEndpoint e) e)
  have hleftDegree : ∀ x : G.V × Fin r,
      ((H ∪ S).filter fun e ↦ left e = x).card ≤ L := by
    rintro ⟨v, k⟩
    apply (Finset.card_le_card ?_).trans (hlocalCopyDegree v k)
    intro e he
    have he' := Finset.mem_filter.mp he
    have hp1 : bip.leftEndpoint e = v := by
      simpa [left] using congrArg Prod.fst he'.2
    have hp2 : copyAt (bip.leftEndpoint e) e = k := by
      simpa [left] using congrArg Prod.snd he'.2
    apply Finset.mem_filter.mpr
    refine ⟨he'.1, ?_, ?_⟩
    · rw [← hp1]
      exact bip.leftEndpoint_inc e
    · simpa [hp1] using hp2
  have hrightDegree : ∀ x : G.V × Fin r,
      ((H ∪ S).filter fun e ↦ right e = x).card ≤ L := by
    rintro ⟨v, k⟩
    apply (Finset.card_le_card ?_).trans (hlocalCopyDegree v k)
    intro e he
    have he' := Finset.mem_filter.mp he
    have hp1 : bip.rightEndpoint e = v := by
      simpa [right] using congrArg Prod.fst he'.2
    have hp2 : copyAt (bip.rightEndpoint e) e = k := by
      simpa [right] using congrArg Prod.snd he'.2
    apply Finset.mem_filter.mpr
    refine ⟨he'.1, ?_, ?_⟩
    · rw [← hp1]
      exact bip.rightEndpoint_inc e
    · simpa [hp1] using hp2
  obtain ⟨color, hproper⟩ :=
    OrdinaryEdgeColoring.exists_finProperColoring_of_bimap_degree_le
      left right (H ∪ S) L hL hleftDegree hrightDegree
  refine ⟨color, ?_⟩
  intro v i
  let Q := (H ∪ S).filter fun e ↦ G.Inc v e ∧ color e = i
  let QH := H.filter fun e ↦ G.Inc v e ∧ color e = i
  let QS := S.filter fun e ↦ G.Inc v e ∧ color e = i
  have hQsplit : Q = QH ∪ QS := by
    ext e
    simp only [Q, QH, QS, Finset.mem_filter, Finset.mem_union]
    aesop
  have hQdisj : Disjoint QH QS := by
    exact hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcopyInj : Set.InjOn (copyAt v) (Q : Set G.E) := by
    intro e heQ f hfQ hcopies
    have he := Finset.mem_filter.mp (Finset.mem_coe.mp heQ)
    have hf := Finset.mem_filter.mp (Finset.mem_coe.mp hfQ)
    by_contra hef
    have hconflict : left e = left f ∨ right e = right f := by
      cases hv : bip.side v with
      | false =>
          left
          apply Prod.ext
          · exact (bip.leftEndpoint_eq_of_inc_of_side_eq_false he.2.1 hv).trans
              (bip.leftEndpoint_eq_of_inc_of_side_eq_false hf.2.1 hv).symm
          · simpa [left,
              bip.leftEndpoint_eq_of_inc_of_side_eq_false he.2.1 hv,
              bip.leftEndpoint_eq_of_inc_of_side_eq_false hf.2.1 hv]
              using hcopies
      | true =>
          right
          apply Prod.ext
          · exact (bip.rightEndpoint_eq_of_inc_of_side_eq_true he.2.1 hv).trans
              (bip.rightEndpoint_eq_of_inc_of_side_eq_true hf.2.1 hv).symm
          · simpa [right,
              bip.rightEndpoint_eq_of_inc_of_side_eq_true he.2.1 hv,
              bip.rightEndpoint_eq_of_inc_of_side_eq_true hf.2.1 hv]
              using hcopies
    have hneColor := hproper e he.1 f hf.1 hef hconflict
    exact hneColor (he.2.2.trans hf.2.2.symm)
  have hQcard : Q.card ≤ r := by
    have himage : Q.card = (Q.image (copyAt v)).card := by
      exact (Finset.card_image_iff.mpr hcopyInj).symm
    rw [himage]
    simpa using Finset.card_le_card (Finset.subset_univ (Q.image (copyAt v)))
  have hQHcard : QH.card ≤ 1 := by
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
      have heNS : e ∉ S := fun heS ↦
        Finset.disjoint_left.mp hdisj he'.1 heS
      have hfNS : f ∉ S := fun hfS ↦
        Finset.disjoint_left.mp hdisj hf'.1 hfS
      have heNA : e ∉ S.filter (G.Inc v) := by simp [heNS]
      have hfNA : f ∉ S.filter (G.Inc v) := by simp [hfNS]
      exact (hcopyOutside v e heNA).trans (hcopyOutside v f hfNA).symm
  have hcards : Q.card = QH.card + QS.card := by
    rw [hQsplit, Finset.card_union_of_disjoint hQdisj]
  have hloadH :
      G.colorLoadOn H color v i ≤ (QH.card : ℝ) * heavyCap := by
    rw [colorLoadOn, ← Finset.sum_filter]
    change (∑ e ∈ QH, G.weight e) ≤ _
    calc
      (∑ e ∈ QH, G.weight e) ≤ ∑ _e ∈ QH, heavyCap := by
        exact Finset.sum_le_sum fun e he ↦
          hheavy e (Finset.mem_filter.mp he).1
      _ = (QH.card : ℝ) * heavyCap := by simp
  have hloadS :
      G.colorLoadOn S color v i ≤ (QS.card : ℝ) * lightCap := by
    rw [colorLoadOn, ← Finset.sum_filter]
    change (∑ e ∈ QS, G.weight e) ≤ _
    calc
      (∑ e ∈ QS, G.weight e) ≤ ∑ _e ∈ QS, lightCap := by
        exact Finset.sum_le_sum fun e he ↦
          hlight e (Finset.mem_filter.mp he).1
      _ = (QS.card : ℝ) * lightCap := by simp
  have hloadSplit :
      G.colorLoadOn (H ∪ S) color v i =
        G.colorLoadOn H color v i + G.colorLoadOn S color v i := by
    unfold colorLoadOn
    rw [Finset.sum_union hdisj]
  rw [hloadSplit]
  calc
    G.colorLoadOn H color v i + G.colorLoadOn S color v i ≤
        (QH.card : ℝ) * heavyCap + (QS.card : ℝ) * lightCap :=
      add_le_add hloadH hloadS
    _ ≤ 1 := by
      have hQr : QH.card + QS.card ≤ r := hcards ▸ hQcard
      interval_cases hhc : QH.card
      · have hsNat : QS.card ≤ r := by omega
        have hsReal : (QS.card : ℝ) ≤ r := by exact_mod_cast hsNat
        simp only [Nat.cast_zero, zero_mul, zero_add]
        exact (mul_le_mul_of_nonneg_right hsReal hlight_nonneg).trans hsmall
      · have hsNat : QS.card ≤ r - 1 := by omega
        have hsReal : (QS.card : ℝ) ≤ (r - 1 : ℕ) := by exact_mod_cast hsNat
        simp only [Nat.cast_one, one_mul]
        nlinarith

/-- The same compatible-copy statement with the selected edge set named
explicitly. -/
theorem exists_feasibleOn_of_compatible_copies
    (bip : G.Bipartition) (J H S : Finset G.E)
    (hsplit : J = H ∪ S) (hdisj : Disjoint H S)
    (r L : ℕ) (hr : 2 ≤ r) (hL : 0 < L)
    (heavyCap lightCap : ℝ) (hlight_nonneg : 0 ≤ lightCap)
    (hheavy : ∀ e ∈ H, G.weight e ≤ heavyCap)
    (hlight : ∀ e ∈ S, G.weight e ≤ lightCap)
    (hsmall : (r : ℝ) * lightCap ≤ 1)
    (hmixed : heavyCap + ((r - 1 : ℕ) : ℝ) * lightCap ≤ 1)
    (hheavyDegree : ∀ v, G.degreeOn H v ≤ L)
    (htotalDegree : ∀ v, G.degreeOn H v + G.degreeOn S v ≤ r * L) :
    ∃ color : G.E → Fin L, G.IsFeasibleOn J color := by
  rw [hsplit]
  exact exists_feasibleOn_union_of_compatible_copies bip H S hdisj r L hr hL
    heavyCap lightCap hlight_nonneg hheavy hlight hsmall hmixed
    hheavyDegree htotalDegree

end WeightedMultigraph
end WeightedEdgeColoring
