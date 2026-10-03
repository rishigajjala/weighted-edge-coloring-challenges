import WeightedEdgeColoring.RankThreeRegularExtensionBridge

/-!
# Cyclic regularization of the slot side

Assume that every job has exactly `J` options, every slot has degree at most
`S ≤ J`, and every option uses exactly two slots.  We take `2J` disjoint
copies, indexed by `Fin J ⊕ Fin J`.  For every old slot `s` and every one of
its `S - degree(s)` missing incidences, add a dummy job with `J` options.  Its
option `k` joins copy `(inl k)` of `s` to copy `(inr (k+ell))` of `s`.

The cyclic shifts make every copied slot have degree exactly `S`.  Every new
job has degree exactly `J`, and no new job--slot pair or slot--slot pair is
used twice.  The old system is the `inl 0` copy and no new option has an old
owner.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

abbrev CyclicTag (J : ℕ) := Fin J ⊕ Fin J

abbrev CyclicDeficitJob (S : ℕ) :=
  Σ s : Slot, Fin (S - H.slotDegree s)

abbrev CyclicJob (J S : ℕ) :=
  (Job × CyclicTag J) ⊕ H.CyclicDeficitJob S

abbrev CyclicSlot (J : ℕ) := Slot × CyclicTag J

abbrev CyclicOption (J S : ℕ) :=
  (Option × CyclicTag J) ⊕ (H.CyclicDeficitJob S × Fin J)

private theorem card_univ_sum_filter
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (p : Sum A B → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Sum A B)).filter p).card =
      ((Finset.univ : Finset A).filter (fun a ↦ p (.inl a))).card +
      ((Finset.univ : Finset B).filter (fun b ↦ p (.inr b))).card := by
  have hset : (Finset.univ : Finset (Sum A B)).filter p =
      ((Finset.univ : Finset A).filter (fun a ↦ p (.inl a))).disjSum
      ((Finset.univ : Finset B).filter (fun b ↦ p (.inr b))) := by
    ext x
    cases x <;> simp
  rw [hset]
  simp

private theorem card_univ_sigma_fst_fiber
    {A : Type*} [Fintype A] [DecidableEq A]
    (D : A → ℕ) (a : A) :
    ((Finset.univ : Finset (Σ x, Fin (D x))).filter
      (fun x ↦ x.1 = a)).card = D a := by
  calc
    ((Finset.univ : Finset (Σ x, Fin (D x))).filter
      (fun x ↦ x.1 = a)).card =
        ∑ x : (Σ y, Fin (D y)), if x.1 = a then 1 else 0 := by
          rw [Finset.card_filter]
    _ = ∑ y : A, ∑ _i : Fin (D y), if y = a then 1 else 0 := by
      rw [Fintype.sum_sigma]
    _ = D a := by simp

/-- View a deficit index as an element of `Fin J`. -/
def cyclicDeficitIndex {J S : ℕ} (hSJ : S ≤ J)
    (d : H.CyclicDeficitJob S) : Fin J :=
  Fin.castLE ((Nat.sub_le S (H.slotDegree d.1)).trans hSJ) d.2

/-- Owner map of the cyclic extension. -/
def cyclicOwner {J S : ℕ} : H.CyclicOption J S → H.CyclicJob J S
  | .inl ot => .inl (H.owner ot.1, ot.2)
  | .inr dk => .inr dk.1

/-- Slot set of the cyclic extension. -/
def cyclicSlots {J S : ℕ} (hSJ : S ≤ J) :
    H.CyclicOption J S → Finset (CyclicSlot (Slot := Slot) J)
  | .inl ot =>
      (H.slots ot.1).map
        ⟨fun s ↦ (s, ot.2), fun _ _ h ↦ congrArg Prod.fst h⟩
  | .inr dk =>
      {(dk.1.1, Sum.inl dk.2),
        (dk.1.1, Sum.inr (dk.2 + H.cyclicDeficitIndex hSJ dk.1))}

/-- The concrete `2J`-copy cyclic extension. -/
def cyclicRegularization {J S : ℕ} (hSJ : S ≤ J)
    (htwo : ∀ o, (H.slots o).card = 2) :
    RankThreeOptionSystem (H.CyclicJob J S) (CyclicSlot (Slot := Slot) J)
      (H.CyclicOption J S) where
  owner := H.cyclicOwner
  slots := H.cyclicSlots hSJ
  slots_card_le_two := by
    intro q
    rcases q with ot | dk
    · simpa [cyclicSlots] using (htwo ot.1).le
    · simp [cyclicSlots]

namespace CyclicRegularization

variable {H : RankThreeOptionSystem Job Slot Option}
  {J S : ℕ} (hJ : 0 < J) (hSJ : S ≤ J)
  (htwo : ∀ o, (H.slots o).card = 2)

local instance : NeZero J := ⟨Nat.ne_of_gt hJ⟩

abbrev E := H.cyclicRegularization hSJ htwo

/-- The distinguished old copy. -/
def oldTag : CyclicTag J := Sum.inl ⟨0, hJ⟩

def jobEmbedding : Job ↪ H.CyclicJob J S where
  toFun j := Sum.inl (j, oldTag hJ)
  inj' _ _ h := by simpa [oldTag] using h

def slotEmbedding : Slot ↪ CyclicSlot (Slot := Slot) J where
  toFun s := (s, oldTag hJ)
  inj' _ _ h := congrArg Prod.fst h

def optionEmbedding : Option ↪ H.CyclicOption J S where
  toFun o := Sum.inl (o, oldTag hJ)
  inj' _ _ h := by simpa [oldTag] using h

theorem owner_optionEmbedding (o : Option) :
    (E hSJ htwo).owner (optionEmbedding hJ o) =
      jobEmbedding hJ (H.owner o) := by
  rfl

theorem slots_optionEmbedding (o : Option) :
    (E hSJ htwo).slots (optionEmbedding hJ o) =
      (H.slots o).map (slotEmbedding hJ) := by
  rfl

/-- No dummy option is incident with a copied old job. -/
theorem old_job_induced (j : Job) (q : H.CyclicOption J S)
    (hq : (E hSJ htwo).owner q = jobEmbedding hJ j) :
    ∃ o : Option, H.owner o = j ∧ optionEmbedding hJ o = q := by
  rcases q with ot | dk
  · have hpair : (H.owner ot.1, ot.2) = (j, oldTag hJ) :=
      Sum.inl.inj hq
    refine ⟨ot.1, congrArg Prod.fst hpair, ?_⟩
    change Sum.inl (ot.1, oldTag hJ) = Sum.inl ot
    exact congrArg Sum.inl
      (Prod.ext rfl (congrArg Prod.snd hpair).symm)
  · simp [E, cyclicRegularization, cyclicOwner, jobEmbedding] at hq

/-- Every copied old job has the same fibre size as its base job. -/
theorem copiedJob_fiber_card (j : Job) (tag : CyclicTag J) :
    ((E hSJ htwo).fiber (Sum.inl (j, tag))).card =
      (H.fiber j).card := by
  classical
  unfold fiber
  change
    ((Finset.univ : Finset (H.CyclicOption J S)).filter
      (fun q ↦ H.cyclicOwner q = Sum.inl (j, tag))).card =
        (H.fiber j).card
  rw [card_univ_sum_filter]
  have hold :
      ((Finset.univ : Finset (Option × CyclicTag J)).filter
        (fun ot ↦ H.cyclicOwner (S := S) (Sum.inl ot) =
          Sum.inl (j, tag))).card =
        (H.fiber j).card := by
    apply Finset.card_bij (fun ot _hot ↦ ot.1)
    · intro ot hot
      have heq : (H.owner ot.1, ot.2) = (j, tag) :=
        Sum.inl.inj (Finset.mem_filter.mp hot).2
      exact H.mem_fiber.mpr (congrArg Prod.fst heq)
    · intro x hx y hy hxy
      apply Prod.ext hxy
      have hx' : (H.owner x.1, x.2) = (j, tag) :=
        Sum.inl.inj (Finset.mem_filter.mp hx).2
      have hy' : (H.owner y.1, y.2) = (j, tag) :=
        Sum.inl.inj (Finset.mem_filter.mp hy).2
      exact (congrArg Prod.snd hx').trans (congrArg Prod.snd hy').symm
    · intro o ho
      refine ⟨(o, tag), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        change Sum.inl (H.owner o, tag) = Sum.inl (j, tag)
        rw [H.mem_fiber.mp ho]⟩
  rw [hold]
  simp [cyclicOwner]

/-- Every dummy job has exactly `J` options. -/
theorem dummyJob_fiber_card (d : H.CyclicDeficitJob S) :
    ((E hSJ htwo).fiber (Sum.inr d)).card = J := by
  classical
  unfold fiber
  change
    ((Finset.univ : Finset (H.CyclicOption J S)).filter
      (fun q ↦ H.cyclicOwner q = Sum.inr d)).card = J
  rw [card_univ_sum_filter]
  have hdummy :
      ((Finset.univ : Finset (H.CyclicDeficitJob S × Fin J)).filter
        (fun dk ↦ H.cyclicOwner (J := J) (Sum.inr dk) =
          Sum.inr d)).card = J := by
    have hset :
        ((Finset.univ : Finset (H.CyclicDeficitJob S × Fin J)).filter
          (fun dk ↦ H.cyclicOwner (J := J) (Sum.inr dk) =
            Sum.inr d)) =
          (Finset.univ : Finset (Fin J)).map
            ⟨fun k ↦ (d, k), by
              intro x y hxy
              exact congrArg Prod.snd hxy⟩ := by
      ext dk
      simp [cyclicOwner, Prod.ext_iff, eq_comm]
    rw [hset, Finset.card_map]
    simp
  rw [hdummy]
  simp [cyclicOwner]

/-- All job degrees in the cyclic extension are exactly `J`. -/
theorem jobDegree_eq
    (hjob : ∀ j, (H.fiber j).card = J)
    (j' : H.CyclicJob J S) :
    ((E hSJ htwo).fiber j').card = J := by
  rcases j' with jt | d
  · exact (copiedJob_fiber_card (H := H) (hSJ := hSJ) (htwo := htwo)
      jt.1 jt.2).trans (hjob jt.1)
  · exact dummyJob_fiber_card (H := H) (hSJ := hSJ) (htwo := htwo) d

private theorem copied_slot_count (s : Slot) (tag : CyclicTag J) :
    ((Finset.univ : Finset (Option × CyclicTag J)).filter fun ot ↦
      (s, tag) ∈ H.cyclicSlots hSJ (Sum.inl ot)).card =
      H.slotDegree s := by
  classical
  unfold slotDegree
  apply Finset.card_bij (fun ot _hot ↦ ot.1)
  · intro ot hot
    have hm := (Finset.mem_filter.mp hot).2
    have hm' : s ∈ H.slots ot.1 ∧ ot.2 = tag := by
      simpa [cyclicSlots] using hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm'.1⟩
  · intro x hx y hy hxy
    apply Prod.ext hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have hxtag : x.2 = tag := by
      have hxmem : s ∈ H.slots x.1 ∧ x.2 = tag := by
        simpa [cyclicSlots] using hx'
      exact hxmem.2
    have hytag : y.2 = tag := by
      have hymem : s ∈ H.slots y.1 ∧ y.2 = tag := by
        simpa [cyclicSlots] using hy'
      exact hymem.2
    exact hxtag.trans hytag.symm
  · intro o ho
    refine ⟨(o, tag), ?_, rfl⟩
    have hos : s ∈ H.slots o := (Finset.mem_filter.mp ho).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simp [cyclicSlots, hos]⟩

private def deficitJobsAt (s : Slot) : Finset (H.CyclicDeficitJob S) :=
  Finset.univ.filter fun d ↦ d.1 = s

private theorem deficitJobsAt_card (s : Slot) :
    (deficitJobsAt (H := H) (S := S) s).card =
      S - H.slotDegree s := by
  exact card_univ_sigma_fst_fiber (fun t ↦ S - H.slotDegree t) s

private theorem dummy_left_slot_count (s : Slot) (k : Fin J) :
    ((Finset.univ : Finset (H.CyclicDeficitJob S × Fin J)).filter fun dk ↦
      (s, Sum.inl k) ∈ H.cyclicSlots hSJ (Sum.inr dk)).card =
      S - H.slotDegree s := by
  classical
  calc
    ((Finset.univ : Finset (H.CyclicDeficitJob S × Fin J)).filter fun dk ↦
      (s, Sum.inl k) ∈ H.cyclicSlots hSJ (Sum.inr dk)).card =
        (deficitJobsAt (H := H) (S := S) s).card := by
      apply Finset.card_bij (fun dk _hdk ↦ dk.1)
      · intro dk hdk
        have hm := (Finset.mem_filter.mp hdk).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          have hm' : s = dk.1.1 ∧ k = dk.2 := by
            simpa [cyclicSlots] using hm
          exact hm'.1.symm⟩
      · intro x hx y hy hxy
        apply Prod.ext hxy
        have hx' := (Finset.mem_filter.mp hx).2
        have hy' := (Finset.mem_filter.mp hy).2
        have hxmem : s = x.1.1 ∧ k = x.2 := by
          simpa [cyclicSlots] using hx'
        have hymem : s = y.1.1 ∧ k = y.2 := by
          simpa [cyclicSlots] using hy'
        have hxk : x.2 = k := hxmem.2.symm
        have hyk : y.2 = k := hymem.2.symm
        exact hxk.trans hyk.symm
      · intro d hd
        refine ⟨(d, k), ?_, rfl⟩
        have hds : d.1 = s := (Finset.mem_filter.mp hd).2
        subst s
        simp [cyclicSlots]
    _ = S - H.slotDegree s := deficitJobsAt_card (H := H) (S := S) s

private theorem dummy_right_slot_count (s : Slot) (k : Fin J) :
    ((Finset.univ : Finset (H.CyclicDeficitJob S × Fin J)).filter fun dk ↦
      (s, Sum.inr k) ∈ H.cyclicSlots hSJ (Sum.inr dk)).card =
      S - H.slotDegree s := by
  classical
  calc
    ((Finset.univ : Finset (H.CyclicDeficitJob S × Fin J)).filter fun dk ↦
      (s, Sum.inr k) ∈ H.cyclicSlots hSJ (Sum.inr dk)).card =
        (deficitJobsAt (H := H) (S := S) s).card := by
      apply Finset.card_bij (fun dk _hdk ↦ dk.1)
      · intro dk hdk
        have hm := (Finset.mem_filter.mp hdk).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          have hm' : s = dk.1.1 ∧
              k = dk.2 + H.cyclicDeficitIndex hSJ dk.1 := by
            simpa [cyclicSlots] using hm
          exact hm'.1.symm⟩
      · intro x hx y hy hxy
        apply Prod.ext hxy
        have hx' := (Finset.mem_filter.mp hx).2
        have hy' := (Finset.mem_filter.mp hy).2
        have hxk : x.2 + H.cyclicDeficitIndex hSJ x.1 = k := by
          have hxmem : s = x.1.1 ∧
              k = x.2 + H.cyclicDeficitIndex hSJ x.1 := by
            simpa [cyclicSlots] using hx'
          exact hxmem.2.symm
        have hyk : y.2 + H.cyclicDeficitIndex hSJ y.1 = k := by
          have hymem : s = y.1.1 ∧
              k = y.2 + H.cyclicDeficitIndex hSJ y.1 := by
            simpa [cyclicSlots] using hy'
          exact hymem.2.symm
        rw [hxy] at hxk
        exact add_right_cancel (hxk.trans hyk.symm)
      · intro d hd
        let e := H.cyclicDeficitIndex hSJ d
        have hsurj : Function.Surjective (fun q : Fin J ↦ q + e) :=
          Finite.surjective_of_injective (f := fun q : Fin J ↦ q + e)
            (fun _ _ h ↦ add_right_cancel h)
        obtain ⟨q, hq⟩ := hsurj k
        refine ⟨(d, q), ?_, rfl⟩
        have hds : d.1 = s := (Finset.mem_filter.mp hd).2
        subst s
        simp [cyclicSlots, e, hq]
    _ = S - H.slotDegree s := deficitJobsAt_card (H := H) (S := S) s

/-- Every copied slot has exact degree `S`. -/
theorem slotDegree_eq
    (hslot : ∀ s, H.slotDegree s ≤ S)
    (s' : CyclicSlot (Slot := Slot) J) :
    (E hSJ htwo).slotDegree s' = S := by
  classical
  rcases s' with ⟨s, tag⟩
  unfold slotDegree
  change
    ((Finset.univ : Finset (H.CyclicOption J S)).filter
      (fun q ↦ (s, tag) ∈ H.cyclicSlots hSJ q)).card = S
  rw [card_univ_sum_filter]
  have hold := copied_slot_count (H := H) (hSJ := hSJ) s tag
  rcases tag with k | k
  · have hdummy := dummy_left_slot_count (H := H) (hSJ := hSJ) s k
    rw [hold, hdummy]
    exact Nat.add_sub_of_le (hslot s)
  · have hdummy := dummy_right_slot_count (H := H) (hSJ := hSJ) s k
    rw [hold, hdummy]
    exact Nat.add_sub_of_le (hslot s)

private def copiedOptionEmbedding (tag : CyclicTag J) :
    Option ↪ H.CyclicOption J S where
  toFun o := Sum.inl (o, tag)
  inj' _ _ h := by simpa using h

private theorem copied_jobSlotCodegree
    (j : Job) (jobTag : CyclicTag J)
    (s : Slot) (slotTag : CyclicTag J) :
    (E hSJ htwo).jobSlotCodegree (Sum.inl (j, jobTag)) (s, slotTag) =
      if jobTag = slotTag then H.jobSlotCodegree j s else 0 := by
  classical
  by_cases htag : jobTag = slotTag
  · subst slotTag
    have hset :
        (((E hSJ htwo).fiber (Sum.inl (j, jobTag))).filter fun q ↦
          (s, jobTag) ∈ (E hSJ htwo).slots q) =
        ((H.fiber j).filter fun o ↦ s ∈ H.slots o).map
          (copiedOptionEmbedding (H := H) (S := S) jobTag) := by
      ext q
      rcases q with ot | dk
      · simp [E, cyclicRegularization, cyclicOwner, cyclicSlots,
          copiedOptionEmbedding, H.mem_fiber, and_assoc, and_left_comm,
          and_comm] <;> aesop
      · simp [E, cyclicRegularization, cyclicOwner, copiedOptionEmbedding]
          <;> aesop
    simp [jobSlotCodegree, hset]
  · have hset :
        (((E hSJ htwo).fiber (Sum.inl (j, jobTag))).filter fun q ↦
          (s, slotTag) ∈ (E hSJ htwo).slots q) = ∅ := by
      ext q
      rcases q with ot | dk
      · simp [E, cyclicRegularization, cyclicOwner, cyclicSlots, htag,
          and_assoc, and_left_comm, and_comm] <;> aesop
      · simp [E, cyclicRegularization, cyclicOwner, copiedOptionEmbedding]
    simp [jobSlotCodegree, hset, htag]

private theorem dummy_jobSlotCodegree_le_one
    (d : H.CyclicDeficitJob S) (s' : CyclicSlot (Slot := Slot) J) :
    (E hSJ htwo).jobSlotCodegree (Sum.inr d) s' ≤ 1 := by
  classical
  unfold jobSlotCodegree
  rw [Finset.card_le_one_iff]
  intro q r hq hr
  have hqf := (Finset.mem_filter.mp hq).1
  have hrf := (Finset.mem_filter.mp hr).1
  have hqs := (Finset.mem_filter.mp hq).2
  have hrs := (Finset.mem_filter.mp hr).2
  rcases q with ot | qd
  · simp [E, cyclicRegularization, cyclicOwner, fiber] at hqf
  rcases r with ot | rd
  · simp [E, cyclicRegularization, cyclicOwner, fiber] at hrf
  rcases qd with ⟨qd, qk⟩
  rcases rd with ⟨rd, rk⟩
  have hqd : qd = d := by
    simpa [E, cyclicRegularization, cyclicOwner, fiber] using hqf
  have hrd : rd = d := by
    simpa [E, cyclicRegularization, cyclicOwner, fiber] using hrf
  subst qd
  subst rd
  congr 3
  rcases s' with ⟨s, tag⟩
  rcases tag with k | k
  · have hqmem : s = d.1 ∧ k = qk := by
      simpa [E, cyclicRegularization, cyclicSlots] using hqs
    have hrmem : s = d.1 ∧ k = rk := by
      simpa [E, cyclicRegularization, cyclicSlots] using hrs
    have hqk : qk = k := hqmem.2.symm
    have hrk : rk = k := hrmem.2.symm
    exact hqk.trans hrk.symm
  · have hqk : qk + H.cyclicDeficitIndex hSJ d = k := by
      have hqmem : s = d.1 ∧
          k = qk + H.cyclicDeficitIndex hSJ d := by
        simpa [E, cyclicRegularization, cyclicSlots] using hqs
      exact hqmem.2.symm
    have hrk : rk + H.cyclicDeficitIndex hSJ d = k := by
      have hrmem : s = d.1 ∧
          k = rk + H.cyclicDeficitIndex hSJ d := by
        simpa [E, cyclicRegularization, cyclicSlots] using hrs
      exact hrmem.2.symm
    exact add_right_cancel (hqk.trans hrk.symm)

/-- Every job--slot codegree in the extension is at most
`max lambda 1`. -/
theorem jobSlotCodegree_le
    (hlambda : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (j' : H.CyclicJob J S) (s' : CyclicSlot (Slot := Slot) J) :
    (E hSJ htwo).jobSlotCodegree j' s' ≤ max lambda 1 := by
  rcases j' with jt | d
  · rcases s' with ⟨s, tag⟩
    rw [copied_jobSlotCodegree (H := H) (hSJ := hSJ) (htwo := htwo)
      jt.1 jt.2 s tag]
    split_ifs
    · exact (hlambda jt.1 s).trans (Nat.le_max_left _ _)
    · exact Nat.zero_le _
  · exact (dummy_jobSlotCodegree_le_one (H := H) (hSJ := hSJ)
      (htwo := htwo) d s').trans
      (Nat.le_max_right _ _)

private theorem copied_pair_count
    (s t : Slot) (a b : CyclicTag J) :
    ((Finset.univ : Finset (Option × CyclicTag J)).filter fun ot ↦
      (s, a) ∈ H.cyclicSlots hSJ (Sum.inl ot) ∧
      (t, b) ∈ H.cyclicSlots hSJ (Sum.inl ot)).card =
      if a = b then H.slotPairCodegree s t else 0 := by
  classical
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    unfold slotPairCodegree
    apply Finset.card_bij (fun ot _hot ↦ ot.1)
    · intro ot hot
      have hm := (Finset.mem_filter.mp hot).2
      have hm' :
          (s ∈ H.slots ot.1 ∧ ot.2 = a) ∧
            (t ∈ H.slots ot.1 ∧ ot.2 = a) := by
        simpa [cyclicSlots] using hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm'.1.1, hm'.2.1⟩
    · intro x hx y hy hxy
      apply Prod.ext hxy
      have hx' := (Finset.mem_filter.mp hx).2.1
      have hy' := (Finset.mem_filter.mp hy).2.1
      have hxmem : s ∈ H.slots x.1 ∧ x.2 = a := by
        simpa [cyclicSlots] using hx'
      have hymem : s ∈ H.slots y.1 ∧ y.2 = a := by
        simpa [cyclicSlots] using hy'
      have hxa : x.2 = a := hxmem.2
      have hya : y.2 = a := hymem.2
      exact hxa.trans hya.symm
    · intro o ho
      refine ⟨(o, a), ?_, rfl⟩
      have ho' := (Finset.mem_filter.mp ho).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [cyclicSlots] using ho'⟩
  · have hempty :
        ((Finset.univ : Finset (Option × CyclicTag J)).filter fun ot ↦
          (s, a) ∈ H.cyclicSlots hSJ (Sum.inl ot) ∧
          (t, b) ∈ H.cyclicSlots hSJ (Sum.inl ot)) = ∅ := by
      ext ot
      simp [cyclicSlots] <;> aesop
    rw [hempty]
    simp [hab]

private theorem dummySlots_injective :
    Function.Injective
      (fun dk : H.CyclicDeficitJob S × Fin J ↦
        H.cyclicSlots hSJ (Sum.inr dk)) := by
  classical
  rintro ⟨⟨xs, xi⟩, xk⟩ ⟨⟨ys, yi⟩, yk⟩ hxy
  have hxleft :
      (xs, Sum.inl xk) ∈
        H.cyclicSlots hSJ (Sum.inr (⟨xs, xi⟩, xk)) := by
    simp [cyclicSlots]
  have hleftEq := congrArg
    (fun F ↦ (xs, Sum.inl xk) ∈ F) hxy
  have hyleft :
      (xs, Sum.inl xk) ∈
        H.cyclicSlots hSJ (Sum.inr (⟨ys, yi⟩, yk)) :=
    hleftEq.mp hxleft
  have hleft : xs = ys ∧ xk = yk := by
    simpa [cyclicSlots] using hyleft
  rcases hleft with ⟨rfl, rfl⟩
  have hxright :
      (xs, Sum.inr (xk + H.cyclicDeficitIndex hSJ ⟨xs, xi⟩)) ∈
        H.cyclicSlots hSJ (Sum.inr (⟨xs, xi⟩, xk)) := by
    simp [cyclicSlots]
  have hrightEq := congrArg
    (fun F ↦
      (xs, Sum.inr (xk + H.cyclicDeficitIndex hSJ ⟨xs, xi⟩)) ∈ F) hxy
  have hyright := hrightEq.mp hxright
  have hsum : xk + H.cyclicDeficitIndex hSJ ⟨xs, xi⟩ =
      xk + H.cyclicDeficitIndex hSJ ⟨xs, yi⟩ := by
    simpa [cyclicSlots] using hyright
  have hidx : H.cyclicDeficitIndex hSJ ⟨xs, xi⟩ =
      H.cyclicDeficitIndex hSJ ⟨xs, yi⟩ := add_left_cancel hsum
  have hi : xi = yi := by
    let hb : S - H.slotDegree xs ≤ J :=
      (Nat.sub_le S (H.slotDegree xs)).trans hSJ
    apply Fin.castLE_injective hb
    simpa [cyclicDeficitIndex, hb] using hidx
  subst yi
  rfl

private theorem dummy_pair_count_le_one
    (x y : CyclicSlot (Slot := Slot) J) (hxy : x ≠ y) :
    ((Finset.univ : Finset (H.CyclicDeficitJob S × Fin J)).filter fun dk ↦
      x ∈ H.cyclicSlots hSJ (Sum.inr dk) ∧
      y ∈ H.cyclicSlots hSJ (Sum.inr dk)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  have hpSub : ({x, y} : Finset (CyclicSlot (Slot := Slot) J)) ⊆
      H.cyclicSlots hSJ (Sum.inr p) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hp'.1
    · exact hp'.2
  have hqSub : ({x, y} : Finset (CyclicSlot (Slot := Slot) J)) ⊆
      H.cyclicSlots hSJ (Sum.inr q) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hq'.1
    · exact hq'.2
  have hpairCard : ({x, y} : Finset (CyclicSlot (Slot := Slot) J)).card = 2 := by
    simp [hxy]
  have hpCard : (H.cyclicSlots hSJ (Sum.inr p)).card = 2 := by
    simp [cyclicSlots]
  have hqCard : (H.cyclicSlots hSJ (Sum.inr q)).card = 2 := by
    simp [cyclicSlots]
  have hpEq := Finset.eq_of_subset_of_card_le hpSub (by omega)
  have hqEq := Finset.eq_of_subset_of_card_le hqSub (by omega)
  apply dummySlots_injective (H := H) (hSJ := hSJ)
  exact hpEq.symm.trans hqEq

/-- Every distinct slot-pair codegree in the extension is at most
`max lambda 1`. -/
theorem slotPairCodegree_le
    (hpair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (x y : CyclicSlot (Slot := Slot) J) (hxy : x ≠ y) :
    (E hSJ htwo).slotPairCodegree x y ≤ max lambda 1 := by
  classical
  rcases x with ⟨s, a⟩
  rcases y with ⟨t, b⟩
  unfold slotPairCodegree
  change
    ((Finset.univ : Finset (H.CyclicOption J S)).filter
      (fun q ↦ (s, a) ∈ H.cyclicSlots hSJ q ∧
        (t, b) ∈ H.cyclicSlots hSJ q)).card ≤ max lambda 1
  rw [card_univ_sum_filter]
  have hold := copied_pair_count (H := H) (hSJ := hSJ) s t a b
  by_cases hab : a = b
  · subst b
    have hst : s ≠ t := by
      intro h
      exact hxy (Prod.ext h rfl)
    have hdummy :
        ((Finset.univ : Finset (H.CyclicDeficitJob S × Fin J)).filter fun dk ↦
          (s, a) ∈ H.cyclicSlots hSJ (Sum.inr dk) ∧
          (t, a) ∈ H.cyclicSlots hSJ (Sum.inr dk)) = ∅ := by
      ext dk
      rcases a with k | k <;> simp [cyclicSlots] <;> aesop
    rw [hold, if_pos rfl, hdummy]
    simp only [Finset.card_empty, add_zero]
    exact (hpair s t hst).trans (Nat.le_max_left _ _)
  · rw [hold, if_neg hab, zero_add]
    exact (dummy_pair_count_le_one (H := H) (hSJ := hSJ)
      (s, a) (t, b) hxy).trans
      (Nat.le_max_right _ _)

/-- The cyclic construction, packaged for the projection bridge. -/
def regularExtension
    (hjob : ∀ j, (H.fiber j).card = J)
    (hslot : ∀ s, H.slotDegree s ≤ S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hpair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    IsRegularExtension H (E hSJ htwo) J S (max lambda 1) where
  jobEmbedding := jobEmbedding hJ
  slotEmbedding := slotEmbedding hJ
  optionEmbedding := optionEmbedding hJ
  owner_optionEmbedding := owner_optionEmbedding (H := H) hJ hSJ htwo
  slots_optionEmbedding := slots_optionEmbedding (H := H) hJ hSJ htwo
  old_job_induced := old_job_induced (H := H) hJ hSJ htwo
  jobDegree_eq := jobDegree_eq (H := H) (hSJ := hSJ) (htwo := htwo) hjob
  slotDegree_eq := slotDegree_eq (H := H) (hSJ := hSJ) (htwo := htwo) hslot
  jobSlotCodegree_le := jobSlotCodegree_le (H := H) (hSJ := hSJ)
    (htwo := htwo) hjobSlot
  slotPairCodegree_le := slotPairCodegree_le (H := H) (hSJ := hSJ)
    (htwo := htwo) hpair

end CyclicRegularization

end WeightedEdgeColoring.RankThreeOptionSystem
