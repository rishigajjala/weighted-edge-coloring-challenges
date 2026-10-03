import WeightedEdgeColoring.FiniteCategoricalEventLLL
import WeightedEdgeColoring.FiniteCategoricalManySums
import WeightedEdgeColoring.RankThreeResidualHarrisBridge
import WeightedEdgeColoring.RankThreeOptionRestriction
import Mathlib.Order.Lattice

/-!
# The final categorical local-lemma matching step

Assume that every job has exactly `900 * b` remaining options and every
slot occurs in at most `b` options.  Independently choose a uniform option
for each job.  A bad event is an (owner-ordered) pair of choices which meet
in a slot.  Its mass is `(900*b)⁻²`.  One job is incident with at most
`(900*b) * (2*b)` bad events, so every bad event has at most `3600*b²`
support-overlap neighbours.  The finite categorical local lemma therefore
gives one slot-disjoint option for every job.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]

section Ordered

variable
  [LinearOrder Job]
  (H : RankThreeOptionSystem Job Slot Option)

/-- A slot collision between distinct jobs, oriented by the job order. -/
abbrev FinalCollision :=
  {op : Option × Option //
    H.owner op.1 < H.owner op.2 ∧ ¬ H.Compatible op.1 op.2}

/-- The two categorical sources read by a collision event. -/
def finalCollisionSupport (c : H.FinalCollision) : Finset Job :=
  {H.owner c.1.1, H.owner c.1.2}

/-- The event that the two owners choose the displayed conflicting options. -/
noncomputable def finalCollisionEvent (c : H.FinalCollision) :
    Finset (Job → Option) :=
  Finset.univ.filter fun choice ↦
    choice (H.owner c.1.1) = c.1.1 ∧
      choice (H.owner c.1.2) = c.1.2

/-- Uniform probability on the fibre of the source job, extended by zero to
the common state space `Option`. -/
noncomputable def finalUniformProb (m : ℕ) (j : Job) (o : Option) : ℝ :=
  if H.owner o = j then 1 / (m : ℝ) else 0

/-- Collision events containing a specified option. -/
noncomputable def finalCollisionsAtOption (o : Option) :
    Finset H.FinalCollision :=
  Finset.univ.filter fun c ↦ c.1.1 = o ∨ c.1.2 = o

/-- Collision events whose two-source support contains a specified job. -/
noncomputable def finalCollisionsAtJob (j : Job) :
    Finset H.FinalCollision :=
  WeightedEdgeColoring.FiniteCategoricalEventLLL.supportIncidence
    H.finalCollisionSupport j

theorem finalCollisionSupport_card (c : H.FinalCollision) :
    (H.finalCollisionSupport c).card = 2 := by
  have hne : H.owner c.1.1 ≠ H.owner c.1.2 := ne_of_lt c.2.1
  simp [finalCollisionSupport, hne]

theorem finalCollisionEvent_dependsOn (c : H.FinalCollision) :
    WeightedEdgeColoring.FiniteCategoricalSelection.DependsOn
      (H.finalCollisionSupport c) (H.finalCollisionEvent c) := by
  intro x y hxy
  have hleft := hxy (H.owner c.1.1) (by simp [finalCollisionSupport])
  have hright := hxy (H.owner c.1.2) (by simp [finalCollisionSupport])
  simp only [finalCollisionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hleft, hright]

theorem sum_finalUniformProb (m : ℕ)
    (hm : ∀ j, (H.fiber j).card = m) (hm0 : 0 < m) (j : Job) :
    ∑ o, H.finalUniformProb m j o = 1 := by
  unfold finalUniformProb
  rw [← Finset.sum_filter]
  change (∑ o ∈ H.fiber j, (1 / (m : ℝ))) = 1
  simp [hm j, ne_of_gt hm0]

theorem finalUniformProb_nonneg (m : ℕ) :
    ∀ j o, 0 ≤ H.finalUniformProb m j o := by
  intro j o
  simp only [finalUniformProb]
  split <;> positivity

theorem finalUniformProb_pos_iff {m : ℕ} (hm0 : 0 < m)
    {j : Job} {o : Option} :
    0 < H.finalUniformProb m j o ↔ H.owner o = j := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  by_cases h : H.owner o = j <;> simp [finalUniformProb, h, hmR]

/-- Exact mass of a two-coordinate cylinder in a normalized categorical
product. -/
private theorem finalCollisionEvent_mass
    (m : ℕ) (hm : ∀ j, (H.fiber j).card = m) (hm0 : 0 < m)
    (c : H.FinalCollision) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
      (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
        (H.finalUniformProb m))
      (H.finalCollisionEvent c) = 1 / ((m : ℝ) ^ 2) := by
  classical
  let j := H.owner c.1.1
  let k := H.owner c.1.2
  have hjk : j ≠ k := ne_of_lt c.2.1
  have hkj : k ≠ j := Ne.symm hjk
  let weight : Job → Option → ℝ := fun s a ↦
    if s = j then
      if a = c.1.1 then H.finalUniformProb m s a else 0
    else if s = k then
      if a = c.1.2 then H.finalUniformProb m s a else 0
    else H.finalUniformProb m s a
  unfold WeightedEdgeColoring.FiniteLocalLemma.eventMass
  unfold finalCollisionEvent
  rw [Finset.sum_filter]
  have hrewrite (choice : Job → Option) :
      (if choice j = c.1.1 ∧ choice k = c.1.2 then
          WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
            (H.finalUniformProb m) choice else 0) =
        ∏ s, weight s (choice s) := by
    by_cases hleft : choice j = c.1.1
    · by_cases hright : choice k = c.1.2
      · simp only [hleft, hright, and_self, if_true]
        unfold WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
        apply Finset.prod_congr rfl
        intro s _hs
        by_cases hsj : s = j
        · subst s
          simp [weight, hleft]
        · by_cases hsk : s = k
          · subst s
            simp [weight, hkj, hright]
          · simp [weight, hsj, hsk]
      · simp only [hleft, hright, and_false, if_false]
        exact (Finset.prod_eq_zero (Finset.mem_univ k) (by
          simp [weight, hkj, hright])).symm
    · simp only [hleft, false_and, if_false]
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by
        simp [weight, hleft])).symm
  calc
    (∑ choice : Job → Option,
        if choice j = c.1.1 ∧ choice k = c.1.2 then
          WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
            (H.finalUniformProb m) choice else 0) =
        ∑ choice : Job → Option, ∏ s, weight s (choice s) := by
      apply Finset.sum_congr rfl
      intro choice _
      exact hrewrite choice
    _ = ∏ s, ∑ a, weight s a :=
      (Fintype.prod_sum (ι := Job) (κ := fun _ ↦ Option)
        (R := ℝ) weight).symm
    _ = (∑ a, weight j a) * (∑ a, weight k a) := by
      apply Finset.prod_eq_mul_of_mem j k (Finset.mem_univ j)
        (Finset.mem_univ k) hjk
      intro s _hs hs
      simp [weight, hs.1, hs.2, H.sum_finalUniformProb m hm hm0]
    _ = H.finalUniformProb m j c.1.1 *
        H.finalUniformProb m k c.1.2 := by
      simp [weight, hjk, hkj]
    _ = 1 / ((m : ℝ) ^ 2) := by
      have hj : H.owner c.1.1 = j := rfl
      have hk : H.owner c.1.2 = k := rfl
      simp [finalUniformProb, hj, hk]
      ring

/-- A canonical cross-job collision containing `o` is determined by its
other option, and that option meets `o` in a slot. -/
theorem finalCollisionsAtOption_card_le_optionsMeeting (o : Option) :
    (H.finalCollisionsAtOption o).card ≤ (H.optionsMeeting o).card := by
  classical
  let other : H.FinalCollision → Option := fun c ↦
    if c.1.1 = o then c.1.2 else c.1.1
  apply Finset.card_le_card_of_injOn other
  · intro c hc
    have hcontains := (Finset.mem_filter.mp hc).2
    rcases hcontains with hleft | hright
    · have hmeet : ¬ Disjoint (H.slots o) (H.slots c.1.2) := by
        simpa [hleft] using c.2.2
      rw [Finset.not_disjoint_iff] at hmeet
      rcases hmeet with ⟨s, hso, hsc⟩
      simp only [other, hleft, if_true]
      exact Finset.mem_biUnion.mpr
        ⟨s, hso, H.mem_slotOptionFiber.mpr hsc⟩
    · have hmeet : ¬ Disjoint (H.slots o) (H.slots c.1.1) := by
        simpa [Compatible, hright, disjoint_comm] using c.2.2
      have hleftne : c.1.1 ≠ o := by
        intro hleft
        have hirr : H.owner o < H.owner o := by
          simpa [hleft, hright] using c.2.1
        exact (lt_irrefl _ hirr)
      rw [Finset.not_disjoint_iff] at hmeet
      rcases hmeet with ⟨s, hso, hsc⟩
      simp only [other, hleftne, if_false]
      exact Finset.mem_biUnion.mpr
        ⟨s, hso, H.mem_slotOptionFiber.mpr hsc⟩
  · intro c hc d hd heq
    have hc' := (Finset.mem_filter.mp hc).2
    have hd' := (Finset.mem_filter.mp hd).2
    apply Subtype.ext
    rcases hc' with hcl | hcr <;> rcases hd' with hdl | hdr
    · apply Prod.ext
      · exact hcl.trans hdl.symm
      · simpa [other, hcl, hdl] using heq
    · exfalso
      have hdleft : d.1.1 ≠ o := by
        intro hdleft
        have hirr : H.owner o < H.owner o := by
          simpa [hdleft, hdr] using d.2.1
        exact (lt_irrefl _ hirr)
      have hother : c.1.2 = d.1.1 := by
        simpa [other, hcl, hdleft] using heq
      have hirr : H.owner o < H.owner o := by
        have hcLt := c.2.1
        have hdLt := d.2.1
        rw [hcl, hother] at hcLt
        rw [hdr] at hdLt
        exact hcLt.trans hdLt
      exact lt_irrefl _ hirr
    · exfalso
      have hcleft : c.1.1 ≠ o := by
        intro hcleft
        have hirr : H.owner o < H.owner o := by
          simpa [hcleft, hcr] using c.2.1
        exact (lt_irrefl _ hirr)
      have hother : c.1.1 = d.1.2 := by
        simpa [other, hcleft, hdl] using heq
      have hirr : H.owner o < H.owner o := by
        have hdLt := d.2.1
        have hcLt := c.2.1
        rw [hdl, ← hother] at hdLt
        rw [hcr] at hcLt
        exact hdLt.trans hcLt
      exact lt_irrefl _ hirr
    · apply Prod.ext
      · have hcleft : c.1.1 ≠ o := by
          intro hleft
          have hirr : H.owner o < H.owner o := by
            simpa [hleft, hcr] using c.2.1
          exact lt_irrefl _ hirr
        have hdleft : d.1.1 ≠ o := by
          intro hleft
          have hirr : H.owner o < H.owner o := by
            simpa [hleft, hdr] using d.2.1
          exact lt_irrefl _ hirr
        simpa [other, hcleft, hdleft] using heq
      · exact hcr.trans hdr.symm

theorem finalCollisionsAtOption_card_le_two_mul
    (b : ℕ) (hslot : ∀ s, H.slotDegree s ≤ b) (o : Option) :
    (H.finalCollisionsAtOption o).card ≤ 2 * b := by
  exact (H.finalCollisionsAtOption_card_le_optionsMeeting o).trans
    (H.optionsMeeting_card_le_two_mul b hslot o)

theorem finalCollisionsAtJob_card_le
    (m b : ℕ) (hfiber : ∀ j, (H.fiber j).card = m)
    (hslot : ∀ s, H.slotDegree s ≤ b) (j : Job) :
    (H.finalCollisionsAtJob j).card ≤ m * (2 * b) := by
  have hsub : H.finalCollisionsAtJob j ⊆
      (H.fiber j).biUnion H.finalCollisionsAtOption := by
    intro c hc
    have hsource := (Finset.mem_filter.mp hc).2
    simp only [finalCollisionSupport, Finset.mem_insert,
      Finset.mem_singleton] at hsource
    rcases hsource with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨c.1.1,
        H.mem_fiber.mpr hleft.symm,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨c.1.2,
        H.mem_fiber.mpr hright.symm,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl⟩⟩
  calc
    (H.finalCollisionsAtJob j).card ≤
        ((H.fiber j).biUnion H.finalCollisionsAtOption).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ o ∈ H.fiber j, (H.finalCollisionsAtOption o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ H.fiber j, 2 * b := by
      exact Finset.sum_le_sum fun o _ ↦
        H.finalCollisionsAtOption_card_le_two_mul b hslot o
    _ = (H.fiber j).card * (2 * b) := by simp
    _ = m * (2 * b) := by rw [hfiber j]

theorem finalCollision_overlap_degree_le
    (m b : ℕ) (hfiber : ∀ j, (H.fiber j).card = m)
    (hslot : ∀ s, H.slotDegree s ≤ b) (c : H.FinalCollision) :
    (WeightedEdgeColoring.FiniteCategoricalEventLLL.overlapNeighbor
      H.finalCollisionSupport c).card ≤ 2 * (m * (2 * b)) := by
  apply WeightedEdgeColoring.FiniteCategoricalEventLLL.overlapNeighbor_card_le
    H.finalCollisionSupport 2 (m * (2 * b))
  · intro d
    exact (H.finalCollisionSupport_card d).le
  · exact H.finalCollisionsAtJob_card_le m b hfiber hslot

private theorem exists_positive_avoiding_finalCollisions
    (m b : ℕ) (hm0 : 0 < m)
    (hfiber : ∀ j, (H.fiber j).card = m)
    (hslot : ∀ s, H.slotDegree s ≤ b)
    (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hnumeric : 1 / ((m : ℝ) ^ 2) ≤
      x * (1 - x) ^ (2 * (m * (2 * b)))) :
    ∃ choice : Job → Option,
      0 < WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
        (H.finalUniformProb m) choice ∧
      ∀ c, choice ∉ H.finalCollisionEvent c := by
  let prob := H.finalUniformProb m
  let event := H.finalCollisionEvent
  let support := H.finalCollisionSupport
  let neighbor := WeightedEdgeColoring.FiniteCategoricalEventLLL.overlapNeighbor support
  let good := WeightedEdgeColoring.FiniteLocalLemma.avoid event Finset.univ
  have hpositive : 0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass
      (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob) good := by
    apply WeightedEdgeColoring.FiniteProductCylinder.symmetric_lopsided_local_lemma_of_independent
      (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob)
      event neighbor (1 / ((m : ℝ) ^ 2)) x (2 * (m * (2 * b)))
      (WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass_nonneg prob
        (H.finalUniformProb_nonneg m))
      (WeightedEdgeColoring.FiniteCategoricalSelection.sum_categoricalMass prob
        (H.sum_finalUniformProb m hfiber hm0))
      (H.finalCollision_overlap_degree_le m b hfiber hslot)
      hx0 hx1 hnumeric
      (fun c ↦ le_of_eq (H.finalCollisionEvent_mass m hfiber hm0 c))
    intro c T hT
    apply WeightedEdgeColoring.FiniteCategoricalSupportSplit.independentEvents_of_dependsOn_disjoint
      prob (H.sum_finalUniformProb m hfiber hm0)
      (support c)
      (WeightedEdgeColoring.FiniteCategoricalEventLLL.supportsOfEvents support T)
    · exact WeightedEdgeColoring.FiniteCategoricalEventLLL.support_disjoint_supportsOfEvents_of_nonNeighbors
        support c T hT
    · exact H.finalCollisionEvent_dependsOn c
    · exact WeightedEdgeColoring.FiniteCategoricalEventLLL.avoid_dependsOn_supportsOfEvents
        event support H.finalCollisionEvent_dependsOn T
  unfold WeightedEdgeColoring.FiniteLocalLemma.eventMass at hpositive
  have hex : ∃ choice ∈ good,
      0 < WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob choice := by
    by_contra hnone
    push_neg at hnone
    have hnonpos :
        (∑ choice ∈ good,
          WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass prob choice) ≤ 0 :=
      Finset.sum_nonpos fun choice hchoice ↦ hnone choice hchoice
    exact (not_le_of_gt hpositive) hnonpos
  obtain ⟨choice, hchoiceGood, hchoicePos⟩ := hex
  refine ⟨choice, hchoicePos, ?_⟩
  simpa [good, WeightedEdgeColoring.FiniteLocalLemma.avoid] using hchoiceGood

/-- The elementary numerical check for the manuscript constants. -/
theorem finalLLL_numeric (b : ℕ) (hb : 0 < b) :
    let m : ℕ := 900 * b
    let d : ℕ := 3600 * b ^ 2
    let x : ℝ := 1 / (2 * ((d : ℝ) + 1))
    1 / ((m : ℝ) ^ 2) ≤ x * (1 - x) ^ d := by
  dsimp
  have hden : (4 : ℝ) * (3600 * (b : ℝ) ^ 2 + 1) ≤
      ((900 * b : ℕ) : ℝ) ^ 2 := by
    norm_num
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith [sq_nonneg ((b : ℝ) - 1)]
  have hfirst :
      1 / (((900 * b : ℕ) : ℝ) ^ 2) ≤
        1 / (4 * (((3600 * b ^ 2 : ℕ) : ℝ) + 1)) := by
    exact one_div_le_one_div_of_le (by positivity) (by
      norm_num at hden ⊢
      exact hden)
  exact hfirst.trans
    (WeightedEdgeColoring.FiniteCategoricalSelection.quarter_inv_degree_le_lllWitness
      (3600 * b ^ 2))

/-- Final-phase matching theorem: exact job degree `900*b` and slot degree at
most `b` suffice to choose one option from every job with pairwise disjoint
slot sets. -/
theorem exists_covering_partialMatching_finalLLL_of_linearOrder
    (b : ℕ) (hb : 0 < b)
    (hfiber : ∀ j, (H.fiber j).card = 900 * b)
    (hslot : ∀ s, H.slotDegree s ≤ b) :
    ∃ M : Finset Option,
      H.IsPartialMatching M ∧ ∀ j, H.Covers M j := by
  let m := 900 * b
  let d := 3600 * b ^ 2
  let x : ℝ := 1 / (2 * ((d : ℝ) + 1))
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hrewrite : 2 * (m * (2 * b)) = d := by
    dsimp [m, d]
    ring
  have hnumeric : 1 / ((m : ℝ) ^ 2) ≤
      x * (1 - x) ^ (2 * (m * (2 * b))) := by
    rw [hrewrite]
    exact finalLLL_numeric b hb
  have hx0 : 0 ≤ x := by dsimp [x, d]; positivity
  have hx1 : x < 1 := by
    dsimp [x, d]
    apply (div_lt_one (by positivity)).2
    have hd0 : (0 : ℝ) ≤ ((3600 * b ^ 2 : ℕ) : ℝ) := by positivity
    nlinarith
  obtain ⟨choice, hmass, havoid⟩ :=
    H.exists_positive_avoiding_finalCollisions m b hm0 hfiber hslot
      x hx0 hx1 hnumeric
  have howner : ∀ j, H.owner (choice j) = j := by
    intro j
    have hfactor : 0 < H.finalUniformProb m j (choice j) := by
      have hnonneg : 0 ≤ H.finalUniformProb m j (choice j) :=
        H.finalUniformProb_nonneg m j (choice j)
      have hne : H.finalUniformProb m j (choice j) ≠ 0 := by
        intro hz
        have hzero :
            WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
              (H.finalUniformProb m) choice = 0 := by
          unfold WeightedEdgeColoring.FiniteCategoricalSelection.categoricalMass
          exact Finset.prod_eq_zero (Finset.mem_univ j) hz
        rw [hzero] at hmass
        exact (lt_irrefl 0) hmass
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    exact (H.finalUniformProb_pos_iff hm0).mp hfactor
  let M : Finset Option := Finset.univ.image choice
  refine ⟨M, ?_, ?_⟩
  · constructor
    · intro o ho p hp hop
      rcases Finset.mem_image.mp ho with ⟨j, _hj, rfl⟩
      rcases Finset.mem_image.mp hp with ⟨k, _hk, rfl⟩
      by_contra hbad
      have hjk : j ≠ k := by
        intro h
        subst k
        exact hop rfl
      rcases lt_or_gt_of_ne hjk with hjk' | hkj'
      · let c : H.FinalCollision := ⟨(choice j, choice k),
          ⟨by simpa [howner j, howner k] using hjk', hbad⟩⟩
        apply havoid c
        simp [finalCollisionEvent, c, howner]
      · let c : H.FinalCollision := ⟨(choice k, choice j),
          ⟨by simpa [howner j, howner k] using hkj', by
            intro hcompat
            exact hbad (H.compatible_symm.mp hcompat)⟩⟩
        apply havoid c
        simp [finalCollisionEvent, c, howner]
    · intro o ho p hp howners
      rcases Finset.mem_image.mp ho with ⟨j, _hj, rfl⟩
      rcases Finset.mem_image.mp hp with ⟨k, _hk, rfl⟩
      have : j = k := by simpa [howner j, howner k] using howners
      simpa [this]
  · intro j
    exact ⟨choice j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩,
      howner j⟩

end Ordered

/-- Order-free public form.  A finite job type can be given a temporary
linear order solely to orient each unordered collision once. -/
theorem exists_covering_partialMatching_finalLLL
    (H : RankThreeOptionSystem Job Slot Option)
    (b : ℕ) (hb : 0 < b)
    (hfiber : ∀ j, (H.fiber j).card = 900 * b)
    (hslot : ∀ s, H.slotDegree s ≤ b) :
    ∃ M : Finset Option,
      H.IsPartialMatching M ∧ ∀ j, H.Covers M j := by
  letI : LinearOrder Job := LinearOrder.lift' (Fintype.equivFin Job)
    (Fintype.equivFin Job).injective
  exact H.exists_covering_partialMatching_finalLLL_of_linearOrder
    b hb hfiber hslot

/-- The application-facing form: surplus options may first be discarded so
that every job fibre has exactly `900*b` members.  Option restriction cannot
increase a slot degree, and the resulting matching lifts back to the original
system with both partial-matching and coverage properties preserved. -/
theorem exists_covering_partialMatching_finalLLL_of_fiber_ge
    (H : RankThreeOptionSystem Job Slot Option)
    (b : ℕ) (hb : 0 < b)
    (hfiber : ∀ j, 900 * b ≤ (H.fiber j).card)
    (hslot : ∀ s, H.slotDegree s ≤ b) :
    ∃ M : Finset Option,
      H.IsPartialMatching M ∧ ∀ j, H.Covers M j := by
  obtain ⟨keep, hregular, hslotKeep, _hjobSlotKeep, _hslotPairKeep⟩ :=
    H.exists_jobRegularizedSystem (900 * b) hfiber
  let R := H.inducedOnOptions keep
  have hslotR : ∀ s, R.slotDegree s ≤ b := fun s ↦
    (hslotKeep s).trans (hslot s)
  obtain ⟨A, hA, hcoverA⟩ :=
    R.exists_covering_partialMatching_finalLLL b hb hregular hslotR
  refine ⟨H.liftKeptOptionSet keep A,
    H.liftKeptOptionSet_isPartialMatching keep hA, ?_⟩
  intro j
  exact (H.covers_liftKeptOptionSet_iff keep A j).mpr (hcoverA j)

end WeightedEdgeColoring.RankThreeOptionSystem
