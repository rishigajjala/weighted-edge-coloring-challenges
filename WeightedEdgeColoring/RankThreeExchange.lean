import WeightedEdgeColoring.RankThreeAugmentation

namespace WeightedEdgeColoring

universe u v w

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-!
# Arbitrary-depth exchange certificates

The one-for-two obstruction in `RankThreeAugmentation` is the first level of
an augmenting tree.  Here we package all finite levels at once.  Remove an
arbitrary set `P` from a partial matching `M`.  Any partial matching `Q` whose
options are compatible with the untouched part `M \ P`, and whose owners are
not represented there, can replace `P`.  Consequently, if `M` has maximum
cardinality, every such `Q` has cardinality at most `P.card`.

This does not by itself prove the fixed-slack matching theorem: one still has
to use low codegrees to show that a sufficiently large replacement matching
exists.  It does, however, give the exact arbitrary-depth obstruction that
such a counting or augmenting-tree argument must contradict.
-/

/-- Two partial matchings can be united when every cross-pair has disjoint
slots and different owners.  The owner hypothesis also forces the two sets
to be disjoint, so no separate disjointness assumption is needed. -/
theorem IsPartialMatching.union_of_cross
    {A B : Finset Option}
    (hA : H.IsPartialMatching A) (hB : H.IsPartialMatching B)
    (hcompat : ∀ a ∈ A, ∀ b ∈ B, H.Compatible a b)
    (howner : ∀ a ∈ A, ∀ b ∈ B, H.owner a ≠ H.owner b) :
    H.IsPartialMatching (A ∪ B) := by
  constructor
  · intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hxA | hxB <;>
      rcases Finset.mem_union.mp hy with hyA | hyB
    · exact hA.1 hxA hyA hxy
    · exact hcompat x hxA y hyB
    · exact H.compatible_symm.mpr (hcompat y hyA x hxB)
    · exact hB.1 hxB hyB hxy
  · intro x hx y hy heq
    rcases Finset.mem_union.mp hx with hxA | hxB <;>
      rcases Finset.mem_union.mp hy with hyA | hyB
    · exact hA.2 hxA hyA heq
    · exact False.elim (howner x hxA y hyB heq)
    · exact False.elim (howner y hyA x hxB heq.symm)
    · exact hB.2 hxB hyB heq

/-- Replacing a set `P` of selected options by a compatible partial matching
`Q` preserves the partial-matching property. -/
theorem IsPartialMatching.exchange_set
    {M P Q : Finset Option}
    (hM : H.IsPartialMatching M) (hQ : H.IsPartialMatching Q)
    (hcompat : ∀ q ∈ Q, ∀ x ∈ M \ P, H.Compatible q x)
    (howner : ∀ q ∈ Q, ∀ x ∈ M \ P,
      H.owner q ≠ H.owner x) :
    H.IsPartialMatching ((M \ P) ∪ Q) := by
  have hrest : H.IsPartialMatching (M \ P) :=
    hM.mono H (Finset.sdiff_subset)
  apply hrest.union_of_cross H hQ
  · intro x hx q hq
    exact H.compatible_symm.mpr (hcompat q hq x hx)
  · intro x hx q hq
    exact Ne.symm (howner q hq x hx)

/-- The replacement set is automatically disjoint from the untouched part:
an option cannot have an owner different from itself. -/
theorem disjoint_sdiff_of_cross_owner
    {M P Q : Finset Option}
    (howner : ∀ q ∈ Q, ∀ x ∈ M \ P,
      H.owner q ≠ H.owner x) :
    Disjoint (M \ P) Q := by
  rw [Finset.disjoint_left]
  intro x hxrest hxQ
  exact howner x hxQ x hxrest rfl

/-- Arbitrary-depth augmentation obstruction.  In a maximum partial
matching, replacing `P ⊆ M` can never produce more than `P.card` mutually
compatible options whose owners are absent from the untouched matching.

For `P.card = 1` this contains the one-for-two obstruction.  For
`P.card = 2` it rules out every two-for-three exchange, and similarly at all
larger depths. -/
theorem maximum_partialMatching_exchange_card_le
    {M P Q : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (hQ : H.IsPartialMatching Q)
    (hcompat : ∀ q ∈ Q, ∀ x ∈ M \ P, H.Compatible q x)
    (howner : ∀ q ∈ Q, ∀ x ∈ M \ P,
      H.owner q ≠ H.owner x) :
    Q.card ≤ P.card := by
  have hexchange : H.IsPartialMatching ((M \ P) ∪ Q) :=
    hM.exchange_set H hQ hcompat howner
  have hdisj : Disjoint (M \ P) Q :=
    H.disjoint_sdiff_of_cross_owner howner
  have hlarge := hmax ((M \ P) ∪ Q) hexchange
  rw [Finset.card_union_of_disjoint hdisj] at hlarge
  have hdecomp : (M \ P).card + P.card = M.card :=
    Finset.card_sdiff_add_card_eq_card hP
  omega

/-- Options that are locally eligible after deleting all of `P`: they use
no slot and repeat no owner from the untouched part of the matching. -/
def exchangePool (M P : Finset Option) : Finset Option :=
  Finset.univ.filter fun q ↦
    (∀ x ∈ M \ P, H.Compatible q x) ∧
      (∀ x ∈ M \ P, H.owner q ≠ H.owner x)

@[simp] theorem mem_exchangePool {M P : Finset Option} {q : Option} :
    q ∈ H.exchangePool M P ↔
      (∀ x ∈ M \ P, H.Compatible q x) ∧
        (∀ x ∈ M \ P, H.owner q ≠ H.owner x) := by
  simp [exchangePool]

/-- Counting form of the arbitrary-depth certificate: the matching number
of the whole local exchange pool is at most the number of deleted options.
This is the form useful for a later low-codegree expansion argument. -/
theorem maximum_partialMatching_exchangePool_rank_le
    {M P Q : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (hQsub : Q ⊆ H.exchangePool M P)
    (hQ : H.IsPartialMatching Q) :
    Q.card ≤ P.card := by
  apply H.maximum_partialMatching_exchange_card_le hM hmax hP hQ
  · intro q hq x hx
    exact (H.mem_exchangePool.mp (hQsub hq)).1 x hx
  · intro q hq x hx
    exact (H.mem_exchangePool.mp (hQsub hq)).2 x hx

/-- Equivalently, every subset of the exchange pool with one more element
than `P` contains either a slot conflict or an owner collision. -/
theorem maximum_partialMatching_no_large_exchangePool_matching
    {M P Q : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (hQsub : Q ⊆ H.exchangePool M P)
    (hcard : P.card < Q.card) :
    ¬ H.IsPartialMatching Q := by
  intro hQ
  have hle := H.maximum_partialMatching_exchangePool_rank_le
    hM hmax hP hQsub hQ
  exact (Nat.not_le_of_gt hcard) hle

/-! ## A small local certificate inside every exchange pool -/

/-- Every finite set of options contains a maximum-cardinality partial
matching.  This restricted form lets an augmenting search work inside one
exchange pool rather than in the full option system. -/
theorem exists_maximum_partialMatching_subset (S : Finset Option) :
    ∃ Q : Finset Option,
      Q ⊆ S ∧ H.IsPartialMatching Q ∧
        ∀ R : Finset Option,
          R ⊆ S → H.IsPartialMatching R → R.card ≤ Q.card := by
  classical
  let candidates : Finset (Finset Option) :=
    S.powerset.filter H.IsPartialMatching
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, H.empty_isPartialMatching]
  obtain ⟨Q, hQcand, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hnonempty
  have hQdata : Q ⊆ S ∧ H.IsPartialMatching Q := by
    simpa [candidates] using hQcand
  refine ⟨Q, hQdata.1, hQdata.2, ?_⟩
  intro R hRS hR
  apply hmax R
  simp [candidates, hRS, hR]

/-- A maximum partial matching inside `S` blocks every option in `S` whose
owner it does not cover.  This is the restricted analogue of the global
maximality certificate in `RankThreeMatching`. -/
theorem maximum_partialMatching_subset_fiber_blocked
    {S Q : Finset Option}
    (hQsub : Q ⊆ S) (hQ : H.IsPartialMatching Q)
    (hmax : ∀ R : Finset Option,
      R ⊆ S → H.IsPartialMatching R → R.card ≤ Q.card)
    (j : Job) (huncovered : ¬ H.Covers Q j) :
    H.fiber j ∩ S ⊆ H.blockedBySet j Q := by
  intro q hq
  have hqfiber : q ∈ H.fiber j := (Finset.mem_inter.mp hq).1
  have hqS : q ∈ S := (Finset.mem_inter.mp hq).2
  by_contra hqblocked
  have hqowner : H.owner q = j := H.mem_fiber.mp hqfiber
  have hqnotQ : q ∉ Q := by
    intro hqQ
    exact huncovered ⟨q, hqQ, hqowner⟩
  have hcompat : ∀ p ∈ Q, H.Compatible q p := by
    intro p hp
    by_contra hconflict
    apply hqblocked
    apply Finset.mem_biUnion.mpr
    exact ⟨p, hp, Finset.mem_filter.mpr ⟨hqfiber, hconflict⟩⟩
  have howner : ∀ p ∈ Q, H.owner p ≠ H.owner q := by
    intro p hp heq
    apply huncovered
    exact ⟨p, hp, heq.trans hqowner⟩
  have hins : H.IsPartialMatching (insert q Q) :=
    hQ.insert H q hqnotQ hcompat howner
  have hle : (insert q Q).card ≤ Q.card :=
    hmax (insert q Q) (Finset.insert_subset hqS hQsub) hins
  rw [Finset.card_insert_of_notMem hqnotQ] at hle
  exact (Nat.not_succ_le_self Q.card) hle

/-- Quantitative restricted certificate.  If one job is not represented by
a maximum partial matching `Q` inside `S`, then at most
`Q.card * (2 * lambda)` options of that job lie in `S`. -/
theorem maximum_partialMatching_subset_fiber_card_le
    {S Q : Finset Option}
    (hQsub : Q ⊆ S) (hQ : H.IsPartialMatching Q)
    (hmax : ∀ R : Finset Option,
      R ⊆ S → H.IsPartialMatching R → R.card ≤ Q.card)
    (j : Job) (huncovered : ¬ H.Covers Q j) (lambda : ℕ)
    (hcodeg : ∀ s : Slot, H.jobSlotCodegree j s ≤ lambda) :
    (H.fiber j ∩ S).card ≤ Q.card * (2 * lambda) := by
  calc
    (H.fiber j ∩ S).card ≤ (H.blockedBySet j Q).card :=
      Finset.card_le_card
        (H.maximum_partialMatching_subset_fiber_blocked
          hQsub hQ hmax j huncovered)
    _ ≤ Q.card * (2 * lambda) := by
      apply H.card_blockedBySet_le
      intro p _hp
      apply H.card_blockedBy_le_two_mul j p lambda
      intro s _hs
      exact hcodeg s

/-- For a job absent from the untouched matching, the exchange pool has an
exact description: its eligible options are precisely the fibre options not
slot-blocked by `M \ P`.  Thus the owner condition in `exchangePool` costs
nothing for such a job. -/
theorem fiber_inter_exchangePool_eq_sdiff_blockedBySet
    {M P : Finset Option} (j : Job)
    (huncovered : ¬ H.Covers (M \ P) j) :
    H.fiber j ∩ H.exchangePool M P =
      H.fiber j \ H.blockedBySet j (M \ P) := by
  ext q
  constructor
  · intro hq
    have hqfiber : q ∈ H.fiber j := (Finset.mem_inter.mp hq).1
    have hqpool := H.mem_exchangePool.mp (Finset.mem_inter.mp hq).2
    apply Finset.mem_sdiff.mpr
    refine ⟨hqfiber, ?_⟩
    intro hqblocked
    obtain ⟨p, hp, hconflict⟩ := Finset.mem_biUnion.mp hqblocked
    exact (Finset.mem_filter.mp hconflict).2 (hqpool.1 p hp)
  · intro hq
    have hq' := Finset.mem_sdiff.mp hq
    have hqowner : H.owner q = j := H.mem_fiber.mp hq'.1
    apply Finset.mem_inter.mpr
    refine ⟨hq'.1, H.mem_exchangePool.mpr ⟨?_, ?_⟩⟩
    · intro p hp
      by_contra hconflict
      apply hq'.2
      apply Finset.mem_biUnion.mpr
      exact ⟨p, hp, Finset.mem_filter.mpr ⟨hq'.1, hconflict⟩⟩
    · intro p hp heq
      apply huncovered
      exact ⟨p, hp, heq.symm.trans hqowner⟩

/-- Exact cardinal decomposition of a job fibre into locally eligible and
blocked options after an arbitrary deletion. -/
theorem card_fiber_inter_exchangePool_add_blocked
    {M P : Finset Option} (j : Job)
    (huncovered : ¬ H.Covers (M \ P) j) :
    (H.fiber j ∩ H.exchangePool M P).card +
        (H.blockedBySet j (M \ P)).card = (H.fiber j).card := by
  rw [H.fiber_inter_exchangePool_eq_sdiff_blockedBySet j huncovered]
  exact Finset.card_sdiff_add_card_eq_card
    (H.blockedBySet_subset_fiber j (M \ P))

/-- A lower-bound form of the decomposition.  At most two job-slot
codegree blocks are paid for each untouched selected option. -/
theorem fiber_card_le_exchangePool_add_two_mul
    {M P : Finset Option} (j : Job)
    (huncovered : ¬ H.Covers (M \ P) j) (lambda : ℕ)
    (hcodeg : ∀ s : Slot, H.jobSlotCodegree j s ≤ lambda) :
    (H.fiber j).card ≤
      (H.fiber j ∩ H.exchangePool M P).card +
        (M \ P).card * (2 * lambda) := by
  have hblocked : (H.blockedBySet j (M \ P)).card ≤
      (M \ P).card * (2 * lambda) := by
    apply H.card_blockedBySet_le
    intro p _hp
    apply H.card_blockedBy_le_two_mul j p lambda
    intro s _hs
    exact hcodeg s
  have hsplit := H.card_fiber_inter_exchangePool_add_blocked j huncovered
  omega

/-- The all-depth expansion certificate, in a form ready for iteration.
After deleting `P` from a maximum matching `M`, the exchange pool has a
partial matching `Q` of size at most `P.card`.  Every job not represented in
`Q` contributes at most `P.card * (2 * lambda)` locally eligible options. -/
theorem exists_small_exchange_certificate
    {M P : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmaxM : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (lambda : ℕ)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda) :
    ∃ Q : Finset Option,
      Q ⊆ H.exchangePool M P ∧ H.IsPartialMatching Q ∧
      Q.card ≤ P.card ∧
      ∀ j : Job, ¬ H.Covers Q j →
        (H.fiber j ∩ H.exchangePool M P).card ≤
          P.card * (2 * lambda) := by
  obtain ⟨Q, hQsub, hQ, hmaxQ⟩ :=
    H.exists_maximum_partialMatching_subset (H.exchangePool M P)
  have hQcard : Q.card ≤ P.card :=
    H.maximum_partialMatching_exchangePool_rank_le
      hM hmaxM hP hQsub hQ
  refine ⟨Q, hQsub, hQ, hQcard, ?_⟩
  intro j huncovered
  calc
    (H.fiber j ∩ H.exchangePool M P).card ≤
        Q.card * (2 * lambda) :=
      H.maximum_partialMatching_subset_fiber_card_le
        hQsub hQ hmaxQ j huncovered lambda (hcodeg j)
    _ ≤ P.card * (2 * lambda) :=
      Nat.mul_le_mul_right (2 * lambda) hQcard

/-- A partial matching that covers every job in `J` must have at least
`J.card` options.  This is the elementary owner-counting bridge used in the
augmenting-layer criterion below. -/
theorem card_jobs_le_of_covers
    {Q : Finset Option} {J : Finset Job}
    (hQ : H.IsPartialMatching Q)
    (hcover : ∀ j ∈ J, H.Covers Q j) :
    J.card ≤ Q.card := by
  have hsub : J ⊆ Q.image H.owner := by
    intro j hj
    obtain ⟨q, hq, howner⟩ := hcover j hj
    exact Finset.mem_image.mpr ⟨q, hq, howner⟩
  calc
    J.card ≤ (Q.image H.owner).card := Finset.card_le_card hsub
    _ = Q.card := Finset.card_image_iff.mpr hQ.2

/-- General augmenting-layer obstruction.  Let `M` be maximum but miss the
root job `j`, and delete any `P ⊆ M`.  The natural frontier consists of the
root together with the owners of `P`, hence has exactly `P.card + 1` jobs.
It is impossible for every frontier job to retain more than
`P.card * (2 * lambda)` eligible options in the exchange pool.

Indeed, the local maximum matching supplied by
`exists_small_exchange_certificate` would then cover the entire frontier,
so it would have at least `P.card + 1` options, while the arbitrary exchange
bound gives it at most `P.card`.  This is the finite counting contradiction
that an iterative low-codegree proof must arrange. -/
theorem maximum_partialMatching_not_all_frontier_dense
    {M P : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmaxM : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (j : Job) (huncovered : ¬ H.Covers M j)
    (lambda : ℕ)
    (hcodeg : ∀ k : Job, ∀ s : Slot,
      H.jobSlotCodegree k s ≤ lambda) :
    ¬ (∀ k ∈ insert j (P.image H.owner),
      P.card * (2 * lambda) <
        (H.fiber k ∩ H.exchangePool M P).card) := by
  intro hdense
  obtain ⟨Q, hQsub, hQ, hQcard, hsmall⟩ :=
    H.exists_small_exchange_certificate hM hmaxM hP lambda hcodeg
  have hcover : ∀ k ∈ insert j (P.image H.owner), H.Covers Q k := by
    intro k hk
    by_contra hnot
    exact (Nat.not_lt_of_ge (hsmall k hnot)) (hdense k hk)
  have hfrontle : (insert j (P.image H.owner)).card ≤ Q.card :=
    H.card_jobs_le_of_covers hQ hcover
  have hinj : Set.InjOn H.owner (P : Set Option) := by
    intro p hp q hq heq
    exact hM.2 (hP hp) (hP hq) heq
  have himagecard : (P.image H.owner).card = P.card :=
    Finset.card_image_iff.mpr hinj
  have hjnot : j ∉ P.image H.owner := by
    intro hj
    obtain ⟨p, hp, howner⟩ := Finset.mem_image.mp hj
    apply huncovered
    exact ⟨p, hP hp, howner⟩
  rw [Finset.card_insert_of_notMem hjnot, himagecard] at hfrontle
  omega

end RankThreeOptionSystem

end WeightedEdgeColoring
