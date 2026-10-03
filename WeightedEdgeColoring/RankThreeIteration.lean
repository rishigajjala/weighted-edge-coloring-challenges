import WeightedEdgeColoring.RankThreeFrontierGrowth

namespace WeightedEdgeColoring

universe u v w

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-!
# Iterating the augmenting frontier

An augmenting step has two outcomes.  Either the exchange pool contains more
compatible options than were deleted, in which case the current partial
matching grows, or no such exchange exists.  In the second case the frontier
counting lemma produces many untouched blockers.  While the degree budget is
large enough, a subfamily of those blockers can be added to the deleted set
so that its cardinality doubles exactly.

For a maximum partial matching the first outcome is impossible.  Iterating
the second outcome gives a finite exponential-growth certificate inside the
fixed matching, and therefore a contradiction as soon as `2^n * |P| > |M|`.
-/

/-- A replacement matching in the exchange pool that is larger than the
deleted set. -/
def HasAugmentingExchange (M P : Finset Option) : Prop :=
  ∃ Q : Finset Option,
    Q ⊆ H.exchangePool M P ∧ H.IsPartialMatching Q ∧ P.card < Q.card

/-- An augmenting exchange really produces a larger partial matching. -/
theorem exists_larger_partialMatching_of_hasAugmentingExchange
    {M P : Finset Option} (hM : H.IsPartialMatching M) (hP : P ⊆ M)
    (haug : H.HasAugmentingExchange M P) :
    ∃ M' : Finset Option,
      H.IsPartialMatching M' ∧ M.card < M'.card := by
  obtain ⟨Q, hQsub, hQ, hcard⟩ := haug
  have hcompat : ∀ q ∈ Q, ∀ x ∈ M \ P, H.Compatible q x := by
    intro q hq x hx
    exact (H.mem_exchangePool.mp (hQsub hq)).1 x hx
  have howner : ∀ q ∈ Q, ∀ x ∈ M \ P,
      H.owner q ≠ H.owner x := by
    intro q hq x hx
    exact (H.mem_exchangePool.mp (hQsub hq)).2 x hx
  have hexchange : H.IsPartialMatching ((M \ P) ∪ Q) :=
    hM.exchange_set H hQ hcompat howner
  have hdisj : Disjoint (M \ P) Q :=
    H.disjoint_sdiff_of_cross_owner howner
  refine ⟨(M \ P) ∪ Q, hexchange, ?_⟩
  rw [Finset.card_union_of_disjoint hdisj]
  have hdecomp : (M \ P).card + P.card = M.card :=
    Finset.card_sdiff_add_card_eq_card hP
  omega

/-- A maximum partial matching admits no augmenting exchange at any deleted
subset. -/
theorem maximum_partialMatching_no_augmentingExchange
    {M P : Finset Option} (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) :
    ¬ H.HasAugmentingExchange M P := by
  intro haug
  obtain ⟨M', hM', hlarge⟩ :=
    H.exists_larger_partialMatching_of_hasAugmentingExchange hM hP haug
  exact (Nat.not_lt_of_ge (hmax M' hM')) hlarge

/-- Every actual blocker belongs to the ambient selected set. -/
theorem blockersOf_subset (j : Job) (N : Finset Option) :
    H.blockersOf j N ⊆ N := by
  intro p hp
  exact (H.mem_blockersOf.mp hp).1

/-- If no augmenting exchange exists, some frontier job has few eligible
options.  This is the non-maximum version of
`exists_frontier_job_with_small_exchangePool`; the no-exchange assumption is
exactly the part of maximum cardinality used in its proof. -/
theorem exists_frontier_job_with_small_exchangePool_of_noAugment
    {M P : Finset Option}
    (hM : H.IsPartialMatching M) (hP : P ⊆ M)
    (root : Job) (hroot : ¬ H.Covers M root)
    (lambda : ℕ)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda)
    (hnoaug : ¬ H.HasAugmentingExchange M P) :
    ∃ j ∈ insert root (P.image H.owner),
      (H.fiber j ∩ H.exchangePool M P).card ≤
        P.card * (2 * lambda) := by
  obtain ⟨Q, hQsub, hQ, hmaxQ⟩ :=
    H.exists_maximum_partialMatching_subset (H.exchangePool M P)
  have hQcard : Q.card ≤ P.card := by
    by_contra hnot
    apply hnoaug
    exact ⟨Q, hQsub, hQ, Nat.lt_of_not_ge hnot⟩
  by_contra hnone
  push Not at hnone
  have hcover : ∀ j ∈ insert root (P.image H.owner), H.Covers Q j := by
    intro j hj
    by_contra huncovered
    have hsmallQ := H.maximum_partialMatching_subset_fiber_card_le
      hQsub hQ hmaxQ j huncovered lambda (hcodeg j)
    have hsmallP :
        (H.fiber j ∩ H.exchangePool M P).card ≤
          P.card * (2 * lambda) :=
      hsmallQ.trans (Nat.mul_le_mul_right (2 * lambda) hQcard)
    exact (Nat.not_lt_of_ge hsmallP) (hnone j hj)
  have hfrontle : (insert root (P.image H.owner)).card ≤ Q.card :=
    H.card_jobs_le_of_covers hQ hcover
  have hinj : Set.InjOn H.owner (P : Set Option) := by
    intro p hp q hq heq
    exact hM.2 (hP hp) (hP hq) heq
  have himagecard : (P.image H.owner).card = P.card :=
    Finset.card_image_iff.mpr hinj
  have hrootnot : root ∉ P.image H.owner := by
    intro hr
    obtain ⟨p, hp, howner⟩ := Finset.mem_image.mp hr
    exact hroot ⟨p, hP hp, howner⟩
  rw [Finset.card_insert_of_notMem hrootnot, himagecard] at hfrontle
  omega

/-- Without an augmenting exchange, some frontier job forces the same
distinct-blocker lower bound as in the maximum case. -/
theorem exists_frontier_job_blocker_lower_bound_of_noAugment
    {M P : Finset Option}
    (hM : H.IsPartialMatching M) (hP : P ⊆ M)
    (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda)
    (hnoaug : ¬ H.HasAugmentingExchange M P) :
    ∃ j ∈ insert root (P.image H.owner),
      m - (2 * lambda) * P.card ≤
        (2 * lambda) * (H.blockersOf j (M \ P)).card := by
  obtain ⟨j, hj, heligible⟩ :=
    H.exists_frontier_job_with_small_exchangePool_of_noAugment
      hM hP root hroot lambda hcodeg hnoaug
  have huncovered : ¬ H.Covers (M \ P) j :=
    H.frontier_not_covered_by_sdiff hM hP root hroot hj
  have hsplit := H.card_fiber_inter_exchangePool_add_blocked j huncovered
  have hblockedLower : m - P.card * (2 * lambda) ≤
      (H.blockedBySet j (M \ P)).card := by
    have hdeg := hdegree j
    omega
  have hblockedUpper : (H.blockedBySet j (M \ P)).card ≤
      (H.blockersOf j (M \ P)).card * (2 * lambda) :=
    H.card_blockedBySet_le_two_mul_blockers
      j (M \ P) lambda (hcodeg j)
  refine ⟨j, hj, ?_⟩
  simpa [Nat.mul_comm] using hblockedLower.trans hblockedUpper

/-- One exact doubling step.  Either an augmenting exchange exists, or a
frontier job has enough untouched blockers to choose a set `C` of size
exactly `P.card`.  Then `P ∪ C` stays inside `M` and has twice the size.

The numerical condition says that the common fibre lower bound has room for
two copies of the current `2*lambda` blocking budget. -/
theorem augmentingExchange_or_exists_doubling_extension
    {M P : Finset Option}
    (hM : H.IsPartialMatching M) (hP : P ⊆ M)
    (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ) (hlambda : 0 < lambda)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda)
    (hbudget : 2 * ((2 * lambda) * P.card) ≤ m) :
    H.HasAugmentingExchange M P ∨
      ∃ j ∈ insert root (P.image H.owner), ∃ C : Finset Option,
        C ⊆ H.blockersOf j (M \ P) ∧
        C.card = P.card ∧ P ⊆ P ∪ C ∧ P ∪ C ⊆ M ∧
        (P ∪ C).card = 2 * P.card := by
  by_cases haug : H.HasAugmentingExchange M P
  · exact Or.inl haug
  · right
    obtain ⟨j, hj, hbound⟩ :=
      H.exists_frontier_job_blocker_lower_bound_of_noAugment
        hM hP root hroot m lambda hdegree hcodeg haug
    have hdpos : 0 < 2 * lambda := by omega
    have hhalf : (2 * lambda) * P.card ≤
        m - (2 * lambda) * P.card := by omega
    have hmul : (2 * lambda) * P.card ≤
        (2 * lambda) * (H.blockersOf j (M \ P)).card :=
      hhalf.trans hbound
    have hmany : P.card ≤ (H.blockersOf j (M \ P)).card :=
      Nat.le_of_mul_le_mul_left hmul hdpos
    obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hmany
    have hCrest : C ⊆ M \ P :=
      fun _q hq ↦ H.blockersOf_subset j (M \ P) (hCsub hq)
    have hdisj : Disjoint P C := by
      rw [Finset.disjoint_left]
      intro q hqP hqC
      exact (Finset.mem_sdiff.mp (hCrest hqC)).2 hqP
    refine ⟨j, hj, C, hCsub, hCcard, Finset.subset_union_left, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_union.mp hq with hqP | hqC
      · exact hP hqP
      · exact (Finset.mem_sdiff.mp (hCrest hqC)).1
    · rw [Finset.card_union_of_disjoint hdisj, hCcard]
      omega

/-- In a maximum partial matching only the doubling branch remains. -/
theorem maximum_partialMatching_exists_doubling_extension
    {M P : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ) (hlambda : 0 < lambda)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda)
    (hbudget : 2 * ((2 * lambda) * P.card) ≤ m) :
    ∃ P' : Finset Option,
      P ⊆ P' ∧ P' ⊆ M ∧ P'.card = 2 * P.card := by
  rcases H.augmentingExchange_or_exists_doubling_extension
      hM hP root hroot m lambda hlambda hdegree hcodeg hbudget with
    haug | ⟨j, hj, C, hCsub, hCcard, hPP, hPM, hcard⟩
  · exact False.elim
      (H.maximum_partialMatching_no_augmentingExchange hM hmax hP haug)
  · exact ⟨P ∪ C, hPP, hPM, hcard⟩

/-- Iterated doubling inside a maximum partial matching.  If the degree
budget supports `n` rounds, a deleted superset of `P` with exactly
`2^n * P.card` options exists inside `M`. -/
theorem maximum_partialMatching_exists_iterated_doubling
    {M P : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ) (hlambda : 0 < lambda)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda)
    (n : ℕ) (hbudget : (2 * lambda) * 2 ^ n * P.card ≤ m) :
    ∃ R : Finset Option,
      P ⊆ R ∧ R ⊆ M ∧ R.card = 2 ^ n * P.card := by
  induction n with
  | zero =>
      exact ⟨P, Finset.Subset.rfl, hP, by simp⟩
  | succ n ih =>
      have hpow : 2 ^ n ≤ 2 ^ (n + 1) := by
        rw [pow_succ]
        omega
      have hbudgetN : (2 * lambda) * 2 ^ n * P.card ≤ m := by
        exact (Nat.mul_le_mul_right P.card
          (Nat.mul_le_mul_left (2 * lambda) hpow)).trans hbudget
      obtain ⟨R, hPR, hRM, hRcard⟩ := ih hbudgetN
      have hstepBudget : 2 * ((2 * lambda) * R.card) ≤ m := by
        rw [hRcard]
        simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          using hbudget
      obtain ⟨R', hRR', hR'M, hR'card⟩ :=
        H.maximum_partialMatching_exists_doubling_extension
          hM hmax hRM root hroot m lambda hlambda
          hdegree hcodeg hstepBudget
      refine ⟨R', hPR.trans hRR', hR'M, ?_⟩
      rw [hR'card, hRcard]
      simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]

/-- A maximum partial matching missing a positive-degree root has an actual
selected blocker of that root.  This supplies a one-element seed for the
doubling iteration. -/
theorem maximum_partialMatching_exists_root_blocker
    {M : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (root : Job) (hroot : ¬ H.Covers M root)
    (m : ℕ) (hm : 0 < m)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card) :
    ∃ p ∈ M, p ∈ H.blockersOf root M := by
  have hfibpos : 0 < (H.fiber root).card :=
    hm.trans_le (hdegree root)
  obtain ⟨q, hqfiber⟩ := Finset.card_pos.mp hfibpos
  have hqblocked :=
    H.maximum_partialMatching_fiber_subset_blocked
      hM hmax root hroot hqfiber
  obtain ⟨p, hpM, hqp⟩ := Finset.mem_biUnion.mp hqblocked
  exact ⟨p, hpM, H.mem_blockersOf.mpr ⟨hpM, ⟨q, hqp⟩⟩⟩

/-- Root-seeded iteration.  Starting only from an uncovered root, `n`
supported rounds produce `2^n` distinct selected options inside `M`. -/
theorem maximum_partialMatching_exists_root_seeded_doubling
    {M : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ) (hm : 0 < m) (hlambda : 0 < lambda)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda)
    (n : ℕ) (hbudget : (2 * lambda) * 2 ^ n ≤ m) :
    ∃ R : Finset Option, R ⊆ M ∧ R.card = 2 ^ n := by
  obtain ⟨p, hpM, _hpblock⟩ :=
    H.maximum_partialMatching_exists_root_blocker
      hM hmax root hroot m hm hdegree
  have hseed : ({p} : Finset Option) ⊆ M := by simpa
  have hbudget' : (2 * lambda) * 2 ^ n * ({p} : Finset Option).card ≤ m := by
    simpa using hbudget
  obtain ⟨R, _hseedR, hRM, hRcard⟩ :=
    H.maximum_partialMatching_exists_iterated_doubling
      hM hmax hseed root hroot m lambda hlambda
      hdegree hcodeg n hbudget'
  exact ⟨R, hRM, by simpa using hRcard⟩

/-- Capacity consequence of iteration: every supported doubling depth must
fit inside the fixed maximum matching. -/
theorem pow_mul_card_le_of_maximum_partialMatching
    {M P : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ) (hlambda : 0 < lambda)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda)
    (n : ℕ) (hbudget : (2 * lambda) * 2 ^ n * P.card ≤ m) :
    2 ^ n * P.card ≤ M.card := by
  obtain ⟨R, _hPR, hRM, hRcard⟩ :=
    H.maximum_partialMatching_exists_iterated_doubling
      hM hmax hP root hroot m lambda hlambda
      hdegree hcodeg n hbudget
  rw [← hRcard]
  exact Finset.card_le_card hRM

/-- Finite contradiction form.  A maximum matching missing `root` cannot
simultaneously support `n` doubling rounds and have fewer than
`2^n * P.card` selected options. -/
theorem maximum_partialMatching_no_overflowing_doubling
    {M P : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (hP : P ⊆ M) (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ) (hlambda : 0 < lambda)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda)
    (n : ℕ) (hbudget : (2 * lambda) * 2 ^ n * P.card ≤ m)
    (hoverflow : M.card < 2 ^ n * P.card) :
    False := by
  exact (Nat.not_le_of_gt hoverflow)
    (H.pow_mul_card_le_of_maximum_partialMatching
      hM hmax hP root hroot m lambda hlambda
      hdegree hcodeg n hbudget)

/-- Root-seeded capacity contradiction.  If the local degree budget supports
`n` doublings but `M` has fewer than `2^n` options, a maximum partial
matching cannot miss the root. -/
theorem maximum_partialMatching_no_root_seeded_overflow
    {M : Finset Option}
    (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option,
      H.IsPartialMatching M' → M'.card ≤ M.card)
    (root : Job) (hroot : ¬ H.Covers M root)
    (m lambda : ℕ) (hm : 0 < m) (hlambda : 0 < lambda)
    (hdegree : ∀ j : Job, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j : Job, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda)
    (n : ℕ) (hbudget : (2 * lambda) * 2 ^ n ≤ m)
    (hoverflow : M.card < 2 ^ n) :
    False := by
  obtain ⟨R, hRM, hRcard⟩ :=
    H.maximum_partialMatching_exists_root_seeded_doubling
      hM hmax root hroot m lambda hm hlambda
      hdegree hcodeg n hbudget
  have hle : 2 ^ n ≤ M.card := by
    rw [← hRcard]
    exact Finset.card_le_card hRM
  exact (Nat.not_le_of_gt hoverflow) hle

/-! ## Slot support of an iterated deleted set -/

/-- All slots used by options of `P`. -/
def slotSupport (P : Finset Option) : Finset Slot :=
  P.biUnion H.slots

/-- Rank three gives the elementary support bound `|slots(P)| ≤ 2|P|`. -/
theorem card_slotSupport_le_two_mul (P : Finset Option) :
    (H.slotSupport P).card ≤ 2 * P.card := by
  calc
    (H.slotSupport P).card ≤ ∑ p ∈ P, (H.slots p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, 2 := by
      exact Finset.sum_le_sum fun p _hp ↦ H.slots_card_le_two p
    _ = 2 * P.card := by simp [Nat.mul_comm]

/-- Pair-counting consequence for the support reached by any iteration:
options lying wholly on two reached slots are controlled by the sharp
unordered-pair bound. -/
theorem card_optionsUsingTwoOf_slotSupport_le
    (P : Finset Option) (lambda : ℕ)
    (hpair : ∀ s ∈ H.slotSupport P, ∀ t ∈ H.slotSupport P, s ≠ t →
      H.slotPairCodegree s t ≤ lambda) :
    (H.optionsUsingTwoOf (H.slotSupport P)).card ≤
      Nat.choose (H.slotSupport P).card 2 * lambda := by
  exact H.card_optionsUsingTwoOf_le_choose_mul
    (H.slotSupport P) lambda hpair

end RankThreeOptionSystem

end WeightedEdgeColoring
