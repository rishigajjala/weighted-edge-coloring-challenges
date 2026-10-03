import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Powerset

namespace WeightedEdgeColoring

/-!
# Finite rank-three option systems

This file isolates the purely finite matching problem used when large edges
are rounded.  An option has one owner (the job that it completes) and uses at
most two slots.  Repeated copies of the same geometric option are represented
by distinct values of `Option`.

The main theorem gives an elementary greedy construction and a precise
obstruction certificate: after some jobs have been chosen, a new job can
fail only if the chosen options cover its whole option fibre.
-/

universe u v w

/-- A finite family of options.  Every option belongs to one job and uses at
most two slots. -/
structure RankThreeOptionSystem (Job : Type u) (Slot : Type v)
    (Option : Type w) [Fintype Job] [Fintype Slot] [Fintype Option]
    [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] where
  owner : Option → Job
  slots : Option → Finset Slot
  slots_card_le_two : ∀ o, (slots o).card ≤ 2

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- The listed copies of options belonging to one job. -/
def fiber (j : Job) : Finset Option :=
  Finset.univ.filter fun o ↦ H.owner o = j

@[simp] theorem mem_fiber {j : Job} {o : Option} :
    o ∈ H.fiber j ↔ H.owner o = j := by
  simp [fiber]

/-- Two options are compatible when they use disjoint slots. -/
def Compatible (o p : Option) : Prop :=
  Disjoint (H.slots o) (H.slots p)

instance compatibleDecidable (o p : Option) : Decidable (H.Compatible o p) :=
  by
    unfold Compatible
    infer_instance

theorem compatible_symm {o p : Option} :
    H.Compatible o p ↔ H.Compatible p o := by
  exact disjoint_comm

instance compatibleSymm : Std.Symm H.Compatible where
  symm _ _ h := H.compatible_symm.mp h

/-- Options of `j` blocked by one already chosen option `p`. -/
def blockedBy (j : Job) (p : Option) : Finset Option :=
  (H.fiber j).filter fun o ↦ ¬ H.Compatible o p

@[simp] theorem mem_blockedBy {j : Job} {o p : Option} :
    o ∈ H.blockedBy j p ↔ H.owner o = j ∧ ¬ H.Compatible o p := by
  simp [blockedBy]

/-- Options of `j` blocked by at least one option in `M`. -/
def blockedBySet (j : Job) (M : Finset Option) : Finset Option :=
  M.biUnion (H.blockedBy j)

theorem blockedBySet_subset_fiber (j : Job) (M : Finset Option) :
    H.blockedBySet j M ⊆ H.fiber j := by
  intro o ho
  rcases Finset.mem_biUnion.mp ho with ⟨p, hp, hop⟩
  exact (Finset.mem_filter.mp hop).1

theorem card_blockedBySet_le (j : Job) (M : Finset Option) (r : ℕ)
    (hblock : ∀ p ∈ M, (H.blockedBy j p).card ≤ r) :
    (H.blockedBySet j M).card ≤ M.card * r := by
  calc
    (H.blockedBySet j M).card
        ≤ ∑ p ∈ M, (H.blockedBy j p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ M, r := by
      exact Finset.sum_le_sum fun p hp ↦ hblock p hp
    _ = M.card * r := by simp

/-- A recursive certificate that `opts` chooses one compatible option for
each job in `jobs`, in the same order. -/
inductive IsOrderedSelection : List Job → List Option → Prop
  | nil : IsOrderedSelection [] []
  | cons {j : Job} {jobs : List Job} {o : Option} {opts : List Option}
      (ho : o ∈ H.fiber j)
      (hcompat : ∀ p ∈ opts, H.Compatible o p)
      (htail : IsOrderedSelection jobs opts) :
      IsOrderedSelection (j :: jobs) (o :: opts)

theorem IsOrderedSelection.length_eq {jobs : List Job} {opts : List Option}
    (h : H.IsOrderedSelection jobs opts) : opts.length = jobs.length := by
  induction h <;> simp_all

theorem IsOrderedSelection.pairwise_compatible
    {jobs : List Job} {opts : List Option}
    (h : H.IsOrderedSelection jobs opts) :
    opts.Pairwise H.Compatible := by
  induction h with
  | nil => simp
  | cons ho hcompat htail ih =>
      exact List.pairwise_cons.mpr ⟨hcompat, ih⟩

theorem IsOrderedSelection.owner_mem_of_mem
    {jobs : List Job} {opts : List Option}
    (h : H.IsOrderedSelection jobs opts) {o : Option} (ho : o ∈ opts) :
    H.owner o ∈ jobs := by
  induction h with
  | nil => simp at ho
  | @cons j jobs q opts hq hcompat htail ih =>
      rcases List.mem_cons.mp ho with rfl | ho
      · simp [H.mem_fiber.mp hq]
      · exact List.mem_cons_of_mem j (ih ho)

theorem IsOrderedSelection.opts_nodup
    {jobs : List Job} {opts : List Option}
    (h : H.IsOrderedSelection jobs opts) (hjobs : jobs.Nodup) :
    opts.Nodup := by
  induction h with
  | nil => simp
  | @cons j jobs q opts hq hcompat htail ih =>
      have hjnot : j ∉ jobs := (List.nodup_cons.mp hjobs).1
      have hqowner : H.owner q = j := H.mem_fiber.mp hq
      have hqnot : q ∉ opts := by
        intro hqopts
        have : H.owner q ∈ jobs :=
          IsOrderedSelection.owner_mem_of_mem H htail hqopts
        exact hjnot (by simpa [hqowner] using this)
      exact List.nodup_cons.mpr
        ⟨hqnot, ih (List.nodup_cons.mp hjobs).2⟩

theorem IsOrderedSelection.owner_injOn
    {jobs : List Job} {opts : List Option}
    (h : H.IsOrderedSelection jobs opts) (hjobs : jobs.Nodup) :
    Set.InjOn H.owner (opts.toFinset : Set Option) := by
  induction h with
  | nil => simp
  | @cons j jobs q opts hq hcompat htail ih =>
      have hjnot : j ∉ jobs := (List.nodup_cons.mp hjobs).1
      have hjobsTail : jobs.Nodup := (List.nodup_cons.mp hjobs).2
      have hqowner : H.owner q = j := H.mem_fiber.mp hq
      intro o ho' p hp' heq
      have ho : o ∈ q :: opts := by simpa using ho'
      have hp : p ∈ q :: opts := by simpa using hp'
      rcases List.mem_cons.mp ho with hoq | hoTail
      · rcases List.mem_cons.mp hp with hpq | hpTail
        · exact hoq.trans hpq.symm
        · exfalso
          have hpowner : H.owner p ∈ jobs :=
            IsOrderedSelection.owner_mem_of_mem H htail hpTail
          have hpj : H.owner p = j :=
            heq.symm.trans ((congrArg H.owner hoq).trans hqowner)
          exact hjnot (hpj ▸ hpowner)
      · rcases List.mem_cons.mp hp with hpq | hpTail
        · exfalso
          have hoowner : H.owner o ∈ jobs :=
            IsOrderedSelection.owner_mem_of_mem H htail hoTail
          have hoj : H.owner o = j :=
            heq.trans ((congrArg H.owner hpq).trans hqowner)
          exact hjnot (hoj ▸ hoowner)
        · exact ih hjobsTail (by simpa using hoTail)
            (by simpa using hpTail) heq

/-- Greedy extension: if fewer options are blocked than a job owns, one can
extend an ordered selection by this job. -/
theorem IsOrderedSelection.cons_of_card_blocked_lt
    {jobs : List Job} {opts : List Option}
    (htail : H.IsOrderedSelection jobs opts) (j : Job)
    (hcard : (H.blockedBySet j opts.toFinset).card < (H.fiber j).card) :
    ∃ o, H.IsOrderedSelection (j :: jobs) (o :: opts) := by
  have hnotSubset : ¬ H.fiber j ⊆ H.blockedBySet j opts.toFinset := by
    intro hsub
    exact (Nat.not_lt_of_ge (Finset.card_le_card hsub)) hcard
  have hex : ∃ o ∈ H.fiber j, o ∉ H.blockedBySet j opts.toFinset := by
    by_contra hnone
    apply hnotSubset
    intro o ho
    by_contra honot
    exact hnone ⟨o, ho, honot⟩
  obtain ⟨o, hofiber, honot⟩ := hex
  refine ⟨o, .cons hofiber ?_ htail⟩
  intro p hp
  by_contra hconflict
  apply honot
  apply Finset.mem_biUnion.mpr
  refine ⟨p, by simpa using hp, ?_⟩
  exact Finset.mem_filter.mpr ⟨hofiber, hconflict⟩

/-- An elementary greedy rank-three matching theorem.  The hypothesis `r`
bounds how many options of one job a single previously selected option can
block.  The theorem is useful both as a fallback lemma and as a precise
finite interface for stronger matching arguments. -/
theorem exists_orderedSelection_of_uniform_block_bound
    (jobs : List Job) (m r : ℕ)
    (hdegree : ∀ j ∈ jobs, m ≤ (H.fiber j).card)
    (hblock : ∀ j ∈ jobs, ∀ p : Option,
      (H.blockedBy j p).card ≤ r)
    (hroom : jobs.length * r < m) :
    ∃ opts, H.IsOrderedSelection jobs opts := by
  induction jobs with
  | nil => exact ⟨[], .nil⟩
  | cons j jobs ih =>
      have hroomTail : jobs.length * r < m := by
        exact lt_of_le_of_lt (Nat.mul_le_mul_right r (by simp)) hroom
      have hdegreeTail : ∀ k ∈ jobs, m ≤ (H.fiber k).card := by
        intro k hk
        exact hdegree k (by simp [hk])
      have hblockTail : ∀ k ∈ jobs, ∀ p : Option,
          (H.blockedBy k p).card ≤ r := by
        intro k hk p
        exact hblock k (by simp [hk]) p
      obtain ⟨opts, hopts⟩ := ih hdegreeTail hblockTail hroomTail
      have hblocked : (H.blockedBySet j opts.toFinset).card ≤
          opts.toFinset.card * r := by
        apply H.card_blockedBySet_le
        intro p hp
        exact hblock j (by simp) p
      have hfinList : opts.toFinset.card ≤ opts.length :=
        List.toFinset_card_le opts
      have hlen : opts.length = jobs.length := hopts.length_eq
      have hblocked' : (H.blockedBySet j opts.toFinset).card < m := by
        calc
          (H.blockedBySet j opts.toFinset).card
              ≤ opts.toFinset.card * r := hblocked
          _ ≤ opts.length * r := Nat.mul_le_mul_right r hfinList
          _ = jobs.length * r := by rw [hlen]
          _ < m := hroomTail
      have hblockedFiber : (H.blockedBySet j opts.toFinset).card <
          (H.fiber j).card :=
        lt_of_lt_of_le hblocked' (hdegree j (by simp))
      obtain ⟨o, hsel⟩ :=
        IsOrderedSelection.cons_of_card_blocked_lt H hopts j hblockedFiber
      exact ⟨o :: opts, hsel⟩

/-- The number of options of one job using a fixed slot.  This is the
job-slot codegree in the three-uniform hypergraph representation. -/
def jobSlotCodegree (j : Job) (s : Slot) : ℕ :=
  ((H.fiber j).filter fun o ↦ s ∈ H.slots o).card

/-- In a rank-three system, one selected option blocks at most twice the
maximum job-slot codegree of the next job. -/
theorem card_blockedBy_le_two_mul
    (j : Job) (p : Option) (lambda : ℕ)
    (hcodeg : ∀ s ∈ H.slots p, H.jobSlotCodegree j s ≤ lambda) :
    (H.blockedBy j p).card ≤ 2 * lambda := by
  let U : Finset Option := (H.slots p).biUnion fun s ↦
    (H.fiber j).filter fun o ↦ s ∈ H.slots o
  have hsubset : H.blockedBy j p ⊆ U := by
    intro o ho
    have hofiber : o ∈ H.fiber j := (Finset.mem_filter.mp ho).1
    have hnotdis : ¬ Disjoint (H.slots o) (H.slots p) :=
      (Finset.mem_filter.mp ho).2
    rw [Finset.not_disjoint_iff] at hnotdis
    obtain ⟨s, hso, hsp⟩ := hnotdis
    apply Finset.mem_biUnion.mpr
    exact ⟨s, hsp, Finset.mem_filter.mpr ⟨hofiber, hso⟩⟩
  calc
    (H.blockedBy j p).card ≤ U.card := Finset.card_le_card hsubset
    _ ≤ ∑ s ∈ H.slots p,
        ((H.fiber j).filter fun o ↦ s ∈ H.slots o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ H.slots p, lambda := by
      exact Finset.sum_le_sum fun s hs ↦ hcodeg s hs
    _ = (H.slots p).card * lambda := by simp
    _ ≤ 2 * lambda := Nat.mul_le_mul_right lambda (H.slots_card_le_two p)

/-- A concrete corollary using only job degrees and job-slot codegrees.
This bound depends on the number of jobs, unlike the Delcourt--Postle
fixed-slack theorem. -/
theorem exists_orderedSelection_of_codegree
    (jobs : List Job) (m lambda : ℕ)
    (hdegree : ∀ j ∈ jobs, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j ∈ jobs, ∀ s : Slot,
      H.jobSlotCodegree j s ≤ lambda)
    (hroom : jobs.length * (2 * lambda) < m) :
    ∃ opts, H.IsOrderedSelection jobs opts := by
  apply H.exists_orderedSelection_of_uniform_block_bound jobs m (2 * lambda)
      hdegree ?_ hroom
  intro j hj p
  apply H.card_blockedBy_le_two_mul j p lambda
  intro s hs
  exact hcodeg j hj s

/-! ## Maximal matchings and the obstruction left by greediness -/

/-- A partial matching is a set of pairwise slot-disjoint options with no
two options owned by the same job. -/
def IsPartialMatching (M : Finset Option) : Prop :=
  (M : Set Option).Pairwise H.Compatible ∧
    Set.InjOn H.owner (M : Set Option)

/-- A partial matching covers a job when it contains an option owned by that
job. -/
def Covers (M : Finset Option) (j : Job) : Prop :=
  ∃ o ∈ M, H.owner o = j

instance coversDecidable (M : Finset Option) (j : Job) : Decidable (H.Covers M j) :=
  by
    unfold Covers
    infer_instance

@[simp] theorem empty_isPartialMatching : H.IsPartialMatching ∅ := by
  simp [IsPartialMatching]

theorem IsOrderedSelection.toPartialMatching
    {jobs : List Job} {opts : List Option}
    (h : H.IsOrderedSelection jobs opts) (hjobs : jobs.Nodup) :
    H.IsPartialMatching opts.toFinset := by
  constructor
  · exact (List.pairwise_iff_coe_toFinset_pairwise
      (IsOrderedSelection.opts_nodup H h hjobs)
      (fun _ _ hp ↦ H.compatible_symm.mp hp)).mpr
        (IsOrderedSelection.pairwise_compatible H h)
  · exact IsOrderedSelection.owner_injOn H h hjobs

theorem IsOrderedSelection.covers_of_mem
    {jobs : List Job} {opts : List Option}
    (h : H.IsOrderedSelection jobs opts) {j : Job} (hj : j ∈ jobs) :
    H.Covers opts.toFinset j := by
  induction h with
  | nil => simp at hj
  | @cons k jobs q opts hq hcompat htail ih =>
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨q, by simp, H.mem_fiber.mp hq⟩
      · obtain ⟨o, ho, howner⟩ := ih hj
        exact ⟨o, by simp [ho], howner⟩

/-- Fully packaged greedy covering theorem.  It is exponential-time free in
the proof term and gives an actual finite matching, but its degree condition
still grows with the number of jobs. -/
theorem exists_covering_partialMatching_of_codegree
    (m lambda : ℕ)
    (hdegree : ∀ j, m ≤ (H.fiber j).card)
    (hcodeg : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hroom : Fintype.card Job * (2 * lambda) < m) :
    ∃ M : Finset Option,
      H.IsPartialMatching M ∧ ∀ j, H.Covers M j := by
  let jobs : List Job := (Finset.univ : Finset Job).toList
  have hjobsLength : jobs.length = Fintype.card Job := by
    simp [jobs]
  have hroom' : jobs.length * (2 * lambda) < m := by
    simpa [hjobsLength] using hroom
  obtain ⟨opts, hopts⟩ := H.exists_orderedSelection_of_codegree
    jobs m lambda
    (fun j _hj ↦ hdegree j)
    (fun j _hj s ↦ hcodeg j s) hroom'
  refine ⟨opts.toFinset,
    IsOrderedSelection.toPartialMatching H hopts
      (Finset.nodup_toList (Finset.univ : Finset Job)), ?_⟩
  intro j
  apply hopts.covers_of_mem
  simp [jobs]

/-- Add one option to a partial matching when it uses fresh slots and its
owner is not yet represented. -/
theorem IsPartialMatching.insert
    {M : Finset Option} (hM : H.IsPartialMatching M) (q : Option)
    (hqnot : q ∉ M)
    (hcompat : ∀ p ∈ M, H.Compatible q p)
    (howner : ∀ p ∈ M, H.owner p ≠ H.owner q) :
    H.IsPartialMatching (insert q M) := by
  constructor
  · rw [Finset.coe_insert, Set.pairwise_insert]
    refine ⟨hM.1, ?_⟩
    intro p hp hpne
    have hqp := hcompat p hp
    exact ⟨hqp, H.compatible_symm.mp hqp⟩
  · rw [Finset.coe_insert, Set.injOn_insert (by simpa using hqnot)]
    refine ⟨hM.2, ?_⟩
    intro hmem
    rcases hmem with ⟨p, hp, hpeq⟩
    exact howner p hp hpeq

/-- There is a maximum-cardinality partial matching.  This is a genuine
finite exhaustive-search statement; no efficiency claim is made. -/
theorem exists_maximum_partialMatching :
    ∃ M : Finset Option, H.IsPartialMatching M ∧
      ∀ M' : Finset Option, H.IsPartialMatching M' → M'.card ≤ M.card := by
  classical
  let candidates : Finset (Finset Option) :=
    (Finset.univ : Finset Option).powerset.filter H.IsPartialMatching
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, H.empty_isPartialMatching]
  obtain ⟨M, hMcand, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hnonempty
  refine ⟨M, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hMcand).2
  · intro M' hM'
    apply hmax M'
    simp [candidates, hM']

/-- In a maximum partial matching, every option of an uncovered job is
blocked by an already selected option.  This is the finite obstruction that
an augmenting-tree or nibble argument must overcome. -/
theorem maximum_partialMatching_fiber_subset_blocked
    {M : Finset Option} (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option, H.IsPartialMatching M' → M'.card ≤ M.card)
    (j : Job) (huncovered : ¬ H.Covers M j) :
    H.fiber j ⊆ H.blockedBySet j M := by
  intro q hqfiber
  by_contra hqblocked
  have hqowner : H.owner q = j := H.mem_fiber.mp hqfiber
  have hqnot : q ∉ M := by
    intro hqM
    exact huncovered ⟨q, hqM, hqowner⟩
  have hcompat : ∀ p ∈ M, H.Compatible q p := by
    intro p hp
    by_contra hconflict
    apply hqblocked
    apply Finset.mem_biUnion.mpr
    exact ⟨p, hp, Finset.mem_filter.mpr ⟨hqfiber, hconflict⟩⟩
  have howner : ∀ p ∈ M, H.owner p ≠ H.owner q := by
    intro p hp heq
    apply huncovered
    exact ⟨p, hp, heq.trans hqowner⟩
  have hins : H.IsPartialMatching (insert q M) :=
    IsPartialMatching.insert H hM q hqnot hcompat howner
  have hle : (insert q M).card ≤ M.card := hmax _ hins
  rw [Finset.card_insert_of_notMem hqnot] at hle
  exact (Nat.not_succ_le_self M.card) hle

/-- A maximum partial matching together with its explicit obstruction
certificate for every uncovered job. -/
theorem exists_maximum_partialMatching_with_certificate :
    ∃ M : Finset Option,
      H.IsPartialMatching M ∧
      (∀ M' : Finset Option, H.IsPartialMatching M' → M'.card ≤ M.card) ∧
      ∀ j, ¬ H.Covers M j → H.fiber j ⊆ H.blockedBySet j M := by
  obtain ⟨M, hM, hmax⟩ := H.exists_maximum_partialMatching
  exact ⟨M, hM, hmax,
    fun j hj ↦ H.maximum_partialMatching_fiber_subset_blocked hM hmax j hj⟩

/-- Counting form of the obstruction certificate. -/
theorem maximum_partialMatching_degree_certificate
    {M : Finset Option} (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option, H.IsPartialMatching M' → M'.card ≤ M.card)
    (j : Job) (huncovered : ¬ H.Covers M j) (r : ℕ)
    (hblock : ∀ p ∈ M, (H.blockedBy j p).card ≤ r) :
    (H.fiber j).card ≤ M.card * r := by
  calc
    (H.fiber j).card ≤ (H.blockedBySet j M).card :=
      Finset.card_le_card
        (H.maximum_partialMatching_fiber_subset_blocked hM hmax j huncovered)
    _ ≤ M.card * r := H.card_blockedBySet_le j M r hblock

end RankThreeOptionSystem

end WeightedEdgeColoring
