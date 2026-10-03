import WeightedEdgeColoring.RankThreeMatching

namespace WeightedEdgeColoring

universe u v w

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-!
## The first augmenting-tree certificate

The maximality certificate in `RankThreeMatching` only records that every
option of an uncovered job meets the current matching.  The lemmas below
record the next genuinely stronger fact: after deleting one matched option,
one cannot insert two compatible options with different owners.  This is the
depth-one obstruction from which an augmenting-tree proof must grow.
-/

/-- Taking a subset preserves the partial-matching property. -/
theorem IsPartialMatching.mono {M N : Finset Option}
    (hM : H.IsPartialMatching M) (hNM : N ⊆ M) :
    H.IsPartialMatching N := by
  constructor
  · intro x hx y hy hxy
    exact hM.1 (hNM hx) (hNM hy) hxy
  · exact hM.2.mono (by simpa using hNM)

/-- A one-edge deletion followed by two valid insertions is again a partial
matching.  The hypotheses are deliberately local: they are exactly the facts
an augmenting-tree search has to verify at a depth-one leaf. -/
theorem IsPartialMatching.exchange_one_for_two
    {M : Finset Option} (hM : H.IsPartialMatching M)
    {p q r : Option}
    (hqnot : q ∉ M) (hrnotErase : r ∉ M.erase p)
    (hqr : H.Compatible q r)
    (hqcompat : ∀ x ∈ M.erase p, H.Compatible q x)
    (hrcompat : ∀ x ∈ M.erase p, H.Compatible r x)
    (hqowner : ∀ x ∈ M.erase p, H.owner x ≠ H.owner q)
    (hrowner : ∀ x ∈ M.erase p, H.owner x ≠ H.owner r)
    (hownerqr : H.owner q ≠ H.owner r) :
    H.IsPartialMatching
      (Insert.insert q (Insert.insert r (M.erase p))) := by
  have hErase : H.IsPartialMatching (M.erase p) :=
    hM.mono H (Finset.erase_subset p M)
  have hR : H.IsPartialMatching (Insert.insert r (M.erase p)) :=
    IsPartialMatching.insert H hErase r hrnotErase hrcompat hrowner
  have hqnotR : q ∉ Insert.insert r (M.erase p) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h ↦ hownerqr (congrArg H.owner h),
      fun h ↦ hqnot (Finset.mem_of_mem_erase h)⟩
  apply IsPartialMatching.insert H hR q hqnotR
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hqr
    · exact hqcompat x hx
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Ne.symm hownerqr
    · exact hqowner x hx

/-- A maximum partial matching admits no valid `one-for-two` exchange. -/
theorem maximum_partialMatching_no_exchange_one_for_two
    {M : Finset Option}
    (hmax : ∀ M' : Finset Option, H.IsPartialMatching M' → M'.card ≤ M.card)
    {p q r : Option} (hp : p ∈ M)
    (hqnot : q ∉ M) (hrnotErase : r ∉ M.erase p) (hqr_ne : q ≠ r)
    (hexchange : H.IsPartialMatching
      (Insert.insert q (Insert.insert r (M.erase p)))) :
    False := by
  have hqnotErase : q ∉ M.erase p := fun h ↦ hqnot (Finset.mem_of_mem_erase h)
  have hqnotInsert : q ∉ Insert.insert r (M.erase p) := by
    simp [hqr_ne, hqnotErase]
  have hlarge := hmax _ hexchange
  rw [Finset.card_insert_of_notMem hqnotInsert,
    Finset.card_insert_of_notMem hrnotErase,
    Finset.card_erase_of_mem hp] at hlarge
  omega

/-- Depth-one augmenting obstruction.  If `j` is uncovered and an option
`q` for `j` has only the matched option `p` in its way, then no option `r`
owned by `p` can simultaneously avoid `q` and the rest of the matching.
Otherwise deleting `p` and inserting `q,r` increases the matching size. -/
theorem maximum_partialMatching_single_blocker_obstruction
    {M : Finset Option} (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option, H.IsPartialMatching M' → M'.card ≤ M.card)
    {j : Job} (huncovered : ¬ H.Covers M j)
    {p q r : Option} (hp : p ∈ M) (hq : q ∈ H.fiber j)
    (hr : r ∈ H.fiber (H.owner p))
    (hqr : H.Compatible q r)
    (hqcompat : ∀ x ∈ M.erase p, H.Compatible q x)
    (hrcompat : ∀ x ∈ M.erase p, H.Compatible r x) :
    False := by
  have hqowner : H.owner q = j := H.mem_fiber.mp hq
  have hrowner : H.owner r = H.owner p := H.mem_fiber.mp hr
  have hqnot : q ∉ M := by
    intro hqM
    exact huncovered ⟨q, hqM, hqowner⟩
  have hownerpj : H.owner p ≠ j := by
    intro hpj
    exact huncovered ⟨p, hp, hpj⟩
  have hrnotErase : r ∉ M.erase p := by
    intro hrM
    have hrInM : r ∈ M := Finset.mem_of_mem_erase hrM
    have hrp : r = p := hM.2 hrInM hp hrowner
    exact (Finset.ne_of_mem_erase hrM) hrp
  have hqr_ne : q ≠ r := by
    intro h
    apply hownerpj
    calc
      H.owner p = H.owner r := hrowner.symm
      _ = H.owner q := congrArg H.owner h.symm
      _ = j := hqowner
  have hqownerRest : ∀ x ∈ M.erase p, H.owner x ≠ H.owner q := by
    intro x hx heq
    apply huncovered
    exact ⟨x, Finset.mem_of_mem_erase hx, heq.trans hqowner⟩
  have hrownerRest : ∀ x ∈ M.erase p, H.owner x ≠ H.owner r := by
    intro x hx heq
    have hxp : x = p := hM.2 (Finset.mem_of_mem_erase hx) hp (heq.trans hrowner)
    exact (Finset.ne_of_mem_erase hx) hxp
  have hownerqr : H.owner q ≠ H.owner r := by
    intro heq
    exact hownerpj (hrowner.symm.trans (heq.symm.trans hqowner))
  have hexchange := hM.exchange_one_for_two H hqnot hrnotErase hqr
    hqcompat hrcompat hqownerRest hrownerRest hownerqr
  exact H.maximum_partialMatching_no_exchange_one_for_two hmax hp
    hqnot hrnotErase hqr_ne hexchange

/-- Options owned by `p` that could replace it without meeting any other
edge of the current matching. -/
def availableAfterErase (M : Finset Option) (p : Option) : Finset Option :=
  (H.fiber (H.owner p)).filter fun r ↦
    ∀ x ∈ M.erase p, H.Compatible r x

@[simp] theorem mem_availableAfterErase {M : Finset Option} {p r : Option} :
    r ∈ H.availableAfterErase M p ↔
      H.owner r = H.owner p ∧
        ∀ x ∈ M.erase p, H.Compatible r x := by
  simp [availableAfterErase]

/-- Quantitative depth-one expansion certificate.  If `q` is an option for
an uncovered job and `p` is its unique blocker in a maximum matching, every
option that could replace `p` is blocked by `q`.  Consequently at most
`2 * lambda` replacements are available under the job-slot codegree bound.

This is the first nontrivial counting step of an augmenting-tree proof: all
the other options owned by `p` must point back into the old matching. -/
theorem maximum_partialMatching_availableAfterErase_le_two_mul
    {M : Finset Option} (hM : H.IsPartialMatching M)
    (hmax : ∀ M' : Finset Option, H.IsPartialMatching M' → M'.card ≤ M.card)
    {j : Job} (huncovered : ¬ H.Covers M j)
    {p q : Option} (hp : p ∈ M) (hq : q ∈ H.fiber j)
    (hqcompat : ∀ x ∈ M.erase p, H.Compatible q x)
    (lambda : ℕ)
    (hcodeg : ∀ s ∈ H.slots q,
      H.jobSlotCodegree (H.owner p) s ≤ lambda) :
    (H.availableAfterErase M p).card ≤ 2 * lambda := by
  have hsubset :
      H.availableAfterErase M p ⊆ H.blockedBy (H.owner p) q := by
    intro r hr
    have hr' := H.mem_availableAfterErase.mp hr
    apply Finset.mem_filter.mpr
    refine ⟨H.mem_fiber.mpr hr'.1, ?_⟩
    intro hrq
    have hqr : H.Compatible q r := H.compatible_symm.mp hrq
    exact H.maximum_partialMatching_single_blocker_obstruction hM hmax
      huncovered hp hq (H.mem_fiber.mpr hr'.1) hqr hqcompat hr'.2
  calc
    (H.availableAfterErase M p).card
        ≤ (H.blockedBy (H.owner p) q).card := Finset.card_le_card hsubset
    _ ≤ 2 * lambda := H.card_blockedBy_le_two_mul (H.owner p) q lambda hcodeg

end RankThreeOptionSystem

end WeightedEdgeColoring
