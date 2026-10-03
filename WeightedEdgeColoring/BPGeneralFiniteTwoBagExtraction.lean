import WeightedEdgeColoring.BPGeneralTwoBagMassCertificate

/-!
# Extracting the two-bag mass certificate from finite bin data

This module supplies the finite combinatorial layer immediately before
`OrientedTwoBagMassCertificate`.  A joint fractional packing is represented
by finitely many bins with nonnegative masses and two packet weights whose
sum is at most one.  A second finite type lists pieces pairing every
second-heavy bin completely with available mass in first-heavy bins.

The two separate costs are defined from those pieces: an unpaired
first-heavy piece costs one first bin and half a second bin; a paired piece
costs either `(1, 3/2)` or `(3/2, 1)` according to which two packets fit;
a nonheavy bin costs half a bin on each side.  The main theorem derives all
four aggregate masses and both cost inequalities required by the algebraic
certificate in `BPGeneralTwoBagMassCertificate`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u v

section

variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Finite joint packing data together with a splitting of all second-heavy
mass across first-heavy bins.  Pair pieces may split the mass of either
original bin arbitrarily. -/
structure FiniteTwoBagJointPacking where
  mass : ι → ℝ
  firstWeight : ι → ℝ
  secondWeight : ι → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  firstWeight_nonneg : ∀ i, 0 ≤ firstWeight i
  secondWeight_nonneg : ∀ i, 0 ≤ secondWeight i
  capacity : ∀ i, firstWeight i + secondWeight i ≤ 1
  pairMass : κ → ℝ
  left : κ → ι
  right : κ → ι
  pairMass_nonneg : ∀ k, 0 ≤ pairMass k
  left_heavy : ∀ k, 1 / 2 < firstWeight (left k)
  right_heavy : ∀ k, 1 / 2 < secondWeight (right k)
  left_use_le : ∀ i,
    (∑ k : κ, if left k = i then pairMass k else 0) ≤ mass i
  right_fully_used : ∀ i, 1 / 2 < secondWeight i →
    (∑ k : κ, if right k = i then pairMass k else 0) = mass i

namespace FiniteTwoBagJointPacking

variable (P : FiniteTwoBagJointPacking (ι := ι) (κ := κ))

def firstHeavyBins : Finset ι :=
  Finset.univ.filter fun i ↦ 1 / 2 < P.firstWeight i

def secondHeavyBins : Finset ι :=
  Finset.univ.filter fun i ↦ 1 / 2 < P.secondWeight i

def nonheavyBins : Finset ι :=
  Finset.univ \ (P.firstHeavyBins ∪ P.secondHeavyBins)

def leftUse (i : ι) : ℝ :=
  ∑ k : κ, if P.left k = i then P.pairMass k else 0

def firstHeavyMass : ℝ := ∑ i ∈ P.firstHeavyBins, P.mass i

def secondHeavyMass : ℝ := ∑ i ∈ P.secondHeavyBins, P.mass i

def nonheavyMass : ℝ := ∑ i ∈ P.nonheavyBins, P.mass i

def firstCombinedMass : ℝ :=
  ∑ k : κ,
    if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
    then P.pairMass k else 0

/-- Cost of the explicit first-side fractional packing obtained from the
unpaired first-heavy pieces, the paired pieces, and doubled nonheavy bins. -/
def firstSeparatedCost : ℝ :=
  (∑ i ∈ P.firstHeavyBins, (P.mass i - P.leftUse i)) +
    (∑ k : κ,
      if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
      then P.pairMass k else (3 / 2) * P.pairMass k) +
    P.nonheavyMass / 2

/-- Cost of the symmetric second-side packing extracted from the same
pieces. -/
def secondSeparatedCost : ℝ :=
  (∑ i ∈ P.firstHeavyBins, (P.mass i - P.leftUse i) / 2) +
    (∑ k : κ,
      if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
      then (3 / 2) * P.pairMass k else P.pairMass k) +
    P.nonheavyMass / 2

theorem not_both_heavy (i : ι) :
    ¬(1 / 2 < P.firstWeight i ∧ 1 / 2 < P.secondWeight i) := by
  intro h
  have := P.capacity i
  linarith

/-- In the first-combination branch, the two first-side packets really fit
in one unit bin. -/
theorem first_packets_fit_of_combined (k : κ)
    (h : P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)) :
    P.firstWeight (P.left k) + P.firstWeight (P.right k) ≤ 1 := by
  have hcap := P.capacity (P.right k)
  linarith

/-- In the other branch, the two second-side packets fit in one unit bin. -/
theorem second_packets_fit_of_not_combined (k : κ)
    (h : ¬P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)) :
    P.secondWeight (P.left k) + P.secondWeight (P.right k) ≤ 1 := by
  have hcap := P.capacity (P.left k)
  have hlt : P.secondWeight (P.right k) < P.firstWeight (P.left k) :=
    lt_of_not_ge h
  linarith

theorem weights_le_half_of_mem_nonheavy {i : ι} (hi : i ∈ P.nonheavyBins) :
    P.firstWeight i ≤ 1 / 2 ∧ P.secondWeight i ≤ 1 / 2 := by
  simp only [nonheavyBins, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, firstHeavyBins, secondHeavyBins, Finset.mem_filter] at hi
  exact ⟨le_of_not_gt (fun h ↦ hi (Or.inl h)),
    le_of_not_gt (fun h ↦ hi (Or.inr h))⟩

theorem doubled_weights_fit_of_mem_nonheavy {i : ι} (hi : i ∈ P.nonheavyBins) :
    2 * P.firstWeight i ≤ 1 ∧ 2 * P.secondWeight i ≤ 1 := by
  rcases P.weights_le_half_of_mem_nonheavy hi with ⟨hfirst, hsecond⟩
  constructor <;> linarith

theorem pair_total_eq_secondHeavyMass :
    (∑ k : κ, P.pairMass k) = P.secondHeavyMass := by
  rw [secondHeavyMass]
  calc
    (∑ k : κ, P.pairMass k) =
        ∑ i ∈ P.secondHeavyBins,
          ∑ k : κ, if P.right k = i then P.pairMass k else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_eq_single (P.right k)]
      · simp
      · intro j _hj hne
        simp [hne.symm]
      · intro hnot
        exact (hnot (by simpa [secondHeavyBins] using P.right_heavy k)).elim
    _ = ∑ i ∈ P.secondHeavyBins, P.mass i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact P.right_fully_used i (Finset.mem_filter.mp hi).2

theorem sum_leftUse_firstHeavy :
    (∑ i ∈ P.firstHeavyBins, P.leftUse i) =
      ∑ k : κ, P.pairMass k := by
  simp only [leftUse]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Finset.sum_eq_single (P.left k)]
  · simp
  · intro i _hi hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (by simpa [firstHeavyBins] using P.left_heavy k)).elim

/-- Reindex a weighted sum over pair pieces by their first-heavy bin. -/
theorem sum_pairMass_mul_left (f : ι → ℝ) :
    (∑ k : κ, P.pairMass k * f (P.left k)) =
      ∑ i ∈ P.firstHeavyBins, P.leftUse i * f i := by
  calc
    (∑ k : κ, P.pairMass k * f (P.left k)) =
        ∑ k : κ, ∑ i ∈ P.firstHeavyBins,
          if P.left k = i then P.pairMass k * f i else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_eq_single (P.left k)]
      · simp
      · intro i _hi hne
        simp [hne.symm]
      · intro hnot
        exact (hnot (by simpa [firstHeavyBins] using P.left_heavy k)).elim
    _ = ∑ i ∈ P.firstHeavyBins, ∑ k : κ,
          if P.left k = i then P.pairMass k * f i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ P.firstHeavyBins, P.leftUse i * f i := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [leftUse, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      split_ifs <;> ring

/-- Reindex a weighted sum over pair pieces by their fully used
second-heavy bin. -/
theorem sum_pairMass_mul_right (f : ι → ℝ) :
    (∑ k : κ, P.pairMass k * f (P.right k)) =
      ∑ i ∈ P.secondHeavyBins, P.mass i * f i := by
  calc
    (∑ k : κ, P.pairMass k * f (P.right k)) =
        ∑ k : κ, ∑ i ∈ P.secondHeavyBins,
          if P.right k = i then P.pairMass k * f i else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_eq_single (P.right k)]
      · simp
      · intro i _hi hne
        simp [hne.symm]
      · intro hnot
        exact (hnot (by simpa [secondHeavyBins] using P.right_heavy k)).elim
    _ = ∑ i ∈ P.secondHeavyBins, ∑ k : κ,
          if P.right k = i then P.pairMass k * f i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ P.secondHeavyBins, P.mass i * f i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← P.right_fully_used i (Finset.mem_filter.mp hi).2]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      split_ifs <;> ring

theorem leftUse_nonneg (i : ι) : 0 ≤ P.leftUse i := by
  exact Finset.sum_nonneg fun k _hk ↦ by
    split_ifs
    · exact P.pairMass_nonneg k
    · exact le_rfl

theorem unpaired_firstHeavy_nonneg (i : ι) :
    0 ≤ P.mass i - P.leftUse i :=
  sub_nonneg.mpr (P.left_use_le i)

/-- The first-heavy, second-heavy, and nonheavy bins partition every weighted
sum over the original finite bin type. -/
theorem sum_mass_mul_partition (f : ι → ℝ) :
    (∑ i : ι, P.mass i * f i) =
      (∑ i ∈ P.firstHeavyBins, P.mass i * f i) +
      (∑ i ∈ P.secondHeavyBins, P.mass i * f i) +
      (∑ i ∈ P.nonheavyBins, P.mass i * f i) := by
  have hdisj : Disjoint P.firstHeavyBins P.secondHeavyBins := by
    rw [Finset.disjoint_left]
    intro i hi hj
    exact P.not_both_heavy i
      ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩
  have hrest : Disjoint (P.firstHeavyBins ∪ P.secondHeavyBins)
      P.nonheavyBins := by
    simp [nonheavyBins, Finset.disjoint_sdiff]
  have hsub : P.firstHeavyBins ∪ P.secondHeavyBins ⊆
      (Finset.univ : Finset ι) := Finset.subset_univ _
  rw [← Finset.sum_union hdisj, ← Finset.sum_union hrest]
  simp [nonheavyBins, Finset.union_sdiff_of_subset hsub]

theorem secondHeavyMass_le_firstHeavyMass :
    P.secondHeavyMass ≤ P.firstHeavyMass := by
  rw [← P.pair_total_eq_secondHeavyMass, ← P.sum_leftUse_firstHeavy]
  unfold firstHeavyMass
  exact Finset.sum_le_sum fun i _hi ↦ P.left_use_le i

theorem firstCombinedMass_nonneg : 0 ≤ P.firstCombinedMass := by
  unfold firstCombinedMass
  exact Finset.sum_nonneg fun k _hk ↦ by
    split_ifs
    · exact P.pairMass_nonneg k
    · exact le_rfl

theorem firstCombinedMass_le_secondHeavyMass :
    P.firstCombinedMass ≤ P.secondHeavyMass := by
  rw [← P.pair_total_eq_secondHeavyMass]
  unfold firstCombinedMass
  exact Finset.sum_le_sum fun k _hk ↦ by
    split_ifs
    · exact le_rfl
    · exact P.pairMass_nonneg k

theorem nonheavyMass_nonneg : 0 ≤ P.nonheavyMass := by
  unfold nonheavyMass
  exact Finset.sum_nonneg fun i _hi ↦ P.mass_nonneg i

theorem sum_unpaired_firstHeavy :
    (∑ i ∈ P.firstHeavyBins, (P.mass i - P.leftUse i)) =
      P.firstHeavyMass - P.secondHeavyMass := by
  rw [Finset.sum_sub_distrib, P.sum_leftUse_firstHeavy,
    P.pair_total_eq_secondHeavyMass]
  rfl

theorem first_pair_cost_eq :
    (∑ k : κ,
      if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
      then P.pairMass k else (3 / 2) * P.pairMass k) =
      (3 / 2) * P.secondHeavyMass - P.firstCombinedMass / 2 := by
  rw [← P.pair_total_eq_secondHeavyMass]
  unfold firstCombinedMass
  calc
    (∑ k : κ, if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
      then P.pairMass k else (3 / 2) * P.pairMass k) =
        ∑ k : κ, ((3 / 2) * P.pairMass k -
          (if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
           then P.pairMass k else 0) / 2) := by
          apply Finset.sum_congr rfl
          intro k _hk
          split_ifs <;> ring
    _ = (3 / 2) * (∑ k : κ, P.pairMass k) -
        (∑ k : κ, if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
          then P.pairMass k else 0) / 2 := by
          simp only [Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]

theorem second_pair_cost_eq :
    (∑ k : κ,
      if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
      then (3 / 2) * P.pairMass k else P.pairMass k) =
      (∑ k : κ, P.pairMass k) + P.firstCombinedMass / 2 := by
  unfold firstCombinedMass
  calc
    (∑ k : κ, if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
      then (3 / 2) * P.pairMass k else P.pairMass k) =
        ∑ k : κ, (P.pairMass k +
          (if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
           then P.pairMass k else 0) / 2) := by
          apply Finset.sum_congr rfl
          intro k _hk
          split_ifs <;> ring
    _ = (∑ k : κ, P.pairMass k) +
        (∑ k : κ, if P.firstWeight (P.left k) ≤ P.secondWeight (P.right k)
          then P.pairMass k else 0) / 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_div]

theorem sum_unpaired_firstHeavy_half :
    (∑ i ∈ P.firstHeavyBins, (P.mass i - P.leftUse i) / 2) =
      (P.firstHeavyMass - P.secondHeavyMass) / 2 := by
  rw [← Finset.sum_div, P.sum_unpaired_firstHeavy]

theorem firstSeparatedCost_eq :
    P.firstSeparatedCost =
      P.firstHeavyMass + P.secondHeavyMass / 2 -
        P.firstCombinedMass / 2 + P.nonheavyMass / 2 := by
  rw [firstSeparatedCost, P.sum_unpaired_firstHeavy, P.first_pair_cost_eq]
  ring

theorem secondSeparatedCost_eq :
    P.secondSeparatedCost =
      P.firstHeavyMass / 2 + P.secondHeavyMass / 2 +
        P.firstCombinedMass / 2 + P.nonheavyMass / 2 := by
  rw [secondSeparatedCost, P.sum_unpaired_firstHeavy_half,
    P.second_pair_cost_eq, P.pair_total_eq_secondHeavyMass]
  ring

/-- Extract the exact oriented four-mass certificate from finite joint bins
and their explicit heavy-mass pairing.  The only cost hypotheses say that
`a,b` are dominated by the operational separate costs defined above; the
closed-form inequalities are proved here. -/
noncomputable def toOrientedTwoBagMassCertificate {a b T : ℝ}
    (htotal : T = ∑ i : ι, P.mass i)
    (ha : a ≤ P.firstSeparatedCost)
    (hb : b ≤ P.secondSeparatedCost) :
    OrientedTwoBagMassCertificate a b T := by
  refine
    { ell := P.firstHeavyMass
      m := P.secondHeavyMass
      z := P.nonheavyMass
      p := P.firstCombinedMass
      ell_nonneg := Finset.sum_nonneg fun i _hi ↦ P.mass_nonneg i
      m_nonneg := Finset.sum_nonneg fun i _hi ↦ P.mass_nonneg i
      z_nonneg := P.nonheavyMass_nonneg
      p_nonneg := P.firstCombinedMass_nonneg
      m_le_ell := P.secondHeavyMass_le_firstHeavyMass
      p_le_m := P.firstCombinedMass_le_secondHeavyMass
      total := ?_
      first_cost_le := ?_
      second_cost_le := ?_ }
  · rw [htotal]
    have hdisj : Disjoint P.firstHeavyBins P.secondHeavyBins := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      exact P.not_both_heavy i
        ⟨(Finset.mem_filter.mp hiA).2, (Finset.mem_filter.mp hiB).2⟩
    have hsub : P.firstHeavyBins ∪ P.secondHeavyBins ⊆ (Finset.univ : Finset ι) :=
      Finset.subset_univ _
    have hrest : Disjoint (P.firstHeavyBins ∪ P.secondHeavyBins) P.nonheavyBins := by
      simp [nonheavyBins, Finset.disjoint_sdiff]
    unfold firstHeavyMass secondHeavyMass nonheavyMass
    rw [← Finset.sum_union hdisj, ← Finset.sum_union hrest]
    simp [nonheavyBins, Finset.union_sdiff_of_subset hsub]
  · rw [← P.firstSeparatedCost_eq]
    exact ha
  · rw [← P.secondSeparatedCost_eq]
    exact hb

/-- Symmetric wrapper in the format consumed by the triangle theorem. -/
theorem toTwoBagMassCertificate {a b T : ℝ}
    (htotal : T = ∑ i : ι, P.mass i)
    (ha : a ≤ P.firstSeparatedCost)
    (hb : b ≤ P.secondSeparatedCost) :
    TwoBagMassCertificate a b T :=
  Or.inl ⟨P.toOrientedTwoBagMassCertificate htotal ha hb⟩

end FiniteTwoBagJointPacking

end

end


end WeightedEdgeColoring
