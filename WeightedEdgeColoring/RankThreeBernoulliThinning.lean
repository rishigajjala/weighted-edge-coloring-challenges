import WeightedEdgeColoring.FiniteBernoulliChernoff
import WeightedEdgeColoring.RankThreeMatching

/-!
# Independent thinning of a finite rank-three option system

This file gives the exact first-moment identities used when each option is
kept independently.  Outcomes are finsets of active options and their mass is
the same finite Bernoulli product mass used by `FiniteBernoulliChernoff`.
No concentration estimate is asserted here.
-/

namespace WeightedEdgeColoring.FiniteBernoulliThinning

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Product mass restricted to a specified set of coordinates. -/
private def massOn (indices : Finset I) (q : I → ℝ) (S : Finset I) : ℝ :=
  (∏ i ∈ S, q i) * ∏ i ∈ indices \ S, (1 - q i)

omit [Fintype I] in
private lemma sum_massOn (indices : Finset I) (q : I → ℝ) :
    ∑ S ∈ indices.powerset, massOn indices q S = 1 := by
  calc
    (∑ S ∈ indices.powerset, massOn indices q S) =
        ∏ i ∈ indices, (q i + (1 - q i)) := by
      simpa [massOn] using
        (Finset.prod_add q (fun i ↦ 1 - q i) indices).symm
    _ = 1 := by simp

/-- The total product mass of outcomes containing one fixed coordinate is
exactly that coordinate's retention probability. -/
theorem sum_bernoulliMass_indicator (q : I → ℝ) (i : I) :
    (∑ S : Finset I, if i ∈ S then bernoulliMass q S else 0) = q i := by
  let rest : Finset I := (Finset.univ : Finset I).erase i
  have hfilter :
      (Finset.univ : Finset (Finset I)).filter (fun S ↦ i ∈ S) =
        rest.powerset.image (insert i) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_powerset]
    constructor
    · intro hi
      refine ⟨S.erase i, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_erase] at hx
        simp [rest, hx.1]
      · exact Finset.insert_erase hi
    · rintro ⟨T, hT, rfl⟩
      simp
  rw [← Finset.sum_filter]
  rw [hfilter, Finset.sum_image]
  · have hfactor : ∀ T ∈ rest.powerset,
        bernoulliMass q (insert i T) = q i * massOn rest q T := by
      intro T hT
      have hiT : i ∉ T := by
        intro hi
        exact (Finset.mem_erase.mp (Finset.mem_powerset.mp hT hi)).1 rfl
      have hdiff : (Finset.univ : Finset I) \ insert i T = rest \ T := by
        ext x
        simp [rest, and_comm]
      simp [bernoulliMass, massOn, hiT, hdiff]
      ring
    calc
      (∑ T ∈ rest.powerset, bernoulliMass q (insert i T)) =
          ∑ T ∈ rest.powerset, q i * massOn rest q T := by
            exact Finset.sum_congr rfl fun T hT ↦ hfactor T hT
      _ = q i * (∑ T ∈ rest.powerset, massOn rest q T) := by
            rw [Finset.mul_sum]
      _ = q i := by rw [sum_massOn]; ring
  · intro A hA B hB heq
    have hiA : i ∉ A := by
      intro hi
      exact (Finset.mem_erase.mp (Finset.mem_powerset.mp hA hi)).1 rfl
    have hiB : i ∉ B := by
      intro hi
      exact (Finset.mem_erase.mp (Finset.mem_powerset.mp hB hi)).1 rfl
    have herase := congrArg (fun S : Finset I ↦ S.erase i) heq
    simpa [hiA, hiB] using herase

/-- Exact expectation of an arbitrary weighted sum of retained coordinates. -/
theorem expected_weightedSum (q a : I → ℝ) :
    (∑ S : Finset I, bernoulliMass q S * weightedSum a S) = mean q a := by
  have hpoint (S : Finset I) :
      bernoulliMass q S * weightedSum a S =
        ∑ i : I, if i ∈ S then bernoulliMass q S * a i else 0 := by
    simp [weightedSum, Finset.mul_sum]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  unfold mean
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ S : Finset I, if i ∈ S then bernoulliMass q S * a i else 0) =
        (∑ S : Finset I, if i ∈ S then bernoulliMass q S else 0) * a i := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro S hS
          split <;> simp_all
    _ = q i * a i := by rw [sum_bernoulliMass_indicator]

/-- Exact variance of one retained-coordinate indicator.  The identity is
algebraic and therefore does not need bounds on `q`. -/
theorem coordinate_variance (q : I → ℝ) (i : I) :
    (∑ S : Finset I, bernoulliMass q S *
      ((if i ∈ S then (1 : ℝ) else 0) - q i) ^ 2) =
      q i * (1 - q i) := by
  have hfirst :
      (∑ S : Finset I, bernoulliMass q S *
        (if i ∈ S then (1 : ℝ) else 0)) = q i := by
    simpa using sum_bernoulliMass_indicator q i
  have hsecond :
      (∑ S : Finset I, bernoulliMass q S *
        (if i ∈ S then (1 : ℝ) else 0) ^ 2) = q i := by
    simpa using sum_bernoulliMass_indicator q i
  calc
    (∑ S : Finset I, bernoulliMass q S *
        ((if i ∈ S then (1 : ℝ) else 0) - q i) ^ 2) =
        (∑ S : Finset I, bernoulliMass q S *
          (if i ∈ S then (1 : ℝ) else 0) ^ 2) -
        2 * q i * (∑ S : Finset I, bernoulliMass q S *
          (if i ∈ S then (1 : ℝ) else 0)) +
        (∑ S : Finset I, bernoulliMass q S) * (q i) ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_mul]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = q i - 2 * q i * q i + (q i) ^ 2 := by
      rw [hfirst, hsecond, sum_bernoulliMass]
      ring
    _ = q i * (1 - q i) := by ring

/-- Number of retained coordinates satisfying a decidable predicate. -/
def activeCount (P : I → Prop) [DecidablePred P] (S : Finset I) : ℕ :=
  (S.filter P).card

omit [Fintype I] [DecidableEq I] in
theorem activeCount_cast_eq_weightedSum (P : I → Prop) [DecidablePred P]
    (S : Finset I) :
    (activeCount P S : ℝ) = weightedSum (fun i ↦ if P i then 1 else 0) S := by
  simp [activeCount, weightedSum]

/-- Exact expected number of retained coordinates satisfying `P`. -/
theorem expected_activeCount (q : I → ℝ) (P : I → Prop) [DecidablePred P] :
    (∑ S : Finset I, bernoulliMass q S * (activeCount P S : ℝ)) =
      ∑ i : I, if P i then q i else 0 := by
  simp_rw [activeCount_cast_eq_weightedSum]
  rw [expected_weightedSum]
  simp [mean]

end WeightedEdgeColoring.FiniteBernoulliThinning

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliThinning

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Degree of a job after retaining the options in `S`. -/
def thinnedJobDegree (S : Finset Option) (j : Job) : ℕ :=
  activeCount (fun o ↦ H.owner o = j) S

/-- Degree of a slot after retaining the options in `S`. -/
def thinnedSlotDegree (S : Finset Option) (s : Slot) : ℕ :=
  activeCount (fun o ↦ s ∈ H.slots o) S

/-- Codegree of two slots after retaining the options in `S`. -/
def thinnedSlotPairCodegree (S : Finset Option) (s t : Slot) : ℕ :=
  activeCount (fun o ↦ s ∈ H.slots o ∧ t ∈ H.slots o) S

/-- Indicator-sum form of the expected job degree. -/
theorem expected_thinnedJobDegree_indicator (q : Option → ℝ) (j : Job) :
    (∑ S : Finset Option,
      bernoulliMass q S * (H.thinnedJobDegree S j : ℝ)) =
      ∑ o : Option, if H.owner o = j then q o else 0 := by
  simpa [thinnedJobDegree] using
    (expected_activeCount (I := Option) q (fun o ↦ H.owner o = j))

/-- Exact expected job degree under independent thinning, as the total
retention probability in the job's option fibre. -/
theorem expected_thinnedJobDegree (q : Option → ℝ) (j : Job) :
    (∑ S : Finset Option,
      bernoulliMass q S * (H.thinnedJobDegree S j : ℝ)) =
      ∑ o ∈ H.fiber j, q o := by
  rw [H.expected_thinnedJobDegree_indicator q j]
  symm
  simpa [fiber] using
    (Finset.sum_filter (s := (Finset.univ : Finset Option))
      (p := fun o ↦ H.owner o = j) q)

/-- Exact expected slot degree under independent thinning. -/
theorem expected_thinnedSlotDegree (q : Option → ℝ) (s : Slot) :
    (∑ S : Finset Option,
      bernoulliMass q S * (H.thinnedSlotDegree S s : ℝ)) =
      ∑ o : Option, if s ∈ H.slots o then q o else 0 := by
  simpa [thinnedSlotDegree] using
    (expected_activeCount (I := Option) q (fun o ↦ s ∈ H.slots o))

/-- Exact expected slot-pair codegree under independent thinning. -/
theorem expected_thinnedSlotPairCodegree (q : Option → ℝ) (s t : Slot) :
    (∑ S : Finset Option,
      bernoulliMass q S * (H.thinnedSlotPairCodegree S s t : ℝ)) =
      ∑ o : Option, if s ∈ H.slots o ∧ t ∈ H.slots o then q o else 0 := by
  simpa [thinnedSlotPairCodegree] using
    (expected_activeCount (I := Option) q
      (fun o ↦ s ∈ H.slots o ∧ t ∈ H.slots o))

end WeightedEdgeColoring.RankThreeOptionSystem
