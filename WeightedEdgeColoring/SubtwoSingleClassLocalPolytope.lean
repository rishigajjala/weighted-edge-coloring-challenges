import WeightedEdgeColoring.CardinalityLocalPolytope
import WeightedEdgeColoring.MultigraphLocalPolytope
import WeightedEdgeColoring.MultigraphProfileRepresentation
import WeightedEdgeColoring.SubtwoLabelProfiles

/-! A local distribution that records the class of every sampled feasible set. -/

open scoped BigOperators

namespace WeightedEdgeColoring

section SingleClassLocalPolytope

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem sizeClasses_singleClassDistribution
    {K : Type*} [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : I → K) (w x : I → ℝ) (p : K → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a ≤ 1)
    (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, w i ≤ (1 : ℝ) / capacity (classOf i))
    (hx0 : ∀ i, 0 ≤ x i)
    (hxpoint : ∀ i, x i ≤ p (classOf i))
    (hxclass : ∀ a,
      (∑ i, if classOf i = a then x i else 0) ≤
        (capacity a : ℝ) * p a) :
    ∃ q : Finset I → ℝ,
      (∀ S, 0 ≤ q S) ∧
      (∑ S, q S = 1) ∧
      (∀ S, q S ≠ 0 → ∑ i ∈ S, w i ≤ 1) ∧
      (∀ i, (∑ S, if i ∈ S then q S else 0) = x i) ∧
      (∀ S, q S ≠ 0 → S ≠ ∅ →
        ∃ a : K, ∀ i ∈ S, classOf i = a) ∧
      (∀ a : K,
        (∑ S : Finset I,
          if S ≠ ∅ ∧ (∀ i ∈ S, classOf i = a) then q S else 0) ≤
          p a) := by
  classical
  let y : K → I → ℝ := fun a i ↦
    if classOf i = a then x i / p a else 0
  have hy0 : ∀ a i, 0 ≤ y a i := by
    intro a i
    by_cases hi : classOf i = a
    · by_cases hpa : p a = 0
      · simp [y, hi, hpa]
      · simpa [y, hi] using div_nonneg (hx0 i) (hp0 a)
    · simp [y, hi]
  have hy1 : ∀ a i, y a i ≤ 1 := by
    intro a i
    by_cases hi : classOf i = a
    · subst a
      by_cases hp : p (classOf i) = 0
      · simp [y, hp]
      · have hppos : 0 < p (classOf i) :=
          lt_of_le_of_ne (hp0 (classOf i)) (Ne.symm hp)
        simpa [y, hp] using (div_le_one hppos).2 (hxpoint i)
    · simp [y, hi]
  have hysum : ∀ a, ∑ i, y a i ≤ capacity a := by
    intro a
    by_cases hpa : p a = 0
    · have hxzero : ∀ i, classOf i = a → x i = 0 := by
        intro i hi
        have hle : x i ≤ 0 := by simpa [hi, hpa] using hxpoint i
        exact le_antisymm hle (hx0 i)
      apply le_trans (le_of_eq ?_) (Nat.cast_nonneg (capacity a))
      apply Finset.sum_eq_zero
      intro i _hi
      by_cases hi : classOf i = a
      · simp [y, hi, hpa]
      · simp [y, hi]
    · have hppos : 0 < p a := lt_of_le_of_ne (hp0 a) (Ne.symm hpa)
      have heq : (∑ i, y a i) =
          (∑ i, if classOf i = a then x i else 0) / p a := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hi : classOf i = a <;> simp [y, hi]
      rw [heq]
      apply (div_le_iff₀ hppos).2
      simpa [mul_comm] using hxclass a
  choose mass hmass0 hmasstotal hmasssupport hmassmarg using
    fun a ↦ cardinality_isAverageOfFeasibleSubsets
      (capacity a) (hcapacity a) (y a) (hy0 a) (hy1 a) (hysum a)
  have hmass_card : ∀ a S, mass a S ≠ 0 → S.card ≤ capacity a := by
    intro a S hne
    have hload := hmasssupport a S hne
    have hcapR : (0 : ℝ) < capacity a := by
      exact_mod_cast hcapacity a
    have heq : (∑ i ∈ S, (1 : ℝ) / capacity a) =
        (S.card : ℝ) / capacity a := by simp [div_eq_mul_inv]
    rw [heq] at hload
    have hcast : (S.card : ℝ) ≤ capacity a := by
      simpa using (div_le_iff₀ hcapR).mp hload
    exact_mod_cast hcast
  have hmass_sameClass : ∀ a S, mass a S ≠ 0 →
      ∀ i ∈ S, classOf i = a := by
    intro a S hne i hiS
    by_contra hiClass
    have hyzero : y a i = 0 := by simp [y, hiClass]
    have htermNonneg : ∀ T : Finset I,
        0 ≤ if i ∈ T then mass a T else 0 := by
      intro T
      split
      · exact hmass0 a T
      · exact le_rfl
    have hsingle : mass a S ≤
        ∑ T : Finset I, if i ∈ T then mass a T else 0 := by
      have := Finset.single_le_sum
        (fun T _hT ↦ htermNonneg T) (Finset.mem_univ S)
      simpa [hiS] using this
    rw [hmassmarg a i, hyzero] at hsingle
    have hzero : mass a S = 0 :=
      le_antisymm hsingle (hmass0 a S)
    exact hne hzero
  have hmass_feasible : ∀ a S, mass a S ≠ 0 →
      ∑ i ∈ S, w i ≤ 1 := by
    intro a S hne
    have hsame := hmass_sameClass a S hne
    have hcard := hmass_card a S hne
    have hcapR : (0 : ℝ) < capacity a := by
      exact_mod_cast hcapacity a
    calc
      (∑ i ∈ S, w i) ≤
          ∑ _i ∈ S, (1 : ℝ) / capacity a := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [hsame i hi] using hw i
      _ = (S.card : ℝ) / capacity a := by simp [div_eq_mul_inv]
      _ ≤ (capacity a : ℝ) / capacity a := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hcapR.le
      _ = 1 := by field_simp
  let leftover : ℝ := 1 - ∑ a, p a
  let combined : Finset I → ℝ := fun S ↦
    (if S = ∅ then leftover else 0) +
      ∑ a, p a * mass a S
  refine ⟨combined, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S
    apply add_nonneg
    · split
      · exact sub_nonneg.mpr hpsum
      · exact le_rfl
    · exact Finset.sum_nonneg fun a _ha ↦
        mul_nonneg (hp0 a) (hmass0 a S)
  · calc
      (∑ S, combined S) =
          leftover + ∑ S : Finset I, ∑ a, p a * mass a S := by
        rw [Finset.sum_add_distrib]
        have hempty :
            (∑ S : Finset I, if S = ∅ then leftover else 0) = leftover := by
          simp
        rw [hempty]
      _ = leftover + ∑ a, p a * (∑ S : Finset I, mass a S) := by
        rw [Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = 1 := by
        simp_rw [hmasstotal]
        simp [leftover]
  · intro S hcombined
    by_cases hS : S = ∅
    · subst S
      simp
    · have hsumNe : (∑ a, p a * mass a S) ≠ 0 := by
        intro hz
        apply hcombined
        simp [combined, hS, hz]
      have hex : ∃ a, p a * mass a S ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hsumNe (Finset.sum_eq_zero fun a _ha ↦ hall a)
      obtain ⟨a, ha⟩ := hex
      exact hmass_feasible a S (right_ne_zero_of_mul ha)
  · intro i
    calc
      (∑ S, if i ∈ S then combined S else 0) =
          ∑ S : Finset I, ∑ a,
            p a * (if i ∈ S then mass a S else 0) := by
        apply Finset.sum_congr rfl
        intro S _hS
        by_cases hiS : i ∈ S
        · have hSne : S ≠ ∅ := by
            intro h
            subst S
            simpa using hiS
          simp [combined, hiS, hSne]
        · simp [hiS]
      _ = ∑ a, p a *
          (∑ S : Finset I, if i ∈ S then mass a S else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.mul_sum]
      _ = ∑ a, p a * y a i := by simp_rw [hmassmarg]
      _ = x i := by
        let a0 := classOf i
        by_cases hp : p a0 = 0
        · have hxzero : x i = 0 := by
            have hle : x i ≤ 0 := by simpa [a0, hp] using hxpoint i
            exact le_antisymm hle (hx0 i)
          rw [hxzero]
          apply Finset.sum_eq_zero
          intro a _ha
          by_cases ha0 : a = a0
          · subst a
            simp [a0, hp]
          · have hclass : classOf i ≠ a := by simpa [a0] using Ne.symm ha0
            simp [y, hclass]
        · rw [Finset.sum_eq_single a0]
          · have hclass : classOf i = a0 := rfl
            simp [y, hclass]
            field_simp [hp]
          · intro a _ha hne
            have hclass : classOf i ≠ a := by simpa [a0] using Ne.symm hne
            simp [y, hclass]
          · intro hnot
            exact (hnot (Finset.mem_univ a0)).elim

  · intro S hcombined hS
    have hsumNe : (∑ a, p a * mass a S) ≠ 0 := by
      intro hz
      apply hcombined
      simp [combined, hS, hz]
    have hex : ∃ a, p a * mass a S ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hsumNe (Finset.sum_eq_zero fun a _ha ↦ hall a)
    obtain ⟨a, ha⟩ := hex
    exact ⟨a, hmass_sameClass a S (right_ne_zero_of_mul ha)⟩
  · intro a
    have hpoint : ∀ S : Finset I,
        (if S ≠ ∅ ∧ (∀ i ∈ S, classOf i = a) then combined S else 0) ≤
          p a * mass a S := by
      intro S
      by_cases hc : S ≠ ∅ ∧ (∀ i ∈ S, classOf i = a)
      · have hother : ∀ b : K, b ≠ a → mass b S = 0 := by
          intro b hba
          by_contra hne
          obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hc.1
          have hb := hmass_sameClass b S hne i hi
          have ha := hc.2 i hi
          exact hba (hb.symm.trans ha)
        have hsum : (∑ b, p b * mass b S) = p a * mass a S := by
          apply Finset.sum_eq_single a
          · intro b _hb hba
            simp [hother b hba]
          · intro hnot
            exact (hnot (Finset.mem_univ a)).elim
        rw [if_pos hc]
        simp only [combined, if_neg hc.1, zero_add, hsum]
        exact le_rfl
      · exact le_trans (by simp [hc])
          (mul_nonneg (hp0 a) (hmass0 a S))
    calc
      (∑ S : Finset I,
          if S ≠ ∅ ∧ (∀ i ∈ S, classOf i = a) then combined S else 0) ≤
          ∑ S : Finset I, p a * mass a S :=
        Finset.sum_le_sum fun S _ ↦ hpoint S
      _ = p a := by rw [← Finset.mul_sum, hmasstotal, mul_one]

theorem sizeClasses_singleClassDistribution_of_charge
    {K : Type*} [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : I → K) (w x : I → ℝ) (M : ℝ)
    (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, w i ≤ (1 : ℝ) / capacity (classOf i))
    (hx0 : ∀ i, 0 ≤ x i) (hM0 : 0 ≤ M)
    (hxM : ∀ i, x i ≤ M)
    (hbudget :
      (∑ i, x i / (capacity (classOf i) : ℝ)) +
          (Fintype.card K : ℝ) * M ≤ 1) :
    ∃ q : Finset I → ℝ,
      (∀ S, 0 ≤ q S) ∧
      (∑ S, q S = 1) ∧
      (∀ S, q S ≠ 0 → ∑ i ∈ S, w i ≤ 1) ∧
      (∀ i, (∑ S, if i ∈ S then q S else 0) = x i) ∧
      (∀ S, q S ≠ 0 → S ≠ ∅ →
        ∃ a : K, ∀ i ∈ S, classOf i = a) ∧
      (∀ a : K,
        (∑ S : Finset I,
          if S ≠ ∅ ∧ (∀ i ∈ S, classOf i = a) then q S else 0) ≤
          (∑ i, if classOf i = a then x i else 0) /
            (capacity a : ℝ) + M) := by
  classical
  let classMass : K → ℝ := fun a ↦
    ∑ i, if classOf i = a then x i else 0
  let p : K → ℝ := fun a ↦
    classMass a / (capacity a : ℝ) + M
  have hclassMass0 : ∀ a, 0 ≤ classMass a := by
    intro a
    apply Finset.sum_nonneg
    intro i _hi
    split
    · exact hx0 i
    · exact le_rfl
  have hp0 : ∀ a, 0 ≤ p a := by
    intro a
    exact add_nonneg (div_nonneg (hclassMass0 a)
      (Nat.cast_nonneg (capacity a))) hM0
  have hchargeEq :
      (∑ a, classMass a / (capacity a : ℝ)) =
        ∑ i, x i / (capacity (classOf i) : ℝ) := by
    calc
      (∑ a, classMass a / (capacity a : ℝ)) =
          ∑ a, ∑ i,
            if classOf i = a then x i / (capacity a : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hi : classOf i = a <;> simp [classMass, hi]
      _ = ∑ i, ∑ a,
          if classOf i = a then x i / (capacity a : ℝ) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ i, x i / (capacity (classOf i) : ℝ) := by simp
  have hpsum : ∑ a, p a ≤ 1 := by
    calc
      (∑ a, p a) =
          (∑ a, classMass a / (capacity a : ℝ)) +
            (Fintype.card K : ℝ) * M := by
        simp [p, Finset.sum_add_distrib]
      _ = (∑ i, x i / (capacity (classOf i) : ℝ)) +
            (Fintype.card K : ℝ) * M := by rw [hchargeEq]
      _ ≤ 1 := hbudget
  have hxpoint : ∀ i, x i ≤ p (classOf i) := by
    intro i
    exact (hxM i).trans (le_add_of_nonneg_left
      (div_nonneg (hclassMass0 (classOf i))
        (Nat.cast_nonneg (capacity (classOf i)))))
  have hxclass : ∀ a,
      (∑ i, if classOf i = a then x i else 0) ≤
        (capacity a : ℝ) * p a := by
    intro a
    have hcap : (0 : ℝ) < capacity a := by
      exact_mod_cast hcapacity a
    change classMass a ≤ (capacity a : ℝ) *
      (classMass a / (capacity a : ℝ) + M)
    rw [mul_add]
    have hcancel : (capacity a : ℝ) *
        (classMass a / (capacity a : ℝ)) = classMass a := by
      field_simp [hcap.ne']
    rw [hcancel]
    exact le_add_of_nonneg_right (mul_nonneg hcap.le hM0)
  exact sizeClasses_singleClassDistribution capacity hcapacity classOf
    w x p hp0 hpsum hw0 hw hx0 hxpoint hxclass

end SingleClassLocalPolytope

end WeightedEdgeColoring

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- A star law whose every positive-probability nonempty outcome uses one
class.  Taking the class to be a label--size pair records the label in the
same random choice as the feasible star subset. -/
def IsAverageOfSingleClassStarFeasibleSets
    (v : G.V) {K : Type*} (classOf : G.StarEdge v → K)
    (x : G.StarEdge v → ℝ) : Prop :=
  ∃ (m : ℕ) (p : Fin m → ℝ)
      (outcome : Fin m → Finset (G.StarEdge v)),
    (∀ i, 0 ≤ p i) ∧
    (∑ i, p i = 1) ∧
    (∀ i, G.StarFeasible v (outcome i)) ∧
    (∀ e, (∑ i, if e ∈ outcome i then p i else 0) = x e) ∧
    (∀ i, p i ≠ 0 → outcome i ≠ ∅ →
      ∃ a : K, ∀ e ∈ outcome i, classOf e = a)

/-- Convert a distribution on finite subsets without forgetting the class
of each outcome. -/
theorem singleClassStarAverage_of_subsetDistribution
    {v : G.V} {K : Type*} (classOf : G.StarEdge v → K)
    (x : G.StarEdge v → ℝ)
    (q : Finset (G.StarEdge v) → ℝ)
    (hq0 : ∀ S, 0 ≤ q S)
    (hqtotal : ∑ S, q S = 1)
    (hqfeasible : ∀ S, q S ≠ 0 → G.StarFeasible v S)
    (hqmarg : ∀ e, (∑ S, if e ∈ S then q S else 0) = x e)
    (hqclass : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : K, ∀ e ∈ S, classOf e = a) :
    G.IsAverageOfSingleClassStarFeasibleSets v classOf x := by
  classical
  let equiv := Fintype.equivFin (Finset (G.StarEdge v))
  let m := Fintype.card (Finset (G.StarEdge v))
  let raw : Fin m → Finset (G.StarEdge v) := fun i ↦ equiv.symm i
  let outcome : Fin m → Finset (G.StarEdge v) := fun i ↦
    if q (raw i) = 0 then ∅ else raw i
  let p : Fin m → ℝ := fun i ↦ q (raw i)
  refine ⟨m, p, outcome, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hq0 (raw i)
  · calc
      (∑ i, p i) = ∑ S : Finset (G.StarEdge v), q S := by
        simpa [p, raw, equiv, m] using equiv.symm.sum_comp q
      _ = 1 := hqtotal
  · intro i
    by_cases hi : q (raw i) = 0
    · simp [StarFeasible, outcome, hi]
    · simpa [outcome, hi] using hqfeasible (raw i) hi
  · intro e
    calc
      (∑ i, if e ∈ outcome i then p i else 0) =
          ∑ i, if e ∈ raw i then q (raw i) else 0 := by
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hz : q (raw i) = 0 <;>
          simp [outcome, p, hz]
      _ = ∑ S : Finset (G.StarEdge v),
          if e ∈ S then q S else 0 := by
        simpa [raw, equiv, m] using equiv.symm.sum_comp
          (fun S : Finset (G.StarEdge v) ↦ if e ∈ S then q S else 0)
      _ = x e := hqmarg e
  · intro i hpi hSne
    have hraw : q (raw i) ≠ 0 := hpi
    have hEq : outcome i = raw i := by simp [outcome, hraw]
    rw [hEq] at hSne ⊢
    exact hqclass (raw i) hraw hSne

/-- Harmonic charge with a fixed class overhead gives a *single-class*
star law, retaining the information lost in the usual local-polytope API. -/
theorem sizeClasses_singleClassStarAverage_of_charge
    {v : G.V} {K : Type*} [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : G.StarEdge v → K)
    (x : G.StarEdge v → ℝ) (M : ℝ)
    (hw : ∀ e, G.weight e.1 ≤ (1 : ℝ) / capacity (classOf e))
    (hx0 : ∀ e, 0 ≤ x e) (hM0 : 0 ≤ M)
    (hxM : ∀ e, x e ≤ M)
    (hbudget :
      (∑ e, x e / (capacity (classOf e) : ℝ)) +
          (Fintype.card K : ℝ) * M ≤ 1) :
    G.IsAverageOfSingleClassStarFeasibleSets v classOf x := by
  obtain ⟨q, hq0, hqtotal, hqfeasible, hqmarg, hqclass, _hqbudget⟩ :=
    sizeClasses_singleClassDistribution_of_charge
      capacity hcapacity classOf
      (fun e : G.StarEdge v ↦ G.weight e.1) x M
      (fun e ↦ (G.weight_pos e.1).le) hw hx0 hM0 hxM hbudget
  exact G.singleClassStarAverage_of_subsetDistribution classOf x q
    hq0 hqtotal hqfeasible hqmarg hqclass

end WeightedMultigraph
end WeightedEdgeColoring

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

theorem exists_singleClassBoundedProfileLaw {v : G.V} {x : G.StarEdge v → ℝ}
    {K : Type*} (classOf : G.StarEdge v → K)
    (hx : G.IsAverageOfSingleClassStarFeasibleSets v classOf x)
    {s β q r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hq : 0 < q) (hr : 0 < r) :
    ∃ L : G.BoundedProfileLaw x s β q r,
      ∀ k : Fin L.m, L.probability k ≠ 0 → L.outcome k ≠ ∅ →
        ∃ a : K, ∀ e ∈ L.outcome k, classOf e = a := by
  classical
  rcases hx with ⟨m, p, outcome, hp, hpsum, hfeasible, horiginal, hclass⟩
  have hmarginal : ∀ e,
      (∑ k, ((∑ i, G.rawSlotOccurrence s (p k) β (outcome k) e i) +
        G.rawReservoirOccurrence s (p k) β (outcome k) e)) = s * x e :=
    fun e ↦ G.rawOccurrence_marginal s β p outcome x horiginal e
  have hslot : ∀ k i,
      (∑ e, G.rawSlotOccurrence s (p k) β (outcome k) e i) ≤ p k :=
    fun k i ↦ G.rawSlotOccurrence_capacity hs hs1 (hp k) (outcome k) i
  have hreservoir : ∀ k,
      (∑ e, G.weight e.1 * G.rawReservoirOccurrence s (p k) β (outcome k) e) ≤
        p k * (G.rawProfile β (outcome k)).reservoir :=
    fun k ↦ G.rawReservoirOccurrence_capacity hs hs1 (hp k) (hfeasible k)
  have hmass : ∀ b ∈ G.lawSlotSupport β outcome,
      0 ≤ G.lawSlotMass p β outcome b := by
    intro b _hb
    exact G.lawSlotMass_nonneg p hp β outcome b
  have htotal :
      (∑ b ∈ G.lawSlotSupport β outcome, G.lawSlotMass p β outcome b) ≤
        1 / β :=
    G.sum_lawSlotMass_le_inv p hp hpsum hβ outcome hfeasible
  rcases exists_keptSizes_floor (G.lawSlotSupport β outcome)
      (G.lawSlotMass p β outcome) hmass htotal hq with
    ⟨kept, round, hround, hmono, hrange, hgreatest, hcell, hcard⟩
  have hroundExpectation :
      (∑ k, p k * roundReservoir r (G.rawProfile β (outcome k)).reservoir) ≥
        (∑ k, p k * (G.rawProfile β (outcome k)).reservoir) - r :=
    sum_roundReservoir_ge_sub hr p
      (fun k ↦ (G.rawProfile β (outcome k)).reservoir) hp
      (fun k ↦ G.rawProfile_reservoir_nonneg (hfeasible k)) hpsum
  refine ⟨⟨m, p, outcome, hp, hpsum, hfeasible, horiginal, hmarginal, hslot,
    hreservoir, kept, round, hround, hmono, hrange, hgreatest, hcell,
    hcard, ?_, ?_, ?_, hroundExpectation, ?_⟩, ?_⟩
  · intro t ht
    exact scaled_tail_le_rounded_plus_repair
      (G.lawSlotSupport β outcome) kept (G.lawSlotMass p β outcome) round
      hround hmass hmono hrange hgreatest hq hs ht hcell
  · intro k
    exact G.rawProfile_safe_after_roundReservoir hr (hfeasible k)
  · intro k
    exact roundReservoir_eq_zero_or_ge hr
      (G.rawProfile_reservoir_nonneg (hfeasible k))
  · have hdemand_eq :
        (∑ e, if G.weight e.1 < β then G.weight e.1 * (s * x e) else 0) =
          ∑ k, ∑ e, G.weight e.1 *
            G.rawReservoirOccurrence s (p k) β (outcome k) e := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he_univ
      by_cases hetiny : G.weight e.1 < β
      · have hnotlarge : ∀ k, e ∉ G.largeEdges β (outcome k) := by
          intro k he
          exact (not_lt_of_ge (G.mem_largeEdges.mp he).2) hetiny
        have hslot_zero : ∀ k,
            (∑ i, G.rawSlotOccurrence s (p k) β (outcome k) e i) = 0 := by
          intro k
          rw [G.sum_rawSlotOccurrence]
          simp [hnotlarge k]
        have hres_marginal :
            (∑ k, G.rawReservoirOccurrence s (p k) β (outcome k) e) =
              s * x e := by
          calc
            (∑ k, G.rawReservoirOccurrence s (p k) β (outcome k) e) =
                ∑ k, ((∑ i,
                  G.rawSlotOccurrence s (p k) β (outcome k) e i) +
                    G.rawReservoirOccurrence s (p k) β (outcome k) e) := by
              apply Finset.sum_congr rfl
              intro k _hk
              rw [hslot_zero k, zero_add]
            _ = s * x e := hmarginal e
        simp only [hetiny, if_true]
        rw [← Finset.mul_sum, hres_marginal]
      · have hres_zero : ∀ k,
            G.rawReservoirOccurrence s (p k) β (outcome k) e = 0 := by
          intro k
          unfold rawReservoirOccurrence
          split
          next he => exact (hetiny (G.mem_tinyEdges.mp he).2).elim
          next => rfl
        simp [hetiny, hres_zero]
    have hscaled_capacity :
        (∑ k, ∑ e, G.weight e.1 *
            G.rawReservoirOccurrence s (p k) β (outcome k) e) ≤
          s * (∑ k, p k * (G.rawProfile β (outcome k)).reservoir) := by
      calc
        (∑ k, ∑ e, G.weight e.1 *
            G.rawReservoirOccurrence s (p k) β (outcome k) e) ≤
            ∑ k, (s * p k) * (G.rawProfile β (outcome k)).reservoir := by
          apply Finset.sum_le_sum
          intro k _hk
          rw [G.weighted_rawReservoirOccurrence]
          exact mul_le_mul_of_nonneg_left
            (G.tinyWeight_le_rawProfile_reservoir (hfeasible k))
            (mul_nonneg hs (hp k))
        _ = s * (∑ k, p k * (G.rawProfile β (outcome k)).reservoir) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _hk
          ring
    rw [hdemand_eq]
    have hscaled_round := mul_le_mul_of_nonneg_left hroundExpectation hs
    linarith

  · exact hclass

end WeightedMultigraph
end WeightedEdgeColoring

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- The large- and tiny-edge transports can be built from a fixed profile
law, so they do not erase its coupled class witness. -/
theorem exists_singleClassBoundedProfileRealization
    {v : G.V} {x : G.StarEdge v → ℝ} {K : Type*}
    (classOf : G.StarEdge v → K)
    (hx : G.IsAverageOfSingleClassStarFeasibleSets v classOf x)
    {s β q r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hq : 0 < q) (hr : 0 < r) :
    ∃ R : G.BoundedProfileRealization x s β q r hβ hr,
      ∀ k : Fin R.law.m,
        R.law.probability k ≠ 0 → R.law.outcome k ≠ ∅ →
          ∃ a : K, ∀ e ∈ R.law.outcome k, classOf e = a := by
  classical
  obtain ⟨L, hclass⟩ := G.exists_singleClassBoundedProfileLaw
    classOf hx hs hs1 hβ hq hr
  rcases BoundedProfileLaw.exists_profileLargeTransport (G := G) L hs hβ hq hr with
    ⟨largeAssign, hlarge0, hlargeSupport, hlargeRow, hlargeCol⟩
  rcases BoundedProfileLaw.exists_profileTinyTransport (G := G) L hs hβ hr with
    ⟨tinyAssign, htiny0, htinyRow, htinyCol⟩
  refine ⟨⟨L, G.roundedProfileIndex_card_le_parameters L hβ hr,
    largeAssign, hlarge0, hlargeSupport, hlargeRow, hlargeCol,
    tinyAssign, htiny0, htinyRow, htinyCol⟩, ?_⟩
  exact hclass

/-- A local harmonic-charge bound supplies a rounded profile realization
whose underlying outcomes are coupled to one class. -/
theorem sizeClasses_singleClassRealization_of_charge
    {v : G.V} {K : Type*} [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (classOf : G.StarEdge v → K)
    (x : G.StarEdge v → ℝ) (M : ℝ)
    (hw : ∀ e, G.weight e.1 ≤ (1 : ℝ) / capacity (classOf e))
    (hx0 : ∀ e, 0 ≤ x e) (hM0 : 0 ≤ M)
    (hxM : ∀ e, x e ≤ M)
    (hbudget :
      (∑ e, x e / (capacity (classOf e) : ℝ)) +
          (Fintype.card K : ℝ) * M ≤ 1)
    {s β q r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hq : 0 < q) (hr : 0 < r) :
    ∃ R : G.BoundedProfileRealization x s β q r hβ hr,
      ∀ k : Fin R.law.m,
        R.law.probability k ≠ 0 → R.law.outcome k ≠ ∅ →
          ∃ a : K, ∀ e ∈ R.law.outcome k, classOf e = a := by
  exact G.exists_singleClassBoundedProfileRealization classOf
    (G.sizeClasses_singleClassStarAverage_of_charge
      capacity hcapacity classOf x M hw hx0 hM0 hxM hbudget)
    hs hs1 hβ hq hr

end WeightedMultigraph
end WeightedEdgeColoring

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- Explicit endpoint-label form of the coupled local construction.  The
factor in the budget is the number of label--size pairs and therefore stays
constant when those two alphabets are fixed. -/
theorem sizeClasses_singleLabelRealization_of_charge
    {v : G.V} {Label K : Type*}
    [Fintype Label] [DecidableEq Label]
    [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (edgeLabel : G.StarEdge v → Label)
    (sizeClass : G.StarEdge v → K)
    (x : G.StarEdge v → ℝ) (M : ℝ)
    (hw : ∀ e, G.weight e.1 ≤ (1 : ℝ) / capacity (sizeClass e))
    (hx0 : ∀ e, 0 ≤ x e) (hM0 : 0 ≤ M)
    (hxM : ∀ e, x e ≤ M)
    (hbudget :
      (∑ e, x e / (capacity (sizeClass e) : ℝ)) +
          (Fintype.card (Label × K) : ℝ) * M ≤ 1)
    {s β q r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hq : 0 < q) (hr : 0 < r) :
    ∃ R : G.BoundedProfileRealization x s β q r hβ hr,
      ∀ k : Fin R.law.m,
        R.law.probability k ≠ 0 → R.law.outcome k ≠ ∅ →
          ∃ label : Label, ∀ e ∈ R.law.outcome k,
            edgeLabel e = label := by
  let classOf : G.StarEdge v → Label × K :=
    fun e ↦ (edgeLabel e, sizeClass e)
  let capacity' : Label × K → ℕ := fun a ↦ capacity a.2
  have hcapacity' : ∀ a, 0 < capacity' a := fun a ↦ hcapacity a.2
  obtain ⟨R, hclass⟩ := G.sizeClasses_singleClassRealization_of_charge
    capacity' hcapacity' classOf x M hw hx0 hM0 hxM hbudget
    hs hs1 hβ hq hr
  refine ⟨R, ?_⟩
  intro k hk hne
  obtain ⟨a, ha⟩ := hclass k hk hne
  exact ⟨a.1, fun e he ↦ congrArg Prod.fst (ha e he)⟩

end WeightedMultigraph
end WeightedEdgeColoring

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- Before global profile transportation, a positive ordinary-slot
occurrence stays inside its sampled class. -/
theorem BoundedProfileLaw.rawSlotOccurrence_singleClass
    {v : G.V} {x : G.StarEdge v → ℝ} {K : Type*}
    (classOf : G.StarEdge v → K)
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hs : 0 ≤ s)
    (hclass : ∀ k : Fin L.m,
      L.probability k ≠ 0 → L.outcome k ≠ ∅ →
        ∃ a : K, ∀ e ∈ L.outcome k, classOf e = a)
    (k : Fin L.m) (e i : G.StarEdge v)
    (hpos : 0 < G.rawSlotOccurrence s (L.probability k) β
      (L.outcome k) e i) :
    ∃ a : K, classOf e = a ∧
      ∀ f ∈ L.outcome k, classOf f = a := by
  obtain ⟨hei, hi, _⟩ := G.rawSlotOccurrence_support hpos
  have hiLarge : i ∈ G.largeEdges β (L.outcome k) := hi
  have hie : e ∈ L.outcome k := by
    rw [hei]
    exact (G.mem_largeEdges.mp hiLarge).1
  have hsp : 0 < s * L.probability k := by
    simpa [rawSlotOccurrence, hei, hiLarge] using hpos
  have hp : 0 < L.probability k := by
    by_contra hnot
    have hpnonpos : L.probability k ≤ 0 := le_of_not_gt hnot
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hs hpnonpos)) hsp
  have hne : L.outcome k ≠ ∅ := by
    intro hz
    rw [hz] at hie
    simpa using hie
  obtain ⟨a, ha⟩ := hclass k hp.ne' hne
  exact ⟨a, ha e hie, ha⟩

/-- The same preservation holds for a raw tiny-edge reservoir occurrence. -/
theorem BoundedProfileLaw.rawReservoirOccurrence_singleClass
    {v : G.V} {x : G.StarEdge v → ℝ} {K : Type*}
    (classOf : G.StarEdge v → K)
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (hs : 0 ≤ s)
    (hclass : ∀ k : Fin L.m,
      L.probability k ≠ 0 → L.outcome k ≠ ∅ →
        ∃ a : K, ∀ e ∈ L.outcome k, classOf e = a)
    (k : Fin L.m) (e : G.StarEdge v)
    (hpos : 0 < G.rawReservoirOccurrence s (L.probability k) β
      (L.outcome k) e) :
    ∃ a : K, classOf e = a ∧
      ∀ f ∈ L.outcome k, classOf f = a := by
  have heTiny : e ∈ G.tinyEdges β (L.outcome k) := by
    unfold rawReservoirOccurrence at hpos
    split at hpos
    next hmem => exact hmem
    next => simp at hpos
  have he : e ∈ L.outcome k := (G.mem_tinyEdges.mp heTiny).1
  have hsp : 0 < s * L.probability k := by
    simpa [rawReservoirOccurrence, heTiny] using hpos
  have hp : 0 < L.probability k := by
    by_contra hnot
    have hpnonpos : L.probability k ≤ 0 := le_of_not_gt hnot
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hs hpnonpos)) hsp
  have hne : L.outcome k ≠ ∅ := by
    intro hz
    rw [hz] at he
    simpa using he
  obtain ⟨a, ha⟩ := hclass k hp.ne' hne
  exact ⟨a, ha e he, ha⟩

end WeightedMultigraph
end WeightedEdgeColoring

namespace WeightedEdgeColoring
namespace WeightedMultigraph

variable (G : WeightedMultigraph)

/-- Filtering each sampled feasible star set by a fixed endpoint label
preserves feasibility and gives the exact restricted marginal vector. -/
theorem labelRestrictedStarAverage
    {v : G.V} {Label : Type*} [DecidableEq Label]
    (edgeLabel : G.StarEdge v → Label) (label : Label)
    {x : G.StarEdge v → ℝ}
    (hx : G.IsAverageOfStarFeasibleSets v x) :
    G.IsAverageOfStarFeasibleSets v
      (fun e ↦ if edgeLabel e = label then x e else 0) := by
  classical
  rcases hx with ⟨m, p, outcome, hp0, hpsum, hfeasible, hmarg⟩
  let restricted : Fin m → Finset (G.StarEdge v) :=
    fun k ↦ (outcome k).filter (fun e ↦ edgeLabel e = label)
  refine ⟨m, p, restricted, hp0, hpsum, ?_, ?_⟩
  · intro k
    unfold StarFeasible at hfeasible ⊢
    calc
      (∑ e ∈ restricted k, G.weight e.1) ≤
          ∑ e ∈ outcome k, G.weight e.1 := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro e _he
        by_cases hlabel : edgeLabel e = label
        · simp [hlabel]
        · simpa [hlabel] using (G.weight_pos e.1).le
      _ ≤ 1 := hfeasible k
  · intro e
    by_cases he : edgeLabel e = label
    · simpa [restricted, he] using hmarg e
    · simp [restricted, he]

/-- Existing profile construction may be run independently on every
endpoint-label restriction.  Its transported ordinary slots and reservoirs
then have exactly the same label as every positive assigned edge. -/
theorem exists_labelRestrictedProfileRealizations
    {v : G.V} {Label : Type*} [Fintype Label] [DecidableEq Label]
    (edgeLabel : G.StarEdge v → Label)
    {x : G.StarEdge v → ℝ}
    (hx : G.IsAverageOfStarFeasibleSets v x)
    {s β q r : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hq : 0 < q) (hr : 0 < r) :
    ∃ R : ∀ label : Label,
      G.BoundedProfileRealization
        (fun e ↦ if edgeLabel e = label then x e else 0)
        s β q r hβ hr,
      (∀ label e j, 0 < (R label).largeAssign e j →
        edgeLabel e = label) ∧
      (∀ label e P, 0 < (R label).tinyAssign e P →
        edgeLabel e = label) := by
  classical
  have hR : ∀ label : Label,
      Nonempty (G.BoundedProfileRealization
        (fun e ↦ if edgeLabel e = label then x e else 0)
        s β q r hβ hr) := by
    intro label
    exact G.exists_boundedProfileRealization
      (G.labelRestrictedStarAverage edgeLabel label hx)
      hs hs1 hβ hq hr
  let R := fun label ↦ Classical.choice (hR label)
  refine ⟨R, ?_, ?_⟩
  · intro label e j hpos
    exact BoundedProfileRealization.positive_largeAssign_respects_support
      G (R label) hs
      (fun e ↦ edgeLabel e = label)
      (fun e he ↦ by
        by_cases h : edgeLabel e = label
        · exact h
        · simp [h] at he)
      e j hpos
  · intro label e P hpos
    exact BoundedProfileRealization.positive_tinyAssign_respects_support
      G (R label) hs
      (fun e ↦ edgeLabel e = label)
      (fun e he ↦ by
        by_cases h : edgeLabel e = label
        · exact h
        · simp [h] at he)
      e P hpos

end WeightedMultigraph
end WeightedEdgeColoring

namespace WeightedEdgeColoring

section LabelClassBudget

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Sum the one-class outcome bounds over size classes.  This is the
probability of using one endpoint label in a color, including only nonempty
outcomes, and is bounded by the charge allocated to that label. -/
theorem singleClass_labelMass_le_sum_classBudget
    {Label K : Type*} [Fintype K] [DecidableEq K]
    [DecidableEq Label]
    (classOf : I → Label × K)
    (q : Finset I → ℝ) (hq0 : ∀ S, 0 ≤ q S)
    (hsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label × K, ∀ i ∈ S, classOf i = a)
    (p : Label × K → ℝ)
    (hclassBudget : ∀ a : Label × K,
      (∑ S : Finset I,
        if S ≠ ∅ ∧ (∀ i ∈ S, classOf i = a) then q S else 0) ≤
          p a)
    (label : Label) :
    (∑ S : Finset I,
      if S ≠ ∅ ∧ (∀ i ∈ S, (classOf i).1 = label) then q S else 0) ≤
        ∑ a : K, p (label, a) := by
  classical
  have hpoint : ∀ S : Finset I,
      (if S ≠ ∅ ∧ (∀ i ∈ S, (classOf i).1 = label) then q S else 0) ≤
        ∑ a : K,
          if S ≠ ∅ ∧ (∀ i ∈ S, classOf i = (label, a)) then q S else 0 := by
    intro S
    by_cases hc : S ≠ ∅ ∧ (∀ i ∈ S, (classOf i).1 = label)
    · by_cases hq : q S = 0
      · simp [hq]
      · obtain ⟨b, hb⟩ := hsingle S hq hc.1
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hc.1
        have hblabel : b.1 = label := by
          rw [← hb i hi]
          exact hc.2 i hi
        have hpair : b = (label, b.2) := by
          cases b
          simp_all
        have hclass : ∀ j ∈ S, classOf j = (label, b.2) := by
          intro j hj
          rw [hb j hj, hpair]
        have hterm :
            (if S ≠ ∅ ∧ (∀ j ∈ S, classOf j = (label, b.2))
              then q S else 0) = q S := by
          exact if_pos ⟨hc.1, hclass⟩
        have hnonneg : ∀ a : K,
            0 ≤ if S ≠ ∅ ∧ (∀ j ∈ S, classOf j = (label, a))
              then q S else 0 := by
          intro a
          split
          · exact hq0 S
          · exact le_rfl
        have hsingleTerm := Finset.single_le_sum
          (fun a _ ↦ hnonneg a) (Finset.mem_univ b.2)
        rw [hterm] at hsingleTerm
        rw [if_pos hc]
        exact hsingleTerm
    · have hnonneg : 0 ≤ ∑ a : K,
          if S ≠ ∅ ∧ (∀ i ∈ S, classOf i = (label, a)) then q S else 0 :=
        Finset.sum_nonneg fun a _ ↦ by
          split
          · exact hq0 S
          · exact le_rfl
      simpa [hc] using hnonneg
  calc
    (∑ S : Finset I,
      if S ≠ ∅ ∧ (∀ i ∈ S, (classOf i).1 = label) then q S else 0) ≤
        ∑ S : Finset I, ∑ a : K,
          if S ≠ ∅ ∧ (∀ i ∈ S, classOf i = (label, a)) then q S else 0 :=
      Finset.sum_le_sum fun S _ ↦ hpoint S
    _ = ∑ a : K, ∑ S : Finset I,
          if S ≠ ∅ ∧ (∀ i ∈ S, classOf i = (label, a)) then q S else 0 :=
      Finset.sum_comm
    _ ≤ ∑ a : K, p (label, a) :=
      Finset.sum_le_sum fun a _ ↦ hclassBudget (label, a)

end LabelClassBudget
end WeightedEdgeColoring

namespace WeightedEdgeColoring

section SingleLabelChargeDistribution

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The charge construction with class index `Label × SizeClass` gives
one-label outcomes and an explicit per-label probability upper bound. -/
theorem sizeClasses_singleLabelDistribution_of_charge
    {Label K : Type*}
    [Fintype Label] [DecidableEq Label]
    [Fintype K] [DecidableEq K]
    (capacity : K → ℕ) (hcapacity : ∀ a, 0 < capacity a)
    (edgeLabel : I → Label) (sizeClass : I → K)
    (w x : I → ℝ) (M : ℝ)
    (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, w i ≤ (1 : ℝ) / capacity (sizeClass i))
    (hx0 : ∀ i, 0 ≤ x i) (hM0 : 0 ≤ M)
    (hxM : ∀ i, x i ≤ M)
    (hbudget :
      (∑ i, x i / (capacity (sizeClass i) : ℝ)) +
          (Fintype.card (Label × K) : ℝ) * M ≤ 1) :
    ∃ q : Finset I → ℝ,
      (∀ S, 0 ≤ q S) ∧
      (∑ S, q S = 1) ∧
      (∀ S, q S ≠ 0 → ∑ i ∈ S, w i ≤ 1) ∧
      (∀ i, (∑ S, if i ∈ S then q S else 0) = x i) ∧
      (∀ S, q S ≠ 0 → S ≠ ∅ →
        ∃ label : Label, ∀ i ∈ S, edgeLabel i = label) ∧
      (∀ label : Label,
        (∑ S : Finset I,
          if S ≠ ∅ ∧ (∀ i ∈ S, edgeLabel i = label) then q S else 0) ≤
          ∑ a : K,
            ((∑ i, if edgeLabel i = label ∧ sizeClass i = a
              then x i else 0) / (capacity a : ℝ) + M)) := by
  classical
  let classOf : I → Label × K := fun i ↦ (edgeLabel i, sizeClass i)
  let capacity' : Label × K → ℕ := fun a ↦ capacity a.2
  obtain ⟨q, hq0, hqsum, hqfeas, hqmarg, hqclass, hqbudget⟩ :=
    sizeClasses_singleClassDistribution_of_charge capacity'
      (fun a ↦ hcapacity a.2) classOf w x M hw0 hw hx0 hM0 hxM hbudget
  refine ⟨q, hq0, hqsum, hqfeas, hqmarg, ?_, ?_⟩
  · intro S hpos hne
    obtain ⟨a, ha⟩ := hqclass S hpos hne
    exact ⟨a.1, fun i hi ↦ congrArg Prod.fst (ha i hi)⟩
  · intro label
    have hbound := singleClass_labelMass_le_sum_classBudget
      classOf q hq0 hqclass
      (fun a : Label × K ↦
        (∑ i, if classOf i = a then x i else 0) /
          (capacity' a : ℝ) + M)
      hqbudget label
    simpa [classOf, capacity'] using hbound

end SingleLabelChargeDistribution
end WeightedEdgeColoring
