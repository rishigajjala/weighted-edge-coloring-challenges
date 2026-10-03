import WeightedEdgeColoring.FiniteExactDemandHarmonicMinimum
import WeightedEdgeColoring.SubtwoHarmonicRanks

/-!
# Minimum cost paid by projected-bin harmonic charges

Repeat an entire projected bin `floor(1/load)` times and divide its mass
by the same integer.  This preserves every type demand exactly, while
charging the bin only `harmonicCharge load`.  Zero-load projections are
handled explicitly.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.BinPackingInstance

noncomputable section
variable {B : BinPackingInstance}

namespace Pattern

def subtwoProjectionLoad (p : B.Pattern) : ℝ :=
  ∑ i : B.Item, (p.multiplicity i : ℝ) * B.weight i

theorem subtwoProjectionLoad_nonneg (p : B.Pattern) : 0 ≤ p.subtwoProjectionLoad :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (B.weight_pos i).le

theorem subtwoProjectionLoad_le_one (p : B.Pattern) : p.subtwoProjectionLoad ≤ 1 := p.capacity

theorem multiplicity_zero_of_subtwoProjectionLoad_zero (p : B.Pattern)
    (hload : p.subtwoProjectionLoad = 0) (i : B.Item) : p.multiplicity i = 0 := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset B.Item))
    (f := fun j => (p.multiplicity j : ℝ) * B.weight j)
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (B.weight_pos j).le) (Finset.mem_univ i)
  change (p.multiplicity i : ℝ) * B.weight i ≤ p.subtwoProjectionLoad at h
  rw [hload] at h
  have hm : (p.multiplicity i : ℝ) = 0 := by
    nlinarith [B.weight_pos i, (Nat.cast_nonneg (p.multiplicity i) : (0 : ℝ) ≤ p.multiplicity i)]
  exact_mod_cast hm

def subtwoProjectionRepetitions (p : B.Pattern) : ℕ :=
  Nat.floor (1 / p.subtwoProjectionLoad)

theorem subtwoProjectionRepetitions_pos (p : B.Pattern)
    (hp : 0 < p.subtwoProjectionLoad) : 0 < p.subtwoProjectionRepetitions := by
  apply Nat.le_floor
  rw [le_div_iff₀ hp]
  simpa using p.subtwoProjectionLoad_le_one

theorem subtwoProjectionRepetitions_load_le (p : B.Pattern) :
    (p.subtwoProjectionRepetitions : ℝ) * p.subtwoProjectionLoad ≤ 1 := by
  rcases eq_or_lt_of_le p.subtwoProjectionLoad_nonneg with h | h
  · rw [← h]; norm_num
  · have hf : (p.subtwoProjectionRepetitions : ℝ) ≤ 1 / p.subtwoProjectionLoad :=
      Nat.floor_le (by positivity)
    exact (le_div_iff₀ h).mp hf

def subtwoRepeatProjection (p : B.Pattern) : B.Pattern where
  multiplicity i := p.subtwoProjectionRepetitions * p.multiplicity i
  capacity := by
    simpa only [Nat.cast_mul, mul_assoc, ← Finset.mul_sum] using
      p.subtwoProjectionRepetitions_load_le

/-- Scaling the repeated pattern by its harmonic charge recovers every
original coordinate, including coordinates of an empty projection. -/
theorem subtwoRepeatProjection_coverage (p : B.Pattern) (i : B.Item) :
    harmonicCharge p.subtwoProjectionLoad * ((p.subtwoRepeatProjection).multiplicity i : ℝ) =
      p.multiplicity i := by
  rcases eq_or_lt_of_le p.subtwoProjectionLoad_nonneg with hw | hw
  · have hm := p.multiplicity_zero_of_subtwoProjectionLoad_zero hw.symm i
    simp [subtwoRepeatProjection, hm]
  · have hk : (p.subtwoProjectionRepetitions : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (p.subtwoProjectionRepetitions_pos hw)
    change (1 / (p.subtwoProjectionRepetitions : ℝ)) *
      ((p.subtwoProjectionRepetitions * p.multiplicity i : ℕ) : ℝ) = _
    push_cast
    field_simp

end Pattern

namespace ExactDemandPatternCover

variable {demand : B.Item → ℕ} {J : Type*} [Fintype J] [DecidableEq J]

def subtwoCoverOfProjectedBins (pattern : J → B.Pattern) (mass : J → ℝ)
    (hmass : ∀ j, 0 ≤ mass j)
    (hcovers : ∀ i : B.Item, (∑ j, mass j * ((pattern j).multiplicity i : ℝ)) = demand i) :
    B.ExactDemandPatternCover demand :=
  ofFinitePatterns (fun j => (pattern j).subtwoRepeatProjection)
    (fun j => mass j * harmonicCharge (pattern j).subtwoProjectionLoad)
    (fun j => mul_nonneg (hmass j) (harmonicCharge_nonneg _)) (by
      intro i
      calc
        _ = ∑ j, mass j * ((pattern j).multiplicity i : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_assoc, Pattern.subtwoRepeatProjection_coverage]
        _ = demand i := hcovers i)

theorem subtwoCoverOfProjectedBins_cost (pattern : J → B.Pattern) (mass : J → ℝ)
    (hmass : ∀ j, 0 ≤ mass j)
    (hcovers : ∀ i : B.Item, (∑ j, mass j * ((pattern j).multiplicity i : ℝ)) = demand i) :
    (subtwoCoverOfProjectedBins pattern mass hmass hcovers).cost =
      ∑ j, mass j * harmonicCharge (pattern j).subtwoProjectionLoad := by
  apply ofFinitePatterns_cost

/-- A minimum exact-demand cover is bounded by the harmonic charge of
the physical *projection loads*, rather than the charges of individual
items in those projections. -/
theorem subtwo_cost_le_projected_charge
    (C : B.ExactDemandPatternCover demand) (hmin : C.IsMinimumCost)
    (pattern : J → B.Pattern) (mass : J → ℝ)
    (hmass : ∀ j, 0 ≤ mass j)
    (hcovers : ∀ i : B.Item, (∑ j, mass j * ((pattern j).multiplicity i : ℝ)) = demand i) :
    C.cost ≤ ∑ j, mass j * harmonicCharge (pattern j).subtwoProjectionLoad := by
  calc
    _ ≤ (subtwoCoverOfProjectedBins pattern mass hmass hcovers).cost := hmin _
    _ = _ := subtwoCoverOfProjectedBins_cost pattern mass hmass hcovers

theorem subtwo_cost_le_packing_projection_charge
    (C : B.ExactDemandPatternCover demand) (hmin : C.IsMinimumCost)
    {n : ℕ} (P : PackingCertificate demand n) :
    C.cost ≤ ∑ j : Fin n, harmonicCharge (P.pattern j).subtwoProjectionLoad := by
  have h := C.subtwo_cost_le_projected_charge hmin P.pattern (fun _ => 1)
    (fun _ => zero_le_one) (by
      intro i
      simp only [one_mul]
      exact_mod_cast P.covers_exact i)
  simpa using h

end ExactDemandPatternCover
end
end WeightedEdgeColoring.BinPackingInstance
