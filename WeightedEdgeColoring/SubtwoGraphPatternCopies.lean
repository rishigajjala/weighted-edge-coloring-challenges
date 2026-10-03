import WeightedEdgeColoring.SubtwoGraphPriceInputs
import WeightedEdgeColoring.SubtwoHarmonicRanks

/-!
# Feasible copies and the zero-price case

A local bin and its small projected pieces have a total-load bound.
We turn that bound into actual repeated weighted patterns.  Combining
them with a pattern on disjoint vertices proves the copy-price rows.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

namespace SubtwoWeightedPattern

def ofTotalLoad (m : G.E → ℕ)
    (hload : (∑ e : G.E, (m e : ℝ) * G.weight e) ≤ 1) : G.SubtwoWeightedPattern := by
  refine ⟨m, ?_⟩
  intro v
  refine le_trans (Finset.sum_le_sum ?_) hload
  intro e he
  dsimp only
  split
  · rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (G.weight_pos e).le

def single (e : G.E) : G.SubtwoWeightedPattern :=
  ofTotalLoad G (fun f => if f = e then 1 else 0) (by
    simpa only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using G.weight_le_one e)

theorem single_price (price : G.E → ℝ) (e : G.E) :
    (∑ f : G.E, price f * ((single G e).val f : ℝ)) = price e := by
  simp [single, ofTotalLoad, mul_ite]

def copiesOfTotalLoad (p : G.SubtwoWeightedPattern) (k : ℕ)
    (hload : (k : ℝ) * (∑ e : G.E, (p.val e : ℝ) * G.weight e) ≤ 1) :
    G.SubtwoWeightedPattern :=
  ofTotalLoad G (fun e => k * p.val e) (by
    simpa only [Nat.cast_mul, mul_assoc, ← Finset.mul_sum] using hload)

theorem copiesOfTotalLoad_price (p : G.SubtwoWeightedPattern) (k : ℕ)
    (hload : (k : ℝ) * (∑ e : G.E, (p.val e : ℝ) * G.weight e) ≤ 1)
    (price : G.E → ℝ) :
    (∑ e : G.E, price e * ((p.copiesOfTotalLoad G k hload).val e : ℝ)) =
      (k : ℝ) * ∑ e : G.E, price e * (p.val e : ℝ) := by
  simp only [copiesOfTotalLoad, ofTotalLoad, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem restrictTo_fixed (p : G.SubtwoWeightedPattern) (S : Finset G.V)
    (hsupport : ∀ e, p.val e ≠ 0 → G.fst e ∈ S ∧ G.snd e ∈ S) :
    p.restrictTo G S = p := by
  apply Subtype.ext
  funext e
  by_cases he : p.val e = 0
  · simp [restrictTo, ofLE, he]
  · simp [restrictTo, ofLE, hsupport e he]

theorem copiesOfTotalLoad_supported (p : G.SubtwoWeightedPattern) (k : ℕ)
    (hload : (k : ℝ) * (∑ e : G.E, (p.val e : ℝ) * G.weight e) ≤ 1)
    (S : Finset G.V) (hsupport : ∀ e, p.val e ≠ 0 → G.fst e ∈ S ∧ G.snd e ∈ S) :
    (p.copiesOfTotalLoad G k hload).restrictTo G S = p.copiesOfTotalLoad G k hload := by
  apply restrictTo_fixed
  intro e he
  apply hsupport e
  intro hp
  exact he (by simp [copiesOfTotalLoad, ofTotalLoad, hp])

theorem zero_of_totalLoad_zero (p : G.SubtwoWeightedPattern)
    (hload : (∑ e : G.E, (p.val e : ℝ) * G.weight e) = 0) : ∀ e, p.val e = 0 := by
  intro e
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset G.E)) (f := fun f => (p.val f : ℝ) * G.weight f)
    (fun f _ => mul_nonneg (Nat.cast_nonneg _) (G.weight_pos f).le) (Finset.mem_univ e)
  rw [hload] at hsingle
  have hzero : (p.val e : ℝ) * G.weight e = 0 :=
    le_antisymm hsingle (mul_nonneg (Nat.cast_nonneg _) (G.weight_pos e).le)
  have hc : (p.val e : ℝ) = 0 := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (G.weight_pos e))
  exact_mod_cast hc

end SubtwoWeightedPattern

theorem subtwoColorPriceMax_nonneg (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) :
    0 ≤ G.subtwoColorPriceMax price :=
  Subtwo.paletteMaxScore_nonneg G.subtwoReservedColorPattern
    G.subtwoReservedColorPattern_nonneg price hp none

theorem subtwo_edge_price_le (price : G.E → ℝ) (e : G.E) :
    price e ≤ G.subtwoColorPriceMax price := by
  have h := Subtwo.patternPrice_le_paletteMaxScore G.subtwoReservedColorPattern
    price none (SubtwoWeightedPattern.single G e)
  change (∑ f, price f * ((SubtwoWeightedPattern.single G e).val f : ℝ)) ≤ _ at h
  rwa [SubtwoWeightedPattern.single_price] at h

/-- Normalization loses no nonzero nonnegative price vector. -/
theorem subtwoColorPriceMax_eq_zero_iff (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) :
    G.subtwoColorPriceMax price = 0 ↔ ∀ e, price e = 0 := by
  constructor
  · intro h e
    exact le_antisymm (by simpa [h] using G.subtwo_edge_price_le price e) (hp e)
  · intro h
    simp [subtwoColorPriceMax, Subtwo.paletteMaxScore, h]

/-- A zero unrestricted maximum makes the palette dual inequality an
identity, so the nonzero branch may safely divide all prices by it. -/
theorem subtwo_palette_charge_zero (price demand : G.E → ℝ) (q : G.V → ℝ) (κ : ℝ)
    (hp : ∀ e, 0 ≤ price e) (hR : G.subtwoColorPriceMax price = 0) :
    (∑ e : G.E, price e * demand e) +
      (∑ v : G.V, q v * (G.subtwoColorPriceMax price - G.subtwoAvoidingPriceMax price v)) =
        κ * G.subtwoColorPriceMax price := by
  have hz := (G.subtwoColorPriceMax_eq_zero_iff price hp).mp hR
  simp [hR, hz, subtwoAvoidingPriceMax, Subtwo.paletteMaxScore]

/-- Copy-price inequality from an actual projected pattern and a disjoint
complementary set. Taking `k = 1,2,3` gives the shared-pair price rows. -/
theorem subtwo_pattern_copies_complement_price
    (p : G.SubtwoWeightedPattern) (k : ℕ) (S T : Finset G.V)
    (hST : Disjoint S T)
    (hsupport : ∀ e, p.val e ≠ 0 → G.fst e ∈ S ∧ G.snd e ∈ S)
    (hload : (k : ℝ) * (∑ e : G.E, (p.val e : ℝ) * G.weight e) ≤ 1)
    (price : G.E → ℝ) :
    (k : ℝ) * (∑ e : G.E, price e * (p.val e : ℝ)) + G.subtwoSupportedPriceMax T price ≤
      G.subtwoColorPriceMax price := by
  let q := Subtwo.paletteMaximizer (G.subtwoSupportedColorPattern T) price ()
  let pk := p.copiesOfTotalLoad G k hload
  have h := Subtwo.patternPrice_le_paletteMaxScore G.subtwoReservedColorPattern
    price none (pk.addDisjoint G q S T hST)
  change (∑ e, price e * ((pk.addDisjoint G q S T hST).val e : ℝ)) ≤
    G.subtwoColorPriceMax price at h
  rw [pk.addDisjoint_price G q S T hST price] at h
  have hfixed : pk.restrictTo G S = pk := p.copiesOfTotalLoad_supported G k hload S hsupport
  rw [hfixed, p.copiesOfTotalLoad_price G k hload price] at h
  exact h

/-- The harmonic packet-price bound is realized by repeating the whole
projected packet `floor(1/load)` times. No individual edge is assumed
heavy, and the pattern may contain several edge types. -/
theorem subtwo_pattern_price_le_harmonic_charge
    (p : G.SubtwoWeightedPattern) (S : Finset G.V)
    (hsupport : ∀ e, p.val e ≠ 0 → G.fst e ∈ S ∧ G.snd e ∈ S)
    (hload : (∑ e : G.E, (p.val e : ℝ) * G.weight e) ≤ 1)
    (price : G.E → ℝ) :
    (∑ e : G.E, price e * (p.val e : ℝ)) ≤
      G.subtwoSupportedPriceMax S price *
        harmonicCharge (∑ e : G.E, (p.val e : ℝ) * G.weight e) := by
  let w : ℝ := ∑ e : G.E, (p.val e : ℝ) * G.weight e
  have hw0 : 0 ≤ w := Finset.sum_nonneg fun e _ =>
    mul_nonneg (Nat.cast_nonneg _) (G.weight_pos e).le
  rcases eq_or_lt_of_le hw0 with hw | hw
  · have hp := p.zero_of_totalLoad_zero G hw.symm
    simp [hp, SubtwoHarmonicRanks.harmonicCharge_zero]
  · let k : ℕ := Nat.floor (1 / w)
    have hk1 : 1 ≤ k := by
      apply Nat.le_floor
      rw [le_div_iff₀ hw]
      simpa [w] using hload
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkw : (k : ℝ) * w ≤ 1 := by
      have hfloor : (k : ℝ) ≤ 1 / w := Nat.floor_le (by positivity)
      exact (le_div_iff₀ hw).mp hfloor
    let pk := p.copiesOfTotalLoad G k hkw
    have hscore := Subtwo.patternPrice_le_paletteMaxScore (G.subtwoSupportedColorPattern S)
      price () pk
    change (∑ e, price e * ((pk.restrictTo G S).val e : ℝ)) ≤
      G.subtwoSupportedPriceMax S price at hscore
    have hfixed : pk.restrictTo G S = pk := p.copiesOfTotalLoad_supported G k hkw S hsupport
    rw [hfixed, p.copiesOfTotalLoad_price G k hkw price] at hscore
    change (∑ e, price e * (p.val e : ℝ)) ≤ G.subtwoSupportedPriceMax S price * (1 / (k : ℝ))
    rw [← div_eq_mul_one_div]
    apply (le_div_iff₀ hkR).2
    simpa [mul_comm] using hscore

theorem subtwo_normalized_copies_complement_price
    (p : G.SubtwoWeightedPattern) (k : ℕ) (S T : Finset G.V)
    (hST : Disjoint S T)
    (hsupport : ∀ e, p.val e ≠ 0 → G.fst e ∈ S ∧ G.snd e ∈ S)
    (hload : (k : ℝ) * (∑ e : G.E, (p.val e : ℝ) * G.weight e) ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price) :
    (k : ℝ) * ((∑ e : G.E, price e * (p.val e : ℝ)) / G.subtwoColorPriceMax price) +
      G.subtwoNormalizedSetPrice price T ≤ 1 := by
  unfold subtwoNormalizedSetPrice
  rw [← mul_div_assoc, ← add_div]
  apply (div_le_one hR).2
  exact G.subtwo_pattern_copies_complement_price p k S T hST hsupport hload price

end WeightedEdgeColoring.WeightedMultigraph
