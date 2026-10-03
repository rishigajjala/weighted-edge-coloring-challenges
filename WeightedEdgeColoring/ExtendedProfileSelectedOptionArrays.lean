import WeightedEdgeColoring.ExtendedProfileBlockCandidateCapacityRows
import WeightedEdgeColoring.ExtendedProfileBlockQuadraticBridge
import WeightedEdgeColoring.OptionNormalization

/-!
# Concrete option arrays decoded from a selected block family

The block selector returns one supported word for each vertex and colour
block.  This file flattens those words and writes the resulting equation-(23)
large-slot and tiny-reservoir masses as ordinary arrays indexed by graph
edges and colours.  It also identifies their total mass with the block mass
used by the quadratic estimates.

These are deterministic identities.  No matching or final rounding theorem
is used here.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- The selected equation-(23) mass of one large-edge option. -/
def selectedBlockLargeOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  G.extendedProfileProductOptionMass R0 rho omega e
    (G.decodedExtendedProfileBlockSelection R0 choice (G.fst e) c)
    (G.decodedExtendedProfileBlockSelection R0 choice (G.snd e) c) i j

/-- The selected equation-(23) mass of one tiny-reservoir colour option. -/
def selectedBlockTinyOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k)) : ℝ :=
  G.extendedProfileTinyProductOptionMass R0 rho omega e
    (G.decodedExtendedProfileBlockSelection R0 choice (G.fst e) c)
    (G.decodedExtendedProfileBlockSelection R0 choice (G.snd e) c)

/-- Total selected large and tiny option mass of an edge. -/
def selectedBlockAllOptionMass
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) : ℝ :=
  ∑ c : Fin (B * k),
    ((∑ i, ∑ j,
        G.selectedBlockLargeOptionMass R0 rho omega choice e c i j) +
      G.selectedBlockTinyOptionMass R0 rho omega choice e c)

/-- Fractional load of one selected large slot.  At the first endpoint the
slot is the first place index; at the second endpoint it is the second. -/
def selectedBlockLargeSlotLoad
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileLargeRow
      (n := B * k) (β := β) (q := q) (r := r)) : ℝ :=
  ∑ e : G.E,
    ((if row.1 = G.fst e then
        ∑ j, G.selectedBlockLargeOptionMass
          R0 rho omega choice e row.2.1 row.2.2 j
      else 0) +
      (if row.1 = G.snd e then
        ∑ i, G.selectedBlockLargeOptionMass
          R0 rho omega choice e row.2.1 i row.2.2
      else 0))

/-- Weighted fractional load of one selected tiny reservoir. -/
def selectedBlockTinyReservoirLoad
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileTinyRow (n := B * k)) : ℝ :=
  ∑ e : G.E, if G.Inc row.1 e then
    G.weight e * G.selectedBlockTinyOptionMass
      R0 rho omega choice e row.2
  else 0

theorem selectedBlockLargeOptionMass_nonneg
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r)) :
    0 ≤ G.selectedBlockLargeOptionMass R0 rho omega choice e c i j := by
  exact G.extendedProfileProductOptionMass_nonneg R0
    hs hn hq hr0 hleft homega0 homega1 hrho e _ _ i j

theorem selectedBlockTinyOptionMass_nonneg
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k)) :
    0 ≤ G.selectedBlockTinyOptionMass R0 rho omega choice e c := by
  exact G.extendedProfileTinyProductOptionMass_nonneg R0
    hs hn hq hr0 hleft homega0 homega1 hrho e _ _

theorem selectedBlockAllOptionMass_nonneg
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) :
    0 ≤ G.selectedBlockAllOptionMass R0 rho omega choice e := by
  unfold selectedBlockAllOptionMass
  apply Finset.sum_nonneg
  intro c _hc
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _hi
    apply Finset.sum_nonneg
    intro j _hj
    exact G.selectedBlockLargeOptionMass_nonneg R0 hn hs hq hr0 hleft
      homega0 homega1 hrho choice e c i j
  · exact G.selectedBlockTinyOptionMass_nonneg R0 hn hs hq hr0 hleft
      homega0 homega1 hrho choice e c

/-- Flattening the exact `B × k` colour product does not change total option
mass. -/
theorem selectedBlockAllOptionMass_eq_total
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (rho omega : ℝ) (e : G.E) :
    G.selectedBlockAllOptionMass R0 rho omega choice e =
      G.selectedExtendedProfileTotalOptionMass R0 rho omega choice e := by
  let f : Fin (B * k) → ℝ := fun c ↦
    (∑ i, ∑ j,
      G.selectedBlockLargeOptionMass R0 rho omega choice e c i j) +
      G.selectedBlockTinyOptionMass R0 rho omega choice e c
  have hreindex : (∑ c : Fin (B * k), f c) =
      ∑ p : Fin B × Fin k, f (finProdFinEquiv p) := by
    exact (Equiv.sum_comp finProdFinEquiv f).symm
  calc
    G.selectedBlockAllOptionMass R0 rho omega choice e =
        ∑ c : Fin (B * k), f c := by
      rfl
    _ = ∑ p : Fin B × Fin k, f (finProdFinEquiv p) := hreindex
    _ = ∑ b : Fin B, ∑ j : Fin k, f (finProdFinEquiv (b, j)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ b : Fin B,
        G.selectedExtendedProfileBlockOptionMass
          R0 rho omega choice e b := by
      apply Finset.sum_congr rfl
      intro b _hb
      unfold selectedExtendedProfileBlockOptionMass
        extendedProfileBlockOptionMass
      apply Finset.sum_congr rfl
      intro j _hj
      simp [f, selectedBlockLargeOptionMass, selectedBlockTinyOptionMass,
        decodedExtendedProfileBlockSelection,
        extendedProfileBlockCoordinateOptionMass]
    _ = G.selectedExtendedProfileTotalOptionMass
        R0 rho omega choice e := by
      rfl

/-- The selected candidate large-row load is exactly `B*k` times the
ordinary fractional slot load. -/
theorem selectedBlockCapacityLoad_large_eq
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileLargeRow
      (n := B * k) (β := β) (q := q) (r := r)) :
    G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inl row) =
      (B * k : ℕ) *
        G.selectedBlockLargeSlotLoad R0 rho omega choice row := by
  classical
  unfold selectedBlockCapacityLoad selectedAtomCapacityLoad
    packedExtendedProfileCapacityLoad packedExtendedProfileCapacityUse
    packedExtendedProfileLargeRowUse packedExtendedProfileLargeMass
    selectedBlockLargeSlotLoad selectedBlockLargeOptionMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hfst : row.1 = G.fst e
  · have hne : G.fst e ≠ G.snd e := G.noLoop e
    have hsnd : row.1 ≠ G.snd e := by
      intro h
      exact G.noLoop e (hfst.symm.trans h)
    simp [hfst, hne, decodedExtendedProfileBlockSelection]
  · by_cases hsnd : row.1 = G.snd e
    · have hne : G.snd e ≠ G.fst e := Ne.symm (G.noLoop e)
      simp [hsnd, hne, decodedExtendedProfileBlockSelection]
    · simp [hfst, hsnd]

/-- The selected candidate tiny-row load is exactly `B*k` times the
weighted fractional reservoir load. -/
theorem selectedBlockCapacityLoad_tiny_eq
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileTinyRow (n := B * k)) :
    G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inr row) =
      (B * k : ℕ) *
        G.selectedBlockTinyReservoirLoad R0 rho omega choice row := by
  classical
  unfold selectedBlockCapacityLoad selectedAtomCapacityLoad
    packedExtendedProfileCapacityLoad packedExtendedProfileCapacityUse
    packedExtendedProfileTinyRowUse packedExtendedProfileTinyMass
    selectedBlockTinyReservoirLoad selectedBlockTinyOptionMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hinc : G.Inc row.1 e
  · have hrow : row.1 = G.fst e ∨ row.1 = G.snd e :=
      hinc.imp Eq.symm Eq.symm
    simp only [hinc, if_true]
    simp [WeightedSimpleGraph.Inc, hrow, selectedAtomCapacityLoad,
      decodedExtendedProfileBlockSelection]
    ring
  · have hrow : ¬(row.1 = G.fst e ∨ row.1 = G.snd e) := by
      intro h
      exact hinc (h.imp Eq.symm Eq.symm)
    simp [hinc, hrow]

/-- A positive selected large option uses a fitting concrete slot at both
endpoints. -/
theorem selectedBlockLargeOptionMass_pos_fits
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r))
    (hpos : 0 < G.selectedBlockLargeOptionMass
      R0 rho omega choice e c i j) :
    G.ExtendedLargeSlotFits R0 (G.fst e) (G.fstStarEdge e)
        (G.decodedExtendedProfileBlockSelection R0 choice (G.fst e) c) i ∧
      G.ExtendedLargeSlotFits R0 (G.snd e) (G.sndStarEdge e)
        (G.decodedExtendedProfileBlockSelection R0 choice (G.snd e) c) j := by
  have hy0 := G.extendedProfileEdgeColorMass_nonneg
    (β := β) (n := B * k) hs hn e
  have hy : 0 < G.extendedProfileEdgeColorMass
      (s := s) (β := β) (n := B * k) e := by
    by_contra hnot
    have hzero : G.extendedProfileEdgeColorMass
        (s := s) (β := β) (n := B * k) e = 0 :=
      le_antisymm (le_of_not_gt hnot) hy0
    unfold selectedBlockLargeOptionMass extendedProfileProductOptionMass
      pairedOption at hpos
    simp [hzero] at hpos
  exact G.extendedProfileProductOptionMass_pos_fits R0
    hs hn hq hr0 hleft homega0 homega1 hrho hy _ _ i j hpos

/-- A positive selected tiny option is supported on a tiny edge and on a
positive reservoir at both endpoints. -/
theorem selectedBlockTinyOptionMass_pos_fit
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (hpos : 0 < G.selectedBlockTinyOptionMass
      R0 rho omega choice e c) :
    (G.weight e < β ∧
      0 < G.extendedProfileReservoirSize R0 (G.fst e)
        (G.decodedExtendedProfileBlockSelection R0 choice (G.fst e) c)) ∧
    (G.weight e < β ∧
      0 < G.extendedProfileReservoirSize R0 (G.snd e)
        (G.decodedExtendedProfileBlockSelection R0 choice (G.snd e) c)) := by
  have hy0 := G.extendedProfileTinyEdgeColorMass_nonneg
    (β := β) (n := B * k) hs hn e
  have hy : 0 < G.extendedProfileTinyEdgeColorMass
      (s := s) (β := β) (n := B * k) e := by
    by_contra hnot
    have hzero : G.extendedProfileTinyEdgeColorMass
        (s := s) (β := β) (n := B * k) e = 0 :=
      le_antisymm (le_of_not_gt hnot) hy0
    unfold selectedBlockTinyOptionMass
      extendedProfileTinyProductOptionMass pairedOption at hpos
    simp [hzero] at hpos
  exact G.extendedProfileTinyProductOptionMass_pos_fit R0
    hs hq hr0 hleft homega0 homega1 hrho hy _ _ hpos

end WeightedSimpleGraph

end

end WeightedEdgeColoring
