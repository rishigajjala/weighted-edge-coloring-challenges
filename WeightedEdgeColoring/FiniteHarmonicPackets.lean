import WeightedEdgeColoring.BipartitePackets
import WeightedEdgeColoring.FiniteExactBlockPartition
import WeightedEdgeColoring.HarmonicBinCharge

/-!
# Finite harmonic-class packet decomposition

For a fixed number `T` of size classes, edges in class `r` joining the
same oriented endpoint pair are grouped into blocks of exactly `r` edges.
Each cell leaves fewer than `r` residual edges.  Full blocks have unit
harmonic charge and become packet edges; residual edges retain their
individual charge `1/r`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}}

/-- The natural-number size represented by a zero-based finite class. -/
def finiteClassSize {T : ℕ} (a : Fin T) : ℕ := a.1 + 1

theorem finiteClassSize_pos {T : ℕ} (a : Fin T) :
    0 < finiteClassSize a := by
  unfold finiteClassSize
  omega

/-- Oriented endpoint pair together with a finite harmonic class. -/
abbrev FiniteClassKey (G : WeightedMultigraph.{u}) (T : ℕ) :=
  G.V × G.V × Fin T

namespace Bipartition

/-- The cell key of an edge: left endpoint, right endpoint, and class. -/
def finiteClassKey {T : ℕ} (b : G.Bipartition)
    (classOf : G.E → Fin T) (e : G.E) : FiniteClassKey G T :=
  (b.leftEndpoint e, b.rightEndpoint e, classOf e)

/-- Edges in one oriented endpoint-pair/class cell. -/
def finiteClassCell {T : ℕ} (b : G.Bipartition)
    (classOf : G.E → Fin T) (k : FiniteClassKey G T) : Finset G.E :=
  Finset.univ.filter fun e ↦ b.finiteClassKey classOf e = k

@[simp] theorem mem_finiteClassCell_iff {T : ℕ} (b : G.Bipartition)
    (classOf : G.E → Fin T) (k : FiniteClassKey G T) (e : G.E) :
    e ∈ b.finiteClassCell classOf k ↔ b.finiteClassKey classOf e = k := by
  simp [finiteClassCell]

/-- Incidence read directly from an oriented cell key. -/
def finiteClassKeyInc {T : ℕ} (v : G.V) (k : FiniteClassKey G T) : Prop :=
  k.1 = v ∨ k.2.1 = v

instance {T : ℕ} (v : G.V) (k : FiniteClassKey G T) :
    Decidable (finiteClassKeyInc v k) := by
  unfold finiteClassKeyInc
  infer_instance

theorem inc_iff_finiteClassKeyInc {T : ℕ} (b : G.Bipartition)
    (classOf : G.E → Fin T) (v : G.V) (e : G.E) :
    G.Inc v e ↔ finiteClassKeyInc v (b.finiteClassKey classOf e) := by
  unfold finiteClassKeyInc finiteClassKey Inc leftEndpoint rightEndpoint
  split <;> simp [or_comm]

end Bipartition

/-- A choice of an exact block partition in every endpoint-pair/class cell. -/
structure FiniteClassPacketDecomposition {T : ℕ}
    (b : G.Bipartition) (classOf : G.E → Fin T) where
  cellPartition : ∀ k : FiniteClassKey G T,
    ExactBlockPartition (b.finiteClassCell classOf k)
      (finiteClassSize k.2.2)

/-- Exact finite-class packet decompositions always exist. -/
theorem exists_finiteClassPacketDecomposition {T : ℕ}
    (b : G.Bipartition) (classOf : G.E → Fin T) :
    Nonempty (G.FiniteClassPacketDecomposition b classOf) := by
  classical
  refine ⟨⟨fun k ↦ Classical.choice ?_⟩⟩
  exact exists_exactBlockPartition (b.finiteClassCell classOf k)
    (finiteClassSize k.2.2) (finiteClassSize_pos k.2.2)

namespace FiniteClassPacketDecomposition

variable {T : ℕ} {b : G.Bipartition} {classOf : G.E → Fin T}
    (D : G.FiniteClassPacketDecomposition b classOf)

/-- Full packets, indexed by their cell and their exact block. -/
abbrev Packet :=
  Σ k : FiniteClassKey G T,
    {A : Finset G.E // A ∈ (D.cellPartition k).blocks}

/-- Original edges belonging to a full packet. -/
def packetEdges (p : D.Packet) : Finset G.E := p.2.1

/-- The class of a packet. -/
def packetClass (p : D.Packet) : Fin T := p.1.2.2

/-- Oriented endpoints of a packet. -/
def packetTail (p : D.Packet) : G.V := p.1.1
def packetHead (p : D.Packet) : G.V := p.1.2.1

/-- Total physical weight in a full packet. -/
def packetWeight (p : D.Packet) : ℝ :=
  ∑ e ∈ D.packetEdges p, G.weight e

/-- Edges in the short remainder of their own cell. -/
def residualEdges : Finset G.E :=
  Finset.univ.filter fun e ↦
    e ∈ (D.cellPartition (b.finiteClassKey classOf e)).remainder

@[simp] theorem mem_residualEdges_iff (e : G.E) :
    e ∈ D.residualEdges ↔
      e ∈ (D.cellPartition (b.finiteClassKey classOf e)).remainder := by
  simp [residualEdges]

theorem packetEdges_card (p : D.Packet) :
    (D.packetEdges p).card = finiteClassSize (D.packetClass p) := by
  exact (D.cellPartition p.1).block_card p.2.1 p.2.2

theorem packetEdges_nonempty (p : D.Packet) :
    (D.packetEdges p).Nonempty := by
  apply Finset.card_pos.mp
  rw [D.packetEdges_card p]
  exact finiteClassSize_pos (D.packetClass p)

theorem packetEdges_subset_cell (p : D.Packet) :
    D.packetEdges p ⊆ b.finiteClassCell classOf p.1 :=
  (D.cellPartition p.1).block_subset p.2.1 p.2.2

theorem key_eq_of_mem_packetEdges (p : D.Packet) {e : G.E}
    (he : e ∈ D.packetEdges p) :
    b.finiteClassKey classOf e = p.1 := by
  exact (b.mem_finiteClassCell_iff classOf p.1 e).mp
    (D.packetEdges_subset_cell p he)

theorem class_eq_of_mem_packetEdges (p : D.Packet) {e : G.E}
    (he : e ∈ D.packetEdges p) :
    classOf e = D.packetClass p := by
  have h := congrArg (fun k : FiniteClassKey G T ↦ k.2.2)
    (D.key_eq_of_mem_packetEdges p he)
  exact h

theorem endpoints_eq_of_mem_packetEdges (p : D.Packet) {e : G.E}
    (he : e ∈ D.packetEdges p) :
    b.leftEndpoint e = D.packetTail p ∧
      b.rightEndpoint e = D.packetHead p := by
  have h := D.key_eq_of_mem_packetEdges p he
  exact ⟨congrArg (fun k : FiniteClassKey G T ↦ k.1) h,
    congrArg (fun k : FiniteClassKey G T ↦ k.2.1) h⟩

/-- Every full class-`r` packet has physical weight at most one. -/
theorem packetWeight_le_one
    (hweight : ∀ e, G.weight e ≤
      (1 : ℝ) / finiteClassSize (classOf e))
    (p : D.Packet) : D.packetWeight p ≤ 1 := by
  let r := finiteClassSize (D.packetClass p)
  have hr : (0 : ℝ) < r := by
    exact_mod_cast finiteClassSize_pos (D.packetClass p)
  calc
    D.packetWeight p ≤
        ∑ _e ∈ D.packetEdges p, (1 : ℝ) / r := by
      apply Finset.sum_le_sum
      intro e he
      simpa [r, D.class_eq_of_mem_packetEdges p he] using hweight e
    _ = ((D.packetEdges p).card : ℝ) / r := by
      simp [div_eq_mul_inv]
    _ = 1 := by
      rw [D.packetEdges_card p]
      dsimp [r]
      exact div_self (by
        exact_mod_cast Nat.ne_of_gt (finiteClassSize_pos (D.packetClass p)))

/-- The residual edges in one exact cell are precisely that cell's stored
remainder. -/
theorem residualEdges_filter_key (k : FiniteClassKey G T) :
    D.residualEdges.filter (fun e ↦ b.finiteClassKey classOf e = k) =
      (D.cellPartition k).remainder := by
  ext e
  constructor
  · intro he
    have he' := Finset.mem_filter.mp he
    have hres := (D.mem_residualEdges_iff e).mp he'.1
    rw [← he'.2]
    exact hres
  · intro he
    have heCell := (D.cellPartition k).remainder_subset he
    have hkey := (b.mem_finiteClassCell_iff classOf k e).mp heCell
    apply Finset.mem_filter.mpr
    refine ⟨?_, hkey⟩
    apply (D.mem_residualEdges_iff e).mpr
    rw [hkey]
    exact he

/-- Fewer than `r` residual edges remain in every endpoint-pair/class cell. -/
theorem residual_cell_card_lt (k : FiniteClassKey G T) :
    (D.residualEdges.filter
      (fun e ↦ b.finiteClassKey classOf e = k)).card <
        finiteClassSize k.2.2 := by
  rw [D.residualEdges_filter_key k]
  exact (D.cellPartition k).remainder_card_lt

/-- Every original edge is either residual or belongs to a full packet. -/
theorem mem_residualEdges_or_exists_packet (e : G.E) :
    e ∈ D.residualEdges ∨ ∃ p : D.Packet, e ∈ D.packetEdges p := by
  let k := b.finiteClassKey classOf e
  have heCell : e ∈ b.finiteClassCell classOf k := by
    simp [k]
  have heCover : e ∈
      (D.cellPartition k).blocks.biUnion id ∪
        (D.cellPartition k).remainder := by
    rw [(D.cellPartition k).cover]
    exact heCell
  rcases Finset.mem_union.mp heCover with hfull | hrem
  · rcases Finset.mem_biUnion.mp hfull with ⟨A, hAblocks, heA⟩
    exact Or.inr ⟨⟨k, ⟨A, hAblocks⟩⟩, heA⟩
  · apply Or.inl
    apply (D.mem_residualEdges_iff e).mpr
    simpa [k] using hrem

/-- Residual edges are disjoint from every full packet. -/
theorem residualEdges_disjoint_packetEdges (p : D.Packet) :
    Disjoint D.residualEdges (D.packetEdges p) := by
  apply Finset.disjoint_left.mpr
  intro e heR heP
  have hkey := D.key_eq_of_mem_packetEdges p heP
  have hrem := (D.mem_residualEdges_iff e).mp heR
  rw [hkey] at hrem
  exact Finset.disjoint_left.mp
    ((D.cellPartition p.1).remainder_disjoint p.2.1 p.2.2).symm
      hrem heP

/-- Residual multiplicity between one oriented endpoint pair, summed over
all retained classes, is at most `Σ_{a : Fin T} a`, namely
`Σ_{r=1}^T (r-1)`. -/
theorem residual_pair_multiplicity_le (u v : G.V) :
    (D.residualEdges.filter fun e ↦
      b.leftEndpoint e = u ∧ b.rightEndpoint e = v).card ≤
      ∑ a : Fin T, a.1 := by
  classical
  let Ruv := D.residualEdges.filter fun e ↦
    b.leftEndpoint e = u ∧ b.rightEndpoint e = v
  have hmaps : (Ruv : Set G.E).MapsTo classOf
      (Finset.univ : Finset (Fin T)) := by
    intro e he
    simp
  change Ruv.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_le_sum
  intro a _ha
  have heq :
      (Ruv.filter fun e ↦ classOf e = a) =
        D.residualEdges.filter
          (fun e ↦ b.finiteClassKey classOf e = (u, v, a)) := by
    ext e
    simp [Ruv, Bipartition.finiteClassKey, and_assoc]
  rw [heq]
  have hlt := D.residual_cell_card_lt (u, v, a)
  change
    (D.residualEdges.filter
      (fun e ↦ b.finiteClassKey classOf e = (u, v, a))).card < a.1 + 1 at hlt
  exact Nat.le_of_lt_succ hlt

/-! ## Exact charge accounting -/

/-- Number of full packets incident with a vertex. -/
def packetDegreeAt (v : G.V) : ℕ :=
  ∑ k : FiniteClassKey G T,
    if Bipartition.finiteClassKeyInc v k then
      (D.cellPartition k).blocks.card else 0

/-- Charge retained on the residual edges at a vertex. -/
def residualClassChargeAt (v : G.V) : ℝ :=
  ∑ e ∈ D.residualEdges,
    if G.Inc v e then (1 : ℝ) / finiteClassSize (classOf e) else 0

/-- Original finite-class charge at a vertex. -/
def originalClassChargeAt (v : G.V) : ℝ :=
  let _decomposition := D
  ∑ e : G.E,
    if G.Inc v e then (1 : ℝ) / finiteClassSize (classOf e) else 0

private theorem class_eq_of_mem_cell (k : FiniteClassKey G T)
    {e : G.E} (he : e ∈ b.finiteClassCell classOf k) :
    classOf e = k.2.2 := by
  have hkey := (b.mem_finiteClassCell_iff classOf k e).mp he
  exact congrArg (fun z : FiniteClassKey G T ↦ z.2.2) hkey

private theorem inc_iff_keyInc_of_mem_cell (v : G.V)
    (k : FiniteClassKey G T) {e : G.E}
    (he : e ∈ b.finiteClassCell classOf k) :
    G.Inc v e ↔ Bipartition.finiteClassKeyInc v k := by
  rw [b.inc_iff_finiteClassKeyInc classOf v e]
  have hkey := (b.mem_finiteClassCell_iff classOf k e).mp he
  rw [hkey]

/-- Cellwise accounting: a full block contributes one, while every
remainder edge contributes `1/r`. -/
theorem cell_packet_add_remainder_charge
    (k : FiniteClassKey G T) :
    ((D.cellPartition k).blocks.card : ℝ) +
        ((D.cellPartition k).remainder.card : ℝ) /
          finiteClassSize k.2.2 =
      ((b.finiteClassCell classOf k).card : ℝ) /
        finiteClassSize k.2.2 := by
  let r := finiteClassSize k.2.2
  have hr : (0 : ℝ) < r := by
    exact_mod_cast finiteClassSize_pos k.2.2
  have hcard := (D.cellPartition k).card_decomposition
  have hcardR :
      ((D.cellPartition k).blocks.card : ℝ) * r +
          ((D.cellPartition k).remainder.card : ℝ) =
        (b.finiteClassCell classOf k).card := by
    exact_mod_cast hcard
  change
    ((D.cellPartition k).blocks.card : ℝ) +
        ((D.cellPartition k).remainder.card : ℝ) / r =
      ((b.finiteClassCell classOf k).card : ℝ) / r
  apply (eq_div_iff hr.ne').2
  calc
    (((D.cellPartition k).blocks.card : ℝ) +
        ((D.cellPartition k).remainder.card : ℝ) / r) * r =
        ((D.cellPartition k).blocks.card : ℝ) * r +
          ((D.cellPartition k).remainder.card : ℝ) := by
      field_simp [hr.ne']
    _ = (b.finiteClassCell classOf k).card := hcardR

theorem packetDegreeAt_cast_eq (v : G.V) :
    (D.packetDegreeAt v : ℝ) =
      ∑ k : FiniteClassKey G T,
        if Bipartition.finiteClassKeyInc v k then
          ((D.cellPartition k).blocks.card : ℝ) else 0 := by
  unfold packetDegreeAt
  push_cast
  rfl

theorem originalClassChargeAt_eq_sum_cells (v : G.V) :
    D.originalClassChargeAt v =
      ∑ k : FiniteClassKey G T,
        if Bipartition.finiteClassKeyInc v k then
          ((b.finiteClassCell classOf k).card : ℝ) /
            finiteClassSize k.2.2 else 0 := by
  classical
  let f : G.E → ℝ := fun e ↦
    if G.Inc v e then (1 : ℝ) / finiteClassSize (classOf e) else 0
  have hfiber := Finset.sum_fiberwise (Finset.univ : Finset G.E)
    (b.finiteClassKey classOf) f
  calc
    D.originalClassChargeAt v = ∑ e : G.E, f e := rfl
    _ = ∑ k : FiniteClassKey G T,
        ∑ e ∈ b.finiteClassCell classOf k, f e := by
      symm
      simpa [Bipartition.finiteClassCell] using hfiber
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases hinc : Bipartition.finiteClassKeyInc v k
      · rw [if_pos hinc]
        calc
          (∑ e ∈ b.finiteClassCell classOf k, f e) =
              ∑ _e ∈ b.finiteClassCell classOf k,
                (1 : ℝ) / finiteClassSize k.2.2 := by
            apply Finset.sum_congr rfl
            intro e he
            have heinc := (inc_iff_keyInc_of_mem_cell
              (b := b) (classOf := classOf) v k he).mpr hinc
            have heclass := class_eq_of_mem_cell
              (b := b) (classOf := classOf) k he
            simp [f, heinc, heclass]
          _ = ((b.finiteClassCell classOf k).card : ℝ) /
              finiteClassSize k.2.2 := by
            simp [div_eq_mul_inv]
      · rw [if_neg hinc]
        apply Finset.sum_eq_zero
        intro e he
        have heNot : ¬ G.Inc v e := by
          intro heInc
          exact hinc ((inc_iff_keyInc_of_mem_cell
            (b := b) (classOf := classOf) v k he).mp heInc)
        simp [f, heNot]

theorem residualClassChargeAt_eq_sum_cells (v : G.V) :
    D.residualClassChargeAt v =
      ∑ k : FiniteClassKey G T,
        if Bipartition.finiteClassKeyInc v k then
          ((D.cellPartition k).remainder.card : ℝ) /
            finiteClassSize k.2.2 else 0 := by
  classical
  let f : G.E → ℝ := fun e ↦
    if G.Inc v e then (1 : ℝ) / finiteClassSize (classOf e) else 0
  have hfiber := Finset.sum_fiberwise D.residualEdges
    (b.finiteClassKey classOf) f
  calc
    D.residualClassChargeAt v = ∑ e ∈ D.residualEdges, f e := rfl
    _ = ∑ k : FiniteClassKey G T,
        ∑ e ∈ D.residualEdges.filter
          (fun e ↦ b.finiteClassKey classOf e = k), f e := by
      symm
      exact hfiber
    _ = ∑ k : FiniteClassKey G T,
        ∑ e ∈ (D.cellPartition k).remainder, f e := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [D.residualEdges_filter_key k]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases hinc : Bipartition.finiteClassKeyInc v k
      · rw [if_pos hinc]
        calc
          (∑ e ∈ (D.cellPartition k).remainder, f e) =
              ∑ _e ∈ (D.cellPartition k).remainder,
                (1 : ℝ) / finiteClassSize k.2.2 := by
            apply Finset.sum_congr rfl
            intro e he
            have heCell := (D.cellPartition k).remainder_subset he
            have heinc := (inc_iff_keyInc_of_mem_cell
              (b := b) (classOf := classOf) v k heCell).mpr hinc
            have heclass := class_eq_of_mem_cell
              (b := b) (classOf := classOf) k heCell
            simp [f, heinc, heclass]
          _ = ((D.cellPartition k).remainder.card : ℝ) /
              finiteClassSize k.2.2 := by
            simp [div_eq_mul_inv]
      · rw [if_neg hinc]
        apply Finset.sum_eq_zero
        intro e he
        have heCell := (D.cellPartition k).remainder_subset he
        have heNot : ¬ G.Inc v e := by
          intro heInc
          exact hinc ((inc_iff_keyInc_of_mem_cell
            (b := b) (classOf := classOf) v k heCell).mp heInc)
        simp [f, heNot]

/-- Exact preservation of finite-class charge: every full packet accounts
for one unit and every residual edge keeps charge `1/r`. -/
theorem packetDegree_add_residualClassChargeAt (v : G.V) :
    (D.packetDegreeAt v : ℝ) + D.residualClassChargeAt v =
      D.originalClassChargeAt v := by
  rw [D.packetDegreeAt_cast_eq v,
    D.residualClassChargeAt_eq_sum_cells v,
    D.originalClassChargeAt_eq_sum_cells v]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hinc : Bipartition.finiteClassKeyInc v k
  · simp only [if_pos hinc]
    exact D.cell_packet_add_remainder_charge k
  · simp [hinc]

/-- When the finite class labels agree with harmonic charge, the preceding
identity is exactly the manuscript's packet-degree plus residual-harmonic-
charge identity. -/
theorem packetDegree_add_residualHarmonicChargeAt
    (hcharge : ∀ e, harmonicCharge (G.weight e) =
      (1 : ℝ) / finiteClassSize (classOf e))
    (v : G.V) :
    (D.packetDegreeAt v : ℝ) +
        (∑ e ∈ D.residualEdges,
          if G.Inc v e then harmonicCharge (G.weight e) else 0) =
      ∑ e : G.E,
        if G.Inc v e then harmonicCharge (G.weight e) else 0 := by
  have hres :
      (∑ e ∈ D.residualEdges,
          if G.Inc v e then harmonicCharge (G.weight e) else 0) =
        D.residualClassChargeAt v := by
    unfold residualClassChargeAt
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hinc : G.Inc v e <;> simp [hinc, hcharge e]
  have horig :
      (∑ e : G.E,
          if G.Inc v e then harmonicCharge (G.weight e) else 0) =
        D.originalClassChargeAt v := by
    unfold originalClassChargeAt
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hinc : G.Inc v e <;> simp [hinc, hcharge e]
  rw [hres, horig]
  exact D.packetDegree_add_residualClassChargeAt v

end FiniteClassPacketDecomposition

/-- Packaged finite-class harmonic decomposition theorem.  It simultaneously
records the unit packet-weight bound, exact charge accounting at every
vertex, and the uniform residual multiplicity bound. -/
theorem exists_finiteHarmonicPacketDecomposition {T : ℕ}
    (b : G.Bipartition) (classOf : G.E → Fin T)
    (hweight : ∀ e, G.weight e ≤
      (1 : ℝ) / finiteClassSize (classOf e))
    (hcharge : ∀ e, harmonicCharge (G.weight e) =
      (1 : ℝ) / finiteClassSize (classOf e)) :
    ∃ D : G.FiniteClassPacketDecomposition b classOf,
      (∀ p : D.Packet, D.packetWeight p ≤ 1) ∧
      (∀ v,
        (D.packetDegreeAt v : ℝ) +
            (∑ e ∈ D.residualEdges,
              if G.Inc v e then harmonicCharge (G.weight e) else 0) =
          ∑ e : G.E,
            if G.Inc v e then harmonicCharge (G.weight e) else 0) ∧
      ∀ u v,
        (D.residualEdges.filter fun e ↦
          b.leftEndpoint e = u ∧ b.rightEndpoint e = v).card ≤
          ∑ a : Fin T, a.1 := by
  classical
  let D : G.FiniteClassPacketDecomposition b classOf :=
    Classical.choice (G.exists_finiteClassPacketDecomposition b classOf)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro p
    exact D.packetWeight_le_one hweight p
  · intro v
    exact D.packetDegree_add_residualHarmonicChargeAt hcharge v
  · intro u v
    exact D.residual_pair_multiplicity_le u v

end

end WeightedMultigraph
end WeightedEdgeColoring
