import WeightedEdgeColoring.RankThreeDirectNibbleHarris

/-!
# Adding arbitrary increasing events to the direct nibble

The Harris neighborhood contains only events of opposite monotonicity.  Hence
an additional increasing event pays only for the decreasing coverage rows.
Conversely, a decreasing coverage row pays for the additional increasing
events which contain one of its coordinates.  No extra--extra, extra--pair,
or extra--upper incidence enters the local-lemma products.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliHarris
open WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w x y z e

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  {Conflict : Type x} {LowerRow : Type y} {UpperRow : Type z}
  {Extra : Type e}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [Fintype Conflict] [Fintype LowerRow] [Fintype UpperRow] [Fintype Extra]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  [DecidableEq Conflict] [DecidableEq LowerRow] [DecidableEq UpperRow]
  [DecidableEq Extra]

/-- The old direct-nibble constraints together with an arbitrary family of
additional increasing constraints. -/
abbrev DirectNibbleExtraBadIndex
    (Conflict LowerRow UpperRow Extra : Type*) :=
  DirectNibbleBadIndex Conflict LowerRow UpperRow ⊕ Extra

/-- Coordinate support of the enlarged bad-event family. -/
noncomputable def directNibbleExtraSupport
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option) :
    DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra → Finset Option
  | Sum.inl b => directNibbleSupport left right lowerWeight upperWeight b
  | Sum.inr a => extraSupport a

/-- Local events of the enlarged family. -/
noncomputable def directNibbleExtraLocalBad
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold : LowerRow → ℝ) (upperThreshold : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (extraSupport : Extra → Finset Option)
    (extraLocalBad : (a : Extra) → Finset (Finset (Inside (extraSupport a)))) :
    (b : DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra) →
      Finset (Finset (Inside
        (directNibbleExtraSupport left right lowerWeight upperWeight
          extraSupport b)))
  | Sum.inl b =>
      directNibbleLocalBad left right lowerWeight upperWeight
        lowerThreshold upperThreshold hne b
  | Sum.inr a => extraLocalBad a

/-- Every new event is increasing; the old family keeps its old polarity. -/
def directNibbleExtraPolarity :
    DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra → Bool
  | Sum.inl b => directNibblePolarity b
  | Sum.inr _ => true

/-- Canonical Harris neighborhood of the enlarged family. -/
noncomputable def directNibbleExtraNeighbor
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option) :
    DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra →
      Finset (DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra) :=
  polaritySupportNeighbor
    (directNibbleExtraSupport left right lowerWeight upperWeight extraSupport)
    directNibbleExtraPolarity

/-- Opposite-polarity events which contain one coordinate. -/
noncomputable def directNibbleExtraOppositeIncidence
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (b : DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra)
    (o : Option) :
    Finset (DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra) :=
  Finset.univ.filter fun a ↦
    directNibbleExtraPolarity a ≠ directNibbleExtraPolarity b ∧
      o ∈ directNibbleExtraSupport left right lowerWeight upperWeight
        extraSupport a

/-- Additional increasing events which contain one option coordinate. -/
noncomputable def directNibbleExtraEventIncidence
    (extraSupport : Extra → Finset Option) (o : Option) : Finset Extra :=
  Finset.univ.filter fun a ↦ o ∈ extraSupport a

/-- An increasing event has, at each coordinate, exactly the incident lower
rows as opposite-polarity events.  In particular the added increasing
family creates no new neighbors for another increasing event. -/
theorem directNibbleExtraOppositeIncidence_increasing_card
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (b : DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra)
    (hb : directNibbleExtraPolarity b = true) (o : Option) :
    (directNibbleExtraOppositeIncidence left right lowerWeight upperWeight
      extraSupport b o).card = (linearRowIncidence lowerWeight o).card := by
  have hset :
      directNibbleExtraOppositeIncidence left right lowerWeight upperWeight
          extraSupport b o =
        (((∅ : Finset Conflict).disjSum
            ((linearRowIncidence lowerWeight o).disjSum
              (∅ : Finset UpperRow))).disjSum (∅ : Finset Extra)) := by
    ext a
    simp only [directNibbleExtraOppositeIncidence, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hb]
    rcases a with a | a
    · rcases a with c | r
      · simp [directNibbleExtraPolarity, directNibblePolarity]
      · rcases r with r | r
        · simp [directNibbleExtraPolarity, directNibblePolarity,
            directNibbleExtraSupport, directNibbleSupport,
            linearRowIncidence]
        · simp [directNibbleExtraPolarity, directNibblePolarity]
    · simp [directNibbleExtraPolarity]
  rw [hset, Finset.card_disjSum, Finset.card_disjSum,
    Finset.card_disjSum]
  simp

/-- At each coordinate, a lower event sees precisely the incident conflict
pairs, upper rows, and additional increasing events. -/
theorem directNibbleExtraOppositeIncidence_lower_card
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (r : LowerRow) (o : Option) :
    (directNibbleExtraOppositeIncidence left right lowerWeight upperWeight
      extraSupport (Sum.inl (Sum.inr (Sum.inl r))) o).card =
        (optionConflictIncidence left right o).card +
          (linearRowIncidence upperWeight o).card +
            (directNibbleExtraEventIncidence extraSupport o).card := by
  have hset :
      directNibbleExtraOppositeIncidence left right lowerWeight upperWeight
          extraSupport (Sum.inl (Sum.inr (Sum.inl r))) o =
        ((optionConflictIncidence left right o).disjSum
            ((∅ : Finset LowerRow).disjSum
              (linearRowIncidence upperWeight o))).disjSum
          (directNibbleExtraEventIncidence extraSupport o) := by
    ext a
    rcases a with a | a
    · rcases a with c | u
      · simp [directNibbleExtraOppositeIncidence,
          directNibbleExtraPolarity, directNibblePolarity,
          directNibbleExtraSupport, directNibbleSupport,
          optionConflictIncidence, conflictPairSupport]
      · rcases u with l | u
        · simp [directNibbleExtraOppositeIncidence,
            directNibbleExtraPolarity, directNibblePolarity]
        · simp [directNibbleExtraOppositeIncidence,
            directNibbleExtraPolarity, directNibblePolarity,
            directNibbleExtraSupport, directNibbleSupport,
            linearRowIncidence]
    · simp [directNibbleExtraOppositeIncidence,
        directNibbleExtraPolarity, directNibblePolarity,
        directNibbleExtraSupport,
        directNibbleExtraEventIncidence]
  rw [hset, Finset.card_disjSum, Finset.card_disjSum,
    Finset.card_disjSum]
  simp [Nat.add_assoc]

/-- The usual support-times-incidence count, restricted to opposite-polarity
events. -/
theorem directNibbleExtraNeighbor_card_le
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (b : DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra) (L : ℕ)
    (hincidence : ∀ o,
      (directNibbleExtraOppositeIncidence left right lowerWeight upperWeight
        extraSupport b o).card ≤ L) :
    (directNibbleExtraNeighbor left right lowerWeight upperWeight
      extraSupport b).card ≤
      (directNibbleExtraSupport left right lowerWeight upperWeight
        extraSupport b).card * L := by
  let support := directNibbleExtraSupport left right lowerWeight upperWeight
    extraSupport
  let polarity : DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra → Bool :=
    directNibbleExtraPolarity
  let incidence := directNibbleExtraOppositeIncidence left right lowerWeight
    upperWeight extraSupport
  have hsub : polaritySupportNeighbor support polarity b ⊆
      (support b).biUnion (incidence b) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hoverlap : ¬ Disjoint (support b) (support a) := ha'.2.2.2
    rw [Finset.not_disjoint_iff] at hoverlap
    rcases hoverlap with ⟨o, hob, hoa⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨o, hob, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ a, ha'.2.2.1, hoa⟩
  calc
    (directNibbleExtraNeighbor left right lowerWeight upperWeight
        extraSupport b).card =
        (polaritySupportNeighbor support polarity b).card := rfl
    _ ≤ ((support b).biUnion (incidence b)).card := Finset.card_le_card hsub
    _ ≤ ∑ o ∈ support b, (incidence b o).card := Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ support b, L := by
      exact Finset.sum_le_sum fun o _ ↦ hincidence o
    _ = (support b).card * L := by simp

/-- LLL weights for the enlarged family.  The lower and upper row scales
are kept separate: in the Harris graph every increasing event sees only
the lower scale, while a lower event sees only the other three scales. -/
def directNibbleExtraLLLWeight
    (pairX lowerX upperX : ℝ) (extraX : Extra → ℝ) :
    DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra → ℝ
  | Sum.inl (Sum.inl _) => pairX
  | Sum.inl (Sum.inr (Sum.inl _)) => lowerX
  | Sum.inl (Sum.inr (Sum.inr _)) => upperX
  | Sum.inr a => extraX a

/-- Any increasing event in the enlarged family pays only for lower rows. -/
theorem directNibbleExtra_increasing_product_lower_bound
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (pairX lowerX upperX : ℝ) (extraX : Extra → ℝ) (R : ℕ)
    (hlowerX0 : 0 ≤ lowerX) (hlowerX1 : lowerX ≤ 1)
    (b : DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra)
    (hb : directNibbleExtraPolarity b = true)
    (hincidence : ∀ o,
      (directNibbleExtraOppositeIncidence left right lowerWeight upperWeight
        extraSupport b o).card ≤ R) :
    (1 - lowerX) ^
        ((directNibbleExtraSupport left right lowerWeight upperWeight
          extraSupport b).card * R) ≤
      ∏ a ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
        extraSupport b,
          (1 - directNibbleExtraLLLWeight pairX lowerX upperX extraX a) := by
  apply one_sub_cap_pow_le_neighbor_product_of_mem
    (directNibbleExtraNeighbor left right lowerWeight upperWeight extraSupport)
    (directNibbleExtraLLLWeight pairX lowerX upperX extraX) lowerX
    ((directNibbleExtraSupport left right lowerWeight upperWeight
      extraSupport b).card * R) b hlowerX0 hlowerX1
  · intro a ha
    have hpol := (Finset.mem_filter.mp ha).2.2.1
    rw [hb] at hpol
    rcases a with a | a
    · rcases a with c | r
      · simp [directNibbleExtraPolarity, directNibblePolarity] at hpol
      · rcases r with r | r
        · exact le_rfl
        · simp [directNibbleExtraPolarity, directNibblePolarity] at hpol
    · simp [directNibbleExtraPolarity] at hpol
  · exact directNibbleExtraNeighbor_card_le left right lowerWeight
      upperWeight extraSupport b R hincidence

/-- A decreasing coverage row pays for pair, upper-row, and new-event
weights.  The new family enters only through its coordinate incidence. -/
theorem directNibbleExtra_lower_product_lower_bound
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (pairX lowerX upperX cap : ℝ) (extraX : Extra → ℝ) (L : ℕ)
    (hcap0 : 0 ≤ cap) (hcap1 : cap ≤ 1)
    (hpairCap : pairX ≤ cap) (hupperCap : upperX ≤ cap)
    (hextraCap : ∀ a, extraX a ≤ cap)
    (r : LowerRow)
    (hincidence : ∀ o,
      (directNibbleExtraOppositeIncidence left right lowerWeight upperWeight
        extraSupport (Sum.inl (Sum.inr (Sum.inl r))) o).card ≤ L) :
    (1 - cap) ^ ((linearRowSupport lowerWeight r).card * L) ≤
      ∏ a ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
        extraSupport (Sum.inl (Sum.inr (Sum.inl r))),
          (1 - directNibbleExtraLLLWeight pairX lowerX upperX extraX a) := by
  apply one_sub_cap_pow_le_neighbor_product_of_mem
    (directNibbleExtraNeighbor left right lowerWeight upperWeight extraSupport)
    (directNibbleExtraLLLWeight pairX lowerX upperX extraX) cap
    ((linearRowSupport lowerWeight r).card * L)
    (Sum.inl (Sum.inr (Sum.inl r))) hcap0 hcap1
  · intro a ha
    rcases a with a | a
    · rcases a with c | u
      · exact hpairCap
      · rcases u with l | u
        · have hpol := (Finset.mem_filter.mp ha).2.2.1
          simp [directNibbleExtraPolarity, directNibblePolarity] at hpol
        · exact hupperCap
    · exact hextraCap a
  · simpa [directNibbleExtraSupport] using
      directNibbleExtraNeighbor_card_le left right lowerWeight upperWeight
        extraSupport (Sum.inl (Sum.inr (Sum.inl r))) L hincidence

/-- Support-card form of the increasing-event product estimate. -/
theorem directNibbleExtra_increasing_product_lower_bound_of_support_card
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (pairX lowerX upperX : ℝ) (extraX : Extra → ℝ) (R K : ℕ)
    (hlowerX0 : 0 ≤ lowerX) (hlowerX1 : lowerX ≤ 1)
    (b : DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra)
    (hb : directNibbleExtraPolarity b = true)
    (hsupport :
      (directNibbleExtraSupport left right lowerWeight upperWeight
        extraSupport b).card ≤ K)
    (hincidence : ∀ o,
      (directNibbleExtraOppositeIncidence left right lowerWeight upperWeight
        extraSupport b o).card ≤ R) :
    (1 - lowerX) ^ (K * R) ≤
      ∏ a ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
        extraSupport b,
          (1 - directNibbleExtraLLLWeight pairX lowerX upperX extraX a) := by
  calc
    (1 - lowerX) ^ (K * R) ≤
        (1 - lowerX) ^
          ((directNibbleExtraSupport left right lowerWeight upperWeight
            extraSupport b).card * R) :=
      pow_le_pow_of_le_one (sub_nonneg.mpr hlowerX1)
        (sub_le_self 1 hlowerX0) (Nat.mul_le_mul_right R hsupport)
    _ ≤ _ := directNibbleExtra_increasing_product_lower_bound
      left right lowerWeight upperWeight extraSupport pairX lowerX upperX
      extraX R hlowerX0 hlowerX1 b hb hincidence

/-- A pair event pays only for the lower-row weight. -/
theorem directNibbleExtra_pair_product_lower_bound
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (pairX lowerX upperX : ℝ) (extraX : Extra → ℝ) (R : ℕ)
    (hlowerX0 : 0 ≤ lowerX) (hlowerX1 : lowerX ≤ 1)
    (hlowerIncidence : ∀ o,
      (linearRowIncidence lowerWeight o).card ≤ R) (c : Conflict) :
    (1 - lowerX) ^ (2 * R) ≤
      ∏ a ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
        extraSupport (Sum.inl (Sum.inl c)),
          (1 - directNibbleExtraLLLWeight pairX lowerX upperX extraX a) := by
  apply directNibbleExtra_increasing_product_lower_bound_of_support_card
    left right lowerWeight upperWeight extraSupport pairX lowerX upperX
    extraX R 2 hlowerX0 hlowerX1 (Sum.inl (Sum.inl c))
  · simp [directNibbleExtraPolarity, directNibblePolarity]
  · simpa [directNibbleExtraSupport, directNibbleSupport] using
      conflictPairSupport_card_le_two left right c
  · intro o
    rw [directNibbleExtraOppositeIncidence_increasing_card left right
      lowerWeight upperWeight extraSupport (Sum.inl (Sum.inl c))
      (by simp [directNibbleExtraPolarity, directNibblePolarity]) o]
    exact hlowerIncidence o

/-- An upper row pays only for the lower-row weight. -/
theorem directNibbleExtra_upper_product_lower_bound
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (pairX lowerX upperX : ℝ) (extraX : Extra → ℝ) (R : ℕ)
    (hlowerX0 : 0 ≤ lowerX) (hlowerX1 : lowerX ≤ 1)
    (hlowerIncidence : ∀ o,
      (linearRowIncidence lowerWeight o).card ≤ R) (r : UpperRow) :
    (1 - lowerX) ^ ((linearRowSupport upperWeight r).card * R) ≤
      ∏ a ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
        extraSupport (Sum.inl (Sum.inr (Sum.inr r))),
          (1 - directNibbleExtraLLLWeight pairX lowerX upperX extraX a) := by
  apply directNibbleExtra_increasing_product_lower_bound
    left right lowerWeight upperWeight extraSupport pairX lowerX upperX
    extraX R hlowerX0 hlowerX1 (Sum.inl (Sum.inr (Sum.inr r)))
  · simp [directNibbleExtraPolarity, directNibblePolarity]
  · intro o
    rw [directNibbleExtraOppositeIncidence_increasing_card left right
      lowerWeight upperWeight extraSupport (Sum.inl (Sum.inr (Sum.inr r)))
      (by simp [directNibbleExtraPolarity, directNibblePolarity]) o]
    exact hlowerIncidence o

/-- An additional increasing event also pays only for the lower-row
weight; neither the number nor the overlap pattern of other increasing
events appears in this product. -/
theorem directNibbleExtra_event_product_lower_bound
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (pairX lowerX upperX : ℝ) (extraX : Extra → ℝ) (R : ℕ)
    (hlowerX0 : 0 ≤ lowerX) (hlowerX1 : lowerX ≤ 1)
    (hlowerIncidence : ∀ o,
      (linearRowIncidence lowerWeight o).card ≤ R) (a : Extra) :
    (1 - lowerX) ^ ((extraSupport a).card * R) ≤
      ∏ b ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
        extraSupport (Sum.inr a),
          (1 - directNibbleExtraLLLWeight pairX lowerX upperX extraX b) := by
  apply directNibbleExtra_increasing_product_lower_bound
    left right lowerWeight upperWeight extraSupport pairX lowerX upperX
    extraX R hlowerX0 hlowerX1 (Sum.inr a)
  · simp [directNibbleExtraPolarity]
  · intro o
    rw [directNibbleExtraOppositeIncidence_increasing_card left right
      lowerWeight upperWeight extraSupport (Sum.inr a)
      (by simp [directNibbleExtraPolarity]) o]
    exact hlowerIncidence o

/-- Incidence form of the lower-event product.  This is the only product
in which the added event family occurs, through the additive coordinate
incidence bound `E`. -/
theorem directNibbleExtra_lower_product_lower_bound_of_incidence
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (pairX lowerX upperX cap : ℝ) (extraX : Extra → ℝ)
    (D U E : ℕ)
    (hcap0 : 0 ≤ cap) (hcap1 : cap ≤ 1)
    (hpairCap : pairX ≤ cap) (hupperCap : upperX ≤ cap)
    (hextraCap : ∀ a, extraX a ≤ cap)
    (hconflictIncidence : ∀ o,
      (optionConflictIncidence left right o).card ≤ D)
    (hupperIncidence : ∀ o,
      (linearRowIncidence upperWeight o).card ≤ U)
    (hextraIncidence : ∀ o,
      (directNibbleExtraEventIncidence extraSupport o).card ≤ E)
    (r : LowerRow) :
    (1 - cap) ^
        ((linearRowSupport lowerWeight r).card * (D + U + E)) ≤
      ∏ a ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
        extraSupport (Sum.inl (Sum.inr (Sum.inl r))),
          (1 - directNibbleExtraLLLWeight pairX lowerX upperX extraX a) := by
  apply directNibbleExtra_lower_product_lower_bound left right lowerWeight
    upperWeight extraSupport pairX lowerX upperX cap extraX (D + U + E)
    hcap0 hcap1 hpairCap hupperCap hextraCap r
  intro o
  rw [directNibbleExtraOppositeIncidence_lower_card left right lowerWeight
    upperWeight extraSupport r o]
  have hD := hconflictIncidence o
  have hU := hupperIncidence o
  have hE := hextraIncidence o
  omega

/-- Positive mass of the enlarged avoidance event gives the usual direct
nibble output and also avoids every additional local event. -/
theorem extract_partialMatching_with_extra_of_positive
    (H : RankThreeOptionSystem Job Slot Option)
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold : LowerRow → ℝ) (upperThreshold : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬ H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨
        (left c = p ∧ right c = o))
    (q : Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (extraLocalBad : (a : Extra) → Finset (Finset (Inside (extraSupport a))))
    (hpositive : 0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid
        (fun b ↦ insideCylinder
          (directNibbleExtraSupport left right lowerWeight upperWeight
            extraSupport b)
          (directNibbleExtraLocalBad left right lowerWeight upperWeight
            lowerThreshold upperThreshold hne extraSupport extraLocalBad b))
        Finset.univ)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ r, lowerThreshold r <
        weightedSum
          (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
          (splitEquiv (linearRowSupport lowerWeight r) S).1) ∧
      (∀ r,
        weightedSum
          (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
          (splitEquiv (linearRowSupport upperWeight r) S).1 <
        upperThreshold r) ∧
      (∀ a, (splitEquiv (extraSupport a) S).1 ∉ extraLocalBad a) := by
  let support := directNibbleExtraSupport left right lowerWeight upperWeight
    extraSupport
  let localBad := directNibbleExtraLocalBad left right lowerWeight upperWeight
    lowerThreshold upperThreshold hne extraSupport extraLocalBad
  let good := WeightedEdgeColoring.FiniteLocalLemma.avoid
    (fun b ↦ insideCylinder (support b) (localBad b)) Finset.univ
  have hgood : good.Nonempty := by
    by_contra hempty
    have hz : WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) good = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
      simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass]
    rw [hz] at hpositive
    exact lt_irrefl 0 hpositive
  rcases hgood with ⟨S, hS⟩
  have havoid : ∀ b, S ∉ insideCylinder (support b) (localBad b) := by
    simpa [good, WeightedEdgeColoring.FiniteLocalLemma.avoid] using hS
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro o ho p hp hop
      by_contra hcompat
      rcases hcomplete o p hop (Or.inr hcompat) with ⟨c, hc | hc⟩
      · have hbad := havoid (Sum.inl (Sum.inl c))
        simp [support, localBad, directNibbleExtraSupport,
          directNibbleExtraLocalBad, directNibbleSupport, directNibbleLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad ho hp
      · have hbad := havoid (Sum.inl (Sum.inl c))
        simp [support, localBad, directNibbleExtraSupport,
          directNibbleExtraLocalBad, directNibbleSupport, directNibbleLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad hp ho
    · intro o ho p hp howner
      by_contra hop
      rcases hcomplete o p hop (Or.inl howner) with ⟨c, hc | hc⟩
      · have hbad := havoid (Sum.inl (Sum.inl c))
        simp [support, localBad, directNibbleExtraSupport,
          directNibbleExtraLocalBad, directNibbleSupport, directNibbleLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad ho hp
      · have hbad := havoid (Sum.inl (Sum.inl c))
        simp [support, localBad, directNibbleExtraSupport,
          directNibbleExtraLocalBad, directNibbleSupport, directNibbleLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad hp ho
  · intro r
    have hr := havoid (Sum.inl (Sum.inr (Sum.inl r)))
    simpa [support, localBad, directNibbleExtraSupport,
      directNibbleExtraLocalBad, directNibbleSupport, directNibbleLocalBad,
      lowerTail, not_le] using hr
  · intro r
    have hr := havoid (Sum.inl (Sum.inr (Sum.inr r)))
    simpa [support, localBad, directNibbleExtraSupport,
      directNibbleExtraLocalBad, directNibbleSupport, directNibbleLocalBad,
      upperTail, not_le] using hr
  · intro a
    have ha := havoid (Sum.inr a)
    simpa only [support, localBad, directNibbleExtraSupport,
      directNibbleExtraLocalBad, mem_insideCylinder] using ha

/-- Exact Harris theorem with arbitrary additional increasing cylinder
events.  Its four numerical hypotheses are precisely the four local event
types; the canonical neighbor omits every same-polarity overlap. -/
theorem exists_partialMatching_with_extra_increasing_harris
    (H : RankThreeOptionSystem Job Slot Option)
    (left right : Conflict → Option) (q : Option → ℝ)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold lowerLambda : LowerRow → ℝ)
    (upperThreshold upperLambda : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬ H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨
        (left c = p ∧ right c = o))
    (extraSupport : Extra → Finset Option)
    (extraLocalBad : (a : Extra) → Finset (Finset (Inside (extraSupport a))))
    (hextraIncreasing : ∀ a, IsIncreasing (extraLocalBad a))
    (x : DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o)
    (hlower1 : ∀ r o, lowerWeight r o ≤ 1)
    (hupper0 : ∀ r o, 0 ≤ upperWeight r o)
    (hupper1 : ∀ r o, upperWeight r o ≤ 1)
    (hlowerLambda : ∀ r, 0 ≤ lowerLambda r)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b < 1)
    (hpair : ∀ c,
      q (left c) * q (right c) ≤ x (Sum.inl (Sum.inl c)) *
        ∏ b ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
          extraSupport (Sum.inl (Sum.inl c)), (1 - x b))
    (hlower : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
        (Real.exp (-lowerLambda r) - 1) * linearRowMean q lowerWeight r) ≤
        x (Sum.inl (Sum.inr (Sum.inl r))) *
          ∏ b ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
            extraSupport (Sum.inl (Sum.inr (Sum.inl r))), (1 - x b))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) * linearRowMean q upperWeight r) ≤
        x (Sum.inl (Sum.inr (Sum.inr r))) *
          ∏ b ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
            extraSupport (Sum.inl (Sum.inr (Sum.inr r))), (1 - x b))
    (hextra : ∀ a,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (extraSupport a)))
          (extraLocalBad a) ≤
        x (Sum.inr a) *
          ∏ b ∈ directNibbleExtraNeighbor left right lowerWeight upperWeight
            extraSupport (Sum.inr a), (1 - x b)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ r, lowerThreshold r <
        weightedSum
          (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
          (splitEquiv (linearRowSupport lowerWeight r) S).1) ∧
      (∀ r,
        weightedSum
          (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
          (splitEquiv (linearRowSupport upperWeight r) S).1 <
        upperThreshold r) ∧
      (∀ a, (splitEquiv (extraSupport a) S).1 ∉ extraLocalBad a) := by
  let support := directNibbleExtraSupport left right lowerWeight upperWeight
    extraSupport
  let localBad := directNibbleExtraLocalBad left right lowerWeight upperWeight
    lowerThreshold upperThreshold hne extraSupport extraLocalBad
  let polarity : DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra → Bool :=
    directNibbleExtraPolarity
  let neighbor := directNibbleExtraNeighbor left right lowerWeight upperWeight
    extraSupport
  have hmonoLocal : ∀ b, HasPolarity (polarity b) (localBad b) := by
    intro b
    rcases b with b | a
    · exact directNibbleLocalBad_hasPolarity left right lowerWeight upperWeight
        lowerThreshold upperThreshold hne hlower0 hupper0 b
    · change IsIncreasing (extraLocalBad a)
      exact hextraIncreasing a
  have hmonoGlobal : ∀ b, HasPolarity (polarity b)
      (insideCylinder (support b) (localBad b)) := by
    intro b
    cases hb : polarity b
    · change IsDecreasing (insideCylinder (support b) (localBad b))
      exact WeightedEdgeColoring.FiniteBernoulliCylinderMonotone.insideCylinder_isDecreasing
        (support b) (localBad b) (by
          simpa [HasPolarity, hb] using hmonoLocal b)
    · change IsIncreasing (insideCylinder (support b) (localBad b))
      exact WeightedEdgeColoring.FiniteBernoulliCylinderMonotone.insideCylinder_isIncreasing
        (support b) (localBad b) (by
          simpa [HasPolarity, hb] using hmonoLocal b)
  have hlocal : ∀ b,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (support b))) (localBad b) ≤
        x b * ∏ a ∈ neighbor b, (1 - x a) := by
    intro b
    rcases b with b | a
    · rcases b with c | r
      · change WeightedEdgeColoring.FiniteLocalLemma.eventMass
            (bernoulliMass
              (insideParameter q (conflictPairSupport left right c)))
            (conflictPairLocalBad left right hne c) ≤ _
        rw [conflictPairLocalBad_mass left right q hne c]
        exact hpair c
      · rcases r with r | r
        · exact (bernoulli_lowerTail_le
              (insideParameter q (linearRowSupport lowerWeight r))
              (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
              (lowerThreshold r) (lowerLambda r)
              (fun o ↦ hq0 o) (fun o ↦ hq1 o)
              (fun o ↦ hlower0 r o) (fun o ↦ hlower1 r o)
              (hlowerLambda r)).trans (hlower r)
        · exact (bernoulli_upperTail_le
              (insideParameter q (linearRowSupport upperWeight r))
              (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
              (upperThreshold r) (upperLambda r)
              (fun o ↦ hq0 o) (fun o ↦ hq1 o)
              (fun o ↦ hupper0 r o) (fun o ↦ hupper1 r o)
              (hupperLambda r)).trans (hupper r)
    · exact hextra a
  have hpositive :=
    WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided.asymmetric_lopsided_local_lemma_of_polarity_support_canonical
        q support localBad polarity x hq0 hq1 hx0 hx1 hmonoLocal
        hmonoGlobal hlocal
  exact H.extract_partialMatching_with_extra_of_positive left right lowerWeight
    upperWeight lowerThreshold upperThreshold hne hcomplete q extraSupport
    extraLocalBad (by
      change 0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (WeightedEdgeColoring.FiniteLocalLemma.avoid
          (fun b ↦ insideCylinder (support b) (localBad b)) Finset.univ)
      exact hpositive)

/-- Incidence-based four-weight criterion for arbitrary additional
increasing cylinder events.  Pair, upper-row, and extra events pay only the
lower-row weight `lowerX`.  A lower event pays the three independent
increasing weights, uniformly bounded by `cap`; the extra family enters
only through its per-coordinate incidence `E`. -/
theorem exists_partialMatching_with_extra_increasing_harris_of_incidence
    (H : RankThreeOptionSystem Job Slot Option)
    (left right : Conflict → Option) (q : Option → ℝ)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold lowerLambda : LowerRow → ℝ)
    (upperThreshold upperLambda : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬ H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨
        (left c = p ∧ right c = o))
    (extraSupport : Extra → Finset Option)
    (extraLocalBad : (a : Extra) → Finset (Finset (Inside (extraSupport a))))
    (hextraIncreasing : ∀ a, IsIncreasing (extraLocalBad a))
    (D R U E : ℕ) (pairX lowerX upperX cap : ℝ)
    (extraX : Extra → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o)
    (hlower1 : ∀ r o, lowerWeight r o ≤ 1)
    (hupper0 : ∀ r o, 0 ≤ upperWeight r o)
    (hupper1 : ∀ r o, upperWeight r o ≤ 1)
    (hlowerLambda : ∀ r, 0 ≤ lowerLambda r)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hpairX0 : 0 ≤ pairX) (hlowerX0 : 0 ≤ lowerX)
    (hupperX0 : 0 ≤ upperX) (hextraX0 : ∀ a, 0 ≤ extraX a)
    (hpairXcap : pairX ≤ cap) (hupperXcap : upperX ≤ cap)
    (hextraXcap : ∀ a, extraX a ≤ cap)
    (hlowerX1 : lowerX < 1) (hcap1 : cap < 1)
    (hconflictIncidence : ∀ o,
      (optionConflictIncidence left right o).card ≤ D)
    (hlowerIncidence : ∀ o,
      (linearRowIncidence lowerWeight o).card ≤ R)
    (hupperIncidence : ∀ o,
      (linearRowIncidence upperWeight o).card ≤ U)
    (hextraIncidence : ∀ o,
      (directNibbleExtraEventIncidence extraSupport o).card ≤ E)
    (hpair : ∀ c,
      q (left c) * q (right c) ≤
        pairX * (1 - lowerX) ^ (2 * R))
    (hlower : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
        (Real.exp (-lowerLambda r) - 1) * linearRowMean q lowerWeight r) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport lowerWeight r).card * (D + U + E)))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) * linearRowMean q upperWeight r) ≤
        upperX * (1 - lowerX) ^
          ((linearRowSupport upperWeight r).card * R))
    (hextra : ∀ a,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (extraSupport a)))
          (extraLocalBad a) ≤
        extraX a * (1 - lowerX) ^ ((extraSupport a).card * R)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ r, lowerThreshold r <
        weightedSum
          (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
          (splitEquiv (linearRowSupport lowerWeight r) S).1) ∧
      (∀ r,
        weightedSum
          (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
          (splitEquiv (linearRowSupport upperWeight r) S).1 <
        upperThreshold r) ∧
      (∀ a, (splitEquiv (extraSupport a) S).1 ∉ extraLocalBad a) := by
  let x : DirectNibbleExtraBadIndex Conflict LowerRow UpperRow Extra → ℝ :=
    directNibbleExtraLLLWeight pairX lowerX upperX extraX
  have hcap0 : 0 ≤ cap := hpairX0.trans hpairXcap
  have hx0 : ∀ b, 0 ≤ x b := by
    intro b
    rcases b with b | a
    · rcases b with c | r
      · exact hpairX0
      · rcases r with r | r
        · exact hlowerX0
        · exact hupperX0
    · exact hextraX0 a
  have hx1 : ∀ b, x b < 1 := by
    intro b
    rcases b with b | a
    · rcases b with c | r
      · exact hpairXcap.trans_lt hcap1
      · rcases r with r | r
        · exact hlowerX1
        · exact hupperXcap.trans_lt hcap1
    · exact (hextraXcap a).trans_lt hcap1
  apply H.exists_partialMatching_with_extra_increasing_harris
    left right q lowerWeight upperWeight lowerThreshold lowerLambda
    upperThreshold upperLambda hne hcomplete extraSupport extraLocalBad
    hextraIncreasing x hq0 hq1 hlower0 hlower1 hupper0 hupper1
    hlowerLambda hupperLambda hx0 hx1
  · intro c
    apply (hpair c).trans
    apply mul_le_mul_of_nonneg_left _ hpairX0
    exact directNibbleExtra_pair_product_lower_bound left right lowerWeight
      upperWeight extraSupport pairX lowerX upperX extraX R hlowerX0
      hlowerX1.le hlowerIncidence c
  · intro r
    apply (hlower r).trans
    apply mul_le_mul_of_nonneg_left _ hlowerX0
    exact directNibbleExtra_lower_product_lower_bound_of_incidence
      left right lowerWeight upperWeight extraSupport pairX lowerX upperX cap
      extraX D U E hcap0 hcap1.le hpairXcap hupperXcap hextraXcap
      hconflictIncidence hupperIncidence hextraIncidence r
  · intro r
    apply (hupper r).trans
    apply mul_le_mul_of_nonneg_left _ hupperX0
    exact directNibbleExtra_upper_product_lower_bound left right lowerWeight
      upperWeight extraSupport pairX lowerX upperX extraX R hlowerX0
      hlowerX1.le hlowerIncidence r
  · intro a
    apply (hextra a).trans
    apply mul_le_mul_of_nonneg_left _ (hextraX0 a)
    exact directNibbleExtra_event_product_lower_bound left right lowerWeight
      upperWeight extraSupport pairX lowerX upperX extraX R hlowerX0
      hlowerX1.le hlowerIncidence a

end WeightedEdgeColoring.RankThreeOptionSystem
