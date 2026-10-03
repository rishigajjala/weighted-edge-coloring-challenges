import WeightedEdgeColoring.WeightedMultigraph
import WeightedEdgeColoring.SimpleRoundingReduction
import WeightedEdgeColoring.OrdinarySlotOptions
import WeightedEdgeColoring.DivisibleLocalExtraSlotOptions
import WeightedEdgeColoring.PairUniqueOptions
import WeightedEdgeColoring.SeparatedOptionSystems

/-!
# Pair-codegree bounds for bounded-multiplicity multigraphs

The selected-profile rounding construction uses simplicity in one sharply
localized way: two distinct endpoint slots support at most one base option.
For a loopless multigraph whose endpoint-pair multiplicity is at most `L`,
the correct replacement is that the same pair of slots supports at most `L`
base options.  This file records that replacement at the graph-independent
option-system boundary and proves the resulting factor-`L` quantized
pair-codegree estimate.

The output remains one option system on all indexed edges.  In particular,
these lemmas coordinate parallel edges in the same matching construction;
they do not round simple layers independently.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u v w

namespace RankThreeOptionSystem

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]

/-- The base options using two fixed slots. -/
def pairSupport (H : RankThreeOptionSystem Job Slot Option)
    (s t : Slot) : Finset Option :=
  Finset.univ.filter fun o ↦ s ∈ H.slots o ∧ t ∈ H.slots o

@[simp] theorem mem_pairSupport_iff
    (H : RankThreeOptionSystem Job Slot Option) (s t : Slot) (o : Option) :
    o ∈ H.pairSupport s t ↔ s ∈ H.slots o ∧ t ∈ H.slots o := by
  simp [pairSupport]

/-- Every two distinct slots occur together in at most `L` base options. -/
def PairSupportBounded (H : RankThreeOptionSystem Job Slot Option)
    (L : ℕ) : Prop :=
  ∀ ⦃s t : Slot⦄, s ≠ t → (H.pairSupport s t).card ≤ L

/-- Pair uniqueness is the special case `L = 1`. -/
theorem PairUnique.pairSupportBounded_one
    (H : RankThreeOptionSystem Job Slot Option) (hunique : H.PairUnique) :
    H.PairSupportBounded 1 := by
  intro s t hst
  exact H.card_pairSupport_le_one hunique hst

/-- A bounded base pair support gives the corresponding unreplicated
slot-pair codegree bound. -/
theorem slotPairCodegree_le_of_pairSupportBounded
    (H : RankThreeOptionSystem Job Slot Option)
    {L : ℕ} (hbounded : H.PairSupportBounded L)
    {s t : Slot} (hst : s ≠ t) :
    H.slotPairCodegree s t ≤ L := by
  exact hbounded hst

/-- If every base option has mass at most `tau`, floor replication multiplies
the simple-graph pair-codegree estimate by at most the endpoint-pair
multiplicity `L`. -/
theorem quantized_slotPairCodegree_le_of_pairSupportBounded
    (H : RankThreeOptionSystem Job Slot Option)
    {L : ℕ} (hbounded : H.PairSupportBounded L)
    (N : ℕ) (x : Option → ℝ) (tau : ℝ)
    (htau0 : 0 ≤ tau) (hx0 : ∀ o, 0 ≤ x o)
    (hxtau : ∀ o, x o ≤ tau)
    {s t : Slot} (hst : s ≠ t) :
    (((H.quantized N x).slotPairCodegree s t : ℕ) : ℝ) ≤
      (L : ℝ) * (N : ℝ) * tau := by
  classical
  let A : Finset Option := H.pairSupport s t
  have hA : A.card ≤ L := hbounded hst
  rw [H.quantized_slotPairCodegree, Nat.cast_sum]
  have hrewrite :
      (∑ o, ((if s ∈ H.slots o ∧ t ∈ H.slots o then
          quantizedMultiplicity N (x o) else 0 : ℕ) : ℝ)) =
        ∑ o ∈ A, (quantizedMultiplicity N (x o) : ℝ) := by
    simp only [Nat.cast_ite, Nat.cast_zero]
    rw [← Finset.sum_filter]
    rfl
  rw [hrewrite]
  calc
    (∑ o ∈ A, (quantizedMultiplicity N (x o) : ℝ)) ≤
        ∑ _o ∈ A, (N : ℝ) * tau := by
      apply Finset.sum_le_sum
      intro o _ho
      calc
        (quantizedMultiplicity N (x o) : ℝ) ≤ (N : ℝ) * x o :=
          Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hx0 o))
        _ ≤ (N : ℝ) * tau :=
          mul_le_mul_of_nonneg_left (hxtau o) (Nat.cast_nonneg N)
    _ = (A.card : ℝ) * ((N : ℝ) * tau) := by simp
    _ ≤ (L : ℝ) * ((N : ℝ) * tau) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hA)
        (mul_nonneg (Nat.cast_nonneg N) htau0)
    _ = (L : ℝ) * (N : ℝ) * tau := by ring

universe v₂ w₂

variable {Slot₂ : Type v₂} {Option₂ : Type w₂}
  [Fintype Slot₂] [Fintype Option₂]
  [DecidableEq Slot₂] [DecidableEq Option₂]

/-- Separated composition preserves a common pair-support bound.  A mixed
ordinary/extra slot pair has empty support. -/
theorem separatedSum_pairSupportBounded
    (H : RankThreeOptionSystem Job Slot Option)
    (K : RankThreeOptionSystem Job Slot₂ Option₂)
    {L : ℕ} (hH : H.PairSupportBounded L)
    (hK : K.PairSupportBounded L) :
    (H.separatedSum K).PairSupportBounded L := by
  classical
  intro s t hst
  cases s with
  | inl s =>
      cases t with
      | inl t =>
          have hst' : s ≠ t := by
            intro h
            exact hst (congrArg Sum.inl h)
          have hsupp :
              (H.separatedSum K).pairSupport (Sum.inl s) (Sum.inl t) =
                (H.pairSupport s t).map
                  (⟨Sum.inl, Sum.inl_injective⟩ : Option ↪ Option ⊕ Option₂) := by
            ext z
            cases z <;>
              simp [pairSupport, separatedSum, sum, liftSlotsLeft,
                liftSlotsRight, sumInlEmbedding, sumInrEmbedding]
          rw [hsupp, Finset.card_map]
          exact hH hst'
      | inr t =>
          have hsupp :
              (H.separatedSum K).pairSupport (Sum.inl s) (Sum.inr t) =
                ∅ := by
            ext z
            cases z <;>
              simp [pairSupport, separatedSum, sum, liftSlotsLeft,
                liftSlotsRight, sumInlEmbedding, sumInrEmbedding]
          simp [hsupp]
  | inr s =>
      cases t with
      | inl t =>
          have hsupp :
              (H.separatedSum K).pairSupport (Sum.inr s) (Sum.inl t) =
                ∅ := by
            ext z
            cases z <;>
              simp [pairSupport, separatedSum, sum, liftSlotsLeft,
                liftSlotsRight, sumInlEmbedding, sumInrEmbedding]
          simp [hsupp]
      | inr t =>
          have hst' : s ≠ t := by
            intro h
            exact hst (congrArg Sum.inr h)
          have hsupp :
              (H.separatedSum K).pairSupport (Sum.inr s) (Sum.inr t) =
                (K.pairSupport s t).map
                  (⟨Sum.inr, Sum.inr_injective⟩ : Option₂ ↪ Option ⊕ Option₂) := by
            ext z
            cases z <;>
              simp [pairSupport, separatedSum, sum, liftSlotsLeft,
                liftSlotsRight, sumInlEmbedding, sumInrEmbedding]
          rw [hsupp, Finset.card_map]
          exact hK hst'

end RankThreeOptionSystem

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})

/-- The unordered endpoint pair of an indexed multigraph edge. -/
def endpoints (e : G.E) : Sym2 G.V := s(G.fst e, G.snd e)

/-- All indexed edges joining one unordered pair of vertices. -/
def endpointPairCell (u v : G.V) : Finset G.E :=
  Finset.univ.filter fun e ↦ G.endpoints e = s(u, v)

@[simp] theorem mem_endpointPairCell_iff (u v : G.V) (e : G.E) :
    e ∈ G.endpointPairCell u v ↔ G.endpoints e = s(u, v) := by
  simp [endpointPairCell]

/-- Uniform bound on the number of indexed edges with one unordered endpoint
pair.  This is the multigraph replacement for simplicity. -/
def PairMultiplicityAtMost (L : ℕ) : Prop :=
  ∀ u v, (G.endpointPairCell u v).card ≤ L

/-- An indexed edge joins the displayed vertices, in either orientation.
This is the multigraph form of the candidate-row matching predicate used by
the selected-profile construction. -/
def EndpointPairMatches (u v : G.V) (e : G.E) : Prop :=
  (u = G.fst e ∧ v = G.snd e) ∨
    (u = G.snd e ∧ v = G.fst e)

instance instDecidableEndpointPairMatches (u v : G.V) :
    DecidablePred (G.EndpointPairMatches u v) := by
  intro e
  unfold EndpointPairMatches
  infer_instance

theorem mem_endpointPairCell_iff_endpointPairMatches
    (u v : G.V) (e : G.E) :
    e ∈ G.endpointPairCell u v ↔ G.EndpointPairMatches u v e := by
  rw [G.mem_endpointPairCell_iff]
  constructor
  · intro h
    rcases (Sym2.eq_iff).mp h with h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.2.symm, h.1.symm⟩
  · intro h
    apply (Sym2.eq_iff).2
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.2.symm, h.1.symm⟩

/-- The fixed displayed endpoint pair supports at most `L` indexed edges. -/
theorem endpointPairMatches_card_le
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L) (u v : G.V) :
    ((Finset.univ : Finset G.E).filter
      (G.EndpointPairMatches u v)).card ≤ L := by
  have heq :
      (Finset.univ : Finset G.E).filter (G.EndpointPairMatches u v) =
        G.endpointPairCell u v := by
    ext e
    simp [G.mem_endpointPairCell_iff_endpointPairMatches]
  rw [heq]
  exact hmult u v

/-- Bounded endpoint multiplicity replaces the simple-graph `sum_eq_single`
step in candidate-capacity and variance rows.  If an edge term is zero off one
endpoint pair and at most `A` on that pair, the whole edge sum is
at most `L * A`. -/
theorem sum_le_mul_of_pairMultiplicityAtMost
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L)
    (u v : G.V) (f : G.E → ℝ) (A : ℝ)
    (hA : 0 ≤ A)
    (hfA : ∀ e, G.EndpointPairMatches u v e → f e ≤ A)
    (hoff : ∀ e, ¬ G.EndpointPairMatches u v e → f e = 0) :
    (∑ e : G.E, f e) ≤ (L : ℝ) * A := by
  classical
  let F : Finset G.E :=
    Finset.univ.filter (G.EndpointPairMatches u v)
  have hF : F.card ≤ L := by
    exact G.endpointPairMatches_card_le hmult u v
  calc
    (∑ e : G.E, f e) =
        ∑ e : G.E, if G.EndpointPairMatches u v e then f e else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hmatch : G.EndpointPairMatches u v e
      · simp [hmatch]
      · simp [hmatch, hoff e hmatch]
    _ = ∑ e ∈ F, f e := by
      rw [← Finset.sum_filter]
    _ ≤ ∑ _e ∈ F, A := by
      apply Finset.sum_le_sum
      intro e he
      exact hfA e (Finset.mem_filter.mp he).2
    _ = (F.card : ℝ) * A := by simp
    _ ≤ (L : ℝ) * A := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hF) hA

/-- Simplicity of a weighted simple graph is exactly pair multiplicity at most
one after forgetting the simplicity field. -/
theorem pairMultiplicityAtMost_one_of_simple
    (S : WeightedSimpleGraph.{u}) :
    S.asMultigraph.PairMultiplicityAtMost 1 := by
  intro u v
  rw [Finset.card_le_one]
  intro e he f hf
  apply S.endpoints_injective
  exact ((S.asMultigraph.mem_endpointPairCell_iff u v e).mp he).trans
    ((S.asMultigraph.mem_endpointPairCell_iff u v f).mp hf).symm

variable {G}

private theorem ordinarySlotChoice_job_injective_on_pairSupport
    {Color : Type w} [Fintype Color] [DecidableEq Color]
    (K : ℕ) (s t : OrdinarySlot G.V Color K) (hst : s ≠ t) :
    Set.InjOn OrdinarySlotChoice.job
      (↑((OrdinarySlotChoice.system (Job := G.E) (Vertex := G.V)
        (Color := Color) G.fst G.snd K).pairSupport s t) :
          Set (OrdinarySlotChoice G.E Color K)) := by
  intro q hq p hp hj
  let H := OrdinarySlotChoice.system (Job := G.E) (Vertex := G.V)
    (Color := Color) G.fst G.snd K
  have hqmem : s ∈ H.slots q ∧ t ∈ H.slots q := by
    simpa [H] using
      (RankThreeOptionSystem.mem_pairSupport_iff H s t q).mp hq
  have hpmem : s ∈ H.slots p ∧ t ∈ H.slots p := by
    simpa [H] using
      (RankThreeOptionSystem.mem_pairSupport_iff H s t p).mp hp
  have orient (z : OrdinarySlotChoice G.E Color K)
      (hsz : s ∈ H.slots z) (htz : t ∈ H.slots z) :
      (s = OrdinarySlotChoice.leftSlot G.fst K z ∧
        t = OrdinarySlotChoice.rightSlot G.snd K z) ∨
      (s = OrdinarySlotChoice.rightSlot G.snd K z ∧
        t = OrdinarySlotChoice.leftSlot G.fst K z) := by
    simp only [H, OrdinarySlotChoice.system, Finset.mem_insert,
      Finset.mem_singleton] at hsz htz
    rcases hsz with hs | hs <;> rcases htz with ht | ht
    · exact (hst (hs.trans ht.symm)).elim
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, ht⟩
    · exact (hst (hs.trans ht.symm)).elim
  have hqorient := orient q hqmem.1 hqmem.2
  have hporient := orient p hpmem.1 hpmem.2
  rcases q with ⟨e, c, i, j⟩
  rcases p with ⟨f, d, k, l⟩
  dsimp at hj
  subst f
  rcases hqorient with hq | hq <;> rcases hporient with hp | hp
  · have hleft := hq.1.symm.trans hp.1
    have hright := hq.2.symm.trans hp.2
    have hcd : c = d := congrArg OrdinarySlot.color hleft
    have hik : i = k := congrArg OrdinarySlot.place hleft
    have hjl : j = l := congrArg OrdinarySlot.place hright
    subst d
    subst k
    subst l
    rfl
  · have hleftRight := hq.1.symm.trans hp.1
    exact (G.noLoop e
      (congrArg OrdinarySlot.vertex hleftRight)).elim
  · have hleftRight := hq.2.symm.trans hp.2
    exact (G.noLoop e
      (congrArg OrdinarySlot.vertex hleftRight)).elim
  · have hleft := hq.2.symm.trans hp.2
    have hright := hq.1.symm.trans hp.1
    have hcd : c = d := congrArg OrdinarySlot.color hleft
    have hik : i = k := congrArg OrdinarySlot.place hleft
    have hjl : j = l := congrArg OrdinarySlot.place hright
    subst d
    subst k
    subst l
    rfl

/-- Ordinary color/place choices on a loopless multigraph have pair support
bounded by the graph's endpoint-pair multiplicity. -/
theorem ordinarySlotChoice_pairSupportBounded
    {Color : Type w} [Fintype Color] [DecidableEq Color]
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L) (K : ℕ) :
    (OrdinarySlotChoice.system (Job := G.E) (Vertex := G.V)
      (Color := Color) G.fst G.snd K).PairSupportBounded L := by
  intro s t hst
  let H := OrdinarySlotChoice.system (Job := G.E) (Vertex := G.V)
    (Color := Color) G.fst G.snd K
  have hmaps :
      ((H.pairSupport s t : Finset (OrdinarySlotChoice G.E Color K)) :
          Set (OrdinarySlotChoice G.E Color K)).MapsTo
        OrdinarySlotChoice.job (G.endpointPairCell s.vertex t.vertex) := by
    intro q hq
    have hmem : s ∈ H.slots q ∧ t ∈ H.slots q :=
      (RankThreeOptionSystem.mem_pairSupport_iff H s t q).mp hq
    have horient :
        (s = OrdinarySlotChoice.leftSlot G.fst K q ∧
          t = OrdinarySlotChoice.rightSlot G.snd K q) ∨
        (s = OrdinarySlotChoice.rightSlot G.snd K q ∧
          t = OrdinarySlotChoice.leftSlot G.fst K q) := by
      simp only [H, OrdinarySlotChoice.system, Finset.mem_insert,
        Finset.mem_singleton] at hmem
      rcases hmem.1 with hs | hs <;> rcases hmem.2 with ht | ht
      · exact (hst (hs.trans ht.symm)).elim
      · exact Or.inl ⟨hs, ht⟩
      · exact Or.inr ⟨hs, ht⟩
      · exact (hst (hs.trans ht.symm)).elim
    apply (G.mem_endpointPairCell_iff s.vertex t.vertex q.job).mpr
    rcases horient with h | h
    · apply (Sym2.eq_iff).2
      exact Or.inl
        ⟨(congrArg OrdinarySlot.vertex h.1).symm,
          (congrArg OrdinarySlot.vertex h.2).symm⟩
    · apply (Sym2.eq_iff).2
      exact Or.inr
        ⟨(congrArg OrdinarySlot.vertex h.2).symm,
          (congrArg OrdinarySlot.vertex h.1).symm⟩
  exact (Finset.card_le_card_of_injOn OrdinarySlotChoice.job hmaps
    (ordinarySlotChoice_job_injective_on_pairSupport
      (G := G) K s t hst)).trans (hmult s.vertex t.vertex)

private theorem divisibleLocalExtraChoice_job_injective_on_pairSupport
    {Class : Type w} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (hleftDiv : ∀ e, B (G.fst e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (hrightDiv : ∀ e, B (G.snd e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (hleft : ∀ e, 0 < B (G.fst e) (bucket e))
    (hright : ∀ e, 0 < B (G.snd e) (bucket e))
    (s t : ExtraSlot G.V Class B) (hst : s ≠ t) :
    Set.InjOn Sigma.fst
      (↑((DivisibleLocalExtraChoice.system G.fst G.snd bucket B
        hleftDiv hrightDiv).pairSupport s t) :
          Set (DivisibleLocalExtraChoice G.E G.V Class
            G.fst G.snd bucket B)) := by
  let H := DivisibleLocalExtraChoice.system G.fst G.snd bucket B
    hleftDiv hrightDiv
  intro q hq p hp hj
  have hqmem : s ∈ H.slots q ∧ t ∈ H.slots q := by
    simpa [H] using
      (RankThreeOptionSystem.mem_pairSupport_iff H s t q).mp hq
  have hpmem : s ∈ H.slots p ∧ t ∈ H.slots p := by
    simpa [H] using
      (RankThreeOptionSystem.mem_pairSupport_iff H s t p).mp hp
  have orient (z : DivisibleLocalExtraChoice G.E G.V Class
      G.fst G.snd bucket B)
      (hsz : s ∈ H.slots z) (htz : t ∈ H.slots z) :
      (s = DivisibleLocalExtraChoice.leftSlot G.fst G.snd bucket B
          hleftDiv z ∧
        t = DivisibleLocalExtraChoice.rightSlot G.fst G.snd bucket B
          hrightDiv z) ∨
      (s = DivisibleLocalExtraChoice.rightSlot G.fst G.snd bucket B
          hrightDiv z ∧
        t = DivisibleLocalExtraChoice.leftSlot G.fst G.snd bucket B
          hleftDiv z) := by
    simp only [H, DivisibleLocalExtraChoice.system, Finset.mem_insert,
      Finset.mem_singleton] at hsz htz
    rcases hsz with hs | hs <;> rcases htz with ht | ht
    · exact (hst (hs.trans ht.symm)).elim
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, ht⟩
    · exact (hst (hs.trans ht.symm)).elim
  have hqorient := orient q hqmem.1 hqmem.2
  have hporient := orient p hpmem.1 hpmem.2
  rcases q with ⟨e, i⟩
  rcases p with ⟨f, k⟩
  dsimp at hj
  subst f
  rcases hqorient with hq | hq <;> rcases hporient with hp | hp
  · have hl := hq.1.symm.trans hp.1
    have hr := hq.2.symm.trans hp.2
    have hiLeft :
        DivisibleLocalExtraChoice.leftIndex G.fst G.snd bucket B hleftDiv
            ⟨e, i⟩ =
          DivisibleLocalExtraChoice.leftIndex G.fst G.snd bucket B hleftDiv
            ⟨e, k⟩ := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hl)
    have hiRight :
        DivisibleLocalExtraChoice.rightIndex G.fst G.snd bucket B hrightDiv
            ⟨e, i⟩ =
          DivisibleLocalExtraChoice.rightIndex G.fst G.snd bucket B hrightDiv
            ⟨e, k⟩ := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hr)
    have hik : i = k := by
      rcases le_total (B (G.fst e) (bucket e))
          (B (G.snd e) (bucket e)) with hle | hle
      · exact DivisibleLocalExtraChoice.rightIndex_injective_of_left_le
          G.fst G.snd bucket B hrightDiv hright e hle hiRight
      · exact DivisibleLocalExtraChoice.leftIndex_injective_of_right_le
          G.fst G.snd bucket B hleftDiv hleft e hle hiLeft
    subst k
    rfl
  · have hlr := hq.1.symm.trans hp.1
    exact (G.noLoop e
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hlr)).elim
  · have hlr := hq.2.symm.trans hp.2
    exact (G.noLoop e
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) hlr)).elim
  · have hr := hq.1.symm.trans hp.1
    have hl := hq.2.symm.trans hp.2
    have hiLeft :
        DivisibleLocalExtraChoice.leftIndex G.fst G.snd bucket B hleftDiv
            ⟨e, i⟩ =
          DivisibleLocalExtraChoice.leftIndex G.fst G.snd bucket B hleftDiv
            ⟨e, k⟩ := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hl)
    have hiRight :
        DivisibleLocalExtraChoice.rightIndex G.fst G.snd bucket B hrightDiv
            ⟨e, i⟩ =
          DivisibleLocalExtraChoice.rightIndex G.fst G.snd bucket B hrightDiv
            ⟨e, k⟩ := Fin.ext
      (congrArg (fun z : ExtraSlot G.V Class B ↦ z.2.val) hr)
    have hik : i = k := by
      rcases le_total (B (G.fst e) (bucket e))
          (B (G.snd e) (bucket e)) with hle | hle
      · exact DivisibleLocalExtraChoice.rightIndex_injective_of_left_le
          G.fst G.snd bucket B hrightDiv hright e hle hiRight
      · exact DivisibleLocalExtraChoice.leftIndex_injective_of_right_le
          G.fst G.snd bucket B hleftDiv hleft e hle hiLeft
    subst k
    rfl

/-- The sparse divisible extra-slot family has the same multiplicity-`L`
pair-support bound as the underlying multigraph. -/
theorem divisibleLocalExtraChoice_pairSupportBounded
    {Class : Type w} [Fintype Class] [DecidableEq Class]
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L)
    (bucket : G.E → Class) (B : G.V → Class → ℕ)
    (hleftDiv : ∀ e, B (G.fst e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (hrightDiv : ∀ e, B (G.snd e) (bucket e) ∣
      DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket B e)
    (hleft : ∀ e, 0 < B (G.fst e) (bucket e))
    (hright : ∀ e, 0 < B (G.snd e) (bucket e)) :
    (DivisibleLocalExtraChoice.system G.fst G.snd bucket B
      hleftDiv hrightDiv).PairSupportBounded L := by
  intro s t hst
  let H := DivisibleLocalExtraChoice.system G.fst G.snd bucket B
    hleftDiv hrightDiv
  have hmaps :
      ((H.pairSupport s t : Finset
          (DivisibleLocalExtraChoice G.E G.V Class G.fst G.snd bucket B)) :
          Set (DivisibleLocalExtraChoice G.E G.V Class
            G.fst G.snd bucket B)).MapsTo
        Sigma.fst (G.endpointPairCell s.1.1 t.1.1) := by
    intro q hq
    have hmem : s ∈ H.slots q ∧ t ∈ H.slots q :=
      (RankThreeOptionSystem.mem_pairSupport_iff H s t q).mp hq
    have horient :
        (s = DivisibleLocalExtraChoice.leftSlot G.fst G.snd bucket B
            hleftDiv q ∧
          t = DivisibleLocalExtraChoice.rightSlot G.fst G.snd bucket B
            hrightDiv q) ∨
        (s = DivisibleLocalExtraChoice.rightSlot G.fst G.snd bucket B
            hrightDiv q ∧
          t = DivisibleLocalExtraChoice.leftSlot G.fst G.snd bucket B
            hleftDiv q) := by
      simp only [H, DivisibleLocalExtraChoice.system, Finset.mem_insert,
        Finset.mem_singleton] at hmem
      rcases hmem.1 with hs | hs <;> rcases hmem.2 with ht | ht
      · exact (hst (hs.trans ht.symm)).elim
      · exact Or.inl ⟨hs, ht⟩
      · exact Or.inr ⟨hs, ht⟩
      · exact (hst (hs.trans ht.symm)).elim
    apply (G.mem_endpointPairCell_iff s.1.1 t.1.1 q.1).mpr
    rcases horient with h | h
    · apply (Sym2.eq_iff).2
      exact Or.inl
        ⟨(congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) h.1).symm,
          (congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) h.2).symm⟩
    · apply (Sym2.eq_iff).2
      exact Or.inr
        ⟨(congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) h.2).symm,
          (congrArg (fun z : ExtraSlot G.V Class B ↦ z.1.1) h.1).symm⟩
  exact (Finset.card_le_card_of_injOn Sigma.fst hmaps
    (divisibleLocalExtraChoice_job_injective_on_pairSupport
      (G := G) bucket B hleftDiv hrightDiv hleft hright s t hst)).trans
        (hmult s.1.1 t.1.1)

end WeightedMultigraph

end

end WeightedEdgeColoring
