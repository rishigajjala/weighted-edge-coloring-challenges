import WeightedEdgeColoring.BPBalancedSelection
import WeightedEdgeColoring.BPDiscountedCharge
import WeightedEdgeColoring.BPGeneralSelectedColoring
import WeightedEdgeColoring.BPEdgeRestriction
import WeightedEdgeColoring.BPLocalCharge

/-!
# The finite reduction for the general multigraph `bp` bound

This file carries out the finite selection step in the proof of the
`(h∞ + 2/5) bp + o(bp)` bound.  It does not use the later theorem that colors
an arbitrary residual from its harmonic charge.

We select the fraction `t*` of the edges in the two compatible ranges
`(1/2,3/5]` and `(1/3,2/5]`.  The selected part receives an explicit
Shannon palette.  At each vertex the unselected part has harmonic charge at
most `(8/5) bp + 3`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Edges in the upper range used by the general-multigraph selection. -/
noncomputable def generalUpperRange : Finset G.E :=
  Finset.univ.filter fun e =>
    (1 / 2 : ℝ) < G.weight e ∧ G.weight e ≤ 3 / 5

/-- Edges in the lower range used by the general-multigraph selection. -/
noncomputable def generalLowerRange : Finset G.E :=
  Finset.univ.filter fun e =>
    (1 / 3 : ℝ) < G.weight e ∧ G.weight e ≤ 2 / 5

/-- The degree parameter for the selected-edge Shannon palette. -/
noncomputable def generalSelectionK : ℕ :=
  Nat.ceil (harmonicSelectionFraction * (G.bp : ℝ)) + 2

/-- Charge of a specified edge set at a vertex. -/
noncomputable def chargeOn (charge : ℝ → ℝ) (R : Finset G.E)
    (v : G.V) : ℝ :=
  ∑ e ∈ R, if G.Inc v e then charge (G.weight e) else 0

/-- Harmonic charge of a specified edge set at a vertex. -/
noncomputable def harmonicChargeOn (R : Finset G.E) (v : G.V) : ℝ :=
  G.chargeOn harmonicCharge R v

theorem chargeOn_union {charge : ℝ → ℝ} {A B : Finset G.E}
    (h : Disjoint A B) (v : G.V) :
    G.chargeOn charge (A ∪ B) v =
      G.chargeOn charge A v + G.chargeOn charge B v := by
  unfold chargeOn
  rw [Finset.sum_union h]

theorem starCharge_eq_chargeOn_univ (charge : ℝ → ℝ) (v : G.V) :
    G.starCharge charge v = G.chargeOn charge Finset.univ v := by
  classical
  unfold starCharge chargeOn
  rw [show (∑ e : G.StarEdge v, charge (G.weight e.1)) =
      ∑ e ∈ Finset.univ.filter (G.Inc v), charge (G.weight e) by
    exact (Finset.sum_subtype (Finset.univ.filter (G.Inc v))
      (by intro e; simp) (fun e => charge (G.weight e))).symm]
  simp [← Finset.sum_filter]

/-- The star charge in an edge restriction is the charge of that edge set
computed in the original graph. -/
theorem edgeRestriction_starCharge (charge : ℝ → ℝ)
    (R : Finset G.E) (v : G.V) :
    (G.edgeRestriction R).starCharge charge v = G.chargeOn charge R v := by
  classical
  unfold starCharge chargeOn
  change
    (∑ e : {e : (G.edgeRestriction R).E // G.Inc v e.1},
      charge (G.weight e.1.1)) = _
  calc
    _ = ∑ e ∈ (Finset.univ : Finset {e : G.E // e ∈ R}).filter
          (fun e => G.Inc v e.1), charge (G.weight e.1) := by
      symm
      exact Finset.sum_subtype
        (p := fun e : {e : G.E // e ∈ R} => G.Inc v e.1)
        ((Finset.univ : Finset {e : G.E // e ∈ R}).filter
          (fun e => G.Inc v e.1)) (by simp)
        (fun e => charge (G.weight e.1))
    _ = ∑ e : {e : G.E // e ∈ R},
        if G.Inc v e.1 then charge (G.weight e.1) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ e ∈ R,
        if G.Inc v e then charge (G.weight e) else 0 := by
      symm
      exact Finset.sum_subtype (p := fun e : G.E => e ∈ R) R (by simp)
        (fun e => if G.Inc v e then charge (G.weight e) else 0)

theorem generalUpperRange_disjoint_generalLowerRange :
    Disjoint G.generalUpperRange G.generalLowerRange := by
  classical
  rw [Finset.disjoint_left]
  intro e heA heB
  have hA := (Finset.mem_filter.mp heA).2
  have hB := (Finset.mem_filter.mp heB).2
  norm_num at hA hB
  linarith

theorem generalUpperRange_weight_upper {e : G.E}
    (he : e ∈ G.generalUpperRange) : G.weight e ≤ 3 / 5 :=
  (Finset.mem_filter.mp he).2.2

theorem generalLowerRange_weight_upper {e : G.E}
    (he : e ∈ G.generalLowerRange) : G.weight e ≤ 2 / 5 :=
  (Finset.mem_filter.mp he).2.2

theorem harmonicCharge_eq_one_of_mem_generalUpperRange {e : G.E}
    (he : e ∈ G.generalUpperRange) :
    harmonicCharge (G.weight e) = 1 := by
  have h := (Finset.mem_filter.mp he).2
  have hu : G.weight e ≤ (1 : ℝ) / (1 : ℕ) := by
    norm_num
    exact h.2.trans (by norm_num)
  have hl : (1 : ℝ) / ((1 : ℕ) + 1) < G.weight e := by
    norm_num
    exact h.1
  simpa using
    (harmonicCharge_eq_of_band (r := 1) (by norm_num)
      (G.weight_pos e) hu hl)

theorem harmonicCharge_eq_half_of_mem_generalLowerRange {e : G.E}
    (he : e ∈ G.generalLowerRange) :
    harmonicCharge (G.weight e) = 1 / 2 := by
  have h := (Finset.mem_filter.mp he).2
  apply harmonicCharge_eq_of_band (r := 2) (by norm_num) (G.weight_pos e)
  · norm_num
    exact h.2.trans (by norm_num)
  · norm_num
    exact h.1

theorem mem_upper_union_lower_iff_discountedRange (e : G.E) :
    e ∈ G.generalUpperRange ∪ G.generalLowerRange ↔
      inDiscountedWeightRanges (G.weight e) := by
  classical
  simp only [generalUpperRange, generalLowerRange, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and,
    inDiscountedWeightRanges]

theorem harmonicChargeOn_generalUpperRange (v : G.V) :
    G.harmonicChargeOn G.generalUpperRange v =
      (G.degreeOn G.generalUpperRange v : ℝ) := by
  classical
  unfold harmonicChargeOn chargeOn degreeOn
  rw [← Finset.sum_filter]
  calc
    (∑ e ∈ G.generalUpperRange.filter (G.Inc v),
        harmonicCharge (G.weight e)) =
        ∑ _e ∈ G.generalUpperRange.filter (G.Inc v), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      exact G.harmonicCharge_eq_one_of_mem_generalUpperRange
        (Finset.mem_filter.mp he).1
    _ = (G.generalUpperRange.filter (G.Inc v)).card := by simp

theorem harmonicChargeOn_generalLowerRange (v : G.V) :
    G.harmonicChargeOn G.generalLowerRange v =
      (G.degreeOn G.generalLowerRange v : ℝ) / 2 := by
  classical
  unfold harmonicChargeOn chargeOn degreeOn
  rw [← Finset.sum_filter]
  calc
    (∑ e ∈ G.generalLowerRange.filter (G.Inc v),
        harmonicCharge (G.weight e)) =
        ∑ _e ∈ G.generalLowerRange.filter (G.Inc v), (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      exact G.harmonicCharge_eq_half_of_mem_generalLowerRange
        (Finset.mem_filter.mp he).1
    _ = (G.generalLowerRange.filter (G.Inc v)).card / 2 := by
      simp [div_eq_mul_inv]

theorem harmonicChargeOn_selectedUpper {F : Finset G.E}
    (hF : F ⊆ G.generalUpperRange) (v : G.V) :
    G.harmonicChargeOn F v = (G.degreeOn F v : ℝ) := by
  classical
  unfold harmonicChargeOn chargeOn degreeOn
  rw [← Finset.sum_filter]
  calc
    (∑ e ∈ F.filter (G.Inc v), harmonicCharge (G.weight e)) =
        ∑ _e ∈ F.filter (G.Inc v), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      exact G.harmonicCharge_eq_one_of_mem_generalUpperRange
        (hF (Finset.mem_filter.mp he).1)
    _ = (F.filter (G.Inc v)).card := by simp

theorem harmonicChargeOn_selectedLower {F : Finset G.E}
    (hF : F ⊆ G.generalLowerRange) (v : G.V) :
    G.harmonicChargeOn F v = (G.degreeOn F v : ℝ) / 2 := by
  classical
  unfold harmonicChargeOn chargeOn degreeOn
  rw [← Finset.sum_filter]
  calc
    (∑ e ∈ F.filter (G.Inc v), harmonicCharge (G.weight e)) =
        ∑ _e ∈ F.filter (G.Inc v), (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      exact G.harmonicCharge_eq_half_of_mem_generalLowerRange
        (hF (Finset.mem_filter.mp he).1)
    _ = (F.filter (G.Inc v)).card / 2 := by
      simp [div_eq_mul_inv]

/-- The discounted star charge is the full harmonic charge minus a fraction
`t` of the charge in the two selected ranges. -/
theorem starCharge_discounted_identity (t : ℝ) (v : G.V) :
    G.starCharge (discountedHarmonicCharge t) v =
      G.harmonicChargeOn Finset.univ v -
        t * G.harmonicChargeOn
          (G.generalUpperRange ∪ G.generalLowerRange) v := by
  classical
  rw [G.starCharge_eq_chargeOn_univ]
  unfold harmonicChargeOn chargeOn
  have hDsum :
      t * ∑ e ∈ G.generalUpperRange ∪ G.generalLowerRange,
          (if G.Inc v e then harmonicCharge (G.weight e) else 0) =
        ∑ e ∈ (Finset.univ : Finset G.E),
          if e ∈ G.generalUpperRange ∪ G.generalLowerRange then
            t * (if G.Inc v e then harmonicCharge (G.weight e) else 0)
          else 0 := by
    rw [Finset.mul_sum]
    have hfilter :
        (Finset.univ.filter fun e : G.E =>
          e ∈ G.generalUpperRange ∪ G.generalLowerRange) =
          G.generalUpperRange ∪ G.generalLowerRange := by
      ext e
      simp
    rw [← Finset.sum_filter, hfilter]
  rw [hDsum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hinc : G.Inc v e
  · rw [if_pos hinc]
    by_cases hD : e ∈ G.generalUpperRange ∪ G.generalLowerRange
    · have hrange := (G.mem_upper_union_lower_iff_discountedRange e).mp hD
      simp only [discountedHarmonicCharge, if_pos hrange,
        if_pos hinc, if_pos hD]
      ring
    · have hrange : ¬inDiscountedWeightRanges (G.weight e) := by
        exact fun h => hD ((G.mem_upper_union_lower_iff_discountedRange e).mpr h)
      simp only [discountedHarmonicCharge, if_neg hrange,
        if_pos hinc, if_neg hD, sub_zero]
  · simp [hinc]

/-- The one-bin discounted-charge lemma applied to all `bp(G)` local bins. -/
theorem discountedStarCharge_at_selection_le (v : G.V) :
    G.starCharge
        (discountedHarmonicCharge harmonicSelectionFraction) v ≤
      (G.bp : ℝ) * (8 / 5 : ℝ) := by
  apply G.starCharge_le_mul_of_packsStarInto
    (discountedHarmonicCharge harmonicSelectionFraction) (8 / 5 : ℝ)
    (G.locallyPacksInto_bp v)
  intro S hload
  exact discountedHarmonicCharge_sum_at_selection_le_eight_fifths
    S (fun e => G.weight e.1) (fun e _ => G.weight_pos e.1) hload

/-- In `n` local bins, at most `k n` incident edges can all be heavier than
`1/(k+1)`. -/
theorem degreeOn_le_mul_of_packsStarInto
    (F : Finset G.E) {v : G.V} {n k : ℕ}
    (hpack : G.PacksStarInto v n)
    (hlarge : ∀ e ∈ F, (1 : ℝ) / (k + 1) < G.weight e) :
    G.degreeOn F v ≤ k * n := by
  classical
  rcases hpack with ⟨bin, hbin⟩
  let S : Finset (G.StarEdge v) :=
    Finset.univ.filter fun e => e.1 ∈ F
  have hScard : S.card = G.degreeOn F v := by
    let emb : G.StarEdge v ↪ G.E :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hmap : S.map emb = F.filter (G.Inc v) := by
      ext e
      simp [S, emb]
    rw [degreeOn, ← hmap, Finset.card_map]
  have hfiber (i : Fin n) :
      (S.filter fun e => bin e = i).card ≤ k := by
    by_contra hnot
    have hk1 : k + 1 ≤ (S.filter fun e => bin e = i).card := by omega
    have hsumLower :
        ((S.filter fun e => bin e = i).card : ℝ) *
            ((1 : ℝ) / (k + 1)) <
          ∑ e ∈ S.filter (fun e => bin e = i), G.weight e.1 := by
      calc
        ((S.filter fun e => bin e = i).card : ℝ) *
              ((1 : ℝ) / (k + 1)) =
            ∑ _e ∈ S.filter (fun e => bin e = i),
              ((1 : ℝ) / (k + 1)) := by simp
        _ < _ := Finset.sum_lt_sum_of_nonempty
          (by
            simpa using (show (S.filter fun e => bin e = i).Nonempty from
              Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos k) hk1)))
          (by
            intro e he
            exact (hlarge e.1 (Finset.mem_filter.mp
              (Finset.mem_filter.mp he).1).2))
    have hcast : ((k + 1 : ℕ) : ℝ) ≤
        ((S.filter fun e => bin e = i).card : ℝ) := by
      exact_mod_cast hk1
    have hden : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hone : (1 : ℝ) ≤
        ((S.filter fun e => bin e = i).card : ℝ) *
          ((1 : ℝ) / (k + 1)) := by
      calc
        (1 : ℝ) = ((k + 1 : ℕ) : ℝ) *
            ((1 : ℝ) / (k + 1)) := by
              push_cast
              field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcast (by positivity)
    have hsumUpper :
        (∑ e ∈ S.filter (fun e => bin e = i), G.weight e.1) ≤ 1 := by
      calc
        (∑ e ∈ S.filter (fun e => bin e = i), G.weight e.1) ≤
            ∑ e : G.StarEdge v,
              if bin e = i then G.weight e.1 else 0 := by
          rw [← Finset.sum_filter]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (fun e he => by
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩)
            (fun e _he _hne => G.weight_nonneg e.1)
        _ ≤ 1 := hbin i
    linarith
  calc
    G.degreeOn F v = S.card := hScard.symm
    _ = ∑ e ∈ S, 1 := by simp
    _ = ∑ e ∈ S, ∑ i : Fin n, if bin e = i then 1 else 0 := by simp
    _ = ∑ i : Fin n, ∑ e ∈ S, if bin e = i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, (S.filter fun e => bin e = i).card := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp
    _ ≤ ∑ _i : Fin n, k := Finset.sum_le_sum fun i _ => hfiber i
    _ = k * n := by simp [Nat.mul_comm]

theorem degreeOn_generalUpperRange_le_bp (v : G.V) :
    G.degreeOn G.generalUpperRange v ≤ G.bp := by
  simpa using G.degreeOn_le_mul_of_packsStarInto G.generalUpperRange
    (G.locallyPacksInto_bp v) (k := 1) (by
      intro e he
      norm_num
      exact (Finset.mem_filter.mp he).2.1)

theorem degreeOn_upper_union_lower_le_two_mul_bp (v : G.V) :
    G.degreeOn (G.generalUpperRange ∪ G.generalLowerRange) v ≤ 2 * G.bp := by
  apply G.degreeOn_le_mul_of_packsStarInto
    (G.generalUpperRange ∪ G.generalLowerRange)
    (G.locallyPacksInto_bp v) (k := 2)
  intro e he
  rcases Finset.mem_union.mp he with heA | heB
  · have h := (Finset.mem_filter.mp heA).2.1
    norm_num at h ⊢
    linarith
  · norm_num
    exact (Finset.mem_filter.mp heB).2.1

theorem degreeOn_union_of_disjoint {A B : Finset G.E}
    (h : Disjoint A B) (v : G.V) :
    G.degreeOn (A ∪ B) v = G.degreeOn A v + G.degreeOn B v := by
  classical
  unfold degreeOn
  have hfilter :
      (A ∪ B).filter (G.Inc v) =
        A.filter (G.Inc v) ∪ B.filter (G.Inc v) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  rw [hfilter, Finset.card_union_of_disjoint]
  exact h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- The exact selected palette has the required leading coefficient, with a
uniform additive constant six. -/
theorem generalSelectionPalette_bound :
    ((3 * ((G.generalSelectionK + 1) / 2) : ℕ) : ℝ) ≤
      (3 / 2 : ℝ) * harmonicSelectionFraction * G.bp + 6 := by
  let x : ℝ := harmonicSelectionFraction * (G.bp : ℝ)
  let K : ℕ := G.generalSelectionK
  have hx : 0 ≤ x := by
    exact mul_nonneg harmonicSelectionFraction_nonneg (by positivity)
  have hceil : ((Nat.ceil x : ℕ) : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hx).le
  have hdivNat : 2 * ((K + 1) / 2) ≤ K + 1 := by omega
  have hdiv : (2 : ℝ) * (((K + 1) / 2 : ℕ) : ℝ) ≤ (K + 1 : ℕ) := by
    exact_mod_cast hdivNat
  norm_num only [Nat.cast_add, Nat.cast_one] at hdiv
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  change (3 : ℝ) * (((K + 1) / 2 : ℕ) : ℝ) ≤ _
  have hK : (K : ℝ) ≤ x + 3 := by
    dsimp [K, generalSelectionK]
    push_cast
    linarith
  dsimp [x] at hK ⊢
  nlinarith

/-- The selected sets, their explicit coloring, and the residual charge bound
produced by the finite reduction. -/
structure GeneralBPFiniteCertificate where
  selectedUpper : Finset G.E
  selectedLower : Finset G.E
  residual : Finset G.E
  selectedUpper_subset : selectedUpper ⊆ G.generalUpperRange
  selectedLower_subset : selectedLower ⊆ G.generalLowerRange
  residual_eq : residual = Finset.univ \ (selectedUpper ∪ selectedLower)
  upper_degree : ∀ v, G.degreeOn selectedUpper v ≤ G.generalSelectionK
  total_degree : ∀ v,
    G.degreeOn selectedUpper v + G.degreeOn selectedLower v ≤
      2 * G.generalSelectionK
  color : G.E → Fin (3 * ((G.generalSelectionK + 1) / 2))
  feasible : G.IsFeasibleOn (selectedUpper ∪ selectedLower) color
  residual_charge : ∀ v,
    G.harmonicChargeOn residual v ≤ (8 / 5 : ℝ) * G.bp + 3
  residual_locallyPacksInto :
    (G.edgeRestriction residual).LocallyPacksInto G.bp
  residual_graph_charge : ∀ v,
    (G.edgeRestriction residual).starCharge harmonicCharge v ≤
      (8 / 5 : ℝ) * G.bp + 3

/-- The complete finite selection certificate.  The only subsequent input
needed for the asymptotic theorem is a coloring theorem for a residual whose
harmonic charge is bounded at every vertex. -/
theorem exists_generalBPFiniteCertificate :
    Nonempty G.GeneralBPFiniteCertificate := by
  classical
  let t : ℝ := harmonicSelectionFraction
  let A : Finset G.E := G.generalUpperRange
  let B : Finset G.E := G.generalLowerRange
  let n : ℕ := G.bp
  let K : ℕ := G.generalSelectionK
  obtain ⟨FA, hFA, hbalA⟩ :=
    G.exists_balanced_edge_selection A t
      harmonicSelectionFraction_nonneg harmonicSelectionFraction_le_one
  obtain ⟨FB, hFB, hbalB⟩ :=
    G.exists_balanced_edge_selection B t
      harmonicSelectionFraction_nonneg harmonicSelectionFraction_le_one
  have hAB : Disjoint A B := by
    simpa [A, B] using G.generalUpperRange_disjoint_generalLowerRange
  have hFAFB : Disjoint FA FB := hAB.mono hFA hFB
  let R : Finset G.E := Finset.univ \ (FA ∪ FB)
  have hKpos : 0 < K := by
    dsimp [K, generalSelectionK]
    omega
  have hceil : t * (n : ℝ) ≤ (Nat.ceil (t * (n : ℝ)) : ℕ) := by
    exact Nat.le_ceil _
  have hAdegree : ∀ v, G.degreeOn FA v ≤ K := by
    intro v
    have hbase : G.degreeOn A v ≤ n := by
      simpa [A, n] using G.degreeOn_generalUpperRange_le_bp v
    have hbaseR : (G.degreeOn A v : ℝ) ≤ n := by exact_mod_cast hbase
    have hmul : t * (G.degreeOn A v : ℝ) ≤ t * n :=
      mul_le_mul_of_nonneg_left hbaseR harmonicSelectionFraction_nonneg
    have hup := (hbalA v).2
    have hreal : (G.degreeOn FA v : ℝ) ≤ K := by
      dsimp [K, generalSelectionK]
      push_cast
      linarith
    exact_mod_cast hreal
  have htotalDegree : ∀ v,
      G.degreeOn FA v + G.degreeOn FB v ≤ 2 * K := by
    intro v
    have hbase : G.degreeOn A v + G.degreeOn B v ≤ 2 * n := by
      rw [← G.degreeOn_union_of_disjoint hAB v]
      simpa [A, B, n] using
        G.degreeOn_upper_union_lower_le_two_mul_bp v
    have hbaseR :
        (G.degreeOn A v : ℝ) + G.degreeOn B v ≤ 2 * (n : ℝ) := by
      exact_mod_cast hbase
    have hmul :
        t * (G.degreeOn A v : ℝ) +
            t * (G.degreeOn B v : ℝ) ≤ 2 * (t * n) := by
      nlinarith [harmonicSelectionFraction_nonneg]
    have hupA := (hbalA v).2
    have hupB := (hbalB v).2
    have hreal :
        (G.degreeOn FA v : ℝ) + G.degreeOn FB v ≤ 2 * (K : ℝ) := by
      dsimp [K, generalSelectionK]
      push_cast
      linarith
    exact_mod_cast hreal
  obtain ⟨color, hcolor⟩ :=
    exists_feasibleOn_union_three_half_of_degree FA FB hFAFB K hKpos
      (by
        intro e he
        exact G.generalUpperRange_weight_upper (hFA he))
      (by
        intro e he
        exact G.generalLowerRange_weight_upper (hFB he))
      hAdegree htotalDegree
  have hresidual : ∀ v,
      G.harmonicChargeOn R v ≤ (8 / 5 : ℝ) * G.bp + 3 := by
    intro v
    have hselectedLower :
        t * G.harmonicChargeOn (A ∪ B) v - 3 ≤
          G.harmonicChargeOn (FA ∪ FB) v := by
      have hlowA := (hbalA v).1
      have hlowB := (hbalB v).1
      have hchargeAB :
          G.harmonicChargeOn (A ∪ B) v =
            G.harmonicChargeOn A v + G.harmonicChargeOn B v := by
        unfold harmonicChargeOn
        exact G.chargeOn_union hAB v
      have hchargeF :
          G.harmonicChargeOn (FA ∪ FB) v =
            G.harmonicChargeOn FA v + G.harmonicChargeOn FB v := by
        unfold harmonicChargeOn
        exact G.chargeOn_union hFAFB v
      rw [hchargeAB, hchargeF]
      rw [show G.harmonicChargeOn A v = (G.degreeOn A v : ℝ) by
          simpa [A] using G.harmonicChargeOn_generalUpperRange v,
        show G.harmonicChargeOn B v = (G.degreeOn B v : ℝ) / 2 by
          simpa [B] using G.harmonicChargeOn_generalLowerRange v,
        G.harmonicChargeOn_selectedUpper (by simpa [A] using hFA) v,
        G.harmonicChargeOn_selectedLower (by simpa [B] using hFB) v]
      linarith
    have hRFdisj : Disjoint R (FA ∪ FB) := by
      simp [R, Finset.disjoint_left]
    have hRunion : R ∪ (FA ∪ FB) = (Finset.univ : Finset G.E) := by
      ext e
      simp [R]
    have hpartition := G.chargeOn_union
      (charge := harmonicCharge) hRFdisj v
    rw [hRunion] at hpartition
    change G.harmonicChargeOn Finset.univ v =
      G.harmonicChargeOn R v +
        G.harmonicChargeOn (FA ∪ FB) v at hpartition
    have hid := G.starCharge_discounted_identity t v
    have hdiscount := G.discountedStarCharge_at_selection_le v
    rw [hpartition] at hid
    dsimp [t, A, B] at hid hselectedLower
    nlinarith
  exact ⟨{
    selectedUpper := FA
    selectedLower := FB
    residual := R
    selectedUpper_subset := by simpa [A] using hFA
    selectedLower_subset := by simpa [B] using hFB
    residual_eq := by rfl
    upper_degree := by simpa [K] using hAdegree
    total_degree := by simpa [K] using htotalDegree
    color := by simpa [K] using color
    feasible := by simpa [K] using hcolor
    residual_charge := hresidual
    residual_locallyPacksInto :=
      G.edgeRestriction_locallyPacksInto R G.locallyPacksInto_bp
    residual_graph_charge := by
      intro v
      rw [G.edgeRestriction_starCharge harmonicCharge R v]
      exact hresidual v
  }⟩

end WeightedMultigraph

end WeightedEdgeColoring
