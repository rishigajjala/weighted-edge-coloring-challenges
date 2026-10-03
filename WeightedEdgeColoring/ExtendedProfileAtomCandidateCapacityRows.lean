import WeightedEdgeColoring.ExtendedProfileAtomPackingSelection
import WeightedEdgeColoring.ExtendedProfileCandidateCapacityBounds

/-!
# Candidate capacity rows with one source per vertex and colour

The packed-word formulation treats a complete `Fin n` word as one
categorical state.  For the algorithmic application it is better to expose
the product coordinates: a source is `(v,c)` and its state is one padded
extended-profile atom.  A capacity row only reads its own colour coordinate,
so the packed candidate-row estimates can be reused verbatim.

This file contains the deterministic bridge.  It does not assume any
palette-mixing or rounding theorem.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)

/-- Pack the constant word whose every coordinate has code `a`.  Candidate
capacity rows inspect only one coordinate, so this realizes an atom as a
packed word without adding any information. -/
def repeatedExtendedProfileAtomWord
    (a : Fin (extendedProfileStateBound β q r)) :
    ExtendedProfilePackedWordState n β q r :=
  Fintype.equivFin
      (FiniteDependentWordPadding.WordState
        (Color := Fin n) (extendedProfileStateBound β q r))
    (fun _c ↦ a)

@[simp] theorem decode_repeatedExtendedProfileAtomWord
    (v : G.V) (a : Fin (extendedProfileStateBound β q r))
    (c : Fin n) :
    G.decodeExtendedProfileWord R0 v
        (repeatedExtendedProfileAtomWord (n := n) a) c =
      G.decodeExtendedProfileState R0 v a := by
  simp [repeatedExtendedProfileAtomWord, decodeExtendedProfileWord,
    decodeExtendedProfileState, FiniteDependentWordPadding.decodePackedWord]

/-- The colour coordinate inspected by a candidate capacity row. -/
def extendedProfileCandidateCapacityRowColor
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) : Fin n :=
  match row with
  | Sum.inl large => large.color
  | Sum.inr tiny => tiny.color

/-- Candidate capacity use with source type `V × Fin n`.  A source can
contribute only to rows of its own colour. -/
def atomExtendedProfileCandidateCapacityUse
    (rho omega : ℝ) (source : G.V × Fin n)
    (sourceCode : Fin (extendedProfileStateBound β q r))
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  if source.2 = G.extendedProfileCandidateCapacityRowColor R0 row then
    G.packedExtendedProfileCandidateCapacityUse R0 rho omega source.1
      (repeatedExtendedProfileAtomWord (n := n) sourceCode) row
  else 0

/-- The normalized atom-source coefficient. -/
def scaledAtomExtendedProfileCandidateCapacityUse
    (rho omega scale : ℝ) (source : G.V × Fin n)
    (sourceCode : Fin (extendedProfileStateBound β q r))
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  if source.2 = G.extendedProfileCandidateCapacityRowColor R0 row then
    G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega scale
      source.1 (repeatedExtendedProfileAtomWord (n := n) sourceCode) row
  else 0

theorem scaledAtomExtendedProfileCandidateCapacityUse_nonneg
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hscale : 0 ≤ scale)
    (source : G.V × Fin n)
    (sourceCode : Fin (extendedProfileStateBound β q r))
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    0 ≤ G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega scale
      source sourceCode row := by
  unfold scaledAtomExtendedProfileCandidateCapacityUse
  split
  · exact G.scaledPackedExtendedProfileCandidateCapacityUse_nonneg R0
      hn hs hq hr0 hleft homega0 homega1 hrho hscale _ _ _
  · exact le_rfl

theorem scaledAtomExtendedProfileCandidateCapacityUse_le_one
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (source : G.V × Fin n)
    (sourceCode : Fin (extendedProfileStateBound β q r))
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega
        (extendedProfileCandidateCapacityScale rho s omega β q r)
        source sourceCode row ≤ 1 := by
  unfold scaledAtomExtendedProfileCandidateCapacityUse
  split
  · exact G.scaledPackedExtendedProfileCandidateCapacityUse_le_one R0
      hn hs hq hr0 hleft homega0 homega1 hrho hspos _ _ _
  · norm_num

theorem scaledAtomCandidateCapacityUse_eq_div
    (rho omega scale : ℝ) (source : G.V × Fin n)
    (sourceCode : Fin (extendedProfileStateBound β q r))
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega scale
        source sourceCode row =
      G.atomExtendedProfileCandidateCapacityUse R0 rho omega
        source sourceCode row / scale := by
  by_cases hcolor : source.2 =
      G.extendedProfileCandidateCapacityRowColor R0 row
  · simp [scaledAtomExtendedProfileCandidateCapacityUse,
      atomExtendedProfileCandidateCapacityUse, hcolor,
      scaledPackedExtendedProfileCandidateCapacityUse]
  · simp [scaledAtomExtendedProfileCandidateCapacityUse,
      atomExtendedProfileCandidateCapacityUse, hcolor]

/-- The packed choice used to evaluate one fixed row after atom selection.
Every coordinate may be repeated because that row reads only its own
colour. -/
def repeatedSelectedAtomChoice
    (selected : G.ExtendedSelectedProfileWord R0)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r))
    (v : G.V) : ExtendedProfilePackedWordState n β q r :=
  repeatedExtendedProfileAtomWord (n := n)
    (G.extendedProfileStateCode R0 v
      (selected v (G.extendedProfileCandidateCapacityRowColor R0 row)))

/-- Insert the selected center atom in a candidate row.  This is phrased
through the already verified packed-row constructor so the transpose theorem
below can reuse it directly. -/
def selectedAtomCandidateCapacityRow
    (selected : G.ExtendedSelectedProfileWord R0)
    (row : G.ExtendedProfileCapacityRow
      (n := n) (β := β) (q := q) (r := r)) :
    G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r) :=
  let candidateRow : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r) :=
    match row with
    | Sum.inl large => Sum.inl {
        center := large.1
        color := large.2.1
        candidate := selected large.1 large.2.1
        slot := large.2.2 }
    | Sum.inr tiny => Sum.inr {
        center := tiny.1
        color := tiny.2
        candidate := selected tiny.1 tiny.2 }
  candidateRow

/-- The original two-endpoint capacity load evaluated at selected atom
states. -/
def selectedAtomCapacityLoad
    (rho omega : ℝ) (selected : G.ExtendedSelectedProfileWord R0)
    (row : G.ExtendedProfileCapacityRow
      (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  G.packedExtendedProfileCapacityLoad R0 rho omega
    (fun v ↦ repeatedExtendedProfileAtomWord (n := n)
      (G.extendedProfileStateCode R0 v (selected v
        (match row with
        | Sum.inl large => large.2.1
        | Sum.inr tiny => tiny.2)))) row

/-- The additive atom-source load at the selected candidate row is exactly
the original two-endpoint capacity load. -/
theorem rowLoad_atomCandidate_selected_eq_capacityLoad
    (rho omega : ℝ) (selected : G.ExtendedSelectedProfileWord R0)
    (row : G.ExtendedProfileCapacityRow
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowLoad
        (G.atomExtendedProfileCandidateCapacityUse R0 rho omega)
        (G.selectedAtomCandidateCapacityRow R0 selected row)
        (fun source ↦ G.extendedProfileStateCode R0 source.1
          (selected source.1 source.2)) =
      G.selectedAtomCapacityLoad R0 rho omega selected row := by
  classical
  rcases row with large | tiny
  · let candidate := G.selectedAtomCandidateCapacityRow R0 selected
        (Sum.inl large)
    let choice : G.V → ExtendedProfilePackedWordState n β q r :=
      fun v ↦ repeatedExtendedProfileAtomWord (n := n)
        (G.extendedProfileStateCode R0 v (selected v large.2.1))
    have hcandidate : candidate =
        Sum.inl (G.selectedLargeCandidateRow R0 choice large) := by
      simp [candidate, choice, selectedAtomCandidateCapacityRow,
        selectedLargeCandidateRow]
    calc
      FiniteCategoricalSelection.rowLoad
          (G.atomExtendedProfileCandidateCapacityUse R0 rho omega)
          candidate
          (fun source ↦ G.extendedProfileStateCode R0 source.1
            (selected source.1 source.2)) =
          FiniteCategoricalSelection.rowLoad
            (G.packedExtendedProfileCandidateCapacityUse R0 rho omega)
            candidate choice := by
        rw [hcandidate]
        unfold FiniteCategoricalSelection.rowLoad
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro v _hv
        rw [Finset.sum_eq_single large.2.1]
        · simp [atomExtendedProfileCandidateCapacityUse,
            extendedProfileCandidateCapacityRowColor, choice,
            selectedLargeCandidateRow]
        · intro c _hc hne
          simp [atomExtendedProfileCandidateCapacityUse,
            extendedProfileCandidateCapacityRowColor,
            selectedLargeCandidateRow, hne]
        · simp
      _ = G.packedExtendedProfileCapacityLoad R0 rho omega choice
          (Sum.inl large) := by
        rw [hcandidate]
        exact G.rowLoad_candidate_selected_eq_capacityLoad
          R0 rho omega choice (Sum.inl large)
      _ = G.selectedAtomCapacityLoad R0 rho omega selected
          (Sum.inl large) := rfl
  · let candidate := G.selectedAtomCandidateCapacityRow R0 selected
        (Sum.inr tiny)
    let choice : G.V → ExtendedProfilePackedWordState n β q r :=
      fun v ↦ repeatedExtendedProfileAtomWord (n := n)
        (G.extendedProfileStateCode R0 v (selected v tiny.2))
    have hcandidate : candidate =
        Sum.inr (G.selectedTinyCandidateRow R0 choice tiny) := by
      simp [candidate, choice, selectedAtomCandidateCapacityRow,
        selectedTinyCandidateRow]
    calc
      FiniteCategoricalSelection.rowLoad
          (G.atomExtendedProfileCandidateCapacityUse R0 rho omega)
          candidate
          (fun source ↦ G.extendedProfileStateCode R0 source.1
            (selected source.1 source.2)) =
          FiniteCategoricalSelection.rowLoad
            (G.packedExtendedProfileCandidateCapacityUse R0 rho omega)
            candidate choice := by
        rw [hcandidate]
        unfold FiniteCategoricalSelection.rowLoad
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro v _hv
        rw [Finset.sum_eq_single tiny.2]
        · simp [atomExtendedProfileCandidateCapacityUse,
            extendedProfileCandidateCapacityRowColor, choice,
            selectedTinyCandidateRow]
        · intro c _hc hne
          simp [atomExtendedProfileCandidateCapacityUse,
            extendedProfileCandidateCapacityRowColor,
            selectedTinyCandidateRow, hne]
        · simp
      _ = G.packedExtendedProfileCapacityLoad R0 rho omega choice
          (Sum.inr tiny) := by
        rw [hcandidate]
        exact G.rowLoad_candidate_selected_eq_capacityLoad
          R0 rho omega choice (Sum.inr tiny)
      _ = G.selectedAtomCapacityLoad R0 rho omega selected
          (Sum.inr tiny) := rfl

theorem rowLoad_scaledAtomCandidate_selected_eq_capacityLoad_div
    (rho omega scale : ℝ)
    (selected : G.ExtendedSelectedProfileWord R0)
    (row : G.ExtendedProfileCapacityRow
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowLoad
        (G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega scale)
        (G.selectedAtomCandidateCapacityRow R0 selected row)
        (fun source ↦ G.extendedProfileStateCode R0 source.1
          (selected source.1 source.2)) =
      G.selectedAtomCapacityLoad R0 rho omega selected row / scale := by
  classical
  have hraw := G.rowLoad_atomCandidate_selected_eq_capacityLoad
    R0 rho omega selected row
  unfold FiniteCategoricalSelection.rowLoad at hraw ⊢
  simp_rw [G.scaledAtomCandidateCapacityUse_eq_div R0]
  rw [← Finset.sum_div]
  exact congrArg (fun x : ℝ ↦ x / scale) hraw

/-- Atom columns are subcolumns of the corresponding repeated packed-word
column.  Hence the already proved polynomial packed column bound applies. -/
theorem sum_scaledAtomCandidateCapacityUse_le_column
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (hpack : G.LocallyPacksInto n)
    (source : G.V × Fin n)
    (sourceCode : Fin (extendedProfileStateBound β q r)) :
    (∑ row : G.ExtendedProfileCandidateCapacityRow R0
        (n := n) (β := β) (q := q) (r := r),
      G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega
        (extendedProfileCandidateCapacityScale rho s omega β q r)
        source sourceCode row) ≤
      extendedProfileCandidateCapacityColumnBound n β q r := by
  have hpoint : ∀ row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r),
      G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega
          (extendedProfileCandidateCapacityScale rho s omega β q r)
          source sourceCode row ≤
        G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega
          (extendedProfileCandidateCapacityScale rho s omega β q r)
          source.1 (repeatedExtendedProfileAtomWord (n := n) sourceCode) row := by
    intro row
    unfold scaledAtomExtendedProfileCandidateCapacityUse
    split
    · exact le_rfl
    · exact G.scaledPackedExtendedProfileCandidateCapacityUse_nonneg R0
        hn hs hq hr0 hleft homega0 homega1 hrho.le
        (extendedProfileCandidateCapacityScale_nonneg
          (omega := omega) (β := β) (q := q) (r := r) hrho.le hs)
        _ _ _
  calc
    (∑ row : G.ExtendedProfileCandidateCapacityRow R0
        (n := n) (β := β) (q := q) (r := r),
      G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega
        (extendedProfileCandidateCapacityScale rho s omega β q r)
        source sourceCode row) ≤
        ∑ row,
          G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega
            (extendedProfileCandidateCapacityScale rho s omega β q r)
            source.1
            (repeatedExtendedProfileAtomWord (n := n) sourceCode) row := by
      exact Finset.sum_le_sum fun row _hrow ↦ hpoint row
    _ ≤ extendedProfileCandidateCapacityColumnBound n β q r :=
      G.sum_scaledCandidateCapacityUse_le_column R0 hn hs hq hr0 hleft
        homega0 homega1 hrho hspos hpack source.1
        (repeatedExtendedProfileAtomWord (n := n) sourceCode)

/-! ## Atom and packed-word means agree -/

/-- Integrating a function of a padded atom is the same as summing it over
the genuine source-dependent states. -/
theorem sum_paddedExtendedProfileStateProbability_mul
    (omega : ℝ) (v : G.V)
    (f : Fin (extendedProfileStateBound β q r) → ℝ) :
    (∑ a, G.paddedExtendedProfileStateProbability R0 omega v a * f a) =
      ∑ z : G.ExtendedProfileState R0 v,
        G.smoothedExtendedProfileProbability R0 omega v z *
          f (G.extendedProfileStateCode R0 v z) := by
  classical
  unfold paddedExtendedProfileStateProbability
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _hz
  simp

/-- A packed candidate-capacity coefficient reads only the colour stored in
its row.  Replacing the packed word by the repeated code of that decoded
coordinate leaves the coefficient unchanged. -/
theorem packedCandidateCapacityUse_eq_repeated_decoded
    (rho omega : ℝ) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    G.packedExtendedProfileCandidateCapacityUse R0 rho omega
        source sourceCode row =
      G.packedExtendedProfileCandidateCapacityUse R0 rho omega source
        (repeatedExtendedProfileAtomWord (n := n)
          (G.extendedProfileStateCode R0 source
            (G.decodeExtendedProfileWord R0 source sourceCode
              (G.extendedProfileCandidateCapacityRowColor R0 row)))) row := by
  classical
  rcases row with large | tiny
  · unfold packedExtendedProfileCandidateCapacityUse
      packedExtendedProfileLargeCandidateUse
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hfst : large.center = G.fst e ∧ source = G.snd e
    · have hsource := hfst.2
      subst source
      simp [packedExtendedProfileLargeCandidateEdgeUse,
        extendedProfileCandidateCapacityRowColor, hfst.1]
    · by_cases hsnd : large.center = G.snd e ∧ source = G.fst e
      · have hsource := hsnd.2
        subst source
        have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
        simp [packedExtendedProfileLargeCandidateEdgeUse,
          extendedProfileCandidateCapacityRowColor, hfst, hsnd.1, hne]
      · simp [packedExtendedProfileLargeCandidateEdgeUse,
          extendedProfileCandidateCapacityRowColor, hfst, hsnd]
  · unfold packedExtendedProfileCandidateCapacityUse
      packedExtendedProfileTinyCandidateUse
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hfst : tiny.center = G.fst e ∧ source = G.snd e
    · have hsource := hfst.2
      subst source
      simp [packedExtendedProfileTinyCandidateEdgeUse,
        extendedProfileCandidateCapacityRowColor, hfst.1]
    · by_cases hsnd : tiny.center = G.snd e ∧ source = G.fst e
      · have hsource := hsnd.2
        subst source
        have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
        simp [packedExtendedProfileTinyCandidateEdgeUse,
          extendedProfileCandidateCapacityRowColor, hfst, hsnd.1, hne]
      · simp [packedExtendedProfileTinyCandidateEdgeUse,
          extendedProfileCandidateCapacityRowColor, hfst, hsnd]

/- A candidate-capacity statistic has the same expectation under one
padded atom and under a padded independent word. -/
set_option maxHeartbeats 800000 in
theorem sum_paddedAtom_mul_candidateCapacityUse_eq_packedWord
    (omega rho : ℝ) (source : G.V)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    (∑ a : Fin (extendedProfileStateBound β q r),
      G.paddedExtendedProfileStateProbability R0 omega source a *
        G.packedExtendedProfileCandidateCapacityUse R0 rho omega source
          (repeatedExtendedProfileAtomWord (n := n) a) row) =
      ∑ word : ExtendedProfilePackedWordState n β q r,
        G.paddedExtendedProfileWordProbability R0 omega source word *
          G.packedExtendedProfileCandidateCapacityUse R0 rho omega
            source word row := by
  classical
  let c := G.extendedProfileCandidateCapacityRowColor R0 row
  let f : G.ExtendedProfileState R0 source → ℝ := fun z ↦
    G.packedExtendedProfileCandidateCapacityUse R0 rho omega source
      (repeatedExtendedProfileAtomWord (n := n)
        (G.extendedProfileStateCode R0 source z)) row
  have hatom := G.sum_paddedExtendedProfileStateProbability_mul
    R0 omega source
      (fun a ↦ G.packedExtendedProfileCandidateCapacityUse R0 rho omega
        source (repeatedExtendedProfileAtomWord (n := n) a) row)
  have hword :=
    FiniteDependentWordPadding.sum_paddedWordProbability_mul_decode_coordinate
      (fun v ↦ G.ExtendedProfileState R0 v)
      (G.extendedProfileStateEncoding R0)
      (G.inactiveExtendedProfileState R0)
      (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
      (G.sum_smoothedExtendedProfileProbability R0 omega)
      source c f
  calc
    (∑ a : Fin (extendedProfileStateBound β q r),
      G.paddedExtendedProfileStateProbability R0 omega source a *
        G.packedExtendedProfileCandidateCapacityUse R0 rho omega source
          (repeatedExtendedProfileAtomWord (n := n) a) row) =
        ∑ z : G.ExtendedProfileState R0 source,
          G.smoothedExtendedProfileProbability R0 omega source z * f z := by
      simpa only [f] using hatom
    _ = ∑ word : ExtendedProfilePackedWordState n β q r,
        G.paddedExtendedProfileWordProbability R0 omega source word *
          f (G.decodeExtendedProfileWord R0 source word c) := by
      exact hword.symm
    _ = ∑ word : ExtendedProfilePackedWordState n β q r,
        G.paddedExtendedProfileWordProbability R0 omega source word *
          G.packedExtendedProfileCandidateCapacityUse R0 rho omega
            source word row := by
      apply Finset.sum_congr rfl
      intro word _hword
      congr 1
      symm
      simpa only [f, c] using
        G.packedCandidateCapacityUse_eq_repeated_decoded R0 rho omega
          source word row

/-- Consequently the atom-source row mean is exactly the already analysed
packed-word row mean. -/
theorem rowMean_atomCandidateCapacityUse_eq_packedWord
    (omega rho : ℝ)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileStateProbability R0 omega source.1 a)
        (G.atomExtendedProfileCandidateCapacityUse R0 rho omega) row =
      FiniteCategoricalSelection.rowMean
        (G.paddedExtendedProfileWordProbability R0 omega)
        (G.packedExtendedProfileCandidateCapacityUse R0 rho omega) row := by
  classical
  unfold FiniteCategoricalSelection.rowMean
  rw [Fintype.sum_prod_type]
  calc
    (∑ v : G.V, ∑ c : Fin n,
      ∑ a : Fin (extendedProfileStateBound β q r),
        G.paddedExtendedProfileStateProbability R0 omega v a *
          G.atomExtendedProfileCandidateCapacityUse R0 rho omega
            (v, c) a row) =
        ∑ v : G.V,
          ∑ a : Fin (extendedProfileStateBound β q r),
            G.paddedExtendedProfileStateProbability R0 omega v a *
              G.packedExtendedProfileCandidateCapacityUse R0 rho omega v
                (repeatedExtendedProfileAtomWord (n := n) a) row := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.sum_eq_single
        (G.extendedProfileCandidateCapacityRowColor R0 row)]
      · simp [atomExtendedProfileCandidateCapacityUse]
      · intro c _hc hne
        simp [atomExtendedProfileCandidateCapacityUse, hne]
      · simp
    _ = ∑ v : G.V,
        ∑ word : ExtendedProfilePackedWordState n β q r,
          G.paddedExtendedProfileWordProbability R0 omega v word *
            G.packedExtendedProfileCandidateCapacityUse R0 rho omega
              v word row := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact G.sum_paddedAtom_mul_candidateCapacityUse_eq_packedWord
        R0 omega rho v row

/-- The normalized atom and packed row means also agree. -/
theorem rowMean_scaledAtomCandidateCapacityUse_eq_packedWord
    (omega rho scale : ℝ)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileStateProbability R0 omega source.1 a)
        (G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega scale)
        row =
      FiniteCategoricalSelection.rowMean
        (G.paddedExtendedProfileWordProbability R0 omega)
        (G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega scale)
        row := by
  classical
  have hraw := G.rowMean_atomCandidateCapacityUse_eq_packedWord
    R0 omega rho row
  unfold FiniteCategoricalSelection.rowMean at hraw ⊢
  simp_rw [G.scaledAtomCandidateCapacityUse_eq_div R0]
  unfold scaledPackedExtendedProfileCandidateCapacityUse
  simp_rw [mul_div_assoc']
  simpa only [Finset.sum_div] using
    congrArg (fun x : ℝ ↦ x / scale) hraw

/-! ## Concrete atom-source capacity selection -/

/-- The supported finite-PRA selector simultaneously controls all
large-slot and tiny-reservoir capacity rows while selecting one genuine
extended-profile state for every `(vertex, colour)` source. -/
theorem exists_extendedProfileAtom_capacityLoad_lt_packing
    (omega : ℝ)
    (hn : 0 < n) (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto n) :
    ∃ selected : G.ExtendedSelectedProfileWord R0,
      (∀ v c,
        0 < G.smoothedExtendedProfileProbability R0 omega v
          (selected v c)) ∧
      ∀ row : G.ExtendedProfileCapacityRow
          (n := n) (β := β) (q := q) (r := r),
        G.selectedAtomCapacityLoad R0 rho omega selected row /
            extendedProfileCandidateCapacityScale rho s omega β q r <
          ((n : ℝ) * rho) /
              (extendedProfileCandidateCapacityScale rho s omega β q r *
                extendedProfileSmoothingKappa omega β q r) +
            FinitePartialResamplingNumerics.packingDeviation
              (((n : ℝ) * rho) /
                (extendedProfileCandidateCapacityScale rho s omega β q r *
                  extendedProfileSmoothingKappa omega β q r))
              (extendedProfileCandidateCapacityColumnBound n β q r) := by
  let scale := extendedProfileCandidateCapacityScale rho s omega β q r
  let meanBound := ((n : ℝ) * rho) /
    (scale * extendedProfileSmoothingKappa omega β q r)
  let columnBound := extendedProfileCandidateCapacityColumnBound n β q r
  have hscale : 0 < scale := by
    exact extendedProfileCandidateCapacityScale_pos
      (β := β) (q := q) (r := r) hrho hspos homega0
  have hkappa : 0 < extendedProfileSmoothingKappa omega β q r :=
    extendedProfileSmoothingKappa_pos
      (β := β) (q := q) (r := r) homega0 homega1
  have hmeanBound : 0 < meanBound := by
    dsimp [meanBound]
    positivity
  have hcolumnBound : 0 ≤ columnBound := by
    dsimp [columnBound, extendedProfileCandidateCapacityColumnBound]
    positivity
  obtain ⟨selected, hselected, hrows⟩ :=
    G.exists_extendedProfileAtom_rowLoad_lt_packing R0 omega
      hs hq hr0 hleft homega0 homega1
      (G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega scale)
      meanBound columnBound hmeanBound hcolumnBound
      (fun source a row ↦
        G.scaledAtomExtendedProfileCandidateCapacityUse_nonneg R0
          hn hs hq hr0 hleft homega0 homega1 hrho.le hscale.le
          source a row)
      (fun source a row ↦ by
        simpa [scale] using
          G.scaledAtomExtendedProfileCandidateCapacityUse_le_one R0
            hn hs hq hr0 hleft homega0 homega1 hrho hspos
            source a row)
      (fun row ↦ by
        rw [G.rowMean_scaledAtomCandidateCapacityUse_eq_packedWord
          R0 omega rho scale row]
        simpa [meanBound, scale] using
          G.rowMean_scaledCandidateCapacityUse_le R0 hn hs hq hr0 hleft
            homega0 homega1 hrho hspos row)
      (fun source a ↦ by
        simpa [columnBound, scale] using
          G.sum_scaledAtomCandidateCapacityUse_le_column R0
            hn hs hq hr0 hleft homega0 homega1 hrho hspos hpack source a)
  refine ⟨selected, hselected, ?_⟩
  intro row
  have hrow := hrows (G.selectedAtomCandidateCapacityRow R0 selected row)
  have hload :
      FiniteCategoricalSelection.rowLoad
          (G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega scale)
          (G.selectedAtomCandidateCapacityRow R0 selected row)
          (fun source ↦ G.extendedProfileStateCode R0 source.1
            (selected source.1 source.2)) <
        meanBound +
          FinitePartialResamplingNumerics.packingDeviation
            meanBound columnBound := by
    simpa only [FiniteCategoricalSelection.rowLoad] using hrow
  rw [G.rowLoad_scaledAtomCandidate_selected_eq_capacityLoad_div
    R0 rho omega scale selected row] at hload
  simpa [meanBound, columnBound, scale] using hload

end WeightedSimpleGraph

end

end WeightedEdgeColoring
