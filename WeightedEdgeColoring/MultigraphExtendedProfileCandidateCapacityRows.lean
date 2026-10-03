import WeightedEdgeColoring.MultigraphExtendedProfileWordCapacityRows
import WeightedEdgeColoring.BoundedMultiplicityPairCodegree

/-!
# Candidate-state capacity rows

The equation-(23) coefficient of an edge depends on the states chosen at
both endpoints.  For a simple graph this dependence can be made additive
without a vertex partition.  A row centered at `v` records, in addition to
its color and capacity slot, a candidate one-color state at `v`.  The source
of that row is the opposite endpoint of an edge incident with `v`; its state
is read from the chosen packed word.  Thus a source and a row meet on at most
one edge.

After all packed words have been selected, substitute the selected state at
`v` for the candidate recorded by the row.  The transpose identities below
say that the resulting additive source load is exactly the original
two-endpoint capacity load.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)

/-- Decode one common extended-state code at a specified vertex.  Codes not
used at that vertex decode to the inactive state. -/
def decodeExtendedProfileState (v : G.V)
    (a : Fin (extendedProfileStateBound β q r)) :
    G.ExtendedProfileState R0 v :=
  FiniteDependentWordPadding.decodeAtom
    (fun x ↦ G.ExtendedProfileState R0 x)
    (G.extendedProfileStateEncoding R0)
    (G.inactiveExtendedProfileState R0) v a

@[simp] theorem decodeExtendedProfileState_code (v : G.V)
    (z : G.ExtendedProfileState R0 v) :
    G.decodeExtendedProfileState R0 v
        (G.extendedProfileStateCode R0 v z) = z := by
  exact FiniteDependentWordPadding.decodeAtom_code
    (fun x ↦ G.ExtendedProfileState R0 x)
    (G.extendedProfileStateEncoding R0)
    (G.inactiveExtendedProfileState R0) v z

/-- A large capacity row with a candidate state at its center. -/
structure ExtendedProfileLargeCandidateRow where
  center : G.V
  color : Fin n
  candidate : G.ExtendedProfileState R0 center
  slot : Fin (explicitLargeSlotBound β q r)

/-- A tiny-reservoir row with a candidate state at its center. -/
structure ExtendedProfileTinyCandidateRow where
  center : G.V
  color : Fin n
  candidate : G.ExtendedProfileState R0 center

/-- A candidate large row is a finite dependent tuple.  We spell out this
equivalence because Lean's structure deriving mechanism does not handle the
dependent `candidate` field. -/
def extendedProfileLargeCandidateRowEquiv :
    G.ExtendedProfileLargeCandidateRow R0
        (n := n) (β := β) (q := q) (r := r) ≃
      Σ v : G.V, Fin n × G.ExtendedProfileState R0 v ×
        Fin (explicitLargeSlotBound β q r) where
  toFun row := ⟨row.center, row.color, row.candidate, row.slot⟩
  invFun row := ⟨row.1, row.2.1, row.2.2.1, row.2.2.2⟩
  left_inv row := by cases row; rfl
  right_inv row := by rcases row with ⟨v, color, candidate, slot⟩; rfl

/-- A candidate tiny row is a finite dependent tuple. -/
def extendedProfileTinyCandidateRowEquiv :
    G.ExtendedProfileTinyCandidateRow R0
        (n := n) (β := β) (q := q) (r := r) ≃
      Σ v : G.V, Fin n × G.ExtendedProfileState R0 v where
  toFun row := ⟨row.center, row.color, row.candidate⟩
  invFun row := ⟨row.1, row.2.1, row.2.2⟩
  left_inv row := by cases row; rfl
  right_inv row := by rcases row with ⟨v, color, candidate⟩; rfl

noncomputable instance : Fintype
    (G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :=
  Fintype.ofEquiv
    (Σ v : G.V, Fin n × G.ExtendedProfileState R0 v ×
      Fin (explicitLargeSlotBound β q r))
    (G.extendedProfileLargeCandidateRowEquiv R0).symm

noncomputable instance : DecidableEq
    (G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :=
  Classical.decEq _

noncomputable instance : Fintype
    (G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :=
  Fintype.ofEquiv
    (Σ v : G.V, Fin n × G.ExtendedProfileState R0 v)
    (G.extendedProfileTinyCandidateRowEquiv R0).symm

noncomputable instance : DecidableEq
    (G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :=
  Classical.decEq _

/-- All candidate-state capacity rows. -/
abbrev ExtendedProfileCandidateCapacityRow :=
  G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r) ⊕
    G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)

/-- Contribution of one edge to a candidate large row, viewed as a function
of the packed word at the row's opposite endpoint `source`. -/
def packedExtendedProfileLargeCandidateEdgeUse
    (rho omega : ℝ) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r) (e : G.E)
    (row : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  if h : row.center = G.fst e ∧ source = G.snd e then
    n * ∑ j, G.extendedProfileProductOptionMass R0 rho omega e
      (h.1 ▸ row.candidate)
      (G.decodeExtendedProfileWord R0 (G.snd e) sourceCode row.color)
      row.slot j
  else if h : row.center = G.snd e ∧ source = G.fst e then
    n * ∑ i, G.extendedProfileProductOptionMass R0 rho omega e
      (G.decodeExtendedProfileWord R0 (G.fst e) sourceCode row.color)
      (h.1 ▸ row.candidate)
      i row.slot
  else 0

/-- Contribution of one edge to a candidate tiny row. -/
def packedExtendedProfileTinyCandidateEdgeUse
    (rho omega : ℝ) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r) (e : G.E)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  if h : row.center = G.fst e ∧ source = G.snd e then
    n * G.weight e * G.extendedProfileTinyProductOptionMass R0 rho omega e
      (h.1 ▸ row.candidate)
      (G.decodeExtendedProfileWord R0 (G.snd e) sourceCode row.color)
  else if h : row.center = G.snd e ∧ source = G.fst e then
    n * G.weight e * G.extendedProfileTinyProductOptionMass R0 rho omega e
      (G.decodeExtendedProfileWord R0 (G.fst e) sourceCode row.color)
      (h.1 ▸ row.candidate)
  else 0

/-- Additive large-row use of one vertex word. -/
def packedExtendedProfileLargeCandidateUse
    (rho omega : ℝ) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  ∑ e, G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
    source sourceCode e row

/-- Additive tiny-row use of one vertex word. -/
def packedExtendedProfileTinyCandidateUse
    (rho omega : ℝ) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  ∑ e, G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
    source sourceCode e row

/-- Combined additive candidate-row use. -/
def packedExtendedProfileCandidateCapacityUse
    (rho omega : ℝ) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  match row with
  | Sum.inl large =>
      G.packedExtendedProfileLargeCandidateUse R0 rho omega
        source sourceCode large
  | Sum.inr tiny =>
      G.packedExtendedProfileTinyCandidateUse R0 rho omega
        source sourceCode tiny

/-- Scale candidate uses so that the categorical selector sees entries in
`[0,1]`. -/
def scaledPackedExtendedProfileCandidateCapacityUse
    (rho omega scale : ℝ) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) : ℝ :=
  G.packedExtendedProfileCandidateCapacityUse R0 rho omega
    source sourceCode row / scale

/-- Parameter-only normalization for one source/candidate-row entry.  Here
`M` is the common number of one-color extended-state codes. -/
def extendedProfileCandidateCapacityScale (rho s omega β q r : ℝ) : ℝ :=
  rho * s *
    ((extendedProfileStateBound β q r : ℝ) / omega) ^ 2

theorem extendedProfileCandidateCapacityScale_pos
    (hrho : 0 < rho) (hs : 0 < s) (homega : 0 < omega) :
    0 < extendedProfileCandidateCapacityScale rho s omega β q r := by
  unfold extendedProfileCandidateCapacityScale extendedProfileStateBound
  positivity

theorem extendedProfileCandidateCapacityScale_nonneg
    (hrho : 0 ≤ rho) (hs : 0 ≤ s) :
    0 ≤ extendedProfileCandidateCapacityScale rho s omega β q r := by
  unfold extendedProfileCandidateCapacityScale
  positivity

/-- The candidate large row obtained by inserting the actually selected
state at the row center. -/
def selectedLargeCandidateRow
    (choice : G.V → ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileLargeRow
      (n := n) (β := β) (q := q) (r := r)) :
    G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r) where
  center := row.1
  color := row.2.1
  candidate := G.decodeExtendedProfileWord R0 row.1 (choice row.1) row.2.1
  slot := row.2.2

/-- The candidate tiny row obtained by inserting the actually selected
state at the row center. -/
def selectedTinyCandidateRow
    (choice : G.V → ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileTinyRow (n := n)) :
    G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r) where
  center := row.1
  color := row.2
  candidate := G.decodeExtendedProfileWord R0 row.1 (choice row.1) row.2

/-! ## Transpose identities -/

/-- Summing opposite-endpoint source uses after substituting the selected
center state gives exactly the original large-row load. -/
theorem sum_largeCandidateUse_selected_eq_largeRowUse
    (rho omega : ℝ)
    (choice : G.V → ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileLargeRow
      (n := n) (β := β) (q := q) (r := r)) :
    (∑ source, G.packedExtendedProfileLargeCandidateUse R0 rho omega
      source (choice source) (G.selectedLargeCandidateRow R0 choice row)) =
      ∑ e, G.packedExtendedProfileLargeRowUse R0 rho omega e
        (choice (G.fst e)) (choice (G.snd e)) row := by
  classical
  rcases row with ⟨v, color, slot⟩
  unfold packedExtendedProfileLargeCandidateUse
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hfst : v = G.fst e
  · subst v
    have hne : G.fst e ≠ G.snd e := G.noLoop e
    simp [packedExtendedProfileLargeCandidateEdgeUse,
      packedExtendedProfileLargeRowUse, packedExtendedProfileLargeMass,
      selectedLargeCandidateRow,
      hne]
  · by_cases hsnd : v = G.snd e
    · subst v
      have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
      simp [packedExtendedProfileLargeCandidateEdgeUse,
        packedExtendedProfileLargeRowUse, packedExtendedProfileLargeMass,
        selectedLargeCandidateRow,
        hne]
    · simp [packedExtendedProfileLargeCandidateEdgeUse,
        packedExtendedProfileLargeRowUse, packedExtendedProfileLargeMass,
        selectedLargeCandidateRow,
        hfst, hsnd]

/-- Tiny analogue of `sum_largeCandidateUse_selected_eq_largeRowUse`. -/
theorem sum_tinyCandidateUse_selected_eq_tinyRowUse
    (rho omega : ℝ)
    (choice : G.V → ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileTinyRow (n := n)) :
    (∑ source, G.packedExtendedProfileTinyCandidateUse R0 rho omega
      source (choice source) (G.selectedTinyCandidateRow R0 choice row)) =
      ∑ e, G.packedExtendedProfileTinyRowUse R0 rho omega e
        (choice (G.fst e)) (choice (G.snd e)) row := by
  classical
  rcases row with ⟨v, color⟩
  unfold packedExtendedProfileTinyCandidateUse
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hfst : v = G.fst e
  · subst v
    have hne : G.fst e ≠ G.snd e := G.noLoop e
    simp [packedExtendedProfileTinyCandidateEdgeUse,
      packedExtendedProfileTinyRowUse, packedExtendedProfileTinyMass,
      selectedTinyCandidateRow,
      hne]
  · by_cases hsnd : v = G.snd e
    · subst v
      have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
      simp [packedExtendedProfileTinyCandidateEdgeUse,
        packedExtendedProfileTinyRowUse, packedExtendedProfileTinyMass,
        selectedTinyCandidateRow,
        hne]
    · simp [packedExtendedProfileTinyCandidateEdgeUse,
        packedExtendedProfileTinyRowUse, packedExtendedProfileTinyMass,
        selectedTinyCandidateRow,
        hfst, hsnd]

/-- The additive candidate construction exactly transposes the full
large/tiny capacity load. -/
theorem rowLoad_candidate_selected_eq_capacityLoad
    (rho omega : ℝ)
    (choice : G.V → ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileCapacityRow
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowLoad
        (G.packedExtendedProfileCandidateCapacityUse R0 rho omega)
        (match row with
          | Sum.inl large => Sum.inl (G.selectedLargeCandidateRow R0 choice large)
          | Sum.inr tiny => Sum.inr (G.selectedTinyCandidateRow R0 choice tiny))
        choice =
      G.packedExtendedProfileCapacityLoad R0 rho omega choice row := by
  rcases row with large | tiny
  · exact G.sum_largeCandidateUse_selected_eq_largeRowUse
      R0 rho omega choice large
  · exact G.sum_tinyCandidateUse_selected_eq_tinyRowUse
      R0 rho omega choice tiny

/-! ## A uniform bound for one source--row entry -/

/-- The smoothing probability is at least the uniform smoothing atom in the
common padded state space. -/
theorem omega_div_stateBound_le_smoothedExtendedProfileProbability
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (z : G.ExtendedProfileState R0 v) :
    omega / extendedProfileStateBound β q r ≤
      G.smoothedExtendedProfileProbability R0 omega v z := by
  have hcardNat := G.extendedProfileState_card_le R0 v
  have hcard : (Fintype.card (G.ExtendedProfileState R0 v) : ℝ) ≤
      extendedProfileStateBound β q r := by exact_mod_cast hcardNat
  have hcard0 : 0 < (Fintype.card (G.ExtendedProfileState R0 v) : ℝ) := by
    positivity
  have hbound0 : 0 < (extendedProfileStateBound β q r : ℝ) := by
    unfold extendedProfileStateBound
    positivity
  have huniform : omega / extendedProfileStateBound β q r ≤
      omega / Fintype.card (G.ExtendedProfileState R0 v) := by
    exact (div_le_div_iff₀ hbound0 hcard0).2
      (mul_le_mul_of_nonneg_left hcard homega0.le)
  have hbase := G.extendedProfileProbability_nonneg R0 hs hq hr0 hleft v z
  unfold smoothedExtendedProfileProbability
  exact huniform.trans (le_add_of_nonneg_left
    (mul_nonneg (sub_nonneg.mpr homega1) hbase))

/-- A single large assignment is at most the common edge-color mass. -/
theorem extendedProfileLargeAssign_le_edgeColorMass
    (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v)
    (i : Fin (explicitLargeSlotBound β q r)) :
    G.extendedProfileLargeAssign R0 v e z i ≤
      G.extendedProfileEdgeColorMass
        (s := s) (β := β) (n := n) e.1 := by
  have hslot : G.extendedProfileLargeAssign R0 v e z i ≤
      ∑ j, G.extendedProfileLargeAssign R0 v e z j :=
    Finset.single_le_sum
      (fun j _ ↦ G.extendedProfileLargeAssign_nonneg R0 v e z j)
      (Finset.mem_univ i)
  have hstate :
      (∑ j, G.extendedProfileLargeAssign R0 v e z j) ≤
      ∑ z', ∑ j, G.extendedProfileLargeAssign R0 v e z' j :=
    Finset.single_le_sum
      (fun z' _ ↦ Finset.sum_nonneg fun j _ ↦
        G.extendedProfileLargeAssign_nonneg R0 v e z' j)
      (Finset.mem_univ z)
  calc
    G.extendedProfileLargeAssign R0 v e z i ≤
        ∑ j, G.extendedProfileLargeAssign R0 v e z j := hslot
    _ ≤ ∑ z', ∑ j, G.extendedProfileLargeAssign R0 v e z' j := hstate
    _ = G.extendedProfileEdgeColorMass
          (s := s) (β := β) (n := n) e.1 := by
      simpa [extendedProfileEdgeColorMass] using
        G.sum_extendedProfileLargeAssign R0 v e

/-- The sum of the slots of one state is also at most the common edge-color
mass. -/
theorem sum_extendedProfileLargeAssign_le_edgeColorMass
    (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v) :
    (∑ i, G.extendedProfileLargeAssign R0 v e z i) ≤
      G.extendedProfileEdgeColorMass
        (s := s) (β := β) (n := n) e.1 := by
  calc
    (∑ i, G.extendedProfileLargeAssign R0 v e z i) ≤
        ∑ z', ∑ i, G.extendedProfileLargeAssign R0 v e z' i :=
      Finset.single_le_sum
        (fun z' _ ↦ Finset.sum_nonneg fun i _ ↦
          G.extendedProfileLargeAssign_nonneg R0 v e z' i)
        (Finset.mem_univ z)
    _ = G.extendedProfileEdgeColorMass
          (s := s) (β := β) (n := n) e.1 := by
      simpa [extendedProfileEdgeColorMass] using
        G.sum_extendedProfileLargeAssign R0 v e

/-- A single tiny assignment is at most the common tiny edge-color mass. -/
theorem extendedProfileTinyAssign_le_edgeColorMass
    (v : G.V) (e : G.StarEdge v)
    (z : G.ExtendedProfileState R0 v) :
    G.extendedProfileTinyAssign R0 v e z ≤
      G.extendedProfileTinyEdgeColorMass
        (s := s) (β := β) (n := n) e.1 := by
  calc
    G.extendedProfileTinyAssign R0 v e z ≤
        ∑ z', G.extendedProfileTinyAssign R0 v e z' :=
      Finset.single_le_sum
        (fun z' _ ↦ G.extendedProfileTinyAssign_nonneg R0 v e z')
        (Finset.mem_univ z)
    _ = G.extendedProfileTinyEdgeColorMass
          (s := s) (β := β) (n := n) e.1 := by
      simpa [extendedProfileTinyEdgeColorMass] using
        G.sum_extendedProfileTinyAssign R0 v e

/-- Elementary estimate used for both large and tiny equation-(23) entries.
The two assignments and the scaled edge-color mass are each at most `y`;
the two smoothed probabilities are at least `1/L`. -/
private theorem scaled_sum_pair_le
    {I : Type*} [Fintype I]
    (N rho y lambdaP lambdaQ L cap a : ℝ) (b : I → ℝ)
    (hN0 : 0 ≤ N) (hrho0 : 0 ≤ rho) (hy0 : 0 ≤ y)
    (hlambdaP : 0 < lambdaP) (hlambdaQ : 0 < lambdaQ)
    (hL0 : 0 ≤ L) (hcap0 : 0 ≤ cap)
    (hLP : 1 ≤ L * lambdaP)
    (hLQ : 1 ≤ L * lambdaQ)
    (ha0 : 0 ≤ a) (ha : a ≤ y)
    (hb0 : ∀ i, 0 ≤ b i) (hb : ∑ i, b i ≤ y)
    (hNy : N * y ≤ cap) :
    N * (∑ i, rho * a * b i / (y * lambdaP * lambdaQ)) ≤
      rho * cap * L ^ 2 := by
  by_cases hy : y = 0
  · have haZero : a = 0 := le_antisymm (ha.trans_eq hy) ha0
    simp [hy, haZero]
    positivity
  have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
  have hbsum0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ ↦ hb0 i
  have haDiv : a / lambdaP ≤ y * L := by
    apply (div_le_iff₀ hlambdaP).2
    calc
      a ≤ y := ha
      _ ≤ y * (L * lambdaP) := by
        simpa using mul_le_mul_of_nonneg_left hLP hy0
      _ = y * L * lambdaP := by ring
  have hbDiv : (∑ i, b i) / lambdaQ ≤ y * L := by
    apply (div_le_iff₀ hlambdaQ).2
    calc
      (∑ i, b i) ≤ y := hb
      _ ≤ y * (L * lambdaQ) := by
        simpa using mul_le_mul_of_nonneg_left hLQ hy0
      _ = y * L * lambdaQ := by ring
  have hrewrite :
      (∑ i, rho * a * b i / (y * lambdaP * lambdaQ)) =
        (rho / y) * (a / lambdaP) * ((∑ i, b i) / lambdaQ) := by
    calc
      (∑ i, rho * a * b i / (y * lambdaP * lambdaQ)) =
          ∑ i, (rho / y) * (a / lambdaP) * (b i / lambdaQ) := by
        apply Finset.sum_congr rfl
        intro i _hi
        field_simp [hy, hlambdaP.ne', hlambdaQ.ne']
        <;> ring
      _ = (rho / y) * (a / lambdaP) * ((∑ i, b i) / lambdaQ) := by
        rw [Finset.sum_div, Finset.mul_sum]
  rw [hrewrite]
  have hfactor0 : 0 ≤ N * (rho / y) :=
    mul_nonneg hN0 (div_nonneg hrho0 hy0)
  have hprod :
      (a / lambdaP) * ((∑ i, b i) / lambdaQ) ≤
        (y * L) * (y * L) :=
    mul_le_mul haDiv hbDiv
      (div_nonneg hbsum0 hlambdaQ.le)
      (mul_nonneg hy0 hL0)
  calc
    N * ((rho / y) * (a / lambdaP) * ((∑ i, b i) / lambdaQ)) =
        (N * (rho / y)) *
          ((a / lambdaP) * ((∑ i, b i) / lambdaQ)) := by ring
    _ ≤ (N * (rho / y)) * ((y * L) * (y * L)) :=
      mul_le_mul_of_nonneg_left hprod hfactor0
    _ = rho * (N * y) * L ^ 2 := by
      field_simp [hy]
      <;> ring
    _ ≤ rho * cap * L ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNy hrho0) (sq_nonneg L)

private theorem one_le_stateRatio_mul_smoothed
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (z : G.ExtendedProfileState R0 v) :
    1 ≤ ((extendedProfileStateBound β q r : ℝ) / omega) *
      G.smoothedExtendedProfileProbability R0 omega v z := by
  have hlower :=
    G.omega_div_stateBound_le_smoothedExtendedProfileProbability R0
      hs hq hr0 hleft homega0 homega1 v z
  have hratio0 : 0 ≤ (extendedProfileStateBound β q r : ℝ) / omega := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hlower hratio0
  have hbound0 : (extendedProfileStateBound β q r : ℝ) ≠ 0 := by
    unfold extendedProfileStateBound
    positivity
  have homegaNe : omega ≠ 0 := homega0.ne'
  calc
    1 = ((extendedProfileStateBound β q r : ℝ) / omega) *
        (omega / extendedProfileStateBound β q r) := by
      field_simp [hbound0, homegaNe]
    _ ≤ ((extendedProfileStateBound β q r : ℝ) / omega) *
        G.smoothedExtendedProfileProbability R0 omega v z := hmul

private theorem n_mul_largeEdgeColorMass_le_s
    (hn : 0 < n) (hs : 0 ≤ s) (e : G.E) :
    (n : ℝ) * G.extendedProfileEdgeColorMass
      (s := s) (β := β) (n := n) e ≤ s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold extendedProfileEdgeColorMass
  split
  · field_simp [hnR.ne']
    exact le_rfl
  · simpa using hs

private theorem n_mul_tinyEdgeColorMass_le_s
    (hn : 0 < n) (hs : 0 ≤ s) (e : G.E) :
    (n : ℝ) * G.extendedProfileTinyEdgeColorMass
      (s := s) (β := β) (n := n) e ≤ s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold extendedProfileTinyEdgeColorMass
  split
  · field_simp [hnR.ne']
    exact le_rfl
  · simpa using hs

/-- One oriented large edge contribution is bounded by the parameter-only
normalization. -/
theorem packedExtendedProfileLargeCandidateEdgeUse_le_scale
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r) (e : G.E)
    (row : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
        source sourceCode e row ≤
      extendedProfileCandidateCapacityScale rho s omega β q r := by
  let L : ℝ := (extendedProfileStateBound β q r : ℝ) / omega
  unfold packedExtendedProfileLargeCandidateEdgeUse
  split
  · rename_i hmatch
    let P : G.ExtendedProfileState R0 (G.fst e) := hmatch.1 ▸ row.candidate
    let Q := G.decodeExtendedProfileWord R0 (G.snd e) sourceCode row.color
    let y := G.extendedProfileEdgeColorMass
      (s := s) (β := β) (n := n) e
    have hy0 := G.extendedProfileEdgeColorMass_nonneg (β := β) hs hn e
    have hP0 := G.extendedProfileLargeAssign_nonneg R0
      (G.fst e) (G.fstStarEdge e) P row.slot
    have hP := G.extendedProfileLargeAssign_le_edgeColorMass R0
      (G.fst e) (G.fstStarEdge e) P row.slot
    have hQ0 : ∀ j, 0 ≤ G.extendedProfileLargeAssign R0
        (G.snd e) (G.sndStarEdge e) Q j := fun j ↦
      G.extendedProfileLargeAssign_nonneg R0 _ _ Q j
    have hQ := G.sum_extendedProfileLargeAssign_le_edgeColorMass R0
      (G.snd e) (G.sndStarEdge e) Q
    have hlamP := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
      hleft homega0 homega1 (G.fst e) P
    have hlamQ := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
      hleft homega0 homega1 (G.snd e) Q
    have hLP := G.one_le_stateRatio_mul_smoothed R0 hs hq hr0 hleft
      homega0 homega1 (G.fst e) P
    have hLQ := G.one_le_stateRatio_mul_smoothed R0 hs hq hr0 hleft
      homega0 homega1 (G.snd e) Q
    have hpair := scaled_sum_pair_le (I := Fin (explicitLargeSlotBound β q r))
      (n : ℝ) rho y
      (G.smoothedExtendedProfileProbability R0 omega (G.fst e) P)
      (G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q)
      L s
      (G.extendedProfileLargeAssign R0 (G.fst e)
        (G.fstStarEdge e) P row.slot)
      (fun j ↦ G.extendedProfileLargeAssign R0 (G.snd e)
        (G.sndStarEdge e) Q j)
      (Nat.cast_nonneg n) hrho hy0 hlamP hlamQ (by positivity) hs
      hLP hLQ hP0 hP hQ0 hQ
      (n_mul_largeEdgeColorMass_le_s G hn hs e)
    by_cases hy : y = 0 <;>
      simpa [extendedProfileProductOptionMass, pairedOption, P, Q, y, L,
        extendedProfileCandidateCapacityScale, hy] using hpair
  · split
    · rename_i hmatch
      let P := G.decodeExtendedProfileWord R0 (G.fst e) sourceCode row.color
      let Q : G.ExtendedProfileState R0 (G.snd e) := hmatch.1 ▸ row.candidate
      let y := G.extendedProfileEdgeColorMass
        (s := s) (β := β) (n := n) e
      have hy0 := G.extendedProfileEdgeColorMass_nonneg (β := β) hs hn e
      have hQ0 := G.extendedProfileLargeAssign_nonneg R0
        (G.snd e) (G.sndStarEdge e) Q row.slot
      have hQ := G.extendedProfileLargeAssign_le_edgeColorMass R0
        (G.snd e) (G.sndStarEdge e) Q row.slot
      have hP0 : ∀ i, 0 ≤ G.extendedProfileLargeAssign R0
          (G.fst e) (G.fstStarEdge e) P i := fun i ↦
        G.extendedProfileLargeAssign_nonneg R0 _ _ P i
      have hP := G.sum_extendedProfileLargeAssign_le_edgeColorMass R0
        (G.fst e) (G.fstStarEdge e) P
      have hlamQ := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
        hleft homega0 homega1 (G.snd e) Q
      have hlamP := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
        hleft homega0 homega1 (G.fst e) P
      have hLQ := G.one_le_stateRatio_mul_smoothed R0 hs hq hr0 hleft
        homega0 homega1 (G.snd e) Q
      have hLP := G.one_le_stateRatio_mul_smoothed R0 hs hq hr0 hleft
        homega0 homega1 (G.fst e) P
      have hpair := scaled_sum_pair_le
        (I := Fin (explicitLargeSlotBound β q r))
        (n : ℝ) rho y
        (G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q)
        (G.smoothedExtendedProfileProbability R0 omega (G.fst e) P)
        L s
        (G.extendedProfileLargeAssign R0 (G.snd e)
          (G.sndStarEdge e) Q row.slot)
        (fun i ↦ G.extendedProfileLargeAssign R0 (G.fst e)
          (G.fstStarEdge e) P i)
        (Nat.cast_nonneg n) hrho hy0 hlamQ hlamP (by positivity) hs
        hLQ hLP hQ0 hQ hP0 hP
        (n_mul_largeEdgeColorMass_le_s G hn hs e)
      by_cases hy : y = 0 <;>
        convert hpair using 1 <;>
          simp [extendedProfileProductOptionMass, pairedOption, P, Q, y, L,
            extendedProfileCandidateCapacityScale, hy, Nat.ne_of_gt hn] <;>
          first
          | (apply Finset.sum_congr rfl
             intro x _hx
             ring)
          | ring
    · exact extendedProfileCandidateCapacityScale_nonneg
        (omega := omega) (β := β) (q := q) (r := r) hrho hs

/-- One oriented tiny edge contribution is bounded by its edge weight times
the common normalization. -/
theorem packedExtendedProfileTinyCandidateEdgeUse_le_weight_mul_scale
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r) (e : G.E)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
        source sourceCode e row ≤
      G.weight e * extendedProfileCandidateCapacityScale rho s omega β q r := by
  let L : ℝ := (extendedProfileStateBound β q r : ℝ) / omega
  unfold packedExtendedProfileTinyCandidateEdgeUse
  split
  · rename_i hmatch
    let P : G.ExtendedProfileState R0 (G.fst e) := hmatch.1 ▸ row.candidate
    let Q := G.decodeExtendedProfileWord R0 (G.snd e) sourceCode row.color
    let y := G.extendedProfileTinyEdgeColorMass
      (s := s) (β := β) (n := n) e
    have hy0 := G.extendedProfileTinyEdgeColorMass_nonneg (β := β) hs hn e
    have hP0 := G.extendedProfileTinyAssign_nonneg R0
      (G.fst e) (G.fstStarEdge e) P
    have hP := G.extendedProfileTinyAssign_le_edgeColorMass R0
      (G.fst e) (G.fstStarEdge e) P
    have hQ0 := G.extendedProfileTinyAssign_nonneg R0
      (G.snd e) (G.sndStarEdge e) Q
    have hQ := G.extendedProfileTinyAssign_le_edgeColorMass R0
      (G.snd e) (G.sndStarEdge e) Q
    have hlamP := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
      hleft homega0 homega1 (G.fst e) P
    have hlamQ := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
      hleft homega0 homega1 (G.snd e) Q
    have hLP := G.one_le_stateRatio_mul_smoothed R0 hs hq hr0 hleft
      homega0 homega1 (G.fst e) P
    have hLQ := G.one_le_stateRatio_mul_smoothed R0 hs hq hr0 hleft
      homega0 homega1 (G.snd e) Q
    have hpair := scaled_sum_pair_le (I := Unit)
      (n : ℝ) rho y
      (G.smoothedExtendedProfileProbability R0 omega (G.fst e) P)
      (G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q)
      L s (G.extendedProfileTinyAssign R0 (G.fst e) (G.fstStarEdge e) P)
      (fun _ ↦ G.extendedProfileTinyAssign R0
        (G.snd e) (G.sndStarEdge e) Q)
      (Nat.cast_nonneg n) hrho hy0 hlamP hlamQ (by positivity) hs
      hLP hLQ hP0 hP (fun _ ↦ hQ0) (by simpa using hQ)
      (n_mul_tinyEdgeColorMass_le_s G hn hs e)
    have hpairWeighted := mul_le_mul_of_nonneg_left hpair (G.weight_nonneg e)
    calc
      (n : ℝ) * G.weight e *
          G.extendedProfileTinyProductOptionMass R0 rho omega e P Q =
          G.weight e * ((n : ℝ) *
            (∑ _x : Unit, rho *
              G.extendedProfileTinyAssign R0 (G.fst e) (G.fstStarEdge e) P *
              G.extendedProfileTinyAssign R0 (G.snd e) (G.sndStarEdge e) Q /
              (y * G.smoothedExtendedProfileProbability R0 omega (G.fst e) P *
                G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q))) := by
            by_cases hy : y = 0 <;>
              simp [extendedProfileTinyProductOptionMass, pairedOption, P, Q,
                y, hy] <;> ring
      _ ≤ G.weight e * extendedProfileCandidateCapacityScale rho s omega β q r := by
        simpa [L, extendedProfileCandidateCapacityScale] using hpairWeighted
  · split
    · rename_i hmatch
      let P := G.decodeExtendedProfileWord R0 (G.fst e) sourceCode row.color
      let Q : G.ExtendedProfileState R0 (G.snd e) := hmatch.1 ▸ row.candidate
      let y := G.extendedProfileTinyEdgeColorMass
        (s := s) (β := β) (n := n) e
      have hy0 := G.extendedProfileTinyEdgeColorMass_nonneg (β := β) hs hn e
      have hQ0 := G.extendedProfileTinyAssign_nonneg R0
        (G.snd e) (G.sndStarEdge e) Q
      have hQ := G.extendedProfileTinyAssign_le_edgeColorMass R0
        (G.snd e) (G.sndStarEdge e) Q
      have hP0 := G.extendedProfileTinyAssign_nonneg R0
        (G.fst e) (G.fstStarEdge e) P
      have hP := G.extendedProfileTinyAssign_le_edgeColorMass R0
        (G.fst e) (G.fstStarEdge e) P
      have hlamQ := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
        hleft homega0 homega1 (G.snd e) Q
      have hlamP := G.smoothedExtendedProfileProbability_pos R0 hs hq hr0
        hleft homega0 homega1 (G.fst e) P
      have hLQ := G.one_le_stateRatio_mul_smoothed R0 hs hq hr0 hleft
        homega0 homega1 (G.snd e) Q
      have hLP := G.one_le_stateRatio_mul_smoothed R0 hs hq hr0 hleft
        homega0 homega1 (G.fst e) P
      have hpair := scaled_sum_pair_le (I := Unit)
        (n : ℝ) rho y
        (G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q)
        (G.smoothedExtendedProfileProbability R0 omega (G.fst e) P)
        L s (G.extendedProfileTinyAssign R0 (G.snd e) (G.sndStarEdge e) Q)
        (fun _ ↦ G.extendedProfileTinyAssign R0
          (G.fst e) (G.fstStarEdge e) P)
        (Nat.cast_nonneg n) hrho hy0 hlamQ hlamP (by positivity) hs
        hLQ hLP hQ0 hQ (fun _ ↦ hP0) (by simpa using hP)
        (n_mul_tinyEdgeColorMass_le_s G hn hs e)
      have hpairWeighted := mul_le_mul_of_nonneg_left hpair (G.weight_nonneg e)
      calc
        (n : ℝ) * G.weight e *
            G.extendedProfileTinyProductOptionMass R0 rho omega e P Q =
            G.weight e * ((n : ℝ) *
              (∑ _x : Unit, rho *
                G.extendedProfileTinyAssign R0 (G.snd e) (G.sndStarEdge e) Q *
                G.extendedProfileTinyAssign R0 (G.fst e) (G.fstStarEdge e) P /
                (y * G.smoothedExtendedProfileProbability R0 omega (G.snd e) Q *
                  G.smoothedExtendedProfileProbability R0 omega (G.fst e) P))) := by
              by_cases hy : y = 0 <;>
                simp [extendedProfileTinyProductOptionMass, pairedOption, P, Q,
                  y, hy] <;> ring
        _ ≤ G.weight e * extendedProfileCandidateCapacityScale rho s omega β q r := by
          simpa [L, extendedProfileCandidateCapacityScale, mul_comm] using
            hpairWeighted
    · exact mul_nonneg (G.weight_nonneg e)
        (extendedProfileCandidateCapacityScale_nonneg
          (omega := omega) (β := β) (q := q) (r := r) hrho hs)

/-- The coarser unit envelope follows from `weight e ≤ 1`. -/
theorem packedExtendedProfileTinyCandidateEdgeUse_le_scale
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r) (e : G.E)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
        source sourceCode e row ≤
      extendedProfileCandidateCapacityScale rho s omega β q r := by
  exact (G.packedExtendedProfileTinyCandidateEdgeUse_le_weight_mul_scale R0
    hn hs hq hr0 hleft homega0 homega1 hrho source sourceCode e row).trans
      (mul_le_of_le_one_left
        (extendedProfileCandidateCapacityScale_nonneg
          (omega := omega) (β := β) (q := q) (r := r) hrho hs)
        (G.weight_le_one e))

/-- An edge joins an ordered pair of displayed vertices, in either endpoint
orientation. -/
def CandidateEdgeMatches (center source : G.V) (e : G.E) : Prop :=
  (center = G.fst e ∧ source = G.snd e) ∨
    (center = G.snd e ∧ source = G.fst e)

theorem candidateEdgeMatches_iff_endpointPairMatches
    (center source : G.V) (e : G.E) :
    G.CandidateEdgeMatches center source e ↔
      G.EndpointPairMatches center source e := by
  rfl

private theorem largeCandidateEdgeUse_eq_zero_of_not_matches
    (rho omega : ℝ) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r) (e : G.E)
    (row : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r))
    (h : ¬ G.CandidateEdgeMatches row.center source e) :
    G.packedExtendedProfileLargeCandidateEdgeUse R0 rho omega
      source sourceCode e row = 0 := by
  unfold CandidateEdgeMatches at h
  simp only [not_or] at h
  simp [packedExtendedProfileLargeCandidateEdgeUse, h.1, h.2]

private theorem tinyCandidateEdgeUse_eq_zero_of_not_matches
    (rho omega : ℝ) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r) (e : G.E)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r))
    (h : ¬ G.CandidateEdgeMatches row.center source e) :
    G.packedExtendedProfileTinyCandidateEdgeUse R0 rho omega
      source sourceCode e row = 0 := by
  unfold CandidateEdgeMatches at h
  simp only [not_or] at h
  simp [packedExtendedProfileTinyCandidateEdgeUse, h.1, h.2]

/-- Fixed endpoint multiplicity turns the edgewise large bound into an
`L`-scaled bound for the entire source--row coefficient. -/
theorem packedExtendedProfileLargeCandidateUse_le_mul_scale
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileLargeCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    G.packedExtendedProfileLargeCandidateUse R0 rho omega
        source sourceCode row ≤
      (L : ℝ) * extendedProfileCandidateCapacityScale rho s omega β q r := by
  unfold packedExtendedProfileLargeCandidateUse
  apply G.sum_le_mul_of_pairMultiplicityAtMost hmult row.center source
  · exact extendedProfileCandidateCapacityScale_nonneg
      (omega := omega) (β := β) (q := q) (r := r) hrho hs
  · intro e he
    exact G.packedExtendedProfileLargeCandidateEdgeUse_le_scale R0 hn hs hq
      hr0 hleft homega0 homega1 hrho source sourceCode e row
  · intro e he
    exact G.largeCandidateEdgeUse_eq_zero_of_not_matches R0 rho omega
      source sourceCode e row (by
        simpa [G.candidateEdgeMatches_iff_endpointPairMatches] using he)

/-- Tiny analogue of `packedExtendedProfileLargeCandidateUse_le_mul_scale`. -/
theorem packedExtendedProfileTinyCandidateUse_le_mul_scale
    {L : ℕ} (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    G.packedExtendedProfileTinyCandidateUse R0 rho omega
        source sourceCode row ≤
      (L : ℝ) * extendedProfileCandidateCapacityScale rho s omega β q r := by
  unfold packedExtendedProfileTinyCandidateUse
  apply G.sum_le_mul_of_pairMultiplicityAtMost hmult row.center source
  · exact extendedProfileCandidateCapacityScale_nonneg
      (omega := omega) (β := β) (q := q) (r := r) hrho hs
  · intro e he
    exact G.packedExtendedProfileTinyCandidateEdgeUse_le_scale R0 hn hs hq
      hr0 hleft homega0 homega1 hrho source sourceCode e row
  · intro e he
    exact G.tinyCandidateEdgeUse_eq_zero_of_not_matches R0 rho omega
      source sourceCode e row (by
        simpa [G.candidateEdgeMatches_iff_endpointPairMatches] using he)

/-- Every coefficient normalized by the `L`-enlarged candidate scale is at
most one. -/
theorem scaledPackedExtendedProfileCandidateCapacityUse_le_one
    {L : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega
        ((L : ℝ) * extendedProfileCandidateCapacityScale rho s omega β q r)
        source sourceCode row ≤ 1 := by
  apply (div_le_one (mul_pos (by exact_mod_cast hL)
    (extendedProfileCandidateCapacityScale_pos
      (β := β) (q := q) (r := r) hrho hspos homega0))).2
  rcases row with large | tiny
  · exact G.packedExtendedProfileLargeCandidateUse_le_mul_scale R0 hmult hn hs hq
      hr0 hleft homega0 homega1 hrho.le source sourceCode large
  · exact G.packedExtendedProfileTinyCandidateUse_le_mul_scale R0 hmult hn hs hq
      hr0 hleft homega0 homega1 hrho.le source sourceCode tiny

/-! ## Positivity -/

theorem packedExtendedProfileCandidateCapacityUse_nonneg
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (source : G.V)
    (sourceCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    0 ≤ G.packedExtendedProfileCandidateCapacityUse R0 rho omega
      source sourceCode row := by
  rcases row with large | tiny
  · unfold packedExtendedProfileCandidateCapacityUse
    unfold packedExtendedProfileLargeCandidateUse
    apply Finset.sum_nonneg
    intro e _he
    unfold packedExtendedProfileLargeCandidateEdgeUse
    split
    · exact mul_nonneg (Nat.cast_nonneg n) (Finset.sum_nonneg fun j _ ↦
        G.extendedProfileProductOptionMass_nonneg R0 hs hn hq hr0 hleft
          homega0 homega1 hrho e _ _ _ j)
    · split
      · exact mul_nonneg (Nat.cast_nonneg n) (Finset.sum_nonneg fun i _ ↦
          G.extendedProfileProductOptionMass_nonneg R0 hs hn hq hr0 hleft
            homega0 homega1 hrho e _ _ i _)
      · exact le_rfl
  · unfold packedExtendedProfileCandidateCapacityUse
    unfold packedExtendedProfileTinyCandidateUse
    apply Finset.sum_nonneg
    intro e _he
    unfold packedExtendedProfileTinyCandidateEdgeUse
    split
    · exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg n) (G.weight_nonneg e))
        (G.extendedProfileTinyProductOptionMass_nonneg R0 hs hn hq hr0
          hleft homega0 homega1 hrho e _ _)
    · split
      · exact mul_nonneg
          (mul_nonneg (Nat.cast_nonneg n) (G.weight_nonneg e))
          (G.extendedProfileTinyProductOptionMass_nonneg R0 hs hn hq hr0
            hleft homega0 homega1 hrho e _ _)
      · exact le_rfl

theorem scaledPackedExtendedProfileCandidateCapacityUse_nonneg
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hscale : 0 ≤ scale)
    (source : G.V) (sourceCode : ExtendedProfilePackedWordState n β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    0 ≤ G.scaledPackedExtendedProfileCandidateCapacityUse R0 rho omega scale
      source sourceCode row := by
  exact div_nonneg
    (G.packedExtendedProfileCandidateCapacityUse_nonneg R0 hn hs hq hr0
      hleft homega0 homega1 hrho source sourceCode row)
    hscale

end WeightedMultigraph

end

end WeightedEdgeColoring
