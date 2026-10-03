import WeightedEdgeColoring.MultigraphExtendedProfileAtomCandidateCapacityRows
import WeightedEdgeColoring.MultigraphExtendedProfileBlockPackingSelection

/-!
# Candidate capacity rows for block sources

A source is `(vertex, block)` and stores all `k` profile atoms in that
block.  A capacity row still reads one colour.  We decode the row colour as
`(block, position)` through `finProdFinEquiv`; only the matching block source
contributes, and the already verified atom-source coefficient is applied to
that coordinate.

Thus pointwise and mean bounds are inherited exactly from the atom rows.
A block column contains `k` atom-coordinate columns, so its column bound is
at most `k` times the atom column bound.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- The one-colour atom code read from a padded block code. -/
def extendedProfileBlockCoordinateCode
    (v : G.V) (a : ExtendedProfilePackedBlockState k β q r)
    (j : Fin k) : Fin (extendedProfileStateBound β q r) :=
  G.extendedProfileStateCode R0 v
    (G.decodeExtendedProfileBlock R0 v a j)

/-- Candidate capacity use of a block source. -/
def blockExtendedProfileCandidateCapacityUse
    (rho omega : ℝ) (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := B * k) (β := β) (q := q) (r := r)) : ℝ :=
  let c := G.extendedProfileCandidateCapacityRowColor R0 row
  if source.2 = extendedProfileColorBlock c then
    G.atomExtendedProfileCandidateCapacityUse R0 rho omega
      (source.1, c)
      (G.extendedProfileBlockCoordinateCode R0 source.1 sourceCode
        (extendedProfileColorPosition c)) row
  else 0

def scaledBlockExtendedProfileCandidateCapacityUse
    (rho omega scale : ℝ) (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := B * k) (β := β) (q := q) (r := r)) : ℝ :=
  let c := G.extendedProfileCandidateCapacityRowColor R0 row
  if source.2 = extendedProfileColorBlock c then
    G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega scale
      (source.1, c)
      (G.extendedProfileBlockCoordinateCode R0 source.1 sourceCode
        (extendedProfileColorPosition c)) row
  else 0

theorem scaledBlockCandidateCapacityUse_eq_div
    (rho omega scale : ℝ) (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := B * k) (β := β) (q := q) (r := r)) :
    G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega scale
        source sourceCode row =
      G.blockExtendedProfileCandidateCapacityUse R0 rho omega
        source sourceCode row / scale := by
  by_cases hblock : source.2 = extendedProfileColorBlock
      (G.extendedProfileCandidateCapacityRowColor R0 row)
  · simp [scaledBlockExtendedProfileCandidateCapacityUse,
      blockExtendedProfileCandidateCapacityUse, hblock,
      G.scaledAtomCandidateCapacityUse_eq_div R0]
  · simp [scaledBlockExtendedProfileCandidateCapacityUse,
      blockExtendedProfileCandidateCapacityUse, hblock]

theorem scaledBlockCandidateCapacityUse_nonneg
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hscale : 0 ≤ scale)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := B * k) (β := β) (q := q) (r := r)) :
    0 ≤ G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega scale
      source sourceCode row := by
  unfold scaledBlockExtendedProfileCandidateCapacityUse
  dsimp only
  split
  · exact G.scaledAtomExtendedProfileCandidateCapacityUse_nonneg R0
      hn hs hq hr0 hleft homega0 homega1 hrho hscale _ _ _
  · exact le_rfl

theorem scaledBlockCandidateCapacityUse_le_one
    {L : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := B * k) (β := β) (q := q) (r := r)) :
    G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
        ((L : ℝ) * extendedProfileCandidateCapacityScale rho s omega β q r)
        source sourceCode row ≤ 1 := by
  unfold scaledBlockExtendedProfileCandidateCapacityUse
  dsimp only
  split
  · exact G.scaledAtomExtendedProfileCandidateCapacityUse_le_one R0
      hL hmult hn hs hq hr0 hleft homega0 homega1 hrho hspos _ _ _
  · norm_num

/-- Decode selected block codes into the full exactly padded palette word. -/
def decodedExtendedProfileBlockSelection
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r) :
    G.ExtendedSelectedProfileWord R0 :=
  fun v c ↦ G.decodeExtendedProfileBlock R0 v
    (choice (v, extendedProfileColorBlock c))
    (extendedProfileColorPosition c)

/-- Capacity row obtained by inserting the decoded selected center atom. -/
def selectedBlockCandidateCapacityRow
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileCapacityRow
      (n := B * k) (β := β) (q := q) (r := r)) :
    G.ExtendedProfileCandidateCapacityRow R0
      (n := B * k) (β := β) (q := q) (r := r) :=
  G.selectedAtomCandidateCapacityRow R0
    (G.decodedExtendedProfileBlockSelection R0 choice) row

def selectedBlockCapacityLoad
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileCapacityRow
      (n := B * k) (β := β) (q := q) (r := r)) : ℝ :=
  G.selectedAtomCapacityLoad R0 rho omega
    (G.decodedExtendedProfileBlockSelection R0 choice) row

/-- Block-coordinate marginals agree with the padded one-atom law. -/
theorem sum_paddedBlock_mul_coordinateCode_eq_atom
    (omega : ℝ) (v : G.V) (j : Fin k)
    (f : Fin (extendedProfileStateBound β q r) → ℝ) :
    (∑ a : ExtendedProfilePackedBlockState k β q r,
      G.paddedExtendedProfileBlockProbability R0 omega v a *
        f (G.extendedProfileBlockCoordinateCode R0 v a j)) =
      ∑ a : Fin (extendedProfileStateBound β q r),
        G.paddedExtendedProfileStateProbability R0 omega v a * f a := by
  classical
  have hblock :=
    FiniteDependentWordPadding.sum_paddedWordProbability_mul_decode_coordinate
      (fun v ↦ G.ExtendedProfileState R0 v)
      (G.extendedProfileStateEncoding R0)
      (G.inactiveExtendedProfileState R0)
      (fun v z ↦ G.smoothedExtendedProfileProbability R0 omega v z)
      (G.sum_smoothedExtendedProfileProbability R0 omega)
      v j (fun z ↦ f (G.extendedProfileStateCode R0 v z))
  have hatom := G.sum_paddedExtendedProfileStateProbability_mul
    R0 omega v f
  calc
    (∑ a : ExtendedProfilePackedBlockState k β q r,
      G.paddedExtendedProfileBlockProbability R0 omega v a *
        f (G.extendedProfileBlockCoordinateCode R0 v a j)) =
        ∑ z : G.ExtendedProfileState R0 v,
          G.smoothedExtendedProfileProbability R0 omega v z *
            f (G.extendedProfileStateCode R0 v z) := by
      simpa [paddedExtendedProfileBlockProbability,
        decodeExtendedProfileBlock, extendedProfileBlockCoordinateCode] using
          hblock
    _ = ∑ a : Fin (extendedProfileStateBound β q r),
        G.paddedExtendedProfileStateProbability R0 omega v a * f a :=
      hatom.symm

theorem rowMean_scaledBlockCandidateCapacityUse_eq_atom
    (omega rho scale : ℝ)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := B * k) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
        (G.scaledBlockExtendedProfileCandidateCapacityUse
          R0 rho omega scale) row =
      FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileStateProbability R0 omega source.1 a)
        (G.scaledAtomExtendedProfileCandidateCapacityUse
          R0 rho omega scale) row := by
  classical
  let c := G.extendedProfileCandidateCapacityRowColor R0 row
  let b := extendedProfileColorBlock c
  let j := extendedProfileColorPosition c
  unfold FiniteCategoricalSelection.rowMean
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single c]
    · simpa [scaledBlockExtendedProfileCandidateCapacityUse, b, c, j] using
        G.sum_paddedBlock_mul_coordinateCode_eq_atom R0 omega v j
          (fun a ↦ G.scaledAtomExtendedProfileCandidateCapacityUse
            R0 rho omega scale (v, c) a row)
    · intro c' _hc' hc'
      have hcne : c' ≠
          G.extendedProfileCandidateCapacityRowColor R0 row := by
        simpa [c] using hc'
      simp [scaledAtomExtendedProfileCandidateCapacityUse, hcne]
    · simp
  · intro b' _hb' hb'
    have hbne : b' ≠ extendedProfileColorBlock
        (G.extendedProfileCandidateCapacityRowColor R0 row) := by
      simpa [b, c] using hb'
    simp [scaledBlockExtendedProfileCandidateCapacityUse, hbne]
  · simp

theorem rowMean_scaledBlockCandidateCapacityUse_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := B * k) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
        (G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
          (extendedProfileCandidateCapacityScale rho s omega β q r)) row ≤
      ((B * k : ℕ) : ℝ) * rho /
        (extendedProfileCandidateCapacityScale rho s omega β q r *
          extendedProfileSmoothingKappa omega β q r) := by
  rw [G.rowMean_scaledBlockCandidateCapacityUse_eq_atom R0]
  rw [G.rowMean_scaledAtomCandidateCapacityUse_eq_packedWord R0]
  exact G.rowMean_scaledCandidateCapacityUse_le R0
    hn hs hq hr0 hleft homega0 homega1 hrho hspos row

/-- Enlarging the capacity normalization by a positive integral multiplicity
can only decrease every scaled block coefficient. -/
theorem scaledBlockCandidateCapacityUse_mul_scale_le
    {L : ℕ} (hL : 0 < L)
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := B * k) (β := β) (q := q) (r := r)) :
    G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
        ((L : ℝ) * extendedProfileCandidateCapacityScale rho s omega β q r)
        source sourceCode row ≤
      G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
        (extendedProfileCandidateCapacityScale rho s omega β q r)
        source sourceCode row := by
  let scale := extendedProfileCandidateCapacityScale rho s omega β q r
  have hscale : 0 < scale :=
    extendedProfileCandidateCapacityScale_pos
      (omega := omega) (β := β) (q := q) (r := r)
      hrho hspos homega0
  have hLone : (1 : ℝ) ≤ L := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hL.ne')
  have hraw : 0 ≤ G.blockExtendedProfileCandidateCapacityUse R0 rho omega
      source sourceCode row := by
    have h := G.scaledBlockCandidateCapacityUse_nonneg R0
      hn hs hq hr0 hleft homega0 homega1 hrho.le (show (0 : ℝ) ≤ 1 by norm_num)
      source sourceCode row
    simpa [G.scaledBlockCandidateCapacityUse_eq_div R0] using h
  rw [G.scaledBlockCandidateCapacityUse_eq_div R0,
    G.scaledBlockCandidateCapacityUse_eq_div R0]
  exact div_le_div_of_nonneg_left hraw hscale
    (le_mul_of_one_le_left hscale.le hLone)

theorem rowMean_scaledBlockCandidateCapacityUse_mul_scale_le
    {L : ℕ} (hL : 0 < L)
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (row : G.ExtendedProfileCandidateCapacityRow R0
      (n := B * k) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
        (G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
          ((L : ℝ) * extendedProfileCandidateCapacityScale
            rho s omega β q r)) row ≤
      ((B * k : ℕ) : ℝ) * rho /
        (((L : ℝ) * extendedProfileCandidateCapacityScale rho s omega β q r) *
          extendedProfileSmoothingKappa omega β q r) := by
  let scale := extendedProfileCandidateCapacityScale rho s omega β q r
  have hscale : 0 < scale :=
    extendedProfileCandidateCapacityScale_pos
      (omega := omega) (β := β) (q := q) (r := r)
      hrho hspos homega0
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hpoint : ∀ source a,
      G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
          ((L : ℝ) * scale) source a row =
        G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
          scale source a row / L := by
    intro source a
    rw [G.scaledBlockCandidateCapacityUse_eq_div R0,
      G.scaledBlockCandidateCapacityUse_eq_div R0]
    field_simp [hLreal.ne', hscale.ne']
  have heq :
      FiniteCategoricalSelection.rowMean
          (fun source a ↦
            G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
          (G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
            ((L : ℝ) * scale)) row =
        FiniteCategoricalSelection.rowMean
          (fun source a ↦
            G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
          (G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
            scale) row / L := by
    unfold FiniteCategoricalSelection.rowMean
    simp_rw [hpoint, ← mul_div_assoc, Finset.sum_div]
  rw [heq]
  have hbase := G.rowMean_scaledBlockCandidateCapacityUse_le R0
    hn hs hq hr0 hleft homega0 homega1 hrho hspos row
  have hdiv := div_le_div_of_nonneg_right hbase hLreal.le
  dsimp only [scale] at hdiv ⊢
  convert hdiv using 1 <;> field_simp [hLreal.ne', hscale.ne'] <;> ring

/-- The selected block-source row load is the original two-endpoint
capacity load of the decoded full palette word. -/
theorem rowLoad_blockCandidate_selected_eq_capacityLoad
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileCapacityRow
      (n := B * k) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowLoad
        (G.blockExtendedProfileCandidateCapacityUse R0 rho omega)
        (G.selectedBlockCandidateCapacityRow R0 choice row) choice =
      G.selectedBlockCapacityLoad R0 rho omega choice row := by
  classical
  let selected := G.decodedExtendedProfileBlockSelection R0 choice
  let candidate := G.selectedAtomCandidateCapacityRow R0 selected row
  let c := G.extendedProfileCandidateCapacityRowColor R0 candidate
  let b := extendedProfileColorBlock c
  have hblockAtom :
      FiniteCategoricalSelection.rowLoad
          (G.blockExtendedProfileCandidateCapacityUse R0 rho omega)
          candidate choice =
        FiniteCategoricalSelection.rowLoad
          (G.atomExtendedProfileCandidateCapacityUse R0 rho omega)
          candidate
          (fun source ↦ G.extendedProfileStateCode R0 source.1
            (selected source.1 source.2)) := by
    unfold FiniteCategoricalSelection.rowLoad
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v _hv
    rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single c]
      · simp [blockExtendedProfileCandidateCapacityUse,
          selected, decodedExtendedProfileBlockSelection, candidate, b, c,
          extendedProfileBlockCoordinateCode]
      · intro c' _hc' hc'
        have hcne : c' ≠
            G.extendedProfileCandidateCapacityRowColor R0 candidate := by
          simpa [c] using hc'
        simp [atomExtendedProfileCandidateCapacityUse, hcne]
      · simp
    · intro b' _hb' hb'
      have hbne : b' ≠ extendedProfileColorBlock
          (G.extendedProfileCandidateCapacityRowColor R0 candidate) := by
        simpa [b, c] using hb'
      simp [blockExtendedProfileCandidateCapacityUse, hbne]
    · simp
  calc
    FiniteCategoricalSelection.rowLoad
        (G.blockExtendedProfileCandidateCapacityUse R0 rho omega)
        (G.selectedBlockCandidateCapacityRow R0 choice row) choice =
        FiniteCategoricalSelection.rowLoad
          (G.atomExtendedProfileCandidateCapacityUse R0 rho omega)
          candidate
          (fun source ↦ G.extendedProfileStateCode R0 source.1
            (selected source.1 source.2)) := by
      simpa [selectedBlockCandidateCapacityRow, selected, candidate] using
        hblockAtom
    _ = G.selectedAtomCapacityLoad R0 rho omega selected row :=
      G.rowLoad_atomCandidate_selected_eq_capacityLoad
        R0 rho omega selected row
    _ = G.selectedBlockCapacityLoad R0 rho omega choice row := rfl

theorem rowLoad_scaledBlockCandidate_selected_eq_capacityLoad_div
    (rho omega scale : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (row : G.ExtendedProfileCapacityRow
      (n := B * k) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowLoad
        (G.scaledBlockExtendedProfileCandidateCapacityUse
          R0 rho omega scale)
        (G.selectedBlockCandidateCapacityRow R0 choice row) choice =
      G.selectedBlockCapacityLoad R0 rho omega choice row / scale := by
  classical
  unfold FiniteCategoricalSelection.rowLoad
  simp_rw [G.scaledBlockCandidateCapacityUse_eq_div R0]
  rw [← Finset.sum_div]
  exact congrArg (fun x : ℝ ↦ x / scale)
    (G.rowLoad_blockCandidate_selected_eq_capacityLoad
      R0 rho omega choice row)

/-- One block column is the sum of its `k` atom-coordinate subcolumns. -/
theorem sum_scaledBlockCandidateCapacityUse_le_column
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (hpack : G.LocallyPacksInto (B * k))
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r) :
    (∑ row : G.ExtendedProfileCandidateCapacityRow R0
        (n := B * k) (β := β) (q := q) (r := r),
      G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
        (extendedProfileCandidateCapacityScale rho s omega β q r)
        source sourceCode row) ≤
      k * extendedProfileCandidateCapacityColumnBound (B * k) β q r := by
  let scale := extendedProfileCandidateCapacityScale rho s omega β q r
  have hsplit :
      (∑ row : G.ExtendedProfileCandidateCapacityRow R0
          (n := B * k) (β := β) (q := q) (r := r),
        G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega scale
          source sourceCode row) =
        ∑ j : Fin k,
          ∑ row : G.ExtendedProfileCandidateCapacityRow R0
              (n := B * k) (β := β) (q := q) (r := r),
            G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega scale
              (source.1, finProdFinEquiv (source.2, j))
              (G.extendedProfileBlockCoordinateCode R0 source.1 sourceCode j)
              row := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro row _hrow
    let c := G.extendedProfileCandidateCapacityRowColor R0 row
    by_cases hb : source.2 = extendedProfileColorBlock c
    · let j := extendedProfileColorPosition c
      have hc : finProdFinEquiv (source.2, j) = c := by
        simpa [j, extendedProfileColorBlock, extendedProfileColorPosition, hb]
          using (finProdFinEquiv.apply_symm_apply c)
      rw [Finset.sum_eq_single j]
      · simp [scaledBlockExtendedProfileCandidateCapacityUse, scale,
          c, j, hb]
        have hreconstruct :
            finProdFinEquiv
                (extendedProfileColorBlock
                    (G.extendedProfileCandidateCapacityRowColor R0 row),
                  extendedProfileColorPosition
                    (G.extendedProfileCandidateCapacityRowColor R0 row)) =
              G.extendedProfileCandidateCapacityRowColor R0 row := by
          simpa [extendedProfileColorBlock, extendedProfileColorPosition] using
            (finProdFinEquiv.apply_symm_apply
              (G.extendedProfileCandidateCapacityRowColor R0 row))
        rw [hreconstruct]
      · intro j' _hj' hj'
        have hcne : finProdFinEquiv (source.2, j') ≠ c := by
          intro heq
          have := congrArg extendedProfileColorPosition heq
          simp [j, extendedProfileColorPosition_mk] at this
          exact hj' this
        have hcne' : finProdFinEquiv (source.2, j') ≠
            G.extendedProfileCandidateCapacityRowColor R0 row := by
          simpa [c] using hcne
        simp [scaledAtomExtendedProfileCandidateCapacityUse, hcne']
      · simp
    · have hcne : ∀ j : Fin k, finProdFinEquiv (source.2, j) ≠ c := by
        intro j heq
        have := congrArg extendedProfileColorBlock heq
        simp [extendedProfileColorBlock_mk] at this
        exact hb this
      have hb' : source.2 ≠ extendedProfileColorBlock
          (G.extendedProfileCandidateCapacityRowColor R0 row) := by
        simpa [c] using hb
      have hcne' : ∀ j : Fin k, finProdFinEquiv (source.2, j) ≠
          G.extendedProfileCandidateCapacityRowColor R0 row := by
        intro j
        simpa [c] using hcne j
      simp [scaledBlockExtendedProfileCandidateCapacityUse, hb',
        scaledAtomExtendedProfileCandidateCapacityUse, hcne']
  rw [hsplit]
  calc
    (∑ j : Fin k,
      ∑ row : G.ExtendedProfileCandidateCapacityRow R0
          (n := B * k) (β := β) (q := q) (r := r),
        G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega scale
          (source.1, finProdFinEquiv (source.2, j))
          (G.extendedProfileBlockCoordinateCode R0 source.1 sourceCode j)
          row) ≤
        ∑ _j : Fin k,
          extendedProfileCandidateCapacityColumnBound (B * k) β q r := by
      exact Finset.sum_le_sum fun j _hj ↦
        G.sum_scaledAtomCandidateCapacityUse_le_column R0
          hn hs hq hr0 hleft homega0 homega1 hrho hspos hpack
          (source.1, finProdFinEquiv (source.2, j))
          (G.extendedProfileBlockCoordinateCode R0 source.1 sourceCode j)
    _ = k * extendedProfileCandidateCapacityColumnBound
        (B * k) β q r := by simp

theorem sum_scaledBlockCandidateCapacityUse_mul_scale_le_column
    {L : ℕ} (hL : 0 < L)
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (hpack : G.LocallyPacksInto (B * k))
    (source : G.V × Fin B)
    (sourceCode : ExtendedProfilePackedBlockState k β q r) :
    (∑ row : G.ExtendedProfileCandidateCapacityRow R0
        (n := B * k) (β := β) (q := q) (r := r),
      G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
        ((L : ℝ) * extendedProfileCandidateCapacityScale
          rho s omega β q r) source sourceCode row) ≤
      k * extendedProfileCandidateCapacityColumnBound (B * k) β q r := by
  calc
    (∑ row : G.ExtendedProfileCandidateCapacityRow R0
        (n := B * k) (β := β) (q := q) (r := r),
      G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
        ((L : ℝ) * extendedProfileCandidateCapacityScale
          rho s omega β q r) source sourceCode row) ≤
      ∑ row : G.ExtendedProfileCandidateCapacityRow R0
          (n := B * k) (β := β) (q := q) (r := r),
        G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
          (extendedProfileCandidateCapacityScale rho s omega β q r)
          source sourceCode row :=
      Finset.sum_le_sum fun row _hrow ↦
        G.scaledBlockCandidateCapacityUse_mul_scale_le R0
          hL hn hs hq hr0 hleft homega0 homega1 hrho hspos
          source sourceCode row
    _ ≤ _ := G.sum_scaledBlockCandidateCapacityUse_le_column R0
      hn hs hq hr0 hleft homega0 homega1 hrho hspos hpack
      source sourceCode

end WeightedMultigraph

end

end WeightedEdgeColoring
