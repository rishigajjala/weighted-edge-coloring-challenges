import WeightedEdgeColoring.ColorDependentExtendedProfileAtomAssignments
import WeightedEdgeColoring.ColorDependentExtendedProfileCapacityArrays

/-!
# Candidate rows for color-dependent extended-profile atoms

A row fixes a color, a center vertex, and a candidate center state.  Its
only source on an edge is the opposite endpoint.  This makes the two-endpoint
product coefficient additive, while the exact one-endpoint expectation
identities reduce its mean to the center's local slot or reservoir load.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w} [Fintype Color] [DecidableEq Color]
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}

section CandidateRowTypes

variable {proposal : G.E → Color → ℝ}
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

structure ColorDependentLargeCandidateRow (c : Color) where
  center : G.V
  candidate : G.ColorDependentExtendedProfileState R center c
  slot : Fin (explicitLargeSlotBound β q r)

structure ColorDependentTinyCandidateRow (c : Color) where
  center : G.V
  candidate : G.ColorDependentExtendedProfileState R center c

def colorDependentLargeCandidateRowEquiv (c : Color) :
    G.ColorDependentLargeCandidateRow R c ≃
      Σ v : G.V, G.ColorDependentExtendedProfileState R v c ×
        Fin (explicitLargeSlotBound β q r) where
  toFun row := ⟨row.center, row.candidate, row.slot⟩
  invFun row := ⟨row.1, row.2.1, row.2.2⟩
  left_inv row := by cases row; rfl
  right_inv row := by rcases row with ⟨v, z, i⟩; rfl

def colorDependentTinyCandidateRowEquiv (c : Color) :
    G.ColorDependentTinyCandidateRow R c ≃
      Σ v : G.V, G.ColorDependentExtendedProfileState R v c where
  toFun row := ⟨row.center, row.candidate⟩
  invFun row := ⟨row.1, row.2⟩
  left_inv row := by cases row; rfl
  right_inv row := by rcases row with ⟨v, z⟩; rfl

noncomputable instance (c : Color) : Fintype
    (G.ColorDependentLargeCandidateRow R c) :=
  Fintype.ofEquiv _ (G.colorDependentLargeCandidateRowEquiv R c).symm

noncomputable instance (c : Color) : DecidableEq
    (G.ColorDependentLargeCandidateRow R c) := Classical.decEq _

noncomputable instance (c : Color) : Fintype
    (G.ColorDependentTinyCandidateRow R c) :=
  Fintype.ofEquiv _ (G.colorDependentTinyCandidateRowEquiv R c).symm

noncomputable instance (c : Color) : DecidableEq
    (G.ColorDependentTinyCandidateRow R c) := Classical.decEq _

/-- Per-color family consumed by the generic capacity-array lift. -/
abbrev ColorDependentCandidateRowAt (c : Color) :=
  G.ColorDependentLargeCandidateRow R c ⊕
    G.ColorDependentTinyCandidateRow R c

end CandidateRowTypes

section ProposalDependentUses

variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

def colorDependentLargeCandidateEdgeUse
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (e : G.E) (row : G.ColorDependentLargeCandidateRow R c) : ℝ :=
  if h : row.center = G.fst e ∧ source = G.snd e then
    ∑ j, G.colorDependentExtendedProfileLargeProductMass
      proposal R rho omega e c (h.1 ▸ row.candidate)
        (h.2 ▸ sourceState) row.slot j
  else if h : row.center = G.snd e ∧ source = G.fst e then
    ∑ i, G.colorDependentExtendedProfileLargeProductMass
      proposal R rho omega e c (h.2 ▸ sourceState)
        (h.1 ▸ row.candidate) i row.slot
  else 0

def colorDependentTinyCandidateEdgeUse
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (e : G.E) (row : G.ColorDependentTinyCandidateRow R c) : ℝ :=
  if h : row.center = G.fst e ∧ source = G.snd e then
    G.weight e * G.colorDependentExtendedProfileTinyProductMass
      proposal R rho omega e c (h.1 ▸ row.candidate) (h.2 ▸ sourceState)
  else if h : row.center = G.snd e ∧ source = G.fst e then
    G.weight e * G.colorDependentExtendedProfileTinyProductMass
      proposal R rho omega e c (h.2 ▸ sourceState) (h.1 ▸ row.candidate)
  else 0

/-- The actual per-color atom coefficient. -/
def colorDependentCandidateAtomUse
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (row : G.ColorDependentCandidateRowAt R c) : ℝ :=
  match row with
  | Sum.inl large =>
      ∑ e, G.colorDependentLargeCandidateEdgeUse
        proposal R rho omega source c sourceState e large
  | Sum.inr tiny =>
      ∑ e, G.colorDependentTinyCandidateEdgeUse
        proposal R rho omega source c sourceState e tiny

/-- Fixed normalization for diffuse proposals satisfying
`proposal e c ≤ C0 / n`.  The raw equation-(23) coefficient is then at
most `scale / n`, so multiplying by `n / scale` produces a unit-bounded
packing coefficient while amplifying a constant raw row mean to order `n`. -/
def colorDependentCandidateCapacityScale
    (rho s omega β q r C0 : ℝ) : ℝ :=
  rho * s * C0 * ((extendedProfileStateBound β q r : ℝ) / omega) ^ 2

def scaledColorDependentCandidateAtomUse
    (n : ℕ) (scale rho omega : ℝ) (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (row : G.ColorDependentCandidateRowAt R c) : ℝ :=
  (n : ℝ) *
    G.colorDependentCandidateAtomUse proposal R rho omega source c
      sourceState row / scale

theorem colorDependentCandidateCapacityScale_pos
    (hrho : 0 < rho) (hs : 0 < s) (hC0 : 0 < C0) (homega : 0 < omega) :
    0 < colorDependentCandidateCapacityScale rho s omega β q r C0 := by
  unfold colorDependentCandidateCapacityScale extendedProfileStateBound
    profileStateBound
  positivity

theorem colorDependentCandidateCapacityScale_nonneg
    (hrho : 0 ≤ rho) (hs : 0 ≤ s) (hC0 : 0 ≤ C0) (homega : 0 ≤ omega) :
    0 ≤ colorDependentCandidateCapacityScale rho s omega β q r C0 := by
  unfold colorDependentCandidateCapacityScale
  positivity

include R

theorem n_mul_colorDependentLargeEdgeColorMass_le
    {n : ℕ} (hn : 0 < n) (hs : 0 ≤ s) (hC0 : 0 ≤ C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (c : Color) :
    (n : ℝ) * G.colorDependentExtendedProfileLargeEdgeColorMass
      (s := s) (β := β) proposal e c ≤ s * C0 := by
  unfold colorDependentExtendedProfileLargeEdgeColorMass
  split
  · calc
      (n : ℝ) * (s * proposal e c) ≤
          (n : ℝ) * (s * (C0 / (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        exact mul_le_mul_of_nonneg_left (hproposal e c) hs
      _ = s * C0 := by
        field_simp [Nat.ne_of_gt hn]
  · simpa using mul_nonneg hs hC0

theorem n_mul_colorDependentTinyEdgeColorMass_le
    {n : ℕ} (hn : 0 < n) (hs : 0 ≤ s) (hC0 : 0 ≤ C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (c : Color) :
    (n : ℝ) * G.colorDependentExtendedProfileTinyEdgeColorMass
      (s := s) (β := β) proposal e c ≤ s * C0 := by
  unfold colorDependentExtendedProfileTinyEdgeColorMass
  split
  · calc
      (n : ℝ) * (s * proposal e c) ≤
          (n : ℝ) * (s * (C0 / (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        exact mul_le_mul_of_nonneg_left (hproposal e c) hs
      _ = s * C0 := by
        field_simp [Nat.ne_of_gt hn]
  · simpa using mul_nonneg hs hC0

end ProposalDependentUses

section StateRatioBound

variable {proposal : G.E → Color → ℝ}
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

theorem one_le_stateRatio_mul_smoothedColorDependentProbability
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    1 ≤ ((extendedProfileStateBound β q r : ℝ) / omega) *
      G.smoothedColorDependentExtendedProfileProbability R omega v c z := by
  have hbase := G.colorDependentExtendedProfileProbability_nonneg R
    hs hq hr0 hleft v c z
  have hcardPos : 0 < (Fintype.card
      (G.ColorDependentExtendedProfileState R v c) : ℝ) := by positivity
  have hboundPos : 0 < (extendedProfileStateBound β q r : ℝ) := by
    unfold extendedProfileStateBound profileStateBound
    positivity
  have hcard : (Fintype.card
      (G.ColorDependentExtendedProfileState R v c) : ℝ) ≤
      extendedProfileStateBound β q r := by
    exact_mod_cast G.colorDependentExtendedProfileState_card_le R v c
  have hrecip : omega / extendedProfileStateBound β q r ≤
      omega / Fintype.card
        (G.ColorDependentExtendedProfileState R v c) := by
    exact div_le_div_of_nonneg_left homega0.le hcardPos hcard
  have hlower : omega / extendedProfileStateBound β q r ≤
      G.smoothedColorDependentExtendedProfileProbability R omega v c z := by
    unfold smoothedColorDependentExtendedProfileProbability
    exact hrecip.trans (le_add_of_nonneg_left
      (mul_nonneg (sub_nonneg.mpr homega1) hbase))
  have hM : 0 < (extendedProfileStateBound β q r : ℝ) := by
    unfold extendedProfileStateBound profileStateBound
    positivity
  have hratio : 0 < (extendedProfileStateBound β q r : ℝ) / omega :=
    div_pos hM homega0
  calc
    (1 : ℝ) = ((extendedProfileStateBound β q r : ℝ) / omega) *
        (omega / extendedProfileStateBound β q r) := by
          field_simp
    _ ≤ ((extendedProfileStateBound β q r : ℝ) / omega) *
        G.smoothedColorDependentExtendedProfileProbability R omega v c z :=
      mul_le_mul_of_nonneg_left hlower hratio.le

end StateRatioBound

/-- Elementary two-endpoint estimate behind the unit envelope. -/
private theorem colorDependent_scaled_sum_pair_le
    {I : Type*} [Fintype I]
    (N rho y lambdaP lambdaQ L cap a : ℝ) (b : I → ℝ)
    (hN0 : 0 ≤ N) (hrho0 : 0 ≤ rho) (hy0 : 0 ≤ y)
    (hlambdaP : 0 < lambdaP) (hlambdaQ : 0 < lambdaQ)
    (hL0 : 0 ≤ L) (hcap0 : 0 ≤ cap)
    (hLP : 1 ≤ L * lambdaP) (hLQ : 1 ≤ L * lambdaQ)
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
      _ = (rho / y) * (a / lambdaP) * ((∑ i, b i) / lambdaQ) := by
        rw [Finset.sum_div, Finset.mul_sum]
  rw [hrewrite]
  have hrhoDiv0 : 0 ≤ rho / y := div_nonneg hrho0 hypos.le
  have haDiv0 : 0 ≤ a / lambdaP := div_nonneg ha0 hlambdaP.le
  have hbDiv0 : 0 ≤ (∑ i, b i) / lambdaQ :=
    div_nonneg hbsum0 hlambdaQ.le
  calc
    N * ((rho / y) * (a / lambdaP) * ((∑ i, b i) / lambdaQ)) ≤
        N * ((rho / y) * (y * L) * (y * L)) := by
      gcongr
    _ = rho * (N * y) * L ^ 2 := by field_simp [hy]
    _ ≤ rho * cap * L ^ 2 := by
      gcongr

section ProposalDependentBounds

variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- After multiplying by `n`, one oriented large-edge contribution is
bounded by the fixed diffuse-proposal normalization. -/
theorem n_mul_colorDependentLargeCandidateEdgeUse_le_scale
    {n : ℕ} (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (e : G.E) (row : G.ColorDependentLargeCandidateRow R c) :
    (n : ℝ) * G.colorDependentLargeCandidateEdgeUse
        proposal R rho omega source c sourceState e row ≤
      colorDependentCandidateCapacityScale rho s omega β q r C0 := by
  let L : ℝ := (extendedProfileStateBound β q r : ℝ) / omega
  unfold colorDependentLargeCandidateEdgeUse
  split
  · rename_i hmatch
    let P : G.ColorDependentExtendedProfileState R (G.fst e) c :=
      hmatch.1 ▸ row.candidate
    let Q : G.ColorDependentExtendedProfileState R (G.snd e) c :=
      hmatch.2 ▸ sourceState
    let y := G.colorDependentExtendedProfileLargeEdgeColorMass
      (s := s) (β := β) proposal e c
    have hy0 := G.colorDependentExtendedProfileLargeEdgeColorMass_nonneg
      proposal R e c
    have hP0 := G.colorDependentExtendedProfileLargeAssign_nonneg R
      (G.fst e) c (G.fstStarEdge e) P row.slot
    have hP := G.colorDependentExtendedProfileLargeAssign_le_edgeColorMass
      proposal R (G.fst e) c (G.fstStarEdge e) P row.slot
    have hQ0 : ∀ j, 0 ≤ G.colorDependentExtendedProfileLargeAssign R
        (G.snd e) c (G.sndStarEdge e) Q j := fun j ↦
      G.colorDependentExtendedProfileLargeAssign_nonneg R _ c _ Q j
    have hQ := G.sum_colorDependentExtendedProfileLargeAssign_le_edgeColorMass
      proposal R (G.snd e) c (G.sndStarEdge e) Q
    have hlamP := G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.fst e) c P
    have hlamQ := G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 (G.snd e) c Q
    have hLP := G.one_le_stateRatio_mul_smoothedColorDependentProbability R
      hs hq hr0 hleft homega0 homega1 (G.fst e) c P
    have hLQ := G.one_le_stateRatio_mul_smoothedColorDependentProbability R
      hs hq hr0 hleft homega0 homega1 (G.snd e) c Q
    have hpair := colorDependent_scaled_sum_pair_le
      (I := Fin (explicitLargeSlotBound β q r))
      (n : ℝ) rho y
      (G.smoothedColorDependentExtendedProfileProbability
        R omega (G.fst e) c P)
      (G.smoothedColorDependentExtendedProfileProbability
        R omega (G.snd e) c Q)
      L (s * C0)
      (G.colorDependentExtendedProfileLargeAssign R
        (G.fst e) c (G.fstStarEdge e) P row.slot)
      (fun j ↦ G.colorDependentExtendedProfileLargeAssign R
        (G.snd e) c (G.sndStarEdge e) Q j)
      (Nat.cast_nonneg n) hrho hy0 hlamP hlamQ (by positivity)
      (mul_nonneg hs hC0) hLP hLQ hP0 hP hQ0 hQ
      (G.n_mul_colorDependentLargeEdgeColorMass_le proposal R
        hn hs hC0 hproposal e c)
    by_cases hy : y = 0 <;>
      simpa [colorDependentExtendedProfileLargeProductMass, pairedOption,
        P, Q, y, L, colorDependentCandidateCapacityScale, hy,
        mul_assoc] using hpair
  · split
    · rename_i hmatch
      let P : G.ColorDependentExtendedProfileState R (G.fst e) c :=
        hmatch.2 ▸ sourceState
      let Q : G.ColorDependentExtendedProfileState R (G.snd e) c :=
        hmatch.1 ▸ row.candidate
      let y := G.colorDependentExtendedProfileLargeEdgeColorMass
        (s := s) (β := β) proposal e c
      have hy0 := G.colorDependentExtendedProfileLargeEdgeColorMass_nonneg
        proposal R e c
      have hQ0 := G.colorDependentExtendedProfileLargeAssign_nonneg R
        (G.snd e) c (G.sndStarEdge e) Q row.slot
      have hQ := G.colorDependentExtendedProfileLargeAssign_le_edgeColorMass
        proposal R (G.snd e) c (G.sndStarEdge e) Q row.slot
      have hP0 : ∀ i, 0 ≤ G.colorDependentExtendedProfileLargeAssign R
          (G.fst e) c (G.fstStarEdge e) P i := fun i ↦
        G.colorDependentExtendedProfileLargeAssign_nonneg R _ c _ P i
      have hP := G.sum_colorDependentExtendedProfileLargeAssign_le_edgeColorMass
        proposal R (G.fst e) c (G.fstStarEdge e) P
      have hlamQ := G.smoothedColorDependentExtendedProfileProbability_pos R
        hs hq hr0 hleft homega0 homega1 (G.snd e) c Q
      have hlamP := G.smoothedColorDependentExtendedProfileProbability_pos R
        hs hq hr0 hleft homega0 homega1 (G.fst e) c P
      have hLQ := G.one_le_stateRatio_mul_smoothedColorDependentProbability R
        hs hq hr0 hleft homega0 homega1 (G.snd e) c Q
      have hLP := G.one_le_stateRatio_mul_smoothedColorDependentProbability R
        hs hq hr0 hleft homega0 homega1 (G.fst e) c P
      have hpair := colorDependent_scaled_sum_pair_le
        (I := Fin (explicitLargeSlotBound β q r))
        (n : ℝ) rho y
        (G.smoothedColorDependentExtendedProfileProbability
          R omega (G.snd e) c Q)
        (G.smoothedColorDependentExtendedProfileProbability
          R omega (G.fst e) c P)
        L (s * C0)
        (G.colorDependentExtendedProfileLargeAssign R
          (G.snd e) c (G.sndStarEdge e) Q row.slot)
        (fun i ↦ G.colorDependentExtendedProfileLargeAssign R
          (G.fst e) c (G.fstStarEdge e) P i)
        (Nat.cast_nonneg n) hrho hy0 hlamQ hlamP (by positivity)
        (mul_nonneg hs hC0) hLQ hLP hQ0 hQ hP0 hP
        (G.n_mul_colorDependentLargeEdgeColorMass_le proposal R
          hn hs hC0 hproposal e c)
      by_cases hy : y = 0 <;>
        convert hpair using 1 <;>
          simp [colorDependentExtendedProfileLargeProductMass, pairedOption,
            P, Q, y, L, colorDependentCandidateCapacityScale, hy,
            Nat.ne_of_gt hn, mul_assoc] <;>
          first
          | (apply Finset.sum_congr rfl
             intro x _hx
             ring)
          | ring
    · simpa using colorDependentCandidateCapacityScale_nonneg
        (C0 := C0) hrho hs hC0 homega0.le

/-- Tiny analogue of the oriented diffuse envelope. -/
theorem n_mul_colorDependentTinyCandidateEdgeUse_le_weight_mul_scale
    {n : ℕ} (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (e : G.E) (row : G.ColorDependentTinyCandidateRow R c) :
    (n : ℝ) * G.colorDependentTinyCandidateEdgeUse
        proposal R rho omega source c sourceState e row ≤
      G.weight e *
        colorDependentCandidateCapacityScale rho s omega β q r C0 := by
  let L : ℝ := (extendedProfileStateBound β q r : ℝ) / omega
  let scale := colorDependentCandidateCapacityScale rho s omega β q r C0
  have hscale0 : 0 ≤ scale :=
    colorDependentCandidateCapacityScale_nonneg
      (C0 := C0) hrho hs hC0 homega0.le
  unfold colorDependentTinyCandidateEdgeUse
  split
  · rename_i hmatch
    let P : G.ColorDependentExtendedProfileState R (G.fst e) c :=
      hmatch.1 ▸ row.candidate
    let Q : G.ColorDependentExtendedProfileState R (G.snd e) c :=
      hmatch.2 ▸ sourceState
    let y := G.colorDependentExtendedProfileTinyEdgeColorMass
      (s := s) (β := β) proposal e c
    have hpair := colorDependent_scaled_sum_pair_le (I := Fin 1)
      (n : ℝ) rho y
      (G.smoothedColorDependentExtendedProfileProbability
        R omega (G.fst e) c P)
      (G.smoothedColorDependentExtendedProfileProbability
        R omega (G.snd e) c Q)
      L (s * C0)
      (G.colorDependentExtendedProfileTinyAssign R
        (G.fst e) c (G.fstStarEdge e) P)
      (fun _ ↦ G.colorDependentExtendedProfileTinyAssign R
        (G.snd e) c (G.sndStarEdge e) Q)
      (Nat.cast_nonneg n) hrho
      (G.colorDependentExtendedProfileTinyEdgeColorMass_nonneg proposal R e c)
      (G.smoothedColorDependentExtendedProfileProbability_pos R
        hs hq hr0 hleft homega0 homega1 (G.fst e) c P)
      (G.smoothedColorDependentExtendedProfileProbability_pos R
        hs hq hr0 hleft homega0 homega1 (G.snd e) c Q)
      (by positivity) (mul_nonneg hs hC0)
      (G.one_le_stateRatio_mul_smoothedColorDependentProbability R
        hs hq hr0 hleft homega0 homega1 (G.fst e) c P)
      (G.one_le_stateRatio_mul_smoothedColorDependentProbability R
        hs hq hr0 hleft homega0 homega1 (G.snd e) c Q)
      (G.colorDependentExtendedProfileTinyAssign_nonneg R
        (G.fst e) c (G.fstStarEdge e) P)
      (G.colorDependentExtendedProfileTinyAssign_le_edgeColorMass
        proposal R (G.fst e) c (G.fstStarEdge e) P)
      (fun _ ↦ G.colorDependentExtendedProfileTinyAssign_nonneg R
        (G.snd e) c (G.sndStarEdge e) Q)
      (by
        simpa using
          (G.colorDependentExtendedProfileTinyAssign_le_edgeColorMass
            proposal R (G.snd e) c (G.sndStarEdge e) Q))
      (G.n_mul_colorDependentTinyEdgeColorMass_le proposal R
        hn hs hC0 hproposal e c)
    have hproduct : (n : ℝ) *
        G.colorDependentExtendedProfileTinyProductMass
          proposal R rho omega e c P Q ≤ scale := by
      by_cases hy : y = 0 <;>
        simpa [colorDependentExtendedProfileTinyProductMass, pairedOption,
          P, Q, y, L, scale, colorDependentCandidateCapacityScale, hy,
          mul_assoc] using hpair
    calc
      (n : ℝ) * (G.weight e *
          G.colorDependentExtendedProfileTinyProductMass
            proposal R rho omega e c P Q) =
          G.weight e * ((n : ℝ) *
            G.colorDependentExtendedProfileTinyProductMass
              proposal R rho omega e c P Q) := by ring
      _ ≤ G.weight e * scale :=
        mul_le_mul_of_nonneg_left hproduct (G.weight_nonneg e)
  · split
    · rename_i hmatch
      let P : G.ColorDependentExtendedProfileState R (G.fst e) c :=
        hmatch.2 ▸ sourceState
      let Q : G.ColorDependentExtendedProfileState R (G.snd e) c :=
        hmatch.1 ▸ row.candidate
      let y := G.colorDependentExtendedProfileTinyEdgeColorMass
        (s := s) (β := β) proposal e c
      have hpair := colorDependent_scaled_sum_pair_le (I := Fin 1)
        (n : ℝ) rho y
        (G.smoothedColorDependentExtendedProfileProbability
          R omega (G.snd e) c Q)
        (G.smoothedColorDependentExtendedProfileProbability
          R omega (G.fst e) c P)
        L (s * C0)
        (G.colorDependentExtendedProfileTinyAssign R
          (G.snd e) c (G.sndStarEdge e) Q)
        (fun _ ↦ G.colorDependentExtendedProfileTinyAssign R
          (G.fst e) c (G.fstStarEdge e) P)
        (Nat.cast_nonneg n) hrho
        (G.colorDependentExtendedProfileTinyEdgeColorMass_nonneg proposal R e c)
        (G.smoothedColorDependentExtendedProfileProbability_pos R
          hs hq hr0 hleft homega0 homega1 (G.snd e) c Q)
        (G.smoothedColorDependentExtendedProfileProbability_pos R
          hs hq hr0 hleft homega0 homega1 (G.fst e) c P)
        (by positivity) (mul_nonneg hs hC0)
        (G.one_le_stateRatio_mul_smoothedColorDependentProbability R
          hs hq hr0 hleft homega0 homega1 (G.snd e) c Q)
        (G.one_le_stateRatio_mul_smoothedColorDependentProbability R
          hs hq hr0 hleft homega0 homega1 (G.fst e) c P)
        (G.colorDependentExtendedProfileTinyAssign_nonneg R
          (G.snd e) c (G.sndStarEdge e) Q)
        (G.colorDependentExtendedProfileTinyAssign_le_edgeColorMass
          proposal R (G.snd e) c (G.sndStarEdge e) Q)
        (fun _ ↦ G.colorDependentExtendedProfileTinyAssign_nonneg R
          (G.fst e) c (G.fstStarEdge e) P)
        (by
          simpa using
            (G.colorDependentExtendedProfileTinyAssign_le_edgeColorMass
              proposal R (G.fst e) c (G.fstStarEdge e) P))
        (G.n_mul_colorDependentTinyEdgeColorMass_le proposal R
          hn hs hC0 hproposal e c)
      have hproduct : (n : ℝ) *
          G.colorDependentExtendedProfileTinyProductMass
            proposal R rho omega e c P Q ≤ scale := by
        by_cases hy : y = 0 <;>
          convert hpair using 1 <;>
            simp [colorDependentExtendedProfileTinyProductMass, pairedOption,
              P, Q, y, L, scale, colorDependentCandidateCapacityScale, hy,
              Nat.ne_of_gt hn, mul_assoc] <;> ring
      calc
        (n : ℝ) * (G.weight e *
            G.colorDependentExtendedProfileTinyProductMass
              proposal R rho omega e c P Q) =
            G.weight e * ((n : ℝ) *
              G.colorDependentExtendedProfileTinyProductMass
                proposal R rho omega e c P Q) := by ring
        _ ≤ G.weight e * scale :=
          mul_le_mul_of_nonneg_left hproduct (G.weight_nonneg e)
    · simpa using mul_nonneg (G.weight_nonneg e) hscale0

theorem n_mul_colorDependentTinyCandidateEdgeUse_le_scale
    {n : ℕ} (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (e : G.E) (row : G.ColorDependentTinyCandidateRow R c) :
    (n : ℝ) * G.colorDependentTinyCandidateEdgeUse
        proposal R rho omega source c sourceState e row ≤
      colorDependentCandidateCapacityScale rho s omega β q r C0 := by
  exact (G.n_mul_colorDependentTinyCandidateEdgeUse_le_weight_mul_scale
    proposal R hn hs hq hr0 hleft homega0 homega1 hrho hC0 hproposal
      source c sourceState e row).trans
    (mul_le_of_le_one_left
      (colorDependentCandidateCapacityScale_nonneg
        (C0 := C0) hrho hs hC0 homega0.le)
      (G.weight_le_one e))

def ColorDependentCandidateEdgeMatches
    (center source : G.V) (e : G.E) : Prop :=
  (center = G.fst e ∧ source = G.snd e) ∨
    (center = G.snd e ∧ source = G.fst e)

theorem colorDependentCandidateEdgeMatches_unique
    {center source : G.V} {e f : G.E}
    (he : G.ColorDependentCandidateEdgeMatches center source e)
    (hf : G.ColorDependentCandidateEdgeMatches center source f) : e = f := by
  rcases he with he | he <;> rcases hf with hf | hf
  · exact G.endpoints_injective ((Sym2.eq_iff).2 (Or.inl
      ⟨he.1.symm.trans hf.1, he.2.symm.trans hf.2⟩))
  · exact G.endpoints_injective ((Sym2.eq_iff).2 (Or.inr
      ⟨he.1.symm.trans hf.1, he.2.symm.trans hf.2⟩))
  · exact G.endpoints_injective ((Sym2.eq_iff).2 (Or.inr
      ⟨he.2.symm.trans hf.2, he.1.symm.trans hf.1⟩))
  · exact G.endpoints_injective ((Sym2.eq_iff).2 (Or.inl
      ⟨he.2.symm.trans hf.2, he.1.symm.trans hf.1⟩))

private theorem colorDependentLargeCandidateEdgeUse_eq_zero_of_not_matches
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (e : G.E) (row : G.ColorDependentLargeCandidateRow R c)
    (h : ¬G.ColorDependentCandidateEdgeMatches row.center source e) :
    G.colorDependentLargeCandidateEdgeUse proposal R rho omega
      source c sourceState e row = 0 := by
  unfold ColorDependentCandidateEdgeMatches at h
  simp only [not_or] at h
  simp [colorDependentLargeCandidateEdgeUse, h.1, h.2]

private theorem colorDependentTinyCandidateEdgeUse_eq_zero_of_not_matches
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (e : G.E) (row : G.ColorDependentTinyCandidateRow R c)
    (h : ¬G.ColorDependentCandidateEdgeMatches row.center source e) :
    G.colorDependentTinyCandidateEdgeUse proposal R rho omega
      source c sourceState e row = 0 := by
  unfold ColorDependentCandidateEdgeMatches at h
  simp only [not_or] at h
  simp [colorDependentTinyCandidateEdgeUse, h.1, h.2]

/-- Simplicity turns the oriented edge envelopes into a unit envelope for
the complete normalized source--row coefficient. -/
theorem scaledColorDependentCandidateAtomUse_le_one
    {n : ℕ} (hn : 0 < n) (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (row : G.ColorDependentCandidateRowAt R c) :
    G.scaledColorDependentCandidateAtomUse proposal R n
      (colorDependentCandidateCapacityScale rho s omega β q r C0)
      rho omega source c sourceState row ≤ 1 := by
  classical
  let scale := colorDependentCandidateCapacityScale rho s omega β q r C0
  have hscale : 0 < scale :=
    colorDependentCandidateCapacityScale_pos
      (C0 := C0) hrho hs hC0 homega0
  apply (div_le_one hscale).2
  rcases row with large | tiny
  · unfold colorDependentCandidateAtomUse
    by_cases hex : ∃ e,
        G.ColorDependentCandidateEdgeMatches large.center source e
    · obtain ⟨e, he⟩ := hex
      calc
        (n : ℝ) *
            ∑ f, G.colorDependentLargeCandidateEdgeUse proposal R rho omega
              source c sourceState f large =
            (n : ℝ) * G.colorDependentLargeCandidateEdgeUse
              proposal R rho omega source c sourceState e large := by
          congr 1
          apply Finset.sum_eq_single e
          · intro f _hf hfe
            apply G.colorDependentLargeCandidateEdgeUse_eq_zero_of_not_matches
              proposal R
            intro hfmatch
            exact hfe (G.colorDependentCandidateEdgeMatches_unique hfmatch he)
          · simp
        _ ≤ scale := G.n_mul_colorDependentLargeCandidateEdgeUse_le_scale
          proposal R hn hs.le hq hr0 hleft homega0 homega1 hrho.le hC0.le
            hproposal source c sourceState e large
    · have hzero : (∑ e,
          G.colorDependentLargeCandidateEdgeUse proposal R rho omega
            source c sourceState e large) = 0 := by
        apply Finset.sum_eq_zero
        intro e _he
        exact G.colorDependentLargeCandidateEdgeUse_eq_zero_of_not_matches
          proposal R rho omega source c sourceState e large
            (fun h ↦ hex ⟨e, h⟩)
      simp [hzero, hscale.le]

  · unfold colorDependentCandidateAtomUse
    by_cases hex : ∃ e,
        G.ColorDependentCandidateEdgeMatches tiny.center source e
    · obtain ⟨e, he⟩ := hex
      calc
        (n : ℝ) *
            ∑ f, G.colorDependentTinyCandidateEdgeUse proposal R rho omega
              source c sourceState f tiny =
            (n : ℝ) * G.colorDependentTinyCandidateEdgeUse
              proposal R rho omega source c sourceState e tiny := by
          congr 1
          apply Finset.sum_eq_single e
          · intro f _hf hfe
            apply G.colorDependentTinyCandidateEdgeUse_eq_zero_of_not_matches
              proposal R
            intro hfmatch
            exact hfe (G.colorDependentCandidateEdgeMatches_unique hfmatch he)
          · simp
        _ ≤ scale := G.n_mul_colorDependentTinyCandidateEdgeUse_le_scale
          proposal R hn hs.le hq hr0 hleft homega0 homega1 hrho.le hC0.le
            hproposal source c sourceState e tiny
    · have hzero : (∑ e,
          G.colorDependentTinyCandidateEdgeUse proposal R rho omega
            source c sourceState e tiny) = 0 := by
        apply Finset.sum_eq_zero
        intro e _he
        exact G.colorDependentTinyCandidateEdgeUse_eq_zero_of_not_matches
          proposal R rho omega source c sourceState e tiny
            (fun h ↦ hex ⟨e, h⟩)
      simp [hzero, hscale.le]

theorem colorDependentCandidateAtomUse_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (row : G.ColorDependentCandidateRowAt R c) :
    0 ≤ G.colorDependentCandidateAtomUse
      proposal R rho omega source c sourceState row := by
  rcases row with large | tiny
  · unfold colorDependentCandidateAtomUse
    exact Finset.sum_nonneg fun e _he ↦ by
      unfold colorDependentLargeCandidateEdgeUse
      split
      · exact Finset.sum_nonneg fun j _hj ↦
          G.colorDependentExtendedProfileLargeProductMass_nonneg
            proposal R hs hq hr0 hleft homega0 homega1 hrho _ _ _ _ _ _
      · split
        · exact Finset.sum_nonneg fun i _hi ↦
            G.colorDependentExtendedProfileLargeProductMass_nonneg
              proposal R hs hq hr0 hleft homega0 homega1 hrho _ _ _ _ _ _
        · exact le_rfl
  · unfold colorDependentCandidateAtomUse
    exact Finset.sum_nonneg fun e _he ↦ by
      unfold colorDependentTinyCandidateEdgeUse
      split
      · exact mul_nonneg (G.weight_nonneg e)
          (G.colorDependentExtendedProfileTinyProductMass_nonneg
            proposal R hs hq hr0 hleft homega0 homega1 hrho _ _ _ _)
      · split
        · exact mul_nonneg (G.weight_nonneg e)
            (G.colorDependentExtendedProfileTinyProductMass_nonneg
              proposal R hs hq hr0 hleft homega0 homega1 hrho _ _ _ _)
        · exact le_rfl

theorem scaledColorDependentCandidateAtomUse_nonneg
    {n : ℕ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hscale : 0 ≤ scale)
    (source : G.V) (c : Color)
    (sourceState : G.ColorDependentExtendedProfileState R source c)
    (row : G.ColorDependentCandidateRowAt R c) :
    0 ≤ G.scaledColorDependentCandidateAtomUse
      proposal R n scale rho omega source c sourceState row := by
  unfold scaledColorDependentCandidateAtomUse
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg n)
      (G.colorDependentCandidateAtomUse_nonneg proposal R
        hs hq hr0 hleft homega0 homega1 hrho source c sourceState row))
    hscale

/-- Exact mean formula for a large candidate row.  Zero-mass edge--colors
vanish; every nonzero term is reduced by the one-endpoint coupling identity. -/
theorem colorDependentLargeCandidateAtomMean_eq
    (rho omega : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (c : Color)
    (row : G.ColorDependentLargeCandidateRow R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.colorDependentCandidateAtomUse proposal R rho omega source c z
            (Sum.inl row)) =
      rho /
          G.smoothedColorDependentExtendedProfileProbability
            R omega row.center c row.candidate *
        (∑ e : G.StarEdge row.center,
          G.colorDependentExtendedProfileLargeAssign
            R row.center c e row.candidate row.slot) := by
  classical
  rcases row with ⟨center, candidate, slot⟩
  have hstar :
      (∑ e : G.StarEdge center,
        G.colorDependentExtendedProfileLargeAssign
          R center c e candidate slot) =
      ∑ e : G.E, if h : G.Inc center e then
        G.colorDependentExtendedProfileLargeAssign
          R center c ⟨e, h⟩ candidate slot else 0 := by
    symm
    calc
      (∑ e : G.E, if h : G.Inc center e then
          G.colorDependentExtendedProfileLargeAssign
            R center c ⟨e, h⟩ candidate slot else 0) =
          ∑ e ∈ Finset.univ.filter (G.Inc center),
            if h : G.Inc center e then
              G.colorDependentExtendedProfileLargeAssign
                R center c ⟨e, h⟩ candidate slot else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _he
        by_cases hinc : G.Inc center e <;> simp [hinc]
      _ = ∑ e : G.StarEdge center,
          if h : G.Inc center e.1 then
            G.colorDependentExtendedProfileLargeAssign
              R center c ⟨e.1, h⟩ candidate slot else 0 := by
        exact Finset.sum_subtype (p := G.Inc center)
          (Finset.univ.filter (G.Inc center)) (by intro e; simp)
          (fun e ↦ if h : G.Inc center e then
            G.colorDependentExtendedProfileLargeAssign
              R center c ⟨e, h⟩ candidate slot else 0)
      _ = ∑ e : G.StarEdge center,
          G.colorDependentExtendedProfileLargeAssign
            R center c e candidate slot := by
        apply Finset.sum_congr rfl
        intro e _he
        simp [e.property]
  rw [hstar]
  unfold colorDependentCandidateAtomUse
  simp_rw [Finset.mul_sum]
  calc
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        ∑ e : G.E,
          G.smoothedColorDependentExtendedProfileProbability
              R omega source c z *
            G.colorDependentLargeCandidateEdgeUse
              proposal R rho omega source c z e ⟨center, candidate, slot⟩) =
      ∑ source : G.V, ∑ e : G.E,
        ∑ z : G.ColorDependentExtendedProfileState R source c,
          G.smoothedColorDependentExtendedProfileProbability
              R omega source c z *
            G.colorDependentLargeCandidateEdgeUse
              proposal R rho omega source c z e
                ⟨center, candidate, slot⟩ := by
        apply Finset.sum_congr rfl
        intro source _hsource
        rw [Finset.sum_comm]
    _ = ∑ e : G.E, ∑ source : G.V,
        ∑ z : G.ColorDependentExtendedProfileState R source c,
          G.smoothedColorDependentExtendedProfileProbability
              R omega source c z *
            G.colorDependentLargeCandidateEdgeUse
              proposal R rho omega source c z e
                ⟨center, candidate, slot⟩ := by
        rw [Finset.sum_comm]
    _ = ∑ e : G.E,
        rho /
            G.smoothedColorDependentExtendedProfileProbability
              R omega center c candidate *
          (if h : G.Inc center e then
            G.colorDependentExtendedProfileLargeAssign
              R center c ⟨e, h⟩ candidate slot else 0) := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hfst : center = G.fst e
      · subst center
        have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
        rw [Finset.sum_eq_single (G.snd e)]
        · simp only [colorDependentLargeCandidateEdgeUse]
          have htrue : True ∧ True := ⟨True.intro, True.intro⟩
          have hinc : G.Inc (G.fst e) e := Or.inl rfl
          have hstarEdge : (⟨e, hinc⟩ : G.StarEdge (G.fst e)) =
              G.fstStarEdge e := by
            apply Subtype.ext
            rfl
          simp_rw [dif_pos htrue]
          rw [dif_pos hinc]
          by_cases hy : G.colorDependentExtendedProfileLargeEdgeColorMass
              (s := s) (β := β) proposal e c = 0
          · have hle :=
                G.colorDependentExtendedProfileLargeAssign_le_edgeColorMass
                  proposal R (G.fst e) c (G.fstStarEdge e) candidate slot
            change G.colorDependentExtendedProfileLargeAssign R
                (G.fst e) c (G.fstStarEdge e) candidate slot ≤
              G.colorDependentExtendedProfileLargeEdgeColorMass
                (s := s) (β := β) proposal e c at hle
            have hassign0 :
                G.colorDependentExtendedProfileLargeAssign R
                    (G.fst e) c (G.fstStarEdge e)
                    candidate slot = 0 :=
              le_antisymm
                (by simpa only [hy] using hle)
                (G.colorDependentExtendedProfileLargeAssign_nonneg R
                  (G.fst e) c (G.fstStarEdge e) candidate slot)
            simp [colorDependentExtendedProfileLargeProductMass,
              pairedOption, hy, hstarEdge, hassign0]
          · rw [G.colorDependentLargeProductMass_right_expectation
              proposal R hs hq hr0 hleft homega0 homega1 hy
              candidate slot]
            simp [hstarEdge, mul_div_assoc', mul_comm, mul_left_comm]
        · intro source _hsource hsource
          have hsndSource : source ≠ G.snd e := hsource
          have hnotMatch : ¬G.ColorDependentCandidateEdgeMatches
              (G.fst e) source e := by
            intro h
            rcases h with h | h
            · exact hsndSource h.2
            · exact hne h.1.symm
          have hedge0 : ∀ z : G.ColorDependentExtendedProfileState R source c,
              G.colorDependentLargeCandidateEdgeUse proposal R rho omega
                source c z e ⟨G.fst e, candidate, slot⟩ = 0 := fun z ↦
            G.colorDependentLargeCandidateEdgeUse_eq_zero_of_not_matches
              proposal R rho omega source c z e
                ⟨G.fst e, candidate, slot⟩ hnotMatch
          simp only [hedge0, mul_zero, Finset.sum_const_zero]
        · simp
      · by_cases hsnd : center = G.snd e
        · subst center
          rw [Finset.sum_eq_single (G.fst e)]
          · have hnot1 : ¬(G.snd e = G.fst e ∧ G.fst e = G.snd e) :=
              fun h ↦ hfst h.1
            simp only [colorDependentLargeCandidateEdgeUse]
            have htrue : True ∧ True := ⟨True.intro, True.intro⟩
            have hinc : G.Inc (G.snd e) e := Or.inr rfl
            have hstarEdge : (⟨e, hinc⟩ : G.StarEdge (G.snd e)) =
                G.sndStarEdge e := by
              apply Subtype.ext
              rfl
            simp_rw [dif_neg hnot1, dif_pos htrue]
            rw [dif_pos hinc]
            by_cases hy : G.colorDependentExtendedProfileLargeEdgeColorMass
                (s := s) (β := β) proposal e c = 0
            · have hle :=
                  G.colorDependentExtendedProfileLargeAssign_le_edgeColorMass
                    proposal R (G.snd e) c (G.sndStarEdge e) candidate slot
              change G.colorDependentExtendedProfileLargeAssign R
                  (G.snd e) c (G.sndStarEdge e) candidate slot ≤
                G.colorDependentExtendedProfileLargeEdgeColorMass
                  (s := s) (β := β) proposal e c at hle
              have hassign0 :
                  G.colorDependentExtendedProfileLargeAssign R
                      (G.snd e) c (G.sndStarEdge e)
                      candidate slot = 0 :=
                le_antisymm
                  (by simpa only [hy] using hle)
                  (G.colorDependentExtendedProfileLargeAssign_nonneg R
                    (G.snd e) c (G.sndStarEdge e) candidate slot)
              simp [colorDependentExtendedProfileLargeProductMass,
                pairedOption, hy, hstarEdge, hassign0]
            · rw [G.colorDependentLargeProductMass_left_expectation
                proposal R hs hq hr0 hleft homega0 homega1 hy
                candidate slot]
              simp [hstarEdge, mul_div_assoc', mul_comm, mul_left_comm]
          · intro source _hsource hsource
            have hfstSource : source ≠ G.fst e := hsource
            have hnotMatch : ¬G.ColorDependentCandidateEdgeMatches
                (G.snd e) source e := by
              intro h
              rcases h with h | h
              · exact hfst h.1
              · exact hfstSource h.2
            have hedge0 : ∀ z : G.ColorDependentExtendedProfileState R source c,
                G.colorDependentLargeCandidateEdgeUse proposal R rho omega
                  source c z e ⟨G.snd e, candidate, slot⟩ = 0 := fun z ↦
              G.colorDependentLargeCandidateEdgeUse_eq_zero_of_not_matches
                proposal R rho omega source c z e
                  ⟨G.snd e, candidate, slot⟩ hnotMatch
            simp only [hedge0, mul_zero, Finset.sum_const_zero]
          · simp
        · have hnot1 : ∀ source,
              ¬(center = G.fst e ∧ source = G.snd e) :=
            fun _ h ↦ hfst h.1
          have hnot2 : ∀ source,
              ¬(center = G.snd e ∧ source = G.fst e) :=
            fun _ h ↦ hsnd h.1
          have hnotInc : ¬G.Inc center e := by
            intro hinc
            rcases hinc with hinc | hinc
            · exact hfst hinc.symm
            · exact hsnd hinc.symm
          have hnotMatch : ∀ source,
              ¬G.ColorDependentCandidateEdgeMatches center source e := by
            intro source h
            rcases h with h | h
            · exact hfst h.1
            · exact hsnd h.1
          have hedge0 : ∀ source
              (z : G.ColorDependentExtendedProfileState R source c),
              G.colorDependentLargeCandidateEdgeUse proposal R rho omega
                source c z e ⟨center, candidate, slot⟩ = 0 := fun source z ↦
            G.colorDependentLargeCandidateEdgeUse_eq_zero_of_not_matches
              proposal R rho omega source c z e
                ⟨center, candidate, slot⟩ (hnotMatch source)
          rw [dif_neg hnotInc]
          simp only [hedge0, mul_zero, Finset.sum_const_zero]

end ProposalDependentBounds

section StateProbabilityBounds

variable {proposal : G.E → Color → ℝ}
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

theorem colorDependentExtendedProfileProbability_le_one
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    G.colorDependentExtendedProfileProbability R v c z ≤ 1 := by
  have hsingle :
      G.colorDependentExtendedProfileProbability R v c z ≤
        ∑ y : G.ColorDependentExtendedProfileState R v c,
          G.colorDependentExtendedProfileProbability R v c y :=
    Finset.single_le_sum
      (fun y _hy ↦ G.colorDependentExtendedProfileProbability_nonneg R
        hs hq hr0 hleft v c y) (Finset.mem_univ z)
  simpa [G.sum_colorDependentExtendedProfileProbability R v c] using hsingle

theorem omega_div_stateBound_le_smoothedColorDependentProbability
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    omega / extendedProfileStateBound β q r ≤
      G.smoothedColorDependentExtendedProfileProbability R omega v c z := by
  have hbase := G.colorDependentExtendedProfileProbability_nonneg R
    hs hq hr0 hleft v c z
  have hfirst : 0 ≤
      (1 - omega) * G.colorDependentExtendedProfileProbability R v c z :=
    mul_nonneg (sub_nonneg.mpr homega1) hbase
  have hcardPos : 0 < (Fintype.card
      (G.ColorDependentExtendedProfileState R v c) : ℝ) := by positivity
  have hboundPos : 0 < (extendedProfileStateBound β q r : ℝ) := by
    unfold extendedProfileStateBound profileStateBound
    positivity
  have hcard : (Fintype.card
      (G.ColorDependentExtendedProfileState R v c) : ℝ) ≤
      extendedProfileStateBound β q r := by
    exact_mod_cast G.colorDependentExtendedProfileState_card_le R v c
  have hrecip : omega / extendedProfileStateBound β q r ≤
      omega / Fintype.card
        (G.ColorDependentExtendedProfileState R v c) := by
    exact div_le_div_of_nonneg_left homega0.le hcardPos hcard
  unfold smoothedColorDependentExtendedProfileProbability
  linarith

theorem one_sub_omega_mul_colorDependentProbability_le_smoothed
    (homega0 : 0 ≤ omega) (v : G.V) (c : Color)
    (z : G.ColorDependentExtendedProfileState R v c) :
    (1 - omega) * G.colorDependentExtendedProfileProbability R v c z ≤
      G.smoothedColorDependentExtendedProfileProbability R omega v c z := by
  unfold smoothedColorDependentExtendedProfileProbability
  exact le_add_of_nonneg_right (div_nonneg homega0 (Nat.cast_nonneg _))

end StateProbabilityBounds

section CandidateMeanBounds

variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- Sharp common large-row mean bound from the unsmoothed mass in the
numerator. -/
theorem colorDependentLargeCandidateAtomMean_le_one_sub_omega
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (c : Color)
    (row : G.ColorDependentLargeCandidateRow R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.colorDependentCandidateAtomUse proposal R rho omega source c z
            (Sum.inl row)) ≤ rho / (1 - omega) := by
  rw [G.colorDependentLargeCandidateAtomMean_eq proposal R rho omega
    hs hq hr0 hleft homega0 homega1.le c row]
  let A := ∑ e : G.StarEdge row.center,
    G.colorDependentExtendedProfileLargeAssign
      R row.center c e row.candidate row.slot
  let p := G.colorDependentExtendedProfileProbability
    R row.center c row.candidate
  let lam := G.smoothedColorDependentExtendedProfileProbability
    R omega row.center c row.candidate
  have hA : A ≤ p :=
    G.sum_colorDependentExtendedProfileLargeAssign_star_le R
      hs hq hr0 hleft row.center c row.candidate row.slot
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun e _he ↦
    G.colorDependentExtendedProfileLargeAssign_nonneg
      R row.center c e row.candidate row.slot
  have hlam : 0 < lam :=
    G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1.le row.center c row.candidate
  have hone : 0 < 1 - omega := sub_pos.mpr homega1
  have hbase : (1 - omega) * p ≤ lam :=
    G.one_sub_omega_mul_colorDependentProbability_le_smoothed R
      homega0.le row.center c row.candidate
  have hratio : A / lam ≤ 1 / (1 - omega) := by
    apply (div_le_div_iff₀ hlam hone).2
    calc
      A * (1 - omega) ≤ p * (1 - omega) :=
        mul_le_mul_of_nonneg_right hA hone.le
      _ = (1 - omega) * p := by ring
      _ ≤ lam := hbase
      _ = 1 * lam := by ring
  calc
    rho / lam * A = rho * (A / lam) := by ring
    _ ≤ rho * (1 / (1 - omega)) :=
      mul_le_mul_of_nonneg_left hratio hrho
    _ = rho / (1 - omega) := by ring

/-- Uniform large-row mean bound.  It depends only on the common state
bound and smoothing parameter, not on the graph or proposal coefficients. -/
theorem colorDependentLargeCandidateAtomMean_le_uniform
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (c : Color)
    (row : G.ColorDependentLargeCandidateRow R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.colorDependentCandidateAtomUse proposal R rho omega source c z
            (Sum.inl row)) ≤
      rho * extendedProfileStateBound β q r / omega := by
  rw [G.colorDependentLargeCandidateAtomMean_eq proposal R rho omega
    hs hq hr0 hleft homega0 homega1 c row]
  let lam := G.smoothedColorDependentExtendedProfileProbability
    R omega row.center c row.candidate
  let A := ∑ e : G.StarEdge row.center,
    G.colorDependentExtendedProfileLargeAssign
      R row.center c e row.candidate row.slot
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun e _he ↦
    G.colorDependentExtendedProfileLargeAssign_nonneg
      R row.center c e row.candidate row.slot
  have hAprob : A ≤
      G.colorDependentExtendedProfileProbability
        R row.center c row.candidate :=
    G.sum_colorDependentExtendedProfileLargeAssign_star_le R
      hs hq hr0 hleft row.center c row.candidate row.slot
  have hprob1 := G.colorDependentExtendedProfileProbability_le_one R
    hs hq hr0 hleft row.center c row.candidate
  have hA1 : A ≤ 1 := hAprob.trans hprob1
  have hlam : omega / extendedProfileStateBound β q r ≤ lam :=
    G.omega_div_stateBound_le_smoothedColorDependentProbability R
      hs hq hr0 hleft homega0 homega1 row.center c row.candidate
  have hlam0 : 0 < lam :=
    G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 row.center c row.candidate
  have hM0 : 0 < (extendedProfileStateBound β q r : ℝ) := by
    unfold extendedProfileStateBound profileStateBound
    positivity
  have homegaM : 0 < omega / extendedProfileStateBound β q r :=
    div_pos homega0 hM0
  have hratio : rho / lam ≤
      rho / (omega / extendedProfileStateBound β q r) :=
    div_le_div_of_nonneg_left hrho homegaM hlam
  have hmul : rho / lam * A ≤
      (rho / (omega / extendedProfileStateBound β q r)) * 1 :=
    mul_le_mul hratio hA1 hA0
      (div_nonneg hrho homegaM.le)
  calc
    rho / lam * A ≤
        (rho / (omega / extendedProfileStateBound β q r)) * 1 := hmul
    _ = rho * extendedProfileStateBound β q r / omega := by
      field_simp

/-- Exact mean formula for a tiny candidate row.  The edge weight is part of
the row coefficient, so the resulting local expression is precisely the
weighted reservoir load at the fixed center state. -/
theorem colorDependentTinyCandidateAtomMean_eq
    (rho omega : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (c : Color)
    (row : G.ColorDependentTinyCandidateRow R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.colorDependentCandidateAtomUse proposal R rho omega source c z
            (Sum.inr row)) =
      rho /
          G.smoothedColorDependentExtendedProfileProbability
            R omega row.center c row.candidate *
        (∑ e : G.StarEdge row.center,
          G.weight e.1 * G.colorDependentExtendedProfileTinyAssign
            R row.center c e row.candidate) := by
  classical
  rcases row with ⟨center, candidate⟩
  have hstar :
      (∑ e : G.StarEdge center,
        G.weight e.1 * G.colorDependentExtendedProfileTinyAssign
          R center c e candidate) =
      ∑ e : G.E, if h : G.Inc center e then
        G.weight e * G.colorDependentExtendedProfileTinyAssign
          R center c ⟨e, h⟩ candidate else 0 := by
    symm
    calc
      (∑ e : G.E, if h : G.Inc center e then
          G.weight e * G.colorDependentExtendedProfileTinyAssign
            R center c ⟨e, h⟩ candidate else 0) =
          ∑ e ∈ Finset.univ.filter (G.Inc center),
            if h : G.Inc center e then
              G.weight e * G.colorDependentExtendedProfileTinyAssign
                R center c ⟨e, h⟩ candidate else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _he
        by_cases hinc : G.Inc center e <;> simp [hinc]
      _ = ∑ e : G.StarEdge center,
          if h : G.Inc center e.1 then
            G.weight e.1 * G.colorDependentExtendedProfileTinyAssign
              R center c ⟨e.1, h⟩ candidate else 0 := by
        exact Finset.sum_subtype (p := G.Inc center)
          (Finset.univ.filter (G.Inc center)) (by intro e; simp)
          (fun e ↦ if h : G.Inc center e then
            G.weight e * G.colorDependentExtendedProfileTinyAssign
              R center c ⟨e, h⟩ candidate else 0)
      _ = ∑ e : G.StarEdge center,
          G.weight e.1 * G.colorDependentExtendedProfileTinyAssign
            R center c e candidate := by
        apply Finset.sum_congr rfl
        intro e _he
        simp [e.property]
  rw [hstar]
  unfold colorDependentCandidateAtomUse
  simp_rw [Finset.mul_sum]
  calc
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        ∑ e : G.E,
          G.smoothedColorDependentExtendedProfileProbability
              R omega source c z *
            G.colorDependentTinyCandidateEdgeUse
              proposal R rho omega source c z e ⟨center, candidate⟩) =
      ∑ source : G.V, ∑ e : G.E,
        ∑ z : G.ColorDependentExtendedProfileState R source c,
          G.smoothedColorDependentExtendedProfileProbability
              R omega source c z *
            G.colorDependentTinyCandidateEdgeUse
              proposal R rho omega source c z e ⟨center, candidate⟩ := by
        apply Finset.sum_congr rfl
        intro source _hsource
        rw [Finset.sum_comm]
    _ = ∑ e : G.E, ∑ source : G.V,
        ∑ z : G.ColorDependentExtendedProfileState R source c,
          G.smoothedColorDependentExtendedProfileProbability
              R omega source c z *
            G.colorDependentTinyCandidateEdgeUse
              proposal R rho omega source c z e ⟨center, candidate⟩ := by
        rw [Finset.sum_comm]
    _ = ∑ e : G.E,
        rho /
            G.smoothedColorDependentExtendedProfileProbability
              R omega center c candidate *
          (if h : G.Inc center e then
            G.weight e * G.colorDependentExtendedProfileTinyAssign
              R center c ⟨e, h⟩ candidate else 0) := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hfst : center = G.fst e
      · subst center
        have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
        rw [Finset.sum_eq_single (G.snd e)]
        · simp only [colorDependentTinyCandidateEdgeUse]
          have htrue : True ∧ True := ⟨True.intro, True.intro⟩
          have hinc : G.Inc (G.fst e) e := Or.inl rfl
          simp only [htrue, hinc, if_true]
          have hstarEdge : (⟨e, hinc⟩ : G.StarEdge (G.fst e)) =
              G.fstStarEdge e := by
            apply Subtype.ext
            rfl
          by_cases hy : G.colorDependentExtendedProfileTinyEdgeColorMass
              (s := s) (β := β) proposal e c = 0
          · have hle :=
                G.colorDependentExtendedProfileTinyAssign_le_edgeColorMass
                  proposal R (G.fst e) c (G.fstStarEdge e) candidate
            change G.colorDependentExtendedProfileTinyAssign R
                (G.fst e) c (G.fstStarEdge e) candidate ≤
              G.colorDependentExtendedProfileTinyEdgeColorMass
                (s := s) (β := β) proposal e c at hle
            have hassign0 :
                G.colorDependentExtendedProfileTinyAssign R
                    (G.fst e) c (G.fstStarEdge e)
                    candidate = 0 :=
              le_antisymm
                (by simpa only [hy] using hle)
                (G.colorDependentExtendedProfileTinyAssign_nonneg R
                  (G.fst e) c (G.fstStarEdge e) candidate)
            simp [colorDependentExtendedProfileTinyProductMass,
              pairedOption, hy, hstarEdge, hassign0]
          · have hexpect := G.colorDependentTinyProductMass_right_expectation
                proposal R (rho := rho) hs hq hr0 hleft homega0 homega1 hy
                candidate
            calc
              (∑ z : G.ColorDependentExtendedProfileState R (G.snd e) c,
                G.smoothedColorDependentExtendedProfileProbability
                    R omega (G.snd e) c z *
                  (G.weight e *
                    G.colorDependentExtendedProfileTinyProductMass
                      proposal R rho omega e c candidate z)) =
                  G.weight e *
                    (∑ z : G.ColorDependentExtendedProfileState R (G.snd e) c,
                      G.smoothedColorDependentExtendedProfileProbability
                          R omega (G.snd e) c z *
                        G.colorDependentExtendedProfileTinyProductMass
                          proposal R rho omega e c candidate z) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro z _hz
                    ring
              _ = G.weight e *
                    (rho * G.colorDependentExtendedProfileTinyAssign R
                      (G.fst e) c (G.fstStarEdge e)
                        candidate /
                      G.smoothedColorDependentExtendedProfileProbability R
                        omega (G.fst e) c candidate) := by
                    rw [hexpect]
              _ = rho /
                    G.smoothedColorDependentExtendedProfileProbability
                      R omega (G.fst e) c candidate *
                    (G.weight e *
                      G.colorDependentExtendedProfileTinyAssign R
                        (G.fst e) c ⟨e, hinc⟩ candidate) := by
                    simp [hstarEdge]
                    ring
        · intro source _hsource hsource
          have hsndSource : source ≠ G.snd e := hsource
          have hnotMatch : ¬G.ColorDependentCandidateEdgeMatches
              (G.fst e) source e := by
            intro h
            rcases h with h | h
            · exact hsndSource h.2
            · exact hne h.1.symm
          have hedge0 : ∀ z : G.ColorDependentExtendedProfileState R source c,
              G.colorDependentTinyCandidateEdgeUse proposal R rho omega
                source c z e ⟨G.fst e, candidate⟩ = 0 := fun z ↦
            G.colorDependentTinyCandidateEdgeUse_eq_zero_of_not_matches
              proposal R rho omega source c z e
                ⟨G.fst e, candidate⟩ hnotMatch
          simp only [hedge0, mul_zero, Finset.sum_const_zero]
        · simp
      · by_cases hsnd : center = G.snd e
        · subst center
          rw [Finset.sum_eq_single (G.fst e)]
          · have hnot1 : ¬(G.snd e = G.fst e ∧ G.fst e = G.snd e) :=
              fun h ↦ hfst h.1
            simp only [colorDependentTinyCandidateEdgeUse]
            have htrue : True ∧ True := ⟨True.intro, True.intro⟩
            have hinc : G.Inc (G.snd e) e := Or.inr rfl
            simp only [hnot1, htrue, hinc, if_false, if_true]
            have hstarEdge : (⟨e, hinc⟩ : G.StarEdge (G.snd e)) =
                G.sndStarEdge e := by
              apply Subtype.ext
              rfl
            by_cases hy : G.colorDependentExtendedProfileTinyEdgeColorMass
                (s := s) (β := β) proposal e c = 0
            · have hle :=
                  G.colorDependentExtendedProfileTinyAssign_le_edgeColorMass
                    proposal R (G.snd e) c (G.sndStarEdge e) candidate
              change G.colorDependentExtendedProfileTinyAssign R
                  (G.snd e) c (G.sndStarEdge e) candidate ≤
                G.colorDependentExtendedProfileTinyEdgeColorMass
                  (s := s) (β := β) proposal e c at hle
              have hassign0 :
                  G.colorDependentExtendedProfileTinyAssign R
                      (G.snd e) c (G.sndStarEdge e)
                      candidate = 0 :=
                le_antisymm
                  (by simpa only [hy] using hle)
                  (G.colorDependentExtendedProfileTinyAssign_nonneg R
                    (G.snd e) c (G.sndStarEdge e) candidate)
              simp [colorDependentExtendedProfileTinyProductMass,
                pairedOption, hy, hstarEdge, hassign0]
            · have hexpect := G.colorDependentTinyProductMass_left_expectation
                  proposal R (rho := rho) hs hq hr0 hleft homega0 homega1 hy
                  candidate
              calc
                (∑ z : G.ColorDependentExtendedProfileState R (G.fst e) c,
                  G.smoothedColorDependentExtendedProfileProbability
                      R omega (G.fst e) c z *
                    (G.weight e *
                      G.colorDependentExtendedProfileTinyProductMass
                        proposal R rho omega e c z candidate)) =
                    G.weight e *
                      (∑ z : G.ColorDependentExtendedProfileState R (G.fst e) c,
                        G.smoothedColorDependentExtendedProfileProbability
                            R omega (G.fst e) c z *
                          G.colorDependentExtendedProfileTinyProductMass
                            proposal R rho omega e c z candidate) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro z _hz
                      ring
                _ = G.weight e *
                      (rho * G.colorDependentExtendedProfileTinyAssign R
                        (G.snd e) c (G.sndStarEdge e)
                          candidate /
                        G.smoothedColorDependentExtendedProfileProbability R
                          omega (G.snd e) c candidate) := by
                      rw [hexpect]
                _ = rho /
                      G.smoothedColorDependentExtendedProfileProbability
                        R omega (G.snd e) c candidate *
                      (G.weight e *
                        G.colorDependentExtendedProfileTinyAssign R
                          (G.snd e) c ⟨e, hinc⟩ candidate) := by
                      simp [hstarEdge]
                      ring
          · intro source _hsource hsource
            have hfstSource : source ≠ G.fst e := hsource
            have hnotMatch : ¬G.ColorDependentCandidateEdgeMatches
                (G.snd e) source e := by
              intro h
              rcases h with h | h
              · exact hfst h.1
              · exact hfstSource h.2
            have hedge0 : ∀ z : G.ColorDependentExtendedProfileState R source c,
                G.colorDependentTinyCandidateEdgeUse proposal R rho omega
                  source c z e ⟨G.snd e, candidate⟩ = 0 := fun z ↦
              G.colorDependentTinyCandidateEdgeUse_eq_zero_of_not_matches
                proposal R rho omega source c z e
                  ⟨G.snd e, candidate⟩ hnotMatch
            simp only [hedge0, mul_zero, Finset.sum_const_zero]
          · simp
        · have hnot1 : ∀ source,
              ¬(center = G.fst e ∧ source = G.snd e) :=
            fun _ h ↦ hfst h.1
          have hnot2 : ∀ source,
              ¬(center = G.snd e ∧ source = G.fst e) :=
            fun _ h ↦ hsnd h.1
          have hnotInc : ¬G.Inc center e := by
            intro hinc
            rcases hinc with hinc | hinc
            · exact hfst hinc.symm
            · exact hsnd hinc.symm
          have hnotMatch : ∀ source,
              ¬G.ColorDependentCandidateEdgeMatches center source e := by
            intro source h
            rcases h with h | h
            · exact hfst h.1
            · exact hsnd h.1
          have hedge0 : ∀ source
              (z : G.ColorDependentExtendedProfileState R source c),
              G.colorDependentTinyCandidateEdgeUse proposal R rho omega
                source c z e ⟨center, candidate⟩ = 0 := fun source z ↦
            G.colorDependentTinyCandidateEdgeUse_eq_zero_of_not_matches
              proposal R rho omega source c z e
                ⟨center, candidate⟩ (hnotMatch source)
          rw [dif_neg hnotInc]
          simp only [hedge0, mul_zero, Finset.sum_const_zero]

/-- Sharp tiny-row mean retaining the reservoir size of the candidate center
state.  This is the form used after the word has been selected. -/
theorem colorDependentTinyCandidateAtomMean_le_reservoir
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (c : Color)
    (row : G.ColorDependentTinyCandidateRow R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.colorDependentCandidateAtomUse proposal R rho omega source c z
            (Sum.inr row)) ≤
      rho * G.colorDependentExtendedProfileReservoirSize
          R row.center c row.candidate /
        (omega / extendedProfileStateBound β q r) := by
  rw [G.colorDependentTinyCandidateAtomMean_eq proposal R rho omega
    hs hq hr0 hleft homega0 homega1 c row]
  let A := ∑ e : G.StarEdge row.center,
    G.weight e.1 * G.colorDependentExtendedProfileTinyAssign
      R row.center c e row.candidate
  let p := G.colorDependentExtendedProfileProbability
    R row.center c row.candidate
  let lam := G.smoothedColorDependentExtendedProfileProbability
    R omega row.center c row.candidate
  let reservoir := G.colorDependentExtendedProfileReservoirSize
    R row.center c row.candidate
  let kappa := omega / extendedProfileStateBound β q r
  have hA : A ≤ p * reservoir :=
    G.sum_weight_mul_colorDependentExtendedProfileTinyAssign_le_probability_mul_reservoir
      R row.center c row.candidate
  have hres0 : 0 ≤ reservoir :=
    G.colorDependentExtendedProfileReservoirSize_nonneg
      R row.center c row.candidate
  have hlam : 0 < lam :=
    G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 row.center c row.candidate
  have hM : 0 < (extendedProfileStateBound β q r : ℝ) := by
    unfold extendedProfileStateBound profileStateBound
    positivity
  have hkappa : 0 < kappa := div_pos homega0 hM
  have hkappaP : kappa * p ≤ lam := by
    have hp0 : 0 ≤ p := G.colorDependentExtendedProfileProbability_nonneg R
      hs hq hr0 hleft row.center c row.candidate
    have hp1 : p ≤ 1 := G.colorDependentExtendedProfileProbability_le_one R
      hs hq hr0 hleft row.center c row.candidate
    have hklam : kappa ≤ lam :=
      G.omega_div_stateBound_le_smoothedColorDependentProbability R
        hs hq hr0 hleft homega0 homega1 row.center c row.candidate
    calc
      kappa * p ≤ kappa * 1 := mul_le_mul_of_nonneg_left hp1 hkappa.le
      _ = kappa := mul_one _
      _ ≤ lam := hklam
  have hratio : A / lam ≤ reservoir / kappa := by
    apply (div_le_div_iff₀ hlam hkappa).2
    calc
      A * kappa ≤ (p * reservoir) * kappa :=
        mul_le_mul_of_nonneg_right hA hkappa.le
      _ = reservoir * (kappa * p) := by ring
      _ ≤ reservoir * lam := mul_le_mul_of_nonneg_left hkappaP hres0
  calc
    rho / lam * A = rho * (A / lam) := by ring
    _ ≤ rho * (reservoir / kappa) :=
      mul_le_mul_of_nonneg_left hratio hrho
    _ = rho * reservoir / kappa := by ring

/-- Sharper reservoir-sensitive estimate using the unsmoothed component of
the state law. -/
theorem colorDependentTinyCandidateAtomMean_le_reservoir_one_sub_omega
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (c : Color)
    (row : G.ColorDependentTinyCandidateRow R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.colorDependentCandidateAtomUse proposal R rho omega source c z
            (Sum.inr row)) ≤
      rho * G.colorDependentExtendedProfileReservoirSize
          R row.center c row.candidate / (1 - omega) := by
  rw [G.colorDependentTinyCandidateAtomMean_eq proposal R rho omega
    hs hq hr0 hleft homega0 homega1.le c row]
  let A := ∑ e : G.StarEdge row.center,
    G.weight e.1 * G.colorDependentExtendedProfileTinyAssign
      R row.center c e row.candidate
  let p := G.colorDependentExtendedProfileProbability
    R row.center c row.candidate
  let lam := G.smoothedColorDependentExtendedProfileProbability
    R omega row.center c row.candidate
  let reservoir := G.colorDependentExtendedProfileReservoirSize
    R row.center c row.candidate
  have hA : A ≤ p * reservoir :=
    G.sum_weight_mul_colorDependentExtendedProfileTinyAssign_le_probability_mul_reservoir
      R row.center c row.candidate
  have hres0 : 0 ≤ reservoir :=
    G.colorDependentExtendedProfileReservoirSize_nonneg
      R row.center c row.candidate
  have hlam : 0 < lam :=
    G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1.le row.center c row.candidate
  have hone : 0 < 1 - omega := sub_pos.mpr homega1
  have hbase : (1 - omega) * p ≤ lam :=
    G.one_sub_omega_mul_colorDependentProbability_le_smoothed R
      homega0.le row.center c row.candidate
  have hratio : A / lam ≤ reservoir / (1 - omega) := by
    apply (div_le_div_iff₀ hlam hone).2
    calc
      A * (1 - omega) ≤ (p * reservoir) * (1 - omega) :=
        mul_le_mul_of_nonneg_right hA hone.le
      _ = reservoir * ((1 - omega) * p) := by ring
      _ ≤ reservoir * lam := mul_le_mul_of_nonneg_left hbase hres0
  calc
    rho / lam * A = rho * (A / lam) := by ring
    _ ≤ rho * (reservoir / (1 - omega)) :=
      mul_le_mul_of_nonneg_left hratio hrho
    _ = rho * reservoir / (1 - omega) := by ring

/-- Sharp common envelope for either candidate-row family. -/
theorem colorDependentCandidateAtomMean_le_one_sub_omega
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (c : Color)
    (row : G.ColorDependentCandidateRowAt R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.colorDependentCandidateAtomUse proposal R rho omega source c z row) ≤
      rho / (1 - omega) := by
  rcases row with large | tiny
  · exact G.colorDependentLargeCandidateAtomMean_le_one_sub_omega proposal R
      hs hq hr0 hleft homega0 homega1 hrho c large
  · have hsharp :=
      G.colorDependentTinyCandidateAtomMean_le_reservoir_one_sub_omega
        proposal R hs hq hr0 hleft homega0 homega1 hrho c tiny
    have hres1 : G.colorDependentExtendedProfileReservoirSize
        R tiny.center c tiny.candidate ≤ 1 := by
      exact G.colorDependentExtendedProfileReservoirSize_le_one
        R tiny.center c tiny.candidate
    have hden : 0 ≤ rho / (1 - omega) :=
      div_nonneg hrho (sub_nonneg.mpr homega1.le)
    exact hsharp.trans (by
      calc
        rho * G.colorDependentExtendedProfileReservoirSize
              R tiny.center c tiny.candidate / (1 - omega) =
            (rho / (1 - omega)) *
              G.colorDependentExtendedProfileReservoirSize
                R tiny.center c tiny.candidate := by ring
        _ ≤ (rho / (1 - omega)) * 1 :=
          mul_le_mul_of_nonneg_left hres1 hden
        _ = rho / (1 - omega) := mul_one _)

/-- Uniform tiny-row mean bound. -/
theorem colorDependentTinyCandidateAtomMean_le_uniform
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (c : Color)
    (row : G.ColorDependentTinyCandidateRow R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.colorDependentCandidateAtomUse proposal R rho omega source c z
            (Sum.inr row)) ≤
      rho * extendedProfileStateBound β q r / omega := by
  rw [G.colorDependentTinyCandidateAtomMean_eq proposal R rho omega
    hs hq hr0 hleft homega0 homega1 c row]
  let lam := G.smoothedColorDependentExtendedProfileProbability
    R omega row.center c row.candidate
  let A := ∑ e : G.StarEdge row.center,
    G.weight e.1 * G.colorDependentExtendedProfileTinyAssign
      R row.center c e row.candidate
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun e _he ↦
    mul_nonneg (G.weight_nonneg e.1)
      (G.colorDependentExtendedProfileTinyAssign_nonneg
        R row.center c e row.candidate)
  have hAprob : A ≤
      G.colorDependentExtendedProfileProbability
        R row.center c row.candidate :=
    G.sum_weight_mul_colorDependentExtendedProfileTinyAssign_le R
      hs hq hr0 hleft row.center c row.candidate
  have hprob1 := G.colorDependentExtendedProfileProbability_le_one R
    hs hq hr0 hleft row.center c row.candidate
  have hA1 : A ≤ 1 := hAprob.trans hprob1
  have hlam : omega / extendedProfileStateBound β q r ≤ lam :=
    G.omega_div_stateBound_le_smoothedColorDependentProbability R
      hs hq hr0 hleft homega0 homega1 row.center c row.candidate
  have hlam0 : 0 < lam :=
    G.smoothedColorDependentExtendedProfileProbability_pos R
      hs hq hr0 hleft homega0 homega1 row.center c row.candidate
  have hM0 : 0 < (extendedProfileStateBound β q r : ℝ) := by
    unfold extendedProfileStateBound profileStateBound
    positivity
  have homegaM : 0 < omega / extendedProfileStateBound β q r :=
    div_pos homega0 hM0
  have hratio : rho / lam ≤
      rho / (omega / extendedProfileStateBound β q r) :=
    div_le_div_of_nonneg_left hrho homegaM hlam
  have hmul : rho / lam * A ≤
      (rho / (omega / extendedProfileStateBound β q r)) * 1 :=
    mul_le_mul hratio hA1 hA0
      (div_nonneg hrho homegaM.le)
  calc
    rho / lam * A ≤
        (rho / (omega / extendedProfileStateBound β q r)) * 1 := hmul
    _ = rho * extendedProfileStateBound β q r / omega := by
      field_simp

/-- Both kinds of per-color candidate capacity rows have the same uniform
mean bound. -/
theorem colorDependentCandidateAtomMean_le_uniform
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (c : Color)
    (row : G.ColorDependentCandidateRowAt R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.colorDependentCandidateAtomUse proposal R rho omega source c z row) ≤
      rho * extendedProfileStateBound β q r / omega := by
  rcases row with large | tiny
  · exact G.colorDependentLargeCandidateAtomMean_le_uniform proposal R
      hs hq hr0 hleft homega0 homega1 hrho c large
  · exact G.colorDependentTinyCandidateAtomMean_le_uniform proposal R
      hs hq hr0 hleft homega0 homega1 hrho c tiny

/-- Quantitatively useful scaled row-mean bound.  This is the normalization
fed to partial resampling: its mean is linear in `n`, so the packing
deviation is sublinear and becomes `o(1)` after decoding back by `scale/n`. -/
theorem scaledColorDependentCandidateAtomMean_le_uniform
    (n : ℕ) (scale : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hscale : 0 < scale) (c : Color)
    (row : G.ColorDependentCandidateRowAt R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.scaledColorDependentCandidateAtomUse
            proposal R n scale rho omega source c z row) ≤
      (n : ℝ) * (rho * extendedProfileStateBound β q r / omega) /
        scale := by
  have hraw := G.colorDependentCandidateAtomMean_le_uniform proposal R
    hs hq hr0 hleft homega0 homega1 hrho c row
  unfold scaledColorDependentCandidateAtomUse
  have hrearrange :
      (∑ source : G.V,
        ∑ z : G.ColorDependentExtendedProfileState R source c,
          G.smoothedColorDependentExtendedProfileProbability R omega source c z *
            ((n : ℝ) *
              G.colorDependentCandidateAtomUse proposal R rho omega source c z row /
              scale)) =
        (n : ℝ) / scale *
          (∑ source : G.V,
            ∑ z : G.ColorDependentExtendedProfileState R source c,
              G.smoothedColorDependentExtendedProfileProbability
                  R omega source c z *
                G.colorDependentCandidateAtomUse
                  proposal R rho omega source c z row) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _hsource
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    ring
  rw [hrearrange]
  have hcoef : 0 ≤ (n : ℝ) / scale :=
    div_nonneg (Nat.cast_nonneg n) hscale.le
  calc
    (n : ℝ) / scale *
        (∑ source : G.V,
          ∑ z : G.ColorDependentExtendedProfileState R source c,
            G.smoothedColorDependentExtendedProfileProbability
                R omega source c z *
              G.colorDependentCandidateAtomUse
                proposal R rho omega source c z row) ≤
      (n : ℝ) / scale *
        (rho * extendedProfileStateBound β q r / omega) :=
      mul_le_mul_of_nonneg_left hraw hcoef
    _ = (n : ℝ) * (rho * extendedProfileStateBound β q r / omega) /
        scale := by ring

theorem scaledColorDependentCandidateAtomMean_le_one_sub_omega
    (n : ℕ) (scale : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (hscale : 0 < scale) (c : Color)
    (row : G.ColorDependentCandidateRowAt R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.scaledColorDependentCandidateAtomUse
            proposal R n scale rho omega source c z row) ≤
      (n : ℝ) * (rho / (1 - omega)) / scale := by
  have hraw := G.colorDependentCandidateAtomMean_le_one_sub_omega proposal R
    hs hq hr0 hleft homega0 homega1 hrho c row
  unfold scaledColorDependentCandidateAtomUse
  have hrearrange :
      (∑ source : G.V,
        ∑ z : G.ColorDependentExtendedProfileState R source c,
          G.smoothedColorDependentExtendedProfileProbability R omega source c z *
            ((n : ℝ) *
              G.colorDependentCandidateAtomUse proposal R rho omega source c z row /
              scale)) =
        (n : ℝ) / scale *
          (∑ source : G.V,
            ∑ z : G.ColorDependentExtendedProfileState R source c,
              G.smoothedColorDependentExtendedProfileProbability
                  R omega source c z *
                G.colorDependentCandidateAtomUse
                  proposal R rho omega source c z row) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _hsource
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    ring
  rw [hrearrange]
  have hcoef : 0 ≤ (n : ℝ) / scale :=
    div_nonneg (Nat.cast_nonneg n) hscale.le
  calc
    (n : ℝ) / scale *
        (∑ source : G.V,
          ∑ z : G.ColorDependentExtendedProfileState R source c,
            G.smoothedColorDependentExtendedProfileProbability
                R omega source c z *
              G.colorDependentCandidateAtomUse
                proposal R rho omega source c z row) ≤
      (n : ℝ) / scale * (rho / (1 - omega)) :=
      mul_le_mul_of_nonneg_left hraw hcoef
    _ = (n : ℝ) * (rho / (1 - omega)) / scale := by ring

theorem scaledColorDependentTinyCandidateAtomMean_le_reservoir
    (n : ℕ) (scale : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (hscale : 0 < scale) (c : Color)
    (row : G.ColorDependentTinyCandidateRow R c) :
    (∑ source : G.V,
      ∑ z : G.ColorDependentExtendedProfileState R source c,
        G.smoothedColorDependentExtendedProfileProbability R omega source c z *
          G.scaledColorDependentCandidateAtomUse proposal R n scale rho omega
            source c z (Sum.inr row)) ≤
      (n : ℝ) *
        (rho * G.colorDependentExtendedProfileReservoirSize
          R row.center c row.candidate / (1 - omega)) / scale := by
  have hraw :=
    G.colorDependentTinyCandidateAtomMean_le_reservoir_one_sub_omega
      proposal R hs hq hr0 hleft homega0 homega1 hrho c row
  unfold scaledColorDependentCandidateAtomUse
  have hrearrange :
      (∑ source : G.V,
        ∑ z : G.ColorDependentExtendedProfileState R source c,
          G.smoothedColorDependentExtendedProfileProbability R omega source c z *
            ((n : ℝ) *
              G.colorDependentCandidateAtomUse proposal R rho omega source c z
                (Sum.inr row) / scale)) =
        (n : ℝ) / scale *
          (∑ source : G.V,
            ∑ z : G.ColorDependentExtendedProfileState R source c,
              G.smoothedColorDependentExtendedProfileProbability
                  R omega source c z *
                G.colorDependentCandidateAtomUse proposal R rho omega source c z
                  (Sum.inr row)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _hsource
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    ring
  rw [hrearrange]
  exact (mul_le_mul_of_nonneg_left hraw
      (div_nonneg (Nat.cast_nonneg n) hscale.le)).trans_eq (by ring)

end CandidateMeanBounds

end WeightedSimpleGraph

end

end WeightedEdgeColoring
