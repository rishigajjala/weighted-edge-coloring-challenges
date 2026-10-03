import WeightedEdgeColoring.SubtwoMixedGraphCoordinateMass
import WeightedEdgeColoring.FiniteCoordinateDependentWordMoments

/-!
# Weighted block variance for mixed labelled graph atoms

The source is a vertex and a fixed colour block.  Within a block the mixed
atoms are sampled independently across the fixed number of coordinates.
The complete option-mass kernel is bounded and has the exact proposal mean.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {B k : ℕ} {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, (Fin B × Fin k) →
  Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

def mixedBlockProposal (b : Fin B) : G.E → Fin k → ℝ :=
  fun e i ↦ proposal e (b, i)

def mixedBlockLaw (b : Fin B) :
    ∀ v : G.V, Fin k → Finset (G.StarEdge v) → ℝ :=
  fun v i S ↦ qLaw v (b, i) S

def mixedBlockRealization (b : Fin B) :
    ∀ v i label,
      G.BoundedProfileRealization
        (G.conditionalEndpointProposal (edgeLabel v)
          (fun e : G.StarEdge v ↦ G.mixedBlockProposal proposal b e.1 i)
          (G.mixedBlockLaw qLaw b v i) label)
        s β qstep r hβ hr :=
  fun v i label ↦ R v (b, i) label

abbrev MixedGraphPackedBlockState (b : Fin B) :=
  Subtwo.LabelledPackedWordState
    (fun v i ↦ G.MixedGraphAtom
      (G.mixedBlockProposal proposal b) edgeLabel
      (G.mixedBlockLaw qLaw b)
      (G.mixedBlockRealization proposal edgeLabel qLaw R b) v i)
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r))

def mixedBlockProbability (omega : ℝ) (v : G.V) (b : Fin B)
    (state : G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b) : ℝ :=
  G.paddedMixedGraphWordProbability
    (G.mixedBlockProposal proposal b) edgeLabel
    (G.mixedBlockLaw qLaw b)
    (G.mixedBlockRealization proposal edgeLabel qLaw R b)
    omega v state

theorem sum_mixedBlockProbability (omega : ℝ)
    (v : G.V) (b : Fin B) :
    (∑ state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R b,
      G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b state) = 1 := by
  exact G.sum_paddedMixedGraphWordProbability
    (G.mixedBlockProposal proposal b) edgeLabel
    (G.mixedBlockLaw qLaw b)
    (G.mixedBlockRealization proposal edgeLabel qLaw R b)
    omega v

theorem sum_mixedBlockProbability_mul_decode (omega : ℝ)
    (v : G.V) (b : Fin B)
    (f : (∀ i : Fin k,
      G.MixedGraphAtom
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b) v i) → ℝ) :
    (∑ state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b,
      G.mixedBlockProbability proposal edgeLabel qLaw R omega v b state *
        f (fun i ↦ G.decodeMixedGraphAtom
          (G.mixedBlockProposal proposal b) edgeLabel
          (G.mixedBlockLaw qLaw b)
          (G.mixedBlockRealization proposal edgeLabel qLaw R b)
          v state i)) =
      ∑ word : ∀ i : Fin k,
        G.MixedGraphAtom
          (G.mixedBlockProposal proposal b) edgeLabel
          (G.mixedBlockLaw qLaw b)
          (G.mixedBlockRealization proposal edgeLabel qLaw R b) v i,
        (∏ i : Fin k,
          G.smoothedMixedGraphProbability
            (G.mixedBlockProposal proposal b) edgeLabel
            (G.mixedBlockLaw qLaw b)
            (G.mixedBlockRealization proposal edgeLabel qLaw R b)
            omega v i (word i)) * f word := by
  classical
  simpa [mixedBlockProbability, mixedBlockProposal, mixedBlockLaw,
    mixedBlockRealization, Subtwo.labelledWordMass] using
    (Subtwo.sum_paddedLabelledWordProbability_mul_decode
      (fun v i ↦ G.MixedGraphAtom
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b) v i)
      (fun _ _ ↦ none)
      (mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r))
      (fun v i ↦ G.mixedGraphAtom_card_le
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b) v i)
      (G.smoothedMixedGraphProbability
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b) omega)
      v f)

def mixedBlockOptionMass (rho omega : ℝ) (e : G.E) (b : Fin B)
    (left right : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R b) : ℝ :=
  ∑ i : Fin k,
    G.mixedGraphCoordinateOptionMass
      (G.mixedBlockProposal proposal b) edgeLabel
      (G.mixedBlockLaw qLaw b)
      (G.mixedBlockRealization proposal edgeLabel qLaw R b)
      rho omega e i
      (G.decodeMixedGraphAtom
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        (G.fst e) left i)
      (G.decodeMixedGraphAtom
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        (G.snd e) right i)

def mixedBlockTarget (rho s : ℝ) (e : G.E) (b : Fin B) : ℝ :=
  rho * s * ∑ i : Fin k, proposal e (b, i)

def mixedBlockVariance (rho omega : ℝ) (e : G.E) (b : Fin B)
    (left right : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R b) : ℝ :=
  G.weight e *
    (G.mixedBlockOptionMass proposal edgeLabel qLaw R
      rho omega e b left right -
      G.mixedBlockTarget proposal rho s e b) ^ 2

theorem mixedBlockVariance_nonneg (rho omega : ℝ) (e : G.E) (b : Fin B)
    (left right : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R b) :
    0 ≤ G.mixedBlockVariance proposal edgeLabel qLaw R
      rho omega e b left right := by
  unfold mixedBlockVariance
  exact mul_nonneg (G.weight_pos e).le (sq_nonneg _)

theorem n_mul_mixedBlockOptionMass_le
    {n : ℕ} (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (b : Fin B)
    (left right : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R b) :
    (n : ℝ) * G.mixedBlockOptionMass proposal edgeLabel qLaw R
      rho omega e b left right ≤
      (k : ℝ) * mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  unfold mixedBlockOptionMass
  rw [Finset.mul_sum]
  calc
    (∑ i : Fin k,
      (n : ℝ) * G.mixedGraphCoordinateOptionMass
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        rho omega e i
        (G.decodeMixedGraphAtom
          (G.mixedBlockProposal proposal b) edgeLabel
          (G.mixedBlockLaw qLaw b)
          (G.mixedBlockRealization proposal edgeLabel qLaw R b)
          (G.fst e) left i)
        (G.decodeMixedGraphAtom
          (G.mixedBlockProposal proposal b) edgeLabel
          (G.mixedBlockLaw qLaw b)
          (G.mixedBlockRealization proposal edgeLabel qLaw R b)
          (G.snd e) right i)) ≤
        ∑ _i : Fin k,
          mixedCandidateOrientedScale (Label := Label)
            (β := β) (qstep := qstep) (r := r)
            rho s omega C0 := by
      apply Finset.sum_le_sum
      intro i _
      exact G.n_mul_mixedGraphCoordinateOptionMass_le_orientedScale
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        hn (fun v j S ↦ hq0 v (b, j) S)
        (fun v j f ↦ hqmarg v (b, j) f)
        (fun v j S hS0 hSne ↦ hqsingle v (b, j) S hS0 hSne)
        (fun v j ↦ hqsum v (b, j))
        hs hqstep hr0 hleft homega0 homega1 hrho hC0
        (fun f j ↦ hproposal0 f (b, j))
        (fun f j ↦ hproposal f (b, j)) e i _ _
    _ = (k : ℝ) * mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r)
        rho s omega C0 := by simp

theorem mixedBlockOptionMass_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (b : Fin B)
    (left right : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R b) :
    0 ≤ G.mixedBlockOptionMass proposal edgeLabel qLaw R
      rho omega e b left right := by
  unfold mixedBlockOptionMass
  apply Finset.sum_nonneg
  intro i _
  exact G.mixedGraphCoordinateOptionMass_nonneg
    (G.mixedBlockProposal proposal b) edgeLabel
    (G.mixedBlockLaw qLaw b)
    (G.mixedBlockRealization proposal edgeLabel qLaw R b)
    (fun v j S ↦ hq0 v (b, j) S)
    (fun v j ↦ hqsum v (b, j))
    (fun v j S hS0 hSne ↦ hqsingle v (b, j) S hS0 hSne)
    hs hqstep hr0 hleft homega0 homega1 hrho
    (fun f j ↦ hproposal0 f (b, j)) e i _ _

theorem n_mul_mixedBlockTarget_le
    {n : ℕ} (hn : 0 < n)
    (hrho : 0 ≤ rho) (hs : 0 ≤ s)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (b : Fin B) :
    (n : ℝ) * G.mixedBlockTarget proposal rho s e b ≤
      (k : ℝ) * (rho * s * C0) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold mixedBlockTarget
  rw [Finset.mul_sum, Finset.mul_sum]
  calc
    (∑ i : Fin k, (n : ℝ) * (rho * s * proposal e (b, i))) ≤
      ∑ _i : Fin k, rho * s * C0 := by
      apply Finset.sum_le_sum
      intro i _
      have hp := (le_div_iff₀ hnR).1 (hproposal e (b, i))
      nlinarith [mul_nonneg hrho hs]
    _ = (k : ℝ) * (rho * s * C0) := by simp

theorem mixedBlockVariance_le_pairScale
    {n : ℕ} (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (b : Fin B)
    (left right : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R b) :
    G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e b left right ≤
      G.weight e *
        (((k : ℝ) *
          (mixedCandidateOrientedScale (Label := Label)
            (β := β) (qstep := qstep) (r := r)
            rho s omega C0 + rho * s * C0) / (n : ℝ)) ^ 2) := by
  let x := G.mixedBlockOptionMass proposal edgeLabel qLaw R
    rho omega e b left right
  let y := G.mixedBlockTarget proposal rho s e b
  let U := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let D := (k : ℝ) * (U + rho * s * C0) / (n : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ x := G.mixedBlockOptionMass_nonneg
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1 hrho hproposal0 e b left right
  have hy0 : 0 ≤ y := by
    unfold y mixedBlockTarget
    exact mul_nonneg (mul_nonneg hrho hs)
      (Finset.sum_nonneg fun i _ ↦ hproposal0 e (b, i))
  have hx := G.n_mul_mixedBlockOptionMass_le
    proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
    hs hqstep hr0 hleft homega0 homega1 hrho hC0
    hproposal0 hproposal e b left right
  have hy := G.n_mul_mixedBlockTarget_le
    proposal hn hrho hs hproposal e b
  have hD0 : 0 ≤ D := by
    have hU0 : 0 ≤ U := mixedCandidateOrientedScale_nonneg
      (Label := Label) (β := β) (qstep := qstep) (r := r)
      hrho hs homega0 hC0
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (add_nonneg hU0 (mul_nonneg (mul_nonneg hrho hs) hC0)))
      hnR.le
  have hxy : x + y ≤ D := by
    apply (le_div_iff₀ hnR).2
    dsimp [D, U] at *
    nlinarith [hx, hy]
  have hleft : 0 ≤ D - (x - y) := by linarith
  have hright : 0 ≤ D + (x - y) := by linarith
  have hsquare : (x - y) ^ 2 ≤ D ^ 2 := by
    nlinarith [mul_nonneg hleft hright]
  unfold mixedBlockVariance
  exact mul_le_mul_of_nonneg_left hsquare (G.weight_pos e).le

theorem expected_mixedBlockVariance_le
    {n : ℕ} (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (b : Fin B) :
    (∑ left : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b,
      G.mixedBlockProbability proposal edgeLabel qLaw R
        omega (G.fst e) b left *
        ∑ right : G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b,
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega (G.snd e) b right *
            G.mixedBlockVariance proposal edgeLabel qLaw R
              rho omega e b left right) ≤
      G.weight e *
        ((mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 /
            (n : ℝ)) *
          G.mixedBlockTarget proposal rho s e b) := by
  classical
  let pL : ∀ i : Fin k,
      G.MixedGraphAtom
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        (G.fst e) i → ℝ :=
    fun i z ↦ G.smoothedMixedGraphProbability
      (G.mixedBlockProposal proposal b) edgeLabel
      (G.mixedBlockLaw qLaw b)
      (G.mixedBlockRealization proposal edgeLabel qLaw R b)
      omega (G.fst e) i z
  let pR : ∀ i : Fin k,
      G.MixedGraphAtom
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        (G.snd e) i → ℝ :=
    fun i z ↦ G.smoothedMixedGraphProbability
      (G.mixedBlockProposal proposal b) edgeLabel
      (G.mixedBlockLaw qLaw b)
      (G.mixedBlockRealization proposal edgeLabel qLaw R b)
      omega (G.snd e) i z
  let value : ∀ i : Fin k, _ → _ → ℝ :=
    fun i a z ↦ G.mixedGraphCoordinateOptionMass
      (G.mixedBlockProposal proposal b) edgeLabel
      (G.mixedBlockLaw qLaw b)
      (G.mixedBlockRealization proposal edgeLabel qLaw R b)
      rho omega e i a z
  let mean : Fin k → ℝ := fun i ↦ rho * s * proposal e (b, i)
  let U := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0 / (n : ℝ)
  let LeftWord := ∀ i : Fin k,
    G.MixedGraphAtom
      (G.mixedBlockProposal proposal b) edgeLabel
      (G.mixedBlockLaw qLaw b)
      (G.mixedBlockRealization proposal edgeLabel qLaw R b) (G.fst e) i
  let RightWord := ∀ i : Fin k,
    G.MixedGraphAtom
      (G.mixedBlockProposal proposal b) edgeLabel
      (G.mixedBlockLaw qLaw b)
      (G.mixedBlockRealization proposal edgeLabel qLaw R b) (G.snd e) i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmoment :=
    FiniteCoordinateDependentWordMoments.sum_twoWordMass_mul_centered_sum_sq_le
      (fun i : Fin k ↦ G.MixedGraphAtom
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        (G.fst e) i)
      (fun i : Fin k ↦ G.MixedGraphAtom
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        (G.snd e) i)
      pL pR
      (fun i z ↦ (G.smoothedMixedGraphProbability_pos
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        (fun v j S ↦ hq0 v (b, j) S)
        (fun v j ↦ hqsum v (b, j))
        (fun v j S hS0 hSne ↦ hqsingle v (b, j) S hS0 hSne)
        hs hqstep hr0 hleft homega0 homega1 (G.fst e) i z).le)
      (fun i z ↦ (G.smoothedMixedGraphProbability_pos
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        (fun v j S ↦ hq0 v (b, j) S)
        (fun v j ↦ hqsum v (b, j))
        (fun v j S hS0 hSne ↦ hqsingle v (b, j) S hS0 hSne)
        hs hqstep hr0 hleft homega0 homega1 (G.snd e) i z).le)
      (fun i ↦ G.sum_smoothedMixedGraphProbability
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        omega (G.fst e) i)
      (fun i ↦ G.sum_smoothedMixedGraphProbability
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        omega (G.snd e) i)
      value mean (fun _ ↦ U)
      (fun i a z ↦ G.mixedGraphCoordinateOptionMass_nonneg
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        (fun v j S ↦ hq0 v (b, j) S)
        (fun v j ↦ hqsum v (b, j))
        (fun v j S hS0 hSne ↦ hqsingle v (b, j) S hS0 hSne)
        hs hqstep hr0 hleft homega0 homega1 hrho
        (fun f j ↦ hproposal0 f (b, j)) e i a z)
      (fun i a z ↦ by
        have h := G.n_mul_mixedGraphCoordinateOptionMass_le_orientedScale
          (G.mixedBlockProposal proposal b) edgeLabel
          (G.mixedBlockLaw qLaw b)
          (G.mixedBlockRealization proposal edgeLabel qLaw R b)
          hn (fun v j S ↦ hq0 v (b, j) S)
          (fun v j f ↦ hqmarg v (b, j) f)
          (fun v j S hS0 hSne ↦ hqsingle v (b, j) S hS0 hSne)
          (fun v j ↦ hqsum v (b, j))
          hs hqstep hr0 hleft homega0 homega1 hrho hC0
          (fun f j ↦ hproposal0 f (b, j))
          (fun f j ↦ hproposal f (b, j)) e i a z
        exact (le_div_iff₀ hnR).2 (by simpa [value, mul_comm] using h))
      (fun i ↦ G.expected_mixedGraphCoordinateOptionMass
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        (fun v j S ↦ hq0 v (b, j) S)
        (fun v j f ↦ hqmarg v (b, j) f)
        (fun v j S hS0 hSne ↦ hqsingle v (b, j) S hS0 hSne)
        (fun v j ↦ hqsum v (b, j))
        hs hqstep hr0 hleft homega0 homega1 e i)
  -- The padded laws agree exactly with the genuine dependent product laws.
  have hpadded :
      (∑ left : G.MixedGraphPackedBlockState
          proposal edgeLabel qLaw R b,
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega (G.fst e) b left *
          ∑ right : G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b,
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega (G.snd e) b right *
              (G.mixedBlockOptionMass proposal edgeLabel qLaw R
                rho omega e b left right -
                G.mixedBlockTarget proposal rho s e b) ^ 2) ≤
        ∑ i : Fin k, U * mean i := by
    have hpoint (left right : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b) :
        (G.mixedBlockOptionMass proposal edgeLabel qLaw R
          rho omega e b left right -
          G.mixedBlockTarget proposal rho s e b) ^ 2 =
        (∑ i : Fin k,
          (value i
            (G.decodeMixedGraphAtom
              (G.mixedBlockProposal proposal b) edgeLabel
              (G.mixedBlockLaw qLaw b)
              (G.mixedBlockRealization proposal edgeLabel qLaw R b)
              (G.fst e) left i)
            (G.decodeMixedGraphAtom
              (G.mixedBlockProposal proposal b) edgeLabel
              (G.mixedBlockLaw qLaw b)
              (G.mixedBlockRealization proposal edgeLabel qLaw R b)
              (G.snd e) right i) - mean i)) ^ 2 := by
      simp only [mixedBlockOptionMass, mixedBlockTarget, value, mean,
        Finset.sum_sub_distrib, Finset.mul_sum]
    have hpaddedEq :
        (∑ left : G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b,
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega (G.fst e) b left *
            ∑ right : G.MixedGraphPackedBlockState
              proposal edgeLabel qLaw R b,
              G.mixedBlockProbability proposal edgeLabel qLaw R
                omega (G.snd e) b right *
                (G.mixedBlockOptionMass proposal edgeLabel qLaw R
                  rho omega e b left right -
                  G.mixedBlockTarget proposal rho s e b) ^ 2) =
          ∑ leftWord : LeftWord,
            FiniteCoordinateDependentWordMoments.wordMass
              (fun i : Fin k ↦ G.MixedGraphAtom
                (G.mixedBlockProposal proposal b) edgeLabel
                (G.mixedBlockLaw qLaw b)
                (G.mixedBlockRealization proposal edgeLabel qLaw R b)
                (G.fst e) i) pL leftWord *
              ∑ rightWord : RightWord,
                FiniteCoordinateDependentWordMoments.wordMass
                  (fun i : Fin k ↦ G.MixedGraphAtom
                    (G.mixedBlockProposal proposal b) edgeLabel
                    (G.mixedBlockLaw qLaw b)
                    (G.mixedBlockRealization proposal edgeLabel qLaw R b)
                    (G.snd e) i) pR rightWord *
                  (∑ i, (value i (leftWord i) (rightWord i) - mean i)) ^ 2 := by
      calc
        _ = ∑ left : G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b,
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega (G.fst e) b left *
              ∑ rightWord : RightWord,
                (∏ i : Fin k, pR i (rightWord i)) *
                (∑ i, (value i
                  (G.decodeMixedGraphAtom
                    (G.mixedBlockProposal proposal b) edgeLabel
                    (G.mixedBlockLaw qLaw b)
                    (G.mixedBlockRealization proposal edgeLabel qLaw R b)
                    (G.fst e) left i)
                  (rightWord i) - mean i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro left _
          congr 1
          simpa only [hpoint, pR] using
            (G.sum_mixedBlockProbability_mul_decode
              proposal edgeLabel qLaw R omega (G.snd e) b
              (fun rightWord ↦
                (∑ i, (value i
                  (G.decodeMixedGraphAtom
                    (G.mixedBlockProposal proposal b) edgeLabel
                    (G.mixedBlockLaw qLaw b)
                    (G.mixedBlockRealization proposal edgeLabel qLaw R b)
                    (G.fst e) left i)
                  (rightWord i) - mean i)) ^ 2))
        _ = _ := by
          simpa only [pL, pR,
            FiniteCoordinateDependentWordMoments.wordMass] using
            (G.sum_mixedBlockProbability_mul_decode
              proposal edgeLabel qLaw R omega (G.fst e) b
              (fun leftWord ↦
                ∑ rightWord : RightWord,
                  (∏ i : Fin k, pR i (rightWord i)) *
                  (∑ i, (value i (leftWord i) (rightWord i) - mean i)) ^ 2))
    exact hpaddedEq.trans_le hmoment
  unfold mixedBlockVariance
  calc
    _ = G.weight e *
      (∑ left : G.MixedGraphPackedBlockState
          proposal edgeLabel qLaw R b,
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega (G.fst e) b left *
          ∑ right : G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b,
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega (G.snd e) b right *
              (G.mixedBlockOptionMass proposal edgeLabel qLaw R
                rho omega e b left right -
                G.mixedBlockTarget proposal rho s e b) ^ 2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro left _
      apply Finset.sum_congr rfl
      intro right _
      ring
    _ ≤ G.weight e * (∑ i : Fin k, U * mean i) :=
      mul_le_mul_of_nonneg_left hpadded (G.weight_pos e).le
    _ = G.weight e * (U * G.mixedBlockTarget proposal rho s e b) := by
      unfold mixedBlockTarget mean
      rw [← Finset.mul_sum, ← Finset.mul_sum]

end WeightedMultigraph

end
end WeightedEdgeColoring
