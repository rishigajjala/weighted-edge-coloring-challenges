import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockCapacityVarianceSelection

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

abbrev ColorDependentSelectedStates :=
  ∀ v (b : Fin B) (i : Fin k),
    G.ColorDependentExtendedProfileState R v (b, i)

def encodedColorDependentSelectedBlock
    (selected : G.ColorDependentSelectedStates proposal R)
    (source : G.V × Fin B) :
    G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r) :=
  G.encodeColorDependentExtendedProfileBlock proposal R source.1 source.2
    (selected source.1 source.2)

@[simp] theorem decode_encodedColorDependentSelectedBlock
    (selected : G.ColorDependentSelectedStates proposal R)
    (source : G.V × Fin B) (i : Fin k) :
    G.decodeColorDependentExtendedProfileBlock proposal R source
      (G.encodedColorDependentSelectedBlock proposal R selected source) i =
        selected source.1 source.2 i := by
  rcases source with ⟨v, b⟩
  unfold encodedColorDependentSelectedBlock
  exact congrFun
    (G.decode_encodeColorDependentExtendedProfileBlock proposal R
      v b (selected v b)) i

def selectedColorDependentLargeCandidateRow
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (slot : Fin (explicitLargeSlotBound β q r)) :
    G.ColorDependentLargeCandidateRow R c :=
  ⟨v, selected v c.1 c.2, slot⟩

def selectedColorDependentLargeCapacityRow
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (slot : Fin (explicitLargeSlotBound β q r)) :
    G.ColorDependentExtendedProfileCapacityRow
      (G.ColorDependentCandidateRowAt R) :=
  ⟨c, Sum.inl
    (G.selectedColorDependentLargeCandidateRow proposal R selected v c slot)⟩

def selectedColorDependentLargeCapacityLoad
    (rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (slot : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  ∑ source,
    G.colorDependentCandidateAtomUse proposal R rho omega
      source c (selected source c.1 c.2)
      (Sum.inl
        (G.selectedColorDependentLargeCandidateRow proposal R selected v c slot))

def selectedColorDependentTinyCandidateRow
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k) :
    G.ColorDependentTinyCandidateRow R c :=
  ⟨v, selected v c.1 c.2⟩

def selectedColorDependentTinyCapacityRow
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k) :
    G.ColorDependentExtendedProfileCapacityRow
      (G.ColorDependentCandidateRowAt R) :=
  ⟨c, Sum.inr
    (G.selectedColorDependentTinyCandidateRow proposal R selected v c)⟩

def selectedColorDependentTinyCapacityLoad
    (rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k) : ℝ :=
  ∑ source,
    G.colorDependentCandidateAtomUse proposal R rho omega
      source c (selected source c.1 c.2)
      (Sum.inr
        (G.selectedColorDependentTinyCandidateRow proposal R selected v c))

theorem rowLoad_selectedColorDependentLargeCapacityRow_eq
    (scale rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (slot : Fin (explicitLargeSlotBound β q r)) :
    FiniteCategoricalSelection.rowLoad
      (G.colorDependentBlockCandidateUse proposal R n scale rho omega)
      (G.selectedColorDependentLargeCapacityRow proposal R selected v c slot)
      (G.encodedColorDependentSelectedBlock proposal R selected) =
        (n : ℝ) * G.selectedColorDependentLargeCapacityLoad
          proposal R rho omega selected v c slot / scale := by
  classical
  unfold FiniteCategoricalSelection.rowLoad
    selectedColorDependentLargeCapacityRow
    selectedColorDependentLargeCapacityLoad
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ source,
        G.scaledColorDependentCandidateAtomUse proposal R n scale rho omega
          source c (selected source c.1 c.2)
          (Sum.inl
            (G.selectedColorDependentLargeCandidateRow
              proposal R selected v c slot)) := by
      apply Finset.sum_congr rfl
      intro source _hsource
      rw [Finset.sum_eq_single c.1]
      · simp [colorDependentBlockCandidateUse,
          encodedColorDependentSelectedBlock,
          G.decode_encodedColorDependentSelectedBlock]
      · intro b _hb hbc
        simp [colorDependentBlockCandidateUse, hbc]
      · simp
    _ = _ := by
      simp_rw [scaledColorDependentCandidateAtomUse]
      rw [← Finset.sum_div, ← Finset.mul_sum]

theorem rowLoad_selectedColorDependentTinyCapacityRow_eq
    (scale rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k) :
    FiniteCategoricalSelection.rowLoad
      (G.colorDependentBlockCandidateUse proposal R n scale rho omega)
      (G.selectedColorDependentTinyCapacityRow proposal R selected v c)
      (G.encodedColorDependentSelectedBlock proposal R selected) =
        (n : ℝ) * G.selectedColorDependentTinyCapacityLoad
          proposal R rho omega selected v c / scale := by
  classical
  unfold FiniteCategoricalSelection.rowLoad
    selectedColorDependentTinyCapacityRow
    selectedColorDependentTinyCapacityLoad
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ source,
        G.scaledColorDependentCandidateAtomUse proposal R n scale rho omega
          source c (selected source c.1 c.2)
          (Sum.inr
            (G.selectedColorDependentTinyCandidateRow proposal R selected v c)) := by
      apply Finset.sum_congr rfl
      intro source _hsource
      rw [Finset.sum_eq_single c.1]
      · simp [colorDependentBlockCandidateUse,
          encodedColorDependentSelectedBlock,
          G.decode_encodedColorDependentSelectedBlock]
      · intro b _hb hbc
        simp [colorDependentBlockCandidateUse, hbc]
      · simp
    _ = _ := by
      simp_rw [scaledColorDependentCandidateAtomUse]
      rw [← Finset.sum_div, ← Finset.mul_sum]

theorem selectedColorDependentLargeCapacityLoad_lt
    (hn : 0 < n) (scale rho omega deviation : ℝ) (hscale : 0 < scale)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (slot : Fin (explicitLargeSlotBound β q r))
    (hrow :
      FiniteCategoricalSelection.rowLoad
        (G.colorDependentBlockCandidateUse proposal R n scale rho omega)
        (G.selectedColorDependentLargeCapacityRow proposal R selected v c slot)
        (G.encodedColorDependentSelectedBlock proposal R selected) <
          (n : ℝ) * (rho / (1 - omega)) / scale + deviation) :
    G.selectedColorDependentLargeCapacityLoad proposal R rho omega
        selected v c slot <
      rho / (1 - omega) + scale / (n : ℝ) * deviation := by
  rw [G.rowLoad_selectedColorDependentLargeCapacityRow_eq
    proposal R scale rho omega selected v c slot] at hrow
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let base := rho / (1 - omega)
  have hrow' :
      (n : ℝ) * G.selectedColorDependentLargeCapacityLoad
          proposal R rho omega selected v c slot / scale <
        ((n : ℝ) * base + scale * deviation) / scale := by
    calc
      _ < (n : ℝ) * base / scale + deviation := hrow
      _ = ((n : ℝ) * base + scale * deviation) / scale := by
        field_simp
        <;> ring
  have hnum := (div_lt_div_iff_of_pos_right hscale).1 hrow'
  have hnum' :
      G.selectedColorDependentLargeCapacityLoad proposal R rho omega
          selected v c slot * (n : ℝ) <
        (n : ℝ) * base + scale * deviation := by
    simpa [mul_comm] using hnum
  calc
    _ < ((n : ℝ) * base + scale * deviation) / (n : ℝ) :=
      (lt_div_iff₀ hnR).2 hnum'
    _ = _ := by
      unfold base
      field_simp
      <;> ring

theorem selectedColorDependentTinyCapacityLoad_lt
    (hn : 0 < n) (scale rho omega deviation : ℝ) (hscale : 0 < scale)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (hrow :
      FiniteCategoricalSelection.rowLoad
        (G.colorDependentBlockCandidateUse proposal R n scale rho omega)
        (G.selectedColorDependentTinyCapacityRow proposal R selected v c)
        (G.encodedColorDependentSelectedBlock proposal R selected) <
          (n : ℝ) * (rho *
            G.colorDependentExtendedProfileReservoirSize R v c
              (selected v c.1 c.2) / (1 - omega)) / scale + deviation) :
    G.selectedColorDependentTinyCapacityLoad proposal R rho omega selected v c <
      rho * G.colorDependentExtendedProfileReservoirSize R v c
          (selected v c.1 c.2) / (1 - omega) +
        scale / (n : ℝ) * deviation := by
  rw [G.rowLoad_selectedColorDependentTinyCapacityRow_eq
    proposal R scale rho omega selected v c] at hrow
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let base := rho * G.colorDependentExtendedProfileReservoirSize R v c
    (selected v c.1 c.2) / (1 - omega)
  have hrow' :
      (n : ℝ) * G.selectedColorDependentTinyCapacityLoad
          proposal R rho omega selected v c / scale <
        ((n : ℝ) * base + scale * deviation) / scale := by
    calc
      _ < (n : ℝ) * base / scale + deviation := hrow
      _ = ((n : ℝ) * base + scale * deviation) / scale := by
        field_simp
        <;> ring
  have hnum := (div_lt_div_iff_of_pos_right hscale).1 hrow'
  have hnum' :
      G.selectedColorDependentTinyCapacityLoad proposal R rho omega
          selected v c * (n : ℝ) <
        (n : ℝ) * base + scale * deviation := by
    simpa [mul_comm] using hnum
  calc
    _ < ((n : ℝ) * base + scale * deviation) / (n : ℝ) :=
      (lt_div_iff₀ hnR).2 hnum'
    _ = _ := by
      unfold base
      field_simp
      <;> ring

end WeightedMultigraph

end


end WeightedEdgeColoring
