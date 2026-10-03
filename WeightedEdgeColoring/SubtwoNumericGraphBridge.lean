import WeightedEdgeColoring.SubtwoInterpolatedPotential
import WeightedEdgeColoring.SubtwoGraphEndpointCertificate
import WeightedEdgeColoring.SubtwoPriceRelabel

/-! Transport the ten-coordinate endpoint witness to a five-vertex multigraph. -/

namespace WeightedEdgeColoring.Subtwo.NumericGraphBridge

open EndpointPotential
open GraphEndpoint

universe u

variable (G : WeightedMultigraph.{u})

noncomputable def canonicalBundle (label : G.V → Vertex)
    (hinj : Function.Injective label) (e : G.E) : Bundle :=
  PriceRelabel.pairIndex (label (G.fst e)) (label (G.snd e))
    (fun he ↦ G.noLoop e (hinj he))

private theorem pairIndex_ends (u v : Vertex) (huv : u ≠ v) :
    (left (PriceRelabel.pairIndex u v huv) = u ∧
      right (PriceRelabel.pairIndex u v huv) = v) ∨
    (left (PriceRelabel.pairIndex u v huv) = v ∧
      right (PriceRelabel.pairIndex u v huv) = u) := by
  let e := PriceRelabel.pairIndex u v huv
  have hp : ({left e, right e} : Finset Vertex) = {u, v} := by
    rw [← PriceRelabel.edge_eq_endpoints]
    exact PriceRelabel.edge_pairIndex u v huv
  have hl : left e = u ∨ left e = v := by
    have hm : left e ∈ ({u, v} : Finset Vertex) := by rw [← hp]; simp
    simpa using hm
  have hr : right e = u ∨ right e = v := by
    have hm : right e ∈ ({u, v} : Finset Vertex) := by rw [← hp]; simp
    simpa using hm
  rcases hl with hl | hl
  · rcases hr with hr | hr
    · exact False.elim (PriceRelabel.left_ne_right e (hl.trans hr.symm))
    · exact Or.inl ⟨hl, hr⟩
  · rcases hr with hr | hr
    · exact Or.inr ⟨hl, hr⟩
    · exact False.elim (PriceRelabel.left_ne_right e (hl.trans hr.symm))

theorem canonicalBundle_ends (label : G.V → Vertex)
    (hinj : Function.Injective label) (e : G.E) :
    (label (G.fst e) = left (canonicalBundle G label hinj e) ∧
      label (G.snd e) = right (canonicalBundle G label hinj e)) ∨
    (label (G.fst e) = right (canonicalBundle G label hinj e) ∧
      label (G.snd e) = left (canonicalBundle G label hinj e)) := by
  rcases pairIndex_ends (label (G.fst e)) (label (G.snd e))
    (fun he ↦ G.noLoop e (hinj he)) with h | h
  · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · exact Or.inr ⟨h.2.symm, h.1.symm⟩

theorem canonicalBundle_shared (label : G.V → Vertex)
    (hinj : Function.Injective label) (e f : G.E)
    (hs : GraphEndpoint.Shared G e f) :
    canonicalBundle G label hinj f = canonicalBundle G label hinj e := by
  apply TwoModelGeometry.edge_injective
  simp only [canonicalBundle, PriceRelabel.edge_pairIndex]
  rcases hs with ⟨hf, ht⟩
  rcases hf with hf | hf <;> rcases ht with ht | ht
  · exfalso
    exact G.noLoop e (hf.symm.trans ht)
  · simp [hf, ht]
  · simp [hf, ht, Finset.pair_comm]
  · exfalso
    exact G.noLoop e (hf.symm.trans ht)

private theorem inc_iff (label : G.V → Vertex) (hinj : Function.Injective label)
    (bundle : G.E → Bundle)
    (hends : ∀ e,
      (label (G.fst e) = left (bundle e) ∧ label (G.snd e) = right (bundle e)) ∨
      (label (G.fst e) = right (bundle e) ∧ label (G.snd e) = left (bundle e)))
    (v : G.V) (e : G.E) :
    G.Inc v e ↔ EndpointPotential.Inc (label v) (bundle e) := by
  constructor
  · intro hv
    rcases hends e with h | h
    · rcases hv with hv | hv
      · exact Or.inl (hv ▸ h.1)
      · exact Or.inr (hv ▸ h.2)
    · rcases hv with hv | hv
      · exact Or.inr (hv ▸ h.1)
      · exact Or.inl (hv ▸ h.2)
  · intro hv
    rcases hends e with h | h
    · rcases hv with hv | hv
      · exact Or.inl (hinj (hv.trans h.1.symm)).symm
      · exact Or.inr (hinj (hv.trans h.2.symm)).symm
    · rcases hv with hv | hv
      · exact Or.inr (hinj (hv.trans h.2.symm)).symm
      · exact Or.inl (hinj (hv.trans h.1.symm)).symm

noncomputable def lift (label : G.V → Vertex) (hinj : Function.Injective label)
    (bundle : G.E → Bundle)
    (hends : ∀ e,
      (label (G.fst e) = left (bundle e) ∧ label (G.snd e) = right (bundle e)) ∨
      (label (G.fst e) = right (bundle e) ∧ label (G.snd e) = left (bundle e)))
    (hbundle : ∀ e f, GraphEndpoint.Shared G e f → bundle f = bundle e)
    {m rho : Bundle → ℝ} {h : Vertex → ℝ}
    (C : EndpointPotential.Certificate m rho h)
    (hm : ∀ e, 0 ≤ m e) (hr0 : ∀ e, 0 ≤ rho e)
    (hr2 : ∀ e, rho e ≤ 2) (hh : ∀ v, 0 ≤ h v) :
    GraphEndpoint.Certificate G (fun e ↦ m (bundle e)) where
  rho := fun e ↦ rho (bundle e)
  h := fun v ↦ h (label v)
  z := fun v e ↦ C.z (label v) (bundle e)
  c := fun v ↦ C.c (label v)
  alpha := fun v e ↦ C.alpha (label v) (bundle e)
  P := fun v ↦ C.P (label v)
  cap_nonneg := by intro e; exact hm _
  cap_same := by intro e f hs; rw [hbundle e f hs]
  z_same := by intro v e f hs; rw [hbundle e f hs]
  rho_nonneg := by intro e; exact hr0 _
  rho_le_two := by intro e; exact hr2 _
  h_nonneg := by intro v; exact hh _
  z_nonneg := by intro v e; exact C.z_nonneg _ _
  c_nonneg := by intro v; exact C.c_nonneg _
  alpha_nonneg := by intro v e; exact C.alpha_nonneg _ _
  P_nonneg := by intro v; exact C.P_nonneg _
  split := by
    intro e
    rcases hends e with h | h
    · simpa [h.1, h.2] using C.split (bundle e)
    · simpa [h.1, h.2, add_comm] using C.split (bundle e)
  light := by
    intro v e hv
    exact C.light _ _ ((inc_iff G label hinj bundle hends v e).mp hv)
  baseline := by
    intro v
    exact C.baseline (label v)
  off := by
    intro v e f he hf hnot
    have hbf : bundle f ≠ bundle e := by
      intro heq
      apply hnot
      constructor
      · apply (inc_iff G label hinj bundle hends (G.fst e) f).mpr
        rw [heq]
        exact (inc_iff G label hinj bundle hends (G.fst e) e).mp (Or.inl rfl)
      · apply (inc_iff G label hinj bundle hends (G.snd e) f).mpr
        rw [heq]
        exact (inc_iff G label hinj bundle hends (G.snd e) e).mp (Or.inr rfl)
    exact C.off _ _ _ ((inc_iff G label hinj bundle hends v e).mp he)
      ((inc_iff G label hinj bundle hends v f).mp hf) hbf
  same := by
    intro v e hv
    exact C.same _ _ ((inc_iff G label hinj bundle hends v e).mp hv)
  pair := by
    intro e
    rcases hends e with h | h
    · simpa [h.1, h.2] using C.pair (bundle e)
    · simpa [h.1, h.2, add_comm] using C.pair (bundle e)
  edge := by
    intro e
    rcases hends e with h | h
    · simpa [h.1, h.2] using C.edge (bundle e)
    · simpa [h.1, h.2, add_comm] using C.edge (bundle e)

theorem lift_budget_le (label : G.V → Vertex) (hinj : Function.Injective label)
    (bundle : G.E → Bundle)
    (hends : ∀ e,
      (label (G.fst e) = left (bundle e) ∧ label (G.snd e) = right (bundle e)) ∨
      (label (G.fst e) = right (bundle e) ∧ label (G.snd e) = left (bundle e)))
    (hbundle : ∀ e f, GraphEndpoint.Shared G e f → bundle f = bundle e)
    {m rho : Bundle → ℝ} {h : Vertex → ℝ}
    (C : EndpointPotential.Certificate m rho h)
    (hm : ∀ e, 0 ≤ m e) (hr0 : ∀ e, 0 ≤ rho e)
    (hr2 : ∀ e, rho e ≤ 2) (hh : ∀ v, 0 ≤ h v) :
    ∑ v, (lift G label hinj bundle hends hbundle C hm hr0 hr2 hh).P v ≤
      ∑ v, C.P v := by
  change ∑ v, C.P (label v) ≤ ∑ v, C.P v
  calc
    _ = ∑ w ∈ (Finset.univ : Finset G.V).image label, C.P w := by
      rw [Finset.sum_image (by intro v _ w _ heq; exact hinj heq)]
    _ ≤ ∑ w, C.P w := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (by intro w _ _; exact C.P_nonneg w)

private theorem model_cap_nonneg (a x y : ℝ)
    (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1)
    (hsy : 1-a ≤ y) (hyx : y ≤ x) (hxa : x ≤ a) :
    ∀ e, 0 ≤ TwoModelGeometry.M a x y e := by
  intro e
  fin_cases e <;> simp [TwoModelGeometry.M] <;> linarith

private theorem model_rho_nonneg (a : ℝ)
    (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1) :
    ∀ e, 0 ≤ uniformStarRho a e := by
  intro e
  fin_cases e <;> simp [uniformStarRho] <;>
    try { norm_num }
  change 0 ≤ 2*(1-a)/(3*a)
  exact div_nonneg (by nlinarith) (by positivity)

private theorem model_rho_le_two (a : ℝ)
    (ha : (1/2:ℝ) < a) (_ha1 : a ≤ 1) :
    ∀ e, uniformStarRho a e ≤ 2 := by
  intro e
  fin_cases e <;> simp [uniformStarRho] <;>
    try { norm_num }
  change 2*(1-a)/(3*a) ≤ 2
  apply (div_le_iff₀ (by positivity : 0 < 3*a)).mpr
  nlinarith

private theorem model_h_nonneg (a : ℝ) (ha : (1/2:ℝ) < a) :
    ∀ v, 0 ≤ uniformStarH a v := by
  intro v
  fin_cases v <;> simp [uniformStarH]
  all_goals
    change 0 ≤ (2*a-1)/(3*a)
    exact div_nonneg (by nlinarith) (by positivity)

noncomputable def uniformModel_graphCertificate
    (label : G.V → Vertex) (hinj : Function.Injective label)
    (bundle : G.E → Bundle)
    (hends : ∀ e,
      (label (G.fst e) = left (bundle e) ∧ label (G.snd e) = right (bundle e)) ∨
      (label (G.fst e) = right (bundle e) ∧ label (G.snd e) = left (bundle e)))
    (hbundle : ∀ e f, GraphEndpoint.Shared G e f → bundle f = bundle e)
    (a x y : ℝ) (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1)
    (hsy : 1-a ≤ y) (hyx : y ≤ x) (hxa : x ≤ a) :
    GraphEndpoint.Certificate G (fun e ↦ TwoModelGeometry.M a x y (bundle e)) :=
  lift G label hinj bundle hends hbundle
    (uniformModel_certificate a x y ha ha1 hsy hyx hxa)
    (model_cap_nonneg a x y ha ha1 hsy hyx hxa)
    (model_rho_nonneg a ha ha1)
    (model_rho_le_two a ha ha1)
    (model_h_nonneg a ha)

theorem uniformModel_graphBudget
    (label : G.V → Vertex) (hinj : Function.Injective label)
    (bundle : G.E → Bundle)
    (hends : ∀ e,
      (label (G.fst e) = left (bundle e) ∧ label (G.snd e) = right (bundle e)) ∨
      (label (G.fst e) = right (bundle e) ∧ label (G.snd e) = left (bundle e)))
    (hbundle : ∀ e f, GraphEndpoint.Shared G e f → bundle f = bundle e)
    (a x y : ℝ) (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1)
    (hsy : 1-a ≤ y) (hyx : y ≤ x) (hxa : x ≤ a) :
    ∑ v, (uniformModel_graphCertificate G label hinj bundle hends hbundle
      a x y ha ha1 hsy hyx hxa).P v ≤ (157/40:ℝ) := by
  exact (lift_budget_le G label hinj bundle hends hbundle
      (uniformModel_certificate a x y ha ha1 hsy hyx hxa)
      (model_cap_nonneg a x y ha ha1 hsy hyx hxa)
      (model_rho_nonneg a ha ha1)
      (model_rho_le_two a ha ha1)
      (model_h_nonneg a ha)).trans
    (uniformModel_budget a x y ha ha1 hsy hyx hxa)

noncomputable def canonicalGraphCertificate
    (label : G.V → Vertex) (hinj : Function.Injective label)
    (a x y : ℝ) (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1)
    (hsy : 1-a ≤ y) (hyx : y ≤ x) (hxa : x ≤ a) :
    GraphEndpoint.Certificate G
      (fun e ↦ TwoModelGeometry.M a x y (canonicalBundle G label hinj e)) :=
  uniformModel_graphCertificate G label hinj (canonicalBundle G label hinj)
    (canonicalBundle_ends G label hinj)
    (canonicalBundle_shared G label hinj)
    a x y ha ha1 hsy hyx hxa

theorem canonicalGraphBudget
    (label : G.V → Vertex) (hinj : Function.Injective label)
    (a x y : ℝ) (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1)
    (hsy : 1-a ≤ y) (hyx : y ≤ x) (hxa : x ≤ a) :
    ∑ v, (canonicalGraphCertificate G label hinj
      a x y ha ha1 hsy hyx hxa).P v ≤ (157/40:ℝ) := by
  exact uniformModel_graphBudget G label hinj (canonicalBundle G label hinj)
    (canonicalBundle_ends G label hinj)
    (canonicalBundle_shared G label hinj)
    a x y ha ha1 hsy hyx hxa

end WeightedEdgeColoring.Subtwo.NumericGraphBridge
