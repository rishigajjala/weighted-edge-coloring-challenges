import WeightedEdgeColoring.SubtwoEndpointPotential
import WeightedEdgeColoring.SubtwoTwoModelGeometry
import WeightedEdgeColoring.SubtwoLoadOrder
import Mathlib.Tactic

/-! Transport endpoint certificates through permutations of the five vertices. -/

namespace WeightedEdgeColoring.Subtwo.PriceRelabel

open EndpointPotential TwoModelGeometry

theorem edge_surjective_pairs :
    ∀ s : Finset (Fin 5), s.card = 2 → ∃ e : Bundle, edge e = s := by
  decide

noncomputable def edgeEquiv : Bundle ≃ {s : Finset (Fin 5) // s.card = 2} :=
  Equiv.ofBijective
    (fun e => (⟨edge e, edge_card_two e⟩ : {s : Finset (Fin 5) // s.card = 2}))
    ⟨fun e f h => edge_injective (congrArg Subtype.val h),
      fun s => by
        obtain ⟨e, he⟩ := edge_surjective_pairs s.1 s.2
        exact ⟨e, Subtype.ext he⟩⟩

noncomputable def edgeMap (π : Equiv.Perm (Fin 5)) (e : Bundle) : Bundle :=
  edgeEquiv.symm ⟨(edge e).map π.toEmbedding, by
    rw [Finset.card_map]
    exact edge_card_two e⟩

theorem edge_edgeMap (π : Equiv.Perm (Fin 5)) (e : Bundle) :
    edge (edgeMap π e) = (edge e).map π.toEmbedding := by
  exact congrArg Subtype.val (edgeEquiv.apply_symm_apply _)

theorem edgeMap_injective (π : Equiv.Perm (Fin 5)) :
    Function.Injective (edgeMap π) := by
  intro e f hef
  apply edge_injective
  have h := congrArg edge hef
  rw [edge_edgeMap, edge_edgeMap] at h
  exact (Finset.map_injective π.toEmbedding) h

noncomputable def edgePerm (π : Equiv.Perm (Fin 5)) : Equiv.Perm Bundle :=
  Equiv.ofBijective (edgeMap π)
    ⟨edgeMap_injective π,
      (Finite.injective_iff_surjective).mp (edgeMap_injective π)⟩

theorem edge_eq_endpoints (e : Bundle) :
    edge e = {left e, right e} := by
  fin_cases e <;> decide

theorem left_ne_right (e : Bundle) : left e ≠ right e := by
  fin_cases e <;> decide

theorem inc_iff_mem (v : Vertex) (e : Bundle) :
    Inc v e ↔ v ∈ edge e := by
  rw [edge_eq_endpoints]
  simp [Inc]

theorem edge_edgePerm (π : Equiv.Perm (Fin 5)) (e : Bundle) :
    edge (edgePerm π e) = (edge e).map π.toEmbedding :=
  edge_edgeMap π e

theorem edgePerm_symm_apply (π : Equiv.Perm (Fin 5)) (e : Bundle) :
    edgePerm π.symm (edgePerm π e) = e := by
  apply edge_injective
  rw [edge_edgePerm, edge_edgePerm]
  ext v
  simp

theorem edgePerm_apply_symm (π : Equiv.Perm (Fin 5)) (e : Bundle) :
    edgePerm π (edgePerm π.symm e) = e := by
  simpa using edgePerm_symm_apply π.symm e

theorem inc_relabel (π : Equiv.Perm (Fin 5)) (v : Vertex) (e : Bundle) :
    Inc (π v) (edgePerm π e) ↔ Inc v e := by
  rw [inc_iff_mem, edge_edgePerm, Finset.mem_map, inc_iff_mem]
  simp

theorem endpoints_relabel (π : Equiv.Perm (Fin 5)) (e : Bundle) :
    ({π.symm (left e), π.symm (right e)} : Finset Vertex) =
      {left (edgePerm π.symm e), right (edgePerm π.symm e)} := by
  have he := edge_edgePerm π.symm e
  rw [edge_eq_endpoints, edge_eq_endpoints] at he
  simpa using he.symm

private theorem sum_two_of_pair_eq {α β : Type*} [DecidableEq α]
    [AddCommMonoid β] (u v x y : α) (f : α → β)
    (huv : u ≠ v) (hxy : x ≠ y)
    (hpair : ({u, v} : Finset α) = {x, y}) :
    f u + f v = f x + f y := by
  have h := congrArg (fun s : Finset α => ∑ t ∈ s, f t) hpair
  simpa [Finset.sum_pair, huv, hxy] using h

theorem endpoint_sum_relabel (π : Equiv.Perm (Fin 5)) (e : Bundle)
    (f : Vertex → ℝ) :
    f (π.symm (left e)) + f (π.symm (right e)) =
      f (left (edgePerm π.symm e)) + f (right (edgePerm π.symm e)) := by
  apply sum_two_of_pair_eq
  · intro he
    exact left_ne_right e (π.symm.injective he)
  · exact left_ne_right _
  · exact endpoints_relabel π e

noncomputable def permutePrices (π : Equiv.Perm (Fin 5)) (m : Bundle → ℝ) : Bundle → ℝ :=
  fun e => m (edgePerm π.symm e)

def permuteVertices (π : Equiv.Perm (Fin 5)) (h : Vertex → ℝ) : Vertex → ℝ :=
  fun v => h (π.symm v)

noncomputable def transport (π : Equiv.Perm (Fin 5))
    {m rho : Bundle → ℝ} {h : Vertex → ℝ}
    (C : Certificate m rho h) :
    Certificate (permutePrices π m) (permutePrices π rho)
      (permuteVertices π h) where
  z := fun v e => C.z (π.symm v) (edgePerm π.symm e)
  c := fun v => C.c (π.symm v)
  alpha := fun v e => C.alpha (π.symm v) (edgePerm π.symm e)
  P := fun v => C.P (π.symm v)
  z_nonneg := fun v e => C.z_nonneg _ _
  c_nonneg := fun v => C.c_nonneg _
  alpha_nonneg := fun v e => C.alpha_nonneg _ _
  P_nonneg := fun v => C.P_nonneg _
  split := by
    intro e
    let e' := edgePerm π.symm e
    have heq := endpoint_sum_relabel π e (fun v => C.z v e')
    simpa [permutePrices, e'] using heq.trans (C.split e')
  light := by
    intro v e hve
    have hv' : Inc (π.symm v) (edgePerm π.symm e) :=
      (inc_relabel π.symm v e).2 hve
    simpa [permutePrices, permuteVertices] using C.light _ _ hv'
  baseline := by
    intro v
    simpa [permuteVertices] using C.baseline (π.symm v)
  off := by
    intro v e f hve hvf hfe
    have hve' : Inc (π.symm v) (edgePerm π.symm e) :=
      (inc_relabel π.symm v e).2 hve
    have hvf' : Inc (π.symm v) (edgePerm π.symm f) :=
      (inc_relabel π.symm v f).2 hvf
    have hef' : edgePerm π.symm f ≠ edgePerm π.symm e := by
      intro heq
      exact hfe ((edgePerm π.symm).injective heq)
    simpa [permutePrices] using C.off _ _ _ hve' hvf' hef'
  same := by
    intro v e hve
    have hv' : Inc (π.symm v) (edgePerm π.symm e) :=
      (inc_relabel π.symm v e).2 hve
    simpa [permutePrices] using C.same _ _ hv'
  pair := by
    intro e
    let e' := edgePerm π.symm e
    have heq := endpoint_sum_relabel π e (fun v => C.alpha v e')
    simpa [permutePrices, e'] using (C.pair e').trans_eq heq.symm
  edge := by
    intro e
    let e' := edgePerm π.symm e
    have hα := endpoint_sum_relabel π e (fun v => C.alpha v e')
    have hP := endpoint_sum_relabel π e C.P
    have hrow := C.edge e'
    dsimp [permutePrices, e']
    rw [hα, hP]
    exact hrow

theorem transport_budget (π : Equiv.Perm (Fin 5))
    {m rho : Bundle → ℝ} {h : Vertex → ℝ}
    (C : Certificate m rho h) :
    (∑ v, (transport π C).P v) = ∑ v, C.P v := by
  simpa [transport] using (Equiv.sum_comp π.symm C.P)

theorem majorant_transport (π : Equiv.Perm Vertex)
    (p m : Bundle → ℝ)
    (hbound : ∀ e : Bundle, permutePrices π.symm p e ≤ m e) :
    ∀ e : Bundle, p e ≤ permutePrices π m e := by
  intro e
  have h := hbound (edgePerm π.symm e)
  simpa [permutePrices, edgePerm_apply_symm] using h

def lift4 (τ : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 5) where
  toFun := Fin.cases 0 (fun i => Fin.succ (τ i))
  invFun := Fin.cases 0 (fun i => Fin.succ (τ.symm i))
  left_inv := by
    intro v
    cases v using Fin.cases with
    | zero => rfl
    | succ i => simp
  right_inv := by
    intro v
    cases v using Fin.cases with
    | zero => rfl
    | succ i => simp

theorem lift4_zero (τ : Equiv.Perm (Fin 4)) : lift4 τ 0 = 0 := rfl
theorem lift4_succ (τ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    lift4 τ (Fin.succ i) = Fin.succ (τ i) := rfl

def rootedPerm (v : Vertex) (τ : Equiv.Perm (Fin 4)) : Equiv.Perm Vertex :=
  (lift4 τ).trans (Equiv.swap 0 v)

theorem rootedPerm_zero (v : Vertex) (τ : Equiv.Perm (Fin 4)) :
    rootedPerm v τ 0 = v := by
  simp [rootedPerm, Equiv.trans_apply, lift4_zero]

theorem rootedPerm_succ (v : Vertex) (τ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    rootedPerm v τ (Fin.succ i) = (Equiv.swap 0 v) (Fin.succ (τ i)) := by
  simp [rootedPerm, Equiv.trans_apply, lift4_succ]

noncomputable def pairIndex (u v : Vertex) (huv : u ≠ v) : Bundle :=
  edgeEquiv.symm ⟨{u, v}, by simp [huv]⟩

theorem edge_pairIndex (u v : Vertex) (huv : u ≠ v) :
    edge (pairIndex u v huv) = {u, v} := by
  exact congrArg Subtype.val (edgeEquiv.apply_symm_apply _)

theorem pairIndex_symm (u v : Vertex) (huv : u ≠ v) :
    pairIndex u v huv = pairIndex v u (Ne.symm huv) := by
  apply edge_injective
  simp [edge_pairIndex, Finset.pair_comm]

theorem edgePerm_pairIndex (π : Equiv.Perm Vertex) (u v : Vertex)
    (huv : u ≠ v) :
    edgePerm π (pairIndex u v huv) =
      pairIndex (π u) (π v) (fun h => huv (π.injective h)) := by
  apply edge_injective
  rw [edge_edgePerm, edge_pairIndex, edge_pairIndex]
  simp

theorem exists_four_sorted (w : Fin 4 → ℝ) :
    ∃ τ : Equiv.Perm (Fin 4),
      w (τ 3) ≤ w (τ 2) ∧ w (τ 2) ≤ w (τ 1) ∧
      w (τ 1) ≤ w (τ 0) := by
  classical
  obtain ⟨τ, hmax, h21, h31⟩ :=
    WeightedEdgeColoring.SubtwoHarmonicRanks.exists_four_load_order w
  by_cases h23 : w (τ 3) ≤ w (τ 2)
  · exact ⟨τ, h23, h21, hmax (τ 1)⟩
  · let σ : Equiv.Perm (Fin 4) := (Equiv.swap 2 3).trans τ
    have hswap0 : (Equiv.swap (2 : Fin 4) 3) 0 = 0 := by decide
    have hswap1 : (Equiv.swap (2 : Fin 4) 3) 1 = 1 := by decide
    have hσ0 : σ 0 = τ 0 := by simp [σ, Equiv.trans_apply, hswap0]
    have hσ1 : σ 1 = τ 1 := by simp [σ, Equiv.trans_apply, hswap1]
    have hσ2 : σ 2 = τ 3 := by simp [σ, Equiv.trans_apply]
    have hσ3 : σ 3 = τ 2 := by simp [σ, Equiv.trans_apply]
    refine ⟨σ, ?_, ?_, ?_⟩
    · rw [hσ3, hσ2]; exact le_of_not_ge h23
    · rw [hσ2, hσ1]; exact h31
    · rw [hσ1, hσ0]; exact hmax (τ 1)

def starEdge : Fin 4 → Bundle := ![0, 1, 2, 3]

theorem edge_starEdge (i : Fin 4) :
    edge (starEdge i) = {0, Fin.succ i} := by
  fin_cases i <;> decide

noncomputable def spokeWeight (p : Bundle → ℝ) (v : Vertex) (i : Fin 4) : ℝ :=
  let σ : Equiv.Perm Vertex := Equiv.swap 0 v
  p (pairIndex (σ 0) (σ (Fin.succ i)) (by
    intro h
    have hh := σ.injective h
    exact Fin.succ_ne_zero i hh.symm))

theorem rooted_star_spoke (p : Bundle → ℝ) (v : Vertex)
    (τ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    permutePrices (rootedPerm v τ).symm p (starEdge i) =
      spokeWeight p v (τ i) := by
  unfold permutePrices spokeWeight
  simp only [Equiv.symm_symm]
  apply congrArg p
  apply edge_injective
  rw [edge_edgePerm, edge_starEdge, edge_pairIndex]
  simp [rootedPerm_zero, rootedPerm_succ]

theorem exists_star_sorted (p : Bundle → ℝ) (v : Vertex) :
    ∃ π : Equiv.Perm Vertex, π 0 = v ∧
      let p' := permutePrices π.symm p
      p' 3 ≤ p' 2 ∧ p' 2 ≤ p' 1 ∧ p' 1 ≤ p' 0 := by
  obtain ⟨τ, h32, h21, h10⟩ := exists_four_sorted (spokeWeight p v)
  refine ⟨rootedPerm v τ, rootedPerm_zero v τ, ?_⟩
  have he0 : permutePrices (rootedPerm v τ).symm p 0 =
      spokeWeight p v (τ 0) := by
    simpa [starEdge] using rooted_star_spoke p v τ 0
  have he1 : permutePrices (rootedPerm v τ).symm p 1 =
      spokeWeight p v (τ 1) := by
    simpa [starEdge] using rooted_star_spoke p v τ 1
  have he2 : permutePrices (rootedPerm v τ).symm p 2 =
      spokeWeight p v (τ 2) := by
    simpa [starEdge] using rooted_star_spoke p v τ 2
  have he3 : permutePrices (rootedPerm v τ).symm p 3 =
      spokeWeight p v (τ 3) := by
    simpa [starEdge] using rooted_star_spoke p v τ 3
  constructor
  · rw [he3, he2]; exact h32
  constructor
  · rw [he2, he1]; exact h21
  · rw [he1, he0]; exact h10

theorem exists_perm_three (u v w : Vertex)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∃ π : Equiv.Perm Vertex, π 0 = u ∧ π 1 = v ∧ π 2 = w := by
  let σ₀ : Equiv.Perm Vertex := Equiv.swap 0 u
  let t : Vertex := σ₀.symm v
  have ht0 : t ≠ 0 := by
    intro h
    have hh : v = u := by
      calc v = σ₀ t := (σ₀.apply_symm_apply v).symm
        _ = σ₀ 0 := congrArg σ₀ h
        _ = u := by simp [σ₀]
    exact huv hh.symm
  let σ₁ : Equiv.Perm Vertex := Equiv.swap 1 t
  have hσ₁0 : σ₁ 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm ht0)
  let τ : Equiv.Perm Vertex := σ₁.trans σ₀
  have hτ0 : τ 0 = u := by simp [τ, Equiv.trans_apply, hσ₁0, σ₀]
  have hτ1 : τ 1 = v := by
    simp [τ, Equiv.trans_apply, σ₁, t]
  let k : Vertex := τ.symm w
  have hk0 : k ≠ 0 := by
    intro h
    apply huw
    calc u = τ 0 := hτ0.symm
      _ = τ k := congrArg τ h.symm
      _ = w := τ.apply_symm_apply w
  have hk1 : k ≠ 1 := by
    intro h
    apply hvw
    calc v = τ 1 := hτ1.symm
      _ = τ k := congrArg τ h.symm
      _ = w := τ.apply_symm_apply w
  let σ₂ : Equiv.Perm Vertex := Equiv.swap 2 k
  have hσ₂0 : σ₂ 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hk0)
  have hσ₂1 : σ₂ 1 = 1 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hk1)
  refine ⟨σ₂.trans τ, ?_, ?_, ?_⟩
  · simp [Equiv.trans_apply, hσ₂0, hτ0]
  · simp [Equiv.trans_apply, hσ₂1, hτ1]
  · simp [Equiv.trans_apply, σ₂, k]

theorem disjoint_edgePerm (π : Equiv.Perm Vertex) (e f : Bundle)
    (hdis : Disjoint (edge e) (edge f)) :
    Disjoint (edge (edgePerm π e)) (edge (edgePerm π f)) := by
  rw [edge_edgePerm, edge_edgePerm]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨u, hu, hux⟩ := Finset.mem_map.mp hx
  obtain ⟨v, hv, hvx⟩ := Finset.mem_map.mp hy
  have huv : u = v := π.injective (hux.trans hvx.symm)
  exact (Finset.disjoint_left.mp hdis) hu (huv ▸ hv)

theorem permute_disjoint_price (π : Equiv.Perm Vertex) (p : Bundle → ℝ)
    (hdisjoint : ∀ e f : Bundle,
      Disjoint (edge e) (edge f) → p e + p f ≤ 1) :
    ∀ e f : Bundle,
      Disjoint (edge e) (edge f) →
        permutePrices π.symm p e + permutePrices π.symm p f ≤ 1 := by
  intro e f hef
  exact hdisjoint _ _ (disjoint_edgePerm π e f hef)

theorem star_core_low (π : Equiv.Perm Vertex) (p : Bundle → ℝ)
    (hroot : ∀ e : Bundle, (1 / 2 : ℝ) < p e → π 0 ∈ edge e) :
    ∀ e : Bundle, 4 ≤ e.val → permutePrices π.symm p e ≤ 1 / 2 := by
  intro e he
  by_contra h
  have hp : (1 / 2 : ℝ) < p (edgePerm π e) := by
    simpa [permutePrices] using lt_of_not_ge h
  have hv : π 0 ∈ edge (edgePerm π e) := hroot _ hp
  have hi : Inc 0 e := (inc_relabel π 0 e).mp ((inc_iff_mem _ _).2 hv)
  have hno : ∀ f : Bundle, 4 ≤ f.val → ¬Inc 0 f := by decide
  exact (hno e he) hi

theorem exists_star_model_cover (p : Bundle → ℝ)
    (hdisjoint : ∀ e f : Bundle,
      Disjoint (edge e) (edge f) → p e + p f ≤ 1)
    (hstar : ∃ v : Vertex, ∀ e : Bundle,
      (1 / 2 : ℝ) < p e → v ∈ edge e)
    (hne : ∃ e : Bundle, (1 / 2 : ℝ) < p e) :
    ∃ π : Equiv.Perm Vertex, ∃ a x y : ℝ,
      1 / 2 < a ∧ 1 - a ≤ y ∧ y ≤ x ∧ x ≤ a ∧
      ∀ e : Bundle, permutePrices π.symm p e ≤ M a x y e := by
  obtain ⟨v, hv⟩ := hstar
  obtain ⟨π, hπ0, h32, h21, h10⟩ := exists_star_sorted p v
  let p' := permutePrices π.symm p
  let a := p' 0
  let x := max (1 / 2 : ℝ) (p' 1)
  let y := max (1 / 2 : ℝ) (p' 2)
  have hcore : ∀ e : Bundle, 4 ≤ e.val → p' e ≤ 1 / 2 := by
    exact star_core_low π p (by simpa [hπ0] using hv)
  have hdis' := permute_disjoint_price π p hdisjoint
  have hmax : ∀ e : Bundle, Inc 0 e → p' e ≤ a := by
    intro e he
    fin_cases e <;> simp [Inc, left, right, a] at he ⊢ <;> linarith
  have ha : 1 / 2 < a := by
    obtain ⟨e, he⟩ := hne
    let j := edgePerm π.symm e
    have hj : Inc 0 j := by
      have he' : Inc (π 0) e := (inc_iff_mem _ _).2 (by simpa [hπ0] using hv e he)
      have hm := (inc_relabel π 0 j).1
      have hje : edgePerm π j = e := edgePerm_apply_symm π e
      exact hm (by simpa [j, hje] using he')
    have hpj : p' j = p e := by
      simp [p', permutePrices, j, edgePerm_apply_symm]
    have hjle := hmax j hj
    linarith
  have hdomain := star_padded_domain p' a ha.le h10 h21
  refine ⟨π, a, x, y, ha, ?_, ?_, ?_, ?_⟩
  · exact hdomain.1
  · exact hdomain.2.1
  · exact hdomain.2.2
  · exact star_prices_le_M p' a rfl h32 hcore hdis'

theorem triangle_labeled_prices (p : Bundle → ℝ) (π : Equiv.Perm Vertex)
    (u v w : Vertex) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hπ0 : π 0 = u) (hπ1 : π 1 = v) (hπ2 : π 2 = w) :
    permutePrices π.symm p 0 = p (pairIndex u v huv) ∧
      permutePrices π.symm p 1 = p (pairIndex u w huw) ∧
      permutePrices π.symm p 4 = p (pairIndex v w hvw) := by
  have he0 : edgePerm π 0 = pairIndex u v huv := by
    apply edge_injective
    rw [edge_edgePerm, edge_pairIndex]
    simp [edge, hπ0, hπ1]
  have he1 : edgePerm π 1 = pairIndex u w huw := by
    apply edge_injective
    rw [edge_edgePerm, edge_pairIndex]
    simp [edge, hπ0, hπ2]
  have he4 : edgePerm π 4 = pairIndex v w hvw := by
    apply edge_injective
    rw [edge_edgePerm, edge_pairIndex]
    simp [edge, hπ1, hπ2]
  simp [permutePrices, he0, he1, he4]

theorem exists_triangle_ordered_tuple (p : Bundle → ℝ)
    (u v w : Vertex) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hbig : p (pairIndex u w huw) ≤ p (pairIndex u v huv))
    (hsmall : p (pairIndex v w hvw) ≤ p (pairIndex u w huw)) :
    ∃ π : Equiv.Perm Vertex,
      π 0 = u ∧ π 1 = v ∧ π 2 = w ∧
      let p' := permutePrices π.symm p
      p' 4 ≤ p' 1 ∧ p' 1 ≤ p' 0 := by
  obtain ⟨π, h0, h1, h2⟩ := exists_perm_three u v w huv huw hvw
  obtain ⟨hp0, hp1, hp4⟩ :=
    triangle_labeled_prices p π u v w huv huw hvw h0 h1 h2
  refine ⟨π, h0, h1, h2, ?_⟩
  dsimp
  rw [hp4, hp1, hp0]
  exact ⟨hsmall, hbig⟩

end WeightedEdgeColoring.Subtwo.PriceRelabel
