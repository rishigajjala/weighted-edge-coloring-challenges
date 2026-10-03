import WeightedEdgeColoring.FiniteProductCylinder

/-!
# Splitting a finite Bernoulli product by coordinate support

For a finite set of coordinates `K`, a Bernoulli outcome on `I` is exactly a
pair consisting of its coordinates in `K` and its coordinates outside `K`.
This file records that equivalence and the exact factorization of Bernoulli
mass across the two blocks.
-/

namespace WeightedEdgeColoring.FiniteBernoulliSupportSplit

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Coordinates belonging to the chosen support. -/
abbrev Inside (K : Finset I) := {i : I // i ∈ K}

/-- Coordinates outside the chosen support. -/
abbrev Outside (K : Finset I) := {i : I // i ∉ K}

/-- A finite subset of a sum is equivalently a pair of finite subsets. -/
def finsetSumEquiv (A B : Type*) [DecidableEq A] [DecidableEq B] :
    Finset (A ⊕ B) ≃ Finset A × Finset B where
  toFun S := (S.toLeft, S.toRight)
  invFun P := P.1.disjSum P.2
  left_inv S := by
    ext x
    cases x <;> simp
  right_inv P := by
    ext x <;> simp

/-- Split a Bernoulli outcome into the coordinates in `K` and outside `K`. -/
noncomputable def splitEquiv (K : Finset I) :
    Finset I ≃ Finset (Inside K) × Finset (Outside K) :=
  (Equiv.finsetCongr (Equiv.sumCompl (fun i : I ↦ i ∈ K)).symm).trans
    (finsetSumEquiv (Inside K) (Outside K))

/-- Bernoulli parameters restricted to the chosen support. -/
def insideParameter (q : I → ℝ) (K : Finset I) : Inside K → ℝ :=
  fun i ↦ q i

/-- Bernoulli parameters restricted to the complementary support. -/
def outsideParameter (q : I → ℝ) (K : Finset I) : Outside K → ℝ :=
  fun i ↦ q i

@[simp] theorem mem_splitEquiv_symm_inside (K : Finset I)
    (A : Finset (Inside K)) (B : Finset (Outside K)) (i : Inside K) :
    (i : I) ∈ (splitEquiv K).symm (A, B) ↔ i ∈ A := by
  classical
  simp [splitEquiv, finsetSumEquiv]

@[simp] theorem mem_splitEquiv_symm_outside (K : Finset I)
    (A : Finset (Inside K)) (B : Finset (Outside K)) (i : Outside K) :
    (i : I) ∈ (splitEquiv K).symm (A, B) ↔ i ∈ B := by
  classical
  simp [splitEquiv, finsetSumEquiv]

@[simp] theorem mem_splitEquiv_inside (K : Finset I)
    (S : Finset I) (i : Inside K) :
    i ∈ (splitEquiv K S).1 ↔ (i : I) ∈ S := by
  have h := mem_splitEquiv_symm_inside K
    (splitEquiv K S).1 (splitEquiv K S).2 i
  simpa using h.symm

@[simp] theorem mem_splitEquiv_outside (K : Finset I)
    (S : Finset I) (i : Outside K) :
    i ∈ (splitEquiv K S).2 ↔ (i : I) ∈ S := by
  have h := mem_splitEquiv_symm_outside K
    (splitEquiv K S).1 (splitEquiv K S).2 i
  simpa using h.symm

/-- The inside component contains exactly the active global coordinates that
belong to `K`. -/
theorem card_splitEquiv_inside (K S : Finset I) :
    (splitEquiv K S).1.card = (S.filter fun i ↦ i ∈ K).card := by
  let valEmbedding : Inside K ↪ I :=
    ⟨fun i ↦ i.1, Subtype.val_injective⟩
  have hmap : (splitEquiv K S).1.map valEmbedding =
      S.filter fun i ↦ i ∈ K := by
    ext i
    simp [valEmbedding]
  have hcard := congrArg Finset.card hmap
  simpa using hcard

private theorem bernoulliMass_eq_prod_ite (q : I → ℝ) (S : Finset I) :
    WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q S =
      ∏ i, if i ∈ S then q i else 1 - q i := by
  classical
  rw [WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass]
  rw [Finset.prod_ite]
  congr 1 <;> apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    rfl
  · ext i
    simp
  · intro i hi
    rfl

/-- Bernoulli mass factors exactly under `splitEquiv`. -/
theorem bernoulliMass_split (q : I → ℝ) (K : Finset I)
    (A : Finset (Inside K)) (B : Finset (Outside K)) :
    WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q
        ((splitEquiv K).symm (A, B)) =
      WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass (insideParameter q K) A *
        WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass (outsideParameter q K) B := by
  classical
  rw [bernoulliMass_eq_prod_ite, bernoulliMass_eq_prod_ite,
    bernoulliMass_eq_prod_ite]
  rw [← Finset.prod_mul_prod_compl K
    (fun i ↦ if i ∈ (splitEquiv K).symm (A, B) then q i else 1 - q i)]
  congr 1
  · change (∏ i ∈ K, if i ∈ (splitEquiv K).symm (A, B) then q i else 1 - q i) =
      ∏ i ∈ K.attach, if i ∈ A then q i else 1 - q i
    rw [← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro i hi
    simp
  · change (∏ i ∈ Kᶜ, if i ∈ (splitEquiv K).symm (A, B) then q i else 1 - q i) =
      ∏ i : Outside K, if i ∈ B then q i else 1 - q i
    rw [Finset.prod_subtype (p := fun i : I ↦ i ∉ K)
      (F := Subtype.fintype (fun i : I ↦ i ∉ K)) Kᶜ (by simp)
      (fun i ↦ if i ∈ (splitEquiv K).symm (A, B) then q i else 1 - q i)]
    simp

/-- Transport an event on the two coordinate blocks back to global outcomes. -/
noncomputable def splitEvent (K : Finset I)
    (event : Finset (Finset (Inside K) × Finset (Outside K))) :
    Finset (Finset I) :=
  event.map (splitEquiv K).symm.toEmbedding

@[simp] theorem mem_splitEvent (K : Finset I)
    (event : Finset (Finset (Inside K) × Finset (Outside K)))
    (S : Finset I) :
    S ∈ splitEvent K event ↔ splitEquiv K S ∈ event := by
  classical
  simp [splitEvent]

@[simp] theorem splitEvent_inter (K : Finset I)
    (E F : Finset (Finset (Inside K) × Finset (Outside K))) :
    splitEvent K (E ∩ F) = splitEvent K E ∩ splitEvent K F := by
  classical
  ext S
  simp

@[simp] theorem splitEvent_compl (K : Finset I)
    (E : Finset (Finset (Inside K) × Finset (Outside K))) :
    splitEvent K (Finset.univ \ E) = Finset.univ \ splitEvent K E := by
  classical
  ext S
  simp

/-- Exact change-of-variables formula for every event under the split. -/
theorem eventMass_splitEvent (q : I → ℝ) (K : Finset I)
    (event : Finset (Finset (Inside K) × Finset (Outside K))) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q) (splitEvent K event) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteProductCylinder.productMass
          (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass (insideParameter q K))
          (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass (outsideParameter q K))) event := by
  classical
  rw [WeightedEdgeColoring.FiniteLocalLemma.eventMass, splitEvent, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro P hP
  exact bernoulliMass_split q K P.1 P.2

/-- A global event determined only by coordinates in `K`. -/
noncomputable def insideCylinder (K : Finset I) (event : Finset (Finset (Inside K))) :
    Finset (Finset I) :=
  splitEvent K (WeightedEdgeColoring.FiniteProductCylinder.firstCylinder event)

/-- A global event determined only by coordinates outside `K`. -/
noncomputable def outsideCylinder (K : Finset I) (event : Finset (Finset (Outside K))) :
    Finset (Finset I) :=
  splitEvent K (WeightedEdgeColoring.FiniteProductCylinder.secondCylinder event)

@[simp] theorem mem_insideCylinder (K : Finset I)
    (event : Finset (Finset (Inside K))) (S : Finset I) :
    S ∈ insideCylinder K event ↔ (splitEquiv K S).1 ∈ event := by
  classical
  simp [insideCylinder]

@[simp] theorem mem_outsideCylinder (K : Finset I)
    (event : Finset (Finset (Outside K))) (S : Finset I) :
    S ∈ outsideCylinder K event ↔ (splitEquiv K S).2 ∈ event := by
  classical
  simp [outsideCylinder]

/-- Intersection of a supported and an outside-supported global event is the
transport of their rectangle. -/
theorem insideCylinder_inter_outsideCylinder (K : Finset I)
    (eventIn : Finset (Finset (Inside K)))
    (eventOut : Finset (Finset (Outside K))) :
    insideCylinder K eventIn ∩ outsideCylinder K eventOut =
      splitEvent K (eventIn.product eventOut) := by
  classical
  ext S
  simp [insideCylinder, outsideCylinder]

/-- Exact factorization of a supported event and an outside-supported event
under the original global Bernoulli mass. -/
theorem eventMass_inside_inter_outside (q : I → ℝ) (K : Finset I)
    (eventIn : Finset (Finset (Inside K)))
    (eventOut : Finset (Finset (Outside K))) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q)
        (insideCylinder K eventIn ∩ outsideCylinder K eventOut) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass (insideParameter q K)) eventIn *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass (outsideParameter q K)) eventOut := by
  rw [insideCylinder_inter_outsideCylinder, eventMass_splitEvent]
  exact WeightedEdgeColoring.FiniteProductCylinder.eventMass_rectangle _ _ _ _

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Avoiding any finite family of outside-supported events is itself the
transport of the corresponding outside-block avoidance event. -/
theorem avoid_outsideCylinders (K : Finset I)
    (badOutside : J → Finset (Finset (Outside K))) (T : Finset J) :
    WeightedEdgeColoring.FiniteLocalLemma.avoid (fun j ↦ outsideCylinder K (badOutside j)) T =
      outsideCylinder K (WeightedEdgeColoring.FiniteLocalLemma.avoid badOutside T) := by
  classical
  ext S
  simp [WeightedEdgeColoring.FiniteLocalLemma.avoid]

/-- A local probability bound on `K` remains valid after conditioning on the
avoidance of arbitrary bad events supported outside `K`.  The statement is
division-free and is directly usable as a lopsided-LLL hypothesis. -/
theorem conditional_le_avoid_outsideCylinders
    (q : I → ℝ) (K : Finset I)
    (eventIn : Finset (Finset (Inside K)))
    (badOutside : J → Finset (Finset (Outside K))) (T : Finset J) (p : ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1)
    (hlocal : WeightedEdgeColoring.FiniteLocalLemma.eventMass
      (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass (insideParameter q K)) eventIn ≤ p) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q)
        (insideCylinder K eventIn ∩
          WeightedEdgeColoring.FiniteLocalLemma.avoid
            (fun j ↦ outsideCylinder K (badOutside j)) T) ≤
      p * WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q)
        (WeightedEdgeColoring.FiniteLocalLemma.avoid
          (fun j ↦ outsideCylinder K (badOutside j)) T) := by
  rw [avoid_outsideCylinders]
  rw [insideCylinder_inter_outsideCylinder, eventMass_splitEvent]
  rw [show outsideCylinder K (WeightedEdgeColoring.FiniteLocalLemma.avoid badOutside T) =
      splitEvent K (WeightedEdgeColoring.FiniteProductCylinder.secondCylinder
        (WeightedEdgeColoring.FiniteLocalLemma.avoid badOutside T)) by rfl]
  rw [eventMass_splitEvent]
  rw [← WeightedEdgeColoring.FiniteProductCylinder.firstCylinder_inter_secondCylinder]
  apply WeightedEdgeColoring.FiniteProductCylinder.conditional_le_of_disjoint_cylinders
    (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass (insideParameter q K))
    (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass (outsideParameter q K))
    (WeightedEdgeColoring.FiniteBernoulliChernoff.sum_bernoulliMass _)
  · intro B
    apply WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass_nonneg
    · intro i
      exact hq_nonneg i
    · intro i
      exact hq_le_one i
  · exact hlocal

/-- Chernoff upper tails on a coordinate support remain valid after avoiding
any family of bad events determined by complementary coordinates. -/
theorem bernoulli_upperTail_conditioned_outside
    (q weight : I → ℝ) (K : Finset I)
    (badOutside : J → Finset (Finset (Outside K))) (T : Finset J)
    (r lambda : ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_le_one : ∀ i, weight i ≤ 1)
    (hlambda : 0 ≤ lambda) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q)
        (insideCylinder K
            (WeightedEdgeColoring.FiniteBernoulliChernoff.upperTail
              (WeightedEdgeColoring.FiniteBernoulliChernoff.weightedSum
                (fun i : Inside K ↦ weight i)) r) ∩
          WeightedEdgeColoring.FiniteLocalLemma.avoid
            (fun j ↦ outsideCylinder K (badOutside j)) T) ≤
      Real.exp (-lambda * r + (Real.exp lambda - 1) *
          WeightedEdgeColoring.FiniteBernoulliChernoff.mean
            (insideParameter q K) (fun i : Inside K ↦ weight i)) *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q)
          (WeightedEdgeColoring.FiniteLocalLemma.avoid
            (fun j ↦ outsideCylinder K (badOutside j)) T) := by
  apply conditional_le_avoid_outsideCylinders q K _ badOutside T
      (Real.exp (-lambda * r + (Real.exp lambda - 1) *
        WeightedEdgeColoring.FiniteBernoulliChernoff.mean
          (insideParameter q K) (fun i : Inside K ↦ weight i)))
      hq_nonneg hq_le_one
  apply WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulli_upperTail_le
  · intro i
    exact hq_nonneg i
  · intro i
    exact hq_le_one i
  · intro i
    exact hweight_nonneg i
  · intro i
    exact hweight_le_one i
  · exact hlambda

/-- Lower-tail companion to `bernoulli_upperTail_conditioned_outside`. -/
theorem bernoulli_lowerTail_conditioned_outside
    (q weight : I → ℝ) (K : Finset I)
    (badOutside : J → Finset (Finset (Outside K))) (T : Finset J)
    (r lambda : ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_le_one : ∀ i, weight i ≤ 1)
    (hlambda : 0 ≤ lambda) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q)
        (insideCylinder K
            (WeightedEdgeColoring.FiniteBernoulliChernoff.lowerTail
              (WeightedEdgeColoring.FiniteBernoulliChernoff.weightedSum
                (fun i : Inside K ↦ weight i)) r) ∩
          WeightedEdgeColoring.FiniteLocalLemma.avoid
            (fun j ↦ outsideCylinder K (badOutside j)) T) ≤
      Real.exp (lambda * r + (Real.exp (-lambda) - 1) *
          WeightedEdgeColoring.FiniteBernoulliChernoff.mean
            (insideParameter q K) (fun i : Inside K ↦ weight i)) *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q)
          (WeightedEdgeColoring.FiniteLocalLemma.avoid
            (fun j ↦ outsideCylinder K (badOutside j)) T) := by
  apply conditional_le_avoid_outsideCylinders q K _ badOutside T
      (Real.exp (lambda * r + (Real.exp (-lambda) - 1) *
        WeightedEdgeColoring.FiniteBernoulliChernoff.mean
          (insideParameter q K) (fun i : Inside K ↦ weight i)))
      hq_nonneg hq_le_one
  apply WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulli_lowerTail_le
  · intro i
    exact hq_nonneg i
  · intro i
    exact hq_le_one i
  · intro i
    exact hweight_nonneg i
  · intro i
    exact hweight_le_one i
  · exact hlambda

end WeightedEdgeColoring.FiniteBernoulliSupportSplit
