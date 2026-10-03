import WeightedEdgeColoring.FiniteBernoulliChernoff

/-!
# Cylinder independence in finite product spaces

The first factor represents a chosen coordinate support and the second factor
its complement.  The lemmas below are deliberately division-free, so zero-mass
conditioning events cause no special case in local-lemma applications.
-/

namespace WeightedEdgeColoring.FiniteProductCylinder

open scoped BigOperators

variable {A B J : Type*}

/-- Product mass on a two-block finite sample space. -/
def productMass (massA : A → ℝ) (massB : B → ℝ) : A × B → ℝ :=
  fun omega ↦ massA omega.1 * massB omega.2

/-- A cylinder event depending only on the first coordinate block. -/
def firstCylinder [Fintype B] [DecidableEq B]
    (event : Finset A) : Finset (A × B) :=
  event.product Finset.univ

/-- A cylinder event depending only on the second coordinate block. -/
def secondCylinder [Fintype A] [DecidableEq A]
    (event : Finset B) : Finset (A × B) :=
  Finset.univ.product event

/-- An event depends only on the chosen (first) coordinate support. -/
def DependsOnlyOnFirst [Fintype B] [DecidableEq B]
    (event : Finset (A × B)) : Prop :=
  ∃ localEvent : Finset A, event = firstCylinder localEvent

/-- An event depends only on coordinates outside the chosen support. -/
def DependsOnlyOnSecond [Fintype A] [DecidableEq A]
    (event : Finset (A × B)) : Prop :=
  ∃ localEvent : Finset B, event = secondCylinder localEvent

section Algebra

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [Fintype A] [DecidableEq A] in
@[simp] theorem mem_firstCylinder {event : Finset A} {omega : A × B} :
    omega ∈ firstCylinder event ↔ omega.1 ∈ event := by
  simp [firstCylinder]

omit [Fintype B] [DecidableEq B] in
@[simp] theorem mem_secondCylinder {event : Finset B} {omega : A × B} :
    omega ∈ secondCylinder event ↔ omega.2 ∈ event := by
  simp [secondCylinder]

theorem firstCylinder_inter_secondCylinder (eventA : Finset A) (eventB : Finset B) :
    firstCylinder eventA ∩ secondCylinder eventB = eventA.product eventB := by
  ext omega
  simp

@[simp] theorem firstCylinder_compl (event : Finset A) :
    (Finset.univ \ firstCylinder event : Finset (A × B)) =
      firstCylinder (Finset.univ \ event) := by
  ext omega
  simp

@[simp] theorem secondCylinder_compl (event : Finset B) :
    (Finset.univ \ secondCylinder event : Finset (A × B)) =
      secondCylinder (Finset.univ \ event) := by
  ext omega
  simp

omit [Fintype A] in
@[simp] theorem firstCylinder_inter (E F : Finset A) :
    firstCylinder (B := B) (E ∩ F) = firstCylinder E ∩ firstCylinder F := by
  ext omega
  simp

omit [Fintype B] in
@[simp] theorem secondCylinder_inter (E F : Finset B) :
    secondCylinder (A := A) (E ∩ F) = secondCylinder E ∩ secondCylinder F := by
  ext omega
  simp

/-- Avoiding outside-supported events is again an outside-supported event. -/
theorem avoid_secondCylinders [Fintype J] [DecidableEq J]
    (bad : J → Finset B) (T : Finset J) :
    WeightedEdgeColoring.FiniteLocalLemma.avoid (fun j ↦ secondCylinder (A := A) (bad j)) T =
      secondCylinder (A := A) (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) := by
  ext omega
  simp [WeightedEdgeColoring.FiniteLocalLemma.avoid]

end Algebra

section Independence

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Exact mass of a rectangle under product mass. -/
theorem eventMass_rectangle (massA : A → ℝ) (massB : B → ℝ)
    (eventA : Finset A) (eventB : Finset B) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
        (eventA.product eventB) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass massA eventA *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass massB eventB := by
  exact WeightedEdgeColoring.FiniteLocalLemma.eventMass_product massA massB eventA eventB

/-- Cylinders on disjoint coordinate blocks are independent. -/
theorem eventMass_disjoint_cylinders
    (massA : A → ℝ) (massB : B → ℝ)
    (hmassA_one : ∑ a, massA a = 1) (hmassB_one : ∑ b, massB b = 1)
    (eventA : Finset A) (eventB : Finset B) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
        (firstCylinder eventA ∩ secondCylinder eventB) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
          (firstCylinder eventA) *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
          (secondCylinder eventB) := by
  rw [firstCylinder_inter_secondCylinder]
  simp only [firstCylinder, secondCylinder]
  rw [eventMass_rectangle, eventMass_rectangle, eventMass_rectangle]
  simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass, hmassA_one, hmassB_one]

/--
Conditioning on the complements of any finite family of outside-supported
events leaves a first-block cylinder independent.
-/
theorem eventMass_firstCylinder_inter_avoid_secondCylinders
    [Fintype J] [DecidableEq J]
    (massA : A → ℝ) (massB : B → ℝ)
    (hmassA_one : ∑ a, massA a = 1) (hmassB_one : ∑ b, massB b = 1)
    (eventA : Finset A) (badOutside : J → Finset B) (T : Finset J) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
        (firstCylinder eventA ∩
          WeightedEdgeColoring.FiniteLocalLemma.avoid
            (fun j ↦ secondCylinder (A := A) (badOutside j)) T) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
          (firstCylinder eventA) *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
          (WeightedEdgeColoring.FiniteLocalLemma.avoid
            (fun j ↦ secondCylinder (A := A) (badOutside j)) T) := by
  rw [avoid_secondCylinders]
  exact eventMass_disjoint_cylinders massA massB hmassA_one hmassB_one _ _

/--
Division-free conditional bound for disjoint cylinders.  This is the exact
shape required by the lopsided-local-lemma hypothesis.
-/
theorem conditional_le_of_disjoint_cylinders
    (massA : A → ℝ) (massB : B → ℝ)
    (hmassA_one : ∑ a, massA a = 1)
    (hmassB_nonneg : ∀ b, 0 ≤ massB b)
    (eventA : Finset A) (eventB : Finset B) (p : ℝ)
    (hlocal : WeightedEdgeColoring.FiniteLocalLemma.eventMass massA eventA ≤ p) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
        (firstCylinder eventA ∩ secondCylinder eventB) ≤
      p * WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
        (secondCylinder eventB) := by
  rw [firstCylinder_inter_secondCylinder]
  simp only [secondCylinder]
  rw [eventMass_rectangle, eventMass_rectangle]
  simp only [WeightedEdgeColoring.FiniteLocalLemma.eventMass]
  rw [show (∑ a ∈ (Finset.univ : Finset A), massA a) = 1 by simpa using hmassA_one]
  simp only [one_mul]
  exact mul_le_mul_of_nonneg_right hlocal
    (Finset.sum_nonneg fun b _ ↦ hmassB_nonneg b)

/-- Division-free conditioning bound against finitely many outside bad events. -/
theorem conditional_le_avoid_secondCylinders
    [Fintype J] [DecidableEq J]
    (massA : A → ℝ) (massB : B → ℝ)
    (hmassA_one : ∑ a, massA a = 1)
    (hmassB_nonneg : ∀ b, 0 ≤ massB b)
    (eventA : Finset A) (badOutside : J → Finset B) (T : Finset J) (p : ℝ)
    (hlocal : WeightedEdgeColoring.FiniteLocalLemma.eventMass massA eventA ≤ p) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
        (firstCylinder eventA ∩
          WeightedEdgeColoring.FiniteLocalLemma.avoid
            (fun j ↦ secondCylinder (A := A) (badOutside j)) T) ≤
      p * WeightedEdgeColoring.FiniteLocalLemma.eventMass (productMass massA massB)
        (WeightedEdgeColoring.FiniteLocalLemma.avoid
          (fun j ↦ secondCylinder (A := A) (badOutside j)) T) := by
  rw [avoid_secondCylinders]
  exact conditional_le_of_disjoint_cylinders massA massB hmassA_one
    hmassB_nonneg eventA _ p hlocal

/--
An unconditional Chernoff estimate on the supported block remains valid after
conditioning on any event supported on the complementary coordinate block.
-/
theorem bernoulli_chernoff_conditioned_outside
    {I : Type*} [Fintype I] [DecidableEq I]
    (q weight : I → ℝ) (massB : B → ℝ)
    (hmassB_nonneg : ∀ b, 0 ≤ massB b)
    (outsideEvent : Finset B) (r lambda : ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) (hweight_le_one : ∀ i, weight i ≤ 1)
    (hlambda : 0 ≤ lambda) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (productMass (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q) massB)
        (firstCylinder (WeightedEdgeColoring.FiniteBernoulliChernoff.upperTail
          (WeightedEdgeColoring.FiniteBernoulliChernoff.weightedSum weight) r) ∩
          secondCylinder outsideEvent) ≤
      Real.exp (-lambda * r + (Real.exp lambda - 1) *
          WeightedEdgeColoring.FiniteBernoulliChernoff.mean q weight) *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (productMass (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q) massB)
          (secondCylinder outsideEvent) := by
  apply conditional_le_of_disjoint_cylinders
    (WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulliMass q) massB
    (WeightedEdgeColoring.FiniteBernoulliChernoff.sum_bernoulliMass q)
    hmassB_nonneg
  exact WeightedEdgeColoring.FiniteBernoulliChernoff.bernoulli_upperTail_le
    q weight r lambda hq_nonneg hq_le_one hweight_nonneg hweight_le_one hlambda

end Independence

section LocalLemmaBridge

variable [Fintype A] [DecidableEq A]
variable [Fintype J] [DecidableEq J]

/-- Exact independence of two events under a finite mass function. -/
def IndependentEvents (mass : A → ℝ) (E F : Finset A) : Prop :=
  WeightedEdgeColoring.FiniteLocalLemma.eventMass mass (E ∩ F) =
    WeightedEdgeColoring.FiniteLocalLemma.eventMass mass E *
      WeightedEdgeColoring.FiniteLocalLemma.eventMass mass F

/--
Symmetric lopsided LLL from unconditional bad-event bounds plus independence
from every allowed non-neighbour conditioning event.  The cylinder lemmas above
provide the intended way to prove `hindependent`.
-/
theorem symmetric_lopsided_local_lemma_of_independent
    (mass : A → ℝ)
    (bad : J → Finset A)
    (neighbor : J → Finset J)
    (p x : ℝ) (d : ℕ)
    (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_one : ∑ omega, mass omega = 1)
    (hdegree : ∀ j, (neighbor j).card ≤ d)
    (hx_nonneg : 0 ≤ x) (hx_lt_one : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^ d)
    (hbad : ∀ j, WeightedEdgeColoring.FiniteLocalLemma.eventMass mass (bad j) ≤ p)
    (hindependent : ∀ (j : J) (T : Finset J),
      T ⊆ Finset.univ \ insert j (neighbor j) →
      IndependentEvents mass (bad j) (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T)) :
    0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass mass
      (WeightedEdgeColoring.FiniteLocalLemma.avoid bad Finset.univ) := by
  apply WeightedEdgeColoring.FiniteLocalLemma.symmetric_lopsided_local_lemma
    mass bad neighbor p x d hmass hmass_one hdegree hx_nonneg hx_lt_one hnumeric
  intro j T hT
  rw [hindependent j T hT]
  exact mul_le_mul_of_nonneg_right (hbad j)
    (WeightedEdgeColoring.FiniteLocalLemma.eventMass_nonneg hmass _)

end LocalLemmaBridge

end WeightedEdgeColoring.FiniteProductCylinder
