import Mathlib.Tactic

/-! Linear deficit identities for the fifteen edges of `K₆`.

The edge order is `01,02,03,04,05,12,13,14,15,23,24,25,34,35,45`.
These are the identities used by the six-vertex fractional-matching
completion argument. -/

namespace WeightedEdgeColoring.Subtwo.K6MatchingDeficits

abbrev Edge := Fin 15
abbrev Vertex := Fin 6

def ends : Edge → Finset Vertex :=
  ![{0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5},
    {1, 2}, {1, 3}, {1, 4}, {1, 5},
    {2, 3}, {2, 4}, {2, 5},
    {3, 4}, {3, 5}, {4, 5}]

def IsMatching (M : Finset Edge) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (ends e) (ends f)

def triangleMass (x : Edge → ℝ) (S : Finset Vertex) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : Edge => ends e ⊆ S), x e

def fiveMass (x : Edge → ℝ) (S : Finset Vertex) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : Edge => ends e ⊆ S), x e

def degree (x : Edge → ℝ) : Vertex → ℝ :=
  ![x 0 + x 1 + x 2 + x 3 + x 4,
    x 0 + x 5 + x 6 + x 7 + x 8,
    x 1 + x 5 + x 9 + x 10 + x 11,
    x 2 + x 6 + x 9 + x 12 + x 13,
    x 3 + x 7 + x 10 + x 12 + x 14,
    x 4 + x 8 + x 11 + x 13 + x 14]

def total (x : Edge → ℝ) : ℝ := ∑ e, x e
def deficit (x : Edge → ℝ) (v : Vertex) : ℝ := 1 - degree x v
def omitFive (x : Edge → ℝ) (v : Vertex) : ℝ := total x - degree x v

theorem sum_degree_eq_two_total (x : Edge → ℝ) :
    (∑ v, degree x v) = 2 * total x := by
  simp [degree, total, Fin.sum_univ_succ]
  ring

theorem sum_deficit_eq (x : Edge → ℝ) :
    (∑ v, deficit x v) = 6 - 2 * total x := by
  simp only [deficit, Finset.sum_sub_distrib]
  rw [sum_degree_eq_two_total]
  norm_num

/-- When the five-set omitting `v` is tight at value two,
its total degree deficit equals the deficit of `v`. -/
theorem tight_five_deficit_identity (x : Edge → ℝ) (v : Vertex)
    (htight : omitFive x v = 2) :
    (∑ u ∈ (Finset.univ : Finset Vertex).erase v, deficit x u) =
      deficit x v := by
  have htot : total x = 2 + degree x v := by
    dsimp [omitFive] at htight
    linarith
  have hall := sum_deficit_eq x
  have hsplit : (∑ u : Vertex, deficit x u) =
      (∑ u ∈ (Finset.univ : Finset Vertex).erase v, deficit x u) +
        deficit x v := by
    simpa [add_comm] using (Finset.sum_erase_add (Finset.mem_univ v) (deficit x))
  dsimp [deficit] at *
  linarith

theorem fiveMass_compl_singleton_eq_omitFive (x : Edge → ℝ) (v : Vertex) :
    fiveMass x ((Finset.univ : Finset Vertex).erase v) = omitFive x v := by
  fin_cases v <;>
    simp [fiveMass, Finset.sum_filter, ends, omitFive, total, degree,
      Fin.sum_univ_succ, Finset.subset_iff, Finset.mem_erase] <;>
    ring

/-- A tight five-set cannot contain two deficient vertices when one has
maximum deficit. This is the principal obstruction exclusion in the
regular-completion argument. -/
theorem tight_five_excludes_two_deficits (x : Edge → ℝ)
    (hdegree : ∀ z : Vertex, degree x z ≤ 1)
    (w u v : Vertex) (hwu : w ≠ u) (hwv : w ≠ v) (huv : u ≠ v)
    (htight : omitFive x w = 2)
    (hmax : deficit x w ≤ deficit x u)
    (hv : 0 < deficit x v) : False := by
  let S : Finset Vertex := Finset.univ.erase w
  have huS : u ∈ S := by simp [S, Ne.symm hwu]
  have hvS : v ∈ S.erase u := by simp [S, Ne.symm huv, Ne.symm hwv]
  have hrest : 0 ≤ ∑ z ∈ (S.erase u).erase v, deficit x z := by
    apply Finset.sum_nonneg
    intro z _
    dsimp [deficit]
    linarith [hdegree z]
  have hsumU := Finset.sum_erase_add S (deficit x) huS
  have hsumV := Finset.sum_erase_add (S.erase u) (deficit x) hvS
  have hfive := tight_five_deficit_identity x w htight
  dsimp [S] at hsumU hsumV hrest
  linarith

def cross : Fin 3 → Fin 3 → Edge :=
  ![![2, 3, 4], ![6, 7, 8], ![9, 10, 11]]
def oppositeA : Fin 3 → Edge := ![5, 1, 0]
def oppositeB : Fin 3 → Edge := ![14, 13, 12]

def trianglePairMatching (i j : Fin 3) : Finset Edge :=
  {cross i j, oppositeA i, oppositeB j}

theorem trianglePairMatching_isMatching (i j : Fin 3) :
    IsMatching (trianglePairMatching i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [IsMatching, trianglePairMatching, cross, oppositeA, oppositeB, ends]

def trianglePairMarginal (x : Edge → ℝ) (e : Edge) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    if e ∈ trianglePairMatching i j then x (cross i j) else 0

theorem trianglePairMass_eq_one (x : Edge → ℝ)
    (hdegree : ∀ v : Vertex, degree x v = 1)
    (htight : x 0 + x 1 + x 5 = 1) :
    (∑ i : Fin 3, ∑ j : Fin 3, x (cross i j)) = 1 := by
  have h0 := hdegree 0
  have h1 := hdegree 1
  have h2 := hdegree 2
  simp [cross, Fin.sum_univ_succ, degree] at *
  linarith

theorem trianglePairMarginal_eq (x : Edge → ℝ)
    (hdegree : ∀ v : Vertex, degree x v = 1)
    (htight : x 0 + x 1 + x 5 = 1) :
    ∀ e : Edge, trianglePairMarginal x e = x e := by
  have h0 := hdegree 0
  have h1 := hdegree 1
  have h2 := hdegree 2
  have h3 := hdegree 3
  have h4 := hdegree 4
  have h5 := hdegree 5
  simp [degree] at h0 h1 h2 h3 h4 h5
  intro e
  fin_cases e <;>
    simp [trianglePairMarginal, trianglePairMatching, cross,
      oppositeA, oppositeB, Fin.sum_univ_succ] <;>
    linarith

theorem weighted_sum_eq_trianglePairs (x p : Edge → ℝ)
    (hdegree : ∀ v : Vertex, degree x v = 1)
    (htight : x 0 + x 1 + x 5 = 1) :
    (∑ e : Edge, p e * x e) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        x (cross i j) * (∑ e ∈ trianglePairMatching i j, p e) := by
  have hcoord := trianglePairMarginal_eq x hdegree htight
  calc
    (∑ e : Edge, p e * x e) =
        ∑ e : Edge, p e * trianglePairMarginal x e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [hcoord e]
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          x (cross i j) * (∑ e ∈ trianglePairMatching i j, p e) := by
      simp [trianglePairMarginal, trianglePairMatching, cross,
        oppositeA, oppositeB, Fin.sum_univ_succ]
      ring

theorem weighted_sum_le_one_of_tight_triangle (x p : Edge → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hdegree : ∀ v : Vertex, degree x v = 1)
    (htight : x 0 + x 1 + x 5 = 1)
    (hprice : ∀ M : Finset Edge, IsMatching M →
      (∑ e ∈ M, p e) ≤ 1) :
    (∑ e : Edge, p e * x e) ≤ 1 := by
  rw [weighted_sum_eq_trianglePairs x p hdegree htight]
  calc
    (∑ i : Fin 3, ∑ j : Fin 3,
      x (cross i j) * (∑ e ∈ trianglePairMatching i j, p e)) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, x (cross i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_of_le_one_right (hx _) (hprice _ (trianglePairMatching_isMatching i j))
    _ = 1 := trianglePairMass_eq_one x hdegree htight

theorem degree_eq_incidence_sum (x : Edge → ℝ) (v : Vertex) :
    degree x v = ∑ e : Edge, if v ∈ ends e then x e else 0 := by
  fin_cases v <;>
    simp [degree, ends, Fin.sum_univ_succ] <;>
    ring

end WeightedEdgeColoring.Subtwo.K6MatchingDeficits
