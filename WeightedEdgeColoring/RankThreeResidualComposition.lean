import WeightedEdgeColoring.RankThreeResidualLift
import WeightedEdgeColoring.QuantizedOptions

/-!
# Composing residual systems

Taking a residual system twice is the same as taking one residual after the
lifted union of the two matchings.  The option types are nested subtypes, so
the statement is an explicit equivalence together with degree identities.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Flatten a twice-residual option to an option residual after the lifted
union. -/
noncomputable def residualUnionEquiv (M : Finset Option)
    (A : Finset (H.ResidualOption M)) :
    ((H.residualSystem M).ResidualOption A) ≃
      H.ResidualOption (M ∪ H.liftResidualSet M A) where
  toFun q := ⟨q.1.1, by
    rw [H.mem_residualOptions]
    intro p hp
    rcases Finset.mem_union.mp hp with hpM | hpA
    · exact (H.mem_residualOptions.mp q.1.2 p hpM)
    · rcases H.mem_liftResidualSet.mp hpA with ⟨a, ha, rfl⟩
      exact ((H.residualSystem M).mem_residualOptions.mp q.2 a ha)⟩
  invFun q :=
    let r : H.ResidualOption M := ⟨q.1,
      H.residualOptions_anti Finset.subset_union_left q.2⟩
    ⟨r, by
      rw [(H.residualSystem M).mem_residualOptions]
      intro a ha
      have halift : a.1 ∈ H.liftResidualSet M A :=
        H.mem_liftResidualSet.mpr ⟨a, ha, rfl⟩
      exact H.mem_residualOptions.mp q.2 a.1
        (Finset.mem_union_right M halift)⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    rfl

@[simp] theorem residualUnionEquiv_val (M : Finset Option)
    (A : Finset (H.ResidualOption M))
    (q : (H.residualSystem M).ResidualOption A) :
    (H.residualUnionEquiv M A q).1 = q.1.1 := rfl

@[simp] theorem residualUnionEquiv_owner (M : Finset Option)
    (A : Finset (H.ResidualOption M))
    (q : (H.residualSystem M).ResidualOption A) :
    (H.residualSystem (M ∪ H.liftResidualSet M A)).owner
        (H.residualUnionEquiv M A q) =
      ((H.residualSystem M).residualSystem A).owner q := rfl

@[simp] theorem residualUnionEquiv_slots (M : Finset Option)
    (A : Finset (H.ResidualOption M))
    (q : (H.residualSystem M).ResidualOption A) :
    (H.residualSystem (M ∪ H.liftResidualSet M A)).slots
        (H.residualUnionEquiv M A q) =
      ((H.residualSystem M).residualSystem A).slots q := rfl

/-- Job degrees agree under residual composition. -/
theorem residualSystem_union_fiber_card (M : Finset Option)
    (A : Finset (H.ResidualOption M)) (j : Job) :
    (((H.residualSystem M).residualSystem A).fiber j).card =
      ((H.residualSystem (M ∪ H.liftResidualSet M A)).fiber j).card := by
  classical
  let e := H.residualUnionEquiv M A
  let emb : ((H.residualSystem M).ResidualOption A) ↪
      H.ResidualOption (M ∪ H.liftResidualSet M A) := e.toEmbedding
  have hmap :
      (((H.residualSystem M).residualSystem A).fiber j).map emb =
        (H.residualSystem (M ∪ H.liftResidualSet M A)).fiber j := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_map.mp hq with ⟨p, hp, rfl⟩
      exact (H.residualSystem (M ∪ H.liftResidualSet M A)).mem_fiber.mpr
        (((H.residualSystem M).residualSystem A).mem_fiber.mp hp)
    · intro hq
      let p := e.symm q
      apply Finset.mem_map.mpr
      refine ⟨p, ?_, e.apply_symm_apply q⟩
      exact ((H.residualSystem M).residualSystem A).mem_fiber.mpr
        ((H.residualSystem (M ∪ H.liftResidualSet M A)).mem_fiber.mp hq)
  simpa using congrArg Finset.card hmap

/-- Slot degrees agree under residual composition. -/
theorem residualSystem_union_slotDegree (M : Finset Option)
    (A : Finset (H.ResidualOption M)) (s : Slot) :
    ((H.residualSystem M).residualSystem A).slotDegree s =
      (H.residualSystem (M ∪ H.liftResidualSet M A)).slotDegree s := by
  classical
  let e := H.residualUnionEquiv M A
  let emb : ((H.residualSystem M).ResidualOption A) ↪
      H.ResidualOption (M ∪ H.liftResidualSet M A) := e.toEmbedding
  let L : Finset ((H.residualSystem M).ResidualOption A) :=
    Finset.univ.filter fun q ↦
      s ∈ ((H.residualSystem M).residualSystem A).slots q
  let R : Finset (H.ResidualOption (M ∪ H.liftResidualSet M A)) :=
    Finset.univ.filter fun q ↦
      s ∈ (H.residualSystem (M ∪ H.liftResidualSet M A)).slots q
  have hmap : L.map emb = R := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_map.mp hq with ⟨p, hp, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
    · intro hq
      let p := e.symm q
      apply Finset.mem_map.mpr
      refine ⟨p, ?_, e.apply_symm_apply q⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
  change L.card = R.card
  simpa using congrArg Finset.card hmap

end WeightedEdgeColoring.RankThreeOptionSystem
