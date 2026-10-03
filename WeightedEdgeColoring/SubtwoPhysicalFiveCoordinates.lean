import WeightedEdgeColoring.SubtwoPhysicalFiveSharedRows

/-! Exact column meanings for every part of the physical vector. -/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}
namespace SubtwoFivePhysicalData
variable (D : G.SubtwoFivePhysicalData n)

theorem vector_cost (e : Fin 10) : D.vector ⟨10 + e.val, by omega⟩ = D.bundleCost e := by
  unfold vector
  dsimp only
  split_ifs <;> try omega
  apply congrArg D.bundleCost
  apply Fin.ext
  dsimp only
  omega

theorem vector_mass (d : Fin 60) : D.vector ⟨25 + d.val, by omega⟩ = D.heavyMass d := by
  unfold vector
  dsimp only
  split_ifs <;> try omega
  apply congrArg D.heavyMass
  apply Fin.ext
  dsimp only
  omega

theorem vector_demandPrice (e : Fin 10) : D.vector ⟨85 + e.val, by omega⟩ = D.demandPrice e := by
  unfold vector
  dsimp only
  split_ifs <;> try omega
  apply congrArg D.demandPrice
  apply Fin.ext
  dsimp only
  omega

theorem vector_avoidingLoss (v : Fin 5) : D.vector ⟨95 + v.val, by omega⟩ = D.avoidingLoss v := by
  unfold vector
  dsimp only
  split_ifs <;> try omega
  apply congrArg D.avoidingLoss
  apply Fin.ext
  dsimp only
  omega

theorem vector_bigPrice (d : Fin 60) : D.vector ⟨100 + d.val, by omega⟩ = D.bigPrice d := by
  unfold vector
  dsimp only
  split_ifs <;> try omega
  apply congrArg D.bigPrice
  apply Fin.ext
  dsimp only
  omega

theorem vector_smallPrice (d : Fin 60) : D.vector ⟨160 + d.val, by omega⟩ = D.smallPrice d := by
  unfold vector
  dsimp only
  split_ifs <;> try omega
  apply congrArg D.smallPrice
  apply Fin.ext
  dsimp only
  omega

theorem baseCoordinate_cost (e : Fin 10) : D.baseCoordinate ⟨e.val, by omega⟩ = D.bundleCost e := by
  exact (D.vector_baseCoordinate ⟨e.val, by omega⟩).symm.trans (D.vector_cost e)

theorem baseCoordinate_exterior (v : Fin 5) :
    D.baseCoordinate ⟨10 + v.val, by omega⟩ = D.exteriorCharge v := by
  have h := D.vector_baseCoordinate ⟨10 + v.val, by omega⟩
  have hi : (⟨10 + (10 + v.val), by omega⟩ : Fin 970) = ⟨20 + v.val, by omega⟩ := by
    apply Fin.ext
    dsimp only
    omega
  rw [hi, D.vector_exterior] at h
  exact h.symm

theorem baseCoordinate_mass (d : Fin 60) :
    D.baseCoordinate ⟨15 + d.val, by omega⟩ = D.heavyMass d := by
  have h := D.vector_baseCoordinate ⟨15 + d.val, by omega⟩
  have hi : (⟨10 + (15 + d.val), by omega⟩ : Fin 970) = ⟨25 + d.val, by omega⟩ := by
    apply Fin.ext
    dsimp only
    omega
  rw [hi, D.vector_mass] at h
  exact h.symm

theorem vector_product_cost (e f : Fin 10) :
    D.vector ⟨220 + 75 * e.val + f.val, by omega⟩ = D.pairPrice e * D.bundleCost f := by
  exact (D.vector_product e ⟨f.val, by omega⟩).trans
    (congrArg (fun y => D.pairPrice e * y) (D.baseCoordinate_cost f))

theorem vector_product_exterior (e : Fin 10) (v : Fin 5) :
    D.vector ⟨220 + 75 * e.val + 10 + v.val, by omega⟩ = D.pairPrice e * D.exteriorCharge v := by
  have hi : (⟨220 + 75 * e.val + 10 + v.val, by omega⟩ : Fin 970) =
      ⟨220 + 75 * e.val + (10 + v.val), by omega⟩ := by
    apply Fin.ext
    dsimp only
    omega
  rw [hi, D.vector_product e ⟨10 + v.val, by omega⟩, D.baseCoordinate_exterior v]

theorem vector_product_mass (e : Fin 10) (d : Fin 60) :
    D.vector ⟨220 + 75 * e.val + 15 + d.val, by omega⟩ = D.pairPrice e * D.heavyMass d := by
  have hi : (⟨220 + 75 * e.val + 15 + d.val, by omega⟩ : Fin 970) =
      ⟨220 + 75 * e.val + (15 + d.val), by omega⟩ := by
    apply Fin.ext
    dsimp only
    omega
  rw [hi, D.vector_product e ⟨15 + d.val, by omega⟩, D.baseCoordinate_mass d]

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
