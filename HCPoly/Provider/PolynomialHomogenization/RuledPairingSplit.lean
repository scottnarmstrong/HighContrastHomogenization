/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
/- Exact pairing decomposition over the cells of a ruled carrier. -/

import HCPoly.Provider.PolynomialHomogenization.RuledWhitneyRowCauchySchwarz

namespace Homogenization
namespace HighContrast
open Function MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The union over the ruled cell index is the union over all scale rows. -/
theorem iUnion_whitneyCells_eq_rows
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) :
    (⋃ i : system.CellIndex, system.cell i) =
      ⋃ a : ℤ, ⋃ w ∈ (system.rows a : Set (Fin d → ℤ)),
        standardCell d a w := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i.1,
      Set.mem_iUnion₂.mpr ⟨i.2.1, i.2.2, hxi⟩⟩
  · intro hx
    obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
    let i : system.CellIndex := ⟨a, ⟨w, hw⟩⟩
    exact Set.mem_iUnion.mpr ⟨i, hxw⟩

/-- The ruled Whitney cells exhaust the domain up to a null set. -/
theorem iUnion_whitneyCells_ae_eq_domain
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hd : 1 ≤ d) (hU : IsOpenBoundedConvexDomain U) :
    (⋃ i : system.CellIndex, system.cell i) =ᵐ[volume] U := by
  let A : Set (Vec d) := ⋃ i : system.CellIndex, system.cell i
  have hAU : A ⊆ U := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact system.cell_subset i hxi
  have hdiff : volume (U \ A) = 0 := by
    dsimp only [A]
    rw [iUnion_whitneyCells_eq_rows system]
    exact system.ae_exhaustion hd hU
  exact Filter.EventuallyLE.antisymm (ae_of_all volume hAU)
    (ae_le_set.mpr hdiff)

/-- Distinct ruled indices represent disjoint cell interiors. -/
theorem pairwise_disjoint_whitneyCells
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad) :
    Pairwise (Disjoint on fun i : system.CellIndex => system.cell i) := by
  intro i j hij
  exact system.pairwise_disjoint i j hij

/-- Every ruled Whitney cell is measurable. -/
theorem measurableSet_whitneyCell
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (i : system.CellIndex) : MeasurableSet (system.cell i) := by
  exact (isOpen_openCubeSet
    (translateCube (system.index i)
      (originCube d (system.scale i)))).measurableSet

end

end HighContrast
end Homogenization
