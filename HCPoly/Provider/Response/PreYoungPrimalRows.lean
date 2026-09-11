/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.PreYoungPrimalComponentRows
import HCPoly.Provider.Response.PreYoungRecentDefectRows

/-!
# Primal cutoff-mean rows

The recent-difference estimate and the physical projection estimate give the
two cutoff-mean rows required by the compact primal pre-Young assembly.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The primal cutoff mean satisfies both component row estimates whenever the
profile weak quantity is finite. -/
theorem profile_primal_cutoff_mean_rows_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {gamma : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K Cd : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P gamma E Psi K Cd jStar M Y)
    {m0 q : Mat d} (hm0 : m0.PosDef) (hqeq : q = roundedGrid jStar m0)
    (hgrid : IsRoundedGrid jStar q)
    {s t : ℤ} (hjs : jStar ≤ s) (H : ℕ) (ht : t = s + (H : ℤ))
    (hbelow : ∀ k : ℤ, k < jStar → ∀ v : ℤ,
      v = s ∨ v = t → ∀ z ∈ containedCenters q k v,
        adaptedCellTranslate q k z ⊆ centeredCube d M)
    (hblocks : ∀ k : ℤ, jStar ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hweak : profilePrimalWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let X := profilePrimalCenter P hq t (fun a ↦ a.subSkew g hg) p r
    let tau := profilePrimalResponseDefect P hq g hg s t p r
    let EJ := ∫ a, responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P
    let gain := preYoungComponentCoefficient d *
      (3 : ℝ) ^ (-(H : ℝ)) * Real.sqrt EJ
    let cut := adaptedPreYoungCutoff q hq t
    ENNReal.ofReal
        |vecDot X.2 (profilePrimalCutoffMean P hq t
          (fun a ↦ a.subSkew g hg) cut p r).1| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) *
          profileSchurLoadFlux (profileHattedBlock g (adaptedMean P q s)) X.2) +
          ENNReal.ofReal gain *
            profilePrimalHattedEarlierRow P q g s X.1 X.2 ^ (1 / 2 : ℝ) ∧
      ENNReal.ofReal
        |vecDot X.1 (profilePrimalCutoffMean P hq t
          (fun a ↦ a.subSkew g hg) cut p r).2| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) *
          profileSchurLoadGradient (profileHattedBlock g (adaptedMean P q s)) X.1) +
          ENNReal.ofReal gain *
            profilePrimalHattedEarlierRow P q g s X.1 X.2 ^ (1 / 2 : ℝ) := by
  have hst : s ≤ t := by omega
  have hints := (hblocks s hjs hst).1
  have hjt : jStar ≤ t := hjs.trans hst
  have hintt := (hblocks t hjt le_rfl).1
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let X := profilePrimalCenter P hq t (fun a ↦ a.subSkew g hg) p r
  have hrecent := profile_primal_recent_defect_rows_le
    hstat hgrid hjs hst hints hintt hm0 g hg p r X.1 X.2 hweak
  refine profile_primal_cutoff_mean_rows_le_of_recent_defect
    hstat hY hm0 hqeq hgrid hjs H ht hbelow hblocks g hg p r hweak ?_
  dsimp only at hrecent ⊢
  exact ⟨ENNReal.ofReal_le_ofReal hrecent.1,
    ENNReal.ofReal_le_ofReal hrecent.2⟩

end

end Homogenization.HighContrast.Response
