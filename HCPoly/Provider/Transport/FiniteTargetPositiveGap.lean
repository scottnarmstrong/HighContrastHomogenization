/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.FiniteFamilyPositiveGap
import HCPoly.Provider.Recurrence.MeanOrder

/-!
# The collective positive gap for a finite family of adapted target cells

This module supplies the pathwise positivity, translated-cell integrability,
and translated-cell mean identities needed to instantiate the collective gap
estimate with adapted responses.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A finite family of adapted target responses is absorbed collectively by
its ordered majorants. -/
theorem finite_target_family_positive_gap [NeZero d]
    {iota : Type*} [DecidableEq iota]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {Q : ℕ} (hQ : 2 ≤ Q) (hQeven : Even Q)
    {jStar n : ℤ} {p : Mat d} (hp : IsRoundedGrid jStar p)
    (s : Finset iota) (hs : s.Nonempty) (lev : iota → ℤ)
    (idx : iota → Fin d → ℤ) (hlev : ∀ i ∈ s, jStar ≤ lev i)
    (hfin : ∀ i ∈ s, HasFiniteAdaptedMean P p (lev i))
    (wt : iota → ℝ) (hwt : ∀ i ∈ s, 0 < wt i)
    (G : iota → CoeffSpace d → BlockMat d) (K : iota → BlockMat d)
    (hF0pd : Book.Ch02.BlockPosDef (adaptedMean P p n))
    (hGsym : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (G i x))
    (hKsym : ∀ i ∈ s, IsSymmetricBlockMat (K i))
    (hdom : ∀ i ∈ s, ∀ x,
      toFullBlockMat (adaptedResponse p (lev i) (idx i) x) ≤
        toFullBlockMat (G i x))
    (hGint : ∀ i ∈ s, Integrable (fun x => toFullBlockMat (G i x)) P)
    (hGmean : ∀ i ∈ s,
      ∫ x, toFullBlockMat (G i x) ∂P = toFullBlockMat (K i))
    (hGmeas : ∀ i ∈ s, ∀ alpha beta : BlockCoord d,
      AEStronglyMeasurable (fun x => toFullBlockMat (G i x) alpha beta) P)
    (hIH : ∀ i ∈ s, (1 : FullBlockMat d) ≤ toFullBlockMat
      (normalizedBlock (adaptedMean P p (lev i)) (adaptedMean P p n)))
    (hHK : ∀ i ∈ s, toFullBlockMat
        (normalizedBlock (adaptedMean P p (lev i)) (adaptedMean P p n)) ≤
      toFullBlockMat (normalizedBlock (K i) (adaptedMean P p n)))
    {B : ℝ} (hB : 0 ≤ B)
    (hgap : ∑ i ∈ s, wt i ^ (Q : ℝ) *
      gapG (Q : ℝ) (normalizedBlock (K i) (adaptedMean P p n)) ≤ B) :
    ∫⁻ x, ENNReal.ofReal (s.sup' hs fun i => wt i *
        schattenSize (Q : ℝ)
          (blockSub (adaptedResponse p (lev i) (idx i) x)
            (adaptedMean P p (lev i)))
          (adaptedMean P p n)) ^ (Q : ℝ) ∂P ≤
      ENNReal.ofReal
          ((((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹) *
              (1 + (2 * (1 + (2 : ℝ) ^ ((Q : ℝ) - 2) +
                (2 : ℝ) ^ ((Q : ℝ) - 2) *
                  (2 * (d : ℝ)) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
                (2 * (1 + (2 : ℝ) ^ ((Q : ℝ) - 2) +
                  (2 : ℝ) ^ ((Q : ℝ) - 2) *
                    (2 * (d : ℝ)) ^ (1 - ((Q : ℝ))⁻¹))) ^
                  ((Q : ℝ) - 1)⁻¹)) ^ (Q : ℝ) *
            (2 : ℝ) ^ ((Q : ℝ) - 1)) *
        ((∫⁻ x, ENNReal.ofReal (s.sup' hs fun i => wt i *
            schattenSize (Q : ℝ) (blockSub (G i x) (K i))
              (adaptedMean P p n)) ^ (Q : ℝ) ∂P) +
          ENNReal.ofReal (2 * B)) := by
  have hpPD : p.PosDef := Recurrence.posDef_of_isRoundedGrid hp
  have hFsym : ∀ i ∈ s, ∀ x,
      IsSymmetricBlockMat (adaptedResponse p (lev i) (idx i) x) := by
    intro i hi x
    exact Recurrence.isSymmetricBlockMat_adaptedResponse p (lev i) (idx i) x
  have hHsym : ∀ i ∈ s,
      IsSymmetricBlockMat (adaptedMean P p (lev i)) := by
    intro i hi
    exact Recurrence.isSymmetricBlockMat_adaptedMean P p (lev i)
  have hFpos : ∀ i ∈ s, ∀ x,
      (toFullBlockMat (adaptedResponse p (lev i) (idx i) x)).PosSemidef := by
    intro i hi x
    exact (posDef_toFullBlockMat (hFsym i hi x)
      (Recurrence.blockPosDef_adaptedResponse hpPD (lev i) (idx i) x)).posSemidef
  have hFint : ∀ i ∈ s,
      Integrable (fun x => toFullBlockMat
        (adaptedResponse p (lev i) (idx i) x)) P := by
    intro i hi
    simpa only [adaptedResponse] using
      (Recurrence.integrable_toFullBlockMat_coarseBlock_adaptedCellAt hP hp
        (hlev i hi) (hfin i hi) (idx i))
  have hFmean : ∀ i ∈ s,
      ∫ x, toFullBlockMat (adaptedResponse p (lev i) (idx i) x) ∂P =
        toFullBlockMat (adaptedMean P p (lev i)) := by
    intro i hi
    have hintAt := Recurrence.hasIntegrableCoarseBlock_adaptedCellAt hP hp
      (hlev i hi) (hfin i hi) (idx i)
    have hmeas : HasMeasurableCoarseBlock P (adaptedCell p (lev i)) :=
      fun alpha beta => ((hfin i hi) alpha beta).aestronglyMeasurable
    change (∫ x, toFullBlockMat
      (coarseBlock (adaptedCellAt p (lev i) (idx i)) x) ∂P) = _
    rw [← toFullBlockMat_annealedBlock hintAt,
      Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hP hp
        (hlev i hi) hmeas (idx i)]
  exact finite_family_positive_gap P s hs hQ hQeven wt hwt
    (fun i x => adaptedResponse p (lev i) (idx i) x) G
    (fun i => adaptedMean P p (lev i)) K (adaptedMean P p n)
    (Recurrence.isSymmetricBlockMat_adaptedMean P p n) hF0pd hFsym hGsym hHsym
    hKsym hFpos hdom hFint hGint hFmean hGmean hGmeas hIH hHK hB hgap

end

end Transport
end HighContrast
end Homogenization
