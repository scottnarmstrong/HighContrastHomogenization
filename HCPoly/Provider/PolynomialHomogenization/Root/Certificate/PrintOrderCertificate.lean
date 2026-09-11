/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.QuantitativeNormalizedReferenceCertificate

/-!
# Quantitative normalized-reference certificates at the printed order

The fractional order is a function of the already selected stochastic
exponent `g`.  This separates the printed route from an interface that selects one
universal small order before `g`.
-/

namespace Homogenization
namespace HighContrast
namespace Certificate

noncomputable section

variable {d : ℕ}

/-- The fractional order used by the printed row conversion. -/
def printCertificateOrder (g : ℝ) : ℝ :=
  (1 + g) / 4

/-- The physical block-row weight used by the frozen random source. -/
def printRowOrder (g : ℝ) : ℝ :=
  (1 + 3 * g) / 4

/-- A quantitative normalized-reference certificate at the order selected
after `g` in the printed route. -/
def PrintOrderQuantitativeNormalizedReferenceCertificate [NeZero d]
    (abar : Mat d) (g amplitude kappa x : ℝ) (a : CoeffSpace d) : Prop :=
  ∃ (hS : (symmPart abar).PosDef) (aRef : Book.Ch03.CoeffFamily d),
    0 < printCertificateOrder g ∧ printCertificateOrder g < 1 / 2 ∧
    0 ≤ amplitude ∧ 0 < kappa ∧ 1 ≤ x ∧
    (∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ⇑(normalizedCenteredCoeff a abar hS).1) ∧
    ScalarIdentityPowerTail
      aRef (printCertificateOrder g) amplitude kappa x

/-- All strict exponent margins used by the printed row conversion. -/
theorem printOrder_margins {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 < printCertificateOrder g ∧
      printCertificateOrder g < 1 / 2 ∧
      0 < printRowOrder g ∧
      printRowOrder g ≤ 1 ∧
      printRowOrder g - g = (1 - g) / 4 ∧
      2 * printCertificateOrder g - printRowOrder g = (1 - g) / 4 ∧
      printRowOrder g < 2 * printCertificateOrder g ∧
      1 - 2 * printCertificateOrder g = (1 - g) / 2 ∧
      0 < 1 - 2 * printCertificateOrder g := by
  have hg0 : 0 ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hgap : 0 < 1 - g := sub_pos.mpr hg1
  have hs : 0 < printCertificateOrder g := by
    dsimp only [printCertificateOrder]
    linarith only [hg0]
  have hsHalf : printCertificateOrder g < 1 / 2 := by
    dsimp only [printCertificateOrder]
    linarith only [hg1]
  have hrho : 0 < printRowOrder g := by
    dsimp only [printRowOrder]
    linarith only [hg0]
  have hrhoOne : printRowOrder g ≤ 1 := by
    dsimp only [printRowOrder]
    linarith only [hg1]
  have hrhoSub : printRowOrder g - g = (1 - g) / 4 := by
    dsimp only [printRowOrder]
    ring
  have htwiceSub :
      2 * printCertificateOrder g - printRowOrder g = (1 - g) / 4 := by
    dsimp only [printCertificateOrder, printRowOrder]
    ring
  have hrhoGap : printRowOrder g < 2 * printCertificateOrder g := by
    linarith only [htwiceSub, hgap]
  have honeSub :
      1 - 2 * printCertificateOrder g = (1 - g) / 2 := by
    dsimp only [printCertificateOrder]
    ring
  have honePos : 0 < 1 - 2 * printCertificateOrder g := by
    linarith only [honeSub, hgap]
  exact ⟨hs, hsHalf, hrho, hrhoOne, hrhoSub, htwiceSub,
    hrhoGap, honeSub, honePos⟩

end

end Certificate
end HighContrast
end Homogenization
