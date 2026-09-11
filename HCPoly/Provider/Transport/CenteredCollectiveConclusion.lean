/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.TransportConclusion

/-!
# Arithmetic conclusion for the collective centered estimate

This file keeps the final extended-real bookkeeping separate from the cell
geometry.  One collective gap estimate, a three-part majorant split, and the
profile/bridge/source bounds for those parts imply the printed centered-history
shape.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- Assemble a collective gap bound after its inherited, fresh, source, and
deterministic-gap contributions have been discharged. -/
theorem centered_collective_conclusion
    {H V I F S profile : ℝ≥0∞}
    {B etaX Rsrc buf buf2 Kgap Ksplit Cinh Cfresh Csource
      CgapP CgapE CgapS Ccen CcenS : ℝ}
    (heta0 : 0 ≤ etaX) (hR0 : 0 ≤ Rsrc)
    (hbuf0 : 0 ≤ buf) (hbuf1 : 1 ≤ buf) (hbuf2 : buf ≤ buf2)
    (hKgap0 : 0 ≤ Kgap) (hKsplit0 : 0 ≤ Ksplit)
    (hCinh0 : 0 ≤ Cinh) (hCfresh0 : 0 ≤ Cfresh)
    (hCsource0 : 0 ≤ Csource) (hCgapP0 : 0 ≤ CgapP)
    (hCgapE0 : 0 ≤ CgapE) (hCgapS0 : 0 ≤ CgapS)
    (hCcen0 : 0 ≤ Ccen) (hCcenS0 : 0 ≤ CcenS)
    (hCprof : Kgap * (Ksplit * (Cinh + Cfresh) + 2 * CgapP) ≤ Ccen)
    (hCbridge : Kgap * (2 * CgapE) ≤ Ccen)
    (hCsrc : Kgap * (Ksplit * Csource + 2 * CgapS) ≤ CcenS)
    (hmain : H ≤ ENNReal.ofReal Kgap * (V + ENNReal.ofReal (2 * B)))
    (hsplit : V ≤ ENNReal.ofReal Ksplit * (I + F + S))
    (hinherited : I ≤ ENNReal.ofReal (Cinh * buf) * profile)
    (hfresh : F ≤ ENNReal.ofReal (Cfresh * buf) * profile)
    (hsource : S ≤ ENNReal.ofReal (Csource * Rsrc))
    (hgap : ENNReal.ofReal B ≤
      ENNReal.ofReal (CgapP * buf) * profile +
        ENNReal.ofReal (CgapE * etaX) +
        ENNReal.ofReal (CgapS * Rsrc)) :
    H ≤ ENNReal.ofReal (Ccen * buf2) * profile +
        ENNReal.ofReal (Ccen * etaX) +
        ENNReal.ofReal (CcenS * buf * Rsrc) := by
  have hCif0 : 0 ≤ Cinh + Cfresh := add_nonneg hCinh0 hCfresh0
  have hif : I + F ≤ ENNReal.ofReal ((Cinh + Cfresh) * buf) * profile := by
    refine (add_le_add hinherited hfresh).trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add
      (mul_nonneg hCinh0 hbuf0) (mul_nonneg hCfresh0 hbuf0)]
    ring_nf
    exact le_rfl
  have hparts : I + F + S ≤
      ENNReal.ofReal ((Cinh + Cfresh) * buf) * profile +
        ENNReal.ofReal (Csource * Rsrc) :=
    add_le_add hif hsource
  have htwoGap : ENNReal.ofReal (2 * B) ≤
      (2 : ℝ≥0∞) *
        (ENNReal.ofReal (CgapP * buf) * profile +
          ENNReal.ofReal (CgapE * etaX) +
          ENNReal.ofReal (CgapS * Rsrc)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    exact mul_le_mul' le_rfl hgap
  have hraw : H ≤ ENNReal.ofReal Kgap *
      (ENNReal.ofReal Ksplit *
          (ENNReal.ofReal ((Cinh + Cfresh) * buf) * profile +
            ENNReal.ofReal (Csource * Rsrc)) +
        (2 : ℝ≥0∞) *
          (ENNReal.ofReal (CgapP * buf) * profile +
            ENNReal.ofReal (CgapE * etaX) +
            ENNReal.ofReal (CgapS * Rsrc))) := by
    refine hmain.trans (mul_le_mul' le_rfl (add_le_add ?_ htwoGap))
    exact hsplit.trans (mul_le_mul' le_rfl hparts)
  have hprofileCoef0 : 0 ≤ Ksplit * (Cinh + Cfresh) + 2 * CgapP :=
    add_nonneg (mul_nonneg hKsplit0 hCif0) (mul_nonneg (by norm_num) hCgapP0)
  have hbridgeCoef0 : 0 ≤ Kgap * (2 * CgapE) :=
    mul_nonneg hKgap0 (mul_nonneg (by norm_num) hCgapE0)
  have hsourceCoef0 : 0 ≤ Ksplit * Csource + 2 * CgapS :=
    add_nonneg (mul_nonneg hKsplit0 hCsource0)
      (mul_nonneg (by norm_num) hCgapS0)
  have hKprofile0 : 0 ≤
      Kgap * (Ksplit * (Cinh + Cfresh) + 2 * CgapP) :=
    mul_nonneg hKgap0 hprofileCoef0
  have hKsource0 : 0 ≤ Kgap * (Ksplit * Csource + 2 * CgapS) :=
    mul_nonneg hKgap0 hsourceCoef0
  have hofProfileCoef : ENNReal.ofReal
        (Kgap * (Ksplit * (Cinh + Cfresh) + 2 * CgapP) * buf) =
      ENNReal.ofReal Kgap *
        (ENNReal.ofReal Ksplit * ENNReal.ofReal (Cinh + Cfresh) +
          (2 : ℝ≥0∞) * ENNReal.ofReal CgapP) * ENNReal.ofReal buf := by
    rw [ENNReal.ofReal_mul hKprofile0, ENNReal.ofReal_mul hKgap0,
      ENNReal.ofReal_add (mul_nonneg hKsplit0 hCif0)
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hCgapP0),
      ENNReal.ofReal_mul hKsplit0,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
  have hofBridgeCoef : ENNReal.ofReal (Kgap * (2 * CgapE) * etaX) =
      ENNReal.ofReal Kgap * ((2 : ℝ≥0∞) * ENNReal.ofReal CgapE) *
        ENNReal.ofReal etaX := by
    rw [ENNReal.ofReal_mul hbridgeCoef0, ENNReal.ofReal_mul hKgap0,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
  have hofSourceCoef : ENNReal.ofReal
        (Kgap * (Ksplit * Csource + 2 * CgapS) * Rsrc) =
      ENNReal.ofReal Kgap *
        (ENNReal.ofReal Ksplit * ENNReal.ofReal Csource +
          (2 : ℝ≥0∞) * ENNReal.ofReal CgapS) * ENNReal.ofReal Rsrc := by
    rw [ENNReal.ofReal_mul hKsource0, ENNReal.ofReal_mul hKgap0,
      ENNReal.ofReal_add (mul_nonneg hKsplit0 hCsource0)
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hCgapS0),
      ENNReal.ofReal_mul hKsplit0,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
  have hcanon : ENNReal.ofReal Kgap *
      (ENNReal.ofReal Ksplit *
          (ENNReal.ofReal ((Cinh + Cfresh) * buf) * profile +
            ENNReal.ofReal (Csource * Rsrc)) +
        (2 : ℝ≥0∞) *
          (ENNReal.ofReal (CgapP * buf) * profile +
            ENNReal.ofReal (CgapE * etaX) +
            ENNReal.ofReal (CgapS * Rsrc))) =
      ENNReal.ofReal
          (Kgap * (Ksplit * (Cinh + Cfresh) + 2 * CgapP) * buf) * profile +
        ENNReal.ofReal (Kgap * (2 * CgapE) * etaX) +
        ENNReal.ofReal
          (Kgap * (Ksplit * Csource + 2 * CgapS) * Rsrc) := by
    rw [hofProfileCoef, hofBridgeCoef, hofSourceCoef]
    simp only [ENNReal.ofReal_mul hCif0, ENNReal.ofReal_mul hCsource0,
      ENNReal.ofReal_mul hCgapP0, ENNReal.ofReal_mul hCgapE0,
      ENNReal.ofReal_mul hCgapS0]
    ring
  rw [hcanon] at hraw
  refine hraw.trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact mul_le_mul'
      (ENNReal.ofReal_le_ofReal
        ((mul_le_mul_of_nonneg_right hCprof hbuf0).trans
          (mul_le_mul_of_nonneg_left hbuf2 hCcen0))) le_rfl
  · exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCbridge heta0)
  · have hcoef := mul_le_mul_of_nonneg_right hCsrc hR0
    have hbufSrc : CcenS * Rsrc ≤ CcenS * buf * Rsrc := by
      have := mul_le_mul_of_nonneg_left hbuf1 hCcenS0
      nlinarith only [this, hR0]
    exact ENNReal.ofReal_le_ofReal (hcoef.trans hbufSrc)

end

end Transport
end HighContrast
end Homogenization
