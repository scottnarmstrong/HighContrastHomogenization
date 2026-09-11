/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.FiniteTargetGap
import HCPoly.Provider.Transport.NonlinearTerminalProfile

/-!
# The finite target-gap budget in extended nonnegative reals

The exact real budget returned with the finite target majorants is discharged
against the old portable profile, the bridge error, and the transported source
remainder.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-- The real budget selected by `exists_finite_target_majorants_gap_sum_le`
has a direct `ENNReal` discharge against the incoming portable profile, the
bridge error, and the transported source remainder.  All three constants are
chosen before the buffer, law, reference block, and grid data. -/
theorem exists_finite_target_gap_ennreal_bound
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (Q : ℕ) (hQ : 2 ≤ Q) (rhoMax a : ℝ)
    (hadef : a = (Q : ℝ) * (rhoMax - g) - (d : ℝ))
    (halo : 0 < a) (hahi : a < 1 - g) (Khop : ℝ) (hKhop : 1 ≤ Khop) :
    ∃ CgapP CgapE CgapS : ℝ,
      0 ≤ CgapP ∧ 0 ≤ CgapE ∧ 0 ≤ CgapS ∧
      ∀ l0 : ℕ, 1 ≤ l0 →
      ∀ Cd : ℝ, 1 ≤ Cd →
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ jStar M : ℤ, IsCoupledWindow d Q K jStar M →
        ∀ Y : CoeffSpace d → ℝ, IsWindowMultiplier P g E Ψ K Cd jStar M Y →
        ∀ mu mu' : Mat d, mu.PosDef → mu'.PosDef →
        ∀ rchk u : ℤ, jStar ≤ rchk → rchk ≤ u →
        (∀ r : Mat d, r = roundedGrid jStar mu ∨ r = roundedGrid jStar mu' →
          ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
            adaptedCell r j ⊆ centeredCube d M) →
        ∀ etaX : ℝ, 0 ≤ etaX →
        let B : ℝ :=
          (2 * 2 ^ (Q : ℝ) * (1 + 2 * (d : ℝ)) ^ (Q : ℝ)) *
            ((1 + (6 * (d : ℝ) * Real.sqrt d * Khop) *
                ((3 : ℝ) ^ (-(1 - g - a)) /
                  (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
                (3 : ℝ) ^ (a * (l0 : ℝ)) *
                ∑ r ∈ Finset.Ico jStar (u + 2 * (l0 : ℤ)),
                  (3 : ℝ) ^
                      (-a * (((u + 2 * (l0 : ℤ) : ℤ) : ℝ) - 1 - (r : ℝ))) *
                    frakH (Q : ℝ)
                      (relMean P (roundedGrid jStar mu) r
                        (u + 2 * (l0 : ℤ))) +
              6 * (1 / (1 - (3 : ℝ) ^
                (-((Q : ℝ) * rhoMax - (d : ℝ))))) * etaX +
              ((3 : ℝ) ^ a *
                (1 / (1 - (3 : ℝ) ^ (-a)) +
                  1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
                  1 / (1 - (3 : ℝ) ^
                    (-((Q : ℝ) * (1 - g) - a))))) *
                (18 * (d : ℝ) * Real.sqrt d * Khop) ^ (Q : ℝ) *
                transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
                  (u + (l0 : ℤ)));
        ENNReal.ofReal B ≤
            ENNReal.ofReal
                (CgapP * (3 : ℝ) ^ (a * (l0 : ℝ))) *
              portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu)
                jStar rchk (u + 2 * (l0 : ℤ)) +
          ENNReal.ofReal (CgapE * etaX) +
          ENNReal.ofReal
            (CgapS * transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
              (u + (l0 : ℤ))) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := le_trans (by omega) hd
  have hdR0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := le_trans zero_le_one hQ1
  have hQpos : (0 : ℝ) < (Q : ℝ) := lt_of_lt_of_le zero_lt_one hQ1
  have hg0 : 0 ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hKhop0 : 0 ≤ Khop := le_trans zero_le_one hKhop
  have hadm : a ≤ (Q : ℝ) * rhoMax - (d : ℝ) := by
    have hQg : 0 ≤ (Q : ℝ) * g := mul_nonneg hQ0 hg0
    rw [hadef]
    linarith only [hQg]
  have hrowRate : 0 < 1 - g - a := by linarith only [hahi]
  have hrowDen : 0 < 1 - (3 : ℝ) ^ (-(1 - g - a)) := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ))
      (by norm_num) (neg_neg_of_pos hrowRate)
    linarith only [hlt]
  have hmajDen : 0 < 1 - (3 : ℝ) ^ (-a) := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ))
      (by norm_num) (neg_neg_of_pos halo)
    linarith only [hlt]
  have hQrow : 1 - g ≤ (Q : ℝ) * (1 - g) := by
    exact (le_mul_iff_one_le_left (by linarith only [hg1])).2 hQ1
  have hsrcRate : 0 < (Q : ℝ) * (1 - g) - a := by
    linarith only [hahi, hQrow]
  have hsrcDen : 0 < 1 - (3 : ℝ) ^
      (-((Q : ℝ) * (1 - g) - a)) := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ))
      (by norm_num) (neg_neg_of_pos hsrcRate)
    linarith only [hlt]
  have hbetaPos : 0 < (Q : ℝ) * rhoMax - (d : ℝ) := by
    rw [show (Q : ℝ) * rhoMax - (d : ℝ) =
      a + (Q : ℝ) * g by rw [hadef]; ring]
    exact add_pos_of_pos_of_nonneg halo (mul_nonneg hQ0 hg0)
  have hbetaDen : 0 < 1 - (3 : ℝ) ^
      (-((Q : ℝ) * rhoMax - (d : ℝ))) := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ))
      (by norm_num) (neg_neg_of_pos hbetaPos)
    linarith only [hlt]
  let A : ℝ := 2 * 2 ^ (Q : ℝ) * (1 + 2 * (d : ℝ)) ^ (Q : ℝ)
  let Crow : ℝ := 6 * (d : ℝ) * Real.sqrt d * Khop
  let rowGeom : ℝ := (3 : ℝ) ^ (-(1 - g - a)) /
    (1 - (3 : ℝ) ^ (-(1 - g - a)))
  let betaGeom : ℝ := 1 / (1 - (3 : ℝ) ^
    (-((Q : ℝ) * rhoMax - (d : ℝ))))
  let srcGeom : ℝ := (3 : ℝ) ^ a *
    (1 / (1 - (3 : ℝ) ^ (-a)) +
      1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
      1 / (1 - (3 : ℝ) ^ (-((Q : ℝ) * (1 - g) - a))))
  let majorizationConst : ℝ := 1 / (1 - (3 : ℝ) ^ (-a))
  let Lam : ℝ := 18 * (d : ℝ) * Real.sqrt d * Khop
  let profileCoeff : ℝ := 1 + Crow * rowGeom
  let CgapP : ℝ := A * profileCoeff * majorizationConst
  let CgapE : ℝ := A * (6 * betaGeom)
  let CgapS : ℝ := A * (srcGeom * Lam ^ (Q : ℝ))
  have hA0 : 0 ≤ A := by simp only [A]; positivity
  have hCrow0 : 0 ≤ Crow := by simp only [Crow]; positivity
  have hrowGeom0 : 0 ≤ rowGeom := by
    simp only [rowGeom]
    exact div_nonneg (Real.rpow_nonneg (by norm_num) _) hrowDen.le
  have hbetaGeom0 : 0 ≤ betaGeom := by
    simp only [betaGeom]
    exact one_div_nonneg.mpr hbetaDen.le
  have hsrcGeom0 : 0 ≤ srcGeom := by
    simp only [srcGeom]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg
        (add_nonneg (one_div_nonneg.mpr hmajDen.le)
          (one_div_nonneg.mpr hrowDen.le))
        (one_div_nonneg.mpr hsrcDen.le))
  have hmajorizationConst0 : 0 ≤ majorizationConst := by
    simp only [majorizationConst]
    exact one_div_nonneg.mpr hmajDen.le
  have hLam0 : 0 ≤ Lam := by simp only [Lam]; positivity
  have hprofileCoeff0 : 0 ≤ profileCoeff := by
    simp only [profileCoeff]
    exact add_nonneg zero_le_one (mul_nonneg hCrow0 hrowGeom0)
  have hCgapP0 : 0 ≤ CgapP := by
    simp only [CgapP]
    exact mul_nonneg (mul_nonneg hA0 hprofileCoeff0) hmajorizationConst0
  have hCgapE0 : 0 ≤ CgapE := by
    simp only [CgapE]
    exact mul_nonneg hA0 (mul_nonneg (by norm_num) hbetaGeom0)
  have hCgapS0 : 0 ≤ CgapS := by
    simp only [CgapS]
    exact mul_nonneg hA0
      (mul_nonneg hsrcGeom0 (Real.rpow_nonneg hLam0 (Q : ℝ)))
  refine ⟨CgapP, CgapE, CgapS, hCgapP0, hCgapE0, hCgapS0, ?_⟩
  intro l0 hl0 Cd hCd P E Ψ K S hPprob hPstat hced jStar M hw Y hY mu mu'
    hmu hmu' rchk u hjr hru hcont etaX heta0
  letI : IsProbabilityMeasure P := hPprob
  have hCd0 : (0 : ℝ) ≤ Cd := le_trans zero_le_one hCd
  have hjt : jStar ≤ u + 2 * (l0 : ℤ) := by omega
  have hq := isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu
  obtain ⟨hdef, _, _⟩ :=
    transport_definedness_and_bridge d hd g Q hQ l0 Cd P E Ψ K S hPprob hPstat
      hced jStar M hw Y hY mu mu' hmu hmu' rchk u hjr hru hcont
  have hfin : ∀ r : ℤ, jStar ≤ r → r ≤ u + 2 * (l0 : ℤ) →
      HasFiniteAdaptedMean P (roundedGrid jStar mu) r := by
    intro r hr hrt
    exact (hdef _ (Or.inl rfl) r hr hrt).1
  have hIP : ∀ {r : ℤ}, jStar ≤ r → r ≤ u + 2 * (l0 : ℤ) →
      (1 : FullBlockMat d) ≤ toFullBlockMat
        (relMean P (roundedGrid jStar mu) r (u + 2 * (l0 : ℤ))) := by
    intro r hr hrt
    exact PortableHistory.one_le_relMean_window hPstat hq le_rfl hfin hr hrt le_rfl
  let W : ℝ := ∑ r ∈ Finset.Ico jStar (u + 2 * (l0 : ℤ)),
    (3 : ℝ) ^
        (-a * (((u + 2 * (l0 : ℤ) : ℤ) : ℝ) - 1 - (r : ℝ))) *
      frakH (Q : ℝ)
        (relMean P (roundedGrid jStar mu) r (u + 2 * (l0 : ℤ)))
  have hterm0 : ∀ r ∈ Finset.Ico jStar (u + 2 * (l0 : ℤ)),
      0 ≤ (3 : ℝ) ^
          (-a * (((u + 2 * (l0 : ℤ) : ℤ) : ℝ) - 1 - (r : ℝ))) *
        frakH (Q : ℝ)
          (relMean P (roundedGrid jStar mu) r (u + 2 * (l0 : ℤ))) := by
    intro r hr
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (zero_le_frakH hQ0
        (hIP (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2.le))
  have hW0 : 0 ≤ W := by
    simp only [W]
    exact Finset.sum_nonneg hterm0
  have hWmajor : ENNReal.ofReal W ≤
      ENNReal.ofReal majorizationConst *
        portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu) jStar rchk
          (u + 2 * (l0 : ℤ)) := by
    simpa only [W, majorizationConst] using
      nonlinear_terminal_sum_le_portableProfile
        (P := P) (Q := (Q : ℝ)) (a := a) (rhoMax := rhoMax)
        (q := roundedGrid jStar mu) (l := jStar) (jStar := jStar)
        (TMax := u + 2 * (l0 : ℤ)) hQpos halo hadm hPstat hq le_rfl hfin
        (b := rchk) (t := u + 2 * (l0 : ℤ)) hjr (by omega) le_rfl
  let R : ℝ := transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
    (u + (l0 : ℤ))
  have hSrc0 : 0 ≤ transportSrcCoeff Cd g E jStar mu mu' :=
    le_trans zero_le_one (one_le_transportSrcCoeff hCd0 hg1 E jStar mu mu')
  have hR0 : 0 ≤ R := by
    simp only [R, transportSrcRemainder]
    exact mul_nonneg
      (add_nonneg hSrc0 (Real.rpow_nonneg hSrc0 (Q : ℝ)))
      (Real.rpow_nonneg (by norm_num) _)
  let buf : ℝ := (3 : ℝ) ^ (a * (l0 : ℝ))
  let bulk : ℝ := profileCoeff * buf * W
  let bridge : ℝ := 6 * betaGeom * etaX
  let source : ℝ := srcGeom * Lam ^ (Q : ℝ) * R
  have hbuf0 : 0 ≤ buf := by simp only [buf]; positivity
  have hbulk0 : 0 ≤ bulk := by
    simp only [bulk]
    exact mul_nonneg (mul_nonneg hprofileCoeff0 hbuf0) hW0
  have hbridge0 : 0 ≤ bridge := by
    simp only [bridge]
    exact mul_nonneg (mul_nonneg (by norm_num) hbetaGeom0) heta0
  have hsource0 : 0 ≤ source := by
    simp only [source]
    exact mul_nonneg
      (mul_nonneg hsrcGeom0 (Real.rpow_nonneg hLam0 (Q : ℝ))) hR0
  dsimp only
  change ENNReal.ofReal (A * (bulk + bridge + source)) ≤
      ENNReal.ofReal (CgapP * buf) *
          portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu) jStar rchk
            (u + 2 * (l0 : ℤ)) +
        ENNReal.ofReal (CgapE * etaX) + ENNReal.ofReal (CgapS * R)
  have hbulkBound : ENNReal.ofReal (A * bulk) ≤
      ENNReal.ofReal (CgapP * buf) *
        portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu) jStar rchk
          (u + 2 * (l0 : ℤ)) := by
    have hcoef0 : 0 ≤ A * profileCoeff * buf :=
      mul_nonneg (mul_nonneg hA0 hprofileCoeff0) hbuf0
    have hcoefEq : (A * profileCoeff * buf) * majorizationConst =
        CgapP * buf := by
      simp only [CgapP]
      ring
    calc
      ENNReal.ofReal (A * bulk) =
          ENNReal.ofReal (A * profileCoeff * buf * W) := by
            apply congrArg ENNReal.ofReal
            simp only [bulk]
            ring
      _ = ENNReal.ofReal (A * profileCoeff * buf) * ENNReal.ofReal W :=
        ENNReal.ofReal_mul hcoef0
      _ ≤ ENNReal.ofReal (A * profileCoeff * buf) *
          (ENNReal.ofReal majorizationConst *
            portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu)
              jStar rchk (u + 2 * (l0 : ℤ))) := by
            exact mul_le_mul_right hWmajor _
      _ = ENNReal.ofReal (CgapP * buf) *
          portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu)
            jStar rchk (u + 2 * (l0 : ℤ)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hcoef0, hcoefEq]
  have hbridgeEq : ENNReal.ofReal (A * bridge) =
      ENNReal.ofReal (CgapE * etaX) := by
    apply congrArg ENNReal.ofReal
    simp only [bridge, CgapE]
    ring
  have hsourceEq : ENNReal.ofReal (A * source) =
      ENNReal.ofReal (CgapS * R) := by
    apply congrArg ENNReal.ofReal
    simp only [source, CgapS]
    ring
  have hsplit : ENNReal.ofReal (A * (bulk + bridge + source)) =
      ENNReal.ofReal (A * bulk) + ENNReal.ofReal (A * bridge) +
        ENNReal.ofReal (A * source) := by
    have hAbulk0 : 0 ≤ A * bulk := mul_nonneg hA0 hbulk0
    have hAbridge0 : 0 ≤ A * bridge := mul_nonneg hA0 hbridge0
    have hAsource0 : 0 ≤ A * source := mul_nonneg hA0 hsource0
    rw [show A * (bulk + bridge + source) =
        A * bulk + A * bridge + A * source by ring,
      ENNReal.ofReal_add (add_nonneg hAbulk0 hAbridge0) hAsource0,
      ENNReal.ofReal_add hAbulk0 hAbridge0]
  rw [hsplit, hbridgeEq, hsourceEq]
  exact add_le_add (add_le_add hbulkBound le_rfl) le_rfl


end

end Transport
end HighContrast
end Homogenization
