/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.AnnealedSharpOrder
import HCPoly.Geometry.CanonicalDeterminant
import HCPoly.Geometry.ReferenceEntry
import HCPoly.Geometry.ReferenceRadius
import HCPoly.Geometry.SizeAlignment
import HCPoly.Provider.ShortHop.DeterminantDrift
import HCPoly.Provider.ShortHop.Normalization
import HCPoly.Provider.Sharp.CoarseBlockPositivity
/-!
# Determinant accounting along a finite bridge prefix

This file proves the determinant calculation of
`e.global.selection.determinant.telescope`.  A completed bridge costs twice the
logarithm of its near-isometry factor because the doubled block has dimension
`2d` while `detRoot` takes the `d`-th root.  Those costs telescope, and the
current partial stage is retained even when the completed prefix is empty.
-/
namespace Homogenization
namespace HighContrast
namespace Selection
open MeasureTheory
open scoped MatrixOrder Matrix
noncomputable section
variable {d : ℕ}
/-- The determinant charge of the completed stages together with the current
partial stage: the accumulated determinant loss along the prefix of geometries
summed in `p.global.selection`. -/
def determinantPrefix (P : Measure (CoeffSpace d)) (q : ℕ → Mat d)
    (s t : ℕ → ℤ) (k : ℕ) (u : ℤ) : ℝ :=
  ∑ i ∈ Finset.range k, detLoss P (q i) (s i) (t i) +
    detLoss P (q k) (s k) u
/-- The defining equation for the finite-prefix determinant charge. -/
theorem determinantPrefix_eq (P : Measure (CoeffSpace d)) (q : ℕ → Mat d)
    (s t : ℕ → ℤ) (k : ℕ) (u : ℤ) :
    determinantPrefix P q s t k u =
      ∑ i ∈ Finset.range k, detLoss P (q i) (s i) (t i) +
        detLoss P (q k) (s k) u := rfl
/-- The `d`-th root of the `2d`-dimensional scalar determinant factor is the
square of that scalar. -/
private theorem rpow_inv_pow_two_mul {c : ℝ} (hc : 0 ≤ c) (hd : d ≠ 0) :
    (c ^ (2 * d)) ^ ((d : ℝ)⁻¹) = c ^ 2 := by
  rw [← Real.rpow_natCast c (2 * d), ← Real.rpow_mul hc]
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hfactor : ((2 * d : ℕ) : ℝ) * (d : ℝ)⁻¹ = 2 := by
    push_cast
    field_simp
  rw [hfactor, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
/-- A scalar upper comparison of positive doubled blocks passes to determinant
roots with the square of the scalar. -/
theorem detRoot_le_of_le_smul [NeZero d] {A B : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) (hB : (toFullBlockMat B).PosDef)
    {c : ℝ} (hc : 0 < c) (hle : toFullBlockMat A ≤ c • toFullBlockMat B) :
    detRoot d A ≤ c ^ 2 * detRoot d B := by
  have hdet := det_le_det_of_le hA (posDef_smul hB hc) hle
  rw [Matrix.det_smul, show Fintype.card (BlockCoord d) = 2 * d by
    simp [Fintype.card_sum, two_mul]] at hdet
  have hmono := Real.rpow_le_rpow hA.det_pos.le hdet
    (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)
  rw [Real.mul_rpow (pow_nonneg hc.le _) hB.det_pos.le,
    rpow_inv_pow_two_mul hc.le (NeZero.ne d)] at hmono
  exact hmono
/-- The `2d`-dimensional completed-bridge comparison, the determinant comparison
across one change of geometry. -/
theorem log_detRoot_le_add_two_log [NeZero d] {A B : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) (hB : (toFullBlockMat B).PosDef)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hle : toFullBlockMat A ≤ (1 + eta) • toFullBlockMat B) :
    Real.log (detRoot d A) ≤ Real.log (detRoot d B) + 2 * Real.log (1 + eta) := by
  have hc : 0 < 1 + eta := by linarith only [heta]
  have hroot := detRoot_le_of_le_smul hA hB hc hle
  have hlog := Real.log_le_log (ShortHop.detRoot_pos hA) hroot
  rw [Real.log_mul (pow_ne_zero _ hc.ne') (ShortHop.detRoot_pos hB).ne', Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog]
/-- The finite-prefix determinant charges telescope, including the current
partial stage (`e.global.selection.determinant.telescope`). -/
private theorem determinantPrefix_le_of_sharp [NeZero d] {P : Measure (CoeffSpace d)}
    {q : ℕ → Mat d} {s t : ℕ → ℤ} {eta : ℕ → ℝ} {k : ℕ} {u : ℤ}
    (hA : ∀ i : ℕ, i ≤ k → (toFullBlockMat (adaptedMean P (q i) (s i))).PosDef)
    (hF : ∀ i : ℕ, i < k → (toFullBlockMat (adaptedMean P (q i) (t i))).PosDef)
    (hU : (toFullBlockMat (adaptedMean P (q k) u)).PosDef)
    (hUsharp : fullBlockSharp (toFullBlockMat (adaptedMean P (q k) u)) ≤
      toFullBlockMat (adaptedMean P (q k) u))
    (heta : ∀ i : ℕ, i < k → 0 ≤ eta i)
    (hbridge : ∀ i : ℕ, i < k →
      toFullBlockMat (adaptedMean P (q (i + 1)) (s (i + 1))) ≤
        (1 + eta i) • toFullBlockMat (adaptedMean P (q i) (t i))) :
    determinantPrefix P q s t k u ≤
      Real.log (adaptedDetRoot P (q 0) (s 0)) +
        2 * ∑ i ∈ Finset.range k, Real.log (1 + eta i) := by
  have hstage : ∀ i ∈ Finset.range k,
      detLoss P (q i) (s i) (t i) ≤
        Real.log (adaptedDetRoot P (q i) (s i)) -
          Real.log (adaptedDetRoot P (q (i + 1)) (s (i + 1))) +
            2 * Real.log (1 + eta i) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hdim := log_detRoot_le_add_two_log
      (hA (i + 1) (by omega)) (hF i hik) (heta i hik) (hbridge i hik)
    change Real.log (adaptedDetRoot P (q (i + 1)) (s (i + 1))) ≤
      Real.log (adaptedDetRoot P (q i) (t i)) + 2 * Real.log (1 + eta i) at hdim
    rw [detLoss]
    linarith only [hdim]
  have hsum := Finset.sum_le_sum hstage
  have honeDet : 1 ≤ (toFullBlockMat (adaptedMean P (q k) u)).det :=
    one_le_det_of_fullBlockSharp_le hU hUsharp
  have honeRoot : 1 ≤ adaptedDetRoot P (q k) u := by
    rw [adaptedDetRoot, detRoot]
    exact Real.one_le_rpow honeDet (by positivity)
  have hcurrent : detLoss P (q k) (s k) u ≤
      Real.log (adaptedDetRoot P (q k) (s k)) := by
    rw [detLoss]
    have := Real.log_nonneg honeRoot
    linarith only [this]
  calc
    determinantPrefix P q s t k u =
        (∑ i ∈ Finset.range k, detLoss P (q i) (s i) (t i)) +
          detLoss P (q k) (s k) u := rfl
    _ ≤ (∑ i ∈ Finset.range k,
          (Real.log (adaptedDetRoot P (q i) (s i)) -
              Real.log (adaptedDetRoot P (q (i + 1)) (s (i + 1))) +
            2 * Real.log (1 + eta i))) +
          Real.log (adaptedDetRoot P (q k) (s k)) := add_le_add hsum hcurrent
    _ = Real.log (adaptedDetRoot P (q 0) (s 0)) +
          2 * ∑ i ∈ Finset.range k, Real.log (1 + eta i) := by
      rw [Finset.sum_add_distrib, Finset.sum_range_sub', ← Finset.mul_sum]
      ring
/-- The finite-prefix telescope on the printed rounded-grid carriers.  The
integrability hypotheses supply positivity and the terminal sharp order. -/
theorem determinantPrefix_le [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {jStar : ℤ} {q : ℕ → Mat d} {s t : ℕ → ℤ}
    {eta : ℕ → ℝ} {k : ℕ} {u : ℤ}
    (hq : ∀ i : ℕ, i ≤ k → IsRoundedGrid jStar (q i))
    (hfinA : ∀ i : ℕ, i ≤ k → HasFiniteAdaptedMean P (q i) (s i))
    (hfinF : ∀ i : ℕ, i < k → HasFiniteAdaptedMean P (q i) (t i))
    (hfinU : HasFiniteAdaptedMean P (q k) u)
    (heta : ∀ i : ℕ, i < k → 0 ≤ eta i)
    (hbridge : ∀ i : ℕ, i < k →
      toFullBlockMat (adaptedMean P (q (i + 1)) (s (i + 1))) ≤
        (1 + eta i) • toFullBlockMat (adaptedMean P (q i) (t i))) :
    determinantPrefix P q s t k u ≤
      Real.log (adaptedDetRoot P (q 0) (s 0)) +
        2 * ∑ i ∈ Finset.range k, Real.log (1 + eta i) := by
  have hpos : ∀ i : ℕ, i ≤ k → ∀ r : ℤ,
      HasFiniteAdaptedMean P (q i) r → (toFullBlockMat (adaptedMean P (q i) r)).PosDef :=
    fun i hi r hfin => posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P (q i) r)
      (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid (hq i hi) r hfin)
  have hUsharp : fullBlockSharp (toFullBlockMat (adaptedMean P (q k) u)) ≤
      toFullBlockMat (adaptedMean P (q k) u) := by
    apply fullBlockSharp_le_of_blockMatLoewnerLE
      (Recurrence.isSymmetricBlockMat_adaptedMean P (q k) u)
      (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid (hq k le_rfl) u hfinU)
    exact Sharp.blockSharp_annealedBlock_le_of_nonempty
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell
        (Recurrence.posDef_of_isRoundedGrid (hq k le_rfl)) u)
      (Recurrence.adaptedCell_nonempty (q k) u) hfinU
  exact determinantPrefix_le_of_sharp
    (fun i hi => hpos i hi (s i) (hfinA i hi))
    (fun i hi => hpos i hi.le (t i) (hfinF i hi))
    (hpos k le_rfl u hfinU) hUsharp heta hbridge
/-- The determinant-root part of the identity-grid entry bound, which expresses
the determinant of the entry block through `Π`. -/
theorem entry_detRoot_bounds [NeZero d] {E A : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) (hA : (toFullBlockMat A).PosDef)
    (hEsharp : fullBlockSharp (toFullBlockMat E) ≤ toFullBlockMat E)
    {c kap : ℝ} (hc : 1 ≤ c) (hAE : toFullBlockMat A ≤ c • toFullBlockMat E)
    (hkap : canonImbalance (toFullBlockMat E) ≤ kap) :
    detRoot d A ≤ c ^ 2 * detRoot d E ∧
      detRoot d E ≤ canonImbalance (toFullBlockMat E) ∧
      detRoot d A ≤ c ^ 2 * kap := by
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hAEroot := detRoot_le_of_le_smul hA hE hc0 hAE
  have hdet := det_le_canonImbalance_pow hE hEsharp
  have hrootE : detRoot d E ≤ canonImbalance (toFullBlockMat E) := by
    have hmono := Real.rpow_le_rpow hE.det_pos.le hdet
      (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast
      (canonImbalance_nonneg (toFullBlockMat E)) (NeZero.ne d)] at hmono
    change (toFullBlockMat E).det ^ ((d : ℝ)⁻¹) ≤
      canonImbalance (toFullBlockMat E)
    exact hmono
  exact ⟨hAEroot, hrootE, hAEroot.trans (mul_le_mul_of_nonneg_left
    (hrootE.trans hkap) (sq_nonneg c))⟩
/-- The printed entry determinant bound with the reference ratio carrier. -/
theorem entry_detRoot_le_kappaRef [NeZero d] {E A : BlockMat d}
    (hEsymm : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hA : (toFullBlockMat A).PosDef)
    (hEsharp : fullBlockSharp (toFullBlockMat E) ≤ toFullBlockMat E)
    {c : ℝ} (hc : 1 ≤ c) (hAE : toFullBlockMat A ≤ c • toFullBlockMat E) :
    detRoot d A ≤ c ^ 2 * kappaRef E := by
  have hE := posDef_toFullBlockMat hEsymm hEpd
  exact (entry_detRoot_bounds hE hA hEsharp hc hAE
    (le_of_eq (kappaRef_eq_canonImbalance hEsymm hEpd).symm)).2.2
/-- The projective-radius part of the identity-grid entry bound.  It keeps the
reference radius and the entry determinant loss separate, so a consumer may
insert its preferred dimension-only comparison with `log (2 + c² Π)`. -/
private theorem entry_projectiveRadius_aux [NeZero d] (hd : 2 ≤ d) {E A : FullBlockMat d}
    (hE : E.PosDef) (hA : A.PosDef) (hEsharp : fullBlockSharp E ≤ E)
    (hAsharp : fullBlockSharp A ≤ A) {c kap : ℝ} (hc : 1 ≤ c)
    (hAE : A ≤ c • E) (hkap : canonImbalance E ≤ kap)
    {s sStar k : Mat d} (hs : s.PosDef) (hstar : sStar.PosDef)
    (hform : E = schurBlock s sStar k) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : 0 < Lam)
    (hlow : lam • (1 : Mat d) ≤ sStar) (hhigh : s ≤ Lam • (1 : Mat d)) :
    projDist 1 (canonMetric A) ≤
      (1 / 2) * Real.log (Lam / lam) +
        ((d : ℝ) / 2) * Real.log (c ^ 2 * kap) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hscaled : (c • E).PosDef := posDef_smul hE hc0
  have hcanon : canonBlock (c • E) = canonBlock E := by
    rw [canonBlock, fullBlockSharp_smul hE hc0,
      matGeomMean_smul hE (posDef_fullBlockSharp hE) hc0 (inv_pos.mpr hc0),
      mul_inv_cancel₀ hc0.ne', Real.sqrt_one, one_smul]
    rfl
  have hmetric : canonMetric (c • E) = canonMetric E := by
    obtain ⟨hm, hg, hfac⟩ := canonFactor_spec hE
    exact (canonFactor_eq hscaled hm hg (hcanon.trans hfac)).1.symm
  have himbalance : canonImbalance (c • E) = c ^ 2 * canonImbalance E := by
    rw [canonImbalance, canonImbalance, hcanon, relSize_smul_left hc0.le]
    ring
  have hscaledSharp : fullBlockSharp (c • E) ≤ c • E := by
    rw [fullBlockSharp_smul hE hc0]
    have hfirst := smul_le_smul_of_le (inv_nonneg.mpr hc0.le) hEsharp
    refine hfirst.trans (Matrix.le_iff.mpr ?_)
    rw [← sub_smul]
    exact hE.posSemidef.smul (by
      have hinv : c⁻¹ ≤ c := by
        exact (inv_le_one_of_one_le₀ hc).trans hc
      linarith only [hinv])
  have href :=
    (canonMetric_reference_radius hE hEsharp hs hstar hform hlam hLam hlow hhigh).2.2
  have hentry := projDist_canonMetric_entry hd hscaled hA hAE hscaledSharp hAsharp
  rw [hmetric, himbalance] at hentry
  have hlog : Real.log (c ^ 2 * canonImbalance E) ≤ Real.log (c ^ 2 * kap) := by
    have hleft : 0 < c ^ 2 * canonImbalance E :=
      mul_pos (sq_pos_of_pos hc0) (canonImbalance_pos hE)
    refine Real.log_le_log hleft ?_
    exact mul_le_mul_of_nonneg_left hkap (sq_nonneg c)
  have hentry' := hentry.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
  have htri := projDist_triangle Matrix.PosDef.one (posDef_canonMetric hE)
    (posDef_canonMetric hA)
  linarith only [htri, href, hentry']
/-- The identity-grid entry radius in the printed `C_d log (2 + c² Π)`
form, with the explicit admissible choice `C_d = 2d`. -/
theorem entry_projectiveRadius [NeZero d] (hd : 2 ≤ d) {E : BlockMat d}
    (hEsymm : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hEsharp : fullBlockSharp (toFullBlockMat E) ≤ toFullBlockMat E)
    {A : FullBlockMat d} (hA : A.PosDef) (hAsharp : fullBlockSharp A ≤ A)
    {c Pi : ℝ} (hc : 1 ≤ c) (hPi : 1 ≤ Pi) (hAE : A ≤ c • toFullBlockMat E)
    (hkap : kappaRef E ≤ 6 * Pi) {s sStar k : Mat d}
    (hs : s.PosDef) (hstar : sStar.PosDef)
    (hform : toFullBlockMat E = schurBlock s sStar k) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : 0 < Lam) (hlow : lam • (1 : Mat d) ≤ sStar)
    (hhigh : s ≤ Lam • (1 : Mat d)) (hratio : Lam / lam ≤ Pi) :
    projDist 1 (canonMetric A) ≤ 2 * (d : ℝ) * Real.log (2 + c ^ 2 * Pi) := by
  have hE := posDef_toFullBlockMat hEsymm hEpd
  have hkEq := kappaRef_eq_canonImbalance hEsymm hEpd
  have hbase := entry_projectiveRadius_aux hd hE hA hEsharp hAsharp hc hAE
    (le_of_eq hkEq.symm) hs hstar hform hlam hLam hlow hhigh
  have hc2 : 1 ≤ c ^ 2 := one_le_pow₀ hc
  have hPiC : Pi ≤ c ^ 2 * Pi := by
    have := mul_le_mul_of_nonneg_right hc2 (by linarith only [hPi])
    simpa only [one_mul] using this
  have hX : 1 ≤ 2 + c ^ 2 * Pi := by linarith only [hPi, hPiC]
  have hlogRatio : Real.log (Lam / lam) ≤ Real.log (2 + c ^ 2 * Pi) :=
    Real.log_le_log (div_pos hLam hlam) (hratio.trans (by linarith only [hPiC]))
  have hkapArg : c ^ 2 * kappaRef E ≤ 6 * c ^ 2 * Pi := by
    have := mul_le_mul_of_nonneg_left hkap (sq_nonneg c)
    linarith only [this]
  have hkapPos : 0 < kappaRef E := by rw [hkEq]; exact canonImbalance_pos hE
  have hlogKap : Real.log (c ^ 2 * kappaRef E) ≤ Real.log (6 * c ^ 2 * Pi) :=
    Real.log_le_log (mul_pos (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hc)) hkapPos) hkapArg
  have hsquare : 6 * c ^ 2 * Pi ≤ (2 + c ^ 2 * Pi) ^ 2 := by
    have hy : 1 ≤ c ^ 2 * Pi := hPi.trans hPiC
    nlinarith only [sq_nonneg (c ^ 2 * Pi - 1), hy]
  have hlogSquare := Real.log_le_log (by positivity : 0 < 6 * c ^ 2 * Pi) hsquare
  rw [Real.log_pow] at hlogSquare
  norm_num only [Nat.cast_ofNat] at hlogSquare
  have hterm₁ := mul_le_mul_of_nonneg_left hlogRatio (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hterm₂ := mul_le_mul_of_nonneg_left (hlogKap.trans hlogSquare)
    (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)
  calc
    projDist 1 (canonMetric A) ≤
        (1 / 2) * Real.log (Lam / lam) +
          ((d : ℝ) / 2) * Real.log (c ^ 2 * kappaRef E) := hbase
    _ ≤ (1 / 2 + (d : ℝ)) * Real.log (2 + c ^ 2 * Pi) := by
      linarith only [hterm₁, hterm₂]
    _ ≤ 2 * (d : ℝ) * Real.log (2 + c ^ 2 * Pi) := by
      apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hX)
      have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith only [hdR]
/-- The two-line combined prefix bound after a uniform bridge tolerance and
the identity-grid entry comparison. -/
theorem determinantPrefix_bound {P : Measure (CoeffSpace d)} {q : ℕ → Mat d}
    {s t : ℕ → ℤ} {eta : ℕ → ℝ} {k : ℕ} {u : ℤ} {c Pi etaX : ℝ}
    (hpref : determinantPrefix P q s t k u ≤
      Real.log (adaptedDetRoot P (q 0) (s 0)) +
        2 * ∑ i ∈ Finset.range k, Real.log (1 + eta i))
    (hroot : 0 < adaptedDetRoot P (q 0) (s 0))
    (hentry : adaptedDetRoot P (q 0) (s 0) ≤ 6 * c ^ 2 * Pi)
    (heta : ∀ i : ℕ, i < k → 0 ≤ eta i ∧ eta i ≤ etaX)
    (hetaX : 0 ≤ etaX) :
    determinantPrefix P q s t k u ≤
        Real.log (6 * c ^ 2 * Pi) + 2 * (k : ℝ) * Real.log (1 + etaX) ∧
      determinantPrefix P q s t k u ≤
        Real.log (6 * c ^ 2 * Pi) + 2 * etaX * (k : ℝ) := by
  have hlogEntry := Real.log_le_log hroot hentry
  have hsum : ∑ i ∈ Finset.range k, Real.log (1 + eta i) ≤
      (k : ℝ) * Real.log (1 + etaX) := by
    have hpoint : ∀ i ∈ Finset.range k,
        Real.log (1 + eta i) ≤ Real.log (1 + etaX) := by
      intro i hi
      exact Real.log_le_log
        (by linarith only [(heta i (Finset.mem_range.mp hi)).1])
        (by linarith only [(heta i (Finset.mem_range.mp hi)).2])
    have h := Finset.sum_le_sum hpoint
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  have hfirst : determinantPrefix P q s t k u ≤
      Real.log (6 * c ^ 2 * Pi) + 2 * (k : ℝ) * Real.log (1 + etaX) := by
    calc
      determinantPrefix P q s t k u ≤
          Real.log (adaptedDetRoot P (q 0) (s 0)) +
            2 * ∑ i ∈ Finset.range k, Real.log (1 + eta i) := hpref
      _ ≤ Real.log (6 * c ^ 2 * Pi) +
          2 * (k : ℝ) * Real.log (1 + etaX) :=
        by
          simpa only [mul_assoc] using add_le_add hlogEntry
            (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))
  refine ⟨hfirst, hfirst.trans ?_⟩
  have hlog := Real.log_le_sub_one_of_pos (by linarith only [hetaX] : 0 < 1 + etaX)
  have hlog' : Real.log (1 + etaX) ≤ etaX := by linarith only [hlog]
  have hmul := mul_le_mul_of_nonneg_left hlog'
    (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ))
  calc
    Real.log (6 * c ^ 2 * Pi) + 2 * (k : ℝ) * Real.log (1 + etaX) ≤
        Real.log (6 * c ^ 2 * Pi) + 2 * (k : ℝ) * etaX := add_le_add_right hmul _
    _ = Real.log (6 * c ^ 2 * Pi) + 2 * etaX * (k : ℝ) := by ring
end
end Selection
end HighContrast
end Homogenization
