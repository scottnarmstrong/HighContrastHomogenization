/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.AnnealedRows
import HCPoly.Provider.Transport.NonlinearRow

/-!
# The transported nonlinear row of a target cell

The pathwise majorant of `AnnealedRows` is averaged, normalized and fed to
`e.two.grid.whitney.mean.bound`, closing the row of
`e.two.grid.profile` at a continued target level.

*The annealed row.*  Averaging is monotone for the Loewner order, so the adapted
mean of a target cell of the new grid is below the weighted adapted means of the
old grid's filling plus the mean of the below-start term.  Stationarity collapses
each row: every cell of a row has the same annealed block, the adapted mean at
that scale, so the weight of a scale is the total relative volume of its cells.

*The normalized source row.*  Normalized by the new terminal block, the
below-start remainder is a scalar multiple of the reference block measured
against that terminal block; the terminal normalization
`e.two.grid.source.normalization` bounds that measurement by
`κ_𝐄B_{\mathbf q'}E[Y_P]`.  The `ε_j` this exhibits decays like `3^{-(j-j_*)}`,
strictly faster than the printed `3^{-(1-g)(j-j_*)}`; the conversion is recorded,
in the same zpow-to-rpow step the boundary row of the printed statement needs.

*The row.*  The weights of the filling are nonnegative, of total mass at most
one, and obey the conservative boundary row -- three of the hypotheses of
`e.two.grid.whitney.mean.bound` -- so the row comes out in exactly the shape
that `e.two.grid.profile` binds, with the four constants
`C_1 = A`, `C_2 = AC_b`, `C_3 = 4A`, `C_4 = A` at `A = 2^{2Q+1}(1+2d)^Q`.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The boundary row in the printed rate -/

/-- **The cross-grid row in the printed rate.**  `e.two.grid.whitney.volumes`
produces the row weight as the integer power `3^{r-j}`; the boundary row of
`e.two.grid.whitney.mean.bound` reads it as the real power
`3^{-(1-g)(j-r)}`.  The two are compatible, and the printed one is the weaker:
the burn exponent `g` is nonnegative, so `1-g ≤ 1`. -/
theorem zpow_le_rpow_boundary_rate {g : ℝ} (hg : 0 ≤ g) {r j : ℤ} (hrj : r ≤ j) :
    (3 : ℝ) ^ (r - j) ≤ (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) := by
  have hrjR : (r : ℝ) ≤ (j : ℝ) := by exact_mod_cast hrj
  have hexp : ((r : ℝ) - (j : ℝ)) ≤ -(1 - g) * ((j : ℝ) - (r : ℝ)) := by
    nlinarith only [hg, hrjR]
  rw [← Real.rpow_intCast (3 : ℝ) (r - j)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  push_cast
  linarith only [hexp]

/-- The same conversion for the cross-grid row of the maximal filling: the
printed boundary row `C_dK_{hop}3^{-(1-g)(j-r)}` of
`e.two.grid.whitney.mean.bound` is implied by the sharper integer-power row
of `e.two.grid.whitney.volumes`. -/
theorem sum_relative_volume_row_le_rpow {p q : Mat d} {g : ℝ} (hd : 1 ≤ d)
    (hp : p.PosDef) (hq : q.PosDef) (hg : 0 ≤ g) {n j r : ℤ} (hrn : r < n)
    (hrj : r ≤ j) {y : Vec d} {Zr : Finset (Fin d → ℤ)}
    (hZ : ↑Zr = fillingIndex q n (adaptedCellTranslate p j y) r) {Khop : ℝ}
    (hK : gridRatio q p ≤ Khop) :
    ∑ w ∈ Zr, (volume (adaptedCellAt q r w)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal ≤
      6 * (d : ℝ) * Real.sqrt d * Khop *
        (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hKh : (0 : ℝ) ≤ Khop :=
    le_trans (le_trans zero_le_one (one_le_gridRatio q p)) hK
  have hchop : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * Khop :=
    mul_nonneg (mul_nonneg (by linarith only [hdR]) (Real.sqrt_nonneg _)) hKh
  exact (sum_relative_volume_row_le_hop hd hp hq hrn hZ hK).trans
    (mul_le_mul_of_nonneg_left (zpow_le_rpow_boundary_rate hg hrj) hchop)

/-! ## The annealed row -/

section Annealed

variable {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- **The annealed form of the exhaustion of a target cell.**  The adapted mean of
a target cell of the new grid is below the weighted adapted means of the old
grid's filling from the alignment scale up, plus the mean of the below-start
term.  This is `e.two.grid.whitney.average` read after averaging, in the
shape `e.two.grid.whitney.mean.bound` consumes: one weight per scale, the total
relative volume of the cells of that scale. -/
theorem adaptedMean_le_filling_rows [NeZero d] (hd : 1 ≤ d) (hCd : 0 ≤ Cd)
    (hg : g < 1) (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu nu' : Mat d}
    (hnu : nu.PosDef) (hnu' : nu'.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu))
    (hq' : IsRoundedGrid jStar (roundedGrid jStar nu'))
    {Khop : ℝ} (hK : gridRatio (roundedGrid jStar nu) (roundedGrid jStar nu') ≤ Khop)
    {n j : ℤ} (hjn : jStar ≤ n) (hjj : jStar ≤ j) {z : Fin d → ℤ}
    {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ r, ↑(Z r) = fillingIndex (roundedGrid jStar nu) n
      (adaptedCellAt (roundedGrid jStar nu') j z) r)
    (hcont : ∀ (r : ℤ), ∀ w ∈ Z r,
      adaptedCellAt (roundedGrid jStar nu) r w ⊆ centeredCube d M)
    (hcont' : adaptedCellAt (roundedGrid jStar nu') j z ⊆ centeredCube d M) :
    toFullBlockMat (adaptedMean P (roundedGrid jStar nu') j) ≤
      (∑ r ∈ Finset.Icc jStar n,
        (∑ w ∈ Z r, (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
            (volume (adaptedCellAt (roundedGrid jStar nu') j z)).toReal) •
          toFullBlockMat (adaptedMean P (roundedGrid jStar nu) r)) +
        (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g nu * zetaG g *
          (3 : ℝ) ^ (jStar - j) * ∫ a, Y a ∂P) • toFullBlockMat E := by
  classical
  have hq'pd : (roundedGrid jStar nu').PosDef := Recurrence.posDef_of_isRoundedGrid hq'
  have hpath := coarseBlock_le_filling_rows_add_belowStart
    (y := adaptedCellCenter (roundedGrid jStar nu') j z) hd hCd hg hE hEpd hY hnu hq
    hq'pd hK hjn hZ fun r _ w hw => hcont r w hw
  rw [← adaptedCellAt_eq_adaptedCellTranslate] at hpath
  have hW : HasIntegrableCoarseBlock P (adaptedCellAt (roundedGrid jStar nu') j z) :=
    hasIntegrableCoarseBlock_adaptedCellTranslate hY hnu' hq' j
      (adaptedCellCenter (roundedGrid jStar nu') j z) hcont'
  have hcellint : ∀ r ∈ Finset.Icc jStar n, ∀ w ∈ Z r,
      HasIntegrableCoarseBlock P (adaptedCellAt (roundedGrid jStar nu) r w) :=
    fun r _ w hw => hasIntegrableCoarseBlock_adaptedCellTranslate hY hnu hq r
      (adaptedCellCenter (roundedGrid jStar nu) r w) (hcont r w hw)
  have hGint : Integrable (fun a =>
      (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g nu * zetaG g *
        (3 : ℝ) ^ (jStar - j) * Y a) • toFullBlockMat E) P :=
    ((integrable_of_isWindowMultiplier hY).const_mul _).smul_const _
  have hkey := annealedBlock_le_of_ae_le hW hcellint hGint hpath
  -- the mean of the below-start term
  have hGm : ∫ a, (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g nu * zetaG g *
      (3 : ℝ) ^ (jStar - j) * Y a) • toFullBlockMat E ∂P =
      (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g nu * zetaG g *
        (3 : ℝ) ^ (jStar - j) * ∫ a, Y a ∂P) • toFullBlockMat E := by
    rw [integral_smul_const, integral_const_mul]
  -- stationarity collapses every row to the adapted mean of its scale
  have hrows : ∀ r ∈ Finset.Icc jStar n,
      (∑ w ∈ Z r, ((volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
          (volume (adaptedCellAt (roundedGrid jStar nu') j z)).toReal) •
            toFullBlockMat
              (annealedBlock P (adaptedCellAt (roundedGrid jStar nu) r w))) =
        (∑ w ∈ Z r, (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
            (volume (adaptedCellAt (roundedGrid jStar nu') j z)).toReal) •
          toFullBlockMat (adaptedMean P (roundedGrid jStar nu) r) := by
    intro r hr
    have hjr : jStar ≤ r := (Finset.mem_Icc.mp hr).1
    have hmeas : HasMeasurableCoarseBlock P (adaptedCell (roundedGrid jStar nu) r) :=
      Recurrence.hasMeasurableCoarseBlock_adaptedCell P (Recurrence.posDef_of_isRoundedGrid hq) r
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun w _ => by
      rw [Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hP hq hjr hmeas w]
  have hmeas' : HasMeasurableCoarseBlock P (adaptedCell (roundedGrid jStar nu') j) :=
    Recurrence.hasMeasurableCoarseBlock_adaptedCell P hq'pd j
  rw [hGm, Finset.sum_congr rfl hrows] at hkey
  rwa [Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean hP hq' hjj hmeas' z] at hkey

/-! ## The normalized source row -/

/-- **The normalized source row `ε_j` of `e.two.grid.whitney.mean.bound`.**  The
below-start remainder of the exhaustion is a nonnegative multiple of the reference
block; normalized by the new terminal block it is below `ε_j I`, with
`ε_j = cκ_𝐄B_{\mathbf q'}E[Y_P]` for the below-start coefficient `c`.  The
terminal normalization `e.two.grid.source.normalization` is
what measures the reference block against the terminal mean. -/
theorem toFullBlockMat_le_srcRow_smul_one [NeZero d] [IsProbabilityMeasure P]
    (hCd : 0 < Cd) (hg : g < 1) (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu' : Mat d} (hnu' : nu'.PosDef)
    (hq' : IsRoundedGrid jStar (roundedGrid jStar nu')) {nT : ℤ} (hnT : jStar ≤ nT)
    (hcontT : adaptedCell (roundedGrid jStar nu') nT ⊆ centeredCube d M) {c : ℝ}
    (hc : 0 ≤ c) {Rm : BlockMat d}
    (hRm : toFullBlockMat Rm =
      matSqrt ((toFullBlockMat (adaptedMean P (roundedGrid jStar nu') nT))⁻¹) *
        (c • toFullBlockMat E) *
        matSqrt ((toFullBlockMat (adaptedMean P (roundedGrid jStar nu') nT))⁻¹)) :
    toFullBlockMat Rm ≤
      (c * (kappaRef E * (boundaryConst Cd g nu' * ∫ a, Y a ∂P))) •
        (1 : FullBlockMat d) := by
  set F : BlockMat d := adaptedMean P (roundedGrid jStar nu') nT with hF
  have hFsym : IsSymmetricBlockMat F := Recurrence.isSymmetricBlockMat_adaptedMean P _ nT
  have hFpd : Book.Ch02.BlockPosDef F :=
    blockPosDef_adaptedMean_of_isWindowMultiplier hY hnu' hq' hnT hcontT
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hFsym hFpd
  have hkap := blockSize_adaptedMean_le hCd hg hE hEpd hY hnu' hq' hnT hcontT
  obtain ⟨hup, -⟩ := PortableHistory.blockSize_sandwich hE hFsym hFpd
  have hmono : blockSize E F • toFullBlockMat F ≤
      (kappaRef E * (boundaryConst Cd g nu' * ∫ a, Y a ∂P)) • toFullBlockMat F := by
    refine Matrix.le_iff.mpr ?_
    rw [← sub_smul]
    exact hFfull.posSemidef.smul (by linarith only [hkap])
  have hconj :=
    (conj_normalize hFfull (kappaRef E * (boundaryConst Cd g nu' * ∫ a, Y a ∂P))).mp
      (hup.trans hmono)
  have hsm := smul_le_smul_of_le hc hconj
  rw [hRm, Matrix.mul_smul, Matrix.smul_mul, ← smul_smul]
  exact hsm

end Annealed

/-! ## The nonlinear row -/

section Row

variable {P : Measure (CoeffSpace d)} {g : ℝ} {jStar : ℤ}

/-- **`e.two.grid.whitney.mean.bound` at a continued target level, with the
weights of the filling discharged.**  The relative volumes of the maximal filling
of a target cell of the new grid are nonnegative, of total mass at most one, and
obey the conservative boundary row `C_dK_{hop}3^{-(1-g)(j-r)}`; those are the
three weight hypotheses of the printed row.  The bridge error is converted from
`3η = 3η_x/(1-η_x)` to `4η_x` on the box `0 ≤ η_x ≤ 1/4`, so the row comes out in
exactly the shape `e.two.grid.profile` binds, at
`C_1 = A`, `C_2 = AC_dK_{hop}`, `C_3 = 4A`, `C_4 = A` with
`A = 2^{2Q+1}(1+2d)^Q`. -/
theorem nonlinear_row_of_filling [NeZero d] [IsProbabilityMeasure P] (hd : 1 ≤ d)
    {Q : ℝ} (hQ : 1 ≤ Q) (hg : 0 ≤ g) (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q p : Mat d} (hp : p.PosDef) {l : ℤ} (hqr : IsRoundedGrid l q) (hlj : l ≤ jStar)
    {Khop : ℝ} (hK : gridRatio q p ≤ Khop) {t j lam : ℤ} (hlam : jStar ≤ j - lam)
    (hlam0 : 0 ≤ lam) (hjt : j - lam ≤ t)
    (hfin : ∀ r : ℤ, jStar ≤ r → r ≤ t → HasFiniteAdaptedMean P q r)
    {y : Vec d} {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ r, ↑(Z r) = fillingIndex q (j - lam) (adaptedCellTranslate p j y) r)
    {Pnew Pbar Mblk Phat KW Rm : BlockMat d} {S : FullBlockMat d} {etaX eps : ℝ}
    (heta0 : 0 ≤ etaX) (heta4 : etaX ≤ 1 / 4) (heps : 0 ≤ eps)
    (hS : Sᵀ * S ≤ (1 + etaX / (1 - etaX)) • (1 : FullBlockMat d))
    (hR : toFullBlockMat Rm ≤ eps • (1 : FullBlockMat d))
    (hPbar : toFullBlockMat Pbar =
      ∑ r ∈ Finset.Icc jStar (j - lam),
          (∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal) •
            toFullBlockMat (relMean P q r t) +
        (1 - ∑ r ∈ Finset.Icc jStar (j - lam),
          ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal) • (1 : FullBlockMat d))
    (hM : toFullBlockMat Mblk = Sᵀ * toFullBlockMat Pbar * S - 1)
    (hPhat : toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk))
    (hKW : toFullBlockMat KW =
      Sᵀ * toFullBlockMat Pbar * S -
        (1 - ∑ r ∈ Finset.Icc jStar (j - lam),
          ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal) • (Sᵀ * S) +
        toFullBlockMat Rm)
    (hIP : (1 : FullBlockMat d) ≤ toFullBlockMat Pnew)
    (hPK : toFullBlockMat Pnew ≤ toFullBlockMat KW) :
    frakH Q Pnew ≤
      (2 ^ (2 * Q + 1) * (1 + 2 * (d : ℝ)) ^ Q) * frakH Q (relMean P q (j - lam) t) +
        (2 ^ (2 * Q + 1) * (1 + 2 * (d : ℝ)) ^ Q * (6 * (d : ℝ) * Real.sqrt d * Khop)) *
          ∑ r ∈ Finset.Ico jStar (j - lam),
            (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (relMean P q r t) +
        (4 * (2 ^ (2 * Q + 1) * (1 + 2 * (d : ℝ)) ^ Q)) * etaX +
        (2 ^ (2 * Q + 1) * (1 + 2 * (d : ℝ)) ^ Q) * (eps + eps ^ Q) := by
  classical
  have hqpd : q.PosDef := Recurrence.posDef_of_isRoundedGrid hqr
  have hden : (0 : ℝ) < 1 - etaX := by linarith only [heta4]
  have hth : ∀ r ∈ Finset.Icc jStar (j - lam),
      (0 : ℝ) ≤ ∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal := fun _ _ =>
    Finset.sum_nonneg fun _ _ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hm := sum_relative_volume_le_one hp hqpd (R := Finset.Icc jStar (j - lam)) hZ
  have hbdry : ∀ r ∈ Finset.Ico jStar (j - lam),
      (∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
          (volume (adaptedCellTranslate p j y)).toReal) ≤
        6 * (d : ℝ) * Real.sqrt d * Khop *
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) := by
    intro r hr
    have hrlt : r < j - lam := (Finset.mem_Ico.mp hr).2
    exact sum_relative_volume_row_le_rpow hd hp hqpd hg hrlt (by omega) (hZ r) hK
  have hPold : ∀ r ∈ Finset.Icc jStar (j - lam),
      (1 : FullBlockMat d) ≤ toFullBlockMat (relMean P q r t) := by
    intro r hr
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hr
    exact PortableHistory.one_le_relMean_window hP hqr hlj hfin h1 (le_trans h2 hjt) le_rfl
  have heta : (0 : ℝ) ≤ etaX / (1 - etaX) := div_nonneg heta0 hden.le
  have heta3 : etaX / (1 - etaX) ≤ 1 / 3 := by
    rw [div_le_iff₀ hden]
    linarith only [heta4]
  have hrow := nonlinear_row hd hQ hlam hth hm hbdry hPold hPbar heta heta3 heps hS hR
    hM hPhat hKW hIP hPK
  -- the printed bridge conversion on the box `0 ≤ η_x ≤ 1/4`
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hA0 : (0 : ℝ) ≤ 2 ^ (2 * Q + 1) * (1 + 2 * (d : ℝ)) ^ Q :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by linarith only [hdR]) _)
  have hconv : 3 * (etaX / (1 - etaX)) ≤ 4 * etaX := by
    rw [mul_div_assoc', div_le_iff₀ hden]
    nlinarith only [heta0, heta4, hden]
  have hmul := mul_le_mul_of_nonneg_left hconv hA0
  nlinarith only [hrow, hmul]

end Row

end

end Transport
end HighContrast
end Homogenization
