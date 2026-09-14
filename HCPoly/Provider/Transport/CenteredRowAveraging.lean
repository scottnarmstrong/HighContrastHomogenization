/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.FiniteRangeAveraging
import HCPoly.Provider.Transport.WhitneySquareWeights

/-!
# The centered matrix sum of the filling rows

The centered half of the principal cell sum of the grid transport is the
random matrix

`Σ_r Σ_{V ∈ 𝒱_r(W;q)} (|V|/|W|)(𝐀(V) - E_r^q)`,

and the square-weight bounds for the boundary and bulk cells are turned into
bounds on its mixed norm by `l.fixed.geometry.matrix.averaging`, applied one row
at a time.  This file performs that application.

The match between the two is exact, and that is the point of the file.  The
averaging lemma is stated for the *equal-weight* average of `M` aligned cells
and produces the gain `M^{-1/2}`; a filling row consists of aligned cells of one
scale, so all its weights are the same real number, and for such a row

`(Σ_V (|V|/|W|)²)^{1/2} = (Σ_V |V|/|W|) · M^{-1/2}`

is an identity, not an estimate.  The `ℓ²` weight of the printed square-weight
displays is therefore exactly what the equal-weight lemma delivers once the row
is written as its total weight times its average, and no weighted generalization
of `l.fixed.geometry.matrix.averaging` is needed.

The rows are summed at the scalar level.  Normalization is a fixed real-linear
map of the entries of a doubled block, so an entry of the normalized total is
the weighted total of the entries of the normalized centered responses; the
entries obey Minkowski's inequality, each row is paid by the colour-split
estimate of `l.fixed.geometry.matrix.averaging`, and the `4d²` entries are
reassembled at the printed cost `2d`.  The scale-`r` moment bound is a
hypothesis: the transport reads it from the cell-moment clause of
`e.source.adapted.bound`, which the window multiplier supplies.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix

noncomputable section

variable {d : ℕ}

/-! ## The exact equal-weight match -/

/-- **The `ℓ²` weight of a constant row.**  A finite family whose weights are all
the same nonnegative real has `ℓ²` norm equal to that weight times the square
root of the cardinality. -/
theorem sqrt_sum_sq_const {ι : Type*} (Z : Finset ι) {c : ℝ} (hc : 0 ≤ c) :
    Real.sqrt (∑ _w ∈ Z, c ^ 2) = c * Real.sqrt (Z.card : ℝ) := by
  rw [Finset.sum_const, nsmul_eq_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq hc]
  ring

/-! ## Normalization is linear on the entries -/

/-- **An entry of the normalized total is the total of the entries.**
Normalization by a deterministic block is a fixed real-linear map of the entries
of a doubled block. -/
theorem normalizedBlock_sum_apply {ι : Type*} (s : Finset ι) (M : ι → FullBlockMat d)
    (F : BlockMat d) (α β : BlockCoord d) :
    toFullBlockMat (normalizedBlock (ofFullBlockMat (∑ i ∈ s, M i)) F) α β =
      ∑ i ∈ s, toFullBlockMat (normalizedBlock (ofFullBlockMat (M i)) F) α β := by
  set sq : FullBlockMat d := matSqrt ((toFullBlockMat F)⁻¹) with hsq
  have hterm : ∀ γ δ : BlockCoord d,
      sq α δ * (∑ i ∈ s, M i δ γ) * sq γ β = ∑ i ∈ s, sq α δ * M i δ γ * sq γ β := by
    intro γ δ
    rw [Finset.mul_sum, Finset.sum_mul]
  simp only [Recurrence.toFullBlockMat_normalizedBlock_apply, toFullBlockMat_ofFullBlockMat,
    Matrix.sum_apply, ← hsq]
  calc ∑ γ : BlockCoord d, ∑ δ : BlockCoord d, sq α δ * (∑ i ∈ s, M i δ γ) * sq γ β
      = ∑ γ : BlockCoord d, ∑ δ : BlockCoord d, ∑ i ∈ s, sq α δ * M i δ γ * sq γ β :=
        Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => hterm γ δ
    _ = ∑ γ : BlockCoord d, ∑ i ∈ s, ∑ δ : BlockCoord d, sq α δ * M i δ γ * sq γ β :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ γ : BlockCoord d, ∑ δ : BlockCoord d, sq α δ * M i δ γ * sq γ β :=
        Finset.sum_comm

/-- **An entry of the normalized scaling is the scaled entry.** -/
theorem normalizedBlock_smul_apply (t : ℝ) (M : FullBlockMat d) (F : BlockMat d)
    (α β : BlockCoord d) :
    toFullBlockMat (normalizedBlock (ofFullBlockMat (t • M)) F) α β =
      t * toFullBlockMat (normalizedBlock (ofFullBlockMat M) F) α β := by
  set sq : FullBlockMat d := matSqrt ((toFullBlockMat F)⁻¹) with hsq
  simp only [Recurrence.toFullBlockMat_normalizedBlock_apply, toFullBlockMat_ofFullBlockMat,
    Matrix.smul_apply, smul_eq_mul, ← hsq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun δ _ => by ring

/-! ## Reassembling the entries -/

/-- The `ℓ²` combination of the `4d²` entrywise bounds costs the factor `2d` of
the printed proof.  This is the reassembly step of
`l.fixed.geometry.matrix.averaging`, restated for a bound that is not of the
form the recurrence consumes. -/
theorem rpow_sum_sq_le' {x : ℝ≥0∞} {y : BlockCoord d → BlockCoord d → ℝ≥0∞}
    (h : ∀ α β, y α β ≤ x) :
    (∑ α : BlockCoord d, ∑ β : BlockCoord d, y α β ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (2 * (d : ℝ)) * x := by
  have hsq : ∀ z : ℝ≥0∞, z ^ (2 : ℝ) = z * z := fun z => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, pow_two]
  have hcard : (Finset.univ : Finset (BlockCoord d)).card = 2 * d := by
    simp [Finset.card_univ, Fintype.card_sum, two_mul]
  have hc : ENNReal.ofReal (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ≥0∞) := by
    rw [show (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  have heq : (∑ _α : BlockCoord d, ∑ _β : BlockCoord d, x ^ (2 : ℝ)) =
      (((2 * d : ℕ) : ℝ≥0∞) * x) ^ (2 : ℝ) := by
    rw [Finset.sum_const, Finset.sum_const, hcard, nsmul_eq_mul, nsmul_eq_mul, hsq, hsq]
    ring
  have hle : (∑ α : BlockCoord d, ∑ β : BlockCoord d, y α β ^ (2 : ℝ)) ≤
      (((2 * d : ℕ) : ℝ≥0∞) * x) ^ (2 : ℝ) :=
    le_trans (Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ =>
      ENNReal.rpow_le_rpow (h α β) (by norm_num)) (le_of_eq heq)
  calc (∑ α : BlockCoord d, ∑ β : BlockCoord d, y α β ^ (2 : ℝ)) ^ (2⁻¹ : ℝ)
      ≤ ((((2 * d : ℕ) : ℝ≥0∞) * x) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ((2 * d : ℕ) : ℝ≥0∞) * x := by
        rw [← ENNReal.rpow_mul]
        norm_num
    _ = ENNReal.ofReal (2 * (d : ℝ)) * x := by rw [hc]

/-! ## The centered matrix sum of the rows -/

/-- **`l.fixed.geometry.matrix.averaging` applied to the filling rows.**  The
mixed norm of the centered matrix sum of a finite family of filling rows is at
most the printed constant times the sum, over the rows, of the row's `ℓ²` weight
times the row's moment bound.

A row is indexed by `Z r` and carries the single relative volume `c r`, since
all its cells are aligned cells of the scale `r`; the `ℓ²` weight of such a row
is `c r · M_r^{1/2}` by `sqrt_sum_sq_const`, which is what the equal-weight gain
`M_r^{-1/2}` of `l.fixed.geometry.matrix.averaging` produces once the row is
written as its total weight times its average.  The exhibited constant is the
one of the averaging lemma,
`2d(2Q + 4C_{RB}√Q)√(3^d)`. -/
theorem lqSchattenSize_filling_rows_le {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hPs : HCPoly.Frozen.IsStationaryLaw P) (hP : HCPoly.Frozen.IsUnitRangeLaw P) {Q : ℝ}
    (hQ : 2 ≤ Q) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) (F : BlockMat d)
    {R : Finset ℤ} {Z : ℤ → Finset (Fin d → ℤ)} {c : ℤ → ℝ} {v : ℤ → ℝ≥0∞}
    (hc : ∀ r ∈ R, 0 ≤ c r) (hl : ∀ r ∈ R, l ≤ r)
    (hint : ∀ r ∈ R, HasFiniteAdaptedMean P q r) (hv : ∀ r ∈ R, v r ≠ ⊤)
    (hbd : ∀ r ∈ R, ∀ w ∈ Z r, ∀ α β : BlockCoord d,
      lqNorm P Q (fun a => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q r w) a) (adaptedMean P q r)) F) α β) ≤ v r) :
    lqSchattenSize P Q (fun a => ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r,
        c r • toFullBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
          (adaptedMean P q r)))) F ≤
      ENNReal.ofReal (2 * (d : ℝ) *
          ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
            Real.sqrt ((3 : ℝ) ^ d))) *
        ∑ r ∈ R, ENNReal.ofReal (c r * Real.sqrt ((Z r).card : ℝ)) * v r := by
  classical
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_two hQ
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Q := ENNReal.one_le_ofReal.mpr (by linarith only [hQ])
  set B : ℝ := 2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q with hB
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hB]
    have : (0 : ℝ) ≤ IndependentSums.rosenthalBennettIntegralConst := by
      simp only [IndependentSums.rosenthalBennettIntegralConst]
      positivity
    positivity
  -- the entries of the normalized total
  have hcell : ∀ (a : CoeffSpace d) (r : ℤ) (w : Fin d → ℤ),
      IsSymmetricBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
        (adaptedMean P q r)) := fun a r w =>
    Recurrence.isSymmetricBlockMat_coarseBlock_sub a (Recurrence.isSymmetricBlockMat_adaptedMean P q r)
  have hsymm : ∀ a : CoeffSpace d, IsSymmetricBlockMat (ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r,
      c r • toFullBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
        (adaptedMean P q r)))) := by
    intro a
    refine isSymmetricBlockMat_of_isSymm ?_
    ext γ δ
    simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun w _ =>
      congrArg _ ((isSymm_toFullBlockMat_of_isSymmetricBlockMat (hcell a r w)).apply γ δ)
  -- the entries of the normalized total are the weighted totals of the entries
  have hentry : ∀ (a : CoeffSpace d) (alp bet : BlockCoord d),
      toFullBlockMat (normalizedBlock (ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r,
          c r • toFullBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
            (adaptedMean P q r)))) F) alp bet =
        ∑ r ∈ R, c r * ∑ w ∈ Z r, toFullBlockMat (normalizedBlock
          (blockSub (coarseBlock (adaptedCellAt q r w) a) (adaptedMean P q r)) F) alp bet := by
    intro a alp bet
    rw [normalizedBlock_sum_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [normalizedBlock_sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by
      rw [normalizedBlock_smul_apply, ofFullBlockMat_toFullBlockMat]
  -- the rows as functions of the sample
  set G : ℤ → BlockCoord d → BlockCoord d → CoeffSpace d → ℝ := fun r alp bet a =>
    ∑ w ∈ Z r, toFullBlockMat (normalizedBlock
      (blockSub (coarseBlock (adaptedCellAt q r w) a) (adaptedMean P q r)) F) alp bet with hG
  have hGmeas : ∀ (r : ℤ) (alp bet : BlockCoord d), AEStronglyMeasurable (G r alp bet) P := by
    intro r alp bet
    have hsum := Finset.aestronglyMeasurable_sum (Z r) fun w (_ : w ∈ Z r) =>
      Recurrence.aestronglyMeasurable_toFullBlockMat_normalizedBlock_blockSub
        (Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hqPD r w) (adaptedMean P q r) F alp bet
    refine hsum.congr (_root_.Filter.Eventually.of_forall fun a => ?_)
    simp only [Finset.sum_apply]
    rfl
  have hfun : ∀ alp bet : BlockCoord d,
      (fun a => toFullBlockMat (normalizedBlock (ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r,
          c r • toFullBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
            (adaptedMean P q r)))) F) alp bet) = ∑ r ∈ R, c r • G r alp bet := by
    intro alp bet
    funext a
    rw [hentry a alp bet, Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => rfl
  have hnorm : ∀ alp bet : BlockCoord d,
      lqNorm P Q (fun a => toFullBlockMat (normalizedBlock (ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r,
          c r • toFullBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
            (adaptedMean P q r)))) F) alp bet) ≤
        ∑ r ∈ R, ENNReal.ofReal (c r) * lqNorm P Q (G r alp bet) := by
    intro alp bet
    rw [lqNorm, hfun alp bet]
    refine le_trans (eLpNorm_sum_le (fun r _ => (hGmeas r alp bet).const_smul (c r)) hone) ?_
    refine Finset.sum_le_sum fun r hr => ?_
    rw [eLpNorm_const_smul, lqNorm, ← ofReal_norm, Real.norm_of_nonneg (hc r hr)]
  -- the per-row estimate of the finite-range averaging lemma
  have hrow : ∀ (alp bet : BlockCoord d), ∀ r ∈ R,
      ENNReal.ofReal (c r) * lqNorm P Q (G r alp bet) ≤
        ENNReal.ofReal (B * Real.sqrt ((3 : ℝ) ^ d)) *
          (ENNReal.ofReal (c r * Real.sqrt ((Z r).card : ℝ)) * v r) := by
    intro alp bet r hr
    have haux := Recurrence.lqNorm_sum_aligned_le hPs hP hQ hq (hl r hr) (hint r hr) F (hv r hr)
      (Z r) alp bet fun w hw => hbd r hr w hw alp bet
    have hmul := mul_le_mul' (le_refl (ENNReal.ofReal (c r))) haux
    refine le_trans hmul (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (hc r hr),
      show c r * (B * (Real.sqrt ((3 : ℝ) ^ d) * Real.sqrt ((Z r).card : ℝ) * (v r).toReal)) =
        B * Real.sqrt ((3 : ℝ) ^ d) *
          (c r * Real.sqrt ((Z r).card : ℝ) * (v r).toReal) by ring,
      ENNReal.ofReal_mul (mul_nonneg hB0 (Real.sqrt_nonneg _)),
      ENNReal.ofReal_mul (mul_nonneg (hc r hr) (Real.sqrt_nonneg _)),
      ENNReal.ofReal_toReal (hv r hr)]
  -- the entrywise bound
  have hx : ∀ alp bet : BlockCoord d,
      lqNorm P Q (fun a => toFullBlockMat (normalizedBlock (ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r,
          c r • toFullBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
            (adaptedMean P q r)))) F) alp bet) ≤
        ENNReal.ofReal (B * Real.sqrt ((3 : ℝ) ^ d)) *
          ∑ r ∈ R, ENNReal.ofReal (c r * Real.sqrt ((Z r).card : ℝ)) * v r := by
    intro alp bet
    refine le_trans (hnorm alp bet) ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (hrow alp bet)
  -- measurability of the entries of the normalized total
  have hmeas : ∀ alp bet : BlockCoord d, AEStronglyMeasurable
      (fun a => toFullBlockMat (normalizedBlock (ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r,
        c r • toFullBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
          (adaptedMean P q r)))) F) alp bet) P := by
    intro alp bet
    rw [hfun alp bet]
    exact Finset.aestronglyMeasurable_sum _ fun r _ => (hGmeas r alp bet).const_smul (c r)
  -- reassembling the entries
  refine le_trans (Recurrence.lqSchattenSize_le P hQ F hsymm hmeas) ?_
  refine le_trans (rpow_sum_sq_le' fun alp bet => hx alp bet) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end

end Transport
end HighContrast
end Homogenization
