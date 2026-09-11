/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CellDomination
import HCPoly.Setup.SourceObjects
import HCPoly.Geometry.SizeAlignment

/-!
# Well-definedness of the transported quantities on a bounded window

`p.two.grid.transport` states its well-definedness as a
conclusion, not as a hypothesis: under the containment of the two grid towers in
the window, the annealed blocks of both grids are finite and positive definite at
every scale of the range, their centered moments are finite, and the means are
ordered, so the histories and the profile denote the printed quantities.

That conclusion is proved here from the window multiplier alone.  A common
multiplier `Y_P` serves every adapted cell of every rounded grid inside the
window, in the form `𝐀(y + ⋄_r^q) ≤ B_q Y_P 3^{g(j_* - r)_+}𝐄`; at or above the
alignment scale the discount is one, so on a cell of the range the response is
below `B_q Y_P 𝐄`.  Three consequences follow, and they are exactly the printed
ones.

The entries of the response are then bounded by a multiple of `Y_P`, which is
integrable because its excess over one has the source gauge's tail; the annealed
block is therefore an expectation, and being an expectation of positive definite
responses it is positive definite.  The centered moment is the `L^Q` norm of the
Schatten size of the response centered and normalized by that same mean, and the
Loewner bound turns it into a multiple of `Y_P` as well, whose `L^Q` norm the
window multiplier bounds outright.  The mean order is then the subdivision
argument for the variational coarse block taken from HC, which needs only the
finiteness just obtained.

Nothing here uses `e.source.adapted.bound`: the terminal comparison and the
cell-moment clause the reference text quotes at this point are, for the cells of
the range, immediate from the multiplier's own primal cell bound.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The two structural readings of the window hypotheses -/

/-- A coupled window puts its alignment scale above the dimensional floor, so
the rounding of any positive witness at that scale is a rounded adapted grid. -/
theorem isRoundedGrid_roundedGrid_of_isCoupledWindow {Q K : ℝ} {jStar M : ℤ}
    (hw : IsCoupledWindow d Q K jStar M) {nu : Mat d} (hnu : nu.PosDef) :
    IsRoundedGrid jStar (roundedGrid jStar nu) :=
  ⟨le_trans (le_max_left _ _) hw.1, nu, hnu, rfl⟩

/-- The window multiplier is integrable: its `L^1` moment is bounded by the
weak-Orlicz moment display at `p = 1`. -/
theorem integrable_of_isWindowMultiplier {P : Measure (CoeffSpace d)} {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) : Integrable Y P := by
  have h1 := hY.lp_moment 1 le_rfl
  rw [ENNReal.ofReal_one] at h1
  exact memLp_one_iff_integrable.mp
    ⟨hY.measurable.aestronglyMeasurable, lt_of_le_of_lt h1 ENNReal.ofReal_lt_top⟩

/-- **The primal cell bound on an adapted cell of the range.**  The multiplier's
bound is stated for an arbitrary translate of an adapted cell and carries the
burn discount `3^{g(j_* - r)_+}`; at the centered cell of a scale at or above
the alignment the translate is the cell itself and the discount is one. -/
theorem ae_blockMatLoewnerLE_coarseBlock_adaptedCell {P : Measure (CoeffSpace d)}
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ}
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    {j : ℤ} (hj : jStar ≤ j)
    (hcont : adaptedCell (roundedGrid jStar nu) j ⊆ centeredCube d M) :
    ∀ᵐ a ∂P, BlockMatLoewnerLE
      (coarseBlock (adaptedCell (roundedGrid jStar nu) j) a)
      (blockScale (boundaryConst Cd g nu * Y a) E) := by
  have hzero : adaptedCellTranslate (roundedGrid jStar nu) j 0 =
      adaptedCell (roundedGrid jStar nu) j := by
    simp [adaptedCellTranslate]
  have hburn : burnDiscount g jStar j = 1 := by
    have hle : ((jStar : ℝ) - (j : ℝ)) ≤ 0 := by
      have hc : (jStar : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      linarith only [hc]
    rw [burnDiscount, max_eq_right hle, mul_zero, Real.rpow_zero]
  filter_upwards [hY.adapted_primal] with a ha
  have hloew := ha nu hnu j 0 (by rw [hzero]; exact hcont)
  rwa [hzero, hburn, mul_one] at hloew

/-! ## The three definedness clauses at one scale -/

/-- **The annealed block of an adapted cell of the range is an expectation.**
The entries of the response are bounded by a multiple of the window multiplier,
which is integrable. -/
theorem hasFiniteAdaptedMean_of_isWindowMultiplier {P : Measure (CoeffSpace d)}
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ}
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {j : ℤ} (hj : jStar ≤ j)
    (hcont : adaptedCell (roundedGrid jStar nu) j ⊆ centeredCube d M) :
    HasFiniteAdaptedMean P (roundedGrid jStar nu) j := by
  intro α β
  refine Integrable.mono'
    ((integrable_of_isWindowMultiplier hY).const_mul
      (2 * (|boundaryConst Cd g nu| * blockEntrySum E)))
    (Recurrence.hasMeasurableCoarseBlock_adaptedCell_of_isRoundedGrid P hq j α β) ?_
  filter_upwards [ae_blockMatLoewnerLE_coarseBlock_adaptedCell hY hnu hj hcont] with a ha
  have h := abs_blockMatEntry_coarseBlock_le_of_blockMatLoewnerLE ha α β
  rw [abs_mul, abs_of_nonneg (le_trans zero_le_one (hY.one_le a))] at h
  rw [Real.norm_eq_abs]
  exact h.trans_eq (by ring)

/-- **The annealed block of an adapted cell of the range is positive definite.**
The pathwise positivity of the response integrates as soon as the block is an
expectation. -/
theorem blockPosDef_adaptedMean_of_isWindowMultiplier {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {j : ℤ} (hj : jStar ≤ j)
    (hcont : adaptedCell (roundedGrid jStar nu) j ⊆ centeredCube d M) :
    Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid jStar nu) j) :=
  Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq j
    (hasFiniteAdaptedMean_of_isWindowMultiplier hY hnu hq hj hcont)

/-- **The centered moment of an adapted cell of the range is finite.**  The
centered normalized response has Schatten size at most a multiple of the window
multiplier — the multiple being the trace of the reference block in the
normalization of the annealed mean — and the multiplier's `L^Q` moment is
bounded by the weak-Orlicz moment display. -/
theorem centeredMoment_ne_top_of_isWindowMultiplier {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {Q : ℝ} (hQ : 1 ≤ Q) {j : ℤ}
    (hj : jStar ≤ j)
    (hcont : adaptedCell (roundedGrid jStar nu) j ⊆ centeredCube d M) :
    centeredMoment P Q (roundedGrid jStar nu) j ≠ ⊤ := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le one_pos hQ
  have hint := hasFiniteAdaptedMean_of_isWindowMultiplier hY hnu hq hj hcont
  set Em : BlockMat d := adaptedMean P (roundedGrid jStar nu) j
  have hEmsym : IsSymmetricBlockMat Em := Recurrence.isSymmetricBlockMat_adaptedMean _ _ _
  have hEmpd : (toFullBlockMat Em).PosDef :=
    Recurrence.posDef_toFullBlockMat_adaptedMean hq j hint
  set tau : ℝ := Matrix.trace (toFullBlockMat (normalizedBlock E Em))
  set C : ℝ := (2 * d : ℝ) ^ Q⁻¹ * (1 + |boundaryConst Cd g nu * tau|) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hsymA : ∀ a : CoeffSpace d,
      IsSymmetricBlockMat (coarseBlock (adaptedCell (roundedGrid jStar nu) j) a) := by
    intro a
    rw [coarseBlock]
    exact isSymmetricBlockMat_coarseBlockMatrix _ _
  -- the pathwise bound on the Schatten size of the centered response
  have hptwise : ∀ᵐ a ∂P,
      schattenSize Q (blockSub (coarseBlock (adaptedCell (roundedGrid jStar nu) j) a) Em)
        Em ≤ C * Y a := by
    filter_upwards [ae_blockMatLoewnerLE_coarseBlock_adaptedCell hY hnu hj hcont] with a ha
    have hAsym : IsSymmetricBlockMat
        (coarseBlock (adaptedCell (roundedGrid jStar nu) j) a) := hsymA a
    have hApsd : (toFullBlockMat
        (coarseBlock (adaptedCell (roundedGrid jStar nu) j) a)).PosSemidef :=
      (posDef_toFullBlockMat hAsym
        (Recurrence.blockPosDef_coarseBlock_adaptedCell_of_isRoundedGrid hq j a)).posSemidef
    have hflat : toFullBlockMat (coarseBlock (adaptedCell (roundedGrid jStar nu) j) a) ≤
        (boundaryConst Cd g nu * Y a) • toFullBlockMat E := by
      have h := le_of_blockMatLoewnerLE hAsym (isSymmetricBlockMat_blockScale _ hE) ha
      rwa [toFullBlockMat_blockScale] at h
    have hstep := schattenSize_blockSub_le_of_trace_le hQ0 hAsym hApsd hEmsym hEmpd
      (trace_toFullBlockMat_normalizedBlock_le hEmpd hflat)
    refine hstep.trans ?_
    have hY1 : (1 : ℝ) ≤ Y a := hY.one_le a
    have hrw : |boundaryConst Cd g nu * Y a * tau| = |boundaryConst Cd g nu * tau| * Y a := by
      rw [show boundaryConst Cd g nu * Y a * tau = boundaryConst Cd g nu * tau * Y a by ring,
        abs_mul, abs_of_nonneg (le_trans zero_le_one hY1)]
    rw [hrw, hC]
    have hpow : (0 : ℝ) ≤ (2 * d : ℝ) ^ Q⁻¹ := Real.rpow_nonneg (by positivity) _
    have hmid : 1 + |boundaryConst Cd g nu * tau| * Y a ≤
        (1 + |boundaryConst Cd g nu * tau|) * Y a := by
      rw [show (1 + |boundaryConst Cd g nu * tau|) * Y a =
        Y a + |boundaryConst Cd g nu * tau| * Y a by ring]
      linarith only [hY1]
    calc (2 * d : ℝ) ^ Q⁻¹ * (1 + |boundaryConst Cd g nu * tau| * Y a)
        ≤ (2 * d : ℝ) ^ Q⁻¹ * ((1 + |boundaryConst Cd g nu * tau|) * Y a) :=
          mul_le_mul_of_nonneg_left hmid hpow
      _ = (2 * d : ℝ) ^ Q⁻¹ * (1 + |boundaryConst Cd g nu * tau|) * Y a := by ring
  -- the mixed norm of a multiple of the multiplier is finite
  have hnn : ∀ a : CoeffSpace d,
      (0 : ℝ) ≤ schattenSize Q
        (blockSub (coarseBlock (adaptedCell (roundedGrid jStar nu) j) a) Em) Em :=
    fun a => Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock
        (isSymmetricBlockMat_blockSub (hsymA a) hEmsym)) Q
  have hmono : centeredMoment P Q (roundedGrid jStar nu) j ≤
      eLpNorm (C • Y) (ENNReal.ofReal Q) P := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hptwise] with a ha
    show ‖schattenSize Q
      (blockSub (coarseBlock (adaptedCell (roundedGrid jStar nu) j) a) Em) Em‖ ≤ ‖C * Y a‖
    rw [Real.norm_of_nonneg (hnn a),
      Real.norm_of_nonneg (mul_nonneg hC0 (le_trans zero_le_one (hY.one_le a)))]
    exact ha
  refine ne_of_lt (lt_of_le_of_lt hmono ?_)
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hC0]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_of_le_of_lt (hY.lp_moment Q hQ) ENNReal.ofReal_lt_top)

/-! ## The mean order and the packaged definedness -/

/-- **The annealed means of the range are ordered.**  The subdivision and
monotonicity argument for the variational coarse block taken from HC applies
once both means are expectations. -/
theorem adaptedMean_le_of_isWindowMultiplier [NeZero d] {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {j T : ℤ} (hj : jStar ≤ j)
    (hjT : j ≤ T)
    (hcontj : adaptedCell (roundedGrid jStar nu) j ⊆ centeredCube d M)
    (hcontT : adaptedCell (roundedGrid jStar nu) T ⊆ centeredCube d M) :
    BlockMatLoewnerLE (adaptedMean P (roundedGrid jStar nu) T)
      (adaptedMean P (roundedGrid jStar nu) j) :=
  Recurrence.adaptedMean_le hP hq hj hjT
    (hasFiniteAdaptedMean_of_isWindowMultiplier hY hnu hq hj hcontj)
    (hasFiniteAdaptedMean_of_isWindowMultiplier hY hnu hq (hj.trans hjT) hcontT)

/-- **The well-definedness conclusions of `p.two.grid.transport`.**
Under the containment of the two grid towers in the window, the annealed blocks
of both grids are finite and positive definite at every scale of the range, the
centered moments are finite, and the means are ordered. -/
theorem definedness_of_isWindowMultiplier (hd : 2 ≤ d) {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hP : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) {Ψ : ℝ → ℝ} {K Cd : ℝ} {Q : ℝ}
    (hQ : 1 ≤ Q) {jStar M : ℤ} (hw : IsCoupledWindow d Q K jStar M)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mu mu' : Mat d} (hmu : mu.PosDef) (hmu' : mu'.PosDef) {b : ℤ}
    (hcont : ∀ r : Mat d, r = roundedGrid jStar mu ∨ r = roundedGrid jStar mu' →
      ∀ j : ℤ, jStar ≤ j → j ≤ b → adaptedCell r j ⊆ centeredCube d M) :
    (∀ r : Mat d, r = roundedGrid jStar mu ∨ r = roundedGrid jStar mu' →
        ∀ j : ℤ, jStar ≤ j → j ≤ b →
          HasFiniteAdaptedMean P r j ∧ Book.Ch02.BlockPosDef (adaptedMean P r j) ∧
            centeredMoment P Q r j ≠ ⊤) ∧
      (∀ r : Mat d, r = roundedGrid jStar mu ∨ r = roundedGrid jStar mu' →
        ∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ b →
          BlockMatLoewnerLE (adaptedMean P r T) (adaptedMean P r j)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hall : ∀ nu : Mat d, nu.PosDef →
      (∀ j : ℤ, jStar ≤ j → j ≤ b →
        adaptedCell (roundedGrid jStar nu) j ⊆ centeredCube d M) →
      (∀ j : ℤ, jStar ≤ j → j ≤ b →
          HasFiniteAdaptedMean P (roundedGrid jStar nu) j ∧
            Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid jStar nu) j) ∧
            centeredMoment P Q (roundedGrid jStar nu) j ≠ ⊤) ∧
        (∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ b →
          BlockMatLoewnerLE (adaptedMean P (roundedGrid jStar nu) T)
            (adaptedMean P (roundedGrid jStar nu) j)) := by
    intro nu hnu hc
    have hq := isRoundedGrid_roundedGrid_of_isCoupledWindow hw hnu
    refine ⟨fun j hj hjb => ⟨?_, ?_, ?_⟩, fun j T hj hjT hTb => ?_⟩
    · exact hasFiniteAdaptedMean_of_isWindowMultiplier hY hnu hq hj (hc j hj hjb)
    · exact blockPosDef_adaptedMean_of_isWindowMultiplier hY hnu hq hj (hc j hj hjb)
    · exact centeredMoment_ne_top_of_isWindowMultiplier hE hY hnu hq hQ hj (hc j hj hjb)
    · exact adaptedMean_le_of_isWindowMultiplier hP hY hnu hq hj hjT
        (hc j hj (hjT.trans hTb)) (hc T (hj.trans hjT) hTb)
  refine ⟨fun r hr j hj hjb => ?_, fun r hr j T hj hjT hTb => ?_⟩
  · rcases hr with hr | hr
    · exact hr ▸ (hall mu hmu (fun j hj hjb => hcont _ (Or.inl rfl) j hj hjb)).1 j hj hjb
    · exact hr ▸ (hall mu' hmu' (fun j hj hjb => hcont _ (Or.inr rfl) j hj hjb)).1 j hj hjb
  · rcases hr with hr | hr
    · exact hr ▸ (hall mu hmu (fun j hj hjb => hcont _ (Or.inl rfl) j hj hjb)).2 j T hj hjT hTb
    · exact hr ▸ (hall mu' hmu' (fun j hj hjb => hcont _ (Or.inr rfl) j hj hjb)).2 j T hj hjT hTb

end

end Transport
end HighContrast
end Homogenization
