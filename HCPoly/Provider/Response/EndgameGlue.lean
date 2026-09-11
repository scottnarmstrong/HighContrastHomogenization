/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.DeterminantLoss
import HCPoly.Setup.TransportObjects
import HCPoly.Provider.Response.SourceBuffer

/-!
# Local glue for the fixed-window response argument

Four readings that the response argument uses without comment, each of them an
identification between two printed forms of the same quantity, collected here so
that the argument can cite them in one step.

The determinant ratio of the load calibration is written in two ways inside the
proof of `p.response.transfer`: as `ϱ = (det E_s/det E_t)^{1/d}` in the
calibration of the response loads, and as `ϱ = Ξ_s/Ξ_t` in the block orders and
determinant ratio at the two response endpoints.  The two agree
because the `d`-th root is multiplicative on positive determinants, which is the
first pair of results below; the second of them is stated at the annealed
adapted blocks of a terminal window, where the argument reads it.

The calibration constant `c_ε = ((1+ε_cal)/(1-ε_cal))^{1/2}` of the same
calibration is bounded by the universal `c_{ε,*} = √2` among the calibration
constants of the response estimate, because the calibration tolerance of
`e.response.transfer.tolerances` is at most `1/3`.  This is the first of the
canonical comparisons at the response endpoints.

The smallness of the all-earlier source row is read at the uniform multiplier
cap `𝒰 = 2` of the window, since that is the normalization at which the source
data carried into the response estimate supplies the two rows; the mean of the
multiplier is at most the cap and enters only through it.

Finally, the terminal geometry of `e.global.selection.scales` presents the
adapted grid as the rounding `q = Q_{j_*}(m_0)` of the printed metric.  The
rounded-grid predicate, which follows the rounded adapted grid of
`s.scale.selection`, asserts only that some positive metric generates the grid,
so a consumer that needs the predicate derives it from the printed metric rather
than reading a witness back out of it:
the witness returned by the predicate has no reason to be the metric the source
constants and the auxiliary block are written with.  The alignment floor the
predicate also asserts is the one the coupling between the lower generation and
the containing window of the source multiplier (`e.source.multiplier`) already
supplies.
-/

namespace Homogenization
namespace HighContrast
namespace Response

open MeasureTheory

open scoped Matrix

noncomputable section

/-! ## The determinant ratio of the load calibration -/

/-- **The determinant-loss ratio is the quotient of the determinant roots.**
The determinant ratio `ϱ = (det E/det F)^{1/d}` of two ordered blocks and the
determinant roots `Ξ = det(·)^{1/d}` of
`e.scale.selection.logdet.loss` are the same `d`-th root, so on a
pair of positive definite doubled blocks the ratio splits. -/
theorem canonDetRatio_toFullBlockMat_eq_detRoot_div {d : ℕ} {A B : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) (hB : (toFullBlockMat B).PosDef) :
    canonDetRatio (toFullBlockMat A) (toFullBlockMat B) =
      detRoot d A / detRoot d B := by
  rw [canonDetRatio, detRoot, detRoot, Real.div_rpow hA.det_pos.le hB.det_pos.le]

/-- **The two printed readings of the terminal determinant ratio agree.**  At
the annealed adapted blocks of a terminal window the ratio of the response-load
calibration is the quotient `Ξ_s^q/Ξ_t^q` of the two determinant roots compared
in the block data at the response endpoints. -/
theorem canonDetRatio_eq_adaptedDetRoot_div {d : ℕ} {P : Measure (CoeffSpace d)}
    {q : Mat d} {s t : ℤ} {Es Et : BlockMat d} (hEs : Es = adaptedMean P q s)
    (hEt : Et = adaptedMean P q t) (hsPos : (toFullBlockMat Es).PosDef)
    (htPos : (toFullBlockMat Et).PosDef) :
    canonDetRatio (toFullBlockMat Es) (toFullBlockMat Et) =
      adaptedDetRoot P q s / adaptedDetRoot P q t := by
  rw [canonDetRatio_toFullBlockMat_eq_detRoot_div hsPos htPos, adaptedDetRoot,
    adaptedDetRoot, hEs, hEt]

/-! ## The calibration constant at the printed tolerance -/

/-- **The calibration constant is below its universal bound.**  For a
calibration tolerance in the range of `e.response.transfer.tolerances` the
constant `c_ε = ((1+ε_cal)/(1-ε_cal))^{1/2}` of the response-load calibration
is at most the universal `c_{ε,*} = √2` among the calibration constants of the
response estimate; this is the first of the canonical comparisons at the
response endpoints. -/
theorem sqrt_calibration_le_sqrt_two {epsCal : ℝ} (hhi : epsCal ≤ 1 / 3) :
    Real.sqrt ((1 + epsCal) / (1 - epsCal)) ≤ Real.sqrt 2 := by
  have hden : (0 : ℝ) < 1 - epsCal := by linarith only [hhi]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_iff₀ hden]
  linarith only [hhi]

/-! ## The all-earlier row at the uniform multiplier cap -/

/-- **The all-earlier source row at the cap**, that is, the smallness of the
all-earlier source row read at the uniform multiplier cap `𝒰 = 2` of the window
rather than at the mean of the multiplier.  The cap is the normalization at which
the source data carried into the response estimate supplies the row, and the mean
is at most the cap, so this is the form the argument absorbs. -/
theorem source_row_bound_cap {d : ℕ} (hd : 2 ≤ d) {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {Csrc : ℝ} {E : BlockMat d} {m0 : Mat d}
    {Arad Bresp : ℝ} {jStar s : ℤ} (hPi : 1 ≤ aspectRatio E)
    (hBresp : 0 < Bresp)
    (hslack : 1 + 2 * Arad < initExpRhoMax d g * Bresp)
    (hrow : 24 * (Csrc * zetaG g) ^ 2 / ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (1 + 2 * Arad - 3 / 2 * Bresp) ≤ 1)
    (hkap : kappaRef E ≤ 6 * aspectRatio E)
    (hecc : witnessEccentricity m0 ≤ (2 + aspectRatio E) ^ Arad)
    (hbuf : jStar + ⌈Bresp * Real.logb 3 (2 + aspectRatio E)⌉ ≤ s) :
    kappaRef E * boundaryConst Csrc g m0 ^ 2 * 2 ^ 2 /
          ((3 : ℝ) ^ (3 / 2 - g) - 1) *
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) ≤ 1 :=
  source_row_bound (EY := 2) hd hg hPi hBresp hslack hrow hkap hecc
    (by norm_num) le_rfl hbuf

/-! ## The rounded grid of the printed metric -/

/-- **The printed metric is a rounded-grid witness.**  A grid presented as the
rounding of a positive metric at an alignment above the dimensional floor is a
rounded adapted grid in the sense of `s.scale.selection`, with that metric as
the witness.  A consumer that needs the predicate alongside the printed metric
derives it this way; reading a witness out of the predicate would not return the
printed metric. -/
theorem isRoundedGrid_of_eq_roundedGrid {d : ℕ} {jAl : ℤ} {q m0 : Mat d}
    (hfloor : (kZero d : ℤ) ≤ jAl) (hm0 : m0.PosDef)
    (hqeq : q = roundedGrid jAl m0) : IsRoundedGrid jAl q :=
  ⟨hfloor, m0, hm0, hqeq⟩

/-- **The same witness on a coupled window.**  The alignment of a coupled window
lies above the source floor of the window coupling, hence above the dimensional
floor, so the alignment condition of the rounded adapted grid is automatic and
the printed metric alone supplies the witness. -/
theorem isRoundedGrid_of_eq_roundedGrid_of_isCoupledWindow {d : ℕ} {Q K : ℝ}
    {jStar M : ℤ} (hw : IsCoupledWindow d Q K jStar M) {q m0 : Mat d}
    (hm0 : m0.PosDef) (hqeq : q = roundedGrid jStar m0) :
    IsRoundedGrid jStar q :=
  isRoundedGrid_of_eq_roundedGrid (le_trans (le_max_left _ _) hw.1) hm0 hqeq

/-! ## The response constant of the window -/

/-- **The merged response constant.**  The constant the response window of
`e.response.transfer.tolerances` is produced at is the maximum of the
dimensional constants the response lemmas supply: it is admissible, and it
dominates each of them.  It is not the universal source and window multiplier of
the printed statement, which is bound later and enters only the source
allocations. -/
theorem one_le_response_constant {Cprof Cpre Cresp : ℝ} (hCprof : 1 ≤ Cprof)
    (hCresp : Cresp = max Cprof Cpre) :
    1 ≤ Cresp ∧ Cprof ≤ Cresp ∧ Cpre ≤ Cresp := by
  subst hCresp
  exact ⟨le_max_of_le_left hCprof, le_max_left _ _, le_max_right _ _⟩

end

end Response
end HighContrast
end Homogenization
