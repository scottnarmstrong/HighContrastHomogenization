/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TerminalProfile
import HCPoly.Provider.ShortHop.DriftAccount

/-!
# Terminal calibration and drift

The candidate comparison retained by the terminal phase is widened to the
requested calibration tolerance.  The strict terminal determinant test then
controls the determinant quotient in the fixed-grid drift propagation row.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

private theorem blockScale_mono_of_posDef {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    {a b : ℝ} (hab : a ≤ b) :
    BlockMatLoewnerLE (blockScale a E) (blockScale b E) := by
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale, toFullBlockMat_blockScale]
  refine Matrix.le_iff.mpr ?_
  have hps := (posDef_toFullBlockMat hE hEpd).posSemidef.smul
    (sub_nonneg.mpr hab)
  simpa [sub_smul] using hps

/-- The retained T5 comparison widens from the internal bridge tolerance to
the requested calibration tolerance. -/
theorem terminal_calibration_bounds {P : Measure (CoeffSpace d)}
    {jStar : ℤ} {S : State d} {E0 : BlockMat d}
    (hE0 : IsSymmetricBlockMat E0) (hE0pd : Book.Ch02.BlockPosDef E0)
    (hcandidate : S.candidate = some E0)
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hterminal : TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew
      c.etaX jStar S) :
    BlockMatLoewnerLE (blockScale (1 - epsCal) E0)
        (adaptedMean P S.q S.base) ∧
      BlockMatLoewnerLE (adaptedMean P S.q S.base)
        (blockScale (1 + epsCal) E0) := by
  rcases hexact with ⟨-, hmean, -, -, -, -⟩
  rcases hterminal with ⟨-, -, -, -, -, E1, hcand1, -, hlo, hhi⟩
  have hE : E1 = E0 := Option.some.inj (hcand1.symm.trans hcandidate)
  subst E1
  rw [← hmean]
  constructor
  · exact (blockScale_mono_of_posDef hE0 hE0pd (by
      linarith only [c.etaX_le_epsCal])).trans hlo
  · exact hhi.trans (blockScale_mono_of_posDef hE0 hE0pd (by
      linarith only [c.etaX_le_epsCal]))

/-- The strict terminal determinant test and the fixed-grid propagation row
give both determinant and drift conclusions of the returned tuple. -/
theorem terminal_determinant_drift_bounds (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {P : Measure (CoeffSpace d)}
    {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hterminal : TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew
      c.etaX jStar S)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ S.base + (H : ℤ) →
      Book.Ch02.BlockPosDef (adaptedMean P S.q j))
    (hmono : ∀ j T : ℤ, jStar ≤ j → j ≤ T →
      T ≤ S.base + (H : ℤ) →
        BlockMatLoewnerLE (adaptedMean P S.q T) (adaptedMean P S.q j))
    (hpass : adaptedDetRoot P S.q S.base <
      (1 + c.deltaTerm) * adaptedDetRoot P S.q (S.base + (H : ℤ))) :
    adaptedDetRoot P S.q S.base <
        (1 + c.deltaTerm) * adaptedDetRoot P S.q (S.base + (H : ℤ)) ∧
      linearDrift P (initExpRhoDr g) S.q jStar S.base +
          linearDrift P (initExpRhoDr g) S.q jStar (S.base + (H : ℤ)) ≤
        etaDr := by
  have hjbase : jStar ≤ S.base := by
    rcases hexact with ⟨-, -, -, -, hjcheck, -⟩
    rcases hterminal with ⟨-, hbase, -, -, -, -⟩
    simpa only [hbase] using hjcheck
  have hbaseTerm : S.base ≤ S.base + (H : ℤ) := by omega
  have hfullPos : ∀ j : ℤ, jStar ≤ j → j ≤ S.base + (H : ℤ) →
      (toFullBlockMat (adaptedMean P S.q j)).PosDef := by
    intro j hj hjt
    exact posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q j)
      (hpos j hj hjt)
  have hfullMono : ∀ j T : ℤ, jStar ≤ j → j ≤ T →
      T ≤ S.base + (H : ℤ) →
        toFullBlockMat (adaptedMean P S.q T) ≤
          toFullBlockMat (adaptedMean P S.q j) := by
    intro j T hj hjT hT
    exact le_of_blockMatLoewnerLE
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q T)
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q j) (hmono j T hj hjT hT)
  have hprop := ShortHop.linearDrift_propagation (initExpRhoDr_pos hg).le hjbase
    hbaseTerm hfullPos hfullMono
  set R : ℝ := (toFullBlockMat (adaptedMean P S.q S.base)).det /
    (toFullBlockMat (adaptedMean P S.q (S.base + (H : ℤ)))).det
  set G : ℝ := (3 : ℝ) ^
    (-initExpRhoDr g * (((S.base + (H : ℤ) : ℤ) : ℝ) - (S.base : ℝ)))
  set D0 : ℝ := linearDrift P (initExpRhoDr g) S.q jStar S.base
  set D1 : ℝ := linearDrift P (initExpRhoDr g) S.q jStar (S.base + (H : ℤ))
  have hR : R ≤ (1 + c.deltaTerm) ^ d := by
    dsimp [R]
    exact ShortHop.det_div_le_of_short_test (by omega)
      (hfullPos S.base hjbase hbaseTerm)
      (hfullPos (S.base + (H : ℤ)) (hjbase.trans hbaseTerm) le_rfl) hpass.le
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact (div_pos (hfullPos S.base hjbase hbaseTerm).det_pos
      (hfullPos (S.base + (H : ℤ)) (hjbase.trans hbaseTerm) le_rfl).det_pos).le
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have hD0 : 0 ≤ D0 := by
    dsimp [D0]
    exact ShortHop.linearDrift_nonneg (hfullPos S.base hjbase hbaseTerm) (by
      intro r hr1 hrs
      exact hfullMono (r - 1) r (by omega) (by omega) (hrs.trans hbaseTerm))
  have hD0le : D0 ≤ c.etaNew := by
    rcases hterminal with ⟨-, hbase, hcheck, -, hdrift, -⟩
    simpa only [D0, hbase, hcheck] using hdrift
  have hR_nonneg : 0 ≤ (1 + c.deltaTerm) ^ d :=
    pow_nonneg (by linarith only [c.deltaTerm_pos]) d
  have hmain : D1 ≤ R * G * D0 + 2 * (d : ℝ) * (R - 1) := by
    simpa only [D1, D0, R, G] using hprop
  have hfirst : R * G * D0 ≤
      (1 + c.deltaTerm) ^ d * G * c.etaNew := by
    exact mul_le_mul (mul_le_mul_of_nonneg_right hR hG0) hD0le
      hD0 (mul_nonneg hR_nonneg hG0)
  have hsecond : 2 * (d : ℝ) * (R - 1) ≤
      2 * (d : ℝ) * ((1 + c.deltaTerm) ^ d - 1) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hR 1)
      (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
  have hG : G = (3 : ℝ) ^ (-initExpRhoDr g * (H : ℝ)) := by
    dsimp [G]
    congr 2
    push_cast
    ring
  constructor
  · exact hpass
  · calc
      D0 + D1 ≤ D0 +
          (R * G * D0 + 2 * (d : ℝ) * (R - 1)) := add_le_add le_rfl hmain
      _ ≤ c.etaNew + ((1 + c.deltaTerm) ^ d * G * c.etaNew +
            2 * (d : ℝ) * ((1 + c.deltaTerm) ^ d - 1)) :=
        add_le_add hD0le (add_le_add hfirst hsecond)
      _ = (1 + (1 + c.deltaTerm) ^ d *
          (3 : ℝ) ^ (-initExpRhoDr g * (H : ℝ))) * c.etaNew +
            2 * (d : ℝ) * ((1 + c.deltaTerm) ^ d - 1) := by rw [hG]; ring
      _ ≤ etaDr := c.terminal_drift

end

end Homogenization.HighContrast.Selection
