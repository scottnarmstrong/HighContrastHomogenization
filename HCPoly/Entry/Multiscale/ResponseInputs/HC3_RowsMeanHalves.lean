import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsObligations

/-!
# The cutoff-mean row from its cell and oscillation halves

The cutoff-mean row of `p.response.transfer` bounds the crossed pairing of the cutoff-mean defect
against the dual variable by `C (tau L_s)^{1/2} + C 3^{-H} (E[J_t] L_s)^{1/2}`.  The defect splits
into a cell part and an oscillation part: the cell part costs `(2 tau L_s)^{1/2}`, while the
oscillation part is already of the printed size `c₂ 3^{-H} (E[J_t] L_s)^{1/2}`.  This module is the
purely scalar assembly of the row from those two halves, for both signs, with the coefficient
`max 1 c₂`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cutoff-mean row for the negative sign from its two halves.**  The coordinatewise mean
defect splits as `N = Ncell + Nosc`.  Bilinearity of `vecDot` splits the crossed pairing along the
two coordinates into the cell and oscillation halves; the triangle inequality bounds the total by
the sum of the two half-bounds; `√L √(2τ) = √2 √(τ L)` with `√2 / 2 ≤ 1` absorbs the cell factor;
and `1 ≤ max 1 c₂` together with `(1 / 2) c₂ ≤ max 1 c₂` absorbs the row's factor `1 / 2`. -/
theorem cutoffMeanRowMinus_of_halves {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d)
    (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (c₂ : ℝ) (hc₂ : 0 ≤ c₂) (Ncell Nosc : BlockVec d)
    (hsplit1 : ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1)
      = Ncell.1 + Nosc.1)
    (hsplit2 : ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2)
      = Ncell.2 + Nosc.2)
    (hcell : |vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e))
    (hosc : |vecDot Nosc.1 (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1 Nosc.2|
      ≤ c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)))
    (hτ : 0 ≤ respTauMinus P jStar F s t e) (hL : 0 ≤ respLsMinus P jStar F s t e) :
    CutoffMeanRowMinus (max 1 c₂) P jStar F H s t e φ uM := by
  unfold CutoffMeanRowMinus
  have hsplit_l : vecDot
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1)
        (respYMinus P jStar F t e).2
      = vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot Nosc.1 (respYMinus P jStar F t e).2 := by
    rw [hsplit1, vecDot_add_left]
  have hsplit_r : vecDot (respYMinus P jStar F t e).1
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2)
      = vecDot (respYMinus P jStar F t e).1 Ncell.2
        + vecDot (respYMinus P jStar F t e).1 Nosc.2 := by
    rw [hsplit2, vecDot_add_right]
  rw [hsplit_l, hsplit_r]
  have htri : |(vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot Nosc.1 (respYMinus P jStar F t e).2)
        + (vecDot (respYMinus P jStar F t e).1 Ncell.2
          + vecDot (respYMinus P jStar F t e).1 Nosc.2)|
      ≤ |vecDot Ncell.1 (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1 Ncell.2|
        + |vecDot Nosc.1 (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1 Nosc.2| := by
    have hre : (vecDot Ncell.1 (respYMinus P jStar F t e).2
          + vecDot Nosc.1 (respYMinus P jStar F t e).2)
          + (vecDot (respYMinus P jStar F t e).1 Ncell.2
            + vecDot (respYMinus P jStar F t e).1 Nosc.2)
        = (vecDot Ncell.1 (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1 Ncell.2)
          + (vecDot Nosc.1 (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1 Nosc.2) := by ring
    rw [hre]
    exact abs_add_le _ _
  have hpair : |(vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot Nosc.1 (respYMinus P jStar F t e).2)
        + (vecDot (respYMinus P jStar F t e).1 Ncell.2
          + vecDot (respYMinus P jStar F t e).1 Nosc.2)|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) :=
    le_trans htri (add_le_add hcell hosc)
  have hhalfpair : (1 / 2 : ℝ) * |(vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot Nosc.1 (respYMinus P jStar F t e).2)
        + (vecDot (respYMinus P jStar F t e).1 Ncell.2
          + vecDot (respYMinus P jStar F t e).1 Nosc.2)|
      ≤ (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))) :=
    mul_le_mul_of_nonneg_left hpair (by norm_num)
  have hcell' : (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e))
      ≤ max 1 c₂ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) := by
    have hsq : Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e)
        = Real.sqrt 2 * Real.sqrt (respTauMinus P jStar F s t e
            * respLsMinus P jStar F s t e) := by
      rw [← Real.sqrt_mul hL (2 * respTauMinus P jStar F s t e),
        show respLsMinus P jStar F s t e * (2 * respTauMinus P jStar F s t e)
            = 2 * (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) by ring,
        Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)
          (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)]
    have htwo : Real.sqrt 2 / 2 ≤ 1 := by linarith [Real.sqrt_two_lt_three_halves]
    have hs : 0 ≤ Real.sqrt (respTauMinus P jStar F s t e
        * respLsMinus P jStar F s t e) := by
      rw [Real.sqrt_mul hτ (respLsMinus P jStar F s t e)]
      positivity
    calc (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e))
        = (Real.sqrt 2 / 2) * Real.sqrt (respTauMinus P jStar F s t e
            * respLsMinus P jStar F s t e) := by rw [hsq]; ring
      _ ≤ 1 * Real.sqrt (respTauMinus P jStar F s t e
            * respLsMinus P jStar F s t e) :=
          mul_le_mul_of_nonneg_right htwo hs
      _ ≤ max 1 c₂ * Real.sqrt (respTauMinus P jStar F s t e
            * respLsMinus P jStar F s t e) :=
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) c₂) hs
  have hosp' : (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)))
      ≤ max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) := by
    have hnonneg : 0 ≤ (3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e) :=
      mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (-(H : ℝ)))
        (Real.sqrt_nonneg _)
    have hc₂' : (1 / 2 : ℝ) * c₂ ≤ max 1 c₂ := by
      have : (1 / 2 : ℝ) * c₂ ≤ c₂ := by linarith only [hc₂]
      exact le_trans this (le_max_right (1 : ℝ) c₂)
    calc (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ))
          * Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)))
        = ((1 / 2 : ℝ) * c₂) * ((3 : ℝ) ^ (-(H : ℝ))
            * Real.sqrt (respEJMinus P jStar F t e
              * respLsMinus P jStar F s t e)) := by ring
      _ ≤ max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ))
            * Real.sqrt (respEJMinus P jStar F t e
              * respLsMinus P jStar F s t e)) :=
          mul_le_mul_of_nonneg_right hc₂' hnonneg
  have hsplitmul : (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)))
      = (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e))
        + (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))) := by ring
  calc (1 / 2 : ℝ) * |(vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot Nosc.1 (respYMinus P jStar F t e).2)
        + (vecDot (respYMinus P jStar F t e).1 Ncell.2
          + vecDot (respYMinus P jStar F t e).1 Nosc.2)|
      ≤ (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))) := hhalfpair
    _ = (1 / 2 : ℝ) * (Real.sqrt (respLsMinus P jStar F s t e)
          * Real.sqrt (2 * respTauMinus P jStar F s t e))
        + (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))) := hsplitmul
    _ ≤ max 1 c₂ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
        + max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) :=
          add_le_add hcell' hosp'

/-- **The cutoff-mean row for the positive sign from its two halves.**  The adjoint coordinatewise
mean defect splits as `N = Ncell + Nosc`.  Bilinearity of `vecDot` splits the crossed pairing along
the two coordinates into the cell and oscillation halves; the triangle inequality bounds the total
by the sum of the two half-bounds; `√L √(2τ) = √2 √(τ L)` with `√2 / 2 ≤ 1` absorbs the cell
factor; and `1 ≤ max 1 c₂` together with `(1 / 2) c₂ ≤ max 1 c₂` absorbs the row's factor `1 / 2`. -/
theorem cutoffMeanRowPlus_of_halves {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d)
    (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (c₂ : ℝ) (hc₂ : 0 ≤ c₂) (Ncell Nosc : BlockVec d)
    (hsplit1 : ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1)
      = Ncell.1 + Nosc.1)
    (hsplit2 : ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
        (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2)
      = Ncell.2 + Nosc.2)
    (hcell : |vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e))
    (hosc : |vecDot Nosc.1 (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1 Nosc.2|
      ≤ c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)))
    (hτ : 0 ≤ respTauPlus P jStar F s t e) (hL : 0 ≤ respLsPlus P jStar F s t e) :
    CutoffMeanRowPlus (max 1 c₂) P jStar F H s t e φ uP := by
  unfold CutoffMeanRowPlus
  have hsplit_l : vecDot
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1)
        (respYPlus P jStar F t e).2
      = vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot Nosc.1 (respYPlus P jStar F t e).2 := by
    rw [hsplit1, vecDot_add_left]
  have hsplit_r : vecDot (respYPlus P jStar F t e).1
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2)
      = vecDot (respYPlus P jStar F t e).1 Ncell.2
        + vecDot (respYPlus P jStar F t e).1 Nosc.2 := by
    rw [hsplit2, vecDot_add_right]
  rw [hsplit_l, hsplit_r]
  have htri : |(vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot Nosc.1 (respYPlus P jStar F t e).2)
        + (vecDot (respYPlus P jStar F t e).1 Ncell.2
          + vecDot (respYPlus P jStar F t e).1 Nosc.2)|
      ≤ |vecDot Ncell.1 (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1 Ncell.2|
        + |vecDot Nosc.1 (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1 Nosc.2| := by
    have hre : (vecDot Ncell.1 (respYPlus P jStar F t e).2
          + vecDot Nosc.1 (respYPlus P jStar F t e).2)
          + (vecDot (respYPlus P jStar F t e).1 Ncell.2
            + vecDot (respYPlus P jStar F t e).1 Nosc.2)
        = (vecDot Ncell.1 (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1 Ncell.2)
          + (vecDot Nosc.1 (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1 Nosc.2) := by ring
    rw [hre]
    exact abs_add_le _ _
  have hpair : |(vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot Nosc.1 (respYPlus P jStar F t e).2)
        + (vecDot (respYPlus P jStar F t e).1 Ncell.2
          + vecDot (respYPlus P jStar F t e).1 Nosc.2)|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) :=
    le_trans htri (add_le_add hcell hosc)
  have hhalfpair : (1 / 2 : ℝ) * |(vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot Nosc.1 (respYPlus P jStar F t e).2)
        + (vecDot (respYPlus P jStar F t e).1 Ncell.2
          + vecDot (respYPlus P jStar F t e).1 Nosc.2)|
      ≤ (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))) :=
    mul_le_mul_of_nonneg_left hpair (by norm_num)
  have hcell' : (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e))
      ≤ max 1 c₂ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) := by
    have hsq : Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e)
        = Real.sqrt 2 * Real.sqrt (respTauPlus P jStar F s t e
            * respLsPlus P jStar F s t e) := by
      rw [← Real.sqrt_mul hL (2 * respTauPlus P jStar F s t e),
        show respLsPlus P jStar F s t e * (2 * respTauPlus P jStar F s t e)
            = 2 * (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) by ring,
        Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)
          (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)]
    have htwo : Real.sqrt 2 / 2 ≤ 1 := by linarith [Real.sqrt_two_lt_three_halves]
    have hs : 0 ≤ Real.sqrt (respTauPlus P jStar F s t e
        * respLsPlus P jStar F s t e) := by
      rw [Real.sqrt_mul hτ (respLsPlus P jStar F s t e)]
      positivity
    calc (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e))
        = (Real.sqrt 2 / 2) * Real.sqrt (respTauPlus P jStar F s t e
            * respLsPlus P jStar F s t e) := by rw [hsq]; ring
      _ ≤ 1 * Real.sqrt (respTauPlus P jStar F s t e
            * respLsPlus P jStar F s t e) :=
          mul_le_mul_of_nonneg_right htwo hs
      _ ≤ max 1 c₂ * Real.sqrt (respTauPlus P jStar F s t e
            * respLsPlus P jStar F s t e) :=
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) c₂) hs
  have hosp' : (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)))
      ≤ max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) := by
    have hnonneg : 0 ≤ (3 : ℝ) ^ (-(H : ℝ))
        * Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e) :=
      mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (-(H : ℝ)))
        (Real.sqrt_nonneg _)
    have hc₂' : (1 / 2 : ℝ) * c₂ ≤ max 1 c₂ := by
      have : (1 / 2 : ℝ) * c₂ ≤ c₂ := by linarith only [hc₂]
      exact le_trans this (le_max_right (1 : ℝ) c₂)
    calc (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ))
          * Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)))
        = ((1 / 2 : ℝ) * c₂) * ((3 : ℝ) ^ (-(H : ℝ))
            * Real.sqrt (respEJPlus P jStar F t e
              * respLsPlus P jStar F s t e)) := by ring
      _ ≤ max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ))
            * Real.sqrt (respEJPlus P jStar F t e
              * respLsPlus P jStar F s t e)) :=
          mul_le_mul_of_nonneg_right hc₂' hnonneg
  have hsplitmul : (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)))
      = (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e))
        + (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))) := by ring
  calc (1 / 2 : ℝ) * |(vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot Nosc.1 (respYPlus P jStar F t e).2)
        + (vecDot (respYPlus P jStar F t e).1 Ncell.2
          + vecDot (respYPlus P jStar F t e).1 Nosc.2)|
      ≤ (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e)
        + c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))) := hhalfpair
    _ = (1 / 2 : ℝ) * (Real.sqrt (respLsPlus P jStar F s t e)
          * Real.sqrt (2 * respTauPlus P jStar F s t e))
        + (1 / 2 : ℝ) * (c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))) := hsplitmul
    _ ≤ max 1 c₂ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
        + max 1 c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) :=
          add_le_add hcell' hosp'

end

end Homogenization.HighContrast.Multiscale
