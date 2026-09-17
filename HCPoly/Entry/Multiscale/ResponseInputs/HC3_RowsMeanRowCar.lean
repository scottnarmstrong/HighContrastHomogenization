import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCellSplit
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsMeanHalves

/-!
# The cutoff-mean row on the carriers from its cell and oscillation halves

The cutoff-mean row of `e.response.cutoff.estimate` is the sum of a cell part and an oscillation
part.  `HC3_RowsCellSplit` exhibits those two parts explicitly, and `HC3_RowsMeanHalves` assembles
the row from a cell-half bound `(L_s^∓ 2 tau^∓)^{1/2}` and an oscillation-half bound
`c₂ 3^{-H} (E[J_t^∓] L_s^∓)^{1/2}`.  This file instantiates the assembly at the two functions that
`HC3_RowsCellSplit` produces, so that a caller holding the standing data of the cutoff-mean defect,
the cell-half bound and the oscillation-half bound obtains the named obligation
`CutoffMeanRow∓` with constant `max 1 c₂`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cutoff-mean row for the negative sign on the carriers.**  Assume the standing data of
the cutoff-mean defect: `Y^-` is the annealed cell average of the terminal optimizer state for
`respCoeffMinus F`, the grid is invertible, the sample functions are integrable on the terminal cell
and on each depth-`H` subcell, and the two parts of the split are `P`-integrable.  Assume the
cell-half bound for the explicit cell part, the oscillation-half bound `c₂ 3^{-H} (E[J^-] L^-)^{1/2}`
for the explicit oscillation part, and the nonnegativity of `tau^-` and `L^-`.  Then the named
obligation `CutoffMeanRowMinus` holds with constant `max 1 c₂`.  The cell-half and
oscillation-half bounds remain undischarged inputs. -/
theorem cutoffMeanRowMinus_of_cellSplit {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hY : respYMinus P jStar F t e
      = ((fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).1 i ∂P),
         (fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).2 i ∂P)))
    (hgrid : IsUnit (respGrid jStar F))
    (hφG1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
      (respCell jStar F t))
    (hG1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) (respCell jStar F t))
    (hint1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (φ x - 1) * (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
      (respCell jStar F t))
    (h1_1 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ) *
        (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (h2_1 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1) *
        (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (hφG2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
      (respCell jStar F t))
    (hG2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) (respCell jStar F t))
    (hint2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (φ x - 1) * (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
      (respCell jStar F t))
    (h1_2 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ) *
        (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (h2_2 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1) *
        (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (hIntM1 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffMinus F a) (uM a)).1 i) P)
    (hIntC1 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffMinus F a) (uM a))).1 i) P)
    (hIntOsc1 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
          (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) P)
    (hIntCell1 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) P)
    (hIntM2 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffMinus F a) (uM a)).2 i) P)
    (hIntC2 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffMinus F a) (uM a))).2 i) P)
    (hIntOsc2 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
          (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P)
    (hIntCell2 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P)
    (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hcell : let Ncell : BlockVec d :=
        ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P),
         (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P));
      |vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e))
    (hosc : let Nosc : BlockVec d :=
        ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P),
         (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P));
      |vecDot Nosc.1 (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1 Nosc.2|
      ≤ c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)))
    (hτ : 0 ≤ respTauMinus P jStar F s t e) (hL : 0 ≤ respLsMinus P jStar F s t e) :
    CutoffMeanRowMinus (max 1 c₂) P jStar F H s t e φ uM := by
  have hsplit := integral_cutoffStateMeanAux_sub_respYMinus_eq_cell_add_osc P jStar F H s t ht e
    φ uM hY hgrid hφG1 hG1 hint1 h1_1 h2_1 hφG2 hG2 hint2 h1_2 h2_2
    hIntM1 hIntC1 hIntOsc1 hIntCell1 hIntM2 hIntC2 hIntOsc2 hIntCell2
  let Ncell : BlockVec d :=
    ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P),
     (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P))
  let Nosc : BlockVec d :=
    ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P),
     (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P))
  exact cutoffMeanRowMinus_of_halves P jStar F H s t e φ uM c₂ hc₂ Ncell Nosc
    hsplit.1 hsplit.2 hcell hosc hτ hL

/-- **The cutoff-mean row for the positive sign on the carriers.**  The adjoint twin of
`cutoffMeanRowMinus_of_cellSplit`: with `Y^+` the annealed cell average of the terminal optimizer
state for `respCoeffPlus F`, the same standing data and the cell-half and oscillation-half bounds
for the explicit parts of `HC3_RowsCellSplit` give `CutoffMeanRowPlus` with constant `max 1 c₂`. -/
theorem cutoffMeanRowPlus_of_cellSplit {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hY : respYPlus P jStar F t e
      = ((fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).1 i ∂P),
         (fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).2 i ∂P)))
    (hgrid : IsUnit (respGrid jStar F))
    (hφG1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
      (respCell jStar F t))
    (hG1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) (respCell jStar F t))
    (hint1 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (φ x - 1) * (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
      (respCell jStar F t))
    (h1_1 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ) *
        (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (h2_1 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1) *
        (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (hφG2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
      (respCell jStar F t))
    (hG2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) (respCell jStar F t))
    (hint2 : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => (φ x - 1) * (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
      (respCell jStar F t))
    (h1_2 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ) *
        (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (h2_2 : ∀ (a : CoeffSpace d) (i : Fin d), ∀ w ∈ triadicIndexBox d H, IntegrableOn
      (fun x => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1) *
        (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
      (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w))
    (hIntM1 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffPlus F a) (uP a)).1 i) P)
    (hIntC1 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffPlus F a) (uP a))).1 i) P)
    (hIntOsc1 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
          (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) P)
    (hIntCell1 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) P)
    (hIntM2 : ∀ i : Fin d, Integrable (fun a => (cutoffStateMeanAux (respCell jStar F t) φ
      (respCoeffPlus F a) (uP a)).2 i) P)
    (hIntC2 : ∀ i : Fin d, Integrable (fun a => (cellAverage (respCell jStar F t)
      (optimizerField (respCoeffPlus F a) (uP a))).2 i) P)
    (hIntOsc2 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
          (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P)
    (hIntCell2 : ∀ i : Fin d, Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P)
    (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hcell : let Ncell : BlockVec d :=
        ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P),
         (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P));
      |vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e))
    (hosc : let Nosc : BlockVec d :=
        ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P),
         (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P));
      |vecDot Nosc.1 (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1 Nosc.2|
      ≤ c₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)))
    (hτ : 0 ≤ respTauPlus P jStar F s t e) (hL : 0 ≤ respLsPlus P jStar F s t e) :
    CutoffMeanRowPlus (max 1 c₂) P jStar F H s t e φ uP := by
  have hsplit := integral_cutoffStateMeanAux_sub_respYPlus_eq_cell_add_osc P jStar F H s t ht e
    φ uP hY hgrid hφG1 hG1 hint1 h1_1 h2_1 hφG2 hG2 hint2 h1_2 h2_2
    hIntM1 hIntC1 hIntOsc1 hIntCell1 hIntM2 hIntC2 hIntOsc2 hIntCell2
  let Ncell : BlockVec d :=
    ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P),
     (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P))
  let Nosc : BlockVec d :=
    ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P),
     (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
            (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P))
  exact cutoffMeanRowPlus_of_halves P jStar F H s t e φ uP c₂ hc₂ Ncell Nosc
    hsplit.1 hsplit.2 hcell hosc hτ hL

end

end Homogenization.HighContrast.Multiscale
