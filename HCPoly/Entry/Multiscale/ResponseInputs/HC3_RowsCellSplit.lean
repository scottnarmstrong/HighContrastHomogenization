import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsMeanSplit
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock

/-!
# The integrated cutoff-mean defect splits into its cell and oscillation parts

The centred cutoff decomposition of `e.response.cutoff.estimate` leaves the defect of the
annealed cutoff-weighted state mean against the annealed mean `Y^∓`.  On the terminal cell the
mean `Y^∓` is the annealed cell average of the optimizer state `X = (∇v, b ∇v)`, so that defect
is the annealed `(φ - 1)`-weighted average of `X`.  Subdividing the terminal cell into its
depth-`H` triadic subcells splits it, coordinate by coordinate, into a cell part — the subcell
means of `φ - 1` times the subcell means of the state — and an oscillation part — the subcell
averages of `φ` minus their own cell means, weighted by the state.  This file integrates the
pathwise split `cutoffStateMeanAux_fst_eq_osc_add_cell` /
`cutoffStateMeanAux_snd_eq_osc_add_cell` against the law `P`, keeping the two parts as separate
functions so that a later assembly can consume each one.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The integrated cutoff-mean defect splits for the recentred response**
(`e.response.cutoff.estimate`).  Assume that `Y^-` is the annealed cell average of the terminal
optimizer state `X = (∇v, b ∇v)` with `b = respCoeffMinus F` (the hypothesis `hY`), that the
grid `respGrid F` is invertible, and that the sample functions of the split are integrable, both
on the terminal cell and on each depth-`H` triadic subcell, and `P`-integrable as functions of the
coefficient.  Then the annealed cutoff-mean defect
`∫_a (cutoffStateMeanAux U φ (X a)) i - (Y^-) i` splits, in each of the two coordinates, into the
annealed CELL part — the flat average over the depth-`H` subcells of `(⨍ φ - 1)` times the subcell
mean of the coordinate — plus the annealed OSCILLATION part — the flat average over the subcells
of the subcell mean of `(φ - ⨍ φ)` times the coordinate.  The two parts are kept as separate
functions added with `+`, as the row assembly consumes them separately. -/
theorem integral_cutoffStateMeanAux_sub_respYMinus_eq_cell_add_osc {d : ℕ} [NeZero d]
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
            (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) P) :
    ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1
        = (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P)
          + (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P))
      ∧ ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
            (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2
        = (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P)
          + (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P)) := by
  have hst : t - (H : ℤ) = s := by omega
  constructor
  · funext i
    have hY1 : (respYMinus P jStar F t e).1
        = fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).1 i ∂P := by
      rw [hY]
    have hpath : ∀ a : CoeffSpace d,
        (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).1 i
          - (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).1 i
        = ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
          + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) := by
      intro a
      have hsplit := cutoffStateMeanAux_fst_eq_osc_add_cell (respGrid jStar F) hgrid t H φ
        (uM a) i (hφG1 a i) (hG1 a i) (hint1 a i) (h1_1 a i) (h2_1 a i)
      rwa [hst] at hsplit
    simp only [Pi.sub_apply, Pi.add_apply, hY1]
    calc (∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).1 i ∂P)
        - (∫ a, (cellAverage (respCell jStar F t)
          (optimizerField (respCoeffMinus F a) (uM a))).1 i ∂P)
        = ∫ a, ((cutoffStateMeanAux (respCell jStar F t) φ
              (respCoeffMinus F a) (uM a)).1 i
            - (cellAverage (respCell jStar F t)
              (optimizerField (respCoeffMinus F a) (uM a))).1 i) ∂P :=
          (integral_sub (hIntM1 i) (hIntC1 i)).symm
      _ = ∫ a, (((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
            + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i)) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards with a
          exact hpath a
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P) :=
          integral_add (hIntOsc1 i) (hIntCell1 i)
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P) :=
          add_comm _ _
  · funext i
    have hY2 : (respYMinus P jStar F t e).2
        = fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).2 i ∂P := by
      rw [hY]
    have hpath : ∀ a : CoeffSpace d,
        (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).2 i
          - (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffMinus F a) (uM a))).2 i
        = ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
          + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) := by
      intro a
      have hsplit := cutoffStateMeanAux_snd_eq_osc_add_cell (respGrid jStar F) hgrid t H φ
        (uM a) i (hφG2 a i) (hG2 a i) (hint2 a i) (h1_2 a i) (h2_2 a i)
      rwa [hst] at hsplit
    simp only [Pi.sub_apply, Pi.add_apply, hY2]
    calc (∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).2 i ∂P)
        - (∫ a, (cellAverage (respCell jStar F t)
          (optimizerField (respCoeffMinus F a) (uM a))).2 i ∂P)
        = ∫ a, ((cutoffStateMeanAux (respCell jStar F t) φ
              (respCoeffMinus F a) (uM a)).2 i
            - (cellAverage (respCell jStar F t)
              (optimizerField (respCoeffMinus F a) (uM a))).2 i) ∂P :=
          (integral_sub (hIntM2 i) (hIntC2 i)).symm
      _ = ∫ a, (((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
            + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards with a
          exact hpath a
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P) :=
          integral_add (hIntOsc2 i) (hIntCell2 i)
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P) :=
          add_comm _ _

/-- **The integrated cutoff-mean defect splits for the adjoint recentred response**
(`e.response.cutoff.estimate`).  The adjoint twin of
`integral_cutoffStateMeanAux_sub_respYMinus_eq_cell_add_osc`: with `Y^+` the annealed cell average
of the terminal optimizer state for the adjoint recentred coefficient `respCoeffPlus F`, the
annealed cutoff-mean defect splits, in each coordinate, into the annealed CELL part — the flat
average over the depth-`H` subcells of `(⨍ φ - 1)` times the subcell mean of the coordinate — plus
the annealed OSCILLATION part, the two kept as separate functions. -/
theorem integral_cutoffStateMeanAux_sub_respYPlus_eq_cell_add_osc {d : ℕ} [NeZero d]
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
            (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) P) :
    ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1
        = (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P)
          + (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P))
      ∧ ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
            (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2
        = (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P)
          + (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P)) := by
  have hst : t - (H : ℤ) = s := by omega
  constructor
  · funext i
    have hY1 : (respYPlus P jStar F t e).1
        = fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).1 i ∂P := by
      rw [hY]
    have hpath : ∀ a : CoeffSpace d,
        (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).1 i
          - (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).1 i
        = ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
          + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) := by
      intro a
      have hsplit := cutoffStateMeanAux_fst_eq_osc_add_cell (respGrid jStar F) hgrid t H φ
        (uP a) i (hφG1 a i) (hG1 a i) (hint1 a i) (h1_1 a i) (h2_1 a i)
      rwa [hst] at hsplit
    simp only [Pi.sub_apply, Pi.add_apply, hY1]
    calc (∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).1 i ∂P)
        - (∫ a, (cellAverage (respCell jStar F t)
          (optimizerField (respCoeffPlus F a) (uP a))).1 i ∂P)
        = ∫ a, ((cutoffStateMeanAux (respCell jStar F t) φ
              (respCoeffPlus F a) (uP a)).1 i
            - (cellAverage (respCell jStar F t)
              (optimizerField (respCoeffPlus F a) (uP a))).1 i) ∂P :=
          (integral_sub (hIntM1 i) (hIntC1 i)).symm
      _ = ∫ a, (((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
            + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i)) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards with a
          exact hpath a
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P) :=
          integral_add (hIntOsc1 i) (hIntCell1 i)
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P) :=
          add_comm _ _
  · funext i
    have hY2 : (respYPlus P jStar F t e).2
        = fun i => ∫ a, (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).2 i ∂P := by
      rw [hY]
    have hpath : ∀ a : CoeffSpace d,
        (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).2 i
          - (cellAverage (respCell jStar F t)
            (optimizerField (respCoeffPlus F a) (uP a))).2 i
        = ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
          + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) := by
      intro a
      have hsplit := cutoffStateMeanAux_snd_eq_osc_add_cell (respGrid jStar F) hgrid t H φ
        (uP a) i (hφG2 a i) (hG2 a i) (hint2 a i) (h1_2 a i) (h2_2 a i)
      rwa [hst] at hsplit
    simp only [Pi.sub_apply, Pi.add_apply, hY2]
    calc (∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).2 i ∂P)
        - (∫ a, (cellAverage (respCell jStar F t)
          (optimizerField (respCoeffPlus F a) (uP a))).2 i ∂P)
        = ∫ a, ((cutoffStateMeanAux (respCell jStar F t) φ
              (respCoeffPlus F a) (uP a)).2 i
            - (cellAverage (respCell jStar F t)
              (optimizerField (respCoeffPlus F a) (uP a))).2 i) ∂P :=
          (integral_sub (hIntM2 i) (hIntC2 i)).symm
      _ = ∫ a, (((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
            + ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards with a
          exact hpath a
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P) :=
          integral_add (hIntOsc2 i) (hIntCell2 i)
      _ = (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                  (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P)
            + (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                  (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P) :=
          add_comm _ _

end

end Homogenization.HighContrast.Multiscale
