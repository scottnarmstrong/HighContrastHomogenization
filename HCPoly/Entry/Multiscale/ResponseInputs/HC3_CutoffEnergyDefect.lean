import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffWeakGlue
import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Ellipticity

/-!
# The cutoff energy defect as a `(φ − 1)`-weighted energy

At a response maximizer the pathwise response `J(U; p, r; b)` of AK.HC (2.9) is half the
unweighted variation energy.  Consequently, in the centred cutoff decomposition of
AK.HC (3.45)-(3.54), replacing the terminal optimizer energy by the pathwise response leaves
exactly the `(φ − 1)`-weighted optimizer energy: the cost of the terminal-optimizer replacement
is the fluctuation of the optimizer energy against the cutoff, and `φ − 1` has mean zero on the
cell where `φ` has mean one.

* `cutoffHalfEnergy_sub_respJ_eq` — the first error row `e1`: the terminal-optimizer replacement
  costs exactly the `(φ − 1)`-weighted energy.
* `volumeAverage_sub_one_eq_zero` — a cutoff of mean one has mean-zero fluctuation.

Paper: AK.HC (3.45)-(3.54).
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The doubled optimizer energy `⟨Z₁, Z₂⟩ = ∇v · b ∇v` agrees pointwise with the variation
energy `∇v · (symmPart b) ∇v`: the antisymmetric part of `b` contributes nothing to the
quadratic form. -/
private theorem vecDot_optimizerField_eq {d : ℕ} (b : CoeffField d) {U : Set (Vec d)}
    (v : AHarmonicFunction b U) :
    (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      = scalarVariationEnergyIntegrand b v := by
  funext x
  simp only [optimizerField, scalarVariationEnergyIntegrand]
  exact (vecDot_matVecMul_symmPart (b x) (v.toH1.grad x)).symm

/-- **The cutoff energy defect `e1`.**  For a response maximizer `v` of the loads `(p, r)` in the
adapted cell `⋄_t^q`, the cutoff-weighted half optimizer energy differs from the pathwise
response `J(U; p, r; b)` by half the `(φ − 1)`-weighted optimizer energy.  This is the exact
algebraic form of the first error row of the centred cutoff decomposition AK.HC (3.45)-(3.54):
the terminal-optimizer replacement costs the `(φ − 1)`-weighted energy, and `φ − 1` has mean
zero on the cell.  The side conditions are the integrability hypotheses of the CoarseGraining
energy–response identity together with the integrability of the weighted energy. -/
theorem cutoffHalfEnergy_sub_respJ_eq {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (φ : Vec d → ℝ) (p r : Vec d) (v : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hv : IsResponseMaximizer (HighContrast.adaptedCell q t) p r b v)
    (hu_int : weakFluxIntegrable (HighContrast.adaptedCell q t) b v)
    (hresp_u : IntegrableOn
      (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r v)
      (HighContrast.adaptedCell q t))
    (hlin_self : IntegrableOn
      (scalarFirstVariationIntegrand (HighContrast.adaptedCell q t) b p r v v)
      (HighContrast.adaptedCell q t))
    (henergy : IntegrableOn (scalarVariationEnergyIntegrand b v) (HighContrast.adaptedCell q t))
    (hφD : IntegrableOn
      (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      (HighContrast.adaptedCell q t)) :
    (1 / 2 : ℝ) * volumeAverage (HighContrast.adaptedCell q t)
        (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      - respJ q t p r b
    = (1 / 2 : ℝ) * volumeAverage (HighContrast.adaptedCell q t)
        (fun x => (φ x - 1) * vecDot (optimizerField b v x).1 (optimizerField b v x).2) := by
  have _ := hq
  have _ := hEll
  have hD_eq := vecDot_optimizerField_eq b v
  have hD_int : IntegrableOn
      (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      (HighContrast.adaptedCell q t) := by
    rw [hD_eq]
    exact henergy
  have hsub : volumeAverage (HighContrast.adaptedCell q t)
        (fun x => (φ x - 1) * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      = volumeAverage (HighContrast.adaptedCell q t)
          (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
        - volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v) := by
    have hfun :
        (fun x => (φ x - 1) * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
          = (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
            - (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2) := by
      funext x
      simp only [Pi.sub_apply]
      ring
    rw [hfun, volumeAverage_sub hφD hD_int, hD_eq]
  unfold respJ
  rw [responseJ_energy_of_isResponseMaximizer (HighContrast.adaptedCell q t) b p r v hv
    hu_int hresp_u hlin_self henergy]
  rw [hsub]
  ring

/-- **Mean-zero fluctuation of a mean-one cutoff.**  If `φ` averages to `1` over a cell of finite
nonzero volume, then `φ − 1` averages to `0`. -/
theorem volumeAverage_sub_one_eq_zero {d : ℕ} (U : Set (Vec d)) {φ : Vec d → ℝ}
    (hφ1 : volumeAverage U φ = 1) (hvol : (volume U).toReal ≠ 0)
    (hφ : IntegrableOn φ U) :
    volumeAverage U (fun x => φ x - 1) = 0 := by
  have hfin : volume U ≠ ⊤ := ((ENNReal.toReal_ne_zero).mp hvol).2
  have h1 : IntegrableOn (fun _ : Vec d => (1 : ℝ)) U := integrableOn_const hfin
  have h : (fun x => φ x - 1) = φ - (fun _ : Vec d => (1 : ℝ)) := by
    funext x
    rfl
  rw [h, volumeAverage_sub hφ h1, hφ1, volumeAverage_const hvol]
  ring

end

end Homogenization.HighContrast.Multiscale
