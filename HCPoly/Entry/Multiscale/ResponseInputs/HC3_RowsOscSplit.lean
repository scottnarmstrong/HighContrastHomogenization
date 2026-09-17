import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm

/-!
# Splitting a weighted cell average over a partition

Weighted averages are not additive in the weight, but they split at a chosen level `c`:
the average of `w * f` is the average of the fluctuation `(w - c) * f` plus the level `c`
times the unweighted average of `f`.  Applying this identity cell by cell and recombining
with the equal-volume partition identity gives the cell decomposition behind the two
cutoff-mean rows of `e.response.cutoff.estimate`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- **Splitting a weighted cell average at a level `c`.**  For any constant `c`, the average
of `w * f` over `V` is the average of `(w - c) * f` over `V` plus `c` times the average of `f`
over `V`.  The first summand records the part of the weight that fluctuates about the level `c`;
the second is that level times the unweighted cell average.  The identity is purely pointwise
under the average and needs only the integrability of the two summands on `V`. -/
theorem volumeAverage_weight_mul_split {d : ℕ} {V : Set (Vec d)} (w : Vec d → ℝ) (c : ℝ)
    (f : Vec d → ℝ)
    (h1 : IntegrableOn (fun x => (w x - c) * f x) V)
    (h2 : IntegrableOn (fun x => c * f x) V) :
    volumeAverage V (fun x => w x * f x)
      = volumeAverage V (fun x => (w x - c) * f x) + c * volumeAverage V f := by
  have hdecomp : (fun x => w x * f x) =
      (fun x => (w x - c) * f x) + (fun x => c * f x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  have hsmul : volumeAverage V (fun x => c * f x) = c * volumeAverage V f := by
    rw [show (fun x => c * f x) = c • f by
      funext x
      simp [smul_eq_mul]]
    exact volumeAverage_smul V c f
  rw [hdecomp, volumeAverage_add h1 h2, hsmul]

end

end Homogenization.HighContrast.Multiscale
