import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCellDeficit
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectSubcellMax

/-!
# The subcell deficit bound on the aligned cells of the adapted grid

`HC3_DirectCellDeficit` proves, for an abstract pair of open sets `V ⊆ U`, that the energy of the
restricted optimizer of `U` on `V` is controlled by the response of `V` through the deficit of the
restricted optimizer there:

  `|½ ⨍_V ⟨∇u, symmPart(a) ∇u⟩ - J(V)| ≤ J(V) - ⨍_V g_U(u) + 2 √(J(V) · (J(V) - ⨍_V g_U(u)))`.

The terminal-optimizer replacement of `p.response.transfer` consumes this estimate on the concrete
pair consisting of an aligned subcell `adaptedCellAtCenter q (t - n) w` of the coarse scale sitting inside
the terminal cell `HighContrast.adaptedCell q t`.  This module records that instance: the subcell is an
open bounded convex domain, it is contained in the terminal cell, and the ellipticity of `b` on the
terminal cell transfers to the subcell.  The maximizer on the subcell and the finite-measure
instance are supplied by the caller, so the bound holds for whatever subcell maximizer is at hand.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The subcell deficit controls the terminal optimizer's energy on an aligned adapted
subcell.**  Let `b` be elliptic on the terminal cell `HighContrast.adaptedCell q t`, let `u` be
`b`-harmonic there, and let `w ∈ triadicIndexBox d n`, so that the depth-`n` subcell
`adaptedCellAtCenter q (t - n) w` is an open bounded convex domain contained in the terminal cell.  For
any response maximizer `v` on that subcell — with the subcell response and the deficit of the
restricted parent `u` — the terminal optimizer's energy on the subcell is controlled by

  `|½ ⨍ ⟨∇u, symmPart(b) ∇u⟩ - J| ≤ D + 2 √(J · D)`

with `J = J(adaptedCellAtCenter q (t - n) w; p, r; b)` and
`D = J - ⨍ g_{adaptedCell q t}(u)`.  The caller supplies both the finite-measure instance and the
subcell maximizer together with the inequality relating them. -/
theorem abs_half_energy_adaptedCellAtCenter_sub_responseJ_le {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) (n : ℕ) {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n)
    (hside : ∀ (_hfin : MeasureTheory.IsFiniteMeasure
          (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)))
        (v : AHarmonicFunction b (adaptedCellAtCenter q (t - (n : ℤ)) w)),
      IsResponseMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b v →
      |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand b u)
          - ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b|
        ≤ (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
            - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))
          + 2 * Real.sqrt (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b *
              (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
                - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                    (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u)))) :
    |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand b u)
        - ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b|
      ≤ (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
          - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))
        + 2 * Real.sqrt (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b *
            (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
              - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))) := by
  have hVfin : volume (adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hVopen : IsOpen (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter q hq (t - (n : ℤ)) w
  have hne : (adaptedCellAtCenter q (t - (n : ℤ)) w).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hpos := volume_adaptedCellAtCenter_toReal_pos q hq (t - (n : ℤ)) w
    rw [h] at hpos
    simp at hpos
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) b :=
    hEll.mono hVopen.measurableSet hVU
  obtain ⟨v⟩ :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hdom hEllV p r
  exact hside ⟨by simpa [volumeMeasureOn] using hVfin.lt_top⟩
    (v : AHarmonicFunction b (adaptedCellAtCenter q (t - (n : ℤ)) w)) v.isResponseMaximizer

end

end Homogenization.HighContrast.Multiscale

