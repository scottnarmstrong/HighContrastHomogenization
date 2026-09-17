import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakQRRecombined
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakPartitionAE
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCellCover

/-!
# The recombined quadratic-response identity on an almost-everywhere partition

The recombined quadratic-response identity is stated over an exact finite cover
`U = ⋃ w ∈ Z, V w` with equal cell volumes.  The adapted
cells the response estimate uses are open, so they meet their parent cell only up to the grid
seams; the exact cover is not available at those carriers and the identity cannot be
instantiated there.  This file restates the two statements with the almost-everywhere
hypotheses of `h6a_average_over_aePartition`: the cells are contained in `U`, `U` differs from
their union by a null set, and the equal-volume condition is stated through `.toReal`.

The new hypotheses are implied by the old ones — `hcover` gives containment and a null
difference, and the equal-volume identity in `ℝ≥0∞` gives its `.toReal` form once `U` has
finite measure — so these statements are strictly stronger than the exact-cover originals.

The per-cell average of the parent integrand depends on the cell, so the abstract recombination
carries `gavg : iota → ℝ`; the right-hand side is the parent average.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- **Averaging a per-cell deficit identity over an almost-everywhere finite equal-volume
partition.**  Suppose the measurable cells `V w` (`w ∈ Z`) are pairwise disjoint and contained
in `U`, that `U` differs from their union by a null set, and that each cell has the same volume
`|V w| = |U| / |Z|` stated in `.toReal` form.  If each cell carries the deficit identity
`Eng w = 2 (Jchild w − gavg w)` for its own parent average `gavg w`, and the flat average of
those parent averages is `Jparent`, then the flat average of `Eng` is twice the difference
between the flat average of `Jchild` and `Jparent`.  The exact equal-volume cover is replaced
here by the almost-everywhere cover `h6a_average_over_aePartition`. -/
theorem h6a_avg_difference_energy_eq_deficit_adapted_ae {iota : Type*}
    (Z : Finset iota) (V : iota → Set (Vec d)) (U : Set (Vec d))
    (g : Vec d → ℝ) (Eng Jchild : iota → ℝ)
    (hZ : Z.Nonempty)
    (hmeas : ∀ w ∈ Z, MeasurableSet (V w))
    (hdisj : ∀ w ∈ Z, ∀ w' ∈ Z, w ≠ w' → Disjoint (V w) (V w'))
    (hsub : ∀ w ∈ Z, V w ⊆ U)
    (hnull : volume (U \ ⋃ w ∈ Z, V w) = 0)
    (hvolw : ∀ w ∈ Z, ((Z.card : ℝ)) * (volume (V w)).toReal = (volume U).toReal)
    (hint : IntegrableOn g U)
    (hUpos : 0 < (volume U).toReal) (hUfin : volume U ≠ ⊤)
    (hpair : ∀ w ∈ Z, Eng w = 2 * (Jchild w - volumeAverage (V w) g)) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Eng w
      = 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, Jchild w - volumeAverage U g) := by
  exact h6a_avg_difference_energy_eq_deficit Z Eng Jchild
    (fun w => volumeAverage (V w) g) (volumeAverage U g) hZ hpair
    (h6a_average_over_aePartition Z V U g hmeas hdisj hsub hnull hvolw hint hUpos hUfin hZ)

omit [NeZero d] in
/-- **The cell instance of the quadratic response recombination over an almost-everywhere
partition.**  The exact cover of the recombination is replaced here by the almost-everywhere
hypotheses: the cells `V w` (`w ∈ Z`) are contained in `U`,
`U` differs from their union by a null set, and the equal-volume condition is stated through
`.toReal`.  The result is the flat average of the cell difference energies in terms of the flat
average of the cell responses and the parent response:

  `|Z|⁻¹ ∑_w ⨍_{V w} (∇u − ∇v_w) · symmPart(a) (∇u − ∇v_w)
     = 2 (|Z|⁻¹ ∑_w J(V w) − J(U))`.

Because the difference energy is written with the parent gradient `∇u`, the gradients of the
restrictions of `u` agree with `∇u` definitionally and no separate rewriting hypothesis is
needed. -/
theorem h6a_avg_difference_energy_eq_responseJ_deficit_ae {iota : Type*}
    (Z : Finset iota) (V : iota → Set (Vec d)) (U : Set (Vec d))
    {a : CoeffField d} {lam Lam : ℝ} {p q : Vec d}
    (u : AHarmonicFunction a U) (v : (w : iota) → AHarmonicFunction a (V w))
    [hfin : ∀ w, IsFiniteMeasure (volumeMeasureOn (V w))]
    (hZ : Z.Nonempty)
    (hU : IsOpen U) (hVopen : ∀ w ∈ Z, IsOpen (V w))
    (hVU : ∀ w ∈ Z, V w ⊆ U)
    (hsub : ∀ w ∈ Z, V w ⊆ U)
    (hnull : volume (U \ ⋃ w ∈ Z, V w) = 0)
    (hvolw : ∀ w ∈ Z, ((Z.card : ℝ)) * (volume (V w)).toReal = (volume U).toReal)
    (hEll : ∀ w ∈ Z, IsEllipticFieldOn lam Lam (V w) a)
    (hmaxV : ∀ w ∈ Z, IsResponseMaximizer (V w) p q a (v w))
    (huV_int : ∀ w (hw : w ∈ Z), weakFluxIntegrable (V w) a
      (u.restrictOfIsEllipticFieldOn hU (hVopen w hw) (hVU w hw) (hEll w hw)))
    (hv_int : ∀ w ∈ Z, weakFluxIntegrable (V w) a (v w))
    (hresp_v : ∀ w ∈ Z, IntegrableOn (scalarResponseIntegrand (V w) a p q (v w)) (V w))
    (hlin : ∀ w (hw : w ∈ Z), IntegrableOn (scalarFirstVariationIntegrand (V w) a p q (v w)
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU (hVopen w hw) (hVU w hw) (hEll w hw)) (v w)
        (huV_int w hw) (hv_int w hw) (-1))) (V w))
    (henergy : ∀ w (hw : w ∈ Z), IntegrableOn (scalarVariationEnergyIntegrand a
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU (hVopen w hw) (hVU w hw) (hEll w hw)) (v w)
        (huV_int w hw) (hv_int w hw) (-1))) (V w))
    (hmeas : ∀ w ∈ Z, MeasurableSet (V w))
    (hdisj : ∀ w ∈ Z, ∀ w' ∈ Z, w ≠ w' → Disjoint (V w) (V w'))
    (hint : IntegrableOn (scalarResponseIntegrand U a p q u) U)
    (hUpos : 0 < (volume U).toReal) (hUfin : volume U ≠ ⊤)
    (hmaxU : IsResponseMaximizer U p q a u) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z,
        volumeAverage (V w) (fun x => vecDot (u.toH1.grad x - (v w).toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - (v w).toH1.grad x)))
      = 2 * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, ResponseJ (V w) p q a - ResponseJ U p q a) := by
  have hpair : ∀ w ∈ Z,
      volumeAverage (V w) (fun x => vecDot (u.toH1.grad x - (v w).toH1.grad x)
        (matVecMul (symmPart (a x)) (u.toH1.grad x - (v w).toH1.grad x)))
      = 2 * (ResponseJ (V w) p q a
        - volumeAverage (V w) (scalarResponseIntegrand U a p q u)) := by
    intro w hw
    exact h6a_difference_energy_eq_response_deficit (hVU w hw) hU (hVopen w hw)
      (hEll w hw) (hmaxV w hw) (huV_int w hw) (hv_int w hw) (hresp_v w hw)
      (hlin w hw) (henergy w hw)
  have hmain := h6a_avg_difference_energy_eq_deficit_adapted_ae Z V U
    (scalarResponseIntegrand U a p q u)
    (fun w => volumeAverage (V w) (fun x => vecDot (u.toH1.grad x - (v w).toH1.grad x)
      (matVecMul (symmPart (a x)) (u.toH1.grad x - (v w).toH1.grad x))))
    (fun w => ResponseJ (V w) p q a)
    hZ hmeas hdisj hsub hnull hvolw hint hUpos hUfin hpair
  rw [hmain, ← responseJ_eq_of_isResponseMaximizer U p q a hmaxU]

omit [NeZero d] in
/-- **The recombined quadratic-response identity at the aligned adapted cells.**  For an
invertible grid `q`, generation `t` and depth `n`, the partition geometry of
`h6a_avg_difference_energy_eq_responseJ_deficit_ae` is supplied by the tree's cell lemmas: the
depth-`n` subcells of `HighContrast.adaptedCell q t` are open hence measurable, pairwise disjoint,
contained in the parent, omit only the null grid seams, and have equal volume, and the parent
cell has positive finite volume.  The elliptic, maximizer and integrability data are not
available from `IsUnit q` alone and remain explicit hypotheses. -/
theorem h6a_avg_difference_energy_eq_responseJ_deficit_adaptedCell_ae
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ)
    {a : CoeffField d} {lam Lam : ℝ} {p r : Vec d}
    (u : AHarmonicFunction a (HighContrast.adaptedCell q t))
    (v : (w : Fin d → ℤ) → AHarmonicFunction a (adaptedCellAtCenter q (t - (n : ℤ)) w))
    [hfin : ∀ w, IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w))]
    (hEll : ∀ w ∈ triadicIndexBox d n,
      IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) a)
    (hmaxV : ∀ w ∈ triadicIndexBox d n,
      IsResponseMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r a (v w))
    (huV_int : ∀ w (hw : w ∈ triadicIndexBox d n),
      weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) a
        (u.restrictOfIsEllipticFieldOn (isOpen_adaptedCell_of_isUnit hq t)
          (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w)
          (adaptedCellAtCenter_subset_adaptedCell q t n hw) (hEll w hw)))
    (hv_int : ∀ w ∈ triadicIndexBox d n,
      weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) a (v w))
    (hresp_v : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (scalarResponseIntegrand (adaptedCellAtCenter q (t - (n : ℤ)) w) a p r (v w))
        (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hlin : ∀ w (hw : w ∈ triadicIndexBox d n),
      IntegrableOn (scalarFirstVariationIntegrand (adaptedCellAtCenter q (t - (n : ℤ)) w) a p r (v w)
        (AHarmonicFunction.addSMulOfIntegrable
          (u.restrictOfIsEllipticFieldOn (isOpen_adaptedCell_of_isUnit hq t)
            (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w)
            (adaptedCellAtCenter_subset_adaptedCell q t n hw) (hEll w hw)) (v w)
          (huV_int w hw) (hv_int w hw) (-1)))
        (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (henergy : ∀ w (hw : w ∈ triadicIndexBox d n),
      IntegrableOn (scalarVariationEnergyIntegrand a
        (AHarmonicFunction.addSMulOfIntegrable
          (u.restrictOfIsEllipticFieldOn (isOpen_adaptedCell_of_isUnit hq t)
            (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w)
            (adaptedCellAtCenter_subset_adaptedCell q t n hw) (hEll w hw)) (v w)
          (huV_int w hw) (hv_int w hw) (-1)))
        (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hint : IntegrableOn (scalarResponseIntegrand (HighContrast.adaptedCell q t) a p r u)
      (HighContrast.adaptedCell q t))
    (hmaxU : IsResponseMaximizer (HighContrast.adaptedCell q t) p r a u) :
    ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (fun x => vecDot (u.toH1.grad x - (v w).toH1.grad x)
            (matVecMul (symmPart (a x)) (u.toH1.grad x - (v w).toH1.grad x)))
      = 2 * (((triadicIndexBox d n).card : ℝ)⁻¹ *
          ∑ w ∈ triadicIndexBox d n, ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r a
        - ResponseJ (HighContrast.adaptedCell q t) p r a) := by
  have hUfin : volume (HighContrast.adaptedCell q t) ≠ ⊤ := by
    rw [Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hUpos : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [Geometry.volume_adaptedCell_toReal]
    have hdet : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  have hZne : (triadicIndexBox d n).Nonempty := by
    refine ⟨0, ?_⟩
    rw [triadicIndexBox, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr
      ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩
  exact h6a_avg_difference_energy_eq_responseJ_deficit_ae
    (triadicIndexBox d n) (fun w => adaptedCellAtCenter q (t - (n : ℤ)) w)
    (HighContrast.adaptedCell q t) u v hZne
    (isOpen_adaptedCell_of_isUnit hq t)
    (fun w _ => isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w)
    (fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw)
    (fun w hw => adaptedCellAtCenter_subset_adaptedCell q t n hw)
    (h6a_adaptedCell_diff_biUnion_null q hq t n)
    (fun w _ => h6a_volume_adaptedCellAtCenter_card_eq q hq t n w)
    hEll hmaxV huV_int hv_int hresp_v hlin henergy
    (fun w _ => (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet)
    (fun w _ w' _ hww' => Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (n : ℤ)) hww')
    hint hUpos hUfin hmaxU

end

end Homogenization.HighContrast.Multiscale
