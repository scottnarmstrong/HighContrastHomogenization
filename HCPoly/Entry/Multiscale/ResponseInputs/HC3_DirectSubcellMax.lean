import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeMaximizer

/-!
# Response maximizers on every aligned subcell

The terminal-optimizer replacement of `p.response.transfer` compares the optimizer of the
terminal cell with the optimizer of each aligned subcell `z + ⋄_j^q` of the coarse scale.
This module supplies the existence input for that comparison: for the recentred coefficient
families `a_-` and `a_+` and for every sample, a scalar canonical response maximizer exists
on each translated aligned cell `adaptedCellAtCenter q j w`.  The centered-cell statements
`nonempty_scalarCanonicalMaximizer_respCoeffMinus` and `..._respCoeffPlus` are transported to
the translate by exhibiting the translate as an affine image of the centered adapted cell,
which is open, bounded, convex and nonempty.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Existence of a scalar canonical maximizer for `a_- = a - g` on the translated aligned
cell `z + ⋄_j^q` at `z = 3^j q w`, the aligned subcell produced by subdividing the coarse
scale.  This is the translate of `nonempty_scalarCanonicalMaximizer_respCoeffMinus` to the
recentred coefficient `a_-`. -/
theorem nonempty_scalarCanonicalMaximizer_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) :
    Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q j w) p r (respCoeffMinus F a)) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq j (adaptedCellCenter q j w) a
  have hEll' := isEllipticFieldOn_sub_skew hEll (respg F) (respg_isSkew F)
  have hne : (adaptedCellAtCenter q j w).Nonempty := by
    obtain ⟨z, hz⟩ := adaptedCell_nonempty q j
    exact ⟨adaptedCellCenter q j w + z, z, hz, rfl⟩
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter q j w) := by
    change IsOpenBoundedConvexDomain
      (HighContrast.adaptedCellTranslate q j (adaptedCellCenter q j w))
    rw [Annealed.adaptedCellTranslate_eq_cg_affine]
    exact isOpenBoundedConvexDomain_affine_openCube q hq j (adaptedCellCenter q j w)
  have hbase : Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q j w) p r
      (fun x => f x - respg F)) :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hdom hEll' p r
  refine nonempty_scalarCanonicalMaximizer_of_aeEq ?_ p r hbase
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffMinus, hx]

/-- Existence of a scalar canonical maximizer for `a_+ = a^t + g` on the translated aligned
cell `z + ⋄_j^q` at `z = 3^j q w`, the aligned subcell produced by subdividing the coarse
scale.  This is the translate of `nonempty_scalarCanonicalMaximizer_respCoeffPlus` to the
recentred coefficient `a_+`. -/
theorem nonempty_scalarCanonicalMaximizer_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) :
    Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q j w) p r (respCoeffPlus F a)) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq j (adaptedCellCenter q j w) a
  have hEll' := isEllipticFieldOn_transpose_add_skew hEll (respg F) (respg_isSkew F)
  have hne : (adaptedCellAtCenter q j w).Nonempty := by
    obtain ⟨z, hz⟩ := adaptedCell_nonempty q j
    exact ⟨adaptedCellCenter q j w + z, z, hz, rfl⟩
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter q j w) := by
    change IsOpenBoundedConvexDomain
      (HighContrast.adaptedCellTranslate q j (adaptedCellCenter q j w))
    rw [Annealed.adaptedCellTranslate_eq_cg_affine]
    exact isOpenBoundedConvexDomain_affine_openCube q hq j (adaptedCellCenter q j w)
  have hbase : Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q j w) p r
      (fun x => matTranspose (f x) + respg F)) :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hdom hEll' p r
  refine nonempty_scalarCanonicalMaximizer_of_aeEq ?_ p r hbase
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffPlus, hx]

end

end Homogenization.HighContrast.Multiscale
