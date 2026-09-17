import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakHeadTail
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSupport

/-!
# The left-hand side of the cell-average estimate, public

The cell-average estimate has left-hand side

`3 ^ (-(t / 2)) * besovSeminorm t (fun n w => blockMatVecMul A (cellAverageFamily q t X n w - c))`,

and its argument needs that quantity rewritten as a `besovSeminorm` of a genuine
`cellAverageFamily` and then split at the window depth.  `HC2b_DiagonalWeakRecentSupport2.lean`
contains both steps, but `private`, so no consumer above that module can reach them.  This module
lands public copies.

The recentring here asks integrability only on the cells the seminorm actually reads,
`w ∈ triadicIndexBox d n`, rather than on every label; that is exactly the hypothesis
`besovSeminorm_congr` needs.

## Main results

* `h6a_cellAverage_blockMatVecMul_pub`: the cell average commutes with block transport.
* `h6a_cellAverage_sub_const_pub`: the cell average of a recentred field.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem h6a_integrableOn_matVecMul_apply {V : Set (Vec d)} (M : Mat d) (Y : Vec d → Vec d)
    (hY : ∀ j, IntegrableOn (fun x => Y x j) V) (i : Fin d) :
    IntegrableOn (fun x => matVecMul M (Y x) i) V := by
  have h : (fun x => matVecMul M (Y x) i) = fun x => ∑ j, M i j * Y x j := rfl
  rw [h]
  exact integrable_finsetSum _ (fun j _ => (hY j).const_mul (M i j))

omit [NeZero d] in
private theorem h6a_volumeAverage_sub_const {V : Set (Vec d)} (hVfin : volume V ≠ ⊤)
    (hvol : (volume V).toReal ≠ 0) {f : Vec d → ℝ} (hf : IntegrableOn f V) (k : ℝ) :
    volumeAverage V (fun x => f x - k) = volumeAverage V f - k := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hVfin⟩
  have hc : IntegrableOn (fun _ : Vec d => k) V := integrable_const k
  have h : (fun x => f x - k) = f - (fun _ => k) := rfl
  rw [h, volumeAverage_sub hf hc, volumeAverage_const hvol]

omit [NeZero d] in
/-- The cell average commutes with the block transport: averaging the transported field is the
transport of the averaged field.  Integrability is asked componentwise on `V`. -/
theorem h6a_cellAverage_blockMatVecMul_pub {V : Set (Vec d)} (A : BlockMat d)
    (Y : Vec d → BlockVec d)
    (h1 : ∀ j, IntegrableOn (fun x => (Y x).1 j) V)
    (h2 : ∀ j, IntegrableOn (fun x => (Y x).2 j) V) :
    cellAverage V (fun x => blockMatVecMul A (Y x)) = blockMatVecMul A (cellAverage V Y) := by
  have key : ∀ (M N : Mat d) (i : Fin d),
      volumeAverage V (fun x => matVecMul M (Y x).1 i + matVecMul N (Y x).2 i)
        = matVecMul M (fun j => volumeAverage V (fun x => (Y x).1 j)) i
          + matVecMul N (fun j => volumeAverage V (fun x => (Y x).2 j)) i := by
    intro M N i
    have hM : IntegrableOn (fun x => matVecMul M (Y x).1 i) V :=
      h6a_integrableOn_matVecMul_apply M (fun x => (Y x).1) h1 i
    have hN : IntegrableOn (fun x => matVecMul N (Y x).2 i) V :=
      h6a_integrableOn_matVecMul_apply N (fun x => (Y x).2) h2 i
    have hsplit : (fun x => matVecMul M (Y x).1 i + matVecMul N (Y x).2 i)
        = (fun x => matVecMul M (Y x).1 i) + (fun x => matVecMul N (Y x).2 i) := rfl
    rw [hsplit, volumeAverage_add hM hN]
    congr 1
    · exact volumeAverage_vecDot_left (M i) (fun x => (Y x).1) h1
    · exact volumeAverage_vecDot_left (N i) (fun x => (Y x).2) h2
  have hfst : (cellAverage V fun x => blockMatVecMul A (Y x)).1
      = (blockMatVecMul A (cellAverage V Y)).1 := by
    funext i
    exact key A.upperLeft A.upperRight i
  have hsnd : (cellAverage V fun x => blockMatVecMul A (Y x)).2
      = (blockMatVecMul A (cellAverage V Y)).2 := by
    funext i
    exact key A.lowerLeft A.lowerRight i
  exact Prod.ext hfst hsnd

omit [NeZero d] in
/-- The cell average of a recentred field is the recentred cell average, provided the cell has
finite and nonzero volume so that the constant integrates to itself. -/
theorem h6a_cellAverage_sub_const_pub {V : Set (Vec d)} (hVfin : volume V ≠ ⊤)
    (hVpos : (volume V).toReal ≠ 0) (Y : Vec d → BlockVec d) (c : BlockVec d)
    (h1 : ∀ j, IntegrableOn (fun x => (Y x).1 j) V)
    (h2 : ∀ j, IntegrableOn (fun x => (Y x).2 j) V) :
    cellAverage V (fun x => Y x - c) = cellAverage V Y - c := by
  have hfst : (cellAverage V fun x => Y x - c).1 = (cellAverage V Y - c).1 := by
    funext i
    exact h6a_volumeAverage_sub_const hVfin hVpos (h1 i) (c.1 i)
  have hsnd : (cellAverage V fun x => Y x - c).2 = (cellAverage V Y - c).2 := by
    funext i
    exact h6a_volumeAverage_sub_const hVfin hVpos (h2 i) (c.2 i)
  exact Prod.ext hfst hsnd

end

end Homogenization.HighContrast.Multiscale
