import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportBesov
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportState
import HCPoly.Entry.Multiscale.ResponseInputs.HC2a_ReferenceCubePullback

/-!
# The scale-average seminorm of a recentred doubled field

The scale averages that enter the weak quantity of `e.response.weak.estimate` are the cell
averages of a doubled field after an affine change `Z \mapsto S(Z - Y)` with a constant block
matrix `S` and a constant doubled vector `Y`.  Because the cell average is linear, those averages
are the affine images of the cell averages of the field itself, so the Jensen/partition bound
applies verbatim to the recentred family.

The affine identity needs the two side conditions of an average over a cell: the cell has finite
nonzero volume, and each of the `2d` coordinates of the field is integrable on it.  Both are
supplied here from square integrability on the ambient cell.

Paper: `e.response.weak.estimate`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Linearity of the cell average under a constant affine map -/

/-- The average of `c (g - k)` over a cell of finite nonzero volume is `c` times the average of
`g` minus `k`. -/
theorem volumeAverage_const_mul_sub_const {V : Set (Vec d)} (hfin : volume V ≠ ⊤)
    (hvol : (volume V).toReal ≠ 0) (c k : ℝ) {g : Vec d → ℝ} (hg : IntegrableOn g V) :
    volumeAverage V (fun x => c * (g x - k)) = c * (volumeAverage V g - k) := by
  have hk : IntegrableOn (fun _ : Vec d => k) V := integrableOn_const hfin
  have hsub : volumeAverage V (fun x => g x - k) = volumeAverage V g - k := by
    have h := volumeAverage_sub (U := V) (f := g) (g := fun _ => k) hg hk
    simpa [volumeAverage_const hvol] using! h
  have hsm := volumeAverage_smul V c (fun x => g x - k)
  rw [show (fun x => c * (g x - k)) = (fun x => c • ((fun y => g y - k) x)) from rfl]
  simpa [hsub] using! hsm

/-- Linearity of the doubled cell average under the constant affine map `Z \mapsto S(Z - Y)`. -/
theorem cellAverage_blockMatVecMul_sub_const {V : Set (Vec d)} (hfin : volume V ≠ ⊤)
    (hvol : (volume V).toReal ≠ 0) (S : BlockMat d) (Y : BlockVec d) {Z : Vec d → BlockVec d}
    (h1 : ∀ i, IntegrableOn (fun x => (Z x).1 i) V)
    (h2 : ∀ i, IntegrableOn (fun x => (Z x).2 i) V) :
    cellAverage V (fun x => blockMatVecMul S (Z x - Y))
      = blockMatVecMul S (cellAverage V Z - Y) := by
  classical
  have hintterm : ∀ (c k : ℝ) (g : Vec d → ℝ), IntegrableOn g V →
      IntegrableOn (fun x => c * (g x - k)) V :=
    fun c k g hg => ((hg.sub (integrableOn_const hfin)).const_mul c)
  have hsum1 : ∀ (A : Mat d) (i : Fin d),
      volumeAverage V (fun x => ∑ j, A i j * ((Z x).1 j - Y.1 j))
        = ∑ j, A i j * (volumeAverage V (fun x => (Z x).1 j) - Y.1 j) := by
    intro A i
    rw [volumeAverage_sum Finset.univ (fun j x => A i j * ((Z x).1 j - Y.1 j))
      (fun j _ => hintterm _ _ _ (h1 j))]
    exact Finset.sum_congr rfl fun j _ => volumeAverage_const_mul_sub_const hfin hvol _ _ (h1 j)
  have hsum2 : ∀ (A : Mat d) (i : Fin d),
      volumeAverage V (fun x => ∑ j, A i j * ((Z x).2 j - Y.2 j))
        = ∑ j, A i j * (volumeAverage V (fun x => (Z x).2 j) - Y.2 j) := by
    intro A i
    rw [volumeAverage_sum Finset.univ (fun j x => A i j * ((Z x).2 j - Y.2 j))
      (fun j _ => hintterm _ _ _ (h2 j))]
    exact Finset.sum_congr rfl fun j _ => volumeAverage_const_mul_sub_const hfin hvol _ _ (h2 j)
  have hslot : ∀ (A B : Mat d) (i : Fin d),
      volumeAverage V (fun x =>
          (matVecMul A (Z x - Y).1 + matVecMul B (Z x - Y).2) i)
        = (matVecMul A ((fun i => volumeAverage V (fun x => (Z x).1 i)) - Y.1)
            + matVecMul B ((fun i => volumeAverage V (fun x => (Z x).2 i)) - Y.2)) i := by
    intro A B i
    have hrw : (fun x => (matVecMul A (Z x - Y).1 + matVecMul B (Z x - Y).2) i)
        = fun x => (∑ j, A i j * ((Z x).1 j - Y.1 j)) + ∑ j, B i j * ((Z x).2 j - Y.2 j) := by
      funext x
      simp [matVecMul, Prod.fst_sub, Prod.snd_sub]
    rw [hrw, show (fun x => (∑ j, A i j * ((Z x).1 j - Y.1 j))
          + ∑ j, B i j * ((Z x).2 j - Y.2 j))
        = ((fun x => ∑ j, A i j * ((Z x).1 j - Y.1 j))
          + (fun x => ∑ j, B i j * ((Z x).2 j - Y.2 j))) from rfl]
    rw [volumeAverage_add
      (by exact (MeasureTheory.integrable_finsetSum _ fun j _ => hintterm _ _ _ (h1 j)))
      (by exact (MeasureTheory.integrable_finsetSum _ fun j _ => hintterm _ _ _ (h2 j)))]
    rw [hsum1 A i, hsum2 B i]
    simp [matVecMul]
  refine Prod.ext ?_ ?_ <;> · funext i; simpa [cellAverage, blockMatVecMul] using hslot _ _ i

/-! ## The squared seminorm bound for a recentred family -/

variable [NeZero d]

/-! ## The two recentred response coefficients -/

end

end Homogenization.HighContrast.Multiscale
