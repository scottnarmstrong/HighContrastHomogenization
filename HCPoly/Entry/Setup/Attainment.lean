import HCPoly.Setup.Contrast
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact
import HCPoly.Setup.Attainment
import HCPoly.Setup.BlockAlgebra
import HCPoly.Setup.SpectralBound

/-!
# Attainment of the minimum over the skew parameter

The paper reads the intrinsic contrast and the reference constant `Λ_0` as *minima* over
the skew matrices `h` (`e.Theta.m`, `e.reference.aspect.ratio`), whereas the encodings
`blockContrast` and `bigLambdaRef` of `HCPoly.Setup.BlockAlgebra` are infima.  On the data the
print actually uses — a symmetric doubled block matrix that is positive definite — the two
readings coincide, and this file supplies the proof.

The route is the standard compactness argument.  Positive definiteness makes the lower-right
block `σ_*⁻¹` coercive, so the correction `(k - h)ᵗ σ_*⁻¹ (k - h)` grows quadratically in the
skew parameter; hence the set of skew `h` obeying a fixed Loewner bound is bounded, and it is
closed because the Loewner order is cut out by closed conditions.  A Cantor intersection along
thresholds decreasing to the infimum produces a skew matrix at which the infimum is attained.
-/

open Homogenization.HighContrast (IsSkewMat bigLambdaRef blockContrast
  exists_matLoewnerLE_smul_one schurSigma schurSigmaStar schurSkew skewCorrectedForm)
namespace Homogenization.HighContrast

noncomputable section

variable {d : ℕ}

/-! ## Coercivity of a positive quadratic form -/

private theorem vecNormSq_smul_eq (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  show vecDot (c • x) (c • x) = c ^ 2 * vecDot x x
  rw [vecDot_smul_left, vecDot_smul_right]
  ring

private theorem quadForm_smul_vec (c : ℝ) (M : Mat d) (x : Vec d) :
    vecDot (c • x) (matVecMul M (c • x)) = c ^ 2 * vecDot x (matVecMul M x) := by
  rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  ring

private theorem eq_zero_of_vecNormSq_eq_zero {x : Vec d} (h : vecNormSq x = 0) : x = 0 := by
  funext i
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin d)), 0 ≤ x j * x j :=
    fun j _ => mul_self_nonneg (x j)
  exact mul_self_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 h i (Finset.mem_univ i))

private theorem vecNormSq_zero_vec : vecNormSq (0 : Vec d) = 0 := by
  show vecDot (0 : Vec d) (0 : Vec d) = 0
  simp [vecDot]

private theorem continuous_vecNormSq_fun : Continuous (vecNormSq : Vec d → ℝ) := by
  show Continuous fun x : Vec d => ∑ i, x i * x i
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i)

/-- A quadratic form depends continuously on a continuously varying matrix. -/
private theorem continuous_quadForm_comp {X : Type*} [TopologicalSpace X] {F : X → Mat d}
    (hF : Continuous F) (x : Vec d) :
    Continuous fun p : X => vecDot x (matVecMul (F p) x) := by
  show Continuous fun p : X => ∑ i, x i * ∑ j, F p i j * x j
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_finsetSum _ fun j _ =>
      (hF.matrix_elem i j).mul continuous_const)

/-! ## The quadratic form of the skew-corrected Schur form -/

private theorem matVecMul_smul_one_vec (t : ℝ) (x : Vec d) :
    matVecMul (t • (1 : Mat d)) x = t • x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq, mul_comm]

private theorem quadForm_smul_mat (t : ℝ) (A : Mat d) (x : Vec d) :
    vecDot x (matVecMul (t • A) x) = t * vecDot x (matVecMul A x) := by
  simp only [vecDot, matVecMul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem quadForm_le_of_smul_one {M : Mat d} {b : ℝ}
    (h : MatLoewnerLE M (b • (1 : Mat d))) (x : Vec d) :
    vecDot x (matVecMul M x) ≤ b * vecNormSq x := by
  have h1 := h x
  rw [matVecMul_smul_one_vec, vecDot_smul_right, show vecDot x x = vecNormSq x from rfl] at h1
  linarith only [h1]

private theorem quadForm_mono_of_matLoewnerLE {A B : Mat d} (h : MatLoewnerLE A B) (x : Vec d) :
    vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x) := by
  have h1 := h x
  linarith only [h1]

private theorem matLoewnerLE_of_quadForm_le {A B : Mat d}
    (h : ∀ x : Vec d, vecDot x (matVecMul A x) ≤ vecDot x (matVecMul B x)) :
    MatLoewnerLE A B := fun x => by
  have h1 := h x
  linarith only [h1]

/-- The quadratic form of the skew-corrected Schur form is the Schur part plus the
correction carried by the lower-right block. -/
private theorem quadForm_skewCorrectedForm (H : BlockMat d) (h : Mat d) (x : Vec d) :
    vecDot x (matVecMul (skewCorrectedForm H h) x) =
      vecDot x (matVecMul (schurSigma H) x) +
        vecDot (matVecMul (schurSkew H - h) x)
          (matVecMul H.lowerRight (matVecMul (schurSkew H - h) x)) := by
  rw [skewCorrectedForm, add_matVecMul, vecDot_add_right]
  congr 1
  rw [mul_assoc, ← matVecMul_mul, vecDot_matVecMul_transpose, matVecMul_mul]

/-! ## The admissible skew matrices form a compact set -/

private theorem matVecMul_single_col (D : Mat d) (j : Fin d) :
    matVecMul D (Pi.single j (1 : ℝ)) = fun i => D i j := by
  funext i
  simp [matVecMul, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

private theorem vecNormSq_single_one (j : Fin d) : vecNormSq (Pi.single j (1 : ℝ)) = 1 := by
  show vecDot _ _ = 1
  simp [vecDot, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

private theorem abs_entry_le_absEntrySum (A : Mat d) (i j : Fin d) :
    |A i j| ≤ ∑ p : Fin d, ∑ q : Fin d, |A p q| := by
  refine le_trans ?_
    (Finset.single_le_sum (f := fun p : Fin d => ∑ q : Fin d, |A p q|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun q : Fin d => |A i q|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

/-- Coercivity of the lower-right block converts a bound on the correction term into a
bound on the entries of the correcting matrix. -/
private theorem abs_entry_le_sqrt_of_quadForm_le {H : BlockMat d} {lam c0 : ℝ}
    (hlam : 0 < lam) (hc0 : 0 ≤ c0)
    (hcoer : ∀ y : Vec d, lam * vecNormSq y ≤ vecDot y (matVecMul H.lowerRight y))
    (D : Mat d) (i j : Fin d)
    (hcorr : vecDot (matVecMul D (Pi.single j (1 : ℝ)))
        (matVecMul H.lowerRight (matVecMul D (Pi.single j (1 : ℝ)))) ≤ c0) :
    |D i j| ≤ Real.sqrt (c0 / lam) := by
  have hquot : 0 ≤ c0 / lam := div_nonneg hc0 hlam.le
  have hnorm : vecNormSq (matVecMul D (Pi.single j (1 : ℝ))) ≤ c0 / lam := by
    have hchain := (hcoer (matVecMul D (Pi.single j (1 : ℝ)))).trans hcorr
    rw [le_div_iff₀ hlam, mul_comm]
    exact hchain
  have hentry : (D i j) ^ 2 ≤ c0 / lam := by
    have hDe : matVecMul D (Pi.single j (1 : ℝ)) i = D i j :=
      congrFun (matVecMul_single_col D j) i
    have hsq := sq_apply_le_vecNormSq (matVecMul D (Pi.single j (1 : ℝ))) i
    rw [hDe] at hsq
    exact hsq.trans hnorm
  refine abs_le_of_sq_le_sq ?_ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hquot]
  exact hentry

/-- **The sublevel sets are bounded.**  When the lower-right block is coercive, the skew
matrices obeying a fixed Loewner bound on the skew-corrected Schur form have uniformly
bounded entries. -/
private theorem exists_entry_bound_of_matLoewnerLE {H : BlockMat d} {N : Mat d} {t lam : ℝ}
    (ht : 0 ≤ t) (hlam : 0 < lam)
    (hcoer : ∀ y : Vec d, lam * vecNormSq y ≤ vecDot y (matVecMul H.lowerRight y)) :
    ∃ C : ℝ, ∀ h : Mat d,
      MatLoewnerLE (skewCorrectedForm H h) (t • N) → ∀ i j, h i j ∈ Set.Icc (-C) C := by
  classical
  obtain ⟨bN, hbN0, hbN⟩ := exists_matLoewnerLE_smul_one N
  obtain ⟨bS, hbS0, hbS⟩ := exists_matLoewnerLE_smul_one (-(schurSigma H))
  have hc0 : (0 : ℝ) ≤ t * bN + bS := by positivity
  refine ⟨(∑ p : Fin d, ∑ q : Fin d, |schurSkew H p q|) +
    Real.sqrt ((t * bN + bS) / lam), fun h hle i j => ?_⟩
  have hsplit := quadForm_skewCorrectedForm H h (Pi.single j (1 : ℝ))
  have hupper : vecDot (Pi.single j (1 : ℝ))
      (matVecMul (skewCorrectedForm H h) (Pi.single j (1 : ℝ))) ≤ t * bN := by
    refine (quadForm_mono_of_matLoewnerLE hle _).trans ?_
    rw [quadForm_smul_mat]
    have hN := quadForm_le_of_smul_one hbN (Pi.single j (1 : ℝ))
    rw [vecNormSq_single_one, mul_one] at hN
    exact mul_le_mul_of_nonneg_left hN ht
  have hlower : -(vecDot (Pi.single j (1 : ℝ))
      (matVecMul (schurSigma H) (Pi.single j (1 : ℝ)))) ≤ bS := by
    have hS := quadForm_le_of_smul_one hbS (Pi.single j (1 : ℝ))
    rw [vecNormSq_single_one, mul_one, neg_matVecMul, vecDot_neg_right] at hS
    exact hS
  have hcorr : vecDot (matVecMul (schurSkew H - h) (Pi.single j (1 : ℝ)))
      (matVecMul H.lowerRight (matVecMul (schurSkew H - h) (Pi.single j (1 : ℝ)))) ≤
      t * bN + bS := by
    linarith only [hsplit, hupper, hlower]
  have habsD := abs_entry_le_sqrt_of_quadForm_le hlam hc0 hcoer (schurSkew H - h) i j hcorr
  have habsk : |schurSkew H i j| ≤ ∑ p : Fin d, ∑ q : Fin d, |schurSkew H p q| :=
    abs_entry_le_absEntrySum _ i j
  have hhij : h i j = schurSkew H i j - (schurSkew H - h) i j := by simp
  rw [Set.mem_Icc]
  refine abs_le.1 ?_
  rw [hhij]
  exact (abs_sub _ _).trans (add_le_add habsk habsD)

/-! ## Attainment -/

/-! ## The printed minima -/

private theorem matVecMul_one_vec (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem coercivity_one :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ x : Vec d, lam * vecNormSq x ≤ vecDot x (matVecMul (1 : Mat d) x) := by
  refine ⟨1, one_pos, fun x => ?_⟩
  rw [matVecMul_one_vec, one_mul]
  exact le_of_eq rfl

private theorem bigLambdaRef_eq_sInf_form (E : BlockMat d) :
    bigLambdaRef E = sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm E h) (t • (1 : Mat d))} := rfl

private theorem blockContrast_eq_sInf_form (H : BlockMat d) :
    blockContrast H = sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
      MatLoewnerLE (skewCorrectedForm H h) (t • schurSigmaStar H)} := rfl

end

end Homogenization.HighContrast
