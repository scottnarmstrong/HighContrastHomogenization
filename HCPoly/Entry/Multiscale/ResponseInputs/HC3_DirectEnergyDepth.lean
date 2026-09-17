import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPartitionAverage
import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Ellipticity

/-!
# The annealed flat average of the descendant cell energies

The descendant sum of `p.response.transfer` pairs each descendant cell average of the terminal
optimizer state with the annealed mean, and the Fenchel probe leaves behind the cell energy
`⨍_V ⟨∇u_t, S ∇u_t⟩`.  Its flat average over the depth-`m` triadic subdivision of the terminal
cell is the terminal cell energy (exact partition averaging), and for the maximizer the terminal
cell energy is twice the response:

```
⨍_{U_t} ⟨∇u_t, S ∇u_t⟩ = 2 J(U_t, p, q^∓ ; a_∓).
```

Taking expectations, the annealed flat average of twice the half cell energies is exactly
`2 E[J_t^∓]`, the scalar deficit the descendant row consumes.  Paper: `p.response.transfer`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **Response integrability data for an almost-everywhere elliptic coefficient.**  If `b` is
a.e. equal on `V` to a coefficient `f` that is pointwise elliptic on `V`, then the four pairings
of the response identity are integrable for `b`.  Each `L²`/`L¹` statement for `f` is transported
across the a.e. equality. -/
private theorem responseLinearIntegrabilityData_of_aeEq
    {d : ℕ} {V : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn V)]
    {b f : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam V f) (hbf : b =ᵐ[volumeMeasureOn V] f) :
    ResponseLinearIntegrabilityData V b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u φ
    have hfluxf : MemVectorL2 V (fun x => matVecMul (f x) (u.toH1.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
    have hae : (fun x => matVecMul (f x) (u.toH1.grad x)) =ᵐ[volumeMeasureOn V]
        (fun x => matVecMul (b x) (u.toH1.grad x)) := by
      filter_upwards [hbf] with x hx
      rw [hx]
    have hfluxb : MemVectorL2 V (fun x => matVecMul (b x) (u.toH1.grad x)) :=
      (MeasureTheory.memLp_congr_ae hae).mp hfluxf
    exact integrableOn_vecDot_of_memVectorL2 hfluxb φ.toH1Function.grad_memVectorL2
  · intro p u
    exact CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 p
      u.toH1.grad_memVectorL2
  · intro p u
    have hfluxf : MemVectorL2 V (fun x => matVecMul (f x) (u.toH1.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
    have hae : (fun x => matVecMul (f x) (u.toH1.grad x)) =ᵐ[volumeMeasureOn V]
        (fun x => matVecMul (b x) (u.toH1.grad x)) := by
      filter_upwards [hbf] with x hx
      rw [hx]
    have hfluxb : MemVectorL2 V (fun x => matVecMul (b x) (u.toH1.grad x)) :=
      (MeasureTheory.memLp_congr_ae hae).mp hfluxf
    exact CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 p hfluxb
  · intro u w
    have huf : MemVectorL2 V (fun x => matVecMul (symmPart (f x)) (u.toH1.grad x)) :=
      memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
    have hae : (fun x => matVecMul (symmPart (f x)) (u.toH1.grad x)) =ᵐ[volumeMeasureOn V]
        (fun x => matVecMul (symmPart (b x)) (u.toH1.grad x)) := by
      filter_upwards [hbf] with x hx
      rw [hx]
    have hub : MemVectorL2 V (fun x => matVecMul (symmPart (b x)) (u.toH1.grad x)) :=
      (MeasureTheory.memLp_congr_ae hae).mp huf
    exact integrableOn_vecDot_of_memVectorL2 w.toH1.grad_memVectorL2 hub

/-- **Integrability data of the recentred sample `a_- = a - g` on the terminal cell.**  The
sample is an a.e. class; its ellipticity is supplied on the cell by an a.e.-equal elliptic
representative, and the four response pairings are transported to it. -/
private theorem responseLinearIntegrabilityData_respCell_respCoeffMinus
    {d : ℕ} [NeZero d] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hq : IsUnit (respGrid jStar F)) (a : CoeffSpace d) :
    ResponseLinearIntegrabilityData (respCell jStar F t) (respCoeffMinus F a) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted (respGrid jStar F) hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  have hEll' := isEllipticFieldOn_sub_skew hEll (respg F) (respg_isSkew F)
  have hae' : respCoeffMinus F a =ᵐ[volumeMeasureOn (respCell jStar F t)]
      (fun x => f x - respg F) := by
    refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffMinus, hx]
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
      adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  exact responseLinearIntegrabilityData_of_aeEq hEll' hae'

/-- **Integrability data of the adjoint recentred sample `a_+ = a^t + g` on the terminal cell.**
The transposed twin of `responseLinearIntegrabilityData_respCell_respCoeffMinus`. -/
private theorem responseLinearIntegrabilityData_respCell_respCoeffPlus
    {d : ℕ} [NeZero d] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hq : IsUnit (respGrid jStar F)) (a : CoeffSpace d) :
    ResponseLinearIntegrabilityData (respCell jStar F t) (respCoeffPlus F a) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted (respGrid jStar F) hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  have hEll' := isEllipticFieldOn_transpose_add_skew hEll (respg F) (respg_isSkew F)
  have hae' : respCoeffPlus F a =ᵐ[volumeMeasureOn (respCell jStar F t)]
      (fun x => matTranspose (f x) + respg F) := by
    refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffPlus, hx]
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
      adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  exact responseLinearIntegrabilityData_of_aeEq hEll' hae'

/-- **The annealed flat average of the descendant cell energies is twice the annealed terminal
response, minus sign.**  Exact partition averaging collapses the flat average of the depth-`m`
cell energies to the terminal cell energy, and the quadratic-response identity identifies the
latter with twice `J_t^-`. -/
theorem integral_avsum_two_mul_halfEnergy_eq_respEJMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (m : ℕ) (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    (∫ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) ∂P)
      = 2 * respEJMinus P jStar F t e := by
  have hpoint : ∀ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) := by
    intro a
    have hInt : ResponseLinearIntegrabilityData (respCell jStar F t) (respCoeffMinus F a) :=
      responseLinearIntegrabilityData_respCell_respCoeffMinus jStar F t hq a
    have henergy := responseJ_energy_of_isResponseMaximizer (respCell jStar F t)
      (respCoeffMinus F a) (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (uM a) (hmax a) (hInt.weakFlux (uM a))
      (hInt.response (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      (hInt.firstVariation (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (uM a) (uM a)) (hEint a)
    have hsum : (∑ W ∈ triadicIndexBox d m,
          2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))))
        = ∑ W ∈ triadicIndexBox d m,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
      refine Finset.sum_congr rfl ?_
      intro W _
      ring
    rw [hsum, avsum_volumeAverage_eq (respGrid jStar F) hq t m (hEint a)]
    simp only [respJ, respCell] at henergy ⊢
    rw [henergy]
    ring
  have hconst : (∫ a, 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
      = 2 * ∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P := by
    simpa only [smul_eq_mul] using (hJ.integral_smul (2 : ℝ))
  rw [respEJMinus, ← hconst]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- **The annealed flat average of the descendant cell energies is twice the annealed terminal
response, plus sign.**  The adjoint twin of
`integral_avsum_two_mul_halfEnergy_eq_respEJMinus`. -/
theorem integral_avsum_two_mul_halfEnergy_eq_respEJPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (m : ℕ) (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    (∫ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) ∂P)
      = 2 * respEJPlus P jStar F t e := by
  have hpoint : ∀ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) := by
    intro a
    have hInt : ResponseLinearIntegrabilityData (respCell jStar F t) (respCoeffPlus F a) :=
      responseLinearIntegrabilityData_respCell_respCoeffPlus jStar F t hq a
    have henergy := responseJ_energy_of_isResponseMaximizer (respCell jStar F t)
      (respCoeffPlus F a) (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
      (uP a) (hmax a) (hInt.weakFlux (uP a))
      (hInt.response (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (hInt.firstVariation (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (uP a) (uP a)) (hEint a)
    have hsum : (∑ W ∈ triadicIndexBox d m,
          2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))))
        = ∑ W ∈ triadicIndexBox d m,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
      refine Finset.sum_congr rfl ?_
      intro W _
      ring
    rw [hsum, avsum_volumeAverage_eq (respGrid jStar F) hq t m (hEint a)]
    simp only [respJ, respCell] at henergy ⊢
    rw [henergy]
    ring
  have hconst : (∫ a, 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
      = 2 * ∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P := by
    simpa only [smul_eq_mul] using (hJ.integral_smul (2 : ℝ))
  rw [respEJPlus, ← hconst]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)

end

end Homogenization.HighContrast.Multiscale
