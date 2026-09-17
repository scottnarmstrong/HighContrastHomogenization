import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs
import HCPoly.Entry.Setup.BlockCalculus
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRowsShear
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRowsAdjointShear
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedSwarmH10

/-!
# The centred responses on the recentred blocks, in swap form

The two centred responses `Jtilde^-` and `Jtilde^+` of `e.response.cutoff.estimate` are defined
on the annealed block `E_t = respMean` at the skew-shifted loads.  The recentring shear
`G_g = ((1, 0), (g, 1))` of Step 4 carries that block to `Ehat_t^- = G_gᵀ E_t G_g`, and the
adjoint recentring carries the adjoint block to `Ehat_t^+ = G_{-g}ᵀ (D E_t D) G_{-g}`.  Under the
shear, the centred response is unchanged once the second load is shifted back by `g p`, so each
`Jtilde^±` is the centred response of the *recentred* block `Ehat_t^±` at the recentred load
`q^±`.  Because the reciprocal normalizations give `p. q^± = |e|^2 = 1`, the swap form of the
centred response then collapses each `Jtilde^±` to the closed expression
`-1/2 - (1/4) <Ehat_t^± x^±, R Ehat_t^± x^±>`.  Thus the centred response measures exactly the
failure of the recentred block to be reciprocal along its own load, and it vanishes precisely
when `(1/4) <Ehat x, R Ehat x> = -1/2`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The centred response `Jtilde^-(e)` of `e.response.cutoff.estimate` is the centred response
of the recentred block `Ehat_t^-` at the recentred load `q^-`: the shear congruence
`Ehat_t^- = G_gᵀ E_t G_g` acts on the doubled load by the triangular change of variables
`(X₁, X₂) ↦ (X₁, g X₁ + X₂)`, and since the centred response is shear-invariant the definition
of `respCenteredJMinus` on `E_t` at `(p, q - h_t p)` agrees with the response of `Ehat_t^-` at
`(p, q^-)` with `q^- = q + (g - h_t) p`. -/
theorem respCenteredJMinus_eq_blockCenteredResponse_respEhatMinus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    respCenteredJMinus P jStar F t e
      = blockCenteredResponse (respEhatMinus P jStar F t) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) := by
  rw [respCenteredJMinus, respEhatMinus, respG]
  rw [blockCenteredResponse_blockCongr_shear (respMean P jStar F t) (respg_isSkew F)
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)]
  congr 1
  rw [respqMinus, sub_matVecMul]
  abel

/-- The adjoint centred response `Jtilde^+(e)` of `e.response.cutoff.estimate` is the centred
response of the recentred adjoint block `Ehat_t^+` at the recentred load `q^+`.  The adjoint
recentred block is the `(-g)`-shear congruence `Ehat_t^+ = G_{-g}ᵀ (D E_t D) G_{-g}`, and the
centred response of that congruence at `(p, q^+)` is the response of the adjoint block at
`(p, q^+ + g p)`, which is the definition of `respCenteredJPlus` on the adjoint annealed block
at `(p, q + h_t p)`. -/
theorem respCenteredJPlus_eq_blockCenteredResponse_respEhatPlus {d : ℕ}
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d) :
    respCenteredJPlus P jStar F t e
      = blockCenteredResponse (respEhatPlus P jStar F t) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) := by
  rw [respCenteredJPlus, respEhatPlus_eq_blockCongr_shear]
  have hgneg : matTranspose (-(respg F)) = -(-(respg F)) := by
    have hT : matTranspose (-(respg F)) = -matTranspose (respg F) := by
      simp only [matTranspose, Matrix.transpose_neg]
    rw [hT, respg_isSkew F]
  rw [blockCenteredResponse_blockCongr_shear (blockAdjoint (respMean P jStar F t)) hgneg
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)]
  congr 1
  rw [respqPlus, sub_matVecMul, neg_matVecMul]
  abel

end

end Homogenization.HighContrast.Multiscale
