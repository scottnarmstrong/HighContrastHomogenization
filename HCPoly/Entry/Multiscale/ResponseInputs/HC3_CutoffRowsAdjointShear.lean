import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock

/-!
# The adjoint of a sheared block is the sheared adjoint

The recentring shear `G_g = [[Id, 0], [g, Id]]` and the flux flip `D = diag(Id, -Id)` form the
adjoint pair of the response decomposition.  Flipping the flux sign commutes with congruence by
`G_g` up to reversing the shear,

`D (G_gᵀ A G_g) D = G_{-g}ᵀ (D A D) G_{-g}`,

so the adjoint recentred block `Ehat_u^+` is the `(-g)`-shear congruence of the adjoint annealed
block, exactly as `Ehat_u^-` is the `g`-shear congruence of the annealed block itself.  This is the
algebraic identity that places the adjoint row of `e.response.cutoff.estimate` on the same footing
as the primal row of `p.response.transfer`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Flipping the flux sign commutes with congruence by the recentring shear up to reversing the
shear: `D (G_gᵀ A G_g) D = G_{-g}ᵀ (D A D) G_{-g}`, where `D = blockD d` and
`G_g = ⟨1, 0, g, 1⟩`. -/
theorem blockAdjoint_blockCongr_shear {d : ℕ} (A : BlockMat d) (g : Mat d) :
    blockAdjoint (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A)
      = blockCongr (⟨1, 0, -g, 1⟩ : BlockMat d) (blockAdjoint A) := by
  simp only [blockAdjoint, blockCongr_blockCongr, blockD_mul_shear_neg]

/-- The adjoint recentred block of `e.response.cutoff.estimate` is the `(-g)`-shear congruence of
the adjoint annealed block:
`Ehat_u^+ = G_{-g}ᵀ (D E_u D) G_{-g}`, the adjoint twin of the primal identity
`Ehat_u^- = G_gᵀ E_u G_g` used by `p.response.transfer`. -/
theorem respEhatPlus_eq_blockCongr_shear {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (u : ℤ) :
    respEhatPlus P jStar F u
      = blockCongr (⟨1, 0, -respg F, 1⟩ : BlockMat d) (blockAdjoint (respMean P jStar F u)) := by
  rw [respEhatPlus, respEhatMinus, respG]
  exact blockAdjoint_blockCongr_shear (respMean P jStar F u) (respg F)

end

end Homogenization.HighContrast.Multiscale
