import HCPoly.Entry.SourceWhitney
import HCPoly.Entry.Source.CoarseSubadditivity
import HCPoly.Entry.Setup.UnitRange
import HCPoly.Entry.Multiscale.ResponseInputs.AdapterBasic
import HCPoly.Entry.Multiscale.ResponseInputs.AdapterGeometry
import HCPoly.Entry.Multiscale.ResponseInputs.AdapterSummation
import HCPoly.Entry.Multiscale.ResponseInputs.AdapterPartition
import HCPoly.Entry.Multiscale.ResponseInputs.AdapterForward
import HCPoly.Entry.Multiscale.ResponseInputs.AdapterReverse

/-!
# Response inputs — the analytic kernels

* E1/E2: HC Lemma 2.15, re-derived at the rounded grid
  `q = explicitRoundedGrid jStar m` with a `C(d,γ)` and every binder witnessed.  HC's
  `a.CFS` premise is unused by the proof; the fine-grid Euclidean adapter supplies the
  concentration input from the unit-range law.  Consumed at `p.response.transfer`,
  with the source term normalized by `p.response.transfer` (`𝐄 ≤ C(d,γ) Π 𝔢(m) 𝐀hom_{t,q}`, i.e.
  `adaptedMean_refBlock_normalization`) and the HC source factor `(1 + K² 3^{-t})^γ ≤ 2` absorbed into
  `Csrc` exactly as `adaptedMean_refBlock_normalization` absorbs it (`⌈Csrc log₃(2K)⌉ ≤ j_*`).
  Here `𝔢(m)² = ‖m‖‖m⁻¹‖`.
-/

open Homogenization.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale blockSub)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

/-- **E1** kernel: Euclidean-by-adapted comparison (HC's `e.Euc.by.tilt`, at the rounded grid;
`p.response.transfer`, first inequality): for `ℓ ≥ 1`,
`𝐀hom_{t+ℓ,Id} ≤ (1 + C Π ‖m‖‖m⁻¹‖ 3^{-ℓ}) 𝐀hom_{t,q}`.
Proof route (HC): use maximal adapted cells
capped at `t` to tile `□_{t+ℓ}` up to a null set. Integer stationarity identifies the cap
with `adaptedMean P q t`. Every lower row has relative volume `≤ C(d) 𝔢(m) 3^{j-(t+ℓ)}`
and is controlled by the source bound. Fine cells are recentered into the source window;
the inverse-norm bound two makes this source estimate independent of eccentricity.
The geometric series and `adaptedMean_refBlock_normalization` then give the result.
This uses only stationarity and dagger; the stated unit-range assumption is unnecessary. -/
theorem euclidean_le_adapted_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → IsUnitRangeLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (m : Mat d), m.PosDef →
            ∀ t : ℤ, (jStar : ℤ) ≤ t →
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) t ⊆
                HighContrast.centeredCube d (2 * (jStar : ℤ)) →
              ∀ ℓ : ℕ, 1 ≤ ℓ →
                BlockMatLoewnerLE (adaptedMean P (1 : Mat d) (t + (ℓ : ℤ)))
                  (blockScale (1 + C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(ℓ : ℝ)))
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m) t)) := by
  obtain ⟨Csrc, C, hCsrc, hC, h⟩ := Adapter.forward_comparison d hd γ hγ
  refine ⟨Csrc, C, hCsrc, hC, ?_⟩
  intro P hP E Ψ K S hstat _hunit hdag
  exact h P E Ψ K S hstat hdag

/-- **E2** kernel: adapted-by-Euclidean comparison (HC's `e.tilt.by.Euc`, at the rounded grid;
`p.response.transfer`, second inequality): for `ℓ, r ≥ 1`,
`𝐀hom_{t+ℓ+r,q} ≤ 𝐀hom_{t+ℓ,Id} + C Π ‖m‖‖m⁻¹‖ 3^{-r} 𝐀hom_{t,q}`.
Same route with the roles exchanged: tile `⋄^q_{t+ℓ+r}` by standard cells capped at `t+ℓ`.
Use stationarity on the cap and the annealed source bound on every lower row, whose volume
fraction is `≤ 12 d^{3/2} 3^{j-(t+ℓ+r)}`. Normalize at the original generation `t`.
The argument applies at every later generation without enlarging the source window.
The stated unit-range assumption is again unnecessary. -/
theorem adapted_le_euclidean_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → IsUnitRangeLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (m : Mat d), m.PosDef →
            ∀ t : ℤ, (jStar : ℤ) ≤ t →
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) t ⊆
                HighContrast.centeredCube d (2 * (jStar : ℤ)) →
              ∀ ℓ r : ℕ, 1 ≤ ℓ → 1 ≤ r →
                BlockMatLoewnerLE
                  (blockSub (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (t + (ℓ : ℤ) + (r : ℤ)))
                    (blockScale (C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) * (3 : ℝ) ^ (-(r : ℝ)))
                      (adaptedMean P (Geometry.explicitRoundedGrid jStar m) t)))
                  (adaptedMean P (1 : Mat d) (t + (ℓ : ℤ))) := by
  obtain ⟨Csrc, C, hCsrc, hC, h⟩ := Adapter.reverse_comparison d hd γ hγ
  refine ⟨Csrc, C, hCsrc, hC, ?_⟩
  intro P hP E Ψ K S hstat _hunit hdag
  exact h P E Ψ K S hstat hdag

end Homogenization.HighContrast.Multiscale
