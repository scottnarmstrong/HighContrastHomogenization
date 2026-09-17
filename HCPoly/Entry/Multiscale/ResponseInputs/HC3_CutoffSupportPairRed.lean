import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportPathFinal

/-!
# Integrability of the cutoff pairing, reduced to its measurability

The pathwise cutoff pairing bound `e.response.cutoff.estimate` (`AK.HC` Lemma A.1, (A.4)) dominates
the absolute cutoff pairing, sample by sample, by a fixed multiple of the scale-weighted squared
scale-average seminorm of the `M_0 ^ (1/2)`-transported recentred optimizer state.  Consequently the
pairing is integrable over the law as soon as it is measurable and that seminorm square is
integrable, which isolates measurability as the only remaining obstruction to the integrability
premise of the cutoff rows.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cutoff pairing is `P`-integrable whenever it is `P`-a.e.-strongly measurable and the
scale-weighted squared scale-average seminorm of the `M_0 ^ (1/2)`-scaled recentred optimizer state
is `P`-integrable.  The pathwise bound `e.response.cutoff.estimate` (`AK.HC` Lemma A.1, (A.4))
dominates the absolute pairing by a fixed multiple of that seminorm square, so the finite-integral
half of `Integrable` follows by domination, while the measurability half is supplied as the
hypothesis.  The elliptic-representative hypothesis on the coefficient family is exactly the
hypothesis consumed by the pathwise bound, and no further regularity of the pairing is required. -/
theorem integrable_abs_pairing_of_measurable_of_integrable_besov {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (φ : Vec d → ℝ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (hm : (explicitCanonicalMetric F).PosDef)
    (c : CoeffSpace d → CoeffField d)
    (hc : ∀ a, ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        c a =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (Y : BlockVec d) (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (hmeas : AEStronglyMeasurable (fun a => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (c a) (u a) x).1 - Y.1)
          ((optimizerField (c a) (u a) x).2 - Y.2))|) P)
    (hbesov : Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P) :
    Integrable (fun a => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (c a) (u a) x).1 - Y.1)
          ((optimizerField (c a) (u a) x).2 - Y.2))|) P := by
  obtain ⟨C₀, _, hpath⟩ := exists_pathwise_cutoff_pairing_bound d
  refine ⟨hmeas, HasFiniteIntegral.mono'
    (((hbesov.const_mul ((3 : ℝ) ^ (-(t : ℝ)))).const_mul C₀).hasFiniteIntegral) ?_⟩
  filter_upwards with a
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  exact hpath jStar F t φ hjStar hφ hm (c a) Y (u a) (hc a)

end

end Homogenization.HighContrast.Multiscale
