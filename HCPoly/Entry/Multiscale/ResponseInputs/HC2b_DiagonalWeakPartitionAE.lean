import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm

/-!
# Averaging over an almost-everywhere finite partition

`h6a_average_over_partition` proves the partition identity for an exact cover
`U = ⋃ w ∈ Z, V w`.  The cells produced by the adapted grid are open, so they meet their
parent cell only up to the grid seams, a Lebesgue-null set; the exact cover is therefore
not available.  This file restates the identity for an almost-everywhere cover: `U` and the
disjoint union of the `V w` agree up to a null set, and the integral over `U` may be
replaced by the integral over that union.

The identity survives `volume (V w) = 0` for no `w ∈ Z`: `hvolw` with `hUpos` and
`Z.card > 0` gives `(volume (V w)).toReal = (volume U).toReal / |Z| > 0`, so every cell
has nonzero (and, in particular, non-infinite) volume and `volumeAverage` never divides by
zero.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **Averaging over an almost-everywhere finite equal-volume partition.**  If the
measurable sets `V w` (`w ∈ Z`) are pairwise disjoint and contained in `U`, if `U`
differs from their union by a null set, and if every cell has the same volume
`|V w| = |U| / |Z|` (stated in `toReal` form), then for any `g` integrable on `U`
the flat average over `Z` of the cell averages `⨍_{V w} g` equals the average
`⨍_U g`:

  `|Z|⁻¹ ∑_{w ∈ Z} ⨍_{V w} g = ⨍_U g`.

The null-set hypothesis is what the open adapted cells supply: they cover the parent
only up to the grid seams.  The integral over `U` is transferred to the union with
`setIntegral_congr_set`, whose two sides have the same restricted measure; the union is
then split with `integral_biUnion_finset` exactly as in the exact-cover statement. -/
theorem h6a_average_over_aePartition {iota : Type*} (Z : Finset iota) (V : iota → Set (Vec d))
    (U : Set (Vec d)) (g : Vec d → ℝ)
    (hmeas : ∀ w ∈ Z, MeasurableSet (V w))
    (hdisj : ∀ w ∈ Z, ∀ w' ∈ Z, w ≠ w' → Disjoint (V w) (V w'))
    (hsub : ∀ w ∈ Z, V w ⊆ U)
    (hnull : volume (U \ ⋃ w ∈ Z, V w) = 0)
    (hvolw : ∀ w ∈ Z, ((Z.card : ℝ)) * (volume (V w)).toReal = (volume U).toReal)
    (hint : IntegrableOn g U)
    (hUpos : 0 < (volume U).toReal) (hUfin : volume U ≠ ⊤) (hZ : Z.Nonempty) :
    (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, volumeAverage (V w) g = volumeAverage U g := by
  classical
  have hUpos' : 0 < (volume U).toReal := hUpos
  have hUtop : volume U ≠ ⊤ := hUfin
  have hZpos : (0 : ℝ) < (Z.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hZ)
  have hdisj' : Set.Pairwise (↑Z : Set iota) (Function.onFun Disjoint V) := by
    intro a ha b hb hab
    exact hdisj a ha b hb hab
  have hVint : ∀ w ∈ Z, IntegrableOn g (V w) :=
    fun w hw => hint.mono_set (hsub w hw)
  have hsubU : (⋃ w ∈ Z, V w) ⊆ U := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨w, hw, hxw⟩
    exact hsub w hw hxw
  have hU_ae : U =ᵐ[volume] ⋃ w ∈ Z, V w := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨hnull, by rw [Set.sdiff_eq_empty.mpr hsubU]; simp⟩
  have hInt : ∫ x in U, g x = ∑ w ∈ Z, ∫ x in V w, g x := by
    calc ∫ x in U, g x
        = ∫ x in ⋃ w ∈ Z, V w, g x := MeasureTheory.setIntegral_congr_set hU_ae
      _ = ∑ w ∈ Z, ∫ x in V w, g x :=
          MeasureTheory.integral_biUnion_finset Z hmeas hdisj' hVint
  have hcell : ∀ w ∈ Z, volumeAverage (V w) g =
      (Z.card : ℝ) * (volume U).toReal⁻¹ * ∫ x in V w, g x := by
    intro w hw
    have hvolw' : (volume (V w)).toReal = (volume U).toReal / (Z.card : ℝ) := by
      rw [eq_div_iff (ne_of_gt hZpos), mul_comm]
      exact hvolw w hw
    rw [volumeAverage, hvolw', div_eq_mul_inv, mul_inv, inv_inv]
    ring
  have hsum : ∑ w ∈ Z, volumeAverage (V w) g =
      (Z.card : ℝ) * (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x := by
    calc ∑ w ∈ Z, volumeAverage (V w) g
        = ∑ w ∈ Z, (Z.card : ℝ) * (volume U).toReal⁻¹ * ∫ x in V w, g x :=
          Finset.sum_congr rfl (fun w hw => hcell w hw)
      _ = (Z.card : ℝ) * (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x := by
          rw [Finset.mul_sum]
  have hcancel : (Z.card : ℝ)⁻¹ *
        ((Z.card : ℝ) * (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x) =
      (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x := by
    have hc0 : (Z.card : ℝ) ≠ 0 := ne_of_gt hZpos
    calc (Z.card : ℝ)⁻¹ *
          ((Z.card : ℝ) * (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x)
        = ((Z.card : ℝ)⁻¹ * (Z.card : ℝ)) *
            ((volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x) := by ring
      _ = (volume U).toReal⁻¹ * ∑ w ∈ Z, ∫ x in V w, g x := by
            rw [inv_mul_cancel₀ hc0, one_mul]
  rw [volumeAverage, hInt, hsum]
  exact hcancel

end

end Homogenization.HighContrast.Multiscale

