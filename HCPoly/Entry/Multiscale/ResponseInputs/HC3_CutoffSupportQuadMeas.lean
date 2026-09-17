import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportCanPairMeas

/-!
# The quadratic readout of the canonical cutoff pairing

The cutoff pairing of `e.response.cutoff.estimate` is the volume average of the cutoff-weighted
Euclidean pairing of the potential and flux defects of the canonical optimizer state.  Its
integrand expands into one quadratic term and three linear terms (AK.HC Lemma A.1, (A.4)).  The
linear terms are measurable in the sample by `HC3_CutoffSupportCanPairMeas`; this file treats the
quadratic term,

`a ↦ volumeAverage (adaptedCell q t) (fun x => φ x * ⟨Z(a,x).1, Z(a,x).2⟩)`,

where `Z(a,·)` is the canonical optimizer state.

The second slot of the canonical optimizer state is the coefficient applied to the first, so the
block self-pairing of that state is twice the Euclidean pairing of the two slots.  The displayed
quadratic readout therefore reduces to the cutoff-weighted volume average of the block
self-pairing of the canonical optimizer state.  That volume average is the quadratic counterpart
of the linear readouts of `HC3_CutoffSupportCanPairMeas`, and its measurability is isolated here
as the exact hypothesis under which the display follows.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Pairing of a primal state -/

/-! ## The canonical optimizer state as a block state -/

/-- The canonical minus optimizer state of `e.response.cutoff.estimate`, packaged as a block
state so that it can be paired with the recentred coefficient. -/
def canonicalOptimizerStateMinus [NeZero d] (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (p r : Vec d) (a : CoeffSpace d) : BlockState d :=
  { potential := fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t)
      (canonicalRespCoeffMinusOn q hq t F a) p r x).1
    flux := fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t)
      (canonicalRespCoeffMinusOn q hq t F a) p r x).2 }

/-- The canonical plus optimizer state of `e.response.cutoff.estimate`, packaged as a block
state so that it can be paired with the recentred coefficient. -/
def canonicalOptimizerStatePlus [NeZero d] (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (p r : Vec d) (a : CoeffSpace d) : BlockState d :=
  { potential := fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t)
      (canonicalRespCoeffPlusOn q hq t F a) p r x).1
    flux := fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t)
      (canonicalRespCoeffPlusOn q hq t F a) p r x).2 }

/-- The block state packaged from the canonical minus optimizer state evaluates to that state. -/
@[simp] theorem canonicalOptimizerStateMinus_eval [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d) (a : CoeffSpace d)
    (x : Vec d) :
    (canonicalOptimizerStateMinus q hq t F p r a).eval x =
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r x :=
  rfl

/-- The block state packaged from the canonical plus optimizer state evaluates to that state. -/
@[simp] theorem canonicalOptimizerStatePlus_eval [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d) (a : CoeffSpace d)
    (x : Vec d) :
    (canonicalOptimizerStatePlus q hq t F p r a).eval x =
      canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r x :=
  rfl

/-! ## The almost-everywhere self-pairing identities -/

/-! ## Reduction of the quadratic readout to the block self-pairing -/

end

end Homogenization.HighContrast.Multiscale
