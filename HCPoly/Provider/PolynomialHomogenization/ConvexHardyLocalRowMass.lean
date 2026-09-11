/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.ConvexHardyLocalLayer
import HCPoly.Provider.PolynomialHomogenization.ConvexWhitneyGeometry

/-!
# Local mass of maximal Whitney rows

The identity-grid maximal filling has a local row estimate as well as its
global boundary-volume estimate.  At one scale, retain only those selected
cubes that meet a prescribed Euclidean ball.  The whole retained cubes lie in
a slightly larger Euclidean ball, while their escaping parents put them in a
common inner boundary layer.  Pairwise disjointness then turns the finite sum
of their volumes into the volume of their union.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

end

end HighContrast
end Homogenization
