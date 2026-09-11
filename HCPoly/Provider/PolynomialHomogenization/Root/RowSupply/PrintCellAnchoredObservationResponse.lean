/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.RowSupply.DescendantHomogenizationErrorInfinityTwo
import Homogenization.Book.Ch02.Theorems.Dilation

/-!
# Cell-anchored observation response

The dimensionful response row uses the scale of the cube on which it is
evaluated.  With this normalization, restriction to a triadic descendant is
monotone: the growth in the scale-normalized homogenization error is exactly
cancelled by the change of the physical scale factor.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- The physical scale factor carried by the dimensionful Besov row. -/
noncomputable def printCellScaleFactor (Q : TriadicCube d) (s : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (s * (Q.scale : ℝ))

end

end RowSupply
end HighContrast
end Homogenization
