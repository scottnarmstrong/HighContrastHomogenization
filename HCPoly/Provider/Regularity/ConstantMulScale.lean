/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Constant multiplication of a random scale

This module records the route-independent measurable and order API for
enlarging a real-valued random scale by a deterministic positive constant.
-/

namespace Homogenization
namespace HighContrast

/-- Multiply a real-valued scale by a constant chosen independently of the
sample. -/
def constantMulScale {Omega : Type*} (A : ℝ) (X : Omega → ℝ) : Omega → ℝ :=
  fun omega => A * X omega

/-- Constant multiplication preserves measurability of a random scale. -/
theorem Measurable.constantMulScale {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega → ℝ} (hX : Measurable X) (A : ℝ) :
    Measurable (constantMulScale A X) := by
  exact measurable_const.mul hX

end HighContrast
end Homogenization
