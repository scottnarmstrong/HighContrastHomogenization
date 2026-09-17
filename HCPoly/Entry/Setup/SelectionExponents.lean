import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The fixed moment `Q` and the exponent `ρ_max`

`e.scale.selection.Q.choice`:

> Fix the even moment and set
> `Q := 2⌈2(d+1)/(1-γ)⌉` and `ρ_max := γ + (1/Q)(d + ¼(1-γ)) < 1`.

Both are formulas in the dimension `d` and the coarse-ellipticity exponent `γ`, and both are
transcribed literally.  Two things the display asserts are **not** part of either definition
and are not asserted here: that `ρ_max < 1`, and that `Q` is even (it is `2` times a natural
number by construction).  Each is a statement about these values and is proved
separately.

`⌈·⌉` is the ceiling into `ℕ`, so `Q : ℕ`: the print uses `Q` as a moment order and compares
it with integers (`h ≥ 2Q`).  For `γ ∈ [0,1)` — the standing range of the coarse-ellipticity
exponent — the argument `2(d+1)/(1-γ)` is positive and the ceiling into `ℕ` agrees with the
ceiling into `ℤ`.  Outside that range, `1 - γ ≤ 0` makes the quotient nonpositive or
undefined, but `Q` need not vanish; the printed hypothesis `γ ∈ [0,1)` stays with the
consumer.  The resulting totalized values have no printed interpretation outside that range.

The `¼(1-γ)` and `⅛(1-γ)` that appear in the histories, the drift and the profile are
written out at their use sites, exactly as the print does; the print gives them no name and
none is introduced here.

Equivalently, `ρ_max = γ + (d + a)/Q` with `a = ¼(1-γ)`; no symbol for this additive
exponent, and no separate exponent for the drift, occurs in the paper.
-/

namespace Homogenization.HighContrast

noncomputable section

/-- The fixed even moment `Q = 2⌈2(d+1)/(1-γ)⌉` of `e.scale.selection.Q.choice`. -/
def bigQ (d : ℕ) (γ : ℝ) : ℕ :=
  2 * ⌈2 * ((d : ℝ) + 1) / (1 - γ)⌉₊

/-- The exponent `ρ_max = γ + (1/Q)(d + ¼(1-γ))` of `e.scale.selection.Q.choice`. -/
def rhoMax (d : ℕ) (γ : ℝ) : ℝ :=
  γ + (bigQ d γ : ℝ)⁻¹ * ((d : ℝ) + (1 - γ) / 4)

end

end Homogenization.HighContrast
