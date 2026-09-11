/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.TransportObjects

/-!
# Source-coefficient absorption for the two-grid bridge

The bridge source coefficient absorbs each ordered continued-plus-early
coefficient appearing in the four source-row alternatives.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

noncomputable section

/-- Each of the four ordered bridge coefficients is bounded by the common
bridge source coefficient. -/
theorem ordered_coefficients_le_bridgeSrcCoeff {d : ℕ} (Cd g : ℝ)
    (E : BlockMat d) (jStar : ℤ) (mq mq' : Mat d) :
    bridgeContCoeff Cd g E jStar mq mq' mq + bridgeEarlyCoeff Cd g E mq' mq ≤
        bridgeSrcCoeff Cd g E jStar mq mq' ∧
      bridgeContCoeff Cd g E jStar mq mq' mq' + bridgeEarlyCoeff Cd g E mq' mq' ≤
        bridgeSrcCoeff Cd g E jStar mq mq' ∧
      bridgeContCoeff Cd g E jStar mq' mq mq + bridgeEarlyCoeff Cd g E mq mq ≤
        bridgeSrcCoeff Cd g E jStar mq mq' ∧
      bridgeContCoeff Cd g E jStar mq' mq mq' + bridgeEarlyCoeff Cd g E mq mq' ≤
        bridgeSrcCoeff Cd g E jStar mq mq' := by
  let a :=
    bridgeContCoeff Cd g E jStar mq mq' mq + bridgeEarlyCoeff Cd g E mq' mq
  let b :=
    bridgeContCoeff Cd g E jStar mq mq' mq' + bridgeEarlyCoeff Cd g E mq' mq'
  let c :=
    bridgeContCoeff Cd g E jStar mq' mq mq + bridgeEarlyCoeff Cd g E mq mq
  let e :=
    bridgeContCoeff Cd g E jStar mq' mq mq' + bridgeEarlyCoeff Cd g E mq mq'
  change a ≤ 1 + max (max a b) (max c e) ∧
    b ≤ 1 + max (max a b) (max c e) ∧
    c ≤ 1 + max (max a b) (max c e) ∧
    e ≤ 1 + max (max a b) (max c e)
  have ha : a ≤ max (max a b) (max c e) :=
    le_trans (le_max_left a b) (le_max_left (max a b) (max c e))
  have hb : b ≤ max (max a b) (max c e) :=
    le_trans (le_max_right a b) (le_max_left (max a b) (max c e))
  have hc : c ≤ max (max a b) (max c e) :=
    le_trans (le_max_left c e) (le_max_right (max a b) (max c e))
  have he : e ≤ max (max a b) (max c e) :=
    le_trans (le_max_right c e) (le_max_right (max a b) (max c e))
  constructor
  · linarith only [ha]
  constructor
  · linarith only [hb]
  constructor
  · linarith only [hc]
  · linarith only [he]

end

end Bridge
end HighContrast
end Homogenization
