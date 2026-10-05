/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.UniformG
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Sobolev

/-!
# Global `W^{1,p}` estimate: final algebra and containment in a cube

* `p13_final_alg`: the algebra combining the summed estimate with the Poincare inequality, the energy
  bound and the Holder inequality from `L^p` to `L²`.
* `p13_subset_axisCube`, `p13_volume_axisCube`: a set of diameter `D` lies in an axis cube of side
  `2 (D + t)`, whose volume is the `d`-th power of the side.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The final algebra of the global estimate. -/
theorem p13_final_alg {Tg Eg Ep E2 EF Λ Li W Nh Nq : ℝ≥0∞} {A Q dd Z Y Nr : ℝ}
    (hA : 0 ≤ A) (hdd : 0 ≤ dd) (hZ : 0 ≤ Z) (hY : 0 ≤ Y) (hNr : 0 ≤ Nr)
    (h1 : Tg ≤ 4 * (ENNReal.ofReal A * Λ * Nh * Eg + ENNReal.ofReal A * (Λ * Li) * Nh * Ep +
      ENNReal.ofReal A * Nq * EF))
    (hNh : Nh ≤ ENNReal.ofReal Nr) (hNq : Nq ≤ ENNReal.ofReal Nr)
    (h2 : Ep ≤ ENNReal.ofReal Q * Eg) (h3 : Eg ≤ ENNReal.ofReal dd * E2) (h4 : E2 ≤ W * EF)
    (h5 : Λ * W ≤ ENNReal.ofReal Z) (h6 : Li * ENNReal.ofReal Q ≤ ENNReal.ofReal Y) :
    Tg ≤ ENNReal.ofReal (4 * A * Nr * (Z * dd * (1 + Y) + 1)) * EF := by
  set G : ℝ≥0∞ := ENNReal.ofReal A * ENNReal.ofReal Nr with hG
  have t1 : ENNReal.ofReal A * Λ * Nh * Eg ≤ G * (Λ * Eg) := by
    calc ENNReal.ofReal A * Λ * Nh * Eg = ENNReal.ofReal A * Nh * (Λ * Eg) := by ring
      _ ≤ G * (Λ * Eg) := mul_le_mul_left (mul_le_mul_right hNh _) _
  have t2 : ENNReal.ofReal A * (Λ * Li) * Nh * Ep ≤ G * (Λ * ENNReal.ofReal Y * Eg) := by
    calc ENNReal.ofReal A * (Λ * Li) * Nh * Ep
        ≤ ENNReal.ofReal A * (Λ * Li) * Nh * (ENNReal.ofReal Q * Eg) := mul_le_mul_right h2 _
      _ = ENNReal.ofReal A * Nh * (Λ * (Li * ENNReal.ofReal Q) * Eg) := by ring
      _ ≤ G * (Λ * ENNReal.ofReal Y * Eg) :=
          mul_le_mul' (mul_le_mul_right hNh _) (mul_le_mul_left (mul_le_mul_right h6 _) _)
  have t3 : ENNReal.ofReal A * Nq * EF ≤ G * EF :=
    mul_le_mul_left (mul_le_mul_right hNq _) _
  have t4 : Λ * Eg ≤ ENNReal.ofReal dd * ENNReal.ofReal Z * EF := by
    calc Λ * Eg ≤ Λ * (ENNReal.ofReal dd * (W * EF)) :=
          mul_le_mul_right (h3.trans (mul_le_mul_right h4 _)) _
      _ = ENNReal.ofReal dd * ((Λ * W) * EF) := by ring
      _ ≤ ENNReal.ofReal dd * (ENNReal.ofReal Z * EF) :=
          mul_le_mul_right (mul_le_mul_left h5 _) _
      _ = _ := by ring
  have hY1 : Λ * ENNReal.ofReal Y * Eg = ENNReal.ofReal Y * (Λ * Eg) := by ring
  have tsum3 : G * (Λ * Eg) + G * (Λ * ENNReal.ofReal Y * Eg) + G * EF ≤
      G * (ENNReal.ofReal dd * ENNReal.ofReal Z * EF * (1 + ENNReal.ofReal Y) + EF) := by
    calc G * (Λ * Eg) + G * (Λ * ENNReal.ofReal Y * Eg) + G * EF
        = G * ((Λ * Eg) * (1 + ENNReal.ofReal Y) + EF) := by rw [hY1]; ring
      _ ≤ _ := mul_le_mul_right (add_le_add_left (mul_le_mul_left t4 _) _) _
  have hC : ENNReal.ofReal (4 * A * Nr * (Z * dd * (1 + Y) + 1)) * EF =
      4 * (G * (ENNReal.ofReal dd * ENNReal.ofReal Z * EF * (1 + ENNReal.ofReal Y) + EF)) := by
    have e1 : ENNReal.ofReal (Z * dd * (1 + Y) + 1) =
        ENNReal.ofReal Z * ENNReal.ofReal dd * (1 + ENNReal.ofReal Y) + 1 := by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul hZ, ENNReal.ofReal_add zero_le_one hY, ENNReal.ofReal_one]
    have e2 : ENNReal.ofReal (4 * A * Nr * (Z * dd * (1 + Y) + 1)) =
        4 * (ENNReal.ofReal A * ENNReal.ofReal Nr) * ENNReal.ofReal (Z * dd * (1 + Y) + 1) := by
      have e4 : ENNReal.ofReal (4 : ℝ) = 4 := by simp
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), e4]
      ring
    rw [e2, e1, hG]
    ring
  rw [hC]
  calc Tg ≤ 4 * (ENNReal.ofReal A * Λ * Nh * Eg + ENNReal.ofReal A * (Λ * Li) * Nh * Ep +
      ENNReal.ofReal A * Nq * EF) := h1
    _ ≤ 4 * (G * (Λ * Eg) + G * (Λ * ENNReal.ofReal Y * Eg) + G * EF) :=
        mul_le_mul_right (add_le_add (add_le_add t1 t2) t3) _
    _ ≤ _ := mul_le_mul_right tsum3 _

/-- A set of diameter at most `D` lies in an axis cube of side `2 (D + t)`. -/
theorem p13_subset_axisCube {U : Set (Vec d)} {D t : ℝ} (hD : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ D)
    {x₁ : Vec d} (hx₁ : x₁ ∈ U) (ht : 0 < t) :
    U ⊆ axisCube (fun i => x₁ i - (D + t)) (2 * (D + t)) := by
  intro x hx i _
  have h1 : |x i - x₁ i| ≤ D := by
    have := norm_le_pi_norm (x - x₁) i
    rw [Real.norm_eq_abs] at this
    exact (this.trans (hD x hx x₁ hx₁) :)
  have h2 := abs_le.1 h1
  simp only [Set.mem_Ioo]
  constructor <;> linarith only [h2.1, h2.2, ht]

theorem p13_volume_axisCube (z : Vec d) (L : ℝ) :
    volume (axisCube z L) = ENNReal.ofReal L ^ d := by
  have := measure_univ_axisCube z L
  rwa [Measure.restrict_apply_univ] at this

end SuperdiffusionCLT.Section7
