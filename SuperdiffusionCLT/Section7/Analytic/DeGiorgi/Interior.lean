/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Iteration

/-!
# De Giorgi `L^∞–L²` bound for weak solutions in a cube

For an `H¹` weak solution `-∇·(a∇u) = f - ∇·g` in the open cube `Q = axisCube z L`, the level
identity for the truncations `(u-k)₊ η²` is the weak form tested with an `H¹₀(Q)` function
(`level_inequality_of_isWeakSolutionOn`), so the iteration `deGiorgi_eLpNorm_bound` applies.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **De Giorgi `L^∞–L²` bound in a cube, with right-hand side.**
`sup_{Q/2} u₊ ≤ C (Λ/λ)^N (L^{-d/2} ‖u₊‖_{L²(Q)} + L²/λ ‖f‖_∞ + L/λ ‖g‖_∞)`, with
`N = deGiorgiPower d`. -/
theorem deGiorgi_interior_bound (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {lam Lam : ℝ} {a : CoeffField d} (z : Vec d) {L : ℝ}, 0 < L →
      IsEllipticFieldOn lam Lam (axisCube z L) a →
      ∀ (f : Vec d → ℝ) (g : Vec d → Vec d),
        AEStronglyMeasurable g (volume.restrict (axisCube z L)) →
        ∀ (u : H1Function (axisCube z L)),
          IsWeakSolutionOn a (axisCube z L) u f g →
          eLpNorm (fun x => max (u.toFun x) 0) ⊤ (volume.restrict (halfCube z L)) ≤
            ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) *
              (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
                  eLpNorm (fun x => max (u.toFun x) 0) 2 (volume.restrict (axisCube z L)) +
                ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f ⊤ (volume.restrict (axisCube z L)) +
                ENNReal.ofReal (L / lam) *
                  eLpNorm (fun x => eucNorm (g x)) ⊤ (volume.restrict (axisCube z L))) := by
  obtain ⟨C, hC, hmain⟩ := deGiorgi_eLpNorm_bound hd
  refine ⟨C, hC, ?_⟩
  intro lam Lam a z L hL hEll f g hgm u hu
  exact hmain z hL hEll u f g hgm
    (fun k _ _ hη hηc hηs => level_inequality_of_isWeakSolutionOn z u f g hu k hη hηc hηs)

/-- Witness: the constant solution `1` of the identity-coefficient equation on the unit square
meets every non-law hypothesis of `deGiorgi_interior_bound`. -/
example : True := by
  obtain ⟨C, -, hmain⟩ := deGiorgi_interior_bound (d := 2) le_rfl
  have := hmain (lam := 1) (Lam := 1) (a := fun _ => (1 : Mat 2)) (0 : Vec 2) one_pos
    witness_ellipticField (fun _ => 0) (fun _ => 0) aestronglyMeasurable_const witnessOne
    witnessOne_weak
  trivial

end SuperdiffusionCLT.Section7
