/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import Homogenization.Sobolev.Foundations.EuclideanL2CZ
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# Cube norms of a vector field: `L̲^q(cu_M)` and the hatted `Ĥ̲^{-1}(cu_M)`

The paper defines the volume-normalized
norm `‖f‖_{L̲^p(U)} = (⨍_U |f|^p)^{1/p}`, where `|·|` is the Euclidean
magnitude. It defines the hatted negative seminorm at
order one by duality against smooth mean-zero test functions, and adds
the convention used by `l.abstract.response.fields`:

> When these hatted negative norms are applied to vector fields, the pairing is
> understood against gradients; for instance `‖F‖_{Ĥ̲^{-1}(U)}` is the supremum
> of `⨍_U F·∇g` over smooth mean-zero `g` with `‖∇g‖_{L̲²(U)} ≤ 1`.

That last sentence is the definition used in `e.abstract.response.ND.weak` and in
Step 4 of the proof of `l.abstract.response.fields`, so it is the one this
file supplies. At order one the constraint `[g]_{W̲^{1,2}(U)} ≤ 1` is
`‖∇g‖_{L̲²(U)} ≤ 1`, **not** the Gagliardo seminorm, which is the fractional
(`s < 1`) reading. No comparison between the two is asserted here.

## Relation to `Section2/Norms/NegativeHat.lean`

`Section2.Norms.matHatNegENorm` is the *matrix* seminorm at a *fractional*
order `s`, whose test class `IsHatTestField` constrains the Gagliardo
seminorm. This file is the *vector*, *order-one* companion; the two test
classes are different by design and neither is defined in terms of the other.

## Honesty of the value

**Both quantities are valued in `ℝ≥0∞` and `⊤` is a legitimate outcome.**
`vecCubeLpENorm` is an `eLpNorm`, and `vecHatNegENorm` is a supremum over a
nonempty family (the zero function is a test function), so no `Real.sSup` junk value occurs.
The pairing density is integrated with a Bochner integral, whose value on a
non-integrable function is `0`; `vecGradientPairingDensity_integrableOn` shows
that branch is unreachable for a continuous field paired with a smooth test
function.

## Main definitions

* `vecCubeLpENorm`: `‖F‖_{L̲^q(Q)}` for a `Vec d`-valued field, with the
  Euclidean magnitude.
* `IsVecHatTestField`: the test class of the hatted negative norm.
* `vecGradientPairingDensity`: the density `F·∇g`.
* `vecHatNegENorm`: `‖F‖_{Ĥ̲^{-1}(Q)}`.

## Main results

* `vecCubeLpENorm_add_le`, `vecCubeLpENorm_const_smul`, `vecCubeLpENorm_zero`,
  `vecCubeLpENorm_neg`: the norm laws.
* `vecGradientPairingDensity_eq_sum`: the density is `∑ i, F x i * ∂_i g x`.
* `le_vecHatNegENorm`, `vecHatNegENorm_le`: the supremum characterization.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The volume-normalized `L̲^q` norm of a vector field -/

/-- `‖F‖_{L̲^q(Q)}` for a `Vec d`-valued field, with the Euclidean
magnitude `|F(x)|`. The Euclidean magnitude is obtained by reading
the field in the `HilbertVec d` carrier, whose norm is exactly
`Homogenization.vecNorm`; the ambient `Vec d = Fin d → ℝ` carries the supremum
norm instead, which is not the manuscript's `|·|`. -/
noncomputable def vecCubeLpENorm (Q : TriadicCube d) (q : ℝ≥0∞)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  Section2.Norms.cubeLpENorm Q q (hilbertifyVecField F)

theorem norm_hilbertifyVecField_apply (F : Vec d → Vec d) (x : Vec d) :
    ‖hilbertifyVecField F x‖ = vecNorm (F x) :=
  rfl

@[simp] theorem vecCubeLpENorm_zero (Q : TriadicCube d) (q : ℝ≥0∞) :
    vecCubeLpENorm Q q (fun _ : Vec d => (0 : Vec d)) = 0 := by
  have h : hilbertifyVecField (fun _ : Vec d => (0 : Vec d))
      = (0 : Vec d → HilbertVec d) := by
    funext x
    exact map_zero (HilbertVec.linearEquivVec d).symm
  rw [vecCubeLpENorm, h, Section2.Norms.cubeLpENorm_zero]

theorem vecCubeLpENorm_neg (Q : TriadicCube d) (q : ℝ≥0∞) (F : Vec d → Vec d) :
    vecCubeLpENorm Q q (fun x => -F x) = vecCubeLpENorm Q q F := by
  have h : hilbertifyVecField (fun x => -F x) = -hilbertifyVecField F := by
    funext x
    exact map_neg (HilbertVec.linearEquivVec d).symm (F x)
  rw [vecCubeLpENorm, h, Section2.Norms.cubeLpENorm_neg, vecCubeLpENorm]

theorem vecCubeLpENorm_const_smul (Q : TriadicCube d) (q : ℝ≥0∞) (c : ℝ)
    (F : Vec d → Vec d) :
    vecCubeLpENorm Q q (fun x => c • F x) = ‖c‖ₑ * vecCubeLpENorm Q q F := by
  have h : hilbertifyVecField (fun x => c • F x) = c • hilbertifyVecField F := by
    funext x
    exact map_smul (HilbertVec.linearEquivVec d).symm c (F x)
  rw [vecCubeLpENorm, h, Section2.Norms.cubeLpENorm_const_smul, vecCubeLpENorm]

theorem vecCubeLpENorm_add_le {Q : TriadicCube d} {q : ℝ≥0∞}
    {F G : Vec d → Vec d} (hq : 1 ≤ q)
    (hF : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q))
    (hG : AEStronglyMeasurable (hilbertifyVecField G) (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q q (fun x => F x + G x) ≤
      vecCubeLpENorm Q q F + vecCubeLpENorm Q q G := by
  have h : hilbertifyVecField (fun x => F x + G x)
      = hilbertifyVecField F + hilbertifyVecField G := by
    funext x
    exact map_add (HilbertVec.linearEquivVec d).symm (F x) (G x)
  rw [vecCubeLpENorm, h]
  exact Section2.Norms.cubeLpENorm_add_le hq hF hG

/-! ## The hatted negative norm `Ĥ̲^{-1}` of a vector field -/

/-- The test class of the hatted negative norm: smooth, with vanishing average on the cube,
and with normalized `L̲²` gradient norm at most one. The smoothness is global
smoothness on `Vec d`, so `fderiv` is a genuine derivative at every point of
the cube. -/
structure IsVecHatTestField (Q : TriadicCube d) (g : Vec d → ℝ) : Prop where
  /-- `g ∈ C^∞`. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) g
  /-- `(g)_U = 0`. -/
  meanZero : volumeAverage (cubeSet Q) g = 0
  /-- `‖∇g‖_{L̲²(U)} ≤ 1`. -/
  gradient_le_one : vecCubeLpENorm Q 2 (euclideanGradient g) ≤ 1

/-- The density `F(x)·∇g(x)` of the gradient pairing, written as
the derivative of `g` at `x` in the direction `F x`; this needs no
inner-product structure on `Vec d`. -/
noncomputable def vecGradientPairingDensity (F : Vec d → Vec d)
    (g : Vec d → ℝ) : Vec d → ℝ :=
  fun x => fderiv ℝ g x (F x)

/-- The pairing density is the manuscript's `F·∇g`, coordinatewise. -/
theorem vecGradientPairingDensity_eq_sum (F : Vec d → Vec d) (g : Vec d → ℝ)
    (x : Vec d) :
    vecGradientPairingDensity F g x =
      ∑ i, F x i * euclideanGradient g x i := by
  have hsum : F x = ∑ i, F x i • basisVec i := by
    funext j
    simp [basisVec, Finset.sum_apply, Pi.single_apply]
  calc
    vecGradientPairingDensity F g x
        = fderiv ℝ g x (∑ i, F x i • basisVec i) := by
          rw [vecGradientPairingDensity, ← hsum]
    _ = ∑ i, F x i * euclideanGradient g x i := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => by
            rw [map_smul]
            rfl

theorem continuous_vecGradientPairingDensity {F : Vec d → Vec d}
    (hF : Continuous F) {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous (vecGradientPairingDensity F g) := by
  have hfd : Continuous (fun x : Vec d => fderiv ℝ g x) :=
    hg.continuous_fderiv (by simp)
  exact hfd.clm_apply hF

theorem vecGradientPairingDensity_integrableOn {F : Vec d → Vec d}
    (hF : Continuous F) {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (Q : TriadicCube d) :
    IntegrableOn (vecGradientPairingDensity F g) (cubeSet Q) volume :=
  ((continuous_vecGradientPairingDensity hF hg).continuousOn.integrableOn_compact
    ((isBounded_cubeSet Q).isCompact_closure)).mono_set subset_closure

/-- `‖F‖_{Ĥ̲^{-1}(Q)}`: the supremum of the volume-normalized
pairing `⨍_Q F·∇g` over smooth mean-zero `g` with `‖∇g‖_{L̲²(Q)} ≤ 1`. -/
noncomputable def vecHatNegENorm (Q : TriadicCube d) (F : Vec d → Vec d) :
    ℝ≥0∞ :=
  ⨆ g : Vec d → ℝ, ⨆ _ : IsVecHatTestField Q g,
    ENNReal.ofReal
      (volumeAverage (cubeSet Q) (vecGradientPairingDensity F g))

theorem le_vecHatNegENorm {Q : TriadicCube d} (F : Vec d → Vec d)
    {g : Vec d → ℝ} (hg : IsVecHatTestField Q g) :
    ENNReal.ofReal
        (volumeAverage (cubeSet Q) (vecGradientPairingDensity F g)) ≤
      vecHatNegENorm Q F :=
  le_iSup_of_le g (le_iSup_of_le hg le_rfl)

theorem vecHatNegENorm_le {Q : TriadicCube d} {F : Vec d → Vec d} {c : ℝ≥0∞}
    (h : ∀ g : Vec d → ℝ, IsVecHatTestField Q g →
      ENNReal.ofReal
          (volumeAverage (cubeSet Q) (vecGradientPairingDensity F g)) ≤ c) :
    vecHatNegENorm Q F ≤ c :=
  iSup_le fun g => iSup_le fun hg => h g hg

end

end ResponseFields
end Section3
end SuperdiffusionCLT
