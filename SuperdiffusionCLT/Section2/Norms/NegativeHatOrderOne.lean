/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairing

/-!
# The order-one hatted negative norm of a vector field

The paper reads the hatted negative norms of a vector field through the gradient pairing
(the "for instance" sentence in the definition of the hatted norms).
`Section3/ResponseFields/Norms.lean` formalizes that sentence literally, as `vecHatNegENorm`,
with the test class `‖∇g‖_{L̲²(Q)} ≤ 1`.  That quantity is **order zero**: since the pairing
sees the same `L̲²(Q)` gradient norm the test class is normalized by, it is bounded by
`‖F‖_{L̲²(Q)}` with constant one
(`SuperdiffusionCLT.Section2.Norms.vecHatNegENorm_le_vecCubeLpENorm`), and a
unit field oscillating at scale `3^k` inside `cu_l` has `vecHatNegENorm` of size
`1`, not `3^{k−l}`.

Every printed use of `‖·‖_{Ĥ̲^{-1}}` on a vector field needs the **order-one**
quantity instead: `e.jk.Hminus.endpoint`, `e.abstract.response.ND.weak`, Step 4 of
`l.abstract.response.fields`, and Step 2 of `l.RHS.term1`, whose printed dual partner is
`‖∇w‖_{H̲¹(cu_m)}` and not `‖∇w‖_{L̲²(cu_m)}`.  The formalization reads the norm that way:
the instance `s = 1`, `p' = 2` of the hatted negative norm, in the scaled normalization.
The printed "for instance" sentence is thus corrected (see `ERRATA.md`).

This module defines that carrier as `vecHatNegENormOrderOne`.

## The normalization

`vecHatNegENormOrderOne Q F` is the supremum of `⨍_Q F·∇g` over smooth `g` with
`(g)_Q = 0` and

`‖∇g‖_{L̲²(Q)} + 3^{scale Q} ‖∇²g‖_{L̲²(Q)} ≤ 1`,

which is `vecHatTestH1ENorm Q g ≤ 1` below.  In the paper's `H̲¹`
normalization the constraint is `‖∇g‖_{H̲¹(Q)} ≤ 3^{-scale Q}`; the `H̲¹`
carrier `vecCubeH1ENorm` of that normalization is defined in
`Section3/Terms/RHSTerm1Inputs.lean`.

Under this normalization a constant field `c` has norm at most `|c|` (its test
gradient has `‖∇g‖_{L̲²} ≤ 1`), and a unit field oscillating at scale `3^k` on
`cu_l` has norm `≍ 3^{k−l}`: an aligned test potential must pay
`3^l‖∇²g‖_{L̲²} ≍ 3^{l−k}‖∇g‖_{L̲²}`.  This is the convention of
`e.jk.Hminus.endpoint` and of `e.abstract.response.ND.weak`.  It differs from the
un-normalized `H^{-1}` of the printed multiscale display by the single
factor `3^{scale Q}`: with `Q = cu_m`,

`(3^m · vecHatNegENormOrderOne (cu_m) F)² ≤ C ∑_{k ≤ m} 3^{2k} avsum_z |(F)_{z+cu_k}|²`
  iff  `vecHatNegENormOrderOne (cu_m) F ² ≤ C ∑_{k ≤ m} 3^{2(k−m)} avsum_z |(F)_{z+cu_k}|²`.

## Where this module sits

The carrier is stated on the vector-field norms of
`Section3/ResponseFields/Norms.lean` (`vecCubeLpENorm`, `vecGradientPairingDensity`,
`vecHatNegENorm`), exactly as `Section2/Norms/NegativeNormPairing.lean` already is:
that file is this module's only import and already opens those carriers, so no new
module dependency is created by naming them.  Stating the carrier here lets the
Section 2 results — the shell endpoint `e.jk.Hminus.endpoint` first of all — use
the order-one norm without importing the `Section3/Terms/RHSTerm1Inputs*` chain.

## What is proved here, and what is not

* The carrier, its test class, and the norm laws.
* `vecHatNegENormOrderOne_le_vecHatNegENorm`: the V2 test class is contained in the
  order-zero one, so the V2 norm is the smaller of the two; with
  `vecHatNegENorm_le_vecCubeLpENorm` this gives finiteness for every `L̲²` field.
* The duality, in two forms: `ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne_mul`
  for a smooth potential of arbitrary size, and
  `ofReal_abs_volumeAverage_vecDot_le_vecHatNegENormOrderOne_mul` for a general `L̲²`
  gradient field `G` — the shape Step 2 of `l.RHS.term1` needs at `G = ∇w`,
  `w ∈ H^1_0(cu_m)`.  Smooth approximation of `G` inside the V2 test class is
  **not** proved here for `H^1_0` fields, so it is carried as the single explicit
  hypothesis `hDense` of that theorem.
* The **multiscale decomposition is not proved**, and the printed squared form is
  not provable in any carrier.  See the next section.

## The printed multiscale line, and why its squared form fails

The first line of the printed multiscale display reads, in this normalization,

`‖F‖²_{Ĥ̲^{-1}(cu_m)} ≤ C ∑_{k ≤ m} 3^{2(k−m)} avsum_{z ∈ 3^kℤ^d ∩ cu_m}
  |(F)_{z+cu_k}|²`.

What the multiscale Poincaré inequality gives is the `ℓ¹` form

`‖F‖_{Ĥ̲^{-1}(cu_m)} ≤ C ∑_{k ≤ m} 3^{k−m}
  (avsum_{z ∈ 3^kℤ^d ∩ cu_m} |(F)_{z+cu_k}|²)^{1/2}`,

and the squared form does **not** follow from it: the two differ by a factor
equal to the number of active scales, and that loss is real.  Write `Z_k` for the
scale-`k` triadic sub-cubes of `cu_m`, take the admissible potential
`g(x) = c 3^{-m}|x|²/2`, whose gradient has triadic martingale increments
`δ^{(k)}` of size `≍ 3^{k−m}` at every scale, and set
`F = ∑_{j=0}^{J} 3^{j} P_{m−j}`, where `P_k` is the piecewise-constant field
equal on each `R ∈ Z_k` to `δ^{(k)}_R` normalized in `L̲²(cu_m)`.  The `P_k` are
mutually orthogonal martingale increments, so
`avsum_{R ∈ Z_k}|(F)_R|² = ∑_{j ≤ m−k} 9^{j}` and the right-hand side above is
`≍ ∑_{j ≥ 0} 9^{-j} ∑_{j' ≤ j} 9^{j'} ≍ J`.  Pairing `F` against that one
potential already gives `⨍_{cu_m} F·∇g ≍ ∑_{j ≤ J} 3^{j} 3^{-j} = J`, so the left
side is `≍ J²`.  The ratio is the number of scales.  This is an author question,
recorded and not decided here.

## Main definitions

* `euclideanGradientJacobian`: the Jacobian `∇²g` of a smooth gradient.
* `vecHatTestH1ENorm`: `‖∇g‖_{L̲²(Q)} + 3^{scale Q}‖∇²g‖_{L̲²(Q)}`.
* `IsVecHatTestFieldOrderOne`: the order-one test class.
* `vecHatNegENormOrderOne`: the order-one hatted negative norm of a vector field.

## Main results

* `isVecHatTestField_of_isVecHatTestFieldOrderOne`.
* `le_vecHatNegENormOrderOne`, `vecHatNegENormOrderOne_le`: the supremum characterization.
* `vecHatNegENormOrderOne_le_vecHatNegENorm`, `vecHatNegENormOrderOne_le_vecCubeLpENorm`.
* `ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne_mul`: the duality against
  a smooth potential.
* `ofReal_abs_volumeAverage_vecDot_le_vecHatNegENormOrderOne_mul`: the duality against a
  general `L̲²` gradient field, with the smooth approximation carried.

## References

* The paper: the definition of the hatted norms, `e.jk.Hminus.endpoint`,
  `e.abstract.response.ND.weak`, `l.abstract.response.fields` and `l.RHS.term1`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The Jacobian of a smooth gradient -/

/-- `∇²g`, the Jacobian of the Euclidean gradient of a smooth potential, in the
project's matrix carrier. -/
def euclideanGradientJacobian (g : Vec d → ℝ) : Vec d → Mat d :=
  fun x => (fun i j => euclideanCoordDeriv j (fun y => euclideanGradient g y i) x : Mat d)

/-- Each row of a smooth gradient is itself smooth, hence differentiable; this is
what makes `euclideanGradientJacobian` behave linearly. -/
theorem differentiable_euclideanGradient_apply {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    Differentiable ℝ (fun y : Vec d => euclideanGradient g y i) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => fderiv ℝ g y) :=
    hg.fderiv_right (by simp)
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => fderiv ℝ g y (basisVec i)) :=
    hfd.clm_apply contDiff_const
  exact h.differentiable (by simp)

@[simp] theorem euclideanGradientJacobian_zero :
    euclideanGradientJacobian (fun _ : Vec d => (0 : ℝ)) = fun _ => (0 : Mat d) := by
  funext x i j
  simp [euclideanGradientJacobian, euclideanGradient, euclideanCoordDeriv]

theorem euclideanGradientJacobian_neg (g : Vec d → ℝ) :
    euclideanGradientJacobian (-g) = fun x => -euclideanGradientJacobian g x := by
  have hgi : ∀ i : Fin d, (fun y : Vec d => euclideanGradient (-g) y i)
      = -(fun y : Vec d => euclideanGradient g y i) := by
    intro i
    funext y
    show fderiv ℝ (-g) y (basisVec i) = -(fderiv ℝ g y (basisVec i))
    rw [fderiv_neg, neg_apply]
  funext x i j
  show fderiv ℝ (fun y : Vec d => euclideanGradient (-g) y i) x (basisVec j)
      = (-euclideanGradientJacobian g x) i j
  rw [hgi i, fderiv_neg, neg_apply]
  rfl

theorem euclideanGradientJacobian_const_mul (c : ℝ) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    euclideanGradientJacobian (fun x => c * g x)
      = fun x => c • euclideanGradientJacobian g x := by
  have hgi : ∀ i : Fin d, (fun y : Vec d => euclideanGradient (fun z => c * g z) y i)
      = c • (fun y : Vec d => euclideanGradient g y i) := by
    intro i
    funext y
    show euclideanGradient (fun z => c * g z) y i = c * euclideanGradient g y i
    rw [euclideanGradient_const_mul hg c]
    rfl
  funext x i j
  show fderiv ℝ (fun y : Vec d => euclideanGradient (fun z => c * g z) y i) x (basisVec j)
      = (c • euclideanGradientJacobian g x) i j
  rw [hgi i, fderiv_const_smul (differentiable_euclideanGradient_apply hg i x) c,
    smul_apply]
  rfl

theorem hilbertMat_ofMat_smul (c : ℝ) (A : Mat d) :
    HilbertMat.ofMat (c • A) = c • HilbertMat.ofMat A := by
  ext i j
  rfl

/-! ## The order-one test norm -/

/-- `‖∇g‖_{L̲²(Q)} + 3^{scale Q} ‖∇²g‖_{L̲²(Q)}`, the quantity the order-one test
class constrains. -/
def vecHatTestH1ENorm (Q : TriadicCube d) (g : Vec d → ℝ) : ℝ≥0∞ :=
  vecCubeLpENorm Q 2 (euclideanGradient g) +
    ENNReal.ofReal ((3 : ℝ) ^ ((Q.scale : ℝ))) *
      cubeLpENorm Q 2
        (fun x => HilbertMat.ofMat (euclideanGradientJacobian g x))

/-- The `L̲²` gradient norm is the first summand of the test norm. -/
theorem vecCubeLpENorm_euclideanGradient_le_vecHatTestH1ENorm (Q : TriadicCube d)
    (g : Vec d → ℝ) :
    vecCubeLpENorm Q 2 (euclideanGradient g) ≤ vecHatTestH1ENorm Q g :=
  le_self_add

@[simp] theorem vecHatTestH1ENorm_zero (Q : TriadicCube d) :
    vecHatTestH1ENorm Q (fun _ : Vec d => (0 : ℝ)) = 0 := by
  have hgrad : euclideanGradient (fun _ : Vec d => (0 : ℝ))
      = fun _ : Vec d => (0 : Vec d) := by
    funext x i
    simp [euclideanGradient, euclideanCoordDeriv]
  have hjac : (fun x : Vec d =>
      HilbertMat.ofMat (euclideanGradientJacobian (fun _ : Vec d => (0 : ℝ)) x))
      = (0 : Vec d → HilbertMat d) := by
    funext x
    rw [euclideanGradientJacobian_zero]
    ext i j
    rfl
  rw [vecHatTestH1ENorm, hgrad, hjac, vecCubeLpENorm_zero,
    cubeLpENorm_zero, mul_zero, add_zero]

theorem vecHatTestH1ENorm_neg (Q : TriadicCube d) (g : Vec d → ℝ) :
    vecHatTestH1ENorm Q (-g) = vecHatTestH1ENorm Q g := by
  have hgrad : euclideanGradient (-g) = fun x => -euclideanGradient g x := by
    funext x i
    show fderiv ℝ (-g) x (basisVec i) = -(fderiv ℝ g x (basisVec i))
    rw [fderiv_neg, neg_apply]
  have hjac : (fun x : Vec d => HilbertMat.ofMat (euclideanGradientJacobian (-g) x))
      = -(fun x : Vec d => HilbertMat.ofMat (euclideanGradientJacobian g x)) := by
    funext x
    rw [euclideanGradientJacobian_neg]
    ext i j
    rfl
  rw [vecHatTestH1ENorm, hgrad, hjac, vecCubeLpENorm_neg,
    cubeLpENorm_neg, vecHatTestH1ENorm]

theorem vecHatTestH1ENorm_const_mul (Q : TriadicCube d) (c : ℝ) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    vecHatTestH1ENorm Q (fun x => c * g x) = ‖c‖ₑ * vecHatTestH1ENorm Q g := by
  have hjac : (fun x : Vec d =>
      HilbertMat.ofMat (euclideanGradientJacobian (fun y => c * g y) x))
      = c • (fun x : Vec d => HilbertMat.ofMat (euclideanGradientJacobian g x)) := by
    funext x
    rw [euclideanGradientJacobian_const_mul c hg, hilbertMat_ofMat_smul]
    rfl
  rw [vecHatTestH1ENorm, euclideanGradient_const_mul hg c, hjac,
    vecCubeLpENorm_const_smul, cubeLpENorm_const_smul,
    vecHatTestH1ENorm, mul_add]
  ring

/-! ## The order-one test class and the order-one hatted negative norm -/

/-- The order-one test class:
smooth, mean zero on the cube, and with the *gradient field* constrained in
`H̲¹(Q)`, i.e. `vecHatTestH1ENorm Q g ≤ 1`. -/
structure IsVecHatTestFieldOrderOne (Q : TriadicCube d) (g : Vec d → ℝ) : Prop where
  /-- `g ∈ C^∞`. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) g
  /-- `(g)_U = 0`. -/
  meanZero : volumeAverage (cubeSet Q) g = 0
  /-- `‖∇g‖_{L̲²(Q)} + 3^{scale Q}‖∇²g‖_{L̲²(Q)} ≤ 1`. -/
  h1_le_one : vecHatTestH1ENorm Q g ≤ 1

theorem vecHatTestFieldOrderOne_neg {Q : TriadicCube d} {g : Vec d → ℝ}
    (hg : IsVecHatTestFieldOrderOne Q g) : IsVecHatTestFieldOrderOne Q (-g) where
  contDiff := hg.contDiff.neg
  meanZero := by
    have hneg : volumeAverage (cubeSet Q) (-g) = -volumeAverage (cubeSet Q) g := by
      simp only [volumeAverage, Pi.neg_def, integral_neg, mul_neg]
    rw [hneg, hg.meanZero, neg_zero]
  h1_le_one := by rw [vecHatTestH1ENorm_neg]; exact hg.h1_le_one

/-- **The order-one test class is contained in the order-zero one**:
its constraint `‖∇g‖_{L̲²(Q)} + 3^{scale Q}‖∇²g‖_{L̲²(Q)} ≤ 1` implies
`‖∇g‖_{L̲²(Q)} ≤ 1`. -/
theorem isVecHatTestField_of_isVecHatTestFieldOrderOne {Q : TriadicCube d} {g : Vec d → ℝ}
    (hg : IsVecHatTestFieldOrderOne Q g) : IsVecHatTestField Q g where
  contDiff := hg.contDiff
  meanZero := hg.meanZero
  gradient_le_one :=
    le_trans (vecCubeLpENorm_euclideanGradient_le_vecHatTestH1ENorm Q g) hg.h1_le_one

/-- **`‖F‖_{Ĥ̲^{-1}(Q)}` at order one**: the supremum of `⨍_Q F·∇g` over the
order-one test class.  This is the carrier every printed use of the hatted
negative norm on a vector field needs; see the module docstring. -/
def vecHatNegENormOrderOne (Q : TriadicCube d) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ⨆ g : Vec d → ℝ, ⨆ _ : IsVecHatTestFieldOrderOne Q g,
    ENNReal.ofReal
      (volumeAverage (cubeSet Q) (vecGradientPairingDensity F g))

theorem le_vecHatNegENormOrderOne {Q : TriadicCube d} (F : Vec d → Vec d)
    {g : Vec d → ℝ} (hg : IsVecHatTestFieldOrderOne Q g) :
    ENNReal.ofReal
        (volumeAverage (cubeSet Q) (vecGradientPairingDensity F g)) ≤
      vecHatNegENormOrderOne Q F :=
  le_iSup_of_le g (le_iSup_of_le hg le_rfl)

theorem vecHatNegENormOrderOne_le {Q : TriadicCube d} {F : Vec d → Vec d} {c : ℝ≥0∞}
    (h : ∀ g : Vec d → ℝ, IsVecHatTestFieldOrderOne Q g →
      ENNReal.ofReal
          (volumeAverage (cubeSet Q) (vecGradientPairingDensity F g)) ≤ c) :
    vecHatNegENormOrderOne Q F ≤ c :=
  iSup_le fun g => iSup_le fun hg => h g hg

/-- **The order-one norm is the smaller of the two**: the order-one test class is
contained in the order-zero one. -/
theorem vecHatNegENormOrderOne_le_vecHatNegENorm (Q : TriadicCube d) (F : Vec d → Vec d) :
    vecHatNegENormOrderOne Q F ≤ vecHatNegENorm Q F :=
  vecHatNegENormOrderOne_le fun _g hg =>
    le_vecHatNegENorm F (isVecHatTestField_of_isVecHatTestFieldOrderOne hg)

/-- An `L̲²` field has a finite order-one hatted negative norm. -/
theorem vecHatNegENormOrderOne_le_vecCubeLpENorm {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    vecHatNegENormOrderOne Q F ≤ vecCubeLpENorm Q 2 F :=
  le_trans (vecHatNegENormOrderOne_le_vecHatNegENorm Q F)
    (vecHatNegENorm_le_vecCubeLpENorm hF)

/-! ## The duality -/

/-- The pairing against one admissible order-one test field, in absolute value. -/
theorem ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne {Q : TriadicCube d}
    (F : Vec d → Vec d) {g : Vec d → ℝ} (hg : IsVecHatTestFieldOrderOne Q g) :
    ENNReal.ofReal |volumeAverage (cubeSet Q) (vecGradientPairingDensity F g)| ≤
      vecHatNegENormOrderOne Q F := by
  have hneg : vecGradientPairingDensity F (-g) =
      fun x => -vecGradientPairingDensity F g x := by
    funext x
    show fderiv ℝ (-g) x (F x) = -(fderiv ℝ g x (F x))
    rw [fderiv_neg, neg_apply]
  have havg : volumeAverage (cubeSet Q) (vecGradientPairingDensity F (-g)) =
      -volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) := by
    rw [hneg]
    simp only [volumeAverage, integral_neg, mul_neg]
  have hpos := le_vecHatNegENormOrderOne F hg
  have hminus := le_vecHatNegENormOrderOne F (vecHatTestFieldOrderOne_neg hg)
  rw [havg] at hminus
  rcases abs_cases (volumeAverage (cubeSet Q) (vecGradientPairingDensity F g))
    with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]; exact hpos
  · rw [he]; exact hminus

/-- **The duality against a smooth potential of arbitrary size.**

`|⨍_Q F·∇g| ≤ (‖∇g‖_{L̲²(Q)} + 3^{scale Q}‖∇²g‖_{L̲²(Q)}) ‖F‖_{Ĥ̲^{-1}(Q)}`,

in the form with the right-hand test quantity bounded by an explicit `c > 0`.
This is the homogeneity of the supremum in the test potential. -/
theorem ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne_mul {Q : TriadicCube d}
    (F : Vec d → Vec d) {g : Vec d → ℝ} {c : ℝ} (hc : 0 < c)
    (hgc : ContDiff ℝ (⊤ : ℕ∞) g) (hmz : volumeAverage (cubeSet Q) g = 0)
    (hnorm : vecHatTestH1ENorm Q g ≤ ENNReal.ofReal c) :
    ENNReal.ofReal |volumeAverage (cubeSet Q) (vecGradientPairingDensity F g)| ≤
      ENNReal.ofReal c * vecHatNegENormOrderOne Q F := by
  have hcinv : (0 : ℝ) < c⁻¹ := inv_pos.2 hc
  have htest : IsVecHatTestFieldOrderOne Q (fun x => c⁻¹ * g x) := by
    refine ⟨contDiff_const.mul hgc, ?_, ?_⟩
    · rw [volumeAverage_const_mul, hmz, mul_zero]
    · rw [vecHatTestH1ENorm_const_mul Q c⁻¹ hgc]
      have hcast : ‖c⁻¹‖ₑ = ENNReal.ofReal c⁻¹ := by
        rw [Real.enorm_eq_ofReal (le_of_lt hcinv)]
      rw [hcast]
      refine le_trans (mul_le_mul' le_rfl hnorm) ?_
      rw [← ENNReal.ofReal_mul (le_of_lt hcinv), inv_mul_cancel₀ (ne_of_gt hc),
        ENNReal.ofReal_one]
  have hdens : vecGradientPairingDensity F (fun x => c⁻¹ * g x)
      = fun x => c⁻¹ * vecGradientPairingDensity F g x := by
    funext x
    show fderiv ℝ (c⁻¹ • g) x (F x) = c⁻¹ * (fderiv ℝ g x (F x))
    rw [fderiv_const_smul ((hgc.differentiable (by simp)) x) c⁻¹,
      smul_apply, smul_eq_mul]
  have habs := ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne F htest
  rw [hdens, volumeAverage_const_mul, abs_mul, abs_of_pos hcinv] at habs
  have hkey : ENNReal.ofReal c * ENNReal.ofReal (c⁻¹ *
      |volumeAverage (cubeSet Q) (vecGradientPairingDensity F g)|)
      = ENNReal.ofReal |volumeAverage (cubeSet Q) (vecGradientPairingDensity F g)| := by
    rw [← ENNReal.ofReal_mul (le_of_lt hc), ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hc), one_mul]
  rw [← hkey]
  exact mul_le_mul' le_rfl habs

/-- **The duality in the shape Step 2 of `l.RHS.term1` needs.**

`|⨍_Q F·G| ≤ (‖G‖_{L̲²(Q)} + 3^{scale Q}‖∇G‖_{L̲²(Q)}) ‖F‖_{Ĥ̲^{-1}(Q)}`,

in the form with the test quantity bounded by an explicit `c > 0`.  At `G = ∇w`
and `w ∈ H^1_0(cu_m)` with a weak Hessian this is the printed duality display,
whose printed dual partner is `‖∇w‖_{H̲¹(cu_m)}`.

The supremum defining `vecHatNegENormOrderOne` ranges over *smooth* potentials while
`G` is only `L̲²` with an `L̲²` Jacobian, so the passage from a smooth test
potential to `G` is a density statement, not an unfolding of the definition.
Smooth approximation inside the order-one test class is not proved here for `H^1_0`
gradient fields, so it is carried, once, as `hDense`: for every `ε > 0` a smooth
mean-zero `g` admissible at level `c` with `‖G − ∇g‖_{L̲²(Q)} ≤ ε`.  No other
input is carried; in particular `hDense` says nothing about `F`. -/
theorem ofReal_abs_volumeAverage_vecDot_le_vecHatNegENormOrderOne_mul {Q : TriadicCube d}
    {F G : Vec d → Vec d} {c : ℝ} (hc : 0 < c)
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q))
    (hG : MemLp (hilbertifyVecField G) 2 (normalizedCubeMeasure Q))
    (hDense : ∀ eps : ℝ, 0 < eps → ∃ g : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ volumeAverage (cubeSet Q) g = 0 ∧
        vecHatTestH1ENorm Q g ≤ ENNReal.ofReal c ∧
        vecCubeLpENorm Q 2 (fun x => G x - euclideanGradient g x) ≤
          ENNReal.ofReal eps) :
    ENNReal.ofReal |volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x))| ≤
      ENNReal.ofReal c * vecHatNegENormOrderOne Q F := by
  have hV2ne : vecHatNegENormOrderOne Q F ≠ ⊤ :=
    ne_top_of_le_ne_top hF.eLpNorm_lt_top.ne (vecHatNegENormOrderOne_le_vecCubeLpENorm hF)
  set V : ℝ := (vecHatNegENormOrderOne Q F).toReal with hVdef
  have hV0 : (0 : ℝ) ≤ V := ENNReal.toReal_nonneg
  set M : ℝ := (vecCubeLpENorm Q 2 F).toReal with hMdef
  have hM0 : (0 : ℝ) ≤ M := ENNReal.toReal_nonneg
  have hreal : |volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x))| ≤ c * V := by
    refine le_of_forall_pos_le_add fun delta hdelta => ?_
    obtain ⟨g, hgc, hmz, hnorm, hclose⟩ := hDense (delta / (M + 1)) (by positivity)
    have hgfin : vecCubeLpENorm Q 2 (euclideanGradient g) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (le_trans (vecCubeLpENorm_euclideanGradient_le_vecHatTestH1ENorm Q g) hnorm)
    have hgmem := memLp_hilbertifyVecField_euclideanGradient hgc hgfin
    have hDmem : MemLp (hilbertifyVecField (fun x => G x - euclideanGradient g x)) 2
        (normalizedCubeMeasure Q) := by
      rw [hilbertifyVecField_sub']
      exact hG.sub hgmem
    have hLp : hDmem.toLp (hilbertifyVecField (fun x => G x - euclideanGradient g x))
        = hG.toLp (hilbertifyVecField G)
          - hgmem.toLp (hilbertifyVecField (euclideanGradient g)) := by
      rw [← MemLp.toLp_sub]
      exact MemLp.toLp_congr hDmem (hG.sub hgmem)
        (Filter.EventuallyEq.of_eq (hilbertifyVecField_sub' G (euclideanGradient g)))
    have hsplit : volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x))
        = volumeAverage (cubeSet Q) (fun x => vecDot (F x) (euclideanGradient g x))
          + volumeAverage (cubeSet Q)
              (fun x => vecDot (F x) (G x - euclideanGradient g x)) := by
      rw [← inner_toLp_hilbertifyVecField hF hG,
        ← inner_toLp_hilbertifyVecField hF hgmem,
        ← inner_toLp_hilbertifyVecField hF hDmem, hLp, inner_sub_right]
      ring
    have hdens : (fun x => vecDot (F x) (euclideanGradient g x))
        = vecGradientPairingDensity F g := by
      funext x
      rw [vecGradientPairingDensity_eq_vecDot]
    have hsmoothE := ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne_mul F hc hgc
      hmz hnorm
    rw [← hdens] at hsmoothE
    have hprod : ENNReal.ofReal c * vecHatNegENormOrderOne Q F = ENNReal.ofReal (c * V) := by
      rw [ENNReal.ofReal_mul (le_of_lt hc), hVdef, ENNReal.ofReal_toReal hV2ne]
    rw [hprod] at hsmoothE
    have hsmooth : |volumeAverage (cubeSet Q)
        (fun x => vecDot (F x) (euclideanGradient g x))| ≤ c * V :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hsmoothE
    have hcloseR : (vecCubeLpENorm Q 2 (fun x => G x - euclideanGradient g x)).toReal
        ≤ delta / (M + 1) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hclose
    have hremCS := abs_volumeAverage_vecDot_le_mul hF hDmem
    have hrem : |volumeAverage (cubeSet Q)
        (fun x => vecDot (F x) (G x - euclideanGradient g x))| ≤ M * (delta / (M + 1)) :=
      le_trans hremCS (mul_le_mul_of_nonneg_left hcloseR hM0)
    have hMd : M * (delta / (M + 1)) ≤ delta := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have hexp : delta * (M + 1) = M * delta + delta := by ring
      rw [hexp]
      linarith only [hdelta.le]
    rw [hsplit]
    have habs := abs_add_le
      (volumeAverage (cubeSet Q) (fun x => vecDot (F x) (euclideanGradient g x)))
      (volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x - euclideanGradient g x)))
    linarith only [habs, hsmooth, hrem, hMd]
  calc ENNReal.ofReal |volumeAverage (cubeSet Q) (fun x => vecDot (F x) (G x))|
      ≤ ENNReal.ofReal (c * V) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal c * ENNReal.ofReal V := ENNReal.ofReal_mul (le_of_lt hc)
    _ ≤ ENNReal.ofReal c * vecHatNegENormOrderOne Q F :=
        mul_le_mul' le_rfl (by rw [hVdef]; exact ENNReal.ofReal_toReal_le)

end

end Norms
end Section2
end SuperdiffusionCLT
