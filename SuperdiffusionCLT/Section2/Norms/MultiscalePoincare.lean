/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeHat
public import SuperdiffusionCLT.Section2.Estimates.Stream.SpatialAverageTail
public import SuperdiffusionCLT.Probability.OrliczPower
public import Homogenization.Book.Ch04.Theorems.Concentration
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The multiscale depth sums of a matrix field on a triadic cube

display `e.apply.multiscale.Poincare`, applies the multiscale Poincaré inequality
(`\cite[Lemma A.2]{AK.HC}` with `q = 1`) in the form

> `3^{-sl} ‖j_k‖_{Ŵ̲^{-s,p}(cu_l)} ≤ C ∑_{h ≤ l} 3^{s(h-l)}
>   ( ⨍_{y ∈ 3^h ℤ^d ∩ cu_l} |(j_k)_{y+cu_h}|^p )^{1/p}`.

This module builds the right-hand side in the marginal carriers and proves the
`Γ₂` tail of each of its terms for one shell.

## The two depth sums

Two shapes of the right-hand side occur, and both are defined here.

* `cubeMultiscaleDepthSum` is the printed shape: an `ℓ¹` sum over the depths
  `j = l - h` of the geometric weight `3^{-sj}` times the rooted depth moment
  `(cubeDepthPthMoment Q j p M)^{1/p}`.
* `cubeNegativeBesovDepthENorm` is the shape realized upstream by
  `Homogenization.cubeEuclideanNegativeBesovESeminorm`
  (`Homogenization/Book/Ch03/ABK26/NegativeBesov.lean`): the depth weight
  `3^{s p (Q.scale - j)}` sits inside an `ℓ^p` sum which is rooted only at the
  end. Its summand `cubeDepthEnergy` is the marginal transcription of
  `Homogenization.cubeEuclideanNegativeBesovDepthEnergy`, with the matrix
  operator norm of `volumeAverageMat` in place of the Euclidean norm of
  `cubeAverageVec`, and with `ENNReal.ofReal` applied after the `p`-th power
  instead of before it.

`cubeNegativeBesovDepthENorm_le_cubeMultiscaleDepthSum` converts the second
shape into the first at the cost of the factor `3^{s (Q.scale)}`; this is the
`ℓ^p ⊆ ℓ¹` step, which the upstream library does not carry.

## The averaging carriers

The depth moment averages `‖(M)_R‖^p` over the triadic descendants
`descendantsAtDepth Q j`, which is the exact partition of `Q` into the
`3^{dj}` sub-cubes of scale `Q.scale - j`. The printed average is over the
lattice `3^h ℤ^d ∩ cu_l`; the two families coincide when the parent cube is
exactly tiled, which is the case here, and no overlapping family is used.

`volumeAverageMat_cubeSet_eq_shellSpatialAverage` identifies the descendant
average of a shell with the translated-cube carrier
`shellSpatialAverage`, which is what carries the tail estimate.

## What is proved about the hatted negative norm

Nothing here bounds the earlier hatted negative norm by these depth sums, and the
module docstring records why. In the earlier reading of the hatted negative norm,
its test class constrains the
Gagliardo seminorm `[g]_{W̲^{s,p'}(Q)}` of the scalar potential `g`, while the
pairing is the rank-one gradient density `⟨M, v ⊗ ∇g⟩`. With that reading the
supremum is not finite in general: the family of smooth `g` which rise from
`0` to `a` across a boundary layer of width `δ` inside `Q` satisfies
`[g]_{W̲^{s,p'}(Q)} ≍ a (δ / 3^l)^{1/p'} δ^{-s}` while
`|⨍_Q ∇g| ≍ a 3^{-l}`, so the normalized pairing against a matrix field whose
average boundary flux does not vanish is of order `3^{-l/p} δ^{s - 1/p'}`,
which is unbounded as `δ → 0` whenever `s p' < 1`. The realization of
Lemma A.2 in the CoarseGraining library,
`Homogenization.cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm`,
constrains instead the *test vector field* in the full `W^{s,p'}` norm, which
is the constraint the paper itself uses
(`‖∇w‖_{H̲^{1/2}(cu_m)}`) and the one under which the printed display
`e.apply.multiscale.Poincare` is dimensionally consistent. The gap between the
two test classes is a question about the reading of the norm, not a gap in a proof, and no
statement here asserts a bound on the earlier hatted negative norm.

## Main definitions

* `cubeDepthPthMoment`: the normalized average of `‖(M)_R‖^p` over the triadic
  descendants of `Q` at depth `j`.
* `cubeDepthEnergy`, `cubeNegativeBesovDepthENorm`: the upstream `ℓ^p` shape.
* `cubeMultiscaleDepthSum`: the printed `ℓ¹` shape.
* `depthShellTailAmplitude`, `cubeDepthMomentTailConst`: the explicit
  amplitude and constant of the one-shell tail.

## Main results

* `matGradientPairingDensity_eq_vecDot`: the rank-one gradient
  density as the `vecDot` pairing used in the CoarseGraining library.
* `volumeAverageMat_cubeSet_eq_shellSpatialAverage`: the descendant average of
  a shell is a translated centred cube average.
* `cubeNegativeBesovDepthENorm_le_cubeMultiscaleDepthSum`: the `ℓ^p ⊆ ℓ¹`
  comparison of the two depth sums.
* `isBigO_gammaSigma_cubeDepthPthMoment_shell`: the `Γ_{2/p}` tail of one
  depth moment of one shell.
* `isBigO_gammaSigma_rpow_cubeDepthPthMoment_shell`: the same in rooted form,
  a `Γ₂` tail at amplitude `cubeDepthMomentTailConst d p * 3^{-(d/2)((h-k)∨0)}`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## The rank-one gradient pairing as a vector dot product

The negative-norm development of the CoarseGraining library pairs a field against a
smooth *vector* test field through `Homogenization.vecDot`
(`Homogenization.cubeEuclideanNormalizedSmoothPairing`), while the
rank-one gradient density used here is written with `fderiv`. The two are the same
expression once the derivative is resolved on the coordinate basis; the lemmas below
record that, and they hold for every `g`, differentiable or not, because
`fderiv ℝ g x` is a continuous linear map in either case. -/

/-- Every value of a Fréchet derivative of a scalar field on `Vec d` is the dot
product of the direction with the vector of partial derivatives, in the
repo-wide convention `fderiv ℝ g x (Pi.single i 1)` for `∂_i g`. -/
theorem fderiv_eq_vecDot_partialDeriv (g : Vec d → ℝ) (x w : Vec d) :
    fderiv ℝ g x w = vecDot w (fun i ↦ fderiv ℝ g x (Pi.single i 1)) := by
  have hdecomp : w = ∑ i : Fin d, w i • (Pi.single i 1 : Vec d) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    fderiv ℝ g x w = fderiv ℝ g x (∑ i : Fin d, w i • (Pi.single i 1 : Vec d)) := by
      rw [← hdecomp]
    _ = ∑ i : Fin d, w i * fderiv ℝ g x (Pi.single i 1) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
    _ = vecDot w (fun i ↦ fderiv ℝ g x (Pi.single i 1)) := rfl

/-- The rank-one gradient density is the dot product of the row vector
`v ᵥ* M x` with the gradient of `g`. -/
theorem matGradientPairingDensity_eq_vecDot (M : Vec d → Mat d) (v : Vec d)
    (g : Vec d → ℝ) (x : Vec d) :
    matGradientPairingDensity M v g x =
      vecDot (Matrix.vecMul v (M x)) (fun i ↦ fderiv ℝ g x (Pi.single i 1)) :=
  fderiv_eq_vecDot_partialDeriv g x (Matrix.vecMul v (M x))

/-! ## Descendant averages as translated centred cube averages -/

/-- The volume average of a matrix field over a triadic cube is the average of
its translate over the centred cube of the same scale. -/
theorem volumeAverageMat_cubeSet_eq_cubeAverageMat_originCube
    (R : TriadicCube d) (M : Vec d → Mat d) :
    volumeAverageMat (cubeSet R) M =
      cubeAverageMat (originCube d R.scale) (fun x ↦ M (x + triadicCubeShift R)) := by
  ext i k
  have hset : cubeSet R =
      translateSet (triadicCubeShift R) (cubeSet (originCube d R.scale)) :=
    cubeSet_eq_translateSet_originCube_of_triadicCube R
  have hint := setIntegral_comp_addRight_translateSet (d := d) (E := ℝ)
    (triadicCubeShift R) (cubeSet (originCube d R.scale)) (fun x ↦ M x i k)
  simp only [volumeAverageMat, volumeAverage, cubeAverageMat, cubeAverage]
  rw [hset, volume_translateSet_eq, volume_cubeSet_toReal, ← hint]

/-- The average of one shell over a triadic cube is the translated-cube
carrier at the scale and centre of that cube. -/
theorem volumeAverageMat_cubeSet_eq_shellSpatialAverage
    (R : TriadicCube d) (jf : ShellField d) :
    volumeAverageMat (cubeSet R) (fun x ↦ jf x) =
      shellSpatialAverage R.scale (triadicCubeShift R) jf :=
  volumeAverageMat_cubeSet_eq_cubeAverageMat_originCube R (fun x ↦ jf x)

/-! ## The depth moments -/

/-- The depth-`j` normalized `p`-th moment of the sub-cube averages of a matrix
field: the average of `‖(M)_R‖^p` over the `3^{dj}` triadic descendants `R` of
`Q` at depth `j`, that is over the sub-cubes of scale `Q.scale - j`. -/
def cubeDepthPthMoment (Q : TriadicCube d) (j : ℕ) (p : ℝ)
    (M : Vec d → Mat d) : ℝ :=
  ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
    ((descendantsAtDepth Q j).sum fun R ↦ ‖volumeAverageMat (cubeSet R) M‖ ^ p)

theorem cubeDepthPthMoment_nonneg (Q : TriadicCube d) (j : ℕ) (p : ℝ)
    (M : Vec d → Mat d) : 0 ≤ cubeDepthPthMoment Q j p M := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun R _ ↦ ?_)
  exact Real.rpow_nonneg (norm_nonneg _) p

/-- One summand of the depth moment of a shell is measurable in the sample. -/
theorem measurable_matrixOperatorNorm_rpow_volumeAverageMat_shell
    (R : TriadicCube d) (k : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    Measurable (fun omega : ℕ → ShellField d ↦
      ‖volumeAverageMat (cubeSet R) (fun x ↦ omega k x)‖ ^ p) := by
  have hmat : Measurable (fun omega : ℕ → ShellField d ↦
      shellSpatialAverage R.scale (triadicCubeShift R) (omega k)) :=
    (measurable_translatedShellCubeAverage (triadicCubeShift R)
      (originCube d R.scale)).comp (ShellField.measurable_shellCoordinate k)
  have hnorm : Measurable (fun omega : ℕ → ShellField d ↦
      matrixOperatorNorm (shellSpatialAverage R.scale (triadicCubeShift R)
        (omega k))) :=
    ShellField.continuous_matrixOperatorNorm.measurable.comp hmat
  simp only [volumeAverageMat_cubeSet_eq_shellSpatialAverage]
  exact (Real.continuous_rpow_const hp).measurable.comp hnorm

theorem measurable_cubeDepthPthMoment_shell (Q : TriadicCube d) (j k : ℕ)
    {p : ℝ} (hp : 0 ≤ p) :
    Measurable (fun omega : ℕ → ShellField d ↦
      cubeDepthPthMoment Q j p (fun x ↦ omega k x)) := by
  classical
  refine measurable_const.mul (Finset.measurable_sum _ fun R _ ↦ ?_)
  exact measurable_matrixOperatorNorm_rpow_volumeAverageMat_shell R k hp

/-! ## The two depth sums -/

/-- The marginal transcription of the upstream running-scale depth energy
`Homogenization.cubeEuclideanNegativeBesovDepthEnergy`: the weight
`3^{s p (Q.scale - j)}` times the depth-`j` moment. -/
def cubeDepthEnergy (Q : TriadicCube d) (s p : ℝ) (M : Vec d → Mat d)
    (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (s * p * (((Q.scale - (j : ℤ) : ℤ) : ℝ)))) *
    ENNReal.ofReal (cubeDepthPthMoment Q j p M)

/-- The `ℓ^p`-rooted depth sum, the shape of
`Homogenization.cubeEuclideanNegativeBesovESeminorm`. -/
def cubeNegativeBesovDepthENorm (Q : TriadicCube d) (s p : ℝ)
    (M : Vec d → Mat d) : ℝ≥0∞ :=
  (∑' j : ℕ, cubeDepthEnergy Q s p M j) ^ p⁻¹

/-- The printed `ℓ¹` depth sum of `e.apply.multiscale.Poincare`, indexed by the
depth `j = Q.scale - h` and normalized so that the printed prefactor `3^{-sl}`
has already been applied. -/
def cubeMultiscaleDepthSum (Q : TriadicCube d) (s p : ℝ)
    (M : Vec d → Mat d) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s * (j : ℝ)))) *
    cubeDepthPthMoment Q j p M ^ p⁻¹)

/-! ### The `ℓ^p ⊆ ℓ¹` comparison -/

private theorem ennreal_finset_sum_rpow_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (a : ℕ → ℝ≥0∞) (t : Finset ℕ) :
    (∑ i ∈ t, a i) ^ r ≤ ∑ i ∈ t, a i ^ r := by
  classical
  induction t using Finset.induction with
  | empty => simp [ENNReal.zero_rpow_of_pos hr0]
  | insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact le_trans (ENNReal.rpow_add_le_add_rpow _ _ hr0.le hr1)
        (add_le_add le_rfl ih)

private theorem ennreal_tsum_rpow_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (a : ℕ → ℝ≥0∞) :
    (∑' i : ℕ, a i) ^ r ≤ ∑' i : ℕ, a i ^ r := by
  classical
  have hkey : ∑' i : ℕ, a i ≤ (∑' i : ℕ, a i ^ r) ^ r⁻¹ := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun t ↦ ?_
    have h1 : (∑ i ∈ t, a i) ^ r ≤ ∑' i : ℕ, a i ^ r :=
      le_trans (ennreal_finset_sum_rpow_le hr0 hr1 a t) (ENNReal.sum_le_tsum t)
    have h2 := ENNReal.rpow_le_rpow h1 (le_of_lt (inv_pos.2 hr0))
    rwa [ENNReal.rpow_rpow_inv (ne_of_gt hr0)] at h2
  have h3 := ENNReal.rpow_le_rpow hkey hr0.le
  rwa [ENNReal.rpow_inv_rpow (ne_of_gt hr0)] at h3

/-- The upstream `ℓ^p`-rooted depth sum is dominated by the printed `ℓ¹` depth
sum, at the cost of the factor `3^{s (Q.scale)}` which the printed display
carries as its prefactor `3^{-sl}` on the other side.

This is the step the upstream library does not carry: its negative Besov
seminorm roots the depth sum only at the end, whereas the manuscript sums the
rooted depth terms. -/
theorem cubeNegativeBesovDepthENorm_le_cubeMultiscaleDepthSum
    (Q : TriadicCube d) {s p : ℝ} (hp : 1 ≤ p)
    (M : Vec d → Mat d) :
    cubeNegativeBesovDepthENorm Q s p M ≤
      ENNReal.ofReal ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ))) *
        cubeMultiscaleDepthSum Q s p M := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hr0 : (0 : ℝ) < p⁻¹ := inv_pos.2 hp0
  have hr1 : p⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hp
  have hterm : ∀ j : ℕ, cubeDepthEnergy Q s p M j ^ p⁻¹ =
      ENNReal.ofReal ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ))) *
        ENNReal.ofReal (((3 : ℝ) ^ (-(s * (j : ℝ)))) *
          cubeDepthPthMoment Q j p M ^ p⁻¹) := by
    intro j
    have hmom : 0 ≤ cubeDepthPthMoment Q j p M := cubeDepthPthMoment_nonneg Q j p M
    have hpow : (0 : ℝ) ≤ (3 : ℝ) ^ (s * p * (((Q.scale - (j : ℤ) : ℤ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hexp : s * p * (((Q.scale - (j : ℤ) : ℤ) : ℝ)) * p⁻¹ =
        s * ((Q.scale : ℤ) : ℝ) + -(s * (j : ℝ)) := by
      push_cast
      field_simp
      ring
    have hreal : ((3 : ℝ) ^ (s * p * (((Q.scale - (j : ℤ) : ℤ) : ℝ)))) ^ p⁻¹ *
        cubeDepthPthMoment Q j p M ^ p⁻¹ =
        (3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ)) *
          (((3 : ℝ) ^ (-(s * (j : ℝ)))) * cubeDepthPthMoment Q j p M ^ p⁻¹) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hexp,
        Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring
    rw [cubeDepthEnergy, ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
      ENNReal.ofReal_rpow_of_nonneg hpow hr0.le,
      ENNReal.ofReal_rpow_of_nonneg hmom hr0.le,
      ← ENNReal.ofReal_mul (by positivity), hreal,
      ENNReal.ofReal_mul (by positivity)]
  calc
    cubeNegativeBesovDepthENorm Q s p M
        ≤ ∑' j : ℕ, cubeDepthEnergy Q s p M j ^ p⁻¹ :=
      ennreal_tsum_rpow_le hr0 hr1 _
    _ = ∑' j : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ))) *
          ENNReal.ofReal (((3 : ℝ) ^ (-(s * (j : ℝ)))) *
            cubeDepthPthMoment Q j p M ^ p⁻¹) := by
      exact tsum_congr hterm
    _ = ENNReal.ofReal ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ))) *
          cubeMultiscaleDepthSum Q s p M := by
      rw [cubeMultiscaleDepthSum, ENNReal.tsum_mul_left]

/-! ## The one-shell tail of a depth moment -/

/-- The amplitude of the display `e.jk.spatialavg` at the descendant
scale `Q.scale - j` of shell `k`. -/
def depthShellTailAmplitude (d : ℕ) (Q : TriadicCube d) (j k : ℕ) : ℝ :=
  spatialAverageTailConst d *
    (3 : ℝ) ^ (-((d : ℝ) / 2) * ((max (Q.scale - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ))

private theorem gammaTriangleConst_pos (sigma : ℝ) :
    0 < IndependentSums.gammaTriangleConst sigma := by
  have hg : (2 : ℝ) ≤ IndependentSums.gammaGrowthConst sigma := le_max_left _ _
  have hpos : (0 : ℝ) < IndependentSums.gammaGrowthConst sigma := by
    linarith only [hg]
  simp only [IndependentSums.gammaTriangleConst]
  positivity

theorem spatialAverageTailConst_pos (hd : 0 < d) :
    0 < spatialAverageTailConst d := by
  have hcolor : 0 ≤ spatialAverageColorConst d := spatialAverageColorConst_nonneg d
  have htri : 0 < IndependentSums.gammaTriangleConst 2 := gammaTriangleConst_pos 2
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hone : (0 : ℝ) < 1 + spatialAverageColorConst d := by linarith only [hcolor]
  simp only [spatialAverageTailConst]
  positivity

theorem depthShellTailAmplitude_pos (hd : 0 < d) (Q : TriadicCube d) (j k : ℕ) :
    0 < depthShellTailAmplitude d Q j k :=
  mul_pos (spatialAverageTailConst_pos hd) (Real.rpow_pos_of_pos (by norm_num) _)

/-- **The `Γ_{2/p}` tail of one depth moment of one shell.** The depth-`j`
moment of shell `k` on `Q` is a normalized average, over the triadic
descendants of `Q` at depth `j`, of the `p`-th powers of translated cube
averages of the shell; each of those has the `e.jk.spatialavg` tail
`isBigOWith_gammaSigma_matrixOperatorNorm_shellSpatialAverage` at amplitude
`depthShellTailAmplitude d Q j k`, so the `p`-th powers have `Γ_{2/p}` tails at
the `p`-th power of that amplitude, and the average is closed under the finite
triangle inequality at index `2/p`.

The inputs are exactly those of the display: the prefix, J1, J3
and the negation half of J4. -/
theorem isBigO_gammaSigma_cubeDepthPthMoment_shell
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (k : ℕ) (Q : TriadicCube d) (j : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 / p))
      (fun omega : ℕ → ShellField d ↦
        cubeDepthPthMoment Q j p (fun x ↦ omega k x))
      (IndependentSums.gammaTriangleConst (2 / p) *
        depthShellTailAmplitude d Q j k ^ p) := by
  classical
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hA : 0 < depthShellTailAmplitude d Q j k :=
    depthShellTailAmplitude_pos hd Q j k
  have hAp : (0 : ℝ) < depthShellTailAmplitude d Q j k ^ p :=
    Real.rpow_pos_of_pos hA p
  have hne : (descendantsAtDepth Q j).Nonempty := descendantsAtDepth_nonempty Q j
  have hX : ∀ R ∈ descendantsAtDepth Q j,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 / p))
        (fun omega : ℕ → ShellField d ↦
          ‖volumeAverageMat (cubeSet R) (fun x ↦ omega k x)‖ ^ p)
        (depthShellTailAmplitude d Q j k ^ p) := by
    intro R hR
    have hscale : R.scale = Q.scale - (j : ℤ) :=
      scale_eq_sub_of_mem_descendantsAtDepth hR
    have hbase := isBigOWith_gammaSigma_matrixOperatorNorm_shellSpatialAverage
      hPrefix hJ1 hJ3 hJ4 k R.scale (triadicCubeShift R)
    have hroot : IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma 2)
        (fun omega : ℕ → ShellField d ↦
          ‖volumeAverageMat (cubeSet R) (fun x ↦ omega k x)‖)
        (depthShellTailAmplitude d Q j k) := by
      rw [← SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (fun omega ↦ by
          rw [volumeAverageMat_cubeSet_eq_shellSpatialAverage]
          exact matrixOperatorNorm_nonneg _)]
      simp only [volumeAverageMat_cubeSet_eq_shellSpatialAverage, hscale,
        depthShellTailAmplitude] at hbase ⊢
      exact hbase
    have hpow := SuperdiffusionCLT.Probability.isBigO_gammaSigma_rpow_fwd
      (mu := P.toMeasure)
      (X := fun omega : ℕ → ShellField d ↦
        ‖volumeAverageMat (cubeSet R) (fun x ↦ omega k x)‖)
      (K := depthShellTailAmplitude d Q j k) (σ := 2) (p := p) hp0 hA.le
      (fun omega ↦ norm_nonneg _) hroot
    simpa using hpow
  have hXm : ∀ R ∈ descendantsAtDepth Q j,
      Measurable (fun omega : ℕ → ShellField d ↦
        ‖volumeAverageMat (cubeSet R) (fun x ↦ omega k x)‖ ^ p) :=
    fun R _ ↦ measurable_matrixOperatorNorm_rpow_volumeAverageMat_shell R k hp0.le
  have htri := Book.Ch04.isBigO_finsetAverage_of_isBigO_gammaSigma
    (μ := P.toMeasure) (descendantsAtDepth Q j)
    (X := fun R (omega : ℕ → ShellField d) ↦
      ‖volumeAverageMat (cubeSet R) (fun x ↦ omega k x)‖ ^ p)
    (a := fun _ : TriadicCube d ↦ depthShellTailAmplitude d Q j k ^ p)
    (σ := 2 / p) (by positivity) hne (fun _ _ ↦ hAp) hX hXm
  have hconst : (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
      Finset.sum (descendantsAtDepth Q j)
        (fun _ : TriadicCube d ↦ depthShellTailAmplitude d Q j k ^ p) =
      depthShellTailAmplitude d Q j k ^ p := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (((descendantsAtDepth Q j).card : ℝ)) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero_of_mem hne.choose_spec
    field_simp
  rw [hconst] at htri
  exact htri

/-- The explicit constant of the rooted one-shell depth tail: the `p`-th root
of the finite triangle constant at index `2/p`, times the constant of the
display `e.jk.spatialavg`. -/
def cubeDepthMomentTailConst (d : ℕ) (p : ℝ) : ℝ :=
  IndependentSums.gammaTriangleConst (2 / p) ^ p⁻¹ * spatialAverageTailConst d

theorem cubeDepthMomentTailConst_pos (hd : 0 < d) (p : ℝ) :
    0 < cubeDepthMomentTailConst d p :=
  mul_pos (Real.rpow_pos_of_pos (gammaTriangleConst_pos _) _)
    (spatialAverageTailConst_pos hd)

/-- **The rooted one-shell depth tail.** The `p`-th root of the depth-`j`
moment of shell `k` on `Q` has a symmetric `Γ₂` tail at amplitude
`cubeDepthMomentTailConst d p * 3 ^ (-(d/2) ((Q.scale - j - k) ∨ 0))`.

This is the summand of `cubeMultiscaleDepthSum` at depth `j`, before the
geometric weight `3^{-sj}`, and it is the form in which the depth terms enter
the shell sums: the tail index is `2`, as in the display, and the
amplitude is the amplitude of the display times a constant depending only on `p`. -/
theorem isBigO_gammaSigma_rpow_cubeDepthPthMoment_shell
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (k : ℕ) (Q : TriadicCube d) (j : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        cubeDepthPthMoment Q j p (fun x ↦ omega k x) ^ p⁻¹)
      (cubeDepthMomentTailConst d p *
        (3 : ℝ) ^ (-((d : ℝ) / 2) *
          ((max (Q.scale - (j : ℤ) - (k : ℤ)) 0 : ℤ) : ℝ))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hA : 0 < depthShellTailAmplitude d Q j k :=
    depthShellTailAmplitude_pos hd Q j k
  have htri : 0 < IndependentSums.gammaTriangleConst (2 / p) :=
    gammaTriangleConst_pos (2 / p)
  set K : ℝ := IndependentSums.gammaTriangleConst (2 / p) ^ p⁻¹ *
    depthShellTailAmplitude d Q j k with hKdef
  have hK : 0 ≤ K := by
    exact le_of_lt (mul_pos (Real.rpow_pos_of_pos htri _) hA)
  have hKp : K ^ p = IndependentSums.gammaTriangleConst (2 / p) *
      depthShellTailAmplitude d Q j k ^ p := by
    rw [hKdef, Real.mul_rpow (Real.rpow_nonneg htri.le _) hA.le,
      ← Real.rpow_mul htri.le, inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]
  have hbase := isBigO_gammaSigma_cubeDepthPthMoment_shell hPrefix hJ1 hJ3 hJ4
    k Q j hp
  rw [← hKp] at hbase
  have hpow : ∀ omega : ℕ → ShellField d,
      (cubeDepthPthMoment Q j p (fun x ↦ omega k x) ^ p⁻¹) ^ p =
        cubeDepthPthMoment Q j p (fun x ↦ omega k x) := by
    intro omega
    rw [← Real.rpow_mul (cubeDepthPthMoment_nonneg Q j p _),
      inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]
  have hbase' : IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma (2 / p))
      (fun omega : ℕ → ShellField d ↦
        (cubeDepthPthMoment Q j p (fun x ↦ omega k x) ^ p⁻¹) ^ p) (K ^ p) := by
    simpa only [hpow] using hbase
  have hres := SuperdiffusionCLT.Probability.isBigO_gammaSigma_rpow_rev
    (mu := P.toMeasure)
    (X := fun omega : ℕ → ShellField d ↦
      cubeDepthPthMoment Q j p (fun x ↦ omega k x) ^ p⁻¹)
    (K := K) (σ := 2) (p := p) hp0 hK
    (fun omega ↦ Real.rpow_nonneg (cubeDepthPthMoment_nonneg Q j p _) _) hbase'
  simpa only [hKdef, cubeDepthMomentTailConst, depthShellTailAmplitude,
    mul_assoc] using hres

end

end Norms
end Section2
end SuperdiffusionCLT
