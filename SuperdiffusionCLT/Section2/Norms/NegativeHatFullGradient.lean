/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section2.Norms.MultiscalePoincare
public import Homogenization.Sobolev.Fractional.EuclideanWspSmoothDual

/-!
# The hatted negative fractional norms of a matrix field

The paper defines the hatted negative seminorm at order one by duality against
smooth mean-zero test functions and adds that for vector fields the pairing is against
gradients; it constrains `‖∇g‖_{L̲^p(U)}`, that is the *gradient field*.  The estimate
bounding `p · ⨍_{cu_m} (k_{ℓ'} − k_ℓ) ∇w` by
`‖(k_{ℓ'} − k_ℓ) p‖_{Ĥ̲^{-1/2}(cu_m)} ‖∇w‖_{H̲^{1/2}(cu_m)}` again uses a full
norm of the gradient field.

The formalization reads the hatted negative norm accordingly:

> for `s ∈ (0,1)` and `1 < p < ∞`, the order-`s` hatted negative norm of a
> matrix field `M` on a cube `Q` is the supremum of `⨍_Q ⟨M, v ⊗ G⟩` over
> `|v| ≤ 1` and smooth mean-zero-potential vector fields `G = ∇g` on `Q` whose
> normalized full `W̲^{s,p'}(Q)` norm is at most one.

The rank-one gradient class `v ⊗ ∇g` is the one of `Section2/Norms/NegativeHat.lean`, so the pairing
density is the one already carried by
`SuperdiffusionCLT.Section2.Norms.matGradientPairingDensity`.

This module refines `Section2/Norms/NegativeHat.lean`: the constraint is placed on
the vector field `∇g` rather than on the scalar potential `g`, and on the full norm
rather than a seminorm.

## The full norm of the gradient field

`vecCubeEuclideanWspFullENorm Q s q F` is the transcription of
`Homogenization.cubeEuclideanWspFullENorm`, written on the Gagliardo and
`L̲^q` carriers of this directory rather than on the bundled
`FractionalOrder`/`FiniteLpExponent` arguments:

`(3^{-s l q} ‖F‖_{L̲^q(Q)}^q + [F]_{W̲^{s,q}(Q)}^q)^{1/q}`,

the vector length being the Euclidean one throughout, carried by
`Homogenization.HilbertVec.ofVec`.
`vecCubeEuclideanWspFullENorm_eq_cubeEuclideanWspFullENorm` proves that the two
agree exactly, so the packaging constant between this class and the
smooth unit-test class of the CoarseGraining library is `1`.

## Values of the norms

**The norm is valued in `ℝ≥0∞` as a supremum of a nonempty family, and `⊤` is
a legitimate outcome**: the zero test field is always admissible, so the
supremum is a genuine supremum of a nonempty set of extended reals and never a
`Real.sSup` junk value. The finiteness facts that keep the Bochner branch of the
pairing unreachable are the ones already proved for the shared density in
`Section2/Norms/NegativeHat.lean`.

## Main definitions

* `vecGradient`: `∇g`, in the repo convention `(∇g)_i = ∂_i g`.
* `vecCubeEuclideanWspFullENorm`: the normalized full `W̲^{s,q}(Q)` norm of a
  vector field.
* `IsHatTestField`: the admissible test potentials.
* `matHatNegENorm`: `‖M‖_{Ŵ̲^{-s,p}(Q)}`.
* `rowLpField`: the row field `x ↦ v ᵥ* M x` of a continuous matrix field, as
  an `L²` cube field of the CoarseGraining library.

## Main results

* `le_matHatNegENorm`, `matHatNegENorm_le`: the supremum characterization.
* `vecCubeEuclideanWspFullENorm_eq_cubeEuclideanWspFullENorm`: the packaging
  identity with the CoarseGraining library's full norm.
* `IsHatTestField.toSmoothUnitTest`: every admissible potential
  has a gradient in the smooth unit-test class of the CoarseGraining library, with
  constant `1`.
* `cubeEuclideanNormalizedSmoothPairing_eq_volumeAverage`: the rank-one
  pairing density integrates to the library's `vecDot` pairing.
* `matHatNegENorm_le_iSup_cubeEuclideanNegativeWspSmoothDualENorm`: the
  norm of a continuous matrix field is dominated by the library's
  smooth-dual norms of its row fields.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The gradient field -/

/-- `∇g`, in the repo convention `(∇g)_i = ∂_i g = fderiv ℝ g x (Pi.single i 1)`.
No differentiability is assumed: `fderiv ℝ g x` is a continuous linear map in
every case. -/
noncomputable def vecGradient (g : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => fderiv ℝ g x (Pi.single i 1)

@[simp] theorem vecGradient_zero :
    vecGradient (fun _ : Vec d => (0 : ℝ)) = 0 := by
  funext x i
  simp [vecGradient]

theorem contDiff_vecGradient {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (vecGradient g) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => fderiv ℝ g x) :=
    hg.fderiv_right (by simp)
  exact contDiff_pi.2 fun i => hfd.clm_apply contDiff_const

/-- The rank-one gradient density, written against the gradient field. -/
theorem matGradientPairingDensity_eq_vecDot_vecGradient (M : Vec d → Mat d)
    (v : Vec d) (g : Vec d → ℝ) (x : Vec d) :
    matGradientPairingDensity M v g x =
      vecDot (Matrix.vecMul v (M x)) (vecGradient g x) :=
  matGradientPairingDensity_eq_vecDot M v g x

/-! ## The full fractional norm of a vector field -/

/-- The normalized full `W̲^{s,q}(Q)` norm of a vector field, the quantity
bounded on the test gradient field. -/
noncomputable def vecCubeEuclideanWspFullENorm (Q : TriadicCube d) (s : ℝ)
    (q : ℝ≥0∞) (F : Vec d → Vec d) : ℝ≥0∞ :=
  (ENNReal.ofReal (cubeScaleFactor Q) ^ (-s * q.toReal) *
        cubeLpENorm Q q (fun x => HilbertVec.ofVec (F x)) ^ q.toReal +
      cubeEuclideanGagliardoESeminorm Q s q
          (fun x => HilbertVec.ofVec (F x)) ^ q.toReal) ^
    (q.toReal)⁻¹

/-- The packaging identity: the full norm of a vector field defined here is the
`Homogenization.cubeEuclideanWspFullENorm` of the same field, with no
constant. -/
theorem vecCubeEuclideanWspFullENorm_eq_cubeEuclideanWspFullENorm
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d)
    (hF : MeasureTheory.AEStronglyMeasurable (fun x => HilbertVec.ofVec (F x))
      (normalizedCubeMeasure Q)) :
    vecCubeEuclideanWspFullENorm Q s.1 p.exponent F =
      cubeEuclideanWspFullENorm Q s p F := by
  have hLp : cubeLpENorm Q p.exponent (fun x => HilbertVec.ofVec (F x)) =
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
        p.exponent F := by
    rw [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      cubeLpENorm]
    simp only [euclideanNorm_eq_norm_ofVec]
    exact (eLpNorm_norm _ hF).symm
  have hGag : cubeEuclideanGagliardoESeminorm Q s.1 p.exponent
      (fun x => HilbertVec.ofVec (F x)) =
      cubeEuclideanWspESeminorm Q s p F := by
    rw [cubeEuclideanGagliardoESeminorm, cubeEuclideanWspESeminorm]
    congr 1
  rw [vecCubeEuclideanWspFullENorm, cubeEuclideanWspFullENorm,
    cubeEuclideanWspScalePowerWeight, hLp, hGag]

/-! ## The test class -/

/-- The admissible test potentials: smooth, with
vanishing average on the cube, and with the normalized full `W̲^{s,q}(Q)` norm
of the gradient field at most one, `q` the conjugate exponent. The smoothness
is global smoothness on `Vec d`, so that `fderiv` is a genuine derivative at
every point of the cube. -/
structure IsHatTestField (Q : TriadicCube d) (s : ℝ) (q : ℝ≥0∞)
    (g : Vec d → ℝ) : Prop where
  /-- `g ∈ C^∞`. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) g
  /-- `(g)_U = 0`. -/
  meanZero : volumeAverage (cubeSet Q) g = 0
  /-- `‖∇g‖_{W̲^{s,q}(U)} ≤ 1`, the constraint on the gradient field. -/
  fullENorm_le_one :
    vecCubeEuclideanWspFullENorm Q s q (vecGradient g) ≤ 1

/-! ## The two norms -/

/-- `‖M‖_{Ŵ̲^{-s,p}(Q)}`:
the supremum of the volume-normalized rank-one gradient pairing over unit
vectors `v` and admissible test potentials at the conjugate exponent `p'`. -/
noncomputable def matHatNegENorm (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (M : Vec d → Mat d) : ℝ≥0∞ :=
  ⨆ v : Vec d, ⨆ _ : vecNorm v ≤ 1, ⨆ g : Vec d → ℝ,
    ⨆ _ : IsHatTestField Q s (ENNReal.conjExponent p) g,
      ENNReal.ofReal
        (volumeAverage (cubeSet Q) (matGradientPairingDensity M v g))

theorem le_matHatNegENorm {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞}
    (M : Vec d → Mat d) {v : Vec d} (hv : vecNorm v ≤ 1) {g : Vec d → ℝ}
    (hg : IsHatTestField Q s (ENNReal.conjExponent p) g) :
    ENNReal.ofReal
        (volumeAverage (cubeSet Q) (matGradientPairingDensity M v g)) ≤
      matHatNegENorm Q s p M :=
  le_iSup_of_le v (le_iSup_of_le hv (le_iSup_of_le g (le_iSup_of_le hg le_rfl)))

theorem matHatNegENorm_le {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞}
    {M : Vec d → Mat d} {c : ℝ≥0∞}
    (h : ∀ v : Vec d, vecNorm v ≤ 1 → ∀ g : Vec d → ℝ,
      IsHatTestField Q s (ENNReal.conjExponent p) g →
        ENNReal.ofReal
            (volumeAverage (cubeSet Q) (matGradientPairingDensity M v g)) ≤ c) :
    matHatNegENorm Q s p M ≤ c :=
  iSup_le fun v => iSup_le fun hv => iSup_le fun g => iSup_le fun hg =>
    h v hv g hg

/-! ## The seminorm laws -/

/-! ## The comparison with the smooth-dual chain -/

theorem continuous_vecMul {M : Vec d → Mat d} (hM : Continuous M) (v : Vec d) :
    Continuous (fun x : Vec d => Matrix.vecMul v (M x)) := by
  refine continuous_pi fun j => ?_
  have hsum : Continuous (fun x : Vec d => ∑ i, v i * M x i j) :=
    continuous_finsetSum Finset.univ fun i _ =>
      continuous_const.mul
        ((continuous_apply j).comp ((continuous_apply i).comp hM))
  simpa [Matrix.vecMul, dotProduct, Matrix.transpose] using hsum

/-- The row field `x ↦ v ᵥ* M x` of a continuous matrix field, as a
Euclidean `L²` cube field. -/
noncomputable def rowLpField (Q : TriadicCube d) {M : Vec d → Mat d}
    (hM : Continuous M) (v : Vec d) :
    CubeEuclideanLpField Q FiniteLpExponent.two where
  toField := fun x => Matrix.vecMul v (M x)
  euclideanMemLp := by
    simpa only [FiniteLpExponent.two_exponent] using
      CubeEuclideanWspSmoothTest.euclideanMemLp_of_continuous Q 2
        (continuous_vecMul hM v)

@[simp] theorem rowLpField_toField (Q : TriadicCube d) {M : Vec d → Mat d}
    (hM : Continuous M) (v : Vec d) (x : Vec d) :
    (rowLpField Q hM v).toField x = Matrix.vecMul v (M x) :=
  rfl

/-- The gradient of an admissible test potential is a smooth test
field in the unit ball of the full normalized fractional norm: the test
class sits inside the smooth unit-test class with packaging constant `1`. -/
noncomputable def IsHatTestField.toSmoothUnitTest {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} {g : Vec d → ℝ}
    (hg : IsHatTestField Q s.1 p.exponent g) :
    CubeEuclideanWspSmoothUnitTest Q s p :=
  ⟨{ toField := vecGradient g
     contDiff := contDiff_vecGradient hg.contDiff },
    by
      rw [← vecCubeEuclideanWspFullENorm_eq_cubeEuclideanWspFullENorm Q s p (vecGradient g)
        ((HilbertVec.ofVecL d).continuous.comp
          (contDiff_vecGradient hg.contDiff).continuous).aestronglyMeasurable]
      exact hg.fullENorm_le_one⟩

@[simp] theorem IsHatTestField.toSmoothUnitTest_toField {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} {g : Vec d → ℝ}
    (hg : IsHatTestField Q s.1 p.exponent g) :
    (hg.toSmoothUnitTest).1.toField = vecGradient g :=
  rfl

/-- The volume-normalized rank-one gradient pairing is the normalized
`vecDot` pairing of the row field with the gradient field. -/
theorem cubeEuclideanNormalizedSmoothPairing_eq_volumeAverage
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p) (M : Vec d → Mat d) (v : Vec d)
    (g : Vec d → ℝ) (hF : ∀ x, F.toField x = Matrix.vecMul v (M x))
    (hh : ∀ x, h.toField x = vecGradient g x) :
    cubeEuclideanNormalizedSmoothPairing F h =
      volumeAverage (cubeSet Q) (matGradientPairingDensity M v g) := by
  have hpt : ∀ x : Vec d, vecDot (F.toField x) (h.toField x) =
      matGradientPairingDensity M v g x := by
    intro x
    rw [hF x, hh x, matGradientPairingDensity_eq_vecDot_vecGradient]
  rw [cubeEuclideanNormalizedSmoothPairing]
  simp only [hpt]
  rw [normalizedCubeMeasure, cubeMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (cubeVolume_pos Q))),
    volumeAverage, volume_cubeSet_toReal, smul_eq_mul]

/-- The hatted negative norm of a continuous matrix field is dominated
by the smooth-dual norms of its row fields, with constant `1`. This is
the junction the multiscale Poincaré chain of
`Homogenization.cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm`
needs. -/
theorem matHatNegENorm_le_iSup_cubeEuclideanNegativeWspSmoothDualENorm
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    {M : Vec d → Mat d} (hM : Continuous M) :
    matHatNegENorm Q s.1 p.exponent M ≤
      ⨆ v : Vec d, ⨆ _ : vecNorm v ≤ 1,
        cubeEuclideanNegativeWspSmoothDualENorm Q s p (rowLpField Q hM v) := by
  refine matHatNegENorm_le fun v hv g hg => ?_
  have hgc : IsHatTestField Q s.1 p.conjugate.exponent g := hg
  have hpair :
      cubeEuclideanNormalizedSmoothPairing (rowLpField Q hM v)
          (hgc.toSmoothUnitTest (p := p.conjugate)).1 =
        volumeAverage (cubeSet Q) (matGradientPairingDensity M v g) :=
    cubeEuclideanNormalizedSmoothPairing_eq_volumeAverage _ _ M v g
      (fun x => rfl) (fun x => rfl)
  refine le_iSup_of_le v (le_iSup_of_le hv ?_)
  refine le_trans ?_
    (le_iSup (fun u : CubeEuclideanWspSmoothUnitTest Q s p.conjugate =>
      ENNReal.ofReal
        |cubeEuclideanNormalizedSmoothPairing (rowLpField Q hM v) u.1|)
      (hgc.toSmoothUnitTest (p := p.conjugate)))
  rw [hpair]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

end

end Norms
end Section2
end SuperdiffusionCLT
