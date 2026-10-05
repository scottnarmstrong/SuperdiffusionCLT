/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import Homogenization.Book.Ch02.Dilation

/-!
# The triadic dilation law of the normalized fractional norm `‖·‖_{H̲^s}`

The display `e.abstract.response.Hhalf` of the paper is stated on the cube `cu_M`,
while Step 2 of the proof obtains it by interpolating the `L²` and `H¹` estimates,
which the formalization performs on the unit centered cube `originCube d 0`.
The passage between the two scales is the dilation `x ↦ 3^M x`, and this module
records exactly what each of the two pieces of

> `‖f‖²_{H̲^s(cu_l)} = (3^{-sl} ‖f‖_{L̲²(cu_l)})² + [f]²_{H̲^s(cu_l)}`

(the scale-weighted definition of the normalized norm) does under it.

## The two factors

Write `δ_k x = 3^k x` and let `Q ↦ 3^k Q` be `Homogenization.Book.Ch02.dilateCube`.

* The normalized cube measure is a probability measure and is *carried* by
  `δ_k`, so the `L̲^q` piece is invariant:
  `‖f‖_{L̲^q(3^k Q)} = ‖f ∘ δ_k‖_{L̲^q(Q)}`.
* The Gagliardo piece is taken against
  `gagliardoCubeMeasure Q = (normalizedCubeMeasure Q).prod (cubeMeasure Q)`,
  whose second slot is *not* normalized and therefore contributes `3^{kd}`,
  while the kernel `|x − y|^{-(s + d/q)}` contributes `3^{-k(s + d/q)}`. At the
  exponent `q` the two combine to `3^{kd/q} · 3^{-k(s + d/q)} = 3^{-ks}`:
  `[f]_{W̲^{s,q}(3^k Q)} = 3^{-ks} [f ∘ δ_k]_{W̲^{s,q}(Q)}`.
* The scale weight in the definition of the norm satisfies
  `3^{-s(l+k)} = 3^{-ks} · 3^{-sl}`.

So both summands of the norm acquire the same factor `3^{-ks}`, and

> `‖f‖_{H̲^s(3^k Q)} = 3^{-ks} ‖f ∘ δ_k‖_{H̲^s(Q)}`,

which at `Q = originCube d 0`, where the weight is `1`, reads

> `‖f‖_{H̲^s(cu_M)} = 3^{-sM} ‖f ∘ δ_M‖_{H̲^s(cu_0)}`.

## Main results

* `cubeLpENorm_dilateCube`: the `L̲^q` piece is dilation invariant.
* `cubeEuclideanGagliardoESeminorm_dilateCube`: the Gagliardo piece acquires
  `3^{-ks}`.
* `cubeHsWeight_dilateCube`: the scale weight acquires `3^{-ks}`.
* `cubeHsENorm_dilateCube`, `cubeHsENorm_originCube`: the norm itself.
* `cubeHsENorm_congr_ae`: the norm only sees the field almost everywhere on the
  cube, in both of its pieces.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open Section2.Norms
open scoped ENNReal Pointwise

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The dilation `x ↦ 3^k x` as a measurable equivalence -/

/-- The dilation `x ↦ 3^k x` of `Vec d` as a measurable equivalence. -/
private def triadicDilationEquiv (d : ℕ) (k : ℤ) : Vec d ≃ᵐ Vec d :=
  MeasurableEquiv.smul₀ (Book.Ch02.triadicDilationFactor k)
    (Book.Ch02.triadicDilationFactor_ne_zero k)

private theorem cubeVolume_dilateCube (k : ℤ) (Q : TriadicCube d) :
    cubeVolume (Book.Ch02.dilateCube k Q) =
      Book.Ch02.triadicDilationFactor k ^ d * cubeVolume Q := by
  rw [cubeVolume_eq_scaleFactor_pow, Book.Ch02.cubeScaleFactor_dilateCube,
    mul_pow, cubeVolume_eq_scaleFactor_pow]

private theorem map_cubeMeasure_triadicDilationEquiv (k : ℤ) (Q : TriadicCube d) :
    Measure.map (triadicDilationEquiv d k) (cubeMeasure Q) =
      ENNReal.ofReal ((Book.Ch02.triadicDilationFactor k ^ d)⁻¹) •
        cubeMeasure (Book.Ch02.dilateCube k Q) := by
  have hr : 0 < Book.Ch02.triadicDilationFactor k :=
    Book.Ch02.triadicDilationFactor_pos k
  have hT : ((triadicDilationEquiv d k : Vec d ≃ᵐ Vec d) : Vec d → Vec d) =
      fun x => Book.Ch02.triadicDilationFactor k • x := rfl
  rw [cubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    hT, map_smul_volume_restrict hr, Book.Ch02.openCubeSet_dilateCube]

private theorem measurePreserving_triadicDilationEquiv (k : ℤ) (Q : TriadicCube d) :
    MeasurePreserving (triadicDilationEquiv d k) (normalizedCubeMeasure Q)
      (normalizedCubeMeasure (Book.Ch02.dilateCube k Q)) := by
  have hr : 0 < Book.Ch02.triadicDilationFactor k :=
    Book.Ch02.triadicDilationFactor_pos k
  refine ⟨(triadicDilationEquiv d k).measurable, ?_⟩
  rw [normalizedCubeMeasure, normalizedCubeMeasure,
    Measure.map_smul _ (triadicDilationEquiv d k).measurable.aemeasurable,
    map_cubeMeasure_triadicDilationEquiv, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (cubeVolume_nonneg Q))]
  have hrpow : 0 < Book.Ch02.triadicDilationFactor k ^ d := pow_pos hr d
  rw [show (cubeVolume Q)⁻¹ * (Book.Ch02.triadicDilationFactor k ^ d)⁻¹ =
      (Book.Ch02.triadicDilationFactor k ^ d * cubeVolume Q)⁻¹ by
    field_simp, ← cubeVolume_dilateCube k Q]

private theorem gagliardoCubeMeasure_dilateCube (k : ℤ) (Q : TriadicCube d) :
    Gagliardo.gagliardoCubeMeasure (Book.Ch02.dilateCube k Q) =
      (ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) ^ d •
        Measure.map ((triadicDilationEquiv d k).prodCongr (triadicDilationEquiv d k))
          (Gagliardo.gagliardoCubeMeasure Q) := by
  have hr : 0 < Book.Ch02.triadicDilationFactor k :=
    Book.Ch02.triadicDilationFactor_pos k
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have : SFinite (cubeMeasure (Book.Ch02.dilateCube k Q)) := by
    unfold cubeMeasure
    infer_instance
  have hmap : Measure.map
      ((triadicDilationEquiv d k).prodCongr (triadicDilationEquiv d k))
      (Gagliardo.gagliardoCubeMeasure Q) =
      ENNReal.ofReal ((Book.Ch02.triadicDilationFactor k ^ d)⁻¹) •
        Gagliardo.gagliardoCubeMeasure (Book.Ch02.dilateCube k Q) := by
    change Measure.map (Prod.map (triadicDilationEquiv d k) (triadicDilationEquiv d k))
      ((normalizedCubeMeasure Q).prod (cubeMeasure Q)) = _
    rw [← Measure.map_prod_map _ _ (triadicDilationEquiv d k).measurable
        (triadicDilationEquiv d k).measurable,
      (measurePreserving_triadicDilationEquiv k Q).map_eq,
      map_cubeMeasure_triadicDilationEquiv, Measure.prod_smul_right]
    rfl
  rw [hmap, smul_smul, ← ENNReal.ofReal_pow hr.le,
    ← ENNReal.ofReal_mul (pow_pos hr d).le,
    mul_inv_cancel₀ (pow_pos hr d).ne', ENNReal.ofReal_one, one_smul]

/-! ## The two pieces of the norm under the dilation -/

omit [NormedSpace ℝ E] in
/-- The `L̲^q` piece of the normalized fractional norm is dilation invariant:
the normalized cube measure is a probability measure carried by `x ↦ 3^k x`. -/
theorem cubeLpENorm_dilateCube (k : ℤ) (Q : TriadicCube d) (q : ℝ≥0∞)
    (f : Vec d → E) :
    cubeLpENorm (Book.Ch02.dilateCube k Q) q f =
      cubeLpENorm Q q (fun x => f (Book.Ch02.dilateVec k x)) := by
  rw [cubeLpENorm, cubeLpENorm,
    ← (measurePreserving_triadicDilationEquiv k Q).map_eq,
    (triadicDilationEquiv d k).measurableEmbedding.eLpNorm_map_measure]
  rfl

/-- Pointwise covariance of the Gagliardo difference quotient under the
dilation `x ↦ 3^k x`. -/
theorem euclideanGagliardoKernel_dilate (k : ℤ) (s : ℝ) (q : ℝ≥0∞)
    (f : Vec d → E) (z : Vec d × Vec d) :
    euclideanGagliardoKernel s q f
        (Book.Ch02.dilateVec k z.1, Book.Ch02.dilateVec k z.2) =
      (Book.Ch02.triadicDilationFactor k) ^ (-(s + (d : ℝ) / q.toReal)) •
        euclideanGagliardoKernel s q
          (fun x => f (Book.Ch02.dilateVec k x)) z := by
  have hr : 0 < Book.Ch02.triadicDilationFactor k :=
    Book.Ch02.triadicDilationFactor_pos k
  rw [euclideanGagliardoKernel_apply, euclideanGagliardoKernel_apply]
  change (euclideanDist (Book.Ch02.triadicDilationFactor k • z.1)
      (Book.Ch02.triadicDilationFactor k • z.2) ^
        (-(s + (d : ℝ) / q.toReal))) • _ = _
  rw [euclideanDist_smul, abs_of_pos hr,
    Real.mul_rpow hr.le (euclideanDist_nonneg _ _), smul_smul]

/-- **The Gagliardo piece acquires exactly the factor `3^{-ks}`.** The kernel
contributes `3^{-k(s + d/q)}` and the un-normalized second slot of
`gagliardoCubeMeasure` contributes `3^{kd/q}`. -/
theorem cubeEuclideanGagliardoESeminorm_dilateCube (k : ℤ) (Q : TriadicCube d)
    (s : ℝ) {q : ℝ≥0∞} (_hq : q ≠ ⊤) (f : Vec d → E) :
    cubeEuclideanGagliardoESeminorm (Book.Ch02.dilateCube k Q) s q f =
      (ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) ^ (-s) *
        cubeEuclideanGagliardoESeminorm Q s q
          (fun x => f (Book.Ch02.dilateVec k x)) := by
  have hr : 0 < Book.Ch02.triadicDilationFactor k :=
    Book.Ch02.triadicDilationFactor_pos k
  have hR0 : ENNReal.ofReal (Book.Ch02.triadicDilationFactor k) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hr
  have hRtop : ENNReal.ofReal (Book.Ch02.triadicDilationFactor k) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hker : euclideanGagliardoKernel s q f ∘
      ((triadicDilationEquiv d k).prodCongr (triadicDilationEquiv d k)) =
      ((Book.Ch02.triadicDilationFactor k) ^
          (-(s + (d : ℝ) / q.toReal)) : ℝ) •
        euclideanGagliardoKernel s q
          (fun x => f (Book.Ch02.dilateVec k x)) := by
    funext z
    exact euclideanGagliardoKernel_dilate k s q f z
  rw [cubeEuclideanGagliardoESeminorm, cubeEuclideanGagliardoESeminorm,
    gagliardoCubeMeasure_dilateCube, eLpNorm_smul_measure_of_ne_zero (pow_ne_zero d hR0),
    ((triadicDilationEquiv d k).prodCongr
      (triadicDilationEquiv d k)).measurableEmbedding.eLpNorm_map_measure,
    hker, eLpNorm_const_smul,
    Real.enorm_eq_ofReal (Real.rpow_nonneg hr.le _),
    ← ENNReal.ofReal_rpow_of_pos hr,
    ← ENNReal.rpow_natCast (ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) d,
    ← ENNReal.rpow_mul, smul_eq_mul, ← mul_assoc,
    ← ENNReal.rpow_add _ _ hR0 hRtop]
  congr 2
  rw [one_div, ENNReal.toReal_inv, div_eq_mul_inv]
  ring

/-- The scale weight `3^{-sl}` in the definition of the norm acquires the same factor. -/
theorem cubeHsWeight_dilateCube (k : ℤ) (Q : TriadicCube d) (s : ℝ) :
    cubeHsWeight (Book.Ch02.dilateCube k Q) s =
      (ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) ^ (-s) *
        cubeHsWeight Q s := by
  have hr : 0 < Book.Ch02.triadicDilationFactor k :=
    Book.Ch02.triadicDilationFactor_pos k
  have ha : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale
  rw [cubeHsWeight, cubeHsWeight, Book.Ch02.cubeScaleFactor_dilateCube,
    Real.mul_rpow hr.le ha.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _),
    ENNReal.ofReal_rpow_of_pos hr]

/-! ## The dilation law of the norm -/

/-- **The normalized fractional norm acquires exactly the factor `3^{-ks}`
under the dilation `x ↦ 3^k x`.** Both summands of the norm acquire it, the
first through the scale weight and the second through the Gagliardo kernel. -/
theorem cubeHsENorm_dilateCube (k : ℤ) (Q : TriadicCube d) (s : ℝ)
    (f : Vec d → E) :
    cubeHsENorm (Book.Ch02.dilateCube k Q) s f =
      (ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) ^ (-s) *
        cubeHsENorm Q s (fun x => f (Book.Ch02.dilateVec k x)) := by
  have hA : ∀ x : ℝ≥0∞,
      ((ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) ^ (-s) * x) ^ (2 : ℝ) =
        ((ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) ^ (-s)) ^ (2 : ℝ) *
          x ^ (2 : ℝ) :=
    fun x => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  rw [cubeHsENorm, cubeHsENorm, cubeHsWeight_dilateCube, cubeLpENorm_dilateCube,
    cubeEuclideanGagliardoESeminorm_dilateCube k Q s (by norm_num) f, mul_assoc,
    hA, hA, ← mul_add,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2),
    ← ENNReal.rpow_mul]
  norm_num

/-- **The dilation law at the centered cubes.** With `cu_M = originCube d M`
and `δ_M x = 3^M x`, `‖f‖_{H̲^s(cu_M)} = 3^{-sM} ‖f ∘ δ_M‖_{H̲^s(cu_0)}`; the
factor `3^{-sM}` is exactly the scale weight `cubeHsWeight (cu_M) s` of the
definition, the weight of the unit cube being `1`. -/
theorem cubeHsENorm_originCube (M : ℤ) (s : ℝ) (f : Vec d → E) :
    cubeHsENorm (originCube d M) s f =
      cubeHsWeight (originCube d M) s *
        cubeHsENorm (originCube d 0) s (fun x => f (((3 : ℝ) ^ M) • x)) := by
  have hcube : Book.Ch02.dilateCube M (originCube d 0) = originCube d M := by
    simp [Book.Ch02.dilateCube, originCube]
  have hweight : cubeHsWeight (originCube d M) s =
      (ENNReal.ofReal (Book.Ch02.triadicDilationFactor M)) ^ (-s) := by
    rw [cubeHsWeight, cubeScaleFactor_originCube, Book.Ch02.triadicDilationFactor,
      ENNReal.ofReal_rpow_of_pos (zpow_pos (show (0 : ℝ) < 3 by norm_num) M)]
  rw [hweight, ← hcube, cubeHsENorm_dilateCube]
  rfl

/-! ## Almost everywhere congruence -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem ae_normalizedCubeMeasure_of_ae_restrict_openCubeSet
    {Q : TriadicCube d} {f g : Vec d → E}
    (h : f =ᵐ[volume.restrict (openCubeSet Q)] g) :
    f =ᵐ[normalizedCubeMeasure Q] g := by
  have hc : ENNReal.ofReal (cubeVolume Q)⁻¹ ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (inv_pos.2 (cubeVolume_pos Q))
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact Measure.ae_smul_measure h _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem ae_cubeMeasure_of_ae_restrict_openCubeSet
    {Q : TriadicCube d} {f g : Vec d → E}
    (h : f =ᵐ[volume.restrict (openCubeSet Q)] g) :
    f =ᵐ[cubeMeasure Q] g := by
  rwa [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- Modifying a field on a null set of the cube changes the Gagliardo
difference quotient only on a `gagliardoCubeMeasure`-null set of pairs. -/
theorem euclideanGagliardoKernel_congr_ae {Q : TriadicCube d} {s : ℝ} {q : ℝ≥0∞}
    {f g : Vec d → E} (h : f =ᵐ[volume.restrict (openCubeSet Q)] g) :
    euclideanGagliardoKernel s q f =ᵐ[Gagliardo.gagliardoCubeMeasure Q]
      euclideanGagliardoKernel s q g := by
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have h1 : (fun z : Vec d × Vec d => f z.1) =ᵐ[Gagliardo.gagliardoCubeMeasure Q]
      fun z => g z.1 := by
    rw [Gagliardo.gagliardoCubeMeasure]
    exact Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (ae_normalizedCubeMeasure_of_ae_restrict_openCubeSet h)
  have h2 : (fun z : Vec d × Vec d => f z.2) =ᵐ[Gagliardo.gagliardoCubeMeasure Q]
      fun z => g z.2 := by
    rw [Gagliardo.gagliardoCubeMeasure]
    exact Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (ae_cubeMeasure_of_ae_restrict_openCubeSet h)
  filter_upwards [h1, h2] with z hz1 hz2
  rw [euclideanGagliardoKernel_apply, euclideanGagliardoKernel_apply, hz1, hz2]

/-- **The normalized fractional norm only sees the field almost everywhere on
the cube**, in both of its two pieces. -/
theorem cubeHsENorm_congr_ae {Q : TriadicCube d} {s : ℝ} {f g : Vec d → E}
    (h : f =ᵐ[volume.restrict (openCubeSet Q)] g) :
    cubeHsENorm Q s f = cubeHsENorm Q s g := by
  rw [cubeHsENorm, cubeHsENorm, cubeLpENorm, cubeLpENorm,
    eLpNorm_congr_ae (ae_normalizedCubeMeasure_of_ae_restrict_openCubeSet h),
    cubeEuclideanGagliardoESeminorm, cubeEuclideanGagliardoESeminorm,
    eLpNorm_congr_ae (euclideanGagliardoKernel_congr_ae h)]

end

end ResponseFields
end Section3
end SuperdiffusionCLT
