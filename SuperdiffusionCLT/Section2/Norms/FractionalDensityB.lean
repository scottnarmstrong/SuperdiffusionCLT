/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.FractionalDensity

/-!
# The density hypothesis of the order-`s` pairing duality

`ofReal_abs_volumeAverage_matPairing_le_matHatNegENorm_mul_cubeHsENorm`
reduces the Hölder duality of the paper to one explicit hypothesis
`hdense`: smooth gradient fields approximate the field `G` both in `L̲²(Q)` and
in the `H̲^s(Q)` norm. This is false for a
general `G` in dimension `d ≥ 2` (the curl obstruction) and is a statement
about *gradient* fields `G = ∇w`. This module proves it for a gradient
field, from one explicit input: **smooth functions are `H²`-dense on the cube**,
i.e. the smooth approximants may be chosen so that their Hessians converge in
`L̲²(Q)` to the weak Hessian of `w`.

## The chain

* `cubeHsENorm_add_le`: the triangle inequality for the two-piece norm
  `cubeHsENorm`, by the two-vector Minkowski inequality.
* `cubeEuclideanGagliardoESeminorm_le_of_ae_tendsto`: the Gagliardo seminorm is
  lower semicontinuous along almost everywhere convergent sequences (Fatou).
* `cubeEuclideanGagliardoESeminorm_le_of_smooth_approx`: with the smooth
  comparison of `Section2/Norms/FractionalDensity.lean`, the gradient bound
  passes to a field that is only an `L̲²(Q)` limit of smooth fields.
* `hdense_of_hessianDensity`: applied to the difference `∇g - G`, whose
  Jacobian is `∇²g - J` for the weak Jacobian `J` of `G`, this gives exactly
  the two conjuncts of `hdense`.
* `pairing_le_of_hessianDensity`: the duality in the shape the `hDual` binder
  of the term-4 statement of Section 3 consumes.

## What is hypothesised, and why

The single unlanded input is `hH2`, in the exact shape

`∀ eps > 0, ∃ g smooth, ‖∇g - G‖_{L̲²(Q)} ≤ eps ∧ ‖∇²g - J‖_{L̲²(Q)} ≤ eps`,

with `J` a matrix field playing the role of the weak Jacobian of `G` (for
`G = ∇w` the Dirichlet response, `J` is the weak Hessian of `w`, which the a
priori anchor's Hessian clause supplies). It is *not* an extra analytic
assumption beyond the CoarseGraining library: its
convex-approximation results already contain everything needed to prove it —
`Homogenization.HasWeakPartialDerivOn.convexApproxSmoothRepresentative`
transports a weak partial derivative through the smoothing, and
`Homogenization.tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn`
converges the smoothing of an `L²` datum, which is exactly the pair of inputs
that the order-one density argument uses. Running that argument
one derivative higher (the smoothed gradient is continuous, so the a.e.
identity `∂_j(S_t w) = (1-t) S_t(∂_j w)` holds everywhere on the open cube and
may be differentiated again) yields `hH2`. That derivation is not carried out here:
the order-one argument keeps its smoothing family and its transport
step private, so it would have to be rebuilt.

## Honesty of the values

All norms are `ℝ≥0∞`-valued; the passage to real numbers in
`pairing_le_of_hessianDensity` is guarded by the two explicit finiteness
hypotheses `hMfin` and `hGfin`, exactly as in the pairing theorem it applies.

## Main definitions

* `jacobianDistENorm`: `‖DF - J‖_{L̲²(Q)}` in the Frobenius magnitude.

## Main results

* `cubeHsENorm_add_le`, `aestronglyMeasurable_euclideanGagliardoKernel`,
  `cubeLpENorm_jacobianFrobeniusMagnitude_sub_le`: the supporting laws.
* `cubeEuclideanGagliardoESeminorm_le_of_ae_tendsto`,
  `cubeEuclideanGagliardoESeminorm_le_of_smooth_approx`: semicontinuity.
* `hdense_of_hessianDensity`: `hdense` from `H²` density.
* `pairing_le_of_hessianDensity`: the `hDual` of `l.RHS.term4`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Minkowski for the two-piece fractional norm -/

private theorem euclidean_two_norm (p q : ℝ) :
    ‖(WithLp.toLp 2 ![p, q] : EuclideanSpace ℝ (Fin 2))‖
      = Real.sqrt (p ^ 2 + q ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs,
    sq_abs]

private theorem sqrt_sq_add_sq_add_le (a₁ a₂ b₁ b₂ : ℝ) :
    Real.sqrt ((a₁ + a₂) ^ 2 + (b₁ + b₂) ^ 2) ≤
      Real.sqrt (a₁ ^ 2 + b₁ ^ 2) + Real.sqrt (a₂ ^ 2 + b₂ ^ 2) := by
  classical
  have hsum : (WithLp.toLp 2 ![a₁, b₁] : EuclideanSpace ℝ (Fin 2))
      + (WithLp.toLp 2 ![a₂, b₂] : EuclideanSpace ℝ (Fin 2))
      = (WithLp.toLp 2 ![a₁ + a₂, b₁ + b₂] : EuclideanSpace ℝ (Fin 2)) := by
    refine PiLp.ext (fun i => ?_)
    fin_cases i <;> simp
  have hle := norm_add_le (WithLp.toLp 2 ![a₁, b₁] : EuclideanSpace ℝ (Fin 2))
    (WithLp.toLp 2 ![a₂, b₂] : EuclideanSpace ℝ (Fin 2))
  rw [hsum, euclidean_two_norm, euclidean_two_norm, euclidean_two_norm] at hle
  exact hle

private theorem ennreal_sq_add_sq_rpow_half_add_le (a₁ a₂ b₁ b₂ : ℝ≥0∞) :
    ((a₁ + a₂) ^ (2 : ℝ) + (b₁ + b₂) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤
      (a₁ ^ (2 : ℝ) + b₁ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) +
        (a₂ ^ (2 : ℝ) + b₂ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have htop : ∀ c e : ℝ≥0∞, c = ⊤ →
      (c ^ (2 : ℝ) + e ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = ⊤ := by
    intro c e hc
    rw [hc, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2), top_add,
      ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)]
  have htop' : ∀ c e : ℝ≥0∞, e = ⊤ →
      (c ^ (2 : ℝ) + e ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = ⊤ := by
    intro c e he
    rw [he, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2), add_top,
      ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)]
  rcases eq_or_ne a₁ ⊤ with h | ha₁
  · rw [htop a₁ b₁ h]; exact le_add_right le_top
  rcases eq_or_ne b₁ ⊤ with h | hb₁
  · rw [htop' a₁ b₁ h]; exact le_add_right le_top
  rcases eq_or_ne a₂ ⊤ with h | ha₂
  · rw [htop a₂ b₂ h]; exact le_add_left le_top
  rcases eq_or_ne b₂ ⊤ with h | hb₂
  · rw [htop' a₂ b₂ h]; exact le_add_left le_top
  have hrpow2 : ∀ z : ℝ, z ^ (2 : ℝ) = z ^ 2 := by
    intro z
    rw [← Real.rpow_natCast z 2]
    norm_num
  have hbase : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      (ENNReal.ofReal x ^ (2 : ℝ) + ENNReal.ofReal y ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        = ENNReal.ofReal (Real.sqrt (x ^ 2 + y ^ 2)) := by
    intro x y hx hy
    rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg hy (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _),
      hrpow2 x, hrpow2 y,
      ENNReal.ofReal_rpow_of_nonneg (by positivity)
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2), Real.sqrt_eq_rpow]
  have hform : ∀ c e : ℝ≥0∞, c ≠ ⊤ → e ≠ ⊤ →
      (c ^ (2 : ℝ) + e ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        = ENNReal.ofReal (Real.sqrt (c.toReal ^ 2 + e.toReal ^ 2)) := by
    intro c e hc he
    conv_lhs => rw [← ENNReal.ofReal_toReal hc, ← ENNReal.ofReal_toReal he]
    exact hbase _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hsum₁ : (a₁ + a₂).toReal = a₁.toReal + a₂.toReal :=
    ENNReal.toReal_add ha₁ ha₂
  have hsum₂ : (b₁ + b₂).toReal = b₁.toReal + b₂.toReal :=
    ENNReal.toReal_add hb₁ hb₂
  rw [hform a₁ b₁ ha₁ hb₁, hform a₂ b₂ ha₂ hb₂,
    hform (a₁ + a₂) (b₁ + b₂) (ENNReal.add_ne_top.2 ⟨ha₁, ha₂⟩)
      (ENNReal.add_ne_top.2 ⟨hb₁, hb₂⟩),
    hsum₁, hsum₂,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal
    (sqrt_sq_add_sq_add_le a₁.toReal a₂.toReal b₁.toReal b₂.toReal)

/-- **The triangle inequality for `‖·‖_{H̲^s(Q)}`.** Both pieces of clause (b)
are seminorms, and the two-vector Minkowski inequality combines them. -/
theorem cubeHsENorm_add_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : TriadicCube d} {s : ℝ} {f g : Vec d → E}
    (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (hg : AEStronglyMeasurable g (normalizedCubeMeasure Q))
    (hfk : AEStronglyMeasurable (euclideanGagliardoKernel s 2 f)
      (Gagliardo.gagliardoCubeMeasure Q))
    (hgk : AEStronglyMeasurable (euclideanGagliardoKernel s 2 g)
      (Gagliardo.gagliardoCubeMeasure Q)) :
    cubeHsENorm Q s (fun x => f x + g x) ≤
      cubeHsENorm Q s f + cubeHsENorm Q s g := by
  have hL : cubeHsWeight Q s * cubeLpENorm Q 2 (fun x => f x + g x) ≤
      cubeHsWeight Q s * cubeLpENorm Q 2 f +
        cubeHsWeight Q s * cubeLpENorm Q 2 g := by
    rw [← mul_add]
    exact mul_le_mul' le_rfl
      (cubeLpENorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf hg)
  have hG : cubeEuclideanGagliardoESeminorm Q s 2 (fun x => f x + g x) ≤
      cubeEuclideanGagliardoESeminorm Q s 2 f +
        cubeEuclideanGagliardoESeminorm Q s 2 g :=
    cubeEuclideanGagliardoESeminorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) hfk hgk
  refine le_trans (ENNReal.rpow_le_rpow (add_le_add
    (ENNReal.rpow_le_rpow hL (by norm_num))
    (ENNReal.rpow_le_rpow hG (by norm_num))) (by norm_num)) ?_
  exact ennreal_sq_add_sq_rpow_half_add_le _ _ _ _

/-! ## Lower semicontinuity of the Gagliardo seminorm -/

private theorem enorm_kernel_sq_eq {s : ℝ} (H : Vec d → Vec d) (z : Vec d × Vec d) :
    ‖euclideanGagliardoKernel s 2 (hilbertifyVecField H) z‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal
        ((euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / 2))) ^ 2 *
          vecNorm (H z.1 - H z.2) ^ 2) := by
  have hexp : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hknorm : ‖euclideanGagliardoKernel s 2 (hilbertifyVecField H) z‖
      = euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / 2)) * vecNorm (H z.1 - H z.2) := by
    rw [norm_euclideanGagliardoKernel, hexp]
    rfl
  rw [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2),
    hknorm, show ∀ w : ℝ, w ^ (2:ℝ) = w ^ 2 from fun w => by
      rw [← Real.rpow_natCast w 2]; norm_num, mul_pow]

private theorem continuous_vecNorm : Continuous (fun x : Vec d => vecNorm x) :=
  (HilbertVec.ofVecL d).continuous.norm

/-- **Lower semicontinuity of the Gagliardo seminorm.** If measurable fields
`F n` converge almost everywhere on the cube to `G` and their seminorms are all
at most `M`, then so is the seminorm of `G`. -/
theorem cubeEuclideanGagliardoESeminorm_le_of_ae_tendsto {Q : TriadicCube d}
    {s : ℝ} {F : ℕ → Vec d → Vec d} {G : Vec d → Vec d} {M : ℝ≥0∞}
    (hFm : ∀ n : ℕ, Measurable (F n))
    (hae : ∀ᵐ x ∂(normalizedCubeMeasure Q),
      Filter.Tendsto (fun n : ℕ => F n x) Filter.atTop (nhds (G x)))
    (hbd : ∀ n : ℕ,
      cubeEuclideanGagliardoESeminorm Q s 2 (hilbertifyVecField (F n)) ≤ M) :
    cubeEuclideanGagliardoESeminorm Q s 2 (hilbertifyVecField G) ≤ M := by
  classical
  set mu : Measure (Vec d × Vec d) := Gagliardo.gagliardoCubeMeasure Q with hmu
  have hcube : normalizedCubeMeasure Q
      = ENNReal.ofReal (cubeVolume Q)⁻¹ • cubeMeasure Q := rfl
  have haecube : ∀ᵐ x ∂(cubeMeasure Q),
      Filter.Tendsto (fun n : ℕ => F n x) Filter.atTop (nhds (G x)) := by
    rw [hcube] at hae
    exact (Measure.ae_ennreal_smul_measure_iff
      (by simp [(cubeVolume_pos Q)])).1 hae
  have hae1 : ∀ᵐ z ∂mu,
      Filter.Tendsto (fun n : ℕ => F n z.1) Filter.atTop (nhds (G z.1)) :=
    Measure.quasiMeasurePreserving_fst.ae hae
  have hae2 : ∀ᵐ z ∂mu,
      Filter.Tendsto (fun n : ℕ => F n z.2) Filter.atTop (nhds (G z.2)) :=
    Measure.quasiMeasurePreserving_snd.ae haecube
  have htend : ∀ᵐ z ∂mu, Filter.Tendsto
      (fun n : ℕ =>
        ‖euclideanGagliardoKernel s 2 (hilbertifyVecField (F n)) z‖ₑ ^ (2 : ℝ))
      Filter.atTop
      (nhds (‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ))) := by
    filter_upwards [hae1, hae2] with z h1 h2
    simp only [enorm_kernel_sq_eq]
    refine ENNReal.tendsto_ofReal ?_
    exact tendsto_const_nhds.mul
      ((Filter.Tendsto.comp (continuous_vecNorm.tendsto (G z.1 - G z.2))
        (h1.sub h2)).pow 2)
  have hmeasn : ∀ n : ℕ, Measurable (fun z : Vec d × Vec d =>
      ‖euclideanGagliardoKernel s 2 (hilbertifyVecField (F n)) z‖ₑ ^ (2 : ℝ)) := by
    intro n
    have h1 : Measurable (fun z : Vec d × Vec d =>
        euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / 2))) := by
      unfold euclideanDist euclideanNorm vecNormSq vecDot
      fun_prop
    have h2 : Measurable (fun z : Vec d × Vec d => vecNorm (F n z.1 - F n z.2)) :=
      continuous_vecNorm.measurable.comp
        (((hFm n).comp measurable_fst).sub ((hFm n).comp measurable_snd))
    simp only [enorm_kernel_sq_eq]
    exact ((h1.pow_const 2).mul (h2.pow_const 2)).ennreal_ofReal
  have hlimeq : (∫⁻ z, ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ
        ^ (2 : ℝ) ∂mu)
      = ∫⁻ z, Filter.liminf (fun n : ℕ =>
          ‖euclideanGagliardoKernel s 2 (hilbertifyVecField (F n)) z‖ₑ ^ (2 : ℝ))
          Filter.atTop ∂mu := by
    refine lintegral_congr_ae ?_
    filter_upwards [htend] with z hz
    exact (hz.liminf_eq).symm
  have hnint : ∀ n : ℕ,
      (∫⁻ z, ‖euclideanGagliardoKernel s 2 (hilbertifyVecField (F n)) z‖ₑ
        ^ (2 : ℝ) ∂mu) ≤ M ^ (2 : ℝ) := by
    intro n
    have h := ENNReal.rpow_le_rpow (hbd n) (by norm_num : (0:ℝ) ≤ 2)
    rw [cubeEuclideanGagliardoESeminorm,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (aestronglyMeasurable_euclideanGagliardoKernel (s := s)
          (f := hilbertifyVecField (F n))
          ((HilbertVec.ofVecL d).continuous.measurable.comp (hFm n)).aestronglyMeasurable),
      show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num,
      ← ENNReal.rpow_mul, show (1 : ℝ) / 2 * 2 = 1 from by norm_num,
      ENNReal.rpow_one] at h
    exact h
  have hfatou := lintegral_liminf_le' (μ := mu) (u := Filter.atTop)
    (f := fun n z => ‖euclideanGagliardoKernel s 2 (hilbertifyVecField (F n)) z‖ₑ
      ^ (2 : ℝ)) (fun n => (hmeasn n).aemeasurable)
  have hbound : (∫⁻ z, ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ
      ^ (2 : ℝ) ∂mu) ≤ M ^ (2 : ℝ) := by
    rw [hlimeq]
    refine le_trans hfatou ?_
    calc Filter.liminf (fun n : ℕ =>
          ∫⁻ z, ‖euclideanGagliardoKernel s 2 (hilbertifyVecField (F n)) z‖ₑ
            ^ (2 : ℝ) ∂mu) Filter.atTop
        ≤ Filter.liminf (fun _ : ℕ => M ^ (2 : ℝ)) Filter.atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hnint)
      _ = M ^ (2 : ℝ) := Filter.liminf_const _
  have hGm : AEStronglyMeasurable (hilbertifyVecField G) (normalizedCubeMeasure Q) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun n => ((HilbertVec.ofVecL d).continuous.measurable.comp (hFm n)).aestronglyMeasurable)
      (by
        filter_upwards [hae] with x hx
        exact ((HilbertVec.ofVecL d).continuous.tendsto _).comp hx)
  rw [cubeEuclideanGagliardoESeminorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (aestronglyMeasurable_euclideanGagliardoKernel (s := s)
        (f := hilbertifyVecField G) hGm),
    show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num]
  calc (∫⁻ z, ‖euclideanGagliardoKernel s 2 (hilbertifyVecField G) z‖ₑ ^ (2 : ℝ)
        ∂mu) ^ ((1 : ℝ) / 2)
      ≤ (M ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = M := by
        rw [← ENNReal.rpow_mul, show (2 : ℝ) * ((1 : ℝ) / 2) = 1 from by norm_num,
          ENNReal.rpow_one]

/-! ## The comparison for a field approximable by smooth fields -/

private theorem gagliardo_le_of_smooth_approx_eps {Q : TriadicCube d} {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) {G : Vec d → Vec d} {M : ℝ≥0∞}
    (_hGm : AEStronglyMeasurable (hilbertifyVecField G) (normalizedCubeMeasure Q))
    (happrox : ∀ eps : ℝ, 0 < eps → ∃ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F ∧
        vecCubeLpENorm Q 2 (fun x => F x - G x) ≤ ENNReal.ofReal eps ∧
        cubeLpENorm Q 2 (jacobianFrobeniusMagnitude F) ≤ M + ENNReal.ofReal eps)
    {eps : ℝ} (heps : 0 < eps) :
    cubeEuclideanGagliardoESeminorm Q s 2 (hilbertifyVecField G) ≤
      ENNReal.ofReal (gagliardoGradientConst d s * cubeScaleFactor Q ^ (1 - s)) *
        (M + ENNReal.ofReal eps) := by
  classical
  set cr : ℝ := gagliardoGradientConst d s * cubeScaleFactor Q ^ (1 - s) with hcr
  have hdelta : ∀ n : ℕ, 0 < min eps (1 / ((n : ℝ) + 1)) :=
    fun n => lt_min heps (by positivity)
  choose F hFsmooth hFclose hFjac using
    fun n : ℕ => happrox (min eps (1 / ((n : ℝ) + 1))) (hdelta n)
  have hFgag : ∀ n : ℕ,
      cubeEuclideanGagliardoESeminorm Q s 2 (hilbertifyVecField (F n)) ≤
        ENNReal.ofReal cr * (M + ENNReal.ofReal eps) := by
    intro n
    refine le_trans (cubeEuclideanGagliardoESeminorm_le_of_contDiff hs hs1 hd
      (hFsmooth n)) ?_
    exact mul_le_mul' le_rfl (le_trans (hFjac n)
      (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (min_le_left _ _))))
  have hFmeas : ∀ n : ℕ, Measurable (F n) := fun n => (hFsmooth n).continuous.measurable
  have hFae : ∀ n : ℕ,
      AEStronglyMeasurable (hilbertifyVecField (F n)) (normalizedCubeMeasure Q) :=
    fun n => ((HilbertVec.ofVecL d).continuous.comp (hFsmooth n).continuous
      ).aestronglyMeasurable
  have hLp : ∀ n : ℕ,
      eLpNorm (hilbertifyVecField (F n) - hilbertifyVecField G) 2
        (normalizedCubeMeasure Q) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    have h := hFclose n
    rw [vecCubeLpENorm, cubeLpENorm, hilbertifyVecField_sub'] at h
    exact le_trans h (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  have hzero : Filter.Tendsto (fun n : ℕ =>
      eLpNorm (hilbertifyVecField (F n) - hilbertifyVecField G) 2
        (normalizedCubeMeasure Q)) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => zero_le) hLp
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hmeasure : TendstoInMeasure (normalizedCubeMeasure Q)
      (fun n => hilbertifyVecField (F n)) Filter.atTop (hilbertifyVecField G) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hzero
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have haeVec : ∀ᵐ x ∂(normalizedCubeMeasure Q),
      Filter.Tendsto (fun k : ℕ => F (ns k) x) Filter.atTop (nhds (G x)) := by
    filter_upwards [hae] with x hx
    have := ((HilbertVec.continuousLinearEquivVec d).continuous.tendsto
      (hilbertifyVecField G x)).comp hx
    simpa [Function.comp_def, hilbertifyVecField] using this
  refine cubeEuclideanGagliardoESeminorm_le_of_ae_tendsto
    (F := fun k => F (ns k)) (fun k => hFmeas (ns k)) haeVec (fun k => hFgag (ns k))

/-- **The gradient comparison for a field approximable by smooth fields.** If
`G` is approximated in `L̲²(Q)` by smooth fields whose Jacobian `L̲²(Q)` norms
do not exceed `M` in the limit, then
`[G]_{W̲^{s,2}(Q)} ≤ gagliardoGradientConst d s (3^l)^{1-s} M`. -/
theorem cubeEuclideanGagliardoESeminorm_le_of_smooth_approx {Q : TriadicCube d}
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) {G : Vec d → Vec d} {M : ℝ≥0∞}
    (hGm : AEStronglyMeasurable (hilbertifyVecField G) (normalizedCubeMeasure Q))
    (happrox : ∀ eps : ℝ, 0 < eps → ∃ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F ∧
        vecCubeLpENorm Q 2 (fun x => F x - G x) ≤ ENNReal.ofReal eps ∧
        cubeLpENorm Q 2 (jacobianFrobeniusMagnitude F) ≤ M + ENNReal.ofReal eps) :
    cubeEuclideanGagliardoESeminorm Q s 2 (hilbertifyVecField G) ≤
      ENNReal.ofReal (gagliardoGradientConst d s * cubeScaleFactor Q ^ (1 - s)) * M := by
  set cr : ℝ := gagliardoGradientConst d s * cubeScaleFactor Q ^ (1 - s) with hcr
  have hLpos : (0 : ℝ) < cubeScaleFactor Q := by
    rw [cubeScaleFactor]
    positivity
  have hcrnn : 0 ≤ cr := by
    rw [hcr]
    exact mul_nonneg (gagliardoGradientConst_nonneg d s)
      (Real.rpow_nonneg hLpos.le _)
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro delta hdelta _hfin
  set epsr : ℝ := (delta : ℝ) / (cr + 1) with hepsr
  have hepspos : 0 < epsr := by
    have h1 : (0 : ℝ) < (delta : ℝ) := hdelta
    have h2 : (0 : ℝ) < cr + 1 := by linarith only [hcrnn]
    exact div_pos h1 h2
  have hkey := gagliardo_le_of_smooth_approx_eps hs hs1 hd hGm happrox hepspos
  have hle : cr * epsr ≤ (delta : ℝ) := by
    have h2 : (0 : ℝ) < cr + 1 := by linarith only [hcrnn]
    rw [hepsr, mul_div_assoc']
    rw [div_le_iff₀ h2]
    have hnn : (0 : ℝ) ≤ (delta : ℝ) := hdelta.le
    have hid : (delta : ℝ) * (cr + 1) = cr * (delta : ℝ) + (delta : ℝ) := by ring
    linarith only [hid, hnn]
  calc cubeEuclideanGagliardoESeminorm Q s 2 (hilbertifyVecField G)
      ≤ ENNReal.ofReal cr * (M + ENNReal.ofReal epsr) := hkey
    _ = ENNReal.ofReal cr * M + ENNReal.ofReal cr * ENNReal.ofReal epsr := by
        rw [mul_add]
    _ = ENNReal.ofReal cr * M + ENNReal.ofReal (cr * epsr) := by
        rw [ENNReal.ofReal_mul hcrnn]
    _ ≤ ENNReal.ofReal cr * M + ENNReal.ofReal ((delta : ℝ)) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hle)
    _ = ENNReal.ofReal cr * M + (delta : ℝ≥0∞) := by
        rw [ENNReal.ofReal_coe_nnreal]

/-! ## The Frobenius distance to a weak Jacobian -/

private theorem matrixFrobeniusMagnitude_sub_le (M N : Mat d) :
    matrixFrobeniusMagnitude (fun i j => M i j - N i j)
      ≤ matrixFrobeniusMagnitude M + matrixFrobeniusMagnitude N := by
  have h1 : matrixFrobeniusMagnitude (fun i j => M i j - N i j)
      = ‖HilbertMat.ofMat M - HilbertMat.ofMat N‖ := by
    refine (matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat _).trans ?_
    congr 1
  rw [h1, matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat,
    matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat]
  exact norm_sub_le _ _

private theorem euclideanGradient_sub {u v : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Vec d)
    (j : Fin d) :
    euclideanGradient (fun y => u y - v y) x j
      = euclideanGradient u x j - euclideanGradient v x j := by
  have hd1 : HasFDerivAt u (fderiv ℝ u x) x :=
    (hu.differentiable (by simp) x).hasFDerivAt
  have hd2 : HasFDerivAt v (fderiv ℝ v x) x :=
    (hv.differentiable (by simp) x).hasFDerivAt
  have h : fderiv ℝ (fun y => u y - v y) x = fderiv ℝ u x - fderiv ℝ v x :=
    (hd1.sub hd2).fderiv
  show fderiv ℝ (fun y => u y - v y) x (basisVec j)
      = fderiv ℝ u x (basisVec j) - fderiv ℝ v x (basisVec j)
  rw [h]
  rfl

/-- The `L̲²(Q)` norm of the Frobenius distance between the classical Jacobian
of a smooth field and a matrix field. -/
noncomputable def jacobianDistENorm (Q : TriadicCube d) (F : Vec d → Vec d)
    (J : Vec d → Mat d) : ℝ≥0∞ :=
  cubeLpENorm Q 2 (fun x => matrixFrobeniusMagnitude
    (fun i j => euclideanGradient (fun y => F y i) x j - J x i j))

private theorem aestronglyMeasurable_jacobianDist {Q : TriadicCube d}
    {F : Vec d → Vec d} {J : Vec d → Mat d} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hJm : ∀ i j : Fin d,
      AEStronglyMeasurable (fun x => J x i j) (normalizedCubeMeasure Q)) :
    AEStronglyMeasurable (fun x => matrixFrobeniusMagnitude
      (fun i j => euclideanGradient (fun y => F y i) x j - J x i j))
      (normalizedCubeMeasure Q) := by
  have hentry : ∀ i j : Fin d, AEMeasurable
      (fun x : Vec d => euclideanGradient (fun y => F y i) x j - J x i j)
      (normalizedCubeMeasure Q) := by
    intro i j
    have hgrad : Continuous
        (fun x : Vec d => euclideanGradient (fun y => F y i) x j) := by
      have hi : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => F y i) := contDiff_pi.mp hF i
      exact (hi.continuous_fderiv (by simp)).clm_apply
        continuous_const
    exact hgrad.measurable.aemeasurable.sub
      (aestronglyMeasurable_iff_aemeasurable.1 (hJm i j))
  have hfun : (fun x : Vec d => ∑ i : Fin d, ∑ j : Fin d,
        (euclideanGradient (fun y => F y i) x j - J x i j) ^ 2)
      = ∑ i : Fin d, ∑ j : Fin d,
        fun x : Vec d => (euclideanGradient (fun y => F y i) x j - J x i j) ^ 2 := by
    funext x
    simp only [Finset.sum_apply]
  have hsum : AEMeasurable (fun x : Vec d => ∑ i : Fin d, ∑ j : Fin d,
      (euclideanGradient (fun y => F y i) x j - J x i j) ^ 2)
      (normalizedCubeMeasure Q) := by
    rw [hfun]
    exact Finset.aemeasurable_sum _ (fun i _ =>
      Finset.aemeasurable_sum _ (fun j _ => (hentry i j).pow_const 2))
  refine aestronglyMeasurable_iff_aemeasurable.2 ?_
  exact Real.continuous_sqrt.measurable.comp_aemeasurable hsum

/-- The Jacobian of a difference of smooth fields is controlled in `L̲²(Q)` by
the two Frobenius distances to a common matrix field. -/
theorem cubeLpENorm_jacobianFrobeniusMagnitude_sub_le {Q : TriadicCube d}
    {F₁ F₂ : Vec d → Vec d} {J : Vec d → Mat d} (h1 : ContDiff ℝ (⊤ : ℕ∞) F₁)
    (h2 : ContDiff ℝ (⊤ : ℕ∞) F₂)
    (hJm : ∀ i j : Fin d,
      AEStronglyMeasurable (fun x => J x i j) (normalizedCubeMeasure Q)) :
    cubeLpENorm Q 2 (jacobianFrobeniusMagnitude (fun x => F₁ x - F₂ x)) ≤
      jacobianDistENorm Q F₁ J + jacobianDistENorm Q F₂ J := by
  have hpt : ∀ x : Vec d,
      jacobianFrobeniusMagnitude (fun y => F₁ y - F₂ y) x ≤
        matrixFrobeniusMagnitude
            (fun i j => euclideanGradient (fun y => F₁ y i) x j - J x i j) +
          matrixFrobeniusMagnitude
            (fun i j => euclideanGradient (fun y => F₂ y i) x j - J x i j) := by
    intro x
    have hentry : ∀ i j : Fin d,
        euclideanGradient (fun y => (F₁ y - F₂ y) i) x j
          = (euclideanGradient (fun y => F₁ y i) x j - J x i j)
            - (euclideanGradient (fun y => F₂ y i) x j - J x i j) := by
      intro i j
      have := euclideanGradient_sub (u := fun y : Vec d => F₁ y i)
        (v := fun y : Vec d => F₂ y i) (contDiff_pi.mp h1 i) (contDiff_pi.mp h2 i) x j
      rw [show (fun y : Vec d => (F₁ y - F₂ y) i)
          = fun y : Vec d => F₁ y i - F₂ y i from rfl, this]
      ring
    rw [jacobianFrobeniusMagnitude]
    have hrw : (fun i j => euclideanGradient (fun y => (F₁ y - F₂ y) i) x j)
        = fun i j => (euclideanGradient (fun y => F₁ y i) x j - J x i j)
            - (euclideanGradient (fun y => F₂ y i) x j - J x i j) := by
      funext i j
      exact hentry i j
    rw [hrw]
    exact matrixFrobeniusMagnitude_sub_le _ _
  calc cubeLpENorm Q 2 (jacobianFrobeniusMagnitude (fun x => F₁ x - F₂ x))
      ≤ cubeLpENorm Q 2 (fun x =>
          matrixFrobeniusMagnitude
              (fun i j => euclideanGradient (fun y => F₁ y i) x j - J x i j) +
            matrixFrobeniusMagnitude
              (fun i j => euclideanGradient (fun y => F₂ y i) x j - J x i j)) := by
        refine cubeLpENorm_mono_enorm
          (continuous_jacobianFrobeniusMagnitude (h1.sub h2)).aestronglyMeasurable
          (fun x => ?_)
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (jacobianFrobeniusMagnitude_nonneg _ _),
          abs_of_nonneg (by
            exact add_nonneg (matrixFrobeniusMagnitude_nonneg _)
              (matrixFrobeniusMagnitude_nonneg _))]
        exact hpt x
    _ ≤ jacobianDistENorm Q F₁ J + jacobianDistENorm Q F₂ J :=
        cubeLpENorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (aestronglyMeasurable_jacobianDist h1 hJm)
          (aestronglyMeasurable_jacobianDist h2 hJm)

/-! ## The density hypothesis from `H²` density -/

/-- **The density hypothesis `hdense` of the order-`s` duality, from `H²`
density.** For a field `G` with a weak Jacobian `J` on the cube, the `H²`-type
approximation `hH2` — smooth `g` with `∇g → G` and `∇²g → J` in `L̲²(Q)` —
supplies both conjuncts of the `hdense` binder of
`Section2/Norms/NegativeNormPairingHalf.lean`: the gradients converge in
`L̲²(Q)`, and their `H̲^s(Q)` norms do not exceed that of `G` in the limit. -/
theorem hdense_of_hessianDensity {Q : TriadicCube d} {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (hd : 0 < d) {G : Vec d → Vec d} {J : Vec d → Mat d}
    (hGm : AEStronglyMeasurable (hilbertifyVecField G) (normalizedCubeMeasure Q))
    (hJm : ∀ i j : Fin d,
      AEStronglyMeasurable (fun x => J x i j) (normalizedCubeMeasure Q))
    (hH2 : ∀ eps : ℝ, 0 < eps → ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      vecCubeLpENorm Q 2 (fun x => vecGradient g x - G x) ≤ ENNReal.ofReal eps ∧
      jacobianDistENorm Q (vecGradient g) J ≤ ENNReal.ofReal eps) :
    ∀ eps : ℝ, 0 < eps → ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      vecCubeLpENorm Q 2 (fun x => vecGradient g x - G x) ≤ ENNReal.ofReal eps ∧
      cubeHsENorm Q s (hilbertifyVecField (vecGradient g)) ≤
        cubeHsENorm Q s (hilbertifyVecField G) + ENNReal.ofReal eps := by
  intro eps heps
  have hLpos : (0 : ℝ) < cubeScaleFactor Q := by
    rw [cubeScaleFactor]
    positivity
  set wt : ℝ := cubeScaleFactor Q ^ (-s) with hwt
  set cr : ℝ := gagliardoGradientConst d s * cubeScaleFactor Q ^ (1 - s) with hcr
  have hwtpos : 0 < wt := Real.rpow_pos_of_pos hLpos _
  have hcrnn : 0 ≤ cr :=
    mul_nonneg (gagliardoGradientConst_nonneg d s) (Real.rpow_nonneg hLpos.le _)
  have hden : 0 < wt + cr + 1 := by linarith only [hwtpos, hcrnn]
  set del : ℝ := eps / (wt + cr + 1) with hdel
  have hdelpos : 0 < del := div_pos heps hden
  have hdelle : del ≤ eps := by
    rw [hdel, div_le_iff₀ hden]
    have hid : eps * (wt + cr + 1) = eps + eps * (wt + cr) := by ring
    have hnn : 0 ≤ eps * (wt + cr) :=
      mul_nonneg heps.le (by linarith only [hwtpos, hcrnn])
    linarith only [hid, hnn]
  have hkey : (wt + cr) * del ≤ eps := by
    rw [hdel, mul_div_assoc', div_le_iff₀ hden]
    have hid : eps * (wt + cr + 1) = (wt + cr) * eps + eps := by ring
    linarith only [hid, heps]
  obtain ⟨g, hgsmooth, hgclose, hgjac⟩ := hH2 del hdelpos
  refine ⟨g, hgsmooth, le_trans hgclose (ENNReal.ofReal_le_ofReal hdelle), ?_⟩
  set E : Vec d → Vec d := fun x => vecGradient g x - G x with hE
  have hgradsmooth : ContDiff ℝ (⊤ : ℕ∞) (vecGradient g) := contDiff_vecGradient hgsmooth
  have hgradcont : AEStronglyMeasurable (hilbertifyVecField (vecGradient g))
      (normalizedCubeMeasure Q) :=
    ((HilbertVec.ofVecL d).continuous.comp hgradsmooth.continuous).aestronglyMeasurable
  have hEm : AEStronglyMeasurable (hilbertifyVecField E) (normalizedCubeMeasure Q) := by
    rw [hE, hilbertifyVecField_sub']
    exact hgradcont.sub hGm
  have hGag : cubeEuclideanGagliardoESeminorm Q s 2 (hilbertifyVecField E) ≤
      ENNReal.ofReal (cr * del) := by
    have happrox : ∀ eps' : ℝ, 0 < eps' → ∃ F : Vec d → Vec d,
        ContDiff ℝ (⊤ : ℕ∞) F ∧
          vecCubeLpENorm Q 2 (fun x => F x - E x) ≤ ENNReal.ofReal eps' ∧
          cubeLpENorm Q 2 (jacobianFrobeniusMagnitude F) ≤
            ENNReal.ofReal del + ENNReal.ofReal eps' := by
      intro eps' heps'
      obtain ⟨h, hhsmooth, hhclose, hhjac⟩ := hH2 eps' heps'
      have hhgrad : ContDiff ℝ (⊤ : ℕ∞) (vecGradient h) := contDiff_vecGradient hhsmooth
      refine ⟨fun x => vecGradient g x - vecGradient h x,
        hgradsmooth.sub hhgrad, ?_, ?_⟩
      · have hrw : (fun x => (vecGradient g x - vecGradient h x) - E x)
            = fun x => -(vecGradient h x - G x) := by
          funext x
          funext i
          simp only [hE, Pi.sub_apply, Pi.neg_apply]
          ring
        rw [hrw, vecCubeLpENorm_neg]
        exact hhclose
      · exact le_trans
          (cubeLpENorm_jacobianFrobeniusMagnitude_sub_le hgradsmooth hhgrad hJm)
          (add_le_add hgjac hhjac)
    have h := cubeEuclideanGagliardoESeminorm_le_of_smooth_approx (Q := Q) (s := s)
      hs hs1 hd hEm happrox
    rwa [← hcr, ← ENNReal.ofReal_mul hcrnn] at h
  have hHsE : cubeHsENorm Q s (hilbertifyVecField E) ≤ ENNReal.ofReal eps := by
    refine le_trans (cubeHsENorm_le_add Q s (hilbertifyVecField E)) ?_
    have hweight : cubeHsWeight Q s = ENNReal.ofReal wt := rfl
    have hL2 : cubeLpENorm Q 2 (hilbertifyVecField E) ≤ ENNReal.ofReal del := hgclose
    calc cubeHsWeight Q s * cubeLpENorm Q 2 (hilbertifyVecField E) +
          cubeEuclideanGagliardoESeminorm Q s 2 (hilbertifyVecField E)
        ≤ ENNReal.ofReal wt * ENNReal.ofReal del + ENNReal.ofReal (cr * del) := by
          rw [hweight]
          exact add_le_add (mul_le_mul' le_rfl hL2) hGag
      _ = ENNReal.ofReal (wt * del + cr * del) := by
          rw [← ENNReal.ofReal_mul hwtpos.le,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal eps := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hid : wt * del + cr * del = (wt + cr) * del := by ring
          linarith only [hid, hkey]
  have hsplit : hilbertifyVecField (vecGradient g)
      = fun x => hilbertifyVecField E x + hilbertifyVecField G x := by
    funext x
    have hx : hilbertifyVecField E x
        = hilbertifyVecField (vecGradient g) x - hilbertifyVecField G x := by
      rw [hE]
      exact map_sub (HilbertVec.linearEquivVec d).symm _ _
    rw [hx]
    abel
  calc cubeHsENorm Q s (hilbertifyVecField (vecGradient g))
      = cubeHsENorm Q s (fun x => hilbertifyVecField E x + hilbertifyVecField G x) := by
        rw [hsplit]
    _ ≤ cubeHsENorm Q s (hilbertifyVecField E) + cubeHsENorm Q s (hilbertifyVecField G) :=
        cubeHsENorm_add_le hEm hGm
          (aestronglyMeasurable_euclideanGagliardoKernel hEm)
          (aestronglyMeasurable_euclideanGagliardoKernel hGm)
    _ ≤ ENNReal.ofReal eps + cubeHsENorm Q s (hilbertifyVecField G) :=
        add_le_add hHsE le_rfl
    _ = cubeHsENorm Q s (hilbertifyVecField G) + ENNReal.ofReal eps := by
        rw [add_comm]

/-! ## The term-4 duality hypothesis -/

/-- **The duality in the shape `l.RHS.term4` consumes.** This is the exact
`hDual` binder of the term-4 statement of Section 3, with the density
hypothesis of
`ofReal_abs_volumeAverage_matPairing_le_matHatNegENorm_mul_cubeHsENorm` replaced by the
`H²`-density input `hH2` and the weak Jacobian `J` of the field. -/
theorem pairing_le_of_hessianDensity {Q : TriadicCube d} {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (hd : 0 < d) {M : Vec d → Mat d} (p : Vec d)
    {G : Vec d → Vec d} {J : Vec d → Mat d}
    (hrow : ∀ u : Vec d,
      MemLp (hilbertifyVecField (fun x => Matrix.vecMul u (M x))) 2
        (normalizedCubeMeasure Q))
    (hG : MemLp (hilbertifyVecField G) 2 (normalizedCubeMeasure Q))
    (hMfin : matHatNegENorm Q s 2 M ≠ ⊤)
    (hGfin : cubeHsENorm Q s (hilbertifyVecField G) ≠ ⊤)
    (hJm : ∀ i j : Fin d,
      AEStronglyMeasurable (fun x => J x i j) (normalizedCubeMeasure Q))
    (hH2 : ∀ eps : ℝ, 0 < eps → ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      vecCubeLpENorm Q 2 (fun x => vecGradient g x - G x) ≤ ENNReal.ofReal eps ∧
      jacobianDistENorm Q (vecGradient g) J ≤ ENNReal.ofReal eps) :
    |volumeAverage (openCubeSet Q)
        (fun y => vecDot p (matVecMul (M y) (G y)))| ≤
      (matHatNegENorm Q s 2 M).toReal *
        (cubeHsENorm Q s (hilbertifyVecField G)).toReal * vecNorm p := by
  have hdense := hdense_of_hessianDensity hs hs1 hd hG.aestronglyMeasurable hJm hH2
  have hmain := ofReal_abs_volumeAverage_matPairing_le_vecNorm_mul p hrow hG hGfin
    hdense
  have hpt : (fun y : Vec d => vecDot p (matVecMul (M y) (G y)))
      = fun y : Vec d => vecDot (Matrix.vecMul p (M y)) (G y) :=
    funext fun y => vecDot_matVecMul p (M y) (G y)
  rw [hpt, ← volumeAverage_cubeSet_eq_openCubeSet]
  rw [← ENNReal.ofReal_toReal hMfin, ← ENNReal.ofReal_toReal hGfin,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (vecNorm_nonneg p)] at hmain
  have hnn : (0 : ℝ) ≤ vecNorm p *
      ((matHatNegENorm Q s 2 M).toReal *
        (cubeHsENorm Q s (hilbertifyVecField G)).toReal) :=
    mul_nonneg (vecNorm_nonneg p)
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hfinal := (ENNReal.ofReal_le_ofReal_iff hnn).1 hmain
  calc |volumeAverage (cubeSet Q)
        (fun y : Vec d => vecDot (Matrix.vecMul p (M y)) (G y))|
      ≤ vecNorm p * ((matHatNegENorm Q s 2 M).toReal *
          (cubeHsENorm Q s (hilbertifyVecField G)).toReal) := hfinal
    _ = (matHatNegENorm Q s 2 M).toReal *
          (cubeHsENorm Q s (hilbertifyVecField G)).toReal * vecNorm p := by ring

end

end Norms
end Section2
end SuperdiffusionCLT
