/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairing

/-!
# The order-`s` Hölder pairing: hatted negative norm against `H̲^s`

The proof of `l.RHS.term4` bounds the pairing it has to estimate by

> `|E[p·⨍_{cu_m}(k_{ℓ'}−k_ℓ)∇w]| ≤
>   E[‖(k_{ℓ'}−k_ℓ)p‖_{Ĥ̲^{-1/2}(cu_m)} ‖∇w‖_{H̲^{1/2}(cu_m)}]`.

This module proves that Hölder duality for the carriers of this repository, at a general
order `s` and at the exponent `p = 2`: the negative norm is
`matHatNegENorm`, the pairing is the rank-one gradient pairing, and the positive norm
is `cubeHsENorm`.

## The normalization, and the constant

`vecCubeEuclideanWspFullENorm_eq_cubeHsENorm` shows that the norm the
test class of `matHatNegENorm` is constrained by — the normalized *full* `W̲^{s,2}(Q)`
norm of the gradient field `∇g` — is literally `cubeHsENorm Q s` of the same field. The two
sides of the printed display are therefore normalized identically and the
duality holds with **constant exactly `1`**; no dimensional constant enters.
For this pairing the full norm, not the seminorm, is used on both sides.

The earlier hatted negative norm of `Section2/Norms/NegativeHat.lean`
constrained instead the Gagliardo *seminorm of the scalar potential* `g`, a
quantity unrelated by any inequality with constant `1` to `‖∇g‖_{H̲^{s}}`;
no duality of this shape is asserted for it.

## What is hypothesised

The test class consists of smooth gradient fields, while the field the estimate
is applied to is only `H̲^s`. At order one the corresponding density is proved
(`Sobolev.exists_cubeH1SmoothGradientApprox`, used in
`Section2/Norms/NegativeNormPairing.lean`); at a fractional order neither this
repository nor the CoarseGraining library has an endpoint for
it, so it enters as the single explicit hypothesis `hdense` of the two theorems
below. Everything else — the homogeneous step, the passage to the limit, the
extended-real bookkeeping and the degenerate cases — is proved.

## Values of the norms

**All norms are `ℝ≥0∞`-valued and `⊤` is a legitimate outcome.** The
extended-real statements handle `‖M‖ = ⊤` and `‖G‖_{H̲^s} = 0` explicitly. The
real-valued corollary requires both norms to be finite, which is what the
consumers' own hypotheses supply.

## Main results

* `cubeHsWeight_ne_zero`, `cubeHsENorm_const_smul`: the scale weight is
  nonzero and the fractional norm is absolutely homogeneous.
* `vecCubeEuclideanWspFullENorm_eq_cubeHsENorm`: the test-class norm is
  the `H̲^s` norm, with no constant.
* `ofReal_volumeAverage_matPairing_le_of_contDiff` and its two-sided
  companion: the duality against a smooth potential.
* `ofReal_abs_volumeAverage_matPairing_le_matHatNegENorm_mul_cubeHsENorm`:
  the duality against a general `H̲^s` gradient field, under `hdense`.
* `ofReal_abs_volumeAverage_matPairing_le_vecNorm_mul`: the same with the
  printed `|v|` factor instead of `|v| ≤ 1`.
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

/-! ## The scale weight and the homogeneity of the fractional norm -/

/-- The scale weight `3^{-sl}` is a strictly positive real. -/
theorem cubeHsWeight_ne_zero (Q : TriadicCube d) (s : ℝ) :
    cubeHsWeight Q s ≠ 0 := by
  have hc : 0 < cubeScaleFactor Q := by
    rw [cubeScaleFactor]
    positivity
  rw [cubeHsWeight]
  exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hc _)).ne'

private theorem rpow_half_sq_add_sq_mul (a A B : ℝ≥0∞) :
    ((a * A) ^ (2 : ℝ) + (a * B) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      = a * (A ^ (2 : ℝ) + B ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hA : (a * A) ^ (2 : ℝ) = a ^ (2 : ℝ) * A ^ (2 : ℝ) :=
    ENNReal.mul_rpow_of_nonneg a A h2
  have hB : (a * B) ^ (2 : ℝ) = a ^ (2 : ℝ) * B ^ (2 : ℝ) :=
    ENNReal.mul_rpow_of_nonneg a B h2
  rw [hA, hB, ← mul_add, ENNReal.mul_rpow_of_nonneg _ _ hhalf,
    ← ENNReal.rpow_mul]
  norm_num

/-- `‖·‖_{H̲^s(Q)}` is absolutely homogeneous. -/
theorem cubeHsENorm_const_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Q : TriadicCube d) (s : ℝ) (c : ℝ) (f : Vec d → E) :
    cubeHsENorm Q s (c • f) = ‖c‖ₑ * cubeHsENorm Q s f := by
  rw [cubeHsENorm, cubeHsENorm, cubeLpENorm_const_smul,
    cubeEuclideanGagliardoESeminorm_const_smul]
  have hfactor : cubeHsWeight Q s * (‖c‖ₑ * cubeLpENorm Q 2 f)
      = ‖c‖ₑ * (cubeHsWeight Q s * cubeLpENorm Q 2 f) := by ring
  rw [hfactor]
  exact rpow_half_sq_add_sq_mul _ _ _

/-- The Euclidean carrier commutes with scalar multiplication of a field. -/
theorem hilbertifyVecField_const_smul (c : ℝ) (F : Vec d → Vec d) :
    hilbertifyVecField (fun x => c • F x) = c • hilbertifyVecField F := by
  funext x
  exact map_smul (HilbertVec.linearEquivVec d).symm c (F x)

/-- The two spellings of the gradient field agree. -/
theorem vecGradient_eq_euclideanGradient (g : Vec d → ℝ) :
    vecGradient g = euclideanGradient g := rfl

/-! ## The bridge between the two fractional carriers -/

/-- **The test-class norm of `matHatNegENorm` is the `H̲^s` norm,
with no constant.** The test class
constrains `vecCubeEuclideanWspFullENorm Q s 2 (∇g)`, and the positive norm the
paper pairs against is `cubeHsENorm Q s (∇w)`; the two
are the same quantity, so the duality below has constant exactly `1`. -/
theorem vecCubeEuclideanWspFullENorm_eq_cubeHsENorm (Q : TriadicCube d) (s : ℝ)
    (F : Vec d → Vec d) :
    vecCubeEuclideanWspFullENorm Q s 2 F
      = cubeHsENorm Q s (hilbertifyVecField F) := by
  have hc : (0 : ℝ) < cubeScaleFactor Q := by
    rw [cubeScaleFactor]
    positivity
  have hw : ENNReal.ofReal (cubeScaleFactor Q) ^ (-s * (2 : ℝ≥0∞).toReal)
      = (ENNReal.ofReal (cubeScaleFactor Q ^ (-s))) ^ (2 : ℝ) := by
    rw [← ENNReal.ofReal_rpow_of_pos hc, ← ENNReal.rpow_mul]
    norm_num
  rw [vecCubeEuclideanWspFullENorm, cubeHsENorm, cubeHsWeight, hw,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  rfl

/-! ## The homogeneous form of the fractional pairing -/

private theorem vecNorm_neg' (v : Vec d) : vecNorm (-v) = vecNorm v := by
  rw [vecNorm, vecNorm,
    show (WithLp.toLp 2 (-v) : EuclideanSpace ℝ (Fin d)) =
      -(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) from rfl, norm_neg]

private theorem vecMul_neg_left (v : Vec d) (A : Mat d) :
    Matrix.vecMul (-v) A = -Matrix.vecMul v A := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Pi.neg_apply, neg_mul,
    Finset.sum_neg_distrib]

/-- **The order-`s` duality against a smooth potential.** For a matrix field
`M`, a vector `v` in the unit ball and a globally smooth `g` whose gradient
field has a finite `H̲^s(Q)` norm,

`⨍_Q ⟨M, v ⊗ ∇g⟩ ≤ ‖M‖_{Ŵ̲^{-s,2}(Q)} ‖∇g‖_{H̲^s(Q)}`,

with constant exactly `1`: by
`vecCubeEuclideanWspFullENorm_eq_cubeHsENorm` the test class of
`matHatNegENorm` is normalized by the same
`H̲^s` norm of the gradient field that appears on the right. -/
theorem ofReal_volumeAverage_matPairing_le_of_contDiff {Q : TriadicCube d}
    (M : Vec d → Mat d) {v : Vec d} (hv : vecNorm v ≤ 1) {s : ℝ}
    {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfin : cubeHsENorm Q s (hilbertifyVecField (vecGradient g)) ≠ ⊤) :
    ENNReal.ofReal
        (volumeAverage (cubeSet Q)
          (fun x => vecDot (Matrix.vecMul v (M x)) (vecGradient g x))) ≤
      matHatNegENorm Q s 2 M *
        cubeHsENorm Q s (hilbertifyVecField (vecGradient g)) := by
  set N := cubeHsENorm Q s (hilbertifyVecField (vecGradient g)) with hNdef
  set n : ℝ := N.toReal with hndef
  have hNeq : N = ENNReal.ofReal n := (ENNReal.ofReal_toReal hfin).symm
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : (0 : ℝ) ≤ n) with hn0 | hnpos
  · have hn0' : n = 0 := hn0.symm
    have hNzero : N = 0 := by rw [hNeq, hn0', ENNReal.ofReal_zero]
    have hL : vecCubeLpENorm Q 2 (vecGradient g) = 0 := by
      have hle := cubeHsENorm_weighted_le Q s (hilbertifyVecField (vecGradient g))
      rw [← hNdef, hNzero, le_zero_iff, mul_eq_zero] at hle
      rcases hle with hle | hle
      · exact absurd hle (cubeHsWeight_ne_zero Q s)
      · exact hle
    rw [volumeAverage_vecDot_eq_zero_of_vecCubeLpENorm_eq_zero
        (G := vecGradient g)
        (aestronglyMeasurable_hilbertifyVecField_euclideanGradient hg _) hL
        (fun x => Matrix.vecMul v (M x)), ENNReal.ofReal_zero]
    exact zero_le
  · set c : ℝ := n⁻¹ with hcdef
    have hcpos : 0 < c := inv_pos.2 hnpos
    set k : ℝ := volumeAverage (cubeSet Q) g with hkdef
    set h : Vec d → ℝ := fun x => c * (g x - k) with hhdef
    have hhsmooth : ContDiff ℝ (⊤ : ℕ∞) h :=
      contDiff_const.mul (hg.sub contDiff_const)
    have hfd : ∀ x : Vec d, fderiv ℝ h x = c • fderiv ℝ g x := by
      intro x
      have hd1 : HasFDerivAt (fun y : Vec d => g y - k) (fderiv ℝ g x) x :=
        (((hg.differentiable (by simp)) x).hasFDerivAt).sub_const k
      have hd2 : HasFDerivAt h (c • fderiv ℝ g x) x := hd1.const_mul c
      exact hd2.fderiv
    have hhgrad : vecGradient h = fun x => c • vecGradient g x := by
      funext x
      funext i
      simp only [vecGradient, hfd x, smul_apply, smul_eq_mul,
        Pi.smul_apply]
    have hhmean : volumeAverage (cubeSet Q) h = 0 := by
      rw [hhdef, volumeAverage_const_mul, hkdef,
        volumeAverage_sub_self_eq_zero Q hg.continuous, mul_zero]
    have hhfull : vecCubeEuclideanWspFullENorm Q s 2 (vecGradient h) ≤ 1 := by
      rw [vecCubeEuclideanWspFullENorm_eq_cubeHsENorm, hhgrad,
        hilbertifyVecField_const_smul, cubeHsENorm_const_smul, ← hNdef, hNeq]
      have hcn : ‖c‖ₑ = ENNReal.ofReal c := by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hcpos.le]
      rw [hcn, ← ENNReal.ofReal_mul hcpos.le, hcdef,
        inv_mul_cancel₀ (ne_of_gt hnpos), ENNReal.ofReal_one]
    have htest : IsHatTestField Q s (ENNReal.conjExponent 2) h := by
      rw [conjExponent_two]
      exact { contDiff := hhsmooth, meanZero := hhmean,
              fullENorm_le_one := hhfull }
    have hpair := le_matHatNegENorm M hv htest
    have hdens : volumeAverage (cubeSet Q) (matGradientPairingDensity M v h)
        = c * volumeAverage (cubeSet Q)
            (fun x => vecDot (Matrix.vecMul v (M x)) (vecGradient g x)) := by
      have hpt : matGradientPairingDensity M v h
          = fun x : Vec d =>
            c * vecDot (Matrix.vecMul v (M x)) (vecGradient g x) := by
        funext x
        rw [matGradientPairingDensity_eq_vecDot_vecGradient, hhgrad]
        simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hpt, volumeAverage_const_mul]
    rw [hdens] at hpair
    set X : ℝ := volumeAverage (cubeSet Q)
      (fun x => vecDot (Matrix.vecMul v (M x)) (vecGradient g x)) with hXdef
    rcases le_or_gt X 0 with hX | hX
    · rw [ENNReal.ofReal_of_nonpos hX]
      exact zero_le
    · have hXeq : X = n * (c * X) := by
        rw [hcdef, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos), one_mul]
      rw [hNeq, hXeq, ENNReal.ofReal_mul hnpos.le, mul_comm (ENNReal.ofReal n)]
      exact mul_le_mul' hpair le_rfl

/-- The two-sided form: the test class is symmetric in the vector `v`,
over which the matrix norm already takes a supremum. -/
theorem ofReal_abs_volumeAverage_matPairing_le_of_contDiff {Q : TriadicCube d}
    (M : Vec d → Mat d) {v : Vec d} (hv : vecNorm v ≤ 1) {s : ℝ}
    {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfin : cubeHsENorm Q s (hilbertifyVecField (vecGradient g)) ≠ ⊤) :
    ENNReal.ofReal
        |volumeAverage (cubeSet Q)
          (fun x => vecDot (Matrix.vecMul v (M x)) (vecGradient g x))| ≤
      matHatNegENorm Q s 2 M *
        cubeHsENorm Q s (hilbertifyVecField (vecGradient g)) := by
  set X : ℝ := volumeAverage (cubeSet Q)
    (fun x => vecDot (Matrix.vecMul v (M x)) (vecGradient g x)) with hXdef
  rcases abs_choice X with hX | hX
  · rw [hX, hXdef]
    exact ofReal_volumeAverage_matPairing_le_of_contDiff M hv hg hfin
  · have hvneg : vecNorm (-v) ≤ 1 := by rwa [vecNorm_neg']
    have hmain := ofReal_volumeAverage_matPairing_le_of_contDiff M hvneg hg hfin
    have hpt : (fun x : Vec d =>
          vecDot (Matrix.vecMul (-v) (M x)) (vecGradient g x))
        = fun x : Vec d =>
          (-1 : ℝ) * vecDot (Matrix.vecMul v (M x)) (vecGradient g x) := by
      funext x
      rw [vecMul_neg_left]
      simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hpt, volumeAverage_const_mul, ← hXdef] at hmain
    rw [hX]
    calc ENNReal.ofReal (-X) = ENNReal.ofReal ((-1 : ℝ) * X) := by ring_nf
      _ ≤ matHatNegENorm Q s 2 M *
            cubeHsENorm Q s (hilbertifyVecField (vecGradient g)) := hmain

/-! ## The fractional duality against a general gradient field -/

/-- **The fractional Hölder duality.** For a matrix field `M`, a vector `v` in the unit ball and a
vector field `G` on the cube,

`|⨍_Q (v ᵥ* M)·G| ≤ ‖M‖_{Ŵ̲^{-s,2}(Q)} ‖G‖_{H̲^s(Q)}`,

with constant exactly `1`.

The pairing is the rank-one pairing, the negative norm is `matHatNegENorm`,
and the positive norm is `cubeHsENorm`.

The test class of the negative norm consists of *smooth* gradient fields, while
the field `G` the estimate is applied to is only `H̲^s`. At order one the
required density is
`Sobolev.exists_cubeH1SmoothGradientApprox`; at a fractional order the
corresponding statement — smooth gradient fields are dense in the `H̲^s(Q)`
norm — is not available, in this repository or in the CoarseGraining library, so it
enters as the explicit hypothesis `hdense`. Its two conjuncts are the two facts an
`H̲^s`-approximating sequence supplies: the gradient fields converge in `L̲²(Q)`
(which follows from the
`H̲^s` convergence and `cubeHsENorm_weighted_le`), and their `H̲^s` norms do not
exceed that of `G` in the limit. No other input is hypothesised. -/
theorem ofReal_abs_volumeAverage_matPairing_le_matHatNegENorm_mul_cubeHsENorm
    {Q : TriadicCube d} {M : Vec d → Mat d} {v : Vec d} (hv : vecNorm v ≤ 1)
    {s : ℝ} {G : Vec d → Vec d}
    (hrow : MemLp (hilbertifyVecField (fun x => Matrix.vecMul v (M x))) 2
      (normalizedCubeMeasure Q))
    (hG : MemLp (hilbertifyVecField G) 2 (normalizedCubeMeasure Q))
    (hGfin : cubeHsENorm Q s (hilbertifyVecField G) ≠ ⊤)
    (hdense : ∀ eps : ℝ, 0 < eps → ∃ g : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧
        vecCubeLpENorm Q 2 (fun x => vecGradient g x - G x) ≤
          ENNReal.ofReal eps ∧
        cubeHsENorm Q s (hilbertifyVecField (vecGradient g)) ≤
          cubeHsENorm Q s (hilbertifyVecField G) + ENNReal.ofReal eps) :
    ENNReal.ofReal
        |volumeAverage (cubeSet Q)
          (fun x => vecDot (Matrix.vecMul v (M x)) (G x))| ≤
      matHatNegENorm Q s 2 M * cubeHsENorm Q s (hilbertifyVecField G) := by
  set NG := cubeHsENorm Q s (hilbertifyVecField G) with hNGdef
  set Nm := matHatNegENorm Q s 2 M with hNmdef
  rcases eq_or_ne NG 0 with hNG0 | hNG0
  · have hL : vecCubeLpENorm Q 2 G = 0 := by
      have hle := cubeHsENorm_weighted_le Q s (hilbertifyVecField G)
      rw [← hNGdef, hNG0, le_zero_iff, mul_eq_zero] at hle
      rcases hle with hle | hle
      · exact absurd hle (cubeHsWeight_ne_zero Q s)
      · exact hle
    rw [volumeAverage_vecDot_eq_zero_of_vecCubeLpENorm_eq_zero (G := G)
      hG.aestronglyMeasurable hL (fun x => Matrix.vecMul v (M x)), abs_zero,
      ENNReal.ofReal_zero]
    exact zero_le
  rcases eq_or_ne Nm ⊤ with hNmtop | hNmtop
  · rw [hNmtop, ENNReal.top_mul hNG0]
    exact le_top
  set A := hrow.toLp (hilbertifyVecField (fun x => Matrix.vecMul v (M x)))
    with hAdef
  set B := hG.toLp (hilbertifyVecField G) with hBdef
  have hinner : (inner ℝ A B : ℝ) =
      volumeAverage (cubeSet Q)
        (fun x => vecDot (Matrix.vecMul v (M x)) (G x)) :=
    inner_toLp_hilbertifyVecField hrow hG
  set ng : ℝ := NG.toReal with hngdef
  set nm : ℝ := Nm.toReal with hnmdef
  have hng0 : (0 : ℝ) ≤ ng := ENNReal.toReal_nonneg
  have hnm0 : (0 : ℝ) ≤ nm := ENNReal.toReal_nonneg
  have hNGeq : NG = ENNReal.ofReal ng := (ENNReal.ofReal_toReal hGfin).symm
  have hNmeq : Nm = ENNReal.ofReal nm := (ENNReal.ofReal_toReal hNmtop).symm
  have key : ∀ eps : ℝ, 0 < eps →
      |(inner ℝ A B : ℝ)| ≤ nm * ng + (nm + ‖A‖) * eps := by
    intro eps heps
    obtain ⟨g, hgsmooth, hgclose, hgnorm⟩ := hdense eps heps
    have hgfin : cubeHsENorm Q s (hilbertifyVecField (vecGradient g)) ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.add_ne_top.2 ⟨hGfin, ENNReal.ofReal_ne_top⟩) hgnorm
    have hEmem : MemLp (hilbertifyVecField
        (fun x => vecGradient g x - G x)) 2 (normalizedCubeMeasure Q) := by
      exact lt_of_le_of_lt hgclose ENNReal.ofReal_lt_top
    have hsum : hilbertifyVecField (vecGradient g)
        = hilbertifyVecField (fun x => vecGradient g x - G x)
          + hilbertifyVecField G := by
      rw [hilbertifyVecField_sub']
      abel
    have hCmem : MemLp (hilbertifyVecField (vecGradient g)) 2
        (normalizedCubeMeasure Q) := by
      rw [hsum]
      exact hEmem.add hG
    set E := hEmem.toLp (hilbertifyVecField (fun x => vecGradient g x - G x))
      with hEdef
    set C := hCmem.toLp (hilbertifyVecField (vecGradient g)) with hCdef
    have hCeq : C = E + B := by
      rw [hCdef, hEdef, hBdef, ← MemLp.toLp_add]
      exact MemLp.toLp_congr _ _
        (Filter.Eventually.of_forall (fun x => congrFun hsum x))
    have hEnorm : ‖E‖ ≤ eps := by
      have hh := norm_toLp_hilbertifyVecField hEmem
      rw [← hEdef] at hh
      rw [hh]
      have hle := (ENNReal.toReal_le_toReal
        (lt_of_le_of_lt hgclose ENNReal.ofReal_lt_top).ne
        ENNReal.ofReal_ne_top).2 hgclose
      rwa [ENNReal.toReal_ofReal heps.le] at hle
    have hinnerC : (inner ℝ A C : ℝ) =
        volumeAverage (cubeSet Q)
          (fun x => vecDot (Matrix.vecMul v (M x)) (vecGradient g x)) :=
      inner_toLp_hilbertifyVecField hrow hCmem
    have hpairC : |(inner ℝ A C : ℝ)| ≤ nm * (ng + eps) := by
      have hmain := ofReal_abs_volumeAverage_matPairing_le_of_contDiff M hv
        hgsmooth hgfin
      rw [← hinnerC] at hmain
      have hstep : Nm * cubeHsENorm Q s (hilbertifyVecField (vecGradient g))
          ≤ ENNReal.ofReal (nm * (ng + eps)) := by
        calc Nm * cubeHsENorm Q s (hilbertifyVecField (vecGradient g))
            ≤ Nm * (NG + ENNReal.ofReal eps) := mul_le_mul' le_rfl hgnorm
          _ = ENNReal.ofReal (nm * (ng + eps)) := by
              rw [hNmeq, hNGeq, ← ENNReal.ofReal_add hng0 heps.le,
                ← ENNReal.ofReal_mul hnm0]
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg hnm0 (by linarith only [hng0, heps]))).1
        (le_trans hmain hstep)
    have hsplit : (inner ℝ A B : ℝ)
        = (inner ℝ A C : ℝ) - (inner ℝ A E : ℝ) := by
      rw [hCeq, inner_add_right]
      ring
    have hAE : |(inner ℝ A E : ℝ)| ≤ ‖A‖ * eps :=
      le_trans (abs_real_inner_le_norm A E)
        (mul_le_mul_of_nonneg_left hEnorm (norm_nonneg A))
    calc |(inner ℝ A B : ℝ)|
        ≤ |(inner ℝ A C : ℝ)| + |(inner ℝ A E : ℝ)| := by
          rw [hsplit]; exact abs_sub _ _
      _ ≤ nm * (ng + eps) + ‖A‖ * eps := add_le_add hpairC hAE
      _ = nm * ng + (nm + ‖A‖) * eps := by ring
  have hfinal : |(inner ℝ A B : ℝ)| ≤ nm * ng := by
    refine le_of_forall_pos_le_add ?_
    intro ep hep
    have hAnn : (0 : ℝ) ≤ ‖A‖ := norm_nonneg A
    have hden : 0 < nm + ‖A‖ + 1 := by linarith only [hnm0, hAnn]
    have hd : 0 < ep / (nm + ‖A‖ + 1) := div_pos hep hden
    have hk := key (ep / (nm + ‖A‖ + 1)) hd
    have h1 : (nm + ‖A‖) * (ep / (nm + ‖A‖ + 1))
        ≤ (nm + ‖A‖ + 1) * (ep / (nm + ‖A‖ + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith only []) hd.le
    have h2 : (nm + ‖A‖ + 1) * (ep / (nm + ‖A‖ + 1)) = ep := by field_simp
    linarith only [hk, h1, h2]
  rw [hinner] at hfinal
  calc ENNReal.ofReal
        |volumeAverage (cubeSet Q)
          (fun x => vecDot (Matrix.vecMul v (M x)) (G x))|
      ≤ ENNReal.ofReal (nm * ng) := ENNReal.ofReal_le_ofReal hfinal
    _ = Nm * NG := by rw [hNmeq, hNGeq, ENNReal.ofReal_mul hnm0]

private theorem eq_zero_of_vecNorm_eq_zero {v : Vec d} (h : vecNorm v = 0) :
    v = 0 := by
  have h' : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) = 0 := by
    rw [← norm_eq_zero]
    exact h
  funext i
  exact congrFun (congrArg (fun w : EuclideanSpace ℝ (Fin d) => WithLp.ofLp w) h') i

private theorem vecMul_smul_left (c : ℝ) (v : Vec d) (A : Mat d) :
    Matrix.vecMul (c • v) A = c • Matrix.vecMul v A := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

/-- **The fractional duality with the vector kept general.** The rank-one
pairing is homogeneous of degree one in the vector, so the unit-ball form above
gives the printed `|v|` factor,

`|⨍_Q (v ᵥ* M)·G| ≤ |v| ‖M‖_{Ŵ̲^{-s,2}(Q)} ‖G‖_{H̲^s(Q)}`.

The row hypothesis is quantified over the vector because the rescaled vector
`|v|⁻¹ v` is the one the unit-ball form is applied to. -/
theorem ofReal_abs_volumeAverage_matPairing_le_vecNorm_mul {Q : TriadicCube d}
    {M : Vec d → Mat d} (v : Vec d) {s : ℝ} {G : Vec d → Vec d}
    (hrow : ∀ u : Vec d,
      MemLp (hilbertifyVecField (fun x => Matrix.vecMul u (M x))) 2
        (normalizedCubeMeasure Q))
    (hG : MemLp (hilbertifyVecField G) 2 (normalizedCubeMeasure Q))
    (hGfin : cubeHsENorm Q s (hilbertifyVecField G) ≠ ⊤)
    (hdense : ∀ eps : ℝ, 0 < eps → ∃ g : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧
        vecCubeLpENorm Q 2 (fun x => vecGradient g x - G x) ≤
          ENNReal.ofReal eps ∧
        cubeHsENorm Q s (hilbertifyVecField (vecGradient g)) ≤
          cubeHsENorm Q s (hilbertifyVecField G) + ENNReal.ofReal eps) :
    ENNReal.ofReal
        |volumeAverage (cubeSet Q)
          (fun x => vecDot (Matrix.vecMul v (M x)) (G x))| ≤
      ENNReal.ofReal (vecNorm v) *
        (matHatNegENorm Q s 2 M * cubeHsENorm Q s (hilbertifyVecField G)) := by
  rcases eq_or_ne (vecNorm v) 0 with h0 | h0
  · have hv0 : v = 0 := eq_zero_of_vecNorm_eq_zero h0
    have hzero : (fun x : Vec d => vecDot (Matrix.vecMul v (M x)) (G x))
        = fun _ : Vec d => (0 : ℝ) := by
      funext x
      rw [hv0]
      simp [Matrix.vecMul, dotProduct, vecDot]
    rw [hzero]
    simp only [volumeAverage, integral_zero, mul_zero, abs_zero,
      ENNReal.ofReal_zero]
    exact zero_le
  · have hnn : (0 : ℝ) ≤ vecNorm v := norm_nonneg _
    have hpos : 0 < vecNorm v := lt_of_le_of_ne hnn (Ne.symm h0)
    set r : ℝ := vecNorm v with hrdef
    set u : Vec d := r⁻¹ • v with hudef
    have hunorm : vecNorm u = 1 := by
      have hcast : (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))
          = r⁻¹ • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) := rfl
      show ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))‖ = 1
      rw [hcast, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (inv_pos.2 hpos))]
      exact inv_mul_cancel₀ (ne_of_gt hpos)
    have hvu : v = r • u := by
      rw [hudef, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
    have hscale : (fun x : Vec d => vecDot (Matrix.vecMul v (M x)) (G x))
        = fun x : Vec d => r * vecDot (Matrix.vecMul u (M x)) (G x) := by
      funext x
      rw [hvu, vecMul_smul_left]
      simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hmain :=
      ofReal_abs_volumeAverage_matPairing_le_matHatNegENorm_mul_cubeHsENorm
        (le_of_eq hunorm) (hrow u) hG hGfin hdense
    rw [hscale, volumeAverage_const_mul, abs_mul, abs_of_nonneg hpos.le,
      ENNReal.ofReal_mul hpos.le]
    exact mul_le_mul' le_rfl hmain

end

end Norms
end Section2
end SuperdiffusionCLT
