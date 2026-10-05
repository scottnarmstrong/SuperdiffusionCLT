/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2
public import SuperdiffusionCLT.Probability.OrliczMoments

/-!
# `l.RHS.term1`: the per-sample decomposition and the shapes of the step displays

The proof of `l.RHS.term1` (with the display `e.RHS.term1`) is carried out in
the paper in three displays.  This file proves the per-sample decomposition and the
cube-level bookkeeping for the two step displays, whose printed shapes are recorded below.

## The shapes, exactly as printed

* **`e.decompose.flux.u.n`**, a *per-sample* display:

  `|⨍_{cu_m} ∇w·(a_ℓ∇u_n − q)| ≤ |⨍_{cu_m} ∇w·(a_ℓ∇ũ_n − q̃)|
        + ‖∇w‖_{L̲²(cu_m)} (‖a_ℓ(∇u_n − ∇ũ_n)‖_{L̲²(cu_m)} + |q̃ − q|)`.

  It is proved here as `ofReal_abs_volumeAverage_flux_le`: triangle inequality
  and Cauchy-Schwarz in the cube, nothing else.

* **`e.decompose.flux.u.n.first`**, Step 1:

  `E[ ‖∇w‖_{L̲²(cu_m)} ( ‖a_ℓ(∇u_n − ∇ũ_n)‖_{L̲²(cu_m)} + |q̃ − q| ) ]
        ≤ C ν^{-3/2} ℓ h^{1/2} 3^{-(ℓ-n)/2}`.

  A plain expectation of the product: **no exponent anywhere**, neither inside
  nor outside.

* **`e.decompose.flux.u.n.second`**, Step 2:

  `E[ |⨍_{cu_m} ∇w·(a_ℓ∇ũ_n − q̃)| ] ≤ C ν^{-1} (ℓ m (m−ℓ))^{1/2} 3^{-(ℓ'-ℓ)}`.

Expectations of nonnegative quantities are rendered by the truncated Lebesgue
integral `∫⁻ · ∂P.toMeasure` valued in `ℝ≥0∞`, with the printed right-hand
side as an `ENNReal.ofReal`; this is the faithful reading (a divergent
expectation is excluded rather than silently zeroed, as a `.toReal ≤ …`
rendering would do).

## The `L̲²` display of Step 1 from `e.nablaw.Lt`

Line 5386 derives the third display of Step 1,
`E[‖∇w‖²_{L̲²(cu_m)}] ≤ C h |p|²`, from `e.nablaw.Lt`.  That derivation needs only the first
conjunct of `l.w.basic.regbounds` in its exact shape (an `L̲^8(cu_m)` bound by
a `Γ₂` envelope of amplitude `C |p| h^{1/2}`); the proof is the exponent
downgrade on the cube's probability measure together with the printed moment
bound of `l.moments.gamma.psi`.

## The manuscript's scalar `shom_{L',*}(cu_n)`

The paper identifies it with `|Q|²` for the variational direction
`Q = shom_{L',*}^{1/2}(cu_n) e`, so it is
`vecNormSq (fluxSlot nu S.LPrime P S.n e)`; `|p|²` is
`vecNormSq (testVector nu S.LPrime P S.n e)`, and the two are reciprocal
(`vecNormSq_testVector`, `vecNormSq_fluxSlot`).  The cancellation the paper
performs when combining the displays is exactly that reciprocity.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Cube-level bookkeeping -/

/-- The constant field has `L̲²(Q)` norm `|v|`. -/
theorem vecCubeLpENorm_two_const (Q : TriadicCube d) (v : Vec d) :
    vecCubeLpENorm Q 2 (fun _ : Vec d => v) =
      ENNReal.ofReal (Real.sqrt (vecNormSq v)) := by
  have hsq : (vecCubeLpENorm Q 2 (fun _ : Vec d => v)) ^ (2 : ℕ) =
      ENNReal.ofReal (vecNormSq v) := vecCubeLpENorm_const_sq Q v
  have hns : (0 : ℝ) ≤ vecNormSq v := vecNormSq_nonneg v
  have hself : vecCubeLpENorm Q 2 (fun _ : Vec d => v) =
      ((vecCubeLpENorm Q 2 (fun _ : Vec d => v)) ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  rw [hself, hsq, Real.sqrt_eq_rpow,
    ENNReal.ofReal_rpow_of_nonneg hns (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]

/-- The absolute form of the cube Cauchy-Schwarz bound, in `ℝ≥0∞`. -/
theorem ofReal_abs_volumeAverage_openCubeSet_vecDot_le {Q : TriadicCube d}
    {a b : Vec d → Vec d}
    (ha : MemVectorL2 (openCubeSet Q) a) (hb : MemVectorL2 (openCubeSet Q) b) :
    ENNReal.ofReal |volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))| ≤
      vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b := by
  have hna : MemVectorL2 (openCubeSet Q) (fun x => -a x) := ha.neg
  have hpos := ofReal_volumeAverage_openCubeSet_vecDot_le ha hb
  have hneg := ofReal_volumeAverage_openCubeSet_vecDot_le hna hb
  rw [show vecCubeLpENorm Q 2 (fun x : Vec d => -a x) = vecCubeLpENorm Q 2 a from
    vecCubeLpENorm_neg Q 2 a] at hneg
  have hflip : volumeAverage (openCubeSet Q) (fun x => vecDot (-a x) (b x)) =
      -(volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))) := by
    rw [show (fun x : Vec d => vecDot (-a x) (b x)) =
      (fun x : Vec d => -vecDot (a x) (b x)) from
      funext fun x => vecDot_neg_left (a x) (b x)]
    simp only [volumeAverage, integral_neg, mul_neg]
  rw [hflip] at hneg
  rcases abs_cases (volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x)))
    with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]; exact hpos
  · rw [he]; exact hneg

/-- Pointwise linearity of `matVecMul` in the vector slot, subtraction form. -/
private theorem matVecMulSub (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]

/-! ## `e.decompose.flux.u.n`: the per-sample decomposition -/

/-- **`e.decompose.flux.u.n`**: for one sample of the coefficient field, the cube pairing of the
response gradient against the full centred flux `a ∇u_n − q` is bounded by the
same pairing against the localized centred flux `a ∇ũ_n − q̃` plus the
Cauchy-Schwarz amplitude
`‖∇w‖_{L̲²(Q)} (‖a(∇u_n − ∇ũ_n)‖_{L̲²(Q)} + |q̃ − q|)`.

This is triangle inequality and Cauchy-Schwarz in the cube, exactly as the
print says; the `L²` memberships of the two fluxes on the cube are the only
hypotheses. -/
theorem ofReal_abs_volumeAverage_flux_le (Q : TriadicCube d)
    (aField : Vec d → Mat d) (gradW uN uTilde : Vec d → Vec d) (q qTilde : Vec d)
    (hgradW : MemVectorL2 (openCubeSet Q) gradW)
    (hUN : MemVectorL2 (openCubeSet Q) (fun x => matVecMul (aField x) (uN x)))
    (hUT : MemVectorL2 (openCubeSet Q) (fun x => matVecMul (aField x) (uTilde x))) :
    ENNReal.ofReal |volumeAverage (openCubeSet Q)
        (fun x => vecDot (gradW x) (matVecMul (aField x) (uN x) - q))| ≤
      ENNReal.ofReal |volumeAverage (openCubeSet Q)
          (fun x => vecDot (gradW x) (matVecMul (aField x) (uTilde x) - qTilde))| +
        vecCubeLpENorm Q 2 gradW *
          (vecCubeLpENorm Q 2 (fun x => matVecMul (aField x) (uN x - uTilde x)) +
            ENNReal.ofReal (Real.sqrt (vecNormSq (qTilde - q)))) := by
  classical
  set U : Set (Vec d) := openCubeSet Q with hU
  have hdiff : MemVectorL2 U (fun x => matVecMul (aField x) (uN x - uTilde x)) := by
    have : (fun x : Vec d => matVecMul (aField x) (uN x - uTilde x)) =
        fun x : Vec d => matVecMul (aField x) (uN x) - matVecMul (aField x) (uTilde x) :=
      funext fun x => matVecMulSub (aField x) (uN x) (uTilde x)
    rw [this]
    exact hUN.sub hUT
  have hconst : MemVectorL2 U (fun _ : Vec d => qTilde - q) := memVectorL2_const _
  have hUNq : MemVectorL2 U (fun x => matVecMul (aField x) (uN x) - q) :=
    hUN.sub (memVectorL2_const _)
  have hUTq : MemVectorL2 U (fun x => matVecMul (aField x) (uTilde x) - qTilde) :=
    hUT.sub (memVectorL2_const _)
  -- the pointwise splitting of the integrand
  have hsplit : ∀ x : Vec d,
      vecDot (gradW x) (matVecMul (aField x) (uN x) - q) =
        vecDot (gradW x) (matVecMul (aField x) (uTilde x) - qTilde) +
          (vecDot (gradW x) (matVecMul (aField x) (uN x - uTilde x)) +
            vecDot (gradW x) (qTilde - q)) := by
    intro x
    rw [← vecDot_add_right, ← vecDot_add_right, matVecMulSub]
    refine congrArg (vecDot (gradW x)) ?_
    abel
  have hi1 : IntegrableOn
      (fun x => vecDot (gradW x) (matVecMul (aField x) (uTilde x) - qTilde)) U :=
    integrableOn_vecDot_of_memVectorL2 hgradW hUTq
  have hi2 : IntegrableOn
      (fun x => vecDot (gradW x) (matVecMul (aField x) (uN x - uTilde x))) U :=
    integrableOn_vecDot_of_memVectorL2 hgradW hdiff
  have hi3 : IntegrableOn (fun x => vecDot (gradW x) (qTilde - q)) U :=
    integrableOn_vecDot_of_memVectorL2 hgradW hconst
  have havg : volumeAverage U (fun x => vecDot (gradW x)
        (matVecMul (aField x) (uN x) - q)) =
      volumeAverage U (fun x => vecDot (gradW x)
          (matVecMul (aField x) (uTilde x) - qTilde)) +
        (volumeAverage U (fun x => vecDot (gradW x)
            (matVecMul (aField x) (uN x - uTilde x))) +
          volumeAverage U (fun x => vecDot (gradW x) (qTilde - q))) := by
    rw [show (fun x : Vec d => vecDot (gradW x) (matVecMul (aField x) (uN x) - q)) =
      (fun x : Vec d => vecDot (gradW x) (matVecMul (aField x) (uTilde x) - qTilde) +
        (vecDot (gradW x) (matVecMul (aField x) (uN x - uTilde x)) +
          vecDot (gradW x) (qTilde - q))) from funext hsplit]
    rw [volumeAverage_add'
      (f := fun x : Vec d => vecDot (gradW x) (matVecMul (aField x) (uTilde x) - qTilde))
      (g := fun x : Vec d => vecDot (gradW x) (matVecMul (aField x) (uN x - uTilde x)) +
        vecDot (gradW x) (qTilde - q)) hi1 (hi2.add hi3),
      volumeAverage_add'
      (f := fun x : Vec d => vecDot (gradW x) (matVecMul (aField x) (uN x - uTilde x)))
      (g := fun x : Vec d => vecDot (gradW x) (qTilde - q)) hi2 hi3]
  have habs : |volumeAverage U (fun x => vecDot (gradW x)
        (matVecMul (aField x) (uN x) - q))| ≤
      |volumeAverage U (fun x => vecDot (gradW x)
          (matVecMul (aField x) (uTilde x) - qTilde))| +
        (|volumeAverage U (fun x => vecDot (gradW x)
            (matVecMul (aField x) (uN x - uTilde x)))| +
          |volumeAverage U (fun x => vecDot (gradW x) (qTilde - q))|) := by
    rw [havg]
    exact le_trans (abs_add_le _ _) (add_le_add le_rfl (abs_add_le _ _))
  calc ENNReal.ofReal |volumeAverage U (fun x => vecDot (gradW x)
          (matVecMul (aField x) (uN x) - q))|
      ≤ ENNReal.ofReal (|volumeAverage U (fun x => vecDot (gradW x)
            (matVecMul (aField x) (uTilde x) - qTilde))| +
          (|volumeAverage U (fun x => vecDot (gradW x)
              (matVecMul (aField x) (uN x - uTilde x)))| +
            |volumeAverage U (fun x => vecDot (gradW x) (qTilde - q))|)) :=
        ENNReal.ofReal_le_ofReal habs
    _ ≤ ENNReal.ofReal |volumeAverage U (fun x => vecDot (gradW x)
            (matVecMul (aField x) (uTilde x) - qTilde))| +
          (ENNReal.ofReal |volumeAverage U (fun x => vecDot (gradW x)
              (matVecMul (aField x) (uN x - uTilde x)))| +
            ENNReal.ofReal |volumeAverage U (fun x => vecDot (gradW x)
              (qTilde - q))|) := by
        exact le_trans ENNReal.ofReal_add_le
          (add_le_add le_rfl ENNReal.ofReal_add_le)
    _ ≤ ENNReal.ofReal |volumeAverage U (fun x => vecDot (gradW x)
            (matVecMul (aField x) (uTilde x) - qTilde))| +
          vecCubeLpENorm Q 2 gradW *
            (vecCubeLpENorm Q 2 (fun x => matVecMul (aField x) (uN x - uTilde x)) +
              ENNReal.ofReal (Real.sqrt (vecNormSq (qTilde - q)))) := by
        refine add_le_add le_rfl ?_
        rw [mul_add]
        refine add_le_add (ofReal_abs_volumeAverage_openCubeSet_vecDot_le hgradW hdiff) ?_
        have h := ofReal_abs_volumeAverage_openCubeSet_vecDot_le hgradW hconst
        rwa [vecCubeLpENorm_two_const Q (qTilde - q)] at h

/-! ## Annealed bookkeeping -/

/-- **Cauchy-Schwarz in the sample variable**, the "Cauchy-Schwarz inequality"
used in the proof of `l.RHS.term1`: for a
probability measure, `E[f g] ≤ (E[f²])^{1/2} (E[g²])^{1/2}`. -/
theorem lintegral_mul_le_rpow_half_mul_rpow_half
    (P : ProbabilityMeasure (ShellSeq d)) (f g : ShellSeq d → ℝ≥0∞)
    (hf : AEMeasurable f P.toMeasure) (hg : AEMeasurable g P.toMeasure) :
    (∫⁻ omega, f omega * g omega ∂P.toMeasure) ≤
      (∫⁻ omega, f omega ^ (2 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
        (∫⁻ omega, g omega ^ (2 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 2) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P.toMeasure
    Real.HolderConjugate.two_two hf hg
  have hrw : ∀ u : ShellSeq d → ℝ≥0∞,
      (∫⁻ a, u a ^ (2 : ℝ) ∂P.toMeasure) = ∫⁻ a, u a ^ (2 : ℕ) ∂P.toMeasure := by
    intro u
    refine lintegral_congr fun a => ?_
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simpa only [Pi.mul_apply, hrw] using h

/-! ## `e.decompose.flux.u.n.first`: Step 1 -/

/-! ## `e.decompose.flux.u.n.second`: Step 2 -/

/-! ## The `L̲²` display from `e.nablaw.Lt` -/

/-- Lowering the exponent of a normalized cube norm costs nothing: the
normalized cube measure is a probability measure. -/
theorem vecCubeLpENorm_mono_exponent (Q : TriadicCube d) {r s : ℝ≥0∞} (hrs : r ≤ s)
    {F : Vec d → Vec d}
    (_hF : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q r F ≤ vecCubeLpENorm Q s F := by
  let : MeasureTheory.IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hrs

end

end SuperdiffusionCLT.Section3.Terms
