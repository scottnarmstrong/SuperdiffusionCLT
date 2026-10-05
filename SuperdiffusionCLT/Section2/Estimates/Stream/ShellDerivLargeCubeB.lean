/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivLargeCube
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB

/-!
# One shell's derivative on a large cube

This file is the second half of the module: it is the continuation of
`ShellDerivLargeCube`, which it imports, and carries the finite-sum
envelope over a shell interval and the flux-Jacobian estimate required by the
hypothesis `hNablaKmnLow` of `l.w.basic.regbounds`.

The proof of `l.w.basic.regbounds`
bounds the Jacobian of the flux `(k_{L'} - k_{ℓ'})p` on `cu_m` by splitting it
at the scale `m - 1`; the small-cube estimate
`exists_witness_cubeLpENorm_streamFluxWeakGradient` covers the shells `k ≥ m`,
and the shells **below** the cube scale need the display
`‖∇(k_{m−1} − k_{ℓ'})p‖_{L̲^8(cu_m)} = O_{Γ₂}(C|p| 3^{-ℓ'})` of the hypothesis
`hNablaKmnLow` of `l.w.basic.regbounds`. The printed proof
gets those shells from stationarity over the `3^{d(m-k)}` sub-cubes of `cu_m`,
which is exactly the technique of the large-cube clauses.

This module proves that display, as the derivative analogue of the
value module `ShellValueLargeCube`; the route mirrors it exactly:

* on each scale-`k` sub-cube of `cu_m` the shell's derivative norm is the
  translated natural-cube derivative norm
  `ShellField.shellCubeDerivNorm k (ShellField.translate z (omega k))` with
  centre `z = cubeCenter R` (the half-open cube is reached through the
  closed-set extension used in `IncrementLinftyLargeCube`);
* each translated derivative norm has a symmetric `Gamma₂` tail at the
  **derivative scale** `3^{-k}`, by `J3` (through the factor `√d 3^k ‖∇j_k‖` of
  the `j3Observable`) and the one-shell stationarity of the prefix law, with
  no centering or independence hypothesis;
* the finite maximum over the `3^{d(m-k)}` sub-cubes costs the factor
  `(3 log N)^{1/2}` with `N = 3^{d(m-k)}`, that is
  `√(3 d log 3) * √(m-k)`; the amplitude is stated at the honest union-bound
  shape `shellDerivLargeCubeConst d * 3^{-k} * √(1 + (m-k))`, which also covers
  the boundary case `k = m`, where the sub-cube family is the singleton
  `{cu_k}` and the amplitude is the unit constant.

Only the prefix law (dimension and per-shell stationarity) and `J3` are
used; `J1`, `J2` and `J4` are not needed, because no sum, average or centring
of shells is taken.

## Main results

* `matrixDerivativeNorm_deriv_le_shellDerivLargeCubeSupBound` and its open-cube
  form: one random variable dominates
  `matrixDerivativeNorm (ShellField.deriv (omega k) x)` at every point of
  `cubeSet (originCube d m)`, and of the open cube.
* `isBigOWith_gammaSigma_translatedShellDerivSupBound`,
  `isBigOWith_gammaSigma_shellDerivLargeCubeSupBound`: the `Gamma₂` tails.
* `isBigOWith_gammaSigma_shellDerivLargeCubeSumSupBound`: the finite-sum tail
  at the amplitude `shellDerivLargeCubeSumConst d * 3^{-a} * √(1 + (m-a))`,
  the envelope of `∑_{k ∈ (a,b]} ∇ j_k` on `cu_m` with the constant
  `shellDerivLargeCubeSumConst d = gammaTriangleConst 2 * shellDerivLargeCubeConst d`.
* `norm_hilbertMat_streamFluxWeakGradient_le_largeCube` and
  `exists_witness_cubeLpENorm_streamFluxWeakGradient_largeCube`: the display
  required by the hypothesis `hNablaKmnLow` of `l.w.basic.regbounds`, in the carrier
  `HilbertMat.ofMat ∘ streamFluxWeakGradient` at the amplitude
  `(1 + √d * shellDerivLargeCubeSumConst d * √(1 + (m-a))) * (|p| 3^{-a})`.
  The only difference from the paper's printed amplitude `C |p| 3^{-ℓ'}`
  is the honest union-bound factor `√(1 + (m - a))`, which the printed proof
  absorbs into the dimensional constant `C` of the scale window.

## References

* `l.w.basic.regbounds` and the "Moreover" block of `l.ellip.k.scales.estimates`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Set
open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}
/-! ## The finite sum over a shell interval -/

/-- The finite sum of the large-cube derivative envelopes over the shell
interval `(a, b]`. -/
def shellDerivLargeCubeSumSupBound (a b m : ℕ) (omega : ShellSeq d) : ℝ :=
  ∑ k ∈ Finset.Ioc a b, shellDerivLargeCubeSupBound k m omega

theorem shellDerivLargeCubeSumSupBound_nonneg (a b m : ℕ)
    (omega : ShellSeq d) : 0 ≤ shellDerivLargeCubeSumSupBound a b m omega :=
  Finset.sum_nonneg fun k _ ↦ shellDerivLargeCubeSupBound_nonneg k m omega

theorem measurable_shellDerivLargeCubeSumSupBound (a b m : ℕ) :
    Measurable (shellDerivLargeCubeSumSupBound a b m :
      ShellSeq d → ℝ) :=
  Finset.measurable_sum _ fun k _ ↦ measurable_shellDerivLargeCubeSupBound k m

/-- The pointwise sum of the exact induced derivative norms of the shells
`(a, b]` on `cu_m` is bounded by the finite-sum envelope. -/
theorem matrixDerivativeNorm_sum_deriv_le_shellDerivLargeCubeSumSupBound
    (omega : ShellSeq d) {a b m : ℕ} (hbm : b ≤ m) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    (∑ k ∈ Finset.Ioc a b,
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ≤
      shellDerivLargeCubeSumSupBound a b m omega :=
  Finset.sum_le_sum fun _k hk ↦
    matrixDerivativeNorm_deriv_le_shellDerivLargeCubeSupBound omega
      ((Finset.mem_Ioc.mp hk).2.trans hbm) hx

/-- At every point of the half-open cube `cu_m` the exact induced norm of the
reconstructed derivative of `k_b − k_a` is bounded by the envelope. -/
theorem matrixDerivativeNorm_le_shellDerivLargeCubeSumSupBound
    (omega : ShellSeq d) {a b m : ℕ} (hbm : b ≤ m) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) ≤
      shellDerivLargeCubeSumSupBound a b m omega := by
  refine (matrixDerivativeNorm_finset_sum_le (Finset.Ioc a b)
    (fun k => ShellField.deriv (omega k) x)).trans ?_
  exact matrixDerivativeNorm_sum_deriv_le_shellDerivLargeCubeSumSupBound omega
    hbm hx

/-- The explicit dimensional constant of the finite sum, the `Γ₂` triangle
constant times the one-shell large-cube constant. -/
def shellDerivLargeCubeSumConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 * shellDerivLargeCubeConst d

theorem shellDerivLargeCubeSumConst_pos_of_pos (hd : 0 < d) :
    0 < shellDerivLargeCubeSumConst d :=
  mul_pos IndependentSums.gammaTriangleConst_pos
    (shellDerivLargeCubeConst_pos_of_pos hd)

theorem shellDerivLargeCubeSumConst_pos (hPrefix : ShellLawPrefix d P) :
    0 < shellDerivLargeCubeSumConst d :=
  shellDerivLargeCubeSumConst_pos_of_pos (lt_of_lt_of_le (by norm_num)
    hPrefix.dimension)

/-- A variable bounded above by zero at every point has every nonnegative
`Γ₂` amplitude: the tail event is empty (a local form of the zero lemma
proved in a module that is not imported here). -/
private theorem isBigOWith_gammaSigma_of_nonpos_pointwise
    {X : ShellSeq d → ℝ} {A : ℝ} (hA : 0 ≤ A) (hX : ∀ omega, X omega ≤ 0) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2) X A := by
  intro t ht
  have hAt : 0 ≤ A * t := mul_nonneg hA (le_trans zero_le_one ht)
  have hempty : IndependentSums.upperTailEvent X (A * t) =
      (∅ : Set (ShellSeq d)) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, Set.mem_empty_iff_false,
      iff_false, not_lt]
    linarith only [hX omega, hAt]
  rw [hempty, MeasureTheory.measureReal_empty, IndependentSums.gammaSigma_inv]
  exact Real.exp_nonneg _

/-- The `Γ₂` tail of the finite sum of the large-cube derivative envelopes
over `(a, b]` on `cu_m`: the finite `Γ₂` triangle over the shells at the
amplitudes `shellDerivLargeCubeConst d * 3^{-k} * √(1 + (m-k))`, summed by the
geometric tail estimate `∑_{k ∈ (a, b]} 3^{-k} ≤ 3^{-a}`. -/
theorem isBigOWith_gammaSigma_shellDerivLargeCubeSumSupBound
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {a b m : ℕ} (hab : a ≤ b) (hbm : b ≤ m) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (shellDerivLargeCubeSumSupBound a b m)
      (shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ a)⁻¹ *
        Real.sqrt (1 + ((m - a : ℕ) : ℝ))) := by
  have hconstpos : 0 < shellDerivLargeCubeConst d :=
    shellDerivLargeCubeConst_pos hPrefix
  rcases lt_or_eq_of_le hab with hlt | heq
  · -- The interval `(a, b]` is nonempty.
    have hsNonempty : (Finset.Ioc a b).Nonempty :=
      ⟨b + 1 - 1, by simp only [Finset.mem_Ioc]; omega⟩
    -- The one-shell amplitudes.
    have hAkpos : ∀ k ∈ Finset.Ioc a b,
        0 < shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
          Real.sqrt (1 + ((m - k : ℕ) : ℝ)) := by
      intro k _
      have hrpow : 0 < ((3 : ℝ) ^ k)⁻¹ :=
        inv_pos.2 (pow_pos (by norm_num : (0 : ℝ) < 3) k)
      have hsq : 0 < Real.sqrt (1 + ((m - k : ℕ) : ℝ)) := by
        refine Real.sqrt_pos.2 ?_
        have hcast : (0 : ℝ) ≤ ((m - k : ℕ) : ℝ) := by positivity
        linarith only [hcast]
      exact mul_pos (mul_pos hconstpos hrpow) hsq
    have hbigO : ∀ k ∈ Finset.Ioc a b,
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
          (fun omega : ShellSeq d ↦ shellDerivLargeCubeSupBound k m omega)
          (shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
            Real.sqrt (1 + ((m - k : ℕ) : ℝ))) := by
      intro k hk
      have hkm : k ≤ m := (Finset.mem_Ioc.mp hk).2.trans hbm
      exact (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (shellDerivLargeCubeSupBound_nonneg k m)).mp
        (isBigOWith_gammaSigma_shellDerivLargeCubeSupBound hPrefix hJ3 hkm)
    -- The finite `Γ₂` triangle inequality.
    have hsum : IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ shellDerivLargeCubeSumSupBound a b m omega)
        (IndependentSums.gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc a b,
          shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
            Real.sqrt (1 + ((m - k : ℕ) : ℝ))) := by
      have hmeas : ∀ k ∈ Finset.Ioc a b,
          Measurable (fun omega : ShellSeq d ↦
            shellDerivLargeCubeSupBound k m omega) := fun k _ ↦
        measurable_shellDerivLargeCubeSupBound k m
      exact IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
        (μ := P.toMeasure) (s := Finset.Ioc a b)
        (X := fun k omega ↦ shellDerivLargeCubeSupBound k m omega)
        (a := fun k ↦ shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
          Real.sqrt (1 + ((m - k : ℕ) : ℝ)))
        (σ := 2) (by norm_num) hsNonempty hAkpos hbigO hmeas
    -- The amplitude of the sum is bounded by the geometric tail estimate.
    have hsqrt : ∀ k ∈ Finset.Ioc a b,
        Real.sqrt (1 + ((m - k : ℕ) : ℝ)) ≤
          Real.sqrt (1 + ((m - a : ℕ) : ℝ)) := by
      intro k hk
      refine Real.sqrt_le_sqrt ?_
      have hka : a ≤ k := (Finset.mem_Ioc.mp hk).1.le
      have hsub : m - k ≤ m - a := by omega
      have hle : ((m - k : ℕ) : ℝ) ≤ ((m - a : ℕ) : ℝ) := by
        exact_mod_cast hsub
      linarith only [hle]
    have hinv : ∀ k ∈ Finset.Ioc a b, 0 ≤ ((3 : ℝ) ^ k)⁻¹ := by
      intro k _; positivity
    have hcore : (∑ k ∈ Finset.Ioc a b,
          ((3 : ℝ) ^ k)⁻¹ * Real.sqrt (1 + ((m - k : ℕ) : ℝ))) ≤
        ((3 : ℝ) ^ a)⁻¹ * Real.sqrt (1 + ((m - a : ℕ) : ℝ)) := by
      calc ∑ k ∈ Finset.Ioc a b,
          ((3 : ℝ) ^ k)⁻¹ * Real.sqrt (1 + ((m - k : ℕ) : ℝ)) ≤
            ∑ k ∈ Finset.Ioc a b,
              ((3 : ℝ) ^ k)⁻¹ * Real.sqrt (1 + ((m - a : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun k hk ↦
            mul_le_mul_of_nonneg_left (hsqrt k hk) (hinv k hk)
        _ = (∑ k ∈ Finset.Ioc a b, ((3 : ℝ) ^ k)⁻¹) *
              Real.sqrt (1 + ((m - a : ℕ) : ℝ)) :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ ((3 : ℝ) ^ a)⁻¹ * Real.sqrt (1 + ((m - a : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (SuperdiffusionCLT.Probability.sum_Ioc_inv_pow_three_le hab)
            (Real.sqrt_nonneg _)
    have hstep : (∑ k ∈ Finset.Ioc a b,
          shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
            Real.sqrt (1 + ((m - k : ℕ) : ℝ))) ≤
        shellDerivLargeCubeConst d * (((3 : ℝ) ^ a)⁻¹ *
          Real.sqrt (1 + ((m - a : ℕ) : ℝ))) := by
      have hreassoc : (∑ k ∈ Finset.Ioc a b,
          shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
            Real.sqrt (1 + ((m - k : ℕ) : ℝ))) =
          shellDerivLargeCubeConst d * ∑ k ∈ Finset.Ioc a b,
            (((3 : ℝ) ^ k)⁻¹ * Real.sqrt (1 + ((m - k : ℕ) : ℝ))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ ↦ mul_assoc _ _ _
      rw [hreassoc]
      exact mul_le_mul_of_nonneg_left hcore (by positivity)
    have hshape : IndependentSums.gammaTriangleConst 2 *
        (shellDerivLargeCubeConst d * (((3 : ℝ) ^ a)⁻¹ *
          Real.sqrt (1 + ((m - a : ℕ) : ℝ)))) =
        (IndependentSums.gammaTriangleConst 2 * shellDerivLargeCubeConst d) *
          ((3 : ℝ) ^ a)⁻¹ * Real.sqrt (1 + ((m - a : ℕ) : ℝ)) := by
      ring
    have hampl : IndependentSums.gammaTriangleConst 2 *
        ∑ k ∈ Finset.Ioc a b,
          shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
            Real.sqrt (1 + ((m - k : ℕ) : ℝ)) ≤
        (IndependentSums.gammaTriangleConst 2 * shellDerivLargeCubeConst d) *
          ((3 : ℝ) ^ a)⁻¹ * Real.sqrt (1 + ((m - a : ℕ) : ℝ)) := by
      refine le_trans (mul_le_mul_of_nonneg_left hstep
        (IndependentSums.gammaTriangleConst_pos).le) ?_
      rw [hshape]
    -- Convert to the one-sided predicate and scale down.
    have hfrom : IndependentSums.IsBigOWith P.toMeasure
        (IndependentSums.gammaSigma 2)
        (shellDerivLargeCubeSumSupBound a b m)
        (IndependentSums.gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc a b,
          shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ *
            Real.sqrt (1 + ((m - k : ℕ) : ℝ))) :=
      (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (shellDerivLargeCubeSumSupBound_nonneg a b m)).mpr hsum
    have htarget : shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ a)⁻¹ *
        Real.sqrt (1 + ((m - a : ℕ) : ℝ)) =
        (IndependentSums.gammaTriangleConst 2 * shellDerivLargeCubeConst d) *
          ((3 : ℝ) ^ a)⁻¹ * Real.sqrt (1 + ((m - a : ℕ) : ℝ)) := by
      rw [shellDerivLargeCubeSumConst]
    rw [htarget]
    exact hfrom.mono_scale hampl
  · -- `a = b`: the interval is empty and the envelope is the zero variable.
    have hIoc : Finset.Ioc a b = ∅ := by
      rw [heq]
      exact Finset.Ioc_self b
    have hpoint : ∀ omega : ShellSeq d,
        shellDerivLargeCubeSumSupBound a b m omega ≤ 0 := by
      intro omega
      rw [shellDerivLargeCubeSumSupBound, hIoc, Finset.sum_empty]
    have htarget : 0 ≤ shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ a)⁻¹ *
        Real.sqrt (1 + ((m - a : ℕ) : ℝ)) := by
      refine mul_nonneg ?_ ?_
      · refine mul_nonneg ?_ ?_
        · exact (shellDerivLargeCubeSumConst_pos hPrefix).le
        · positivity
      · exact Real.sqrt_nonneg _
    exact isBigOWith_gammaSigma_of_nonpos_pointwise htarget hpoint

/-! ## The Jacobian of the flux on a large cube -/

/-- **The pointwise Jacobian bound of the flux on a large cube.** On the
half-open cube `cu_m` the Frobenius norm of the Jacobian of `(k_b − k_a)p`,
for the shells `k ∈ (a, b]` **below or at the cube scale** (`b ≤ m`), is at
most `√d |p|` times the large-cube derivative envelope of the shells (each
column is the image of a unit vector, and there are `d` columns). The
large-cube analogue of `norm_hilbertMat_streamFluxWeakGradient_le`, which
covers the shells above the cube scale. -/
theorem norm_hilbertMat_streamFluxWeakGradient_le_largeCube
    (omega : ShellSeq d) {a b m : ℕ} (hab : a ≤ b) (hbm : b ≤ m) (p : Vec d)
    {x : Vec d} (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    ‖HilbertMat.ofMat
        (fun i j => streamFluxWeakGradient omega a b p i x j)‖ ≤
      Real.sqrt d * vecNorm p * shellDerivLargeCubeSumSupBound a b m omega := by
  have hGnonneg : 0 ≤ shellDerivLargeCubeSumSupBound a b m omega :=
    shellDerivLargeCubeSumSupBound_nonneg a b m omega
  have hDG : ShellField.matrixDerivativeNorm
      (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) ≤
      shellDerivLargeCubeSumSupBound a b m omega :=
    matrixDerivativeNorm_le_shellDerivLargeCubeSumSupBound omega hbm hx
  have hcol : ∀ j : Fin d, matrixOperatorNorm
      ((∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) (basisVec j)) ≤
      shellDerivLargeCubeSumSupBound a b m omega := by
    intro j
    refine le_trans ?_ hDG
    have h := matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm
      (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) (basisVec j)
    rwa [vecNorm_basisVec, mul_one] at h
  have hsum : ∑ i : Fin d, ∑ j : Fin d,
      streamFluxWeakGradient omega a b p i x j *
        streamFluxWeakGradient omega a b p i x j ≤
      (d : ℝ) * (shellDerivLargeCubeSumSupBound a b m omega ^ 2 *
        vecNormSq p) := by
    have hswap : ∑ i : Fin d, ∑ j : Fin d,
        streamFluxWeakGradient omega a b p i x j *
          streamFluxWeakGradient omega a b p i x j =
        ∑ j : Fin d, vecNormSq (matVecMul
          ((∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) (basisVec j))
          p) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [streamFluxWeakGradient_apply omega hab p i x j]
    rw [hswap]
    calc
      ∑ j : Fin d, vecNormSq (matVecMul
          ((∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) (basisVec j))
          p) ≤
          ∑ _j : Fin d, (shellDerivLargeCubeSumSupBound a b m omega ^ 2 *
            vecNormSq p) := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine
          (vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq _ _).trans ?_
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) (hcol j) 2)
          (vecNormSq_nonneg p)
      _ = (d : ℝ) * (shellDerivLargeCubeSumSupBound a b m omega ^ 2 *
            vecNormSq p) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : 0 ≤ Real.sqrt d * vecNorm p *
      shellDerivLargeCubeSumSupBound a b m omega :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg p)) hGnonneg
  have hsq : ‖HilbertMat.ofMat
      (fun i j => streamFluxWeakGradient omega a b p i x j)‖ ^ 2 ≤
      (Real.sqrt d * vecNorm p * shellDerivLargeCubeSumSupBound a b m omega) ^ 2 := by
    refine (norm_sq_hilbertMat_ofMat
      (fun i j => streamFluxWeakGradient omega a b p i x j)).le.trans (hsum.trans_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d),
      vecNorm_sq_eq_vecNormSq]
    ring
  have hfin := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hB] at hfin

/-- **The Jacobian of the flux on a large cube, in the `∃ Z` shape of the
response estimates.** The shells `k ∈ (a, b]` with `b ≤ m` — the shells
**below or at the cube scale** — have their Jacobian `(k_b − k_a)p` dominated
on `cu_m`, in every `L̲^q(cu_m)` norm, by a witness with the `Γ₂` tail at the
amplitude `(√d · shellDerivLargeCubeSumConst d · √(1 + (m − a))) · (|p| 3^{-a})`.
This is the estimate required by the hypothesis `hNablaKmnLow` of
`l.w.basic.regbounds` for the shells below the cube scale; the printed amplitude `C |p| 3^{-ℓ'}`
differs only by the honest union-bound factor `√(1 + (m − a))`, absorbed into
the dimensional constant `C` quantified after the scale selection. -/
theorem exists_witness_cubeLpENorm_streamFluxWeakGradient_largeCube
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (p : Vec d)
    {a b m : ℕ} (hab : a ≤ b) (hbm : b ≤ m) :
    ∃ Z : ShellSeq d → ℝ, Measurable Z ∧
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) Z
        ((Real.sqrt d * shellDerivLargeCubeSumConst d *
            Real.sqrt (1 + ((m - a : ℕ) : ℝ))) *
          (Real.sqrt (vecNormSq p) * (3 : ℝ) ^ (-(a : ℝ)))) ∧
      ∀ (q : ℝ≥0∞) (omega : ShellSeq d),
        Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) q
            (fun x => HilbertMat.ofMat
              (fun i j => streamFluxWeakGradient omega a b p i x j)) ≤
          ENNReal.ofReal (Z omega) := by
  have hconst : (0 : ℝ) ≤ Real.sqrt d * vecNorm p :=
    mul_nonneg (Real.sqrt_nonneg _) (vecNorm_nonneg p)
  have hsqrtp : Real.sqrt (vecNormSq p) = vecNorm p := by
    rw [← vecNorm_sq_eq_vecNormSq, Real.sqrt_sq (vecNorm_nonneg p)]
  refine ⟨fun omega =>
      Real.sqrt d * vecNorm p * shellDerivLargeCubeSumSupBound a b m omega,
    (measurable_shellDerivLargeCubeSumSupBound a b m).const_mul _, ?_, ?_⟩
  · have htarget : (Real.sqrt d * shellDerivLargeCubeSumConst d *
        Real.sqrt (1 + ((m - a : ℕ) : ℝ))) *
        (Real.sqrt (vecNormSq p) * (3 : ℝ) ^ (-(a : ℝ))) =
      (Real.sqrt d * vecNorm p) * (shellDerivLargeCubeSumConst d *
        ((3 : ℝ) ^ a)⁻¹ * Real.sqrt (1 + ((m - a : ℕ) : ℝ))) := by
      rw [hsqrtp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) ((a : ℕ) : ℝ),
        Real.rpow_natCast]
      ring
    rw [htarget]
    exact
      (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (fun omega =>
          mul_nonneg hconst
            (shellDerivLargeCubeSumSupBound_nonneg a b m omega))).1
        ((isBigOWith_gammaSigma_shellDerivLargeCubeSumSupBound hPrefix hJ3 hab
          hbm).const_mul hconst)
  · intro q omega
    have hbase : Continuous (fun x : Vec d =>
        ((fun i j => streamFluxWeakGradient omega a b p i x j) : Mat d)) :=
      continuous_pi fun i => continuous_pi fun j =>
        (ContinuousLinearMap.apply ℝ ℝ (basisVec j)).continuous.comp
          ((contDiff_streamFlux_apply omega hab p i).continuous_fderiv (by simp))
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun x : Vec d => HilbertMat.ofMat
        (fun i j => streamFluxWeakGradient omega a b p i x j))
        (normalizedCubeMeasure (originCube d (m : ℤ))) :=
      ((HilbertMat.continuousLinearEquivMat d).symm.continuous.comp
        hbase).aestronglyMeasurable
    exact cubeLpENorm_le_of_forall_mem_openCubeSet hmeas (fun x hx =>
      norm_hilbertMat_streamFluxWeakGradient_le_largeCube omega hab hbm p
        (openCubeSet_subset_cubeSet _ hx))

end

end SuperdiffusionCLT.Section2.Estimates.Stream
