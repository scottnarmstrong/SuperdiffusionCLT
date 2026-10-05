/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Integrability

/-!
# The two `P`-integrability side conditions of term 3: `hPair` and `_hbHalfInt`

The final assembly of `e.RHS.term3` carries two sample-side
integrability residues beyond the five printed steps:

* `hPair`, the `P`-integrability of the very left-hand side of the
  conclusion;
* `_hbHalfInt`, the half-weight carrier on the printed range of
  `e.bL.to.bhomell`: `z'` a sub-cube of `cu_m` and `z` a
  sub-cube of `z'`.

## `hPair`, discharged

`hPair_discharged_B` closes `hPair` from the statement's own binders,
through the pairing engine `integrable_volumeAverage_pairing_final` of
`RHSTerm3Integrability.lean`.  The engine's six carriers are produced here:

* the response-gradient `L²(cu_m)` class is measurable because it agrees with
  `gradToHilbertVectorL2` of the family, which by choice independence is the
  canonical Dirichlet response
  (`gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse`) of
  a measurable function of the sample
  (`measurable_gradToHilbertVectorL2_dirichletResponse`);
* the cutoff flux of the glued-field difference is `L²(cu_m)` by
  `memVectorL2_matVecMul_coefficientCutoff` applied to a difference of two glued
  gradients, and its class is measurable as a Caratheodory multiplication of the
  measurable glued class (`measurable_gluedGradientClass`) by the jointly
  measurable cutoff family (`measurable_matFieldMulClass_family`);
* the response-gradient second moment is finite by the fourth moment
  `gradFour_finite_of_regbounds` together with the exponent downgrade
  `‖·‖_{L̲²} ≤ ‖·‖_{L̲⁴}` and `a² ≤ 1 + a⁴` on `ℝ≥0∞`;
* the flux second moment is finite because the cutoff coefficient is bounded on
  `cu_m` by `coeffLinftySupBound nu S.LPrime S.m` and the glued-field difference
  has deterministic energy `2 nu⁻¹ √(vecNormSq F)`, so the second moment is the
  second moment of the envelope, finite at the enlarged cutoff
  (`lintegral_coeffLinftySupBound_sq_ne_top_B`).

The other residue, `_hbHalfInt`, is discharged in `RHSTerm3IntegLeaves`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Elementary carriers -/

/-- The square root of the squared energy factor `nu⁻¹ * nu⁻¹ * vecNormSq F` is
the linear energy factor `nu⁻¹ * Real.sqrt (vecNormSq F)`. -/
private theorem sqrt_invSq_mul_vecNormSq_B {d : ℕ} {nu : ℝ} (hnu : 0 < nu) (F : Vec d) :
    Real.sqrt (nu⁻¹ * nu⁻¹ * vecNormSq F) = nu⁻¹ * Real.sqrt (vecNormSq F) := by
  have h0 : (0 : ℝ) ≤ nu⁻¹ := (inv_pos.2 hnu).le
  rw [show nu⁻¹ * nu⁻¹ * vecNormSq F = nu⁻¹ ^ 2 * vecNormSq F by ring,
    Real.sqrt_mul (sq_nonneg nu⁻¹), Real.sqrt_sq h0]

/-- **The response gradient class is sample-measurable**, for any family of
Dirichlet responses.  Choice independence writes it as the gradient class of the
canonical response, which is measurable because the solution operator is
continuous and the flux class is measurable. -/
private theorem measurable_gradClass_isDirichletResponse_B [NeZero d]
    {LPrime ellPrime m : ℕ} {p : Vec d}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    Measurable fun omega : ShellSeq d => (w omega).toH1Function.gradToHilbertVectorL2 := by
  have hfun : (fun omega : ShellSeq d => (w omega).toH1Function.gradToHilbertVectorL2) =
      fun omega : ShellSeq d =>
        (dirichletResponse omega LPrime ellPrime m p).toH1Function.gradToHilbertVectorL2 := by
    funext omega
    exact (gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse omega
        (hw omega)).trans
      (gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse omega
        (isDirichletResponse_dirichletResponse omega LPrime ellPrime m p)).symm
  rw [hfun]
  exact measurable_gradToHilbertVectorL2_dirichletResponse

/-! ## The response-gradient second moment -/

/-- **`E[‖∇w‖²_{L̲²(cu_m)}] < ∞`** at the cube scale of the statement.
The fourth moment `gradFour_finite_of_regbounds` gives the exponent `4`;
the exponent downgrade `‖·‖_{L̲²} ≤ ‖·‖_{L̲⁴}` together with `a² ≤ 1 + a⁴` on
`ℝ≥0∞` transfers it to the exponent `2`, and the constant `1` is integrated
against a probability measure. -/
private theorem lintegral_gradTwo_sq_ne_top_B [NeZero d] (hd : 2 ≤ d) {nu : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    (∫⁻ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ := by
  have h4 := gradFour_finite_of_regbounds hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  have hpt : ∀ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ) ≤
        1 + (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ) := by
    intro omega
    have hdown : vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad ≤
        vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad :=
      vecCubeLpENorm_mono_exponent (originCube d (S.m : ℤ)) (by norm_num)
        (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
          (w omega).toH1Function.grad_memVectorL2)
    refine (pow_le_pow_left' hdown 2).trans ?_
    rcases le_total (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
        (w omega).toH1Function.grad) 1 with ha | ha
    · calc (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (2 : ℕ)
          ≤ (1 : ℝ≥0∞) ^ (2 : ℕ) := pow_le_pow_left' ha 2
        _ = 1 := one_pow 2
        _ ≤ 1 + (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
              (w omega).toH1Function.grad) ^ (4 : ℕ) := le_self_add
    · have h1 : (1 : ℝ≥0∞) ≤
          (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (2 : ℕ) := by
        calc (1 : ℝ≥0∞) = (1 : ℝ≥0∞) ^ (2 : ℕ) := (one_pow 2).symm
          _ ≤ (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
                (w omega).toH1Function.grad) ^ (2 : ℕ) := pow_le_pow_left' ha 2
      calc (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (2 : ℕ)
          = (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (2 : ℕ) *
              1 := (mul_one _).symm
        _ ≤ (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (2 : ℕ) *
              (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
                (w omega).toH1Function.grad) ^ (2 : ℕ) := mul_le_mul' le_rfl h1
        _ = (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ) := by
            rw [← pow_add]
        _ ≤ 1 + (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
              (w omega).toH1Function.grad) ^ (4 : ℕ) := le_add_self
  have h1fin : (∫⁻ _ : ShellSeq d, (1 : ℝ≥0∞) ∂P.toMeasure) < ⊤ := by
    rw [lintegral_one, measure_univ]
    exact ENNReal.one_lt_top
  refine ne_of_lt ?_
  calc (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ)
        ∂P.toMeasure)
      ≤ ∫⁻ omega : ShellSeq d,
          (1 + (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
            (w omega).toH1Function.grad) ^ (4 : ℕ)) ∂P.toMeasure := lintegral_mono hpt
    _ = (∫⁻ _ : ShellSeq d, (1 : ℝ≥0∞) ∂P.toMeasure) +
          ∫⁻ omega : ShellSeq d,
            (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
              (w omega).toH1Function.grad) ^ (4 : ℕ) ∂P.toMeasure :=
        lintegral_add_left' aemeasurable_const _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h1fin, lt_top_iff_ne_top.2 h4⟩

/-! ## The deterministic energy of the glued-field difference

The scale-`m` and scale-`n` glued fields both satisfy the intermediate-scale
energy bound `vecCubeLpENorm_two_sq_gluedGradientField_le` on `cu_m`, so the
difference has deterministic `L̲²(cu_m)` norm at most `2 nu⁻¹ √(vecNormSq F)`. -/

/-- The `ℝ`-valued energy bound for the glued-field difference on `cu_m`. -/
private theorem toReal_gluedDiff_le_B [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {S : ScaleSelection} (hSorder : ScalesOrdering S) (F : Vec d) (omega : ShellSeq d) :
    (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun y : Vec d => gluedGradientField hnu S.LPrime S.m S.m F omega y -
        gluedGradientField hnu S.LPrime S.n S.m F omega y)).toReal ≤
      2 * (nu⁻¹ * Real.sqrt (vecNormSq F)) := by
  classical
  have hnm : S.n ≤ S.m := (ScalesOrdering.mem_pigeon_range hSorder).1.2
  have hinu0 : (0 : ℝ) ≤ nu⁻¹ := (inv_pos.2 hnu).le
  have hc0 : 0 ≤ nu⁻¹ * nu⁻¹ * vecNormSq F :=
    mul_nonneg (mul_nonneg hinu0 hinu0) (vecNormSq_nonneg F)
  have hAm : (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (gluedGradientField hnu S.LPrime S.m S.m F omega)).toReal ≤
      nu⁻¹ * Real.sqrt (vecNormSq F) :=
    (vecCubeLpENorm_toReal_le_of_sq_le hc0
      (vecCubeLpENorm_two_sq_gluedGradientField_le hnu (le_refl S.m) (le_refl S.m)
        S.LPrime F omega)).trans_eq (sqrt_invSq_mul_vecNormSq_B hnu F)
  have hAn : (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (gluedGradientField hnu S.LPrime S.n S.m F omega)).toReal ≤
      nu⁻¹ * Real.sqrt (vecNormSq F) :=
    (vecCubeLpENorm_toReal_le_of_sq_le hc0
      (vecCubeLpENorm_two_sq_gluedGradientField_le hnu hnm (le_refl S.m)
        S.LPrime F omega)).trans_eq (sqrt_invSq_mul_vecNormSq_B hnu F)
  have hmGm : MemLp (hilbertifyVecField (gluedGradientField hnu S.LPrime S.m S.m F omega)) 2
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) :=
    SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
      (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m F omega
        (originCube d (S.m : ℤ)))
  have hmGn : MemLp (hilbertifyVecField (gluedGradientField hnu S.LPrime S.n S.m F omega)) 2
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) :=
    SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
      (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega
        (originCube d (S.m : ℤ)))
  have htri : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y : Vec d => gluedGradientField hnu S.LPrime S.m S.m F omega y -
          gluedGradientField hnu S.LPrime S.n S.m F omega y) ≤
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (gluedGradientField hnu S.LPrime S.m S.m F omega) +
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.LPrime S.n S.m F omega) := by
    have h := vecCubeLpENorm_add_le (Q := originCube d (S.m : ℤ)) (q := 2)
      (F := gluedGradientField hnu S.LPrime S.m S.m F omega)
      (G := fun y : Vec d => -gluedGradientField hnu S.LPrime S.n S.m F omega y)
      (by norm_num) hmGm.aestronglyMeasurable hmGn.neg.aestronglyMeasurable
    simpa only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, vecCubeLpENorm_neg] using h
  have hfinGm : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (gluedGradientField hnu S.LPrime S.m S.m F omega) ≠ ⊤ := hmGm.eLpNorm_lt_top.ne
  have hfinGn : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (gluedGradientField hnu S.LPrime S.n S.m F omega) ≠ ⊤ := hmGn.eLpNorm_lt_top.ne
  have htoReal : (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y : Vec d => gluedGradientField hnu S.LPrime S.m S.m F omega y -
          gluedGradientField hnu S.LPrime S.n S.m F omega y)).toReal ≤
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.LPrime S.m S.m F omega)).toReal +
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.LPrime S.n S.m F omega)).toReal := by
    have hsumtop : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.LPrime S.m S.m F omega) +
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (gluedGradientField hnu S.LPrime S.n S.m F omega) ≠ ⊤ :=
      (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hfinGm,
        lt_top_iff_ne_top.2 hfinGn⟩).ne
    have h1 := ENNReal.toReal_mono hsumtop htri
    rwa [ENNReal.toReal_add hfinGm hfinGn] at h1
  calc (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y : Vec d => gluedGradientField hnu S.LPrime S.m S.m F omega y -
          gluedGradientField hnu S.LPrime S.n S.m F omega y)).toReal
      ≤ (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.LPrime S.m S.m F omega)).toReal +
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.LPrime S.n S.m F omega)).toReal := htoReal
    _ ≤ nu⁻¹ * Real.sqrt (vecNormSq F) + nu⁻¹ * Real.sqrt (vecNormSq F) := add_le_add hAm hAn
    _ = 2 * (nu⁻¹ * Real.sqrt (vecNormSq F)) := by ring

/-! ## The second moment of the cutoff flux of the difference -/

/-- **`E[‖a_{L'}(∇u_m − ∇u_n)‖²_{L̲²(cu_m)}] < ∞`.**  The multiplier bound
`vecCubeLpENorm_matVecMul_le` and the a.e. operator envelope
`ae_matrixOperatorNorm_coefficientCutoff_le` dominate the norm by
`coeffLinftySupBound nu S.LPrime S.m * 2 nu⁻¹ √(vecNormSq F)`, so its square is
the square of the envelope times a constant, and the envelope square is
`P`-integrable at the enlarged cutoff
(`lintegral_coeffLinftySupBound_sq_ne_top_B`). -/
private theorem lintegral_gluedDiff_sq_ne_top_B [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (F : Vec d) :
    (∫⁻ omega : ShellSeq d, (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun y : Vec d => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m F omega y -
          gluedGradientField hnu S.LPrime S.n S.m F omega y))) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ := by
  classical
  have hmpos : 0 < S.m := lt_of_le_of_lt (Nat.zero_le _) hSorder.ellPrime_lt_m
  have hLpos : 0 < S.LPrime := lt_trans hmpos hSorder.m_lt_LPrime
  have hnu0 : (0 : ℝ) ≤ nu := hnu.le
  set D : ℝ := 2 * (nu⁻¹ * Real.sqrt (vecNormSq F)) with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact mul_nonneg (by norm_num) (mul_nonneg (inv_pos.2 hnu).le (Real.sqrt_nonneg _))
  have hmemD : ∀ omega : ShellSeq d, MemLp (hilbertifyVecField
      (fun y : Vec d => gluedGradientField hnu S.LPrime S.m S.m F omega y -
        gluedGradientField hnu S.LPrime S.n S.m F omega y)) 2
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := fun omega =>
    SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
      ((memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m F omega
          (originCube d (S.m : ℤ))).sub
        (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega
          (originCube d (S.m : ℤ))))
  have hdiff_le : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y : Vec d => gluedGradientField hnu S.LPrime S.m S.m F omega y -
          gluedGradientField hnu S.LPrime S.n S.m F omega y) ≤ ENNReal.ofReal D := by
    intro omega
    have hne : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y : Vec d => gluedGradientField hnu S.LPrime S.m S.m F omega y -
          gluedGradientField hnu S.LPrime S.n S.m F omega y) ≠ ⊤ :=
      (hmemD omega).eLpNorm_lt_top.ne
    refine (ENNReal.le_ofReal_iff_toReal_le hne hD0).2 ?_
    rw [hDdef]
    exact toReal_gluedDiff_le_B hnu hSorder F omega
  have hpt : ∀ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y : Vec d => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m F omega y -
            gluedGradientField hnu S.LPrime S.n S.m F omega y))) ^ (2 : ℕ) ≤
      ENNReal.ofReal (D ^ 2) *
        (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega)) ^ (2 : ℕ) := by
    intro omega
    have hc0 : 0 ≤ coeffLinftySupBound nu S.LPrime S.m omega :=
      coeffLinftySupBound_nonneg nu hnu0 S.LPrime S.m omega
    have h1 : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun y : Vec d => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m F omega y -
            gluedGradientField hnu S.LPrime S.n S.m F omega y)) ≤
        ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega) * ENNReal.ofReal D := by
      calc vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun y : Vec d => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m F omega y -
                gluedGradientField hnu S.LPrime S.n S.m F omega y))
          ≤ ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega) *
              vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun y : Vec d => gluedGradientField hnu S.LPrime S.m S.m F omega y -
                  gluedGradientField hnu S.LPrime S.n S.m F omega y) :=
            vecCubeLpENorm_matVecMul_le 2
              (fun x : Vec d => (coefficientCutoff nu omega S.LPrime).toCoeffField x)
              (fun y : Vec d => gluedGradientField hnu S.LPrime S.m S.m F omega y -
                gluedGradientField hnu S.LPrime S.n S.m F omega y) hc0
              (aestronglyMeasurable_hilbertifyVecField_matVecMul
                (continuous_coefficientCutoff_apply nu omega S.LPrime)
                (hmemD omega).aestronglyMeasurable)
              (ae_matrixOperatorNorm_coefficientCutoff_le hnu0 omega S.LPrime S.m)
        _ ≤ ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega) *
              ENNReal.ofReal D := mul_le_mul' le_rfl (hdiff_le omega)
    calc (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun y : Vec d => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m F omega y -
              gluedGradientField hnu S.LPrime S.n S.m F omega y))) ^ (2 : ℕ)
        ≤ (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega) *
            ENNReal.ofReal D) ^ (2 : ℕ) := pow_le_pow_left' h1 2
      _ = (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega)) ^ (2 : ℕ) *
            ENNReal.ofReal (D ^ 2) := by
          rw [mul_pow, ← ENNReal.ofReal_pow hD0 2]
      _ = ENNReal.ofReal (D ^ 2) *
            (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega)) ^ (2 : ℕ) :=
          mul_comm _ _
  have hmeas : AEMeasurable (fun omega : ShellSeq d =>
      (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega)) ^ (2 : ℕ)) P.toMeasure :=
    (((ENNReal.continuous_ofReal.measurable.comp
      (measurable_coeffLinftySupBound nu S.LPrime S.m)).aemeasurable).pow_const 2)
  have hmul : ENNReal.ofReal (D ^ 2) * (∫⁻ omega : ShellSeq d,
      (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega)) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (lintegral_coeffLinftySupBound_sq_ne_top_B hPrefix hJ2 hJ3 hJ4 hnu0 hLpos hmpos)
  exact ne_top_of_le_ne_top hmul (by
    calc (∫⁻ omega : ShellSeq d, (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun y : Vec d => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m F omega y -
              gluedGradientField hnu S.LPrime S.n S.m F omega y))) ^ (2 : ℕ) ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d, ENNReal.ofReal (D ^ 2) *
            (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega)) ^ (2 : ℕ)
            ∂P.toMeasure := lintegral_mono hpt
      _ = ENNReal.ofReal (D ^ 2) * ∫⁻ omega : ShellSeq d,
            (ENNReal.ofReal (coeffLinftySupBound nu S.LPrime S.m omega)) ^ (2 : ℕ)
            ∂P.toMeasure := lintegral_const_mul'' _ hmeas)

/-! ## `hPair`, discharged -/

/-- **The `hPair` carrier of the final assembly, discharged from
its own binders.**  The cube mean over `cu_m` of the pairing of the response gradient
with the cutoff flux of the glued-field difference is `P`-integrable by the
pairing engine, whose six carriers are supplied above. -/
theorem hPair_discharged_B [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun y : Vec d => vecDot ((w omega).toH1Function.grad y)
          (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e) omega y))))
      P.toMeasure := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  refine integrable_volumeAverage_pairing_final (Q := originCube d (S.m : ℤ))
    (Rf := fun omega : ShellSeq d => (w omega).toH1Function.grad)
    (gf := fun omega : ShellSeq d => fun y : Vec d =>
      matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e) omega y -
          gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e) omega y))
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro omega
    exact (w omega).toH1Function.grad_memVectorL2
  · have heq : (fun omega : ShellSeq d =>
        toHilbertVectorL2OfVecField ((w omega).toH1Function.grad_memVectorL2)) =
        fun omega : ShellSeq d => (w omega).toH1Function.gradToHilbertVectorL2 := by
      funext omega
      rfl
    rw [heq]
    exact (measurable_gradClass_isDirichletResponse_B (LPrime := S.LPrime)
      (ellPrime := S.ellPrime) (m := S.m) (p := testVector nu S.LPrime P S.n e) hw).aemeasurable
  · intro omega
    exact memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime (originCube d (S.m : ℤ))
      ((memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m
          (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ))).sub
        (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ))))
  · have heq : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
        (memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime (originCube d (S.m : ℤ))
          ((memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m
              (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ))).sub
            (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))))) =
        fun omega : ShellSeq d => matFieldMulClass
          (fun y : Vec d => (coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (fun f : Vec d → Vec d => fun hf : MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) f =>
            memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime
              (originCube d (S.m : ℤ)) hf)
          (toHilbertVectorL2OfVecField
              (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m
                (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ))) -
            toHilbertVectorL2OfVecField
              (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))) := by
      funext omega
      rw [← toHilbertVectorL2OfVecField_sub
            (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m
              (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))
            (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ))),
          matFieldMulClass_toHilbertVectorL2OfVecField]
    rw [heq]
    refine measurable_matFieldMulClass_family (mu := P.toMeasure) (U := openCubeSet (originCube d (S.m : ℤ)))
      (measurableSet_openCubeSet (originCube d (S.m : ℤ)))
      (fun omega : ShellSeq d => fun y : Vec d =>
        (coefficientCutoff nu omega S.LPrime).toCoeffField y)
      (measurable_prod_coefficientCutoff nu S.LPrime)
      (fun omega f hf => memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime
        (originCube d (S.m : ℤ)) hf) ?_ ?_
    · intro omega
      exact exists_matVecMul_bound_openCubeSet (originCube d (S.m : ℤ))
        (fun i j => continuous_coefficientCutoff_entry nu omega S.LPrime i j)
    · have hgclass : Measurable (fun omega : ShellSeq d =>
          toHilbertVectorL2OfVecField
              (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m
                (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ))) -
            toHilbertVectorL2OfVecField
              (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))) :=
        (measurable_gluedGradientClass (d := d) hnu S.LPrime S.m S.m
          (fluxSlot nu S.LPrime P S.n e)).sub
          (measurable_gluedGradientClass (d := d) hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e))
      exact hgclass.aemeasurable
  · exact lintegral_gradTwo_sq_ne_top_B hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw
  · exact lintegral_gluedDiff_sq_ne_top_B hnu hPrefix hJ2 hJ3 hJ4 S hSorder
      (fluxSlot nu S.LPrime P S.n e)

end

end SuperdiffusionCLT.Section3.Terms
