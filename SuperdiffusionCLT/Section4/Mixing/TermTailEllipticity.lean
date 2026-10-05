/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Measurability
public import Homogenization.CoarseGraining.MuAdmissibility
public import Homogenization.CoarseGraining.CubeMinimizer
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Existence
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.QuadraticMu
public import Homogenization.CoarseGraining.BlockFormalism.EllipticBounds
public import Homogenization.Sobolev.PotentialSolenoidalL2OriginCubeBridge

/-!
# mixTail: the deterministic ellipticity bound on `s_{L,*}^{-1}(cu_n)`

The printed statement is: "By `e.CG.bounds.1`, since the
symmetric part of `a_m` is `nu Id`, `|s_{m,*}^{-1}(U)| <= nu^{-1}`." This
module proves that Loewner bound for the marginal cutoff field, needed for the tail comparison of
`p.mixing.P.three.prime#term2-scale-comparison` (`Section4/Mixing/Term2ScaleComparison.lean`)
via a Hölder-type bound on the tail-weighted expectation `E[X * sigmaStarInvCoarse(cu_n)]`.

The route is the same one `CoarseGraining.CoarseBounds.Sandwich` uses for the
`(1, Theta)`-normalized case (a constant-competitor argument testing `Mu` at
`(0, y)`), generalized to the actual `(nu, Lam)` ellipticity of the cutoff
field, and specialized to the exact identity `symmPart (a_L x) = nu • 1`
(`symmPart_coefficientCutoff`), which makes the pointwise lower-right block of
`blockMatrixOfCoeff (a_L x)` the *constant* matrix `nu⁻¹ • 1`, giving the sharp
constant `nu⁻¹` (not merely some `C(nu)`).

## Main results

* `mixTail_isEllipticFieldOn_coefficientCutoff`: the cutoff field is
  (everywhere, not merely a.e.) `(nu, Lam)`-elliptic on every triadic cube, for
  an explicit sample-dependent `Lam`.
* `mixTail_hasQuadraticMu_cubeSet_originCube`: `Mu` is quadratic on
  `cubeSet (originCube d n)` for any `(lam, Lam)`-elliptic field.
* `mixTail_mu_eq_half_coarseBlockMatrix_cubeSet_originCube`: the bridge
  `Mu (cubeSet (originCube d n)) P a = (1/2) P . coarseBlockMatrix(...) P`.
* `mixTail_sigmaStarInvCoarse_le_inv_smul_one`: the sharp bound
  `MatLoewnerLE (sigmaStarInvCoarse (openCubeSet (originCube d n))
  (coefficientCutoff nu omega ell).toFun) (nu⁻¹ • 1)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)

noncomputable section

variable {d : ℕ}

/-! ## The cutoff field is everywhere elliptic on every triadic cube -/

/-- **The cutoff field is everywhere (not merely a.e.) `(nu, Lam)`-elliptic**
on the open core of every triadic cube, for the explicit sample-dependent
`Lam := (d*d*C^2 + nu^2)/nu` of `exists_entryBound_coefficientCutoff`. This is
the everywhere form of
`SuperdiffusionCLT.Section2.Annealed.aeLocallyUniformlyEllipticField_coefficientCutoff`,
needed because the `CoarseGraining.MuAdmissibility` / `CoarseBounds.Sandwich`
machinery is stated for `IsEllipticFieldOn` (an everywhere predicate), not the
Chapter 4 restriction-carrier `AELocallyUniformlyEllipticField`. -/
theorem mixTail_isEllipticFieldOn_coefficientCutoff_cubeSet (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    ∃ Lam : ℝ,
      IsEllipticFieldOn nu Lam (cubeSet Q)
        (coefficientCutoff nu omega m).toFun := by
  classical
  obtain ⟨C, hC⟩ :=
    SuperdiffusionCLT.Section2.Annealed.exists_entryBound_coefficientCutoff
      nu omega m Q
  refine ⟨((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu, ?_, fun x hx ↦ ?_⟩
  · refine Measurable.of_eval fun i ↦ Measurable.of_eval fun j ↦ ?_
    exact (((coefficientCutoff nu omega m).entry_measurable i j).ite
      (measurableSet_cubeSet Q) measurable_const)
  · exact
      SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one
        hnu (SuperdiffusionCLT.Section2.Cutoff.symmPart_coefficientCutoff nu omega m x)
        (hC x hx)

/-- The `openCubeSet` restriction of
`mixTail_isEllipticFieldOn_coefficientCutoff_cubeSet`, needed to feed
`openCubeOriginEllipticRecoveryExistence`. -/
theorem mixTail_isEllipticFieldOn_coefficientCutoff (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d) :
    ∃ Lam : ℝ,
      IsEllipticFieldOn nu Lam (openCubeSet Q)
        (coefficientCutoff nu omega m).toFun := by
  obtain ⟨Lam, hLam⟩ := mixTail_isEllipticFieldOn_coefficientCutoff_cubeSet nu hnu omega m Q
  exact ⟨Lam, hLam.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)⟩

/-! ## The `Mu`-quadraticity bridge at general `(lam, Lam)` ellipticity -/

/-- **`Mu` is quadratic on `cubeSet (originCube d n)`** for any
`(lam, Lam)`-elliptic field on the open core, `hasQuadraticMu_cube`
(`CoarseGraining.CubeMinimizer`) generalized from `lam = 1` to a general `lam`.
The underlying origin-cube elliptic-recovery existence theorem
`openCubeOriginEllipticRecoveryExistence` is already unconditional in
`(lam, Lam)`; this module merely instantiates it there instead of at `1`. -/
theorem mixTail_hasQuadraticMu_cubeSet_originCube [NeZero d] {lam Lam : ℝ} {n : ℤ}
    {a : CoeffField d}
    (hEllO : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a) :
    HasQuadraticMu (cubeSet (originCube d n)) a := by
  obtain ⟨R, hData⟩ :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam) n a hEllO
  have hQuadO : HasQuadraticMu (openCubeSet (originCube d n)) a :=
    hasQuadraticMu_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData R hData
  exact (hasQuadraticMu_cubeSet_iff_openCubeSet_of_triadicCube (originCube d n)).2 hQuadO

/-- **The note-faithful quadratic representation of `Mu`** on
`cubeSet (originCube d n)`, at general `(lam, Lam)` ellipticity:
`Mu (cu_n; P, a) = (1/2) P . 𝐀(cu_n; a) P`. -/
theorem mixTail_mu_eq_half_coarseBlockMatrix_cubeSet_originCube [NeZero d] {lam Lam : ℝ}
    {n : ℤ} {a : CoeffField d}
    (hEllO : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a) (P : BlockVec d) :
    Mu (cubeSet (originCube d n)) P a =
      (1 / 2 : ℝ) *
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d n)) a) P) :=
  Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu
    (mixTail_hasQuadraticMu_cubeSet_originCube hEllO) P

/-! ## The pointwise lower-right block of `blockMatrixOfCoeff` for the cutoff field -/

/-- For a coefficient matrix `A` with `symmPart A = nu • 1`, the lower-right
block of `blockMatrixOfCoeff A` is the constant matrix `nu⁻¹ • 1`: this is the
pointwise (not merely coarse-grained) identity behind the sharp constant
`nu⁻¹`. -/
theorem mixTail_blockMatrixOfCoeff_lowerRight_of_symmPart_eq_smul_one {nu : ℝ} (hnu : 0 < nu)
    {A : Mat d} (hsymm : symmPart A = nu • (1 : Mat d)) :
    (blockMatrixOfCoeff A).lowerRight = nu⁻¹ • (1 : Mat d) := by
  show (symmPart A)⁻¹ = nu⁻¹ • (1 : Mat d)
  rw [hsymm, nonsing_inv_smul nu hnu.ne' (by simp)]
  simp

/-- The constant competitor `X₀ := (fun _ => 0, fun _ => y)` is `Mu`-admissible
at the test pair `(0, y)`, on `cubeSet (originCube d n)`. -/
theorem mixTail_isBlockMuAdmissible_constZeroY (n : ℤ) (y : Vec d) :
    IsBlockMuAdmissible (cubeSet (originCube d n)) (0, y)
      { potential := fun _ => (0 : Vec d), flux := fun _ => y } := by
  have hpotZero : (fun _ : Vec d => (0 : Vec d) - (0 : Vec d)) = fun _ => (0 : Vec d) := by
    funext x; abel
  have hfluxZero : (fun _ : Vec d => y - y) = fun _ : Vec d => (0 : Vec d) := by
    funext x; abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · show MemVectorL2 (cubeSet (originCube d n)) (fun _ : Vec d => (0 : Vec d) - (0 : Vec d))
    rw [hpotZero]
    exact memVectorL2_const (U := cubeSet (originCube d n)) (0 : Vec d)
  · show IsPotentialZeroTraceOn (cubeSet (originCube d n))
      (fun _ : Vec d => (0 : Vec d) - (0 : Vec d))
    rw [hpotZero]
    exact isPotentialZeroTraceOn_zero (U := cubeSet (originCube d n)) (d := d)
  · show MemVectorL2 (cubeSet (originCube d n)) (fun _ : Vec d => y - y)
    rw [hfluxZero]
    exact memVectorL2_const (U := cubeSet (originCube d n)) (0 : Vec d)
  · show IsSolenoidalZeroNormalTraceOn (cubeSet (originCube d n))
      (fun _ : Vec d => y - y)
    rw [hfluxZero]
    exact isSolenoidalZeroNormalTraceOn_zero (U := cubeSet (originCube d n)) (d := d)

/-- The energy density of the constant competitor `X₀ := (0, y)` at the cutoff
field `coefficientCutoff nu omega m`, on any point `x`: it is the *constant*
`(1/2) * nu⁻¹ * vecNormSq y`, because `symmPart (a_m(omega) x) = nu • 1`
everywhere. -/
theorem mixTail_blockEnergyDensity_constZeroY_coefficientCutoff (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (y : Vec d) (x : Vec d) :
    blockEnergyDensity (coefficientCutoff nu omega m).toFun
        { potential := fun _ => (0 : Vec d), flux := fun _ => y } x =
      (1 / 2 : ℝ) * (nu⁻¹ * vecNormSq y) := by
  show (1 / 2 : ℝ) * blockVecDot ((0 : Vec d), y)
      (blockMatVecMul (blockMatrixOfCoeff ((coefficientCutoff nu omega m).toFun x))
        ((0 : Vec d), y)) = _
  have hlr :
      (blockMatrixOfCoeff ((coefficientCutoff nu omega m).toFun x)).lowerRight =
        nu⁻¹ • (1 : Mat d) :=
    mixTail_blockMatrixOfCoeff_lowerRight_of_symmPart_eq_smul_one hnu
      (SuperdiffusionCLT.Section2.Cutoff.symmPart_coefficientCutoff nu omega m x)
  have hone : matVecMul (1 : Mat d) y = y := by
    change (1 : Mat d).mulVec y = y
    exact Matrix.one_mulVec y
  simp only [blockVecDot, blockMatVecMul_fst, blockMatVecMul_snd, matVecMul_zero,
    vecDot_zero_left, zero_add, hlr, smul_matVecMul, hone, vecDot_smul_right, vecNormSq]

/-! ## The `Mu` upper bound at `(0, y)`, and the sharp ellipticity bound -/

/-- **`Mu (cu_n; (0, y), a_m(omega)) ≤ (1/2) nu⁻¹ |y|²`.** The constant
competitor `X₀ = (0, y)` is admissible and its energy density is the constant
`(1/2) nu⁻¹ |y|²`, so it witnesses this upper bound on the infimum defining
`Mu`. -/
theorem mixTail_mu_constZeroY_coefficientCutoff_le [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (n : ℤ) (y : Vec d) :
    Mu (cubeSet (originCube d n)) (0, y) (coefficientCutoff nu omega m).toFun ≤
      (1 / 2 : ℝ) * (nu⁻¹ * vecNormSq y) := by
  obtain ⟨Lam, hEll⟩ := mixTail_isEllipticFieldOn_coefficientCutoff_cubeSet nu hnu omega m
    (originCube d n)
  set a : CoeffField d := (coefficientCutoff nu omega m).toFun with ha
  set X₀ : BlockState d := { potential := fun _ => (0 : Vec d), flux := fun _ => y } with hX₀
  have hBddBelow : BddBelow (muValueSet (cubeSet (originCube d n)) (0, y) a) := by
    refine ⟨0, ?_⟩
    rintro s ⟨Y, -, rfl⟩
    refine volumeAverage_nonneg_of_nonneg_on (measurableSet_cubeSet (originCube d n)) ?_
    intro x hx
    have hnonneg := blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (Y.eval x)
    show (0 : ℝ) ≤ (1 / 2 : ℝ) * blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (a x)) (Y.eval x))
    linarith only [hnonneg]
  have hAdm := mixTail_isBlockMuAdmissible_constZeroY n y
  have hMuLe := csInf_le hBddBelow (muValueSet_mem hAdm)
  have hconst : blockEnergyDensity a X₀ = fun _ : Vec d => (1 / 2 : ℝ) * (nu⁻¹ * vecNormSq y) := by
    funext x
    exact mixTail_blockEnergyDensity_constZeroY_coefficientCutoff nu hnu omega m y x
  rw [hconst, volumeAverage_const (volume_cubeSet_originCube_toReal_pos_recovery
    (d := d) n).ne'] at hMuLe
  exact hMuLe

/-- **The sharp deterministic ellipticity bound**:
`s_{m,*}^{-1}(cu_n) ≤ nu⁻¹ • 1`
(Loewner), since the symmetric part of `a_m(omega)` is `nu • 1`. -/
theorem mixTail_sigmaStarInvCoarse_le_inv_smul_one [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (n : ℤ) :
    MatLoewnerLE
      (sigmaStarInvCoarse (openCubeSet (originCube d n)) (coefficientCutoff nu omega m).toFun)
      (nu⁻¹ • (1 : Mat d)) := by
  have hbridge :
      (coarseBlockMatrix (cubeSet (originCube d n)) (coefficientCutoff nu omega m).toFun).lowerRight =
        sigmaStarInvCoarse (openCubeSet (originCube d n)) (coefficientCutoff nu omega m).toFun :=
    SuperdiffusionCLT.Section2.Annealed.coarseBlockMatrix_cubeSet_lowerRight_eq
      (SuperdiffusionCLT.Section2.Annealed.aeLocallyUniformlyEllipticField_coefficientCutoff
        hnu omega m) (originCube d n)
  intro y
  have hmu := mixTail_mu_constZeroY_coefficientCutoff_le nu hnu omega m n y
  rw [mixTail_mu_eq_half_coarseBlockMatrix_cubeSet_originCube
      ((mixTail_isEllipticFieldOn_coefficientCutoff nu hnu omega m
        (originCube d n)).choose_spec) (0, y)] at hmu
  have hval :
      blockVecDot ((0 : Vec d), y)
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d n))
              (coefficientCutoff nu omega m).toFun)
            ((0 : Vec d), y)) =
        vecDot y (matVecMul
          (sigmaStarInvCoarse
            (openCubeSet (originCube d n)) (coefficientCutoff nu omega m).toFun) y) := by
    simp only [blockVecDot, blockMatVecMul_fst, blockMatVecMul_snd, matVecMul_zero,
      vecDot_zero_left, zero_add, hbridge]
  rw [hval] at hmu
  have : (1 / 2 : ℝ) * vecDot y (matVecMul
      (sigmaStarInvCoarse
        (openCubeSet (originCube d n)) (coefficientCutoff nu omega m).toFun) y) ≤
      (1 / 2 : ℝ) * vecDot y (matVecMul (nu⁻¹ • (1 : Mat d)) y) := by
    have hone : matVecMul (1 : Mat d) y = y := by
      change (1 : Mat d).mulVec y = y
      exact Matrix.one_mulVec y
    have hrw : vecDot y (matVecMul (nu⁻¹ • (1 : Mat d)) y) = nu⁻¹ * vecNormSq y := by
      rw [smul_matVecMul, hone, vecDot_smul_right]
      rfl
    rw [hrw]
    linarith only [hmu]
  exact this

end

end SuperdiffusionCLT.Section4.Mixing
