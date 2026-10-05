/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsF
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2
public import SuperdiffusionCLT.Section3.Setup.CrudeBounds
public import SuperdiffusionCLT.Section2.CoarseGraining.VariationalIdentities

/-!
# The quenched energy of the glued field: `e.un.tilde.un.energy`

`RHSTerm1InputsF` reduces the first display of Step 2 of `l.RHS.term1` to
two printed lines, `hEnergy` and `hQTilde`.  This file discharges the first of
them, `e.un.tilde.un.energy`, in its printed quenched shape.

## Main results

* `responseJ_cubeMaximizer_eq_mul_volumeAverage_vecNormSq`: the **first**
  equality of `e.v.ky.energy` for the cube maximizer
  `u_{k,z}`.  The symmetric part of the cutoff coefficient is the constant
  matrix `nu Id` (`symmPart_coefficientCutoff`), so the `s`-energy identity
  `responseJ_eq_energy` reads as the exact identity
  `J(z + cu_k, 0, F; a_L) = (nu/2) ⨍_{z+cu_k} |∇u_{k,z}|²`, not merely as a
  two-sided ellipticity comparison.
* `volumeAverage_vecNormSq_cubeMaximizerGradient_le`: combining that identity
  with `Setup.two_mul_inv_mul_responseJ_le` and the quenched crude ellipticity
  bound `matLoewnerLE_sigmaStarInvCoarse_cutoffCube`, the cube-wise energy
  estimate `⨍_{z+cu_k} |∇u_{k,z}|² ≤ nu^{-2} |F|²`.
* `volumeAverage_vecNormSq_gluedGradientField_le`: the same bound for the glued
  field `∇u_k` on the centred cube `cu_r`, for every intermediate scale
  `k ≤ r ≤ m`, by the lattice partition `RHSTerm2.volumeAverage_avsum_openCubeSet`
  of `cu_r` into its scale-`k` sub-cubes.
* `energy_bridge`: **`hEnergy`, the energy hypothesis of the Step 2 `hL2` display**,
  for the cube scales `S.n ≤ r ≤ S.m`.

## The range of the cube scale

The `hEnergy` hypothesis of the Step 2 display was originally stated
for **every** `r : ℕ`.  That form is not
provable, and is not what the print asserts: below the scale `n` of the glued
family the cube `cu_r` sits strictly inside the single sub-cube
`cu_n = 0 + cu_n`, and no estimate (printed or proved) bounds the local energy of
one maximizer on a sub-cube of its own domain — the printed derivation is the
cube-wise bound of `e.v.ky.energy` **averaged over the scale-`n` sub-cubes**,
which needs `n ≤ r`.  Above `m` the glued field vanishes outside `cu_m` and the
average decays, but that range is never used.  Both consumers use `hEnergy`
only at `r = S.ell` and `r = S.m`, and `ScalesOrdering` puts both in
`[S.n, S.m]`, so the restricted form proved here is the one the proof needs;
`RHSTerm1InputsH` carries the restricted binder through.

## The translation covariance of the maximizer-gradient cube norm

The second half of the file proves the transport of the Chapter 2 response
maximizer along a translation of the domain, and with it the covariance

`‖∇u_{k,z}(omega)‖_{L̲²(z + cu_k)} = ‖∇u_{k,0}(tau_z omega)‖_{L̲²(cu_k)}`

which is the hypothesis `hcov` of `TranslatedBlocks.integral_of_translationCovariant`
and of `TranslatedBlocks.isBigO_gammaSigma_of_translationCovariant` for the
localization line of Step 1.  Every ingredient is already upstream:
`Homogenization.AHarmonicFunction.translate`,
the response-value equivariance
`Homogenization.volumeAverage_scalarResponseIntegrand_translate_forward`, the
value-set equality `Homogenization.responseJValueSet_translateSet`, and the a.e.
uniqueness `Book.Ch02.sameGradientAE_of_isResponseMaximizer`.  Only the assembly, and the
identification of the translated cutoff coefficient
(`translateCoeffField_coefficientCutoff`), are local.

## References

The paper: `e.v.ky.energy`, `e.un.tilde.un.energy`, and the proof of
`l.RHS.term1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The sub-cube family of an intermediate cube -/

/-- Descendant depth is additive: a depth-`j` descendant of a depth-`i`
descendant of `Q` is a depth-`(i + j)` descendant of `Q`.  Upstream lands only
the converse, `Homogenization.exists_descendant_ancestor_at_depth`. -/
private theorem memDescAdd {Q U : TriadicCube d} {i : ℕ}
    (hU : U ∈ descendantsAtDepth Q i) :
    ∀ (j : ℕ) {R : TriadicCube d}, R ∈ descendantsAtDepth U j →
      R ∈ descendantsAtDepth Q (i + j)
  | 0, R, hR => by
      rw [descendantsAtDepth_zero, Finset.mem_singleton] at hR
      subst hR
      simpa using hU
  | (j + 1), R, hR => by
      rw [mem_descendantsAtDepth_succ_iff] at hR
      obtain ⟨S, hS, hRS⟩ := hR
      have hSQ : S ∈ descendantsAtDepth Q (i + j) := memDescAdd hU j hS
      rw [show i + (j + 1) = (i + j) + 1 from rfl, mem_descendantsAtDepth_succ_iff]
      exact ⟨S, hSQ, hRS⟩

/-- A scale-`k` sub-cube of the intermediate centred cube `cu_r` is a scale-`k`
sub-cube of the large cube `cu_m`, so the glued field of `e.u.k.def` is the
single maximizer `∇u_{k,R}` on it. -/
theorem mem_largeCubeSubcubes_of_mem_largeCubeSubcubes_le {k r m : ℕ} (hkr : k ≤ r)
    (hrm : r ≤ m) {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d k r) :
    R ∈ largeCubeSubcubes d k m := by
  have hbase : originCube d (r : ℤ) ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - r) :=
    originCube_mem_largeCubeSubcubes hrm
  have hmem : R ∈ descendantsAtDepth (originCube d (m : ℤ)) ((m - r) + (r - k)) :=
    memDescAdd hbase (r - k) hR
  have hsum : (m - r) + (r - k) = m - k := by omega
  rwa [hsum] at hmem

/-! ## The exact energy identity of `e.v.ky.energy` -/

/-- **The first equality of `e.v.ky.energy`**, for the cube
maximizer `u_{k,z}` of `e.u.k.y.def`: the response value is exactly
`(nu/2) ⨍_{z+cu_k}|∇u_{k,z}|²`.

The `s`-energy identity `responseJ_eq_energy` reads the response value against
`symmPart(a_L)`, which for the cutoff coefficient is the **constant** matrix
`nu Id` (`symmPart_coefficientCutoff`), the shells being antisymmetric.  So no
ellipticity comparison is used and the display is an equality. -/
theorem responseJ_cubeMaximizer_eq_mul_volumeAverage_vecNormSq {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) (F : Vec d) (z : TriadicCube d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain z) (cubeCutoffCoeffOn hnu omega L z) 0 F =
      nu / 2 * volumeAverage (openCubeSet z)
        (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F z x)) := by
  have h := responseJ_eq_energy (isResponseMaximizer_setupMaximizer
    (Book.Ch02.cubeDomain z) (cubeCutoffCoeffOn hnu omega L z) F)
  rw [h]
  show (MeasureTheory.volume (openCubeSet z)).toReal⁻¹ *
      ∫ x in openCubeSet z, (1 / 2 : ℝ) *
        vecDot (cubeMaximizerGradient hnu omega L F z x)
          (matVecMul (symmPart ((coefficientCutoff nu omega L).toCoeffField x))
            (cubeMaximizerGradient hnu omega L F z x)) = _
  have hpt : ∀ x : Vec d, (1 / 2 : ℝ) *
      vecDot (cubeMaximizerGradient hnu omega L F z x)
        (matVecMul (symmPart ((coefficientCutoff nu omega L).toCoeffField x))
          (cubeMaximizerGradient hnu omega L F z x)) =
      nu / 2 * vecNormSq (cubeMaximizerGradient hnu omega L F z x) := by
    intro x
    have hsym : symmPart ((coefficientCutoff nu omega L).toCoeffField x) =
        nu • (1 : Mat d) := symmPart_coefficientCutoff nu omega L x
    rw [hsym, smul_matVecMul, vecDot_smul_right]
    have hone : matVecMul (1 : Mat d) (cubeMaximizerGradient hnu omega L F z x) =
        cubeMaximizerGradient hnu omega L F z x := by
      funext i
      simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
    rw [hone]
    show (1 / 2 : ℝ) * (nu * vecDot _ _) = _
    rw [vecNormSq]
    ring
  rw [MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet z)
    (fun x _ => hpt x), MeasureTheory.integral_const_mul]
  show _ = nu / 2 * ((MeasureTheory.volume (openCubeSet z)).toReal⁻¹ * _)
  ring

/-- **The cube-wise energy bound of `e.v.ky.energy`**:
`⨍_{z+cu_k}|∇u_{k,z}|² ≤ nu^{-2}|F|²`, the energy identity above combined with
`Setup.two_mul_inv_mul_responseJ_le` at the quenched crude ellipticity bound
`s_{L,*}^{-1}(z + cu_k) ≤ nu^{-1} Id`
(`Setup.matLoewnerLE_sigmaStarInvCoarse_cutoffCube`). -/
theorem volumeAverage_vecNormSq_cubeMaximizerGradient_le {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (F : Vec d) (z : TriadicCube d) :
    volumeAverage (openCubeSet z)
        (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F z x)) ≤
      nu⁻¹ * nu⁻¹ * vecNormSq F := by
  have hcrude : MatLoewnerLE (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain z)
      (cubeCutoffCoeffOn hnu omega L z)) (nu⁻¹ • (1 : Mat d)) :=
    matLoewnerLE_sigmaStarInvCoarse_cutoffCube hnu omega L z
  have hbound := two_mul_inv_mul_responseJ_le (Book.Ch02.cubeDomain z)
    (cubeCutoffCoeffOn hnu omega L z) F hnu hcrude
  rw [responseJ_cubeMaximizer_eq_mul_volumeAverage_vecNormSq hnu omega L F z] at hbound
  have hid : 2 * nu⁻¹ * (nu / 2 * volumeAverage (openCubeSet z)
      (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F z x))) =
      volumeAverage (openCubeSet z)
        (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F z x)) := by
    field_simp
  rwa [hid] at hbound

/-! ## The glued field on an intermediate cube -/

/-- The glued field of `e.u.k.def` is `L²` on every open cube: it is `L²` on
the whole space by `GluedField.memLp_two_gluedGradientField`. -/
theorem memVectorL2_openCubeSet_gluedGradientField {nu : ℝ} (hnu : 0 < nu)
    (L k m : ℕ) (F : Vec d) (omega : ShellSeq d) (Q : TriadicCube d) :
    MemVectorL2 (openCubeSet Q) (gluedGradientField hnu L k m F omega) :=
  (memLp_two_gluedGradientField hnu L k m F omega).restrict _

/-- `|∇u_k|²` is integrable on every open cube. -/
theorem integrableOn_vecNormSq_gluedGradientField {nu : ℝ} (hnu : 0 < nu)
    (L k m : ℕ) (F : Vec d) (omega : ShellSeq d) (Q : TriadicCube d) :
    IntegrableOn (fun x => vecNormSq (gluedGradientField hnu L k m F omega x))
      (openCubeSet Q) volume :=
  integrableOn_vecDot_of_memVectorL2
    (memVectorL2_openCubeSet_gluedGradientField hnu L k m F omega Q)
    (memVectorL2_openCubeSet_gluedGradientField hnu L k m F omega Q)

/-- **The energy of the glued field on an intermediate cube.**  For every scale
`k ≤ r ≤ m` the centred cube `cu_r` is the disjoint union of its scale-`k`
sub-cubes, on each of which `∇u_k` is a single maximizer gradient, so the
cube-wise bound of `e.v.ky.energy` averages to
`⨍_{cu_r}|∇u_k|² ≤ nu^{-2}|F|²`. -/
theorem volumeAverage_vecNormSq_gluedGradientField_le {nu : ℝ} (hnu : 0 < nu)
    {k r m : ℕ} (hkr : k ≤ r) (hrm : r ≤ m) (L : ℕ) (F : Vec d)
    (omega : ShellSeq d) :
    volumeAverage (openCubeSet (originCube d (r : ℤ)))
        (fun x => vecNormSq (gluedGradientField hnu L k m F omega x)) ≤
      nu⁻¹ * nu⁻¹ * vecNormSq F := by
  classical
  set c : ℝ := nu⁻¹ * nu⁻¹ * vecNormSq F with hc
  have hc0 : (0 : ℝ) ≤ c := by
    rw [hc]
    have := vecNormSq_nonneg F
    have hi : (0 : ℝ) ≤ nu⁻¹ := le_of_lt (inv_pos.2 hnu)
    positivity
  have hint : ∀ R ∈ largeCubeSubcubes d k r,
      IntegrableOn (fun x => vecNormSq (gluedGradientField hnu L k m F omega x))
        (openCubeSet R) volume :=
    fun R _ => integrableOn_vecNormSq_gluedGradientField hnu L k m F omega R
  rw [volumeAverage_avsum_openCubeSet hint]
  have hterm : ∀ R ∈ largeCubeSubcubes d k r,
      volumeAverage (openCubeSet R)
        (fun x => vecNormSq (gluedGradientField hnu L k m F omega x)) ≤ c := by
    intro R hR
    have hRm : R ∈ largeCubeSubcubes d k m :=
      mem_largeCubeSubcubes_of_mem_largeCubeSubcubes_le hkr hrm hR
    have heq : volumeAverage (openCubeSet R)
          (fun x => vecNormSq (gluedGradientField hnu L k m F omega x)) =
        volumeAverage (openCubeSet R)
          (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F R x)) := by
      refine congrArg
        (fun t : ℝ => (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ * t) ?_
      refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet R) ?_
      intro x hx
      show vecNormSq (gluedGradientField hnu L k m F omega x) =
        vecNormSq (cubeMaximizerGradient hnu omega L F R x)
      rw [gluedGradientField_apply_of_mem_openCubeSet hnu L k m F omega hRm hx]
    rw [heq, hc]
    exact volumeAverage_vecNormSq_cubeMaximizerGradient_le hnu omega L F R
  have hsum : ∑ R ∈ largeCubeSubcubes d k r,
      volumeAverage (openCubeSet R)
        (fun x => vecNormSq (gluedGradientField hnu L k m F omega x)) ≤
      ((largeCubeSubcubes d k r).card : ℝ) * c := by
    have h := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h
  have hcard : (0 : ℝ) < ((largeCubeSubcubes d k r).card : ℝ) := by
    rw [largeCubeSubcubes_card]
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsum
    (le_of_lt (inv_pos.2 hcard))
  refine le_trans hmul (le_of_eq ?_)
  field_simp

/-! ## The `ℝ≥0∞` reading -/

/-- The squared normalized cube norm from a real average bound. -/
theorem vecCubeLpENorm_two_sq_le_of_volumeAverage_le {Q : TriadicCube d}
    {V : Vec d → Vec d} (hV : MemVectorL2 (openCubeSet Q) V) {c : ℝ}
    (h : volumeAverage (openCubeSet Q) (fun x => vecNormSq (V x)) ≤ c) :
    vecCubeLpENorm Q 2 V ^ (2 : ℕ) ≤ ENNReal.ofReal c := by
  rw [vecCubeLpENorm_two_sq_eq_ofReal hV]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_normalizedCubeMeasure_eq]
  have hav : volumeAverage (openCubeSet Q) (fun x => vecNormSq (V x)) =
      (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, vecNormSq (V x) := by
    show (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        ∫ x in openCubeSet Q, vecNormSq (V x) = _
    rw [volume_openCubeSet_toReal]
  rw [hav] at h
  exact h

/-- **`hEnergy` in the `ℝ≥0∞` shape of the Step 2 display**, for the
glued field at every intermediate cube scale `k ≤ r ≤ m`. -/
theorem vecCubeLpENorm_two_sq_gluedGradientField_le {nu : ℝ} (hnu : 0 < nu)
    {k r m : ℕ} (hkr : k ≤ r) (hrm : r ≤ m) (L : ℕ) (F : Vec d)
    (omega : ShellSeq d) :
    vecCubeLpENorm (originCube d (r : ℤ)) 2
        (gluedGradientField hnu L k m F omega) ^ (2 : ℕ) ≤
      ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) :=
  vecCubeLpENorm_two_sq_le_of_volumeAverage_le
    (memVectorL2_openCubeSet_gluedGradientField hnu L k m F omega
      (originCube d (r : ℤ)))
    (volumeAverage_vecNormSq_gluedGradientField_le hnu hkr hrm L F omega)

/-! ## `e.un.tilde.un.energy` -/

/-- **`e.un.tilde.un.energy`**, in its printed quenched shape and in the exact
form in which the Step 2 display consumes it, for the
cube scales `S.n ≤ r ≤ S.m`:

`‖∇ũ_n‖²_{L̲²(cu_r)} ≤ 2 nu^{-2} shom_{L',*}(cu_n)`,

with the right-hand side written in the `l.RHS.term1` convention
`shom_{L',*}(cu_n) = |σ_{L'}(cu_n)|² = vecNormSq (fluxSlot nu S.LPrime P S.n e)`.
The printed constant `2` is not needed: the proof gives `nu^{-2}` outright. -/
theorem energy_bridge [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    {r : ℕ} (hnr : S.n ≤ r) (hrm : r ≤ S.m) (omega : ShellSeq d) :
    vecCubeLpENorm (originCube d (r : ℤ)) 2
        (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)
          omega) ^ (2 : ℕ) ≤
      ENNReal.ofReal (2 * nu ^ (-(2 : ℝ)) *
        vecNormSq (fluxSlot nu S.LPrime P S.n e)) := by
  refine le_trans (vecCubeLpENorm_two_sq_gluedGradientField_le hnu hnr hrm S.ell
    (fluxSlot nu S.LPrime P S.n e) omega) (ENNReal.ofReal_le_ofReal ?_)
  have hrpow : nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hnu),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast, pow_two, mul_inv]
  rw [hrpow]
  have hsig : (0 : ℝ) ≤ vecNormSq (fluxSlot nu S.LPrime P S.n e) :=
    vecNormSq_nonneg _
  have hnu2 : (0 : ℝ) ≤ nu⁻¹ * nu⁻¹ := by
    have hi : (0 : ℝ) ≤ nu⁻¹ := le_of_lt (inv_pos.2 hnu)
    positivity
  nlinarith only [hsig, hnu2]

/-! ## The transport of the Chapter 2 response maximizer along a translation -/

/-- Transport an `a`-harmonic function across an equality of coefficient fields
and an equality of domains. -/
def transportAH {a b : CoeffField d} {U V : Set (Vec d)} (ha : a = b) (hU : U = V)
    (u : AHarmonicFunction a U) : AHarmonicFunction b V := by
  subst ha; subst hU; exact u

/-- The transport of `transportAH` does not move the gradient. -/
private theorem transportAH_grad {a b : CoeffField d} {U V : Set (Vec d)} (ha : a = b)
    (hU : U = V) (u : AHarmonicFunction a U) (x : Vec d) :
    (transportAH ha hU u).toH1.grad x = u.toH1.grad x := by
  subst ha; subst hU; rfl

/-- The scalar response integrand of `e.J.def` depends on the solution only
through its gradient, and not on the domain at all. -/
private theorem scalarResponseIntegrandCongr {a b : CoeffField d} {U V : Set (Vec d)}
    (u : AHarmonicFunction a U) (v : AHarmonicFunction b V) (p q : Vec d)
    (ha : a = b) (hg : ∀ x, u.toH1.grad x = v.toH1.grad x) :
    scalarResponseIntegrand U a p q u = scalarResponseIntegrand V b p q v := by
  subst ha
  funext x
  simp only [scalarResponseIntegrand, hg x]

/-- **The cutoff coefficient is a covariant field of the shell sequence**:
translating the coefficient carrier translates every shell.  This is
`Section2.Annealed.translateReg_coefficientCutoff` read on
the raw `CoeffField` carrier of the CoarseGraining library, the one its
translation lemmas use. -/
theorem translateCoeffField_coefficientCutoff (nu : ℝ) (z : Vec d) (omega : ShellSeq d)
    (L : ℕ) :
    translateCoeffField z (coefficientCutoff nu omega L).toCoeffField =
      (coefficientCutoff nu (ShellField.translateSequence z omega) L).toCoeffField := by
  funext x
  exact congrFun (congrArg (fun A : RegCoeffField d => A.toFun)
    (translateReg_coefficientCutoff nu z omega L)) x

/-- **The transport of a cutoff-harmonic function along the cube translation.**
A solution on the centred cube `cu_{Q.scale}` for the translated shell sequence
`tau_z omega`, `z = triadicCubeShift Q`, becomes a solution on `Q` for `omega`.
It is `Homogenization.AHarmonicFunction.translate` composed with the two
identifications `translateCoeffField_coefficientCutoff` and
`openCubeSet_eq_translateSet_originCube_of_triadicCube`. -/
def translatedCubeSolution (nu : ℝ) (omega : ShellSeq d) (L : ℕ) (Q : TriadicCube d)
    (u : AHarmonicFunction ((coefficientCutoff nu
        (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField)
      (openCubeSet (originCube d Q.scale))) :
    AHarmonicFunction ((coefficientCutoff nu omega L).toCoeffField) (openCubeSet Q) :=
  transportAH rfl (openCubeSet_eq_translateSet_originCube_of_triadicCube Q).symm
    (AHarmonicFunction.translate (triadicCubeShift Q)
      (transportAH (translateCoeffField_coefficientCutoff nu (triadicCubeShift Q) omega L).symm
        rfl u))

/-- The gradient of the transported solution is the translated gradient. -/
theorem translatedCubeSolution_grad (nu : ℝ) (omega : ShellSeq d) (L : ℕ) (Q : TriadicCube d)
    (u : AHarmonicFunction ((coefficientCutoff nu
        (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField)
      (openCubeSet (originCube d Q.scale))) (x : Vec d) :
    (translatedCubeSolution nu omega L Q u).toH1.grad x =
      u.toH1.grad (x - triadicCubeShift Q) := by
  rw [translatedCubeSolution, transportAH_grad, AHarmonicFunction.grad_translate,
    transportAH_grad]

/-- **The response value is unchanged by the transport**, the equivariance of
`e.J.def` under a translation of the domain. -/
theorem volumeAverage_scalarResponseIntegrand_translatedCubeSolution (nu : ℝ)
    (omega : ShellSeq d) (L : ℕ) (Q : TriadicCube d) (p q : Vec d)
    (u : AHarmonicFunction ((coefficientCutoff nu
        (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField)
      (openCubeSet (originCube d Q.scale))) :
    volumeAverage (openCubeSet Q)
        (scalarResponseIntegrand (openCubeSet Q)
          ((coefficientCutoff nu omega L).toCoeffField) p q
          (translatedCubeSolution nu omega L Q u)) =
      volumeAverage (openCubeSet (originCube d Q.scale))
        (scalarResponseIntegrand (openCubeSet (originCube d Q.scale))
          ((coefficientCutoff nu
            (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField) p q u) := by
  have hcoef := translateCoeffField_coefficientCutoff nu (triadicCubeShift Q) omega L
  have hset := openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  have key := volumeAverage_scalarResponseIntegrand_translate_forward (triadicCubeShift Q)
    (openCubeSet (originCube d Q.scale)) ((coefficientCutoff nu omega L).toCoeffField) p q
    (transportAH hcoef.symm rfl u)
  have h1 : scalarResponseIntegrand (openCubeSet Q)
        ((coefficientCutoff nu omega L).toCoeffField) p q
        (translatedCubeSolution nu omega L Q u) =
      scalarResponseIntegrand
        (translateSet (triadicCubeShift Q) (openCubeSet (originCube d Q.scale)))
        ((coefficientCutoff nu omega L).toCoeffField) p q
        (AHarmonicFunction.translate (triadicCubeShift Q) (transportAH hcoef.symm rfl u)) :=
    scalarResponseIntegrandCongr _ _ p q rfl
      (fun x => by rw [translatedCubeSolution, transportAH_grad])
  have h2 : scalarResponseIntegrand (openCubeSet (originCube d Q.scale))
        (translateCoeffField (triadicCubeShift Q)
          ((coefficientCutoff nu omega L).toCoeffField)) p q (transportAH hcoef.symm rfl u) =
      scalarResponseIntegrand (openCubeSet (originCube d Q.scale))
        ((coefficientCutoff nu
          (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField) p q u :=
    scalarResponseIntegrandCongr _ _ p q hcoef (fun x => transportAH_grad _ _ _ x)
  rw [h1, hset, key, h2]

/-- **The set of admissible response values is unchanged by the transport.** -/
theorem responseJValueSet_openCubeSet_coefficientCutoff (nu : ℝ) (omega : ShellSeq d) (L : ℕ)
    (Q : TriadicCube d) (p q : Vec d) :
    responseJValueSet (openCubeSet Q) p q ((coefficientCutoff nu omega L).toCoeffField) =
      responseJValueSet (openCubeSet (originCube d Q.scale)) p q
        ((coefficientCutoff nu
          (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField) := by
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q, responseJValueSet_translateSet,
    translateCoeffField_coefficientCutoff]

/-- **The maximizing property is equivariant.**  This is the transport of
`Book.Ch02.IsResponseMaximizer` along a translation of the domain that the
covariance of the localization line needs. -/
theorem isResponseMaximizer_translatedCubeSolution {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (Q : TriadicCube d) (p q : Vec d)
    (u : Book.Ch02.Solution (Book.Ch02.cubeDomain (originCube d Q.scale))
      (cubeCutoffCoeffOn hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L
        (originCube d Q.scale)))
    (hu : Book.Ch02.IsResponseMaximizer (Book.Ch02.cubeDomain (originCube d Q.scale))
      (cubeCutoffCoeffOn hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L
        (originCube d Q.scale)) p q u) :
    Book.Ch02.IsResponseMaximizer (Book.Ch02.cubeDomain Q) (cubeCutoffCoeffOn hnu omega L Q) p q
      (translatedCubeSolution nu omega L Q u) := by
  intro w
  have hgreat := Book.Ch02.responseValueSet_isGreatest_of_isResponseMaximizer hu
  have hset : Book.Ch02.responseValueSet (Book.Ch02.cubeDomain Q)
        (cubeCutoffCoeffOn hnu omega L Q) p q =
      Book.Ch02.responseValueSet (Book.Ch02.cubeDomain (originCube d Q.scale))
        (cubeCutoffCoeffOn hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L
          (originCube d Q.scale)) p q :=
    responseJValueSet_openCubeSet_coefficientCutoff nu omega L Q p q
  have hmem : Book.Ch02.responseValue (Book.Ch02.cubeDomain Q)
      (cubeCutoffCoeffOn hnu omega L Q) p q w ∈
      Book.Ch02.responseValueSet (Book.Ch02.cubeDomain (originCube d Q.scale))
        (cubeCutoffCoeffOn hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L
          (originCube d Q.scale)) p q := by
    rw [← hset]
    exact ⟨w, rfl⟩
  have hle := hgreat.2 hmem
  have hval : Book.Ch02.responseValue (Book.Ch02.cubeDomain Q)
        (cubeCutoffCoeffOn hnu omega L Q) p q (translatedCubeSolution nu omega L Q u) =
      Book.Ch02.responseValue (Book.Ch02.cubeDomain (originCube d Q.scale))
        (cubeCutoffCoeffOn hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L
          (originCube d Q.scale)) p q u :=
    volumeAverage_scalarResponseIntegrand_translatedCubeSolution nu omega L Q p q u
  rw [hval]
  exact hle

/-! ## The covariance of the maximizer-gradient cube norm -/

/-- The normalized cube norm is translation invariant: reading a field on `Q`
after the shift `x ↦ x - triadicCubeShift Q` is reading it on the centred cube
of the same scale. -/
theorem vecCubeLpENorm_comp_sub_shift {Q : TriadicCube d} {V : Vec d → Vec d}
    (hV : MemVectorL2 (openCubeSet Q) (fun x => V (x - triadicCubeShift Q))) :
    vecCubeLpENorm Q 2 (fun x => V (x - triadicCubeShift Q)) =
      vecCubeLpENorm (originCube d Q.scale) 2 V := by
  have hmp := measurePreserving_addRight_normalizedCubeMeasure_originCube Q
  have hmeas := aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 hV
  have hcomp := MeasureTheory.eLpNorm_comp_measurePreserving (p := 2)
    (g := hilbertifyVecField (fun x => V (x - triadicCubeShift Q))) hmeas hmp
  have hfun : (hilbertifyVecField (fun x => V (x - triadicCubeShift Q)) ∘
      fun x : Vec d => x + triadicCubeShift Q) = hilbertifyVecField V := by
    funext y
    show hilbertifyVecField (fun x => V (x - triadicCubeShift Q))
      (y + triadicCubeShift Q) = _
    simp only [hilbertifyVecField, add_sub_cancel_right]
  rw [hfun] at hcomp
  exact hcomp.symm

/-- **The translation covariance of the maximizer-gradient cube norm.**  The
cube maximizer of `e.u.k.y.def` is produced by a choice, so the transported
maximizer and the maximizer of the translated cube are two different objects;
they are both response maximizers for the same data, and the upstream a.e.
uniqueness `Book.Ch02.sameGradientAE_of_isResponseMaximizer` makes their
gradients agree almost everywhere, hence their cube norms equal.

This is the pointwise covariance `F omega Q = F (tau_{z} omega) (cu_{Q.scale})`
required by `TranslatedBlocks.isBigO_gammaSigma_of_translationCovariant` and
`TranslatedBlocks.integral_of_translationCovariant` for the localization line of
Step 1 of `l.RHS.term1`. -/
theorem vecCubeLpENorm_cubeMaximizerGradient_translate {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (F : Vec d) (Q : TriadicCube d) :
    vecCubeLpENorm Q 2 (cubeMaximizerGradient hnu omega L F Q) =
      vecCubeLpENorm (originCube d Q.scale) 2
        (cubeMaximizerGradient hnu
          (ShellField.translateSequence (triadicCubeShift Q) omega) L F
          (originCube d Q.scale)) := by
  have hmaxT := isResponseMaximizer_translatedCubeSolution hnu omega L Q 0 F
    (cubeMaximizer hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L F
      (originCube d Q.scale)).toSolution
    (cubeMaximizer hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L F
      (originCube d Q.scale)).isMaximizer
  have hsame := Book.Ch02.sameGradientAE_of_isResponseMaximizer
    (cubeMaximizer hnu omega L F Q).isMaximizer hmaxT
  have hgradT : ∀ x : Vec d,
      (translatedCubeSolution nu omega L Q
          (cubeMaximizer hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L F
            (originCube d Q.scale)).toSolution).toH1.grad x =
        cubeMaximizerGradient hnu
          (ShellField.translateSequence (triadicCubeShift Q) omega) L F
          (originCube d Q.scale) (x - triadicCubeShift Q) :=
    fun x => translatedCubeSolution_grad nu omega L Q _ x
  have hae : hilbertifyVecField (cubeMaximizerGradient hnu omega L F Q)
      =ᵐ[normalizedCubeMeasure Q]
      hilbertifyVecField (fun x => cubeMaximizerGradient hnu
        (ShellField.translateSequence (triadicCubeShift Q) omega) L F
        (originCube d Q.scale) (x - triadicCubeShift Q)) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    refine MeasureTheory.Measure.ae_smul_measure ?_ _
    filter_upwards [hsame] with x hx
    show HilbertVec.ofVec _ = HilbertVec.ofVec _
    rw [show cubeMaximizerGradient hnu omega L F Q x =
      (cubeMaximizer hnu omega L F Q).toSolution.toH1.grad x from rfl, hx, hgradT x]
  have h1 : vecCubeLpENorm Q 2 (cubeMaximizerGradient hnu omega L F Q) =
      vecCubeLpENorm Q 2 (fun x => cubeMaximizerGradient hnu
        (ShellField.translateSequence (triadicCubeShift Q) omega) L F
        (originCube d Q.scale) (x - triadicCubeShift Q)) :=
    MeasureTheory.eLpNorm_congr_ae hae
  have hV : MemVectorL2 (openCubeSet Q) (fun x => cubeMaximizerGradient hnu
      (ShellField.translateSequence (triadicCubeShift Q) omega) L F
      (originCube d Q.scale) (x - triadicCubeShift Q)) := by
    have hmem := (translatedCubeSolution nu omega L Q
      (cubeMaximizer hnu (ShellField.translateSequence (triadicCubeShift Q) omega) L F
        (originCube d Q.scale)).toSolution).toH1.grad_memVectorL2
    rwa [funext hgradT] at hmem
  rw [h1]
  exact vecCubeLpENorm_comp_sub_shift hV

/-- On a sub-cube of the family, the glued field of `e.u.k.def` and the single
cube maximizer have the same normalized cube norm: they agree on the half-open
realization, which carries the normalized cube measure. -/
theorem vecCubeLpENorm_gluedGradientField_eq_cubeMaximizer {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L k m : ℕ) (F : Vec d) {Q : TriadicCube d}
    (hQ : Q ∈ largeCubeSubcubes d k m) :
    vecCubeLpENorm Q 2 (gluedGradientField hnu L k m F omega) =
      vecCubeLpENorm Q 2 (cubeMaximizerGradient hnu omega L F Q) := by
  refine MeasureTheory.eLpNorm_congr_ae ?_
  rw [normalizedCubeMeasure, cubeMeasure]
  refine MeasureTheory.Measure.ae_smul_measure ?_ _
  refine MeasureTheory.ae_restrict_of_forall_mem (measurableSet_cubeSet Q) ?_
  intro x hx
  show HilbertVec.ofVec _ = HilbertVec.ofVec _
  rw [gluedGradientField_apply_of_mem_cubeSet hnu L k m F omega hQ hx]

/-- **The covariance of the glued field on a sub-cube of the family.**  This is
the form in which the `avsum` step of the localization line reads it: the cube
norm of `∇u_k` on the sub-cube `z + cu_k` is the cube norm of the centred cube
maximizer of the translated shell sequence. -/
theorem vecCubeLpENorm_gluedGradientField_translate {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) {k m : ℕ} (hkm : k ≤ m) (F : Vec d) {Q : TriadicCube d}
    (hQ : Q ∈ largeCubeSubcubes d k m) :
    vecCubeLpENorm Q 2 (gluedGradientField hnu L k m F omega) =
      vecCubeLpENorm (originCube d (k : ℤ)) 2
        (cubeMaximizerGradient hnu
          (ShellField.translateSequence (triadicCubeShift Q) omega) L F
          (originCube d (k : ℤ))) := by
  have hscale : Q.scale = (k : ℤ) := scale_of_mem_largeCubeSubcubes hkm hQ
  rw [vecCubeLpENorm_gluedGradientField_eq_cubeMaximizer hnu omega L k m F hQ,
    vecCubeLpENorm_cubeMaximizerGradient_translate hnu omega L F Q, hscale]

end

end SuperdiffusionCLT.Section3.Terms
