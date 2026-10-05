/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality

/-!
# The inputs of `l.RHS.term3#block-concentration`

Step 3 of the proof of `l.RHS.term3` decomposes `|b_ℓ(z + cu_n)|` as

`|b_ℓ(z+cu_n)| ≤ d shom_ℓ(cu_n) + ∑_i |e_i·(b_ℓ(z+cu_n) − shom_ℓ(cu_n))e_i|`,

and applies the concentration step `l.RHS.term3#block-concentration` to the
centred coarse blocks

`Y_z^{(i)} = e_i·(b_ℓ(z+cu_n) − shom_ℓ(cu_n))e_i`,  `z ∈ 3^nℤ^d ∩ cu_k`.

`block_concentration` (in `RHSTerm3StepsD.lean`) takes `Y` as a free
binder together with four properties of it — measurability, the centring
`E[Y_z] = 0`, the `Γ₁` envelope `Y_z = O_{Γ₁}(K)`, and the mutual independence
inside each sublattice.  This module supplies all four for the carrier
`blockDeviation`, which *is* the printed `Y_z^{(i)}`.

* `integral_blockDeviation_eq_zero` is the centring.  It requires
  `E[b_ℓ(z+cu_n)] = shom_ℓ(cu_n)Id` on translated cubes (stationarity plus the
  scalar reduction of the paper's Section 3); it is **proved** here, with no
  hypothesis beyond the standing shell laws: stationarity is the translated-cube
  expectation identity of `TranslatedBlocks.lean`, `E[b_ℓ(cu_n)]` is the
  upper-left block of `bfAhom_ℓ(cu_n)`, `khom_ℓ(cu_n) = 0` identifies it with
  `shom_ℓ(cu_n)`, and the dihedral symmetry makes that block scalar.
* `isBigO_gammaSigma_blockDeviation` is the `Γ₁` envelope, obtained from the
  conclusion of `l.bfAm.ellip` on the *centred* cube — an explicit hypothesis
  in that anchor's shape — by the translated-localization bridge.  Its
  corollary `isBigO_gammaSigma_blockDeviation_of_shellLaws` discharges that
  hypothesis outright: the first assertion of `l.bfAm.ellip` is proved on
  every bounded domain in `EnvelopeEllipticity.lean`, and
  `translatedBlockNorm_le_envelope` undoes the `bfE_L` normalization.
* `iIndepFun_blockDeviation_of_local` is the independence inside one sublattice,
  in the exact shape `block_concentration` takes.  It reduces the printed
  sentence *"each `Y_z` is a function only of the cutoff-`ℓ` environment in a
  `C3^ℓ` neighbourhood of `z+cu_n`; this follows from the definition of the
  localized coarse-grained matrix and `a.j.frd`.  Hence the family has range of
  dependence `C3^ℓ`"* to its two halves: the locality of the
  observable, which is a hypothesis because the coarse block is produced by a
  variational problem and has no restriction-lane measurability, and the
  geometric separation of the observation regions, which is proved here from
  the colouring of `SpatialAverageColoring.lean`.

## Main definitions

* `blockDeviation`: the centred coarse block `Y_z^{(i)}`.

## Main results

* `measurable_blockDeviation`.
* `integral_blockDeviation_eq_zero`: `hYmean`.
* `isBigO_gammaSigma_blockDeviation`,
  `isBigO_gammaSigma_blockDeviation_of_shellLaws`: `hYtail`.
* `iIndepFun_blockDeviation_of_local`, `iIndepFun_of_shellRestrictionLocal`:
  `hIndep`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.HighContrast
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The centred coarse block `Y_z^{(i)}` -/

/-- **`Y_z^{(i)} = e·(b_L(z + cu_n) − shom_L(cu_n))e`**,
as in Step 3 of the proof of `l.RHS.term3`: the coarse block on the
translated cube `z`, tested against the fixed unit vector `e` and centred by the
annealed scalar `shom_L(cu_n)`. -/
def blockDeviation [NeZero d] (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (nn : ℕ) (e : Vec d) (omega : ShellSeq d) (z : TriadicCube d) : ℝ :=
  vecDot e (matVecMul (translatedCoarseBlock nu L omega z) e) - sigmaBarSeq nu L P nn

/-! ## Elementary matrix algebra -/

private theorem vecDot_matVecMul_eq_sum (e : Vec d) (M : Mat d) :
    vecDot e (matVecMul M e) = ∑ i, ∑ j, e i * (M i j * e j) := by
  rw [vecDot]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [matVecMul, Finset.mul_sum]

private theorem vecDot_matVecMul_smul_one (c : ℝ) (x : Vec d) :
    vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
  have hrow : ∀ i, matVecMul (c • (1 : Mat d)) x i = c * x i := by
    intro i
    rw [matVecMul]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    · intro j _ hji
      rw [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hji), smul_eq_mul, mul_zero, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [vecDot, vecNormSq, vecDot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrow i]
  ring

section Quadratic

variable {P : ProbabilityMeasure (ShellSeq d)}

private theorem measurable_vecDot_matVecMul (e : Vec d) {M : ShellSeq d → Mat d}
    (hM : ∀ i j, Measurable fun omega : ShellSeq d => M omega i j) :
    Measurable fun omega : ShellSeq d => vecDot e (matVecMul (M omega) e) := by
  have heq : (fun omega : ShellSeq d => vecDot e (matVecMul (M omega) e)) =
      fun omega : ShellSeq d => ∑ i, ∑ j, e i * (M omega i j * e j) :=
    funext fun omega => vecDot_matVecMul_eq_sum e (M omega)
  rw [heq]
  exact Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => ((hM i j).mul_const (e j)).const_mul (e i)

private theorem integrable_vecDot_matVecMul (e : Vec d) {M : ShellSeq d → Mat d}
    (hM : ∀ i j, Integrable (fun omega : ShellSeq d => M omega i j) P.toMeasure) :
    Integrable (fun omega : ShellSeq d => vecDot e (matVecMul (M omega) e)) P.toMeasure := by
  have heq : (fun omega : ShellSeq d => vecDot e (matVecMul (M omega) e)) =
      fun omega : ShellSeq d => ∑ i, ∑ j, e i * (M omega i j * e j) :=
    funext fun omega => vecDot_matVecMul_eq_sum e (M omega)
  rw [heq]
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => ((hM i j).mul_const (e j)).const_mul (e i)

private theorem integral_vecDot_matVecMul (e : Vec d) {M : ShellSeq d → Mat d}
    (hM : ∀ i j, Integrable (fun omega : ShellSeq d => M omega i j) P.toMeasure) :
    ∫ omega : ShellSeq d, vecDot e (matVecMul (M omega) e) ∂P.toMeasure =
      vecDot e (matVecMul
        (fun i j => ∫ omega : ShellSeq d, M omega i j ∂P.toMeasure) e) := by
  have heq : (fun omega : ShellSeq d => vecDot e (matVecMul (M omega) e)) =
      fun omega : ShellSeq d => ∑ i, ∑ j, e i * (M omega i j * e j) :=
    funext fun omega => vecDot_matVecMul_eq_sum e (M omega)
  rw [heq,
    vecDot_matVecMul_eq_sum e (fun i j => ∫ omega : ShellSeq d, M omega i j ∂P.toMeasure),
    integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => ((hM i j).mul_const (e j)).const_mul (e i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((hM i j).mul_const (e j)).const_mul (e i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]

end Quadratic

/-! ## Measurability and integrability of the centred block -/

section Regularity

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)}

/-- Each entry of `b_L(z + cu_n)` is a measurable observable of the shell
sequence. -/
theorem measurable_translatedCoarseBlock_apply (hnu : 0 < nu) (L : ℕ)
    (z : TriadicCube d) (i j : Fin d) :
    Measurable fun omega : ShellSeq d => translatedCoarseBlock nu L omega z i j := by
  have h := SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_upperLeft_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega L)
    (measurable_coefficientCutoff nu L)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) z i j
  simp only [translatedCoarseBlock_apply]
  exact h

/-- Each entry of `b_L(z + cu_n)` is integrable: this is the
integrability of the entries of `bfA_L(cu_Q)`. -/
theorem integrable_translatedCoarseBlock_apply (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L : ℕ) (z : TriadicCube d) (i j : Fin d) :
    Integrable (fun omega : ShellSeq d => translatedCoarseBlock nu L omega z i j)
      P.toMeasure :=
  (integrable_coarseBlockMatrix_upperLeft_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j).congr
    (Filter.Eventually.of_forall fun omega =>
      (translatedCoarseBlock_apply nu L omega z i j).symm)

/-- **`Y_z^{(i)}` is measurable**, the hypothesis `hYmeas` of
`block_concentration`. -/
theorem measurable_blockDeviation (hnu : 0 < nu) (L nn : ℕ) (e : Vec d)
    (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d => blockDeviation nu L P nn e omega z :=
  (measurable_vecDot_matVecMul e
    (fun i j => measurable_translatedCoarseBlock_apply hnu L z i j)).sub measurable_const

end Regularity

/-! ## `hYmean`: the centring `E[Y_z] = 0`

The centring is proved here in
three steps, none of which needs a hypothesis beyond the standing shell laws:
stationarity moves the expectation of `b_L(z + cu_n)` to `E[b_L(cu_n)]`, which is
the upper-left block of `bfAhom_L(cu_n)`; `khom_L(cu_n) = 0`
identifies that block with `shom_L(cu_n)`; and the dihedral symmetry makes
`shom_L(cu_n)` a scalar matrix, whose scalar is by definition
`sigmaBarSeq`. -/

section Mean

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)}

/-- **`E[b_L(z + cu_n)] = shom_L(cu_n) Id` for every translate `z` of scale `n`.**
-/
theorem integral_translatedCoarseBlock_apply (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ4 : ShellLawJ4 d P) (L nn : ℕ) {z : TriadicCube d} (hz : z.scale = (nn : ℤ))
    (i j : Fin d) :
    ∫ omega : ShellSeq d, translatedCoarseBlock nu L omega z i j ∂P.toMeasure =
      (sigmaBarSeq nu L P nn • (1 : Mat d)) i j := by
  have hcov : ∀ omega : ShellSeq d,
      translatedCoarseBlock nu L omega z i j =
        translatedCoarseBlock nu L
          (ShellField.translateSequence (triadicCubeShift z) omega)
          (originCube d z.scale) i j := fun omega =>
    congrFun (congrFun (translatedCoarseBlock_eq_originCube nu L omega z) i) j
  have hstat := integral_of_translationCovariant (P := P) hPrefix hJ2
    (F := fun omega Q => translatedCoarseBlock nu L omega Q i j) hcov
    (measurable_translatedCoarseBlock_apply hnu L (originCube d z.scale) i j).aestronglyMeasurable
  rw [hstat, hz]
  have hbBar : ∫ omega : ShellSeq d,
      translatedCoarseBlock nu L omega (originCube d (nn : ℤ)) i j ∂P.toMeasure =
      bBar nu L P (cubeSet (originCube d (nn : ℤ))) i j := by
    rw [bBar_apply]
    exact integral_congr_ae (Filter.Eventually.of_forall fun omega =>
      translatedCoarseBlock_apply nu L omega (originCube d (nn : ℤ)) i j)
  have hUL : bBar nu L P (cubeSet (originCube d (nn : ℤ))) =
      sigmaBar nu L P (cubeSet (originCube d (nn : ℤ))) :=
    annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu L hJ4 (nn : ℤ)
  rw [hbBar, hUL, sigmaBar_originCube_eq_smul_one hnu L hJ4 (nn : ℤ)]
  rfl

/-- **`hYmean` of `block_concentration`**: the centred coarse block has zero
mean on every translate of scale `n`. -/
theorem integral_blockDeviation_eq_zero (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L nn : ℕ) {e : Vec d} (he : vecNormSq e = 1)
    {z : TriadicCube d} (hz : z.scale = (nn : ℤ)) :
    ∫ omega : ShellSeq d, blockDeviation nu L P nn e omega z ∂P.toMeasure = 0 := by
  have hInt : ∀ i j, Integrable
      (fun omega : ShellSeq d => translatedCoarseBlock nu L omega z i j) P.toMeasure :=
    fun i j => integrable_translatedCoarseBlock_apply hnu hPrefix hJ2 hJ3 hJ4 L z i j
  have hN : (fun i j => ∫ omega : ShellSeq d,
      translatedCoarseBlock nu L omega z i j ∂P.toMeasure) =
      sigmaBarSeq nu L P nn • (1 : Mat d) := by
    funext i j
    exact integral_translatedCoarseBlock_apply hnu hPrefix hJ2 hJ4 L nn hz i j
  have hval : ∫ omega : ShellSeq d,
      vecDot e (matVecMul (translatedCoarseBlock nu L omega z) e) ∂P.toMeasure =
      sigmaBarSeq nu L P nn := by
    rw [integral_vecDot_matVecMul e hInt, hN, vecDot_matVecMul_smul_one, he, mul_one]
  have hfint := integrable_vecDot_matVecMul (P := P) e hInt
  rw [show (fun omega : ShellSeq d => blockDeviation nu L P nn e omega z) =
      fun omega : ShellSeq d =>
        vecDot e (matVecMul (translatedCoarseBlock nu L omega z) e) -
          sigmaBarSeq nu L P nn from rfl,
    integral_sub hfint (integrable_const _), hval, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul, sub_self]

end Mean

/-! ## `hYtail`: the `Γ₁` envelope of the centred block

`l.bfAm.ellip` (in the form `envelopeRescale_ellipticity`) together with
`e.Enaught.mixing` gives `|b_ℓ(cu_n)| = O_{Γ₁}(Cℓν⁻¹)` on the *centred* cube.
The envelope on the translate is the same by the translated-localization bridge
of `TranslatedBlocks.lean`, and the centring costs the additive
constant `shom_ℓ(cu_n)`, which the printed amplitude `Cℓν⁻¹` absorbs
(`IsBigO.mono_scale`). -/

section Tail

/-- Subtracting a bounded quantity from a variable with a `Γ_σ` envelope
enlarges the amplitude by that bound. -/
private theorem isBigO_gammaSigma_of_abs_le_add_const {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    {X Y : Omega → ℝ} {A c sigma : ℝ} (hc : 0 ≤ c)
    (hle : ∀ omega, |Y omega| ≤ |X omega| + c)
    (hX : IsBigO mu (gammaSigma sigma) X A) :
    IsBigO mu (gammaSigma sigma) Y (A + c) := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  refine (measureReal_mono ?_).trans ((isBigO_gammaSigma_iff.1 hX) ht)
  intro omega homega
  have hY : (A + c) * t < |Y omega| := homega
  have hct : c ≤ c * t := le_mul_of_one_le_right hc ht
  have hle' := hle omega
  show A * t < |X omega|
  have hexp : (A + c) * t = A * t + c * t := by ring
  linarith only [hY, hct, hle', hexp]

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)}

/-- `|b_L(z + cu_n)|` is a measurable observable. -/
theorem measurable_translatedBlockNorm (hnu : 0 < nu) (L : ℕ) (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d => translatedBlockNorm nu L omega z := by
  have hmat : Measurable fun omega : ShellSeq d => translatedCoarseBlock nu L omega z :=
    Measurable.of_eval fun i => Measurable.of_eval fun j =>
      measurable_translatedCoarseBlock_apply hnu L z i j
  exact ShellField.continuous_matrixOperatorNorm.measurable.comp hmat

/-- The centred block is dominated by the operator norm of the block plus the
annealed scalar: this is the elementary half of the decomposition of Step 3. -/
theorem abs_blockDeviation_le (hnu : 0 < nu) (L nn : ℕ) {e : Vec d}
    (he : vecNormSq e = 1) (hsb : 0 ≤ sigmaBarSeq nu L P nn) (omega : ShellSeq d)
    (z : TriadicCube d) :
    |blockDeviation nu L P nn e omega z| ≤
      |translatedBlockNorm nu L omega z| + sigmaBarSeq nu L P nn := by
  have hpsd := posSemidef_translatedCoarseBlock hnu L omega z
  have hdef : translatedBlockNorm nu L omega z =
    Book.Ch02.matrixOperatorNorm (translatedCoarseBlock nu L omega z) := rfl
  have hupper := Book.Ch02.vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef
    hpsd e
  rw [he, mul_one, ← hdef] at hupper
  have hlower : 0 ≤ vecDot e (matVecMul (translatedCoarseBlock nu L omega z) e) := by
    simpa only [Homogenization.vecDot, Homogenization.matVecMul, dotProduct,
      Matrix.mulVec, star_trivial] using hpsd.dotProduct_mulVec_nonneg e
  have hnorm : 0 ≤ translatedBlockNorm nu L omega z := by
    rw [hdef]; exact Book.Ch02.matrixOperatorNorm_nonneg _
  rw [abs_of_nonneg hnorm, abs_le]
  refine ⟨?_, ?_⟩
  · show -(translatedBlockNorm nu L omega z + sigmaBarSeq nu L P nn) ≤
      vecDot e (matVecMul (translatedCoarseBlock nu L omega z) e) - sigmaBarSeq nu L P nn
    linarith only [hlower, hnorm]
  · show vecDot e (matVecMul (translatedCoarseBlock nu L omega z) e) -
      sigmaBarSeq nu L P nn ≤ translatedBlockNorm nu L omega z + sigmaBarSeq nu L P nn
    linarith only [hupper, hsb]

/-- **`hYtail` of `block_concentration`.**  `hbig` is the conclusion of
`l.bfAm.ellip` in the form the step consumes it, `|b_L(cu_n)| = O_{Γ₁}(K)` on the
centred cube; the conclusion is the same envelope for the centred block on every
translate of scale `n`, with the additive centring constant. -/
theorem isBigO_gammaSigma_blockDeviation (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L nn : ℕ) {e : Vec d} (he : vecNormSq e = 1) {K : ℝ}
    (hbig : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => translatedBlockNorm nu L omega (originCube d (nn : ℤ))) K)
    {z : TriadicCube d} (hz : z.scale = (nn : ℤ)) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => blockDeviation nu L P nn e omega z)
      (K + sigmaBarSeq nu L P nn) := by
  have hmeas : Measurable fun omega : ShellSeq d =>
      translatedBlockNorm nu L omega (originCube d z.scale) := by
    rw [hz]
    exact measurable_translatedBlockNorm hnu L (originCube d (nn : ℤ))
  have hbig' : IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => translatedBlockNorm nu L omega (originCube d z.scale)) K := by
    rw [hz]; exact hbig
  have htrans := isBigO_gammaSigma_translatedBlockNorm hPrefix hJ2 nu L (Q := z) hmeas hbig'
  exact isBigO_gammaSigma_of_abs_le_add_const
    (sigmaBarSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 nn).le
    (fun omega => abs_blockDeviation_le hnu L nn he
      (sigmaBarSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 nn).le omega z) htrans

/-- **`hYtail` with the envelope discharged.**  The first assertion of
`l.bfAm.ellip` is proved on every bounded domain, so the `Γ₁`
envelope of the centred coarse block needs no anchor at all; its amplitude is
the printed `bfE_L`-scalar `nu + 2C nu⁻¹(1 ∨ L)` plus the centring constant. -/
theorem isBigO_gammaSigma_blockDeviation_of_shellLaws (hnu : 0 < nu)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (L nn : ℕ) {e : Vec d} (he : vecNormSq e = 1)
    {z : TriadicCube d} (hz : z.scale = (nn : ℤ)) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => blockDeviation nu L P nn e omega z)
      (envelopeUpperScalar d nu L + sigmaBarSeq nu L P nn) :=
  isBigO_gammaSigma_blockDeviation hnu hPrefix hJ2 hJ3 hJ4 L nn he
    (isBigO_gammaSigma_translatedBlockNorm_envelope hnu hPrefix hJ2 hJ3 hJ4 L
      (originCube d (nn : ℤ))) hz

end Tail

/-! ## `hIndep`: independence inside one sublattice

The paper states: *"each `Y_z` is a function only of the cutoff-`ℓ` environment
in a `C3^ℓ` neighborhood of `z+cu_n`; this follows from the definition of the
localized coarse-grained matrix and `a.j.frd`.  Hence the family has range of
dependence `C3^ℓ`."*  The two halves are separated here.

* The **locality** half is the hypothesis `hYlocal`: `Y_z` is an observable of
  the join of the shell lanes `0, …, ℓ` restricted to the observation region
  `nbhd z`.  It is a hypothesis and not a theorem because the coarse-grained
  matrix on a cube is produced by a variational problem over an `H¹` space, for
  which no restriction-lane measurability is available; the same statement for
  the sub-cube moments of the stream increment is
  `measurable_blockCubeLane_finiteShellIncrementCubePthMoment`, obtained there
  through Riemann sums.
* The **range-of-dependence** half is `hsep`, the geometric separation of the
  observation regions inside one sublattice, and it is discharged by
  `areShellSeparated_of_subset_cubeSet` from the colouring of
  `SpatialAverageColoring.lean`.

Given the two, the shell law `ShellLawJ1Restriction` (`a.j.frd`) and `ShellLawJ2` give the
mutual independence, in the exact shape `block_concentration` takes. -/

section Independence

/-- Separation is inherited by subsets of the two observation regions. -/
theorem areShellSeparated_of_subset {ell : ℕ} {U V U' V' : Set (Vec d)}
    (hUV : ShellField.AreShellSeparated ell U V) (hU : U' ⊆ U) (hV : V' ⊆ V) :
    ShellField.AreShellSeparated ell U' V' :=
  fun _ _ hx hy => hUV (hU hx) (hV hy)

/-- Separation at a range is separation at every smaller range. -/
theorem areShellSeparated_mono_scale {ell kk : ℕ} (hk : ell ≤ kk) {U V : Set (Vec d)}
    (hUV : ShellField.AreShellSeparated kk U V) :
    ShellField.AreShellSeparated ell U V := by
  intro x y hx hy
  have hpow : (3 : ℝ) ^ ell ≤ (3 : ℝ) ^ kk :=
    pow_le_pow_right₀ (by norm_num) hk
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  exact le_trans (mul_le_mul_of_nonneg_right hpow hsqrt) (hUV hx hy)

/-- **The geometric half of the range of dependence.**  Two observation regions
enclosed in distinct triadic cubes of one scale `kk ≥ ell` and one colour are
separated at the `J1` range of scale `ell`. -/
theorem areShellSeparated_of_subset_cubeSet {ell kk : ℕ} (hk : ell ≤ kk)
    {R S : TriadicCube d} (hR : R.scale = (kk : ℤ)) (hS : S.scale = (kk : ℤ))
    (hcolor : ShellField.cubeShellColor R = ShellField.cubeShellColor S) (hne : R ≠ S)
    {U V : Set (Vec d)} (hU : U ⊆ cubeSet R) (hV : V ⊆ cubeSet S) :
    ShellField.AreShellSeparated ell U V :=
  areShellSeparated_of_subset
    (areShellSeparated_mono_scale hk
      (ShellField.areShellSeparated_cubeSet_of_cubeShellColor_eq hR hS hcolor hne)) hU hV

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- **`hIndep` of `block_concentration`, for an arbitrary family of observables.**
`hYlocal` is the locality of `Y_z` in a region `nbhd z`, `hsep` is the
separation of those regions inside each sublattice, and the conclusion is the
mutual independence inside each sublattice in the exact shape the step takes. -/
theorem iIndepFun_of_shellRestrictionLocal {kappa : Type*}
    (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (ell : ℕ)
    (J : Finset kappa) (part : kappa → Finset (TriadicCube d))
    (Y : ShellSeq d → TriadicCube d → ℝ)
    {nbhd : TriadicCube d → Set (Vec d)} (hnbhd : ∀ z, MeasurableSet (nbhd z))
    (hYlocal : ∀ z : TriadicCube d,
      @Measurable (ShellSeq d) ℝ
        (blockLane ell (ShellField.shellRestrictionSigma (nbhd z) (hnbhd z)))
        inferInstance (fun omega => Y omega z))
    (hsep : ∀ j ∈ J, ∀ z ∈ part j, ∀ z' ∈ part j, z ≠ z' →
      ShellField.AreShellSeparated ell (nbhd z) (nbhd z')) :
    ∀ j ∈ J, iIndepFun
      (fun z : {z // z ∈ part j} => fun omega : ShellSeq d => Y omega (z : TriadicCube d))
      P.toMeasure := by
  intro j hj
  refine iIndepFun_of_blockLane_shellRestrictionSigma hJ1 hJ2 ell
    (U := fun z : {z // z ∈ part j} => nbhd (z : TriadicCube d))
    (fun z => hnbhd (z : TriadicCube d)) (fun z => hYlocal (z : TriadicCube d)) ?_
  intro z z' hzz'
  exact hsep j hj (z : TriadicCube d) z.2 (z' : TriadicCube d) z'.2
    (fun hcon => hzz' (Subtype.ext hcon))

/-- **`hIndep` of `block_concentration` for the centred coarse blocks.**  This is
the hypothesis `hIndep` at `Y = blockDeviation nu L P nn e`. -/
theorem iIndepFun_blockDeviation_of_local [NeZero d] {nu : ℝ} {kappa : Type*}
    (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (ell L nn : ℕ) (e : Vec d)
    (J : Finset kappa) (part : kappa → Finset (TriadicCube d))
    {nbhd : TriadicCube d → Set (Vec d)} (hnbhd : ∀ z, MeasurableSet (nbhd z))
    (hYlocal : ∀ z : TriadicCube d,
      @Measurable (ShellSeq d) ℝ
        (blockLane ell (ShellField.shellRestrictionSigma (nbhd z) (hnbhd z)))
        inferInstance (fun omega => blockDeviation nu L P nn e omega z))
    (hsep : ∀ j ∈ J, ∀ z ∈ part j, ∀ z' ∈ part j, z ≠ z' →
      ShellField.AreShellSeparated ell (nbhd z) (nbhd z')) :
    ∀ j ∈ J, iIndepFun
      (fun z : {z // z ∈ part j} =>
        fun omega : ShellSeq d => blockDeviation nu L P nn e omega (z : TriadicCube d))
      P.toMeasure :=
  iIndepFun_of_shellRestrictionLocal hJ1 hJ2 ell J part
    (fun omega z => blockDeviation nu L P nn e omega z) hnbhd hYlocal hsep

end Independence

end

end SuperdiffusionCLT.Section3.Terms
