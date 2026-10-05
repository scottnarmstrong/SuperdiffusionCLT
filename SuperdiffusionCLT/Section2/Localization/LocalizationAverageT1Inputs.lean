/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageOrlicz
public import SuperdiffusionCLT.Section2.Localization.LocalizationEnvelopeCarrier
public import SuperdiffusionCLT.Section2.Localization.BlockLoewnerCongruence
public import SuperdiffusionCLT.Section2.Localization.BlockGaugeGroup

/-!
# The per-cube inputs of `T1`: `D_z`, `B_z` and the pointwise decomposition

The printed proof of `l.localization.average` uses the per-cube observables `D_z` and `B_z`
(`e.nabla.kmn.Linfty`) and the pointwise decomposition `|LHS| ≤ T₁ + T₂`.  The Orlicz
reduction `localization_average_orlicz_of_summands` takes the latter as the hypothesis `hdecomp`.
This module defines the observables and proves the decomposition from the printed per-cube
inequality.

## The printed carriers

* `localizationGaugeAverage l L R omega` is the printed
  `h_z := (k_L − k_ℓ)_{z+cu_n}`, the volume average of the
  finite shell increment on the cube `R = z + cu_n`.
* `localizationCoarseAt nu l R omega` is the printed `bfA_ℓ(z+cu_n)`:
  the cutoff-`ℓ` coarse block matrix at `R`.
* `localizationT1CubeError nu l L R Pvec omega` is the per-cube localization
  error, the quadratic form
  `G_{−h_z}P · (G_{h_z}ᵗ bfA_L(z+cu_n) G_{h_z} − bfA_ℓ(z+cu_n)) G_{−h_z}P`.
* `localizationB nu l L R Pvec omega` is the printed
  `B_z := |bfA_ℓ^{1/2}(z+cu_n) G_{−h_z}P|²`, read as the
  quadratic form `G_{−h_z}P · bfA_ℓ(z+cu_n) G_{−h_z}P` --- the two agree because
  `|A^{1/2}X|² = X · A X` for the symmetric `bfA_ℓ`.
* `localizationDz nu l L R omega` is the printed `D_z`,
  `ν⁻¹‖k_L − k_ℓ − h_z‖_{L∞(z+cu_n)} + ν⁻²‖k_L − k_ℓ − h_z‖²_{L∞(z+cu_n)}`,
  with the `L∞` norm carried by the explicit `sSup` device used by
  `finiteShellIncrementLinftyNormLargeCube` (a zero is adjoined to the defining
  range, so the carrier is defined in every dimension and for every cube).

## Main results

* `blockVecDot_blockG_conj_eq` --- the printed identity
  `G_{−h}P · G_hᵗ A G_h G_{−h}P = P · A P`, proved from the block adjunction
  `blockVecDot_conj_blockMatMul` and the gauge inverse law `blockG_mul_neg`.
  **No hypothesis.**
* `gaugeComparisonCube_eq_localizationT1CubeError_add_localizationZ` --- the
  per-cube decomposition, an *identity*: the per-cube term of
  the averaged gauged comparison is the localization error plus the printed
  `Z_z`.  **No hypothesis.**
* `abs_averagedGaugeComparison_le_T1_add_localizationT2` --- the printed
  decomposition `|LHS| ≤ T₁ + T₂`, at
  `T₂ = |avsum_z Z_z| = |localizationT2|` and at the printed
  `T₁ = avsum_z D_z B_z`.  Its only hypothesis is the printed per-cube
  inequality, whose left-hand carrier `localizationT1CubeError`
  is defined here; the triangle steps are discharged.
* `localizationD_eq_zero_of_not_lt` --- the printed observation that
  the localization error vanishes identically when `L = ℓ`.  **No hypothesis**,
  and it discharges the `hDdzero` input of the `T1` pipeline at the carrier.
* `localizationB_sq_le_localizationY_sq_mul_localizationR` --- the printed
  pointwise domination `|bfA_ℓ^{1/2}G_{−h_z}P|⁴ ≤ Y_z² R_z`,
  at the carriers `localizationY` and `localizationR`.
  **No hypothesis**: the `bfE_ℓ`-sandwich
  `blockVecDot_envelopeRescale_sandwich` and the block Cauchy--Schwarz
  `abs_blockVecDot_le_blockVecNorm_mul` discharge it.
* `localizationPerturbSize_nonneg`, `localizationD_nonneg` --- the printed
  carriers are nonnegative, the junk branch of the `sSup` device included (the
  pattern of `shellDerivLinftyNorm_nonneg`).  Together they discharge the
  `hDdnn` input of the `T1` pipeline at the carrier; the only hypothesis is the
  parameter range `0 < ν`.
* `localizationB_eq_zero_of_dot_eq_zero` --- the printed `B_z` dies with the
  vector `P`.  **No hypothesis**; it discharges the `hBdzero` input of the `T1`
  pipeline at the carrier.

## What is not proved here

The four `Γ`-indexed per-cube bounds --- the `Γ_1` bound on
`D_z`, the `Γ_{1/2}` bound on `Y_z²`, the
`Γ_2` bound on `|h_z|` and the `Γ_{1/2}` bound on `R_z` --- rest on the analytic
inputs `e.nabla.kmn.Linfty`,
`e.Enaught.vs.A.and.Ahom`, `e.jk.spatialavg`/`p.concentration` and
`e.Enaught.mixing`, none of which is established in this module.  What is proved
from that block is the deterministic part: the vanishing at `L = ℓ`
and the pointwise domination of `|bfA_ℓ^{1/2}G_{−h_z}P|⁴`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## The printed per-cube carriers -/

/-- The printed `h_z := (k_L − k_ℓ)_{z+cu_n}`: the volume
average over the cube `R = z + cu_n` of the finite shell increment. -/
noncomputable def localizationGaugeAverage (l L : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) : Mat d :=
  volumeAverageMat (cubeSet R) (fun y => finiteShellIncrement omega l L y)

/-- The printed `bfA_ℓ(z+cu_n)`: the cutoff-`ℓ` coarse block matrix
at the cube `R`. -/
noncomputable def localizationCoarseAt (nu : ℝ) (l : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) : BlockMat d :=
  Homogenization.coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega l).toCoeffField

/-- The printed per-cube localization error:
`G_{−h_z}P · (G_{h_z}ᵗ bfA_L(z+cu_n) G_{h_z} − bfA_ℓ(z+cu_n)) G_{−h_z}P`.
Its absolute value is dominated by `D_z · B_z`, the printed
per-cube inequality this module's decomposition consumes. -/
noncomputable def localizationT1CubeError (nu : ℝ) (l L : ℕ) (R : TriadicCube d)
    (Pvec : BlockVec d) (omega : ShellSeq d) : ℝ :=
  blockVecDot (localizationGaugeVector l L R Pvec omega)
    (blockMatVecMul
      (ofFullBlockMat
        (toFullBlockMat
            (blockMatMul (blockMatTranspose (blockG (localizationGaugeAverage l L R omega)))
              (blockMatMul (localizationCoarseAt nu L R omega)
                (blockG (localizationGaugeAverage l L R omega)))) -
          toFullBlockMat (localizationCoarseAt nu l R omega)))
      (localizationGaugeVector l L R Pvec omega))

/-- The printed `B_z := |bfA_ℓ^{1/2}(z+cu_n) G_{−h_z}P|²`,
read as the quadratic form `G_{−h_z}P · bfA_ℓ(z+cu_n) G_{−h_z}P`. -/
noncomputable def localizationB (nu : ℝ) (l L : ℕ) (R : TriadicCube d)
    (Pvec : BlockVec d) (omega : ShellSeq d) : ℝ :=
  blockVecDot (localizationGaugeVector l L R Pvec omega)
    (blockMatVecMul (localizationCoarseAt nu l R omega)
      (localizationGaugeVector l L R Pvec omega))

/-! ## The printed localization error `D_z` -/

/-- Values of the perturbation size `‖k_L − k_ℓ − h_z‖_{L∞(z+cu_n)}`,
with an explicit zero adjoined to the index so that the defining
range is nonempty in every dimension and for every cube. -/
noncomputable def localizationPerturbSizeAtIndex (l L : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) : Option {x : Vec d // x ∈ cubeSet R} → ℝ
  | none => 0
  | some x =>
      matrixOperatorNorm
        (finiteShellIncrement omega l L x.1 - localizationGaugeAverage l L R omega)

/-- The printed `‖k_L − k_ℓ − h_z‖_{L∞(z+cu_n)}`. -/
noncomputable def localizationPerturbSize (l L : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) : ℝ :=
  sSup (Set.range (localizationPerturbSizeAtIndex (d := d) l L R omega))

/-- The printed localization error `D_z`,
`ν⁻¹‖k_L − k_ℓ − h_z‖_{L∞(z+cu_n)} + ν⁻²‖k_L − k_ℓ − h_z‖²_{L∞(z+cu_n)}`. -/
noncomputable def localizationDz (nu : ℝ) (l L : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) : ℝ :=
  nu⁻¹ * localizationPerturbSize l L R omega +
    nu⁻¹ ^ 2 * localizationPerturbSize l L R omega ^ 2

/-- **The printed `D_z` vanishes identically when `L = ℓ`**: the localization
error vanishes identically in that case.  For
`¬ ℓ < L` the finite shell increment over `(ℓ, L]` is zero, so `h_z = 0`, the
perturbation `k_L − k_ℓ − h_z` is zero, and the `L∞` carrier collapses to `0`.
This discharges the `hDdzero` input of the `T1` pipeline at the carrier. -/
theorem localizationD_eq_zero_of_not_lt {nu : ℝ} {l L : ℕ} (hlL : ¬ l < L)
    (R : TriadicCube d) (omega : ShellSeq d) :
    localizationDz nu l L R omega = 0 := by
  have hinc : finiteShellIncrement omega l L = 0 := by
    rw [finiteShellIncrement, Finset.Ioc_eq_empty_iff.mpr hlL]
    simp
  have havg : localizationGaugeAverage l L R omega = 0 := by
    have hzero : (fun y => finiteShellIncrement omega l L y) = (0 : Vec d → Mat d) := by
      funext y
      rw [hinc]
      exact RegCoeffField.zero_apply y
    unfold localizationGaugeAverage
    rw [hzero]
    ext i j
    simp [volumeAverageMat, volumeAverage]
  have hsize : localizationPerturbSize l L R omega = 0 := by
    unfold localizationPerturbSize
    have hrange : Set.range (localizationPerturbSizeAtIndex (d := d) l L R omega) = {0} := by
      ext y
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | none => simp [localizationPerturbSizeAtIndex]
        | some x =>
            simp [localizationPerturbSizeAtIndex, hinc, havg]
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨none, rfl⟩
    rw [hrange, csSup_singleton]
  unfold localizationDz
  rw [hsize]
  ring

/-! ## The gauge conjugation identity -/

/-- **The printed identity `G_{−h}P · G_hᵗ A G_h G_{−h}P = P · A P`.**
It is the block adjunction
`blockVecDot_conj_blockMatMul` at the gauge `G_{−h}`, whose pushed-forward
vector is `P` because `G_h G_{−h} = I` (`blockG_mul_neg`).

**No hypothesis.** -/
theorem blockVecDot_blockG_conj_eq (A : BlockMat d) (h : Mat d) (P : BlockVec d) :
    blockVecDot P (blockMatVecMul A P) =
      blockVecDot (blockMatVecMul (blockG (-h)) P)
        (blockMatVecMul
          (blockMatMul (blockMatTranspose (blockG h)) (blockMatMul A (blockG h)))
          (blockMatVecMul (blockG (-h)) P)) := by
  have hP : blockMatVecMul (blockG h) (blockMatVecMul (blockG (-h)) P) = P := by
    rw [← Homogenization.blockMatVecMul_blockMatMul, blockG_mul_neg,
      SuperdiffusionCLT.Section2.Carriers.blockMatVecMul_blockIdentity]
  calc blockVecDot P (blockMatVecMul A P)
      = blockVecDot (blockMatVecMul (blockG h) (blockMatVecMul (blockG (-h)) P))
          (blockMatVecMul A (blockMatVecMul (blockG h) (blockMatVecMul (blockG (-h)) P))) := by
        rw [hP]
    _ = blockVecDot (blockMatVecMul (blockG (-h)) P)
          (blockMatVecMul
            (blockMatMul (blockMatTranspose (blockG h)) (blockMatMul A (blockG h)))
            (blockMatVecMul (blockG (-h)) P)) :=
        (blockVecDot_conj_blockMatMul A (blockG h) (blockMatVecMul (blockG (-h)) P)).symm

/-! ## The per-cube decomposition -/

/-- **The per-cube decomposition, an identity**: for arbitrary block matrices
`AL`, `Al`, `Ahom` and gauge parameter `h`, the quadratic form of the difference
`AL − G_{−h}ᵗ Ahom G_{−h}` at `P` is the quadratic form of the conjugated
difference `G_hᵗ AL G_h − Al` at `G_{−h}P` plus the quadratic form of
`Al − Ahom` at `G_{−h}P`.  The cutoff-`ℓ` terms `Al` cancel. -/
private theorem gaugeQuadratic_decomposition (AL Al Ahom : BlockMat d) (h : Mat d)
    (Pvec : BlockVec d) :
    blockVecDot Pvec
        (blockMatVecMul
          (ofFullBlockMat (toFullBlockMat AL -
            toFullBlockMat (blockMatMul (blockMatTranspose (blockG (-h)))
              (blockMatMul Ahom (blockG (-h)))))) Pvec) =
      blockVecDot (blockMatVecMul (blockG (-h)) Pvec)
          (blockMatVecMul
            (ofFullBlockMat (toFullBlockMat
                (blockMatMul (blockMatTranspose (blockG h)) (blockMatMul AL (blockG h))) -
              toFullBlockMat Al))
            (blockMatVecMul (blockG (-h)) Pvec)) +
        blockVecDot (blockMatVecMul (blockG (-h)) Pvec)
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat Al - toFullBlockMat Ahom))
            (blockMatVecMul (blockG (-h)) Pvec)) := by
  set X : BlockVec d := blockMatVecMul (blockG (-h)) Pvec with hX
  have hP : Pvec = blockMatVecMul (blockG h) X := by
    rw [hX, ← Homogenization.blockMatVecMul_blockMatMul, blockG_mul_neg,
      SuperdiffusionCLT.Section2.Carriers.blockMatVecMul_blockIdentity]
  have hconjAL : blockVecDot Pvec (blockMatVecMul AL Pvec) =
      blockVecDot X
        (blockMatVecMul (blockMatMul (blockMatTranspose (blockG h))
          (blockMatMul AL (blockG h))) X) := by
    rw [hP]
    exact (blockVecDot_conj_blockMatMul AL (blockG h) X).symm
  have hconjAhom : blockVecDot Pvec
        (blockMatVecMul (blockMatMul (blockMatTranspose (blockG (-h)))
          (blockMatMul Ahom (blockG (-h)))) Pvec) =
      blockVecDot X (blockMatVecMul Ahom X) := by
    rw [hX]
    exact blockVecDot_conj_blockMatMul Ahom (blockG (-h)) Pvec
  rw [blockVecDot_blockMatVecMul_ofFullBlockMat_sub AL
      (blockMatMul (blockMatTranspose (blockG (-h))) (blockMatMul Ahom (blockG (-h)))) Pvec,
    hconjAL, hconjAhom,
    blockVecDot_blockMatVecMul_ofFullBlockMat_sub
      (blockMatMul (blockMatTranspose (blockG h)) (blockMatMul AL (blockG h))) Al X,
    blockVecDot_blockMatVecMul_ofFullBlockMat_sub Al Ahom X]
  ring

/-- The per-cube term of the averaged comparison, written in the shape the
abstract decomposition expects.  Definitional. -/
private theorem gaugeComparisonCube_eq_abstractShape (nu : ℝ) (l L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ) (R : TriadicCube d)
    (Pvec : BlockVec d) (omega : ShellSeq d) :
    gaugeComparisonCube nu l L P n R Pvec omega =
      blockVecDot Pvec
        (blockMatVecMul
          (ofFullBlockMat
            (toFullBlockMat (localizationCoarseAt nu L R omega) -
              toFullBlockMat
                (blockMatMul
                  (blockMatTranspose (blockG (-(localizationGaugeAverage l L R omega))))
                  (blockMatMul
                    (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))
                    (blockG (-(localizationGaugeAverage l L R omega)))))))
          Pvec) :=
  rfl

/-- The localization error, written in the shape the abstract decomposition
expects.  Definitional. -/
private theorem localizationT1CubeError_eq_abstractShape (nu : ℝ) (l L : ℕ)
    (R : TriadicCube d) (Pvec : BlockVec d) (omega : ShellSeq d) :
    localizationT1CubeError nu l L R Pvec omega =
      blockVecDot (blockMatVecMul (blockG (-(localizationGaugeAverage l L R omega))) Pvec)
        (blockMatVecMul
          (ofFullBlockMat
            (toFullBlockMat
                (blockMatMul (blockMatTranspose (blockG (localizationGaugeAverage l L R omega)))
                  (blockMatMul (localizationCoarseAt nu L R omega)
                    (blockG (localizationGaugeAverage l L R omega)))) -
              toFullBlockMat (localizationCoarseAt nu l R omega)))
          (blockMatVecMul (blockG (-(localizationGaugeAverage l L R omega))) Pvec)) :=
  rfl

/-- The printed `Z_z`, written in the shape the abstract decomposition
expects.  Definitional. -/
private theorem localizationZ_eq_abstractShape (nu : ℝ) (l L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ) (R : TriadicCube d)
    (Pvec : BlockVec d) (omega : ShellSeq d) :
    localizationZ nu l L P n R Pvec omega =
      blockVecDot (blockMatVecMul (blockG (-(localizationGaugeAverage l L R omega))) Pvec)
        (blockMatVecMul
          (ofFullBlockMat
            (toFullBlockMat (localizationCoarseAt nu l R omega) -
              toFullBlockMat
                (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))))
          (blockMatVecMul (blockG (-(localizationGaugeAverage l L R omega))) Pvec)) :=
  rfl

/-- **The per-cube decomposition**: the per-cube term of the averaged gauged
comparison is the printed localization error plus the printed `Z_z`,

`P·(bfA_L − G_{−h}ᵗ bfAhom G_{−h})P = G_{−h}P·(G_hᵗ bfA_L G_h − bfA_ℓ)G_{−h}P + Z_z`.

This is the printed decomposition read as an identity: `blockVecDot_blockG_conj_eq` rewrites
`P·bfA_L P`, the adjunction rewrites `P·(G_{−h}ᵗ bfAhom G_{−h})P` as
`G_{−h}P·bfAhom G_{−h}P`, and the cutoff-`ℓ` terms cancel between the error and
`Z_z`.

**No hypothesis.** -/
theorem gaugeComparisonCube_eq_localizationT1CubeError_add_localizationZ
    (nu : ℝ) (l L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ)
    (R : TriadicCube d) (Pvec : BlockVec d) (omega : ShellSeq d) :
    gaugeComparisonCube nu l L P n R Pvec omega =
      localizationT1CubeError nu l L R Pvec omega +
        localizationZ nu l L P n R Pvec omega := by
  rw [gaugeComparisonCube_eq_abstractShape nu l L P n R Pvec omega,
    localizationT1CubeError_eq_abstractShape nu l L R Pvec omega,
    localizationZ_eq_abstractShape nu l L P n R Pvec omega]
  exact gaugeQuadratic_decomposition (localizationCoarseAt nu L R omega)
    (localizationCoarseAt nu l R omega)
    (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ))))
    (localizationGaugeAverage l L R omega) Pvec

/-! ## The pointwise decomposition `|LHS| ≤ T₁ + T₂` -/

/-- **The printed pointwise decomposition `|LHS| ≤ T₁ + T₂`.**

`LHS` is the averaged gauged comparison `averagedGaugeComparison`, `T₁` is the
printed normalized average `avsum_z D_z B_z` and `T₂` is
`|avsum_z Z_z|`, that is, `localizationT2` in absolute value.

The unique hypothesis is the printed **per-cube inequality**
`|G_{−h_z}P·(G_{h_z}ᵗ bfA_L G_{h_z} − bfA_ℓ)G_{−h_z}P| ≤ D_z B_z`,
whose left-hand side is the carrier `localizationT1CubeError`.  The
three triangle steps of the printed proof --- the per-cube decomposition
(proved as an identity), the triangle inequality for the finite
average, and the triangle inequality in the summand --- are discharged.
**No other hypothesis**: in particular no positivity, measurability or
nondegeneracy of `D_z` or `B_z` is used. -/
theorem abs_averagedGaugeComparison_le_T1_add_localizationT2
    (nu : ℝ) (l L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (m n : ℕ)
    (Pvec : BlockVec d) (Dd : TriadicCube d → ShellSeq d → ℝ) (T1 : ShellSeq d → ℝ)
    (hT1 : ∀ omega, T1 omega =
      ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
          Dd R omega * localizationB nu l L R Pvec omega)
    (hpoint : ∀ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n), ∀ omega,
      |localizationT1CubeError nu l L R Pvec omega| ≤
        Dd R omega * localizationB nu l L R Pvec omega) :
    ∀ omega, |averagedGaugeComparison nu l L P m n Pvec omega| ≤
      T1 omega + |localizationT2 nu l L P m n Pvec omega| := by
  intro omega
  have hcard : (0 : ℝ) ≤
      ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hsplit : averagedGaugeComparison nu l L P m n Pvec omega =
      ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            localizationT1CubeError nu l L R Pvec omega +
        localizationT2 nu l L P m n Pvec omega := by
    have hterm : ∀ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
        gaugeComparisonCube nu l L P n R Pvec omega =
          localizationT1CubeError nu l L R Pvec omega +
            localizationZ nu l L P n R Pvec omega := fun R _ =>
      gaugeComparisonCube_eq_localizationT1CubeError_add_localizationZ nu l L P n R Pvec omega
    have hsum : (∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
          gaugeComparisonCube nu l L P n R Pvec omega) =
        ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
          (localizationT1CubeError nu l L R Pvec omega +
            localizationZ nu l L P n R Pvec omega) :=
      Finset.sum_congr rfl hterm
    have havg : averagedGaugeComparison nu l L P m n Pvec omega =
        ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            gaugeComparisonCube nu l L P n R Pvec omega :=
      (congrFun (averagedGaugeComparison_eq_average nu l L P m n Pvec) omega).trans rfl
    rw [havg, hsum, Finset.sum_add_distrib, mul_add, localizationT2]
  have herr : |((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
        localizationT1CubeError nu l L R Pvec omega| ≤ T1 omega := by
    rw [hT1 omega, abs_mul, abs_of_nonneg hcard]
    refine mul_le_mul_of_nonneg_left ?_ hcard
    exact le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum fun R hR => hpoint R hR omega)
  have hstep1 : |averagedGaugeComparison nu l L P m n Pvec omega| =
      |((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
              localizationT1CubeError nu l L R Pvec omega +
          localizationT2 nu l L P m n Pvec omega| := by rw [hsplit]
  have hstep2 : |((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
              localizationT1CubeError nu l L R Pvec omega +
          localizationT2 nu l L P m n Pvec omega| ≤
      |((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
              localizationT1CubeError nu l L R Pvec omega| +
          |localizationT2 nu l L P m n Pvec omega| := abs_add_le _ _
  have hstep3 : |((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
              localizationT1CubeError nu l L R Pvec omega| +
          |localizationT2 nu l L P m n Pvec omega| ≤
      T1 omega + |localizationT2 nu l L P m n Pvec omega| :=
    add_le_add herr le_rfl
  exact hstep1.le.trans (hstep2.trans hstep3)

/-! ## The domination `|bfA_ℓ^{1/2}G_{−h_z}P|⁴ ≤ Y_z² R_z` -/

/-- **The printed pointwise domination**:
`|bfA_ℓ^{1/2}(z+cu_n)G_{−h_z}P|⁴ ≤ Y_z² R_z`, at the carriers
`localizationY` and `localizationR`.

The printed `bfE_ℓ`-sandwich `blockVecDot_envelopeRescale_sandwich` rewrites the
quadratic form `B_z` at the pushed-forward vector `bfE_ℓ^{1/2}G_{−h_z}P`, and
the block Cauchy--Schwarz `abs_blockVecDot_le_blockVecNorm_mul` bounds it by
the operator norm of the normalized perturbation times the squared length —
which are exactly `Y_z` and `W_z = R_z^{1/2}`.

**No hypothesis.** -/
theorem localizationB_sq_le_localizationY_sq_mul_localizationR {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (R : TriadicCube d) (Pvec : BlockVec d) (omega : ShellSeq d) :
    localizationB nu l L R Pvec omega ^ 2 ≤
      localizationY nu l R omega ^ 2 * localizationR nu l L R Pvec omega := by
  have hsand := blockVecDot_envelopeRescale_sandwich hnu l
    (localizationCoarseAt nu l R omega) (localizationGaugeVector l L R Pvec omega)
  have hbound : |localizationB nu l L R Pvec omega| ≤
      localizationY nu l R omega *
        blockVecNorm (blockMatVecMul (envelopeSqrt d nu l)
          (localizationGaugeVector l L R Pvec omega)) ^ 2 := by
    rw [localizationB, hsand, localizationY]
    calc |blockVecDot (blockMatVecMul (envelopeSqrt d nu l)
              (localizationGaugeVector l L R Pvec omega))
            (blockMatVecMul
              (envelopeRescale d nu l (localizationCoarseAt nu l R omega))
              (blockMatVecMul (envelopeSqrt d nu l)
                (localizationGaugeVector l L R Pvec omega)))|
        ≤ blockVecNorm (blockMatVecMul (envelopeSqrt d nu l)
              (localizationGaugeVector l L R Pvec omega)) *
            blockVecNorm (blockMatVecMul
              (envelopeRescale d nu l (localizationCoarseAt nu l R omega))
              (blockMatVecMul (envelopeSqrt d nu l)
                (localizationGaugeVector l L R Pvec omega))) :=
          abs_blockVecDot_le_blockVecNorm_mul _ _
      _ ≤ blockVecNorm (blockMatVecMul (envelopeSqrt d nu l)
              (localizationGaugeVector l L R Pvec omega)) *
            (blockMatrixOperatorNorm
                (envelopeRescale d nu l (localizationCoarseAt nu l R omega)) *
              blockVecNorm (blockMatVecMul (envelopeSqrt d nu l)
                (localizationGaugeVector l L R Pvec omega))) :=
          mul_le_mul_of_nonneg_left (blockVecNorm_blockMatVecMul_le _ _)
            (blockVecNorm_nonneg _)
      _ = blockMatrixOperatorNorm
              (envelopeRescale d nu l (localizationCoarseAt nu l R omega)) *
            blockVecNorm (blockMatVecMul (envelopeSqrt d nu l)
              (localizationGaugeVector l L R Pvec omega)) ^ 2 := by ring
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  rw [sq_abs] at hsq
  refine le_trans hsq (le_of_eq ?_)
  unfold localizationR localizationW
  ring

/-! ## Discharges at the printed carriers -/

/-- The printed `L∞` perturbation size `‖k_L − k_ℓ − h_z‖_{L∞(z+cu_n)}` is
nonnegative, the junk branch of the `sSup` device included — the house pattern
of `shellDerivLinftyNorm_nonneg`.  **No hypothesis.** -/
theorem localizationPerturbSize_nonneg (l L : ℕ) (R : TriadicCube d) (omega : ShellSeq d) :
    0 ≤ localizationPerturbSize l L R omega := by
  unfold localizationPerturbSize
  by_cases hb : BddAbove (Set.range (localizationPerturbSizeAtIndex (d := d) l L R omega))
  · exact le_csSup hb ⟨none, rfl⟩
  · rw [Real.sSup_of_not_bddAbove hb]

/-- The printed localization error `D_z` is nonnegative.  This
discharges the `hDdnn` input of the `T1` pipeline at the carrier.  Its only
hypothesis is the parameter range `0 < ν`. -/
theorem localizationD_nonneg {nu : ℝ} (hnu : 0 < nu) (l L : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) : 0 ≤ localizationDz nu l L R omega := by
  have hnup : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  unfold localizationDz
  exact add_nonneg (mul_nonneg hnup (localizationPerturbSize_nonneg l L R omega))
    (mul_nonneg (pow_nonneg hnup 2) (sq_nonneg _))

/-- **The printed `B_z` vanishes on the degenerate vector** `P = 0`.  This
discharges the `hBdzero` input of the `T1` pipeline at the carrier: the printed
pipeline only needs the vanishing branch, and `|bfA_ℓ^{1/2}G_{−h_z}P|²` dies with
`P` because the gauge acts linearly.  **No hypothesis.** -/
theorem localizationB_eq_zero_of_dot_eq_zero {nu : ℝ} {l L : ℕ} {R : TriadicCube d}
    {Pvec : BlockVec d} (hdot : blockVecDot Pvec Pvec = 0) (omega : ShellSeq d) :
    localizationB nu l L R Pvec omega = 0 := by
  have hPvec : Pvec = 0 := by
    have hsum : vecNormSq Pvec.1 + vecNormSq Pvec.2 = 0 := by
      rwa [SuperdiffusionCLT.Section2.Carriers.blockVecDot_self] at hdot
    rw [add_eq_zero_iff_of_nonneg (vecNormSq_nonneg Pvec.1) (vecNormSq_nonneg Pvec.2)] at hsum
    exact Prod.ext (Homogenization.vecNormSq_eq_zero hsum.1)
      (Homogenization.vecNormSq_eq_zero hsum.2)
  subst hPvec
  have hvec : localizationGaugeVector l L R (0 : BlockVec d) omega = 0 := by
    simp [localizationGaugeVector, blockMatVecMul, matVecMul_zero]
  rw [localizationB, hvec]
  simp [blockVecDot, vecDot]

/-! ## The printed `T₁` carrier -/

/-- The printed `T₁ = avsum_{z ∈ 3^nℤ^d ∩ cu_m} D_z B_z`, at
the carriers `localizationDz` and `localizationB`. -/
noncomputable def localizationT1Carrier (nu : ℝ) (l L : ℕ) (m n : ℕ) (Pvec : BlockVec d)
    (omega : ShellSeq d) : ℝ :=
  ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
      localizationDz nu l L R omega * localizationB nu l L R Pvec omega

end SuperdiffusionCLT.Section2.Localization
