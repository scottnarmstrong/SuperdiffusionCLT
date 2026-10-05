/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageOrlicz
public import SuperdiffusionCLT.Section2.Carriers.BlockOperatorNorm

/-!
# The printed envelope `bfE_ℓ` and the printed carriers of `T_2`

## What `bfE_ℓ` is

`bfE_ℓ` is **not a new object**: it is the printed `bfE_m` of the display
`e.Enaught.mixing`, at `m = ℓ`:

```
\bfE_m \coloneqq \begin{pmatrix}
  \bigl(\nu + 2 C_{\text{\eqref{e.km.Ltwo.size}}} \nu^{-1}(1\vee m)\bigr)\Id & 0 \\
  0 & 2 C_{\text{\eqref{e.km.Ltwo.size}}} \nu^{-1} \Id \end{pmatrix}
```

The first display to *use* `bfE_m` (hence `bfE_ℓ`) is `e.Enaught.vs.A.and.Ahom`.

This is exactly `envelopeBlockMat d nu ℓ`, built
from `envelopeUpperScalar d nu m = nu + 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 m`
and `envelopeLowerScalar d nu = 2 * cutoffEnvelopeConst d * nu⁻¹`, with
`cutoffEnvelopeConst d = max 1 (IndependentSums.gammaMomentConst 1 * (2 * cutoffL2Const d))`
the enlarged, below-truncated-at-`1` reading of the printed `C_{(e.km.Ltwo.size)}`,
so that the printed constant is dominated: `two_mul_cutoffL2Const_le_cutoffEnvelopeConst`.
So `bfE_ℓ` is a naming exercise, not a new definition, and no correction of the printed
text is involved.  The genuinely new object is its square root `bfE_ℓ^{1/2}`; before this file
only `envelopeInvSqrt` was defined.

## Main results

`envelopeSqrt` -- the printed `bfE_ℓ^{1/2}` -- and its API (`envelopeInvSqrt_mul_envelopeSqrt`,
`envelopeSqrt_sq`), the printed `bfE_ℓ`-sandwich `blockVecDot_envelopeRescale_sandwich`, the
block Cauchy--Schwarz `abs_blockVecDot_le_blockVecNorm_mul`, the printed carriers `G_{-h_z}P`,
`bfA_ℓ(z+cu_n) − bfAhom_ℓ(cu_n)`, `W_z`, `Z_z`, `Y_z`, `R_z` and the averaged `T_2`, together
with ambient measurability of the perturbation matrix (`measurable_localizationPerturbationMatrix`),
the gauge vector (`measurable_localizationGaugeVector_entry`), `Z_z`
(`measurable_localizationZ`) and `T_2` (`measurable_localizationT2`), and the printed envelope
norm bound `blockMatrixOperatorNorm_envelopeBlockMat_le`, `|bfE_ℓ| ≤ nu + 2C nu⁻¹(1∨ℓ)`.

**`V_z` is NOT a printed symbol.**  The print writes the sandwiched matrix
`bfE_ℓ^{-1/2}(bfA_ℓ(z+cu_n) − bfAhom_ℓ(cu_n))bfE_ℓ^{-1/2}` inline in the proof of
`l.localization.average`; `V_z` is our name for it (`localizationV`).  `Y_z`, `R_z`, `W_z`,
`Z_z` and `Wbar` are printed.

## What these carriers do NOT provide

* The premise `hfac` of the second-summand estimate is an **exact
  product equality** `T2 ω = W ω * (card⁻¹ ∑ V i ω)` with `W` a factor pulled out
  and `V i` **scalar**.  The printed step is instead a pointwise
  absolute-value **domination** with a random weight: it keeps `Wbar` on the left as a random
  `F_>`-measurable factor and bounds the average of the **norms**
  `blockMatrixOperatorNorm (localizationV ...)`, not of scalars.  So the printed
  carriers do not supply `hfac`.
* Lower-shell strong measurability (`h_compl`-style) is not reached: the generic
  `measurable_coarseBlockMatrix_*_apply` needs `Measurable[m] (coefficientCutoff nu · l)`
  as a full `RegCoeffField`-valued function, while only the entrywise form is
  available.  The measurability proved here is in the ambient σ-algebra.
* The printed `bfE_ℓ` bounds at cubes are available **by citation** only, and they
  are per-cube and deterministic: `blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix`
  and `blockMatLoewnerLE_envelopeRescale_annealedBlockMatrix`.  The statement
  `envelopeRescale_ellipticity`, conjunct 1, quantifies over `Book.Ch02.Domain d`
  (bounded open convex), which `cubeSet Q` is not, so it cannot be applied at a closed
  triadic cube.
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

/-! ## The square root `bfE_ℓ^{1/2}` of the envelope -/

private theorem matVecMul_one_local (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem zero_matVecMul_local (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

private theorem smul_one_mul_smul_one_local (a b : ℝ) :
    (a • (1 : Mat d)) * (b • (1 : Mat d)) = (a * b) • (1 : Mat d) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]

private theorem blockMatVecMul_blockDiag_smul_one (a b : ℝ) (X : BlockVec d) :
    blockMatVecMul (blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) X =
      (a • X.1, b • X.2) := by
  rcases X with ⟨p, q⟩
  have h1 : matVecMul (a • (1 : Mat d)) p + matVecMul (0 : Mat d) q = a • p := by
    rw [smul_matVecMul, matVecMul_one_local, zero_matVecMul_local, add_zero]
  have h2 : matVecMul (0 : Mat d) p + matVecMul (b • (1 : Mat d)) q = b • q := by
    rw [smul_matVecMul, matVecMul_one_local, zero_matVecMul_local, zero_add]
  have hpair : blockMatVecMul (blockDiag (a • (1 : Mat d)) (b • (1 : Mat d)))
      (p, q) = (matVecMul (a • (1 : Mat d)) p + matVecMul (0 : Mat d) q,
        matVecMul (0 : Mat d) p + matVecMul (b • (1 : Mat d)) q) := rfl
  rw [hpair, h1, h2]

/-- The printed `bfE_ℓ^{1/2}`, the square root of the deterministic envelope
`bfE_ℓ = envelopeBlockMat d nu l`.  The inverse square root is
`envelopeInvSqrt`; this is the other half. -/
noncomputable def envelopeSqrt (d : ℕ) (nu : ℝ) (m : ℕ) : BlockMat d :=
  blockDiag ((Real.sqrt (envelopeUpperScalar d nu m)) • (1 : Mat d))
    ((Real.sqrt (envelopeLowerScalar d nu)) • (1 : Mat d))

private theorem blockMatMul_blockDiag_local (A B C D : Mat d) :
    blockMatMul (blockDiag A B) (blockDiag C D) = blockDiag (A * C) (B * D) := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> show _ = _ <;>
    simp only [blockMatMul, blockDiag, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add]

private theorem blockMatVecMul_blockMatMul (A B : BlockMat d) (X : BlockVec d) :
    blockMatVecMul (blockMatMul A B) X = blockMatVecMul A (blockMatVecMul B X) := by
  rcases X with ⟨p, q⟩
  refine Prod.ext ?_ ?_ <;> funext i <;>
    simp only [blockMatVecMul, blockMatMul, matVecMul_add, matVecMul_mul,
      add_matVecMul, Pi.add_apply] <;>
    ring

theorem envelopeInvSqrt_mul_envelopeSqrt {nu : ℝ} (hnu : 0 < nu) (d m : ℕ) :
    blockMatMul (envelopeInvSqrt d nu m) (envelopeSqrt d nu m) = blockIdentity d := by
  have hu : (Real.sqrt (envelopeUpperScalar d nu m))⁻¹ *
      Real.sqrt (envelopeUpperScalar d nu m) = 1 :=
    inv_mul_cancel₀ (Real.sqrt_pos.2 (envelopeUpperScalar_pos hnu d m)).ne'
  have hl : (Real.sqrt (envelopeLowerScalar d nu))⁻¹ *
      Real.sqrt (envelopeLowerScalar d nu) = 1 :=
    inv_mul_cancel₀ (Real.sqrt_pos.2 (envelopeLowerScalar_pos hnu d)).ne'
  rw [envelopeSqrt, envelopeInvSqrt, blockMatMul_blockDiag_local,
    smul_one_mul_smul_one_local, smul_one_mul_smul_one_local, hu, hl, one_smul]
  rfl

/-- **`bfE_ℓ^{1/2} · bfE_ℓ^{1/2} = bfE_ℓ`.**  The square root squares back to the
envelope, the identity that makes the printed `W_z = |bfE_ℓ^{1/2}G|^2`
the quadratic form of `bfE_ℓ` itself. -/
theorem envelopeSqrt_sq {nu : ℝ} (hnu : 0 < nu) (d m : ℕ) :
    blockMatMul (envelopeSqrt d nu m) (envelopeSqrt d nu m) = envelopeBlockMat d nu m := by
  have hu : Real.sqrt (envelopeUpperScalar d nu m) *
      Real.sqrt (envelopeUpperScalar d nu m) = envelopeUpperScalar d nu m :=
    Real.mul_self_sqrt (envelopeUpperScalar_pos hnu d m).le
  have hl : Real.sqrt (envelopeLowerScalar d nu) *
      Real.sqrt (envelopeLowerScalar d nu) = envelopeLowerScalar d nu :=
    Real.mul_self_sqrt (envelopeLowerScalar_pos hnu d).le
  rw [envelopeSqrt, envelopeBlockMat, blockMatMul_blockDiag_local,
    smul_one_mul_smul_one_local, smul_one_mul_smul_one_local, hu, hl]

/-! ## Symmetry of the scalar-block-diagonal factors -/

private theorem blockVecDot_blockMatVecMul_blockDiag_smul_one (a b : ℝ)
    (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) Y) =
      blockVecDot (blockMatVecMul (blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) X) Y := by
  rcases X with ⟨p, q⟩
  rcases Y with ⟨u, v⟩
  rw [blockMatVecMul_blockDiag_smul_one, blockMatVecMul_blockDiag_smul_one]
  simp only [blockVecDot, vecDot_smul_left, vecDot_smul_right]

private theorem blockVecDot_envelopeSqrt_symm {nu : ℝ} (m : ℕ) (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul (envelopeSqrt d nu m) Y) =
      blockVecDot (blockMatVecMul (envelopeSqrt d nu m) X) Y :=
  blockVecDot_blockMatVecMul_blockDiag_smul_one _ _ X Y

private theorem blockVecDot_envelopeInvSqrt_symm {nu : ℝ} (m : ℕ) (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul (envelopeInvSqrt d nu m) Y) =
      blockVecDot (blockMatVecMul (envelopeInvSqrt d nu m) X) Y := by
  have h := blockVecDot_blockMatVecMul_blockDiag_smul_one
    ((Real.sqrt (envelopeUpperScalar d nu m))⁻¹)
    ((Real.sqrt (envelopeLowerScalar d nu))⁻¹) X Y
  simpa only [envelopeInvSqrt] using h

/-- **The printed `bfE_ℓ`-sandwich**: the quadratic form of the
perturbation `M` against `X = G_{-h_z}P` equals the quadratic form of the
normalized perturbation `bfE_ℓ^{-1/2} M bfE_ℓ^{-1/2}` against `bfE_ℓ^{1/2}X`. -/
theorem blockVecDot_envelopeRescale_sandwich {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    (M : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul M X) =
      blockVecDot (blockMatVecMul (envelopeSqrt d nu m) X)
        (blockMatVecMul (envelopeRescale d nu m M)
          (blockMatVecMul (envelopeSqrt d nu m) X)) := by
  have hs : blockMatVecMul (envelopeInvSqrt d nu m)
      (blockMatVecMul (envelopeSqrt d nu m) X) = X := by
    rw [← blockMatVecMul_blockMatMul, envelopeInvSqrt_mul_envelopeSqrt hnu]
    exact Carriers.blockMatVecMul_blockIdentity X
  have hassoc : blockMatVecMul (envelopeRescale d nu m M)
      (blockMatVecMul (envelopeSqrt d nu m) X) =
      blockMatVecMul (envelopeInvSqrt d nu m)
        (blockMatVecMul M (blockMatVecMul (envelopeInvSqrt d nu m)
          (blockMatVecMul (envelopeSqrt d nu m) X))) := by
    rw [envelopeRescale, blockMatVecMul_blockMatMul, blockMatVecMul_blockMatMul]
  rw [hassoc, hs, blockVecDot_envelopeInvSqrt_symm, hs]

/-! ## Cauchy--Schwarz for the doubled pairing -/

private theorem isSymmetricBlockMat_blockIdentity_local (d : ℕ) :
    IsSymmetricBlockMat (blockIdentity d) := by
  intro α β
  cases α <;> cases β <;> simp [blockMatEntry, blockIdentity, blockDiag,
    Matrix.one_apply, Matrix.zero_apply, eq_comm]

private theorem sqrt_blockVecDot_blockIdentity (X : BlockVec d) :
    Real.sqrt (blockVecDot X (blockMatVecMul (blockIdentity d) X)) = blockVecNorm X := by
  rw [Carriers.blockMatVecMul_blockIdentity, Carriers.blockVecDot_self]
  rfl

/-- **Cauchy--Schwarz for the doubled pairing**: `|X·Y| ≤ |X| |Y|`.  The
specialisation of the block Cauchy--Schwarz `B′1` to the doubled identity. -/
theorem abs_blockVecDot_le_blockVecNorm_mul (X Y : BlockVec d) :
    |blockVecDot X Y| ≤ blockVecNorm X * blockVecNorm Y := by
  have hpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul (blockIdentity d) Z) :=
    fun Z => by rw [Carriers.blockMatVecMul_blockIdentity]; exact blockVecDot_self_nonneg Z
  have h := Homogenization.abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat
    (B := blockIdentity d) (isSymmetricBlockMat_blockIdentity_local d) hpsd X Y
  rw [sqrt_blockVecDot_blockIdentity X, sqrt_blockVecDot_blockIdentity Y] at h
  have hY : blockMatVecMul (blockIdentity d) Y = Y := Carriers.blockMatVecMul_blockIdentity Y
  rw [hY] at h
  exact h

/-! ## The printed carriers of the second summand -/

/-- The printed `G_{-h_z}P`: the gauge vector at the cube
`R = z + cu_n`, with `h_z` the volume average of the finite shell increment
`k_L - k_ℓ` on `R`, exactly as in `gaugeComparisonCube`. -/
noncomputable def localizationGaugeVector (l L : ℕ) (R : TriadicCube d)
    (Pvec : BlockVec d) (omega : ShellSeq d) : BlockVec d :=
  blockMatVecMul (blockG (-volumeAverageMat (cubeSet R)
    (fun y => finiteShellIncrement omega l L y))) Pvec

/-- The printed `bfA_ℓ(z+cu_n) - bfAhom_ℓ(cu_n)`: the cutoff-`ℓ`
coarse block matrix at the cube minus the annealed matrix at the origin cube
`cu_n`.  This is the perturbation whose sandwich is the printed `V_z`. -/
noncomputable def localizationPerturbationMatrix (nu : ℝ) (l : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) : BlockMat d :=
  ofFullBlockMat
    (toFullBlockMat (Homogenization.coarseBlockMatrix (cubeSet R)
        (coefficientCutoff nu omega l).toCoeffField) -
      toFullBlockMat (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ)))))

/-- The printed normalized perturbation `bfE_ℓ^{-1/2}(bfA_ℓ(z+cu_n) -
bfAhom_ℓ(cu_n))bfE_ℓ^{-1/2}` (the matrix written inline in the proof; `V_z`
is our name for it, not a printed symbol). -/
noncomputable def localizationV (nu : ℝ) (l : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℕ) (R : TriadicCube d) (omega : ShellSeq d) : BlockMat d :=
  envelopeRescale d nu l (localizationPerturbationMatrix nu l P n R omega)

/-- The printed `Z_z`. -/
noncomputable def localizationZ (nu : ℝ) (l L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℕ) (R : TriadicCube d) (Pvec : BlockVec d) (omega : ShellSeq d) : ℝ :=
  blockVecDot (localizationGaugeVector l L R Pvec omega)
    (blockMatVecMul (localizationPerturbationMatrix nu l P n R omega)
      (localizationGaugeVector l L R Pvec omega))

/-- The printed `W_z = |bfE_ℓ^{1/2}G_{-h_z}P|^2`. -/
noncomputable def localizationW (nu : ℝ) (l L : ℕ) (R : TriadicCube d)
    (Pvec : BlockVec d) (omega : ShellSeq d) : ℝ :=
  blockVecNorm (blockMatVecMul (envelopeSqrt d nu l)
    (localizationGaugeVector l L R Pvec omega)) ^ 2

/-- The printed `Y_z = |bfE_ℓ^{-1/2}bfA_ℓ(z+cu_n)bfE_ℓ^{-1/2}|`. -/
noncomputable def localizationY (nu : ℝ) (l : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) : ℝ :=
  blockMatrixOperatorNorm (envelopeRescale d nu l
    (Homogenization.coarseBlockMatrix (cubeSet R)
      (coefficientCutoff nu omega l).toCoeffField))

/-- The printed `R_z = |bfE_ℓ^{1/2}G_{-h_z}P|^4`, the fourth
power `W_z^2`. -/
noncomputable def localizationR (nu : ℝ) (l L : ℕ) (R : TriadicCube d)
    (Pvec : BlockVec d) (omega : ShellSeq d) : ℝ :=
  localizationW nu l L R Pvec omega ^ 2

/-! ## The printed factorisation and the two structural identities -/

/-- **`W_z` is the `bfE_ℓ`-quadratic form of the gauge vector**: the printed
`|bfE_ℓ^{1/2}G_{-h_z}P|^2` equals `(G_{-h_z}P)·bfE_ℓ(G_{-h_z}P)`, computed with
the envelope `envelopeBlockMat`. -/
theorem localizationW_eq_envelopeBlockMat {nu : ℝ} (hnu : 0 < nu) (l L : ℕ)
    (R : TriadicCube d) (Pvec : BlockVec d) (omega : ShellSeq d) :
    localizationW nu l L R Pvec omega =
      blockVecDot (localizationGaugeVector l L R Pvec omega)
        (blockMatVecMul (envelopeBlockMat d nu l)
          (localizationGaugeVector l L R Pvec omega)) := by
  rw [localizationW, blockVecNorm_sq,
    ← blockVecDot_envelopeSqrt_symm (d := d) (nu := nu) l
      (localizationGaugeVector l L R Pvec omega)
      (blockMatVecMul (envelopeSqrt d nu l) (localizationGaugeVector l L R Pvec omega)),
    ← blockMatVecMul_blockMatMul, envelopeSqrt_sq hnu]

/-- `W_z` is nonnegative, being a squared length. -/
theorem localizationW_nonneg (nu : ℝ) (l L : ℕ) (R : TriadicCube d) (Pvec : BlockVec d)
    (omega : ShellSeq d) : 0 ≤ localizationW nu l L R Pvec omega :=
  sq_nonneg _

/-- The printed averaged second summand `avsum_{z ∈ 3^nℤ^d ∩ cu_m} Z_z`
(the argument of the absolute value in `T_2`). -/
noncomputable def localizationT2 (nu : ℝ) (l L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (m n : ℕ) (Pvec : BlockVec d) (omega : ShellSeq d) : ℝ :=
  ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
      localizationZ nu l L P n R Pvec omega

/-! ## Measurability of the printed carriers -/

/-- A block-matrix family is measurable when its unfolded `2d × 2d` matrix
is. -/
private def MeasFull (M : ShellSeq d → BlockMat d) : Prop :=
  Measurable (fun omega => toFullBlockMat (M omega))

private theorem MeasFull.entry {M : ShellSeq d → BlockMat d} (hM : MeasFull M) :
    ∀ α β : BlockCoord d,
      Measurable (fun omega => toFullBlockMat (M omega) α β) :=
  fun α β => (measurable_pi_apply β).comp ((measurable_pi_apply α).comp hM)

private theorem toFullBlockMat_eq_blockMatEntry (M : BlockMat d) :
    toFullBlockMat M = blockMatEntry M := by
  funext α β
  cases α <;> cases β <;> rfl

private theorem measFull_ofEntry {M : ShellSeq d → BlockMat d}
    (h : ∀ α β, Measurable (fun omega => blockMatEntry (M omega) α β)) : MeasFull M := by
  have hfun : (fun omega => toFullBlockMat (M omega)) = fun omega => blockMatEntry (M omega) := by
    funext omega
    exact toFullBlockMat_eq_blockMatEntry (M omega)
  rw [MeasFull, hfun]
  refine measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_
  exact h α β

private theorem measFull_const (N : BlockMat d) : MeasFull (fun _ : ShellSeq d => N) :=
  measurable_const

private theorem measFull_sub {M N : ShellSeq d → BlockMat d} (hM : MeasFull M)
    (hN : MeasFull N) :
    MeasFull (fun omega => ofFullBlockMat (toFullBlockMat (M omega) - toFullBlockMat (N omega))) := by
  rw [MeasFull]
  refine measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_
  have hsub : Measurable (fun omega =>
      (toFullBlockMat (M omega) - toFullBlockMat (N omega)) α β) :=
    ((MeasFull.entry hM) α β).sub ((MeasFull.entry hN) α β)
  simpa only [toFullBlockMat_ofFullBlockMat, Pi.sub_apply] using hsub

private theorem measFull_entry_coarse {nu : ℝ} (hnu : 0 < nu) (l : ℕ) (R : TriadicCube d) :
    ∀ α β : BlockCoord d,
      Measurable (fun omega => toFullBlockMat (Homogenization.coarseBlockMatrix (cubeSet R)
        (coefficientCutoff nu omega l).toCoeffField) α β) := by
  intro α β
  have hul := SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_upperLeft_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega l)
    (measurable_coefficientCutoff nu l)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) R
  have hur := SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_upperRight_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega l)
    (measurable_coefficientCutoff nu l)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) R
  have hll := SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_lowerLeft_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega l)
    (measurable_coefficientCutoff nu l)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) R
  have hlr := SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_lowerRight_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega l)
    (measurable_coefficientCutoff nu l)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) R
  cases α with
  | inl i =>
      cases β with
      | inl j => exact hul i j
      | inr j => exact hur i j
  | inr i =>
      cases β with
      | inl j => exact hll i j
      | inr j => exact hlr i j

/-- **The printed perturbation matrix is measurable** in the shell sequence. -/
theorem measurable_localizationPerturbationMatrix {nu : ℝ} (hnu : 0 < nu) (l : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ) (R : TriadicCube d) :
    Measurable (fun omega => toFullBlockMat (localizationPerturbationMatrix nu l P n R omega)) :=
  measFull_sub (measFull_ofEntry (measFull_entry_coarse hnu l R))
    (measFull_const (annealedBlockMatrix nu l P (cubeSet (originCube d (n : ℤ)))))

private theorem blockMatVecMul_blockG_fst (h : Mat d) (X : BlockVec d) :
    (blockMatVecMul (blockG h) X).1 = X.1 := by
  rcases X with ⟨p, q⟩
  show matVecMul (1 : Mat d) p + matVecMul (0 : Mat d) q = p
  rw [matVecMul_one_local, zero_matVecMul_local, add_zero]

private theorem blockMatVecMul_blockG_snd (h : Mat d) (X : BlockVec d) :
    (blockMatVecMul (blockG h) X).2 = matVecMul h X.1 + X.2 := by
  rcases X with ⟨p, q⟩
  show matVecMul h p + matVecMul (1 : Mat d) q = matVecMul h p + q
  rw [matVecMul_one_local]

private theorem measurable_matVecMul_const_entry {g : ShellSeq d → Mat d}
    (hg : ∀ i j, Measurable (fun omega => g omega i j)) (v : Vec d) :
    ∀ i, Measurable (fun omega => matVecMul (g omega) v i) := by
  intro i
  simp only [matVecMul]
  exact Finset.measurable_sum _ fun j _ => (hg i j).mul measurable_const

/-- **The printed gauge vector `G_{-h_z}P` is measurable** in the shell
sequence. -/
theorem measurable_localizationGaugeVector_entry (l L : ℕ) (R : TriadicCube d)
    (Pvec : BlockVec d) :
    (∀ i, Measurable (fun omega => (localizationGaugeVector l L R Pvec omega).1 i)) ∧
      (∀ i, Measurable (fun omega => (localizationGaugeVector l L R Pvec omega).2 i)) := by
  have hV : Measurable (fun omega => volumeAverageMat (cubeSet R)
      (fun y => finiteShellIncrement omega l L y)) :=
    measurable_volumeAverageMat_of_isBounded (isBounded_cubeSet R) (measurableSet_cubeSet R)
      (measurable_finiteShellIncrement l L)
  have hg : ∀ i j, Measurable (fun omega =>
      (-volumeAverageMat (cubeSet R) (fun y => finiteShellIncrement omega l L y)) i j) := by
    intro i j
    have hij : Measurable (fun omega => volumeAverageMat (cubeSet R)
        (fun y => finiteShellIncrement omega l L y) i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hV)
    exact hij.neg
  constructor
  · intro i
    have hEq : (fun omega => (localizationGaugeVector l L R Pvec omega).1 i) =
        fun _ : ShellSeq d => Pvec.1 i := by
      funext omega
      rw [localizationGaugeVector, blockMatVecMul_blockG_fst]
    rw [hEq]
    exact measurable_const
  · intro i
    have hEq : (fun omega => (localizationGaugeVector l L R Pvec omega).2 i) =
        fun omega => matVecMul (-volumeAverageMat (cubeSet R)
          (fun y => finiteShellIncrement omega l L y)) Pvec.1 i + Pvec.2 i := by
      funext omega
      rw [localizationGaugeVector, blockMatVecMul_blockG_snd]
      simp only [Pi.add_apply]
    rw [hEq]
    exact (measurable_matVecMul_const_entry hg Pvec.1 i).add measurable_const

private theorem measurable_blockVecDot_blockMatVecMul_fun {M : ShellSeq d → BlockMat d}
    (hM : MeasFull M) {X : ShellSeq d → BlockVec d}
    (hX1 : ∀ i, Measurable (fun omega => (X omega).1 i))
    (hX2 : ∀ i, Measurable (fun omega => (X omega).2 i)) :
    Measurable (fun omega => blockVecDot (X omega) (blockMatVecMul (M omega) (X omega))) := by
  have hE := MeasFull.entry hM
  have h1 : ∀ i, Measurable (fun omega => (blockMatVecMul (M omega) (X omega)).1 i) := by
    intro i
    have hA : Measurable (fun omega => matVecMul (M omega).upperLeft (X omega).1 i) := by
      simp only [matVecMul]
      exact Finset.measurable_sum _ fun j _ => (hE (Sum.inl i) (Sum.inl j)).mul (hX1 j)
    have hB : Measurable (fun omega => matVecMul (M omega).upperRight (X omega).2 i) := by
      simp only [matVecMul]
      exact Finset.measurable_sum _ fun j _ => (hE (Sum.inl i) (Sum.inr j)).mul (hX2 j)
    exact hA.add hB
  have h2 : ∀ i, Measurable (fun omega => (blockMatVecMul (M omega) (X omega)).2 i) := by
    intro i
    have hA : Measurable (fun omega => matVecMul (M omega).lowerLeft (X omega).1 i) := by
      simp only [matVecMul]
      exact Finset.measurable_sum _ fun j _ => (hE (Sum.inr i) (Sum.inl j)).mul (hX1 j)
    have hB : Measurable (fun omega => matVecMul (M omega).lowerRight (X omega).2 i) := by
      simp only [matVecMul]
      exact Finset.measurable_sum _ fun j _ => (hE (Sum.inr i) (Sum.inr j)).mul (hX2 j)
    exact hA.add hB
  have hgoal : (fun omega => blockVecDot (X omega) (blockMatVecMul (M omega) (X omega))) =
      fun omega => (∑ i, (X omega).1 i * (blockMatVecMul (M omega) (X omega)).1 i) +
        (∑ i, (X omega).2 i * (blockMatVecMul (M omega) (X omega)).2 i) := by
    funext omega
    simp only [blockVecDot, vecDot]
  rw [hgoal]
  exact (Finset.measurable_sum _ fun i _ => (hX1 i).mul (h1 i)).add
    (Finset.measurable_sum _ fun i _ => (hX2 i).mul (h2 i))

/-- **The printed `Z_z` is measurable** in the shell sequence: the quadratic form
of the measurable perturbation matrix against the measurable gauge vector. -/
theorem measurable_localizationZ {nu : ℝ} (hnu : 0 < nu) (l L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ) (R : TriadicCube d) (Pvec : BlockVec d) :
    Measurable (localizationZ nu l L P n R Pvec) := by
  have hX := measurable_localizationGaugeVector_entry l L R Pvec
  unfold localizationZ
  exact measurable_blockVecDot_blockMatVecMul_fun
    (measurable_localizationPerturbationMatrix hnu l P n R) hX.1 hX.2

/-! ## Measurability of the normalized carriers

`bfE_ℓ` itself is deterministic, so its own measurability is free.  What the
conditional chain consumes is measurability of the *normalized* carriers: the
sandwiched perturbation `V_z = bfE_ℓ^{-1/2}M_z bfE_ℓ^{-1/2}` and the weight
`W_z`, and then the averaged summand `T_2`.  These are the measurability inputs
of `LocalizationAverageT2Inputs.lean`'s `h_meas` once the printed carriers are
substituted for the abstract family `V`. -/

/-- **The printed averaged second summand `T_2` is measurable** in the shell
sequence, being a finite average of the measurable `Z_z`. -/
theorem measurable_localizationT2 {nu : ℝ} (hnu : 0 < nu) (l L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (m n : ℕ) (Pvec : BlockVec d) :
    Measurable (localizationT2 nu l L P m n Pvec) := by
  unfold localizationT2
  refine Measurable.mul measurable_const ?_
  exact Finset.measurable_sum _ fun R _ => measurable_localizationZ hnu l L P n R Pvec

/-- **The printed envelope norm bound** `|bfE_ℓ| ≤ ν + 2Cν⁻¹(1∨ℓ)`
(printed as `|\bfE_ℓ| ≤ Cν⁻¹(1∨ℓ)`): the operator norm of the
block-diagonal envelope is its larger scalar, the upper block. -/
theorem blockMatrixOperatorNorm_envelopeBlockMat_le {nu : ℝ} (hnu : 0 < nu) (d m : ℕ) :
    blockMatrixOperatorNorm (envelopeBlockMat d nu m) ≤ envelopeUpperScalar d nu m := by
  have hUp := envelopeUpperScalar_pos hnu d m
  have hLow := envelopeLowerScalar_pos hnu d
  have hLowLe : envelopeLowerScalar d nu ≤ envelopeUpperScalar d nu m := by
    have hmax1 : (1 : ℝ) ≤ max 1 (m : ℝ) := le_max_left _ _
    have h : 0 ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ * (max 1 (m : ℝ) - 1) := by
      have hC := cutoffEnvelopeConst_pos d
      have hnuinv : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.le) hnuinv)
        (by linarith only [hmax1])
    unfold envelopeUpperScalar envelopeLowerScalar
    nlinarith only [h, hnu]
  have hconj : blockMatVecMul (envelopeBlockMat d nu m) = fun X : BlockVec d =>
      (envelopeUpperScalar d nu m • X.1, envelopeLowerScalar d nu • X.2) := by
    funext X
    exact blockMatVecMul_blockDiag_smul_one _ _ X
  refine blockMatrixOperatorNorm_le_bound hUp.le fun X => ?_
  rw [hconj]
  have hX1 : vecNormSq (envelopeUpperScalar d nu m • X.1) =
      envelopeUpperScalar d nu m ^ 2 * vecNormSq X.1 := by
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hX2 : vecNormSq (envelopeLowerScalar d nu • X.2) =
      envelopeLowerScalar d nu ^ 2 * vecNormSq X.2 := by
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [blockVecNorm, hX1, hX2, blockVecNorm]
  have hbound : envelopeUpperScalar d nu m ^ 2 * vecNormSq X.1 +
      envelopeLowerScalar d nu ^ 2 * vecNormSq X.2 ≤
      envelopeUpperScalar d nu m ^ 2 * (vecNormSq X.1 + vecNormSq X.2) := by
    have h2 : envelopeLowerScalar d nu * envelopeLowerScalar d nu ≤
        envelopeUpperScalar d nu m * envelopeUpperScalar d nu m :=
      mul_self_le_mul_self hLow.le hLowLe
    nlinarith only [h2, vecNormSq_nonneg X.2]
  calc Real.sqrt (envelopeUpperScalar d nu m ^ 2 * vecNormSq X.1 +
        envelopeLowerScalar d nu ^ 2 * vecNormSq X.2)
      ≤ Real.sqrt (envelopeUpperScalar d nu m ^ 2 * (vecNormSq X.1 + vecNormSq X.2)) :=
        Real.sqrt_le_sqrt hbound
    _ = envelopeUpperScalar d nu m * blockVecNorm X := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hUp.le, blockVecNorm]

end SuperdiffusionCLT.Section2.Localization
