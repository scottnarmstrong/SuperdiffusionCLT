/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Probability.OrliczMoments
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyClause
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellValueLargeCube
public import SuperdiffusionCLT.Section2.Cutoff.Size

/-!
# The annealed `L^∞` moments of the infrared cutoff coefficient

The paper uses the annealed fourth moment of the
cutoff coefficient `a_ℓ = ν Id + k_ℓ` in exactly two places inside the proof of
`e.decompose.flux.u.n`: one display carries `E[‖a_ℓ‖_{L^∞(cu_ℓ)}^4]^{1/2}` and another
carries `E[‖a_ℓ‖_{L^∞(cu_m)}^4]^{1/2}` (`m ≥ ℓ`). This module supplies the `L^∞` envelopes
and tails behind those moments.

## Main results

* `matrixOperatorNorm_coefficientCutoff_le_add`: the pointwise triangle bound
  `|a_ℓ(x)| ≤ ν + |k_ℓ(x)|` at every point, in the Euclidean matrix operator
  norm.
* `isBigO_gammaSigma_streamCutoffLargeCubeSupBound` and
  `isBigO_gammaSigma_coeffLinftySupBound`: the `Γ₂` tails of the measurable
  envelopes of `‖k_ℓ‖_{L^∞(cu_m)}` and `‖a_ℓ‖_{L^∞(cu_m)}`, assembled from the
  single-shell estimate of `ShellValueLargeCube.lean` and from the `L^∞` clause
  for the increment `k_ℓ - k_0` (proved in `IncrementLinftyClause.lean` and
  extended to large cubes in `IncrementLinftyLargeCube.lean`).  The clause is not
  restated here as a hypothesis: the proved estimate is used instead, so every
  amplitude is explicit.

## References

* The paper: the two steps of the proof of `l.RHS.term1`, the definitions of the
  cutoff and its coefficient, and `e.kmn.Linfty`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Set
open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Probability
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The pointwise norm calculus -/

/-- The identity matrix has operator norm at most one, in every dimension: in
dimension zero it is the zero matrix. -/
private theorem matrixOperatorNorm_one_le {d : ℕ} :
    matrixOperatorNorm (1 : Mat d) ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · subst h0
    have hone : (1 : Mat 0) = 0 := by
      ext i _
      exact Fin.elim0 i
    rw [hone, matrixOperatorNorm_zero]
    exact le_of_lt (by norm_num)
  · have : NeZero d := ⟨Nat.ne_of_gt hpos⟩
    rw [matrixOperatorNorm_one]

/-- Matrix-valued evaluation of the cutoff coefficient: `a_ℓ(x) = ν Id + k_ℓ(x)`
as matrices. -/
theorem coefficientCutoff_apply (nu : ℝ) (omega : ShellSeq d) (L : ℕ) (x : Vec d) :
    (coefficientCutoff nu omega L).toCoeffField x =
      nu • (1 : Mat d) + streamCutoff omega L x := by
  unfold coefficientCutoff
  rw [RegCoeffField.toCoeffField_apply, RegCoeffField.add_apply,
    RegCoeffField.constRegCoeffField_apply]

/-- The operator norm is subadditive. -/
private theorem matrixOperatorNorm_add_le (A B : Mat d) :
    matrixOperatorNorm (A + B) ≤ matrixOperatorNorm A + matrixOperatorNorm B :=
  norm_add_le A B

/-- The scaled identity matrix has operator norm at most its amplitude. -/
private theorem matrixOperatorNorm_smul_one_le {c : ℝ} (hc : 0 ≤ c) :
    matrixOperatorNorm (c • (1 : Mat d)) ≤ c := by
  rw [matrixOperatorNorm_eq_l2_opNorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
    ← matrixOperatorNorm_eq_l2_opNorm]
  calc c * matrixOperatorNorm (1 : Mat d) ≤ c * 1 :=
    mul_le_mul_of_nonneg_left matrixOperatorNorm_one_le hc
  _ = c := mul_one c

/-- **The pointwise triangle bound**: at every point of `ℝ^d` the Euclidean matrix
operator norm of the cutoff coefficient `a_ℓ` is bounded by the amplitude `ν`
plus the operator norm of the cutoff stream matrix `k_ℓ` at that point. -/
theorem matrixOperatorNorm_coefficientCutoff_le_add (nu : ℝ) (hnu : 0 ≤ nu)
    (omega : ShellSeq d) (L : ℕ) (x : Vec d) :
    matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x) ≤
      nu + matrixOperatorNorm (streamCutoff omega L x) := by
  rw [coefficientCutoff_apply]
  calc matrixOperatorNorm (nu • (1 : Mat d) + streamCutoff omega L x) ≤
      matrixOperatorNorm (nu • (1 : Mat d)) +
        matrixOperatorNorm (streamCutoff omega L x) :=
    matrixOperatorNorm_add_le _ _
  _ ≤ nu + matrixOperatorNorm (streamCutoff omega L x) :=
    add_le_add (matrixOperatorNorm_smul_one_le hnu) le_rfl

/-! ## The large-cube envelopes of the cutoff and of its coefficient -/

/-- The measurable envelope of the `L^∞(cu_m)` norm of the cutoff stream
matrix `k_L` on the cube `cu_m`, `L ≤ m`: the single shell `j_0` on `cu_m`
(see `ShellValueLargeCube.lean`) plus the finite shell
increment `k_L - k_0` on `cu_m` (see `IncrementLinftyLargeCube.lean`), since
`k_L = j_0 + (k_L - k_0)`. -/
def streamCutoffLargeCubeSupBound (L m : ℕ) (omega : ShellSeq d) : ℝ :=
  shellValueLargeCubeSupBound 0 m omega + largeCubeIncrementSupBound 0 L m omega

/-- The measurable envelope of the `L^∞(cu_m)` norm of the cutoff coefficient
`a_L = ν Id + k_L` on the cube `cu_m`: the amplitude `ν` plus the envelope of
the stream matrix. -/
def coeffLinftySupBound (nu : ℝ) (L m : ℕ) (omega : ShellSeq d) : ℝ :=
  nu + streamCutoffLargeCubeSupBound L m omega

/-- The envelope of the stream matrix is nonnegative. -/
theorem streamCutoffLargeCubeSupBound_nonneg (L m : ℕ) (omega : ShellSeq d) :
    0 ≤ streamCutoffLargeCubeSupBound L m omega :=
  add_nonneg (shellValueLargeCubeSupBound_nonneg 0 m omega)
    (largeCubeIncrementSupBound_nonneg 0 L m omega)

/-- The envelope of the coefficient is nonnegative. -/
theorem coeffLinftySupBound_nonneg (nu : ℝ) (hnu : 0 ≤ nu) (L m : ℕ)
    (omega : ShellSeq d) : 0 ≤ coeffLinftySupBound nu L m omega :=
  add_nonneg hnu (streamCutoffLargeCubeSupBound_nonneg L m omega)

/-- The envelope of the stream matrix is measurable in the shell sequence. -/
theorem measurable_streamCutoffLargeCubeSupBound (L m : ℕ) :
    Measurable (streamCutoffLargeCubeSupBound L m : ShellSeq d → ℝ) :=
  (measurable_shellValueLargeCubeSupBound 0 m).add
    (measurable_largeCubeIncrementSupBound 0 L m)

/-- The envelope of the coefficient is measurable in the shell sequence. -/
theorem measurable_coeffLinftySupBound (nu : ℝ) (L m : ℕ) :
    Measurable (coeffLinftySupBound nu L m : ShellSeq d → ℝ) :=
  measurable_const.add (measurable_streamCutoffLargeCubeSupBound L m)

/-! ## The pointwise dominations on the half-open cube -/

/-- The cutoff field at scale zero is the single shell `j_0`. -/
private theorem streamCutoff_zero_apply (omega : ShellSeq d) (x : Vec d) :
    streamCutoff omega 0 x = omega 0 x := by
  rw [streamCutoff_apply]
  simp

/-- The cutoff field at scale `L` is the single shell plus the finite increment
over `(0, L]`, read pointwise out of the increment identity. -/
private theorem streamCutoff_eq_add_finiteShellIncrement (omega : ShellSeq d)
    (L : ℕ) (x : Vec d) :
    streamCutoff omega L x =
      streamCutoff omega 0 x + finiteShellIncrement omega 0 L x := by
  have h := finiteShellIncrement_apply_eq_streamCutoff_sub omega (Nat.zero_le L) x
  rw [h]
  abel

/-- **The pointwise domination of the cutoff on the large cube.** At every
point of the half-open cube `cu_m`, for every cutoff scale `L` (in particular
for `L ≤ m`), the operator norm of `k_L` is dominated by the measurable
envelope `streamCutoffLargeCubeSupBound L m`. -/
theorem matrixOperatorNorm_streamCutoff_le_streamCutoffLargeCubeSupBound
    (omega : ShellSeq d) {L m : ℕ} {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    matrixOperatorNorm (streamCutoff omega L x) ≤
      streamCutoffLargeCubeSupBound L m omega := by
  have h0 : matrixOperatorNorm (streamCutoff omega 0 x) ≤
      shellValueLargeCubeSupBound 0 m omega := by
    rw [streamCutoff_zero_apply]
    exact matrixOperatorNorm_shellValue_le_shellValueLargeCubeSupBound omega
      (Nat.zero_le m) hx
  have h1 : matrixOperatorNorm (finiteShellIncrement omega 0 L x) ≤
      largeCubeIncrementSupBound 0 L m omega :=
    matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound omega
      (Nat.zero_le m) hx
  calc matrixOperatorNorm (streamCutoff omega L x)
      = matrixOperatorNorm (streamCutoff omega 0 x +
          finiteShellIncrement omega 0 L x) :=
        congrArg matrixOperatorNorm
          (streamCutoff_eq_add_finiteShellIncrement omega L x)
    _ ≤ matrixOperatorNorm (streamCutoff omega 0 x) +
          matrixOperatorNorm (finiteShellIncrement omega 0 L x) :=
      matrixOperatorNorm_add_le _ _
    _ ≤ streamCutoffLargeCubeSupBound L m omega := add_le_add h0 h1

/-- **The pointwise domination of the coefficient on the large cube.** At every
point of the half-open cube `cu_m`, for every cutoff scale `L`, the operator
norm of `a_L` is bounded by the measurable envelope `coeffLinftySupBound nu L m`. -/
theorem matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound
    (nu : ℝ) (hnu : 0 ≤ nu) (omega : ShellSeq d) {L m : ℕ} {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x) ≤
      coeffLinftySupBound nu L m omega := by
  calc matrixOperatorNorm ((coefficientCutoff nu omega L).toCoeffField x) ≤
      nu + matrixOperatorNorm (streamCutoff omega L x) :=
    matrixOperatorNorm_coefficientCutoff_le_add nu hnu omega L x
  _ ≤ nu + streamCutoffLargeCubeSupBound L m omega :=
    add_le_add le_rfl
      (matrixOperatorNorm_streamCutoff_le_streamCutoffLargeCubeSupBound omega hx)
  _ = coeffLinftySupBound nu L m omega := rfl

/-! ## The `L^∞(cu_m)` carrier dominations -/

/-- The coefficient field is continuous in the spatial variable. -/
theorem continuous_coefficientCutoff_apply (nu : ℝ) (omega : ShellSeq d) (L : ℕ) :
    Continuous fun x : Vec d ↦ (coefficientCutoff nu omega L).toCoeffField x := by
  have hcongr : (fun x : Vec d ↦ (coefficientCutoff nu omega L).toCoeffField x) =
      fun x : Vec d ↦ nu • (1 : Mat d) + streamCutoff omega L x :=
    funext fun x ↦ coefficientCutoff_apply nu omega L x
  rw [hcongr]
  exact continuous_const.add (continuous_streamCutoff_apply omega L)

/-! ## The sup-over-the-cube triangle bound -/

/-! ## The `Γ₂` tail of the `L^∞(cu_m)` carrier of the cutoff stream -/

/-- The `Γ₂` amplitude of the `L^∞(cu_m)` carrier of the cutoff stream `k_L` on
the large cube `cu_m`: the stretched-exponential triangle constant
`gammaTriangleConst 2` times the sum of the single-shell amplitude
`shellValueLargeCubeConst d √(1 + m)` of the shell `k_0` on `cu_m` (see
`ShellValueLargeCube.lean`) and the clause (c) increment amplitude
`C √L √m` for `k_L - k_0` on `cu_m` (`e.kmn.Linfty`). -/
def streamCutoffLinftyGammaTwoAmplitude (C : ℝ) (d L m : ℕ) : ℝ :=
  gammaTriangleConst 2 *
    (shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ)) +
      C * (Real.sqrt ((L : ℕ) : ℝ) * Real.sqrt ((m : ℕ) : ℝ)))

/-- The amplitude of the annealed `Γ₂` tail of the `L^∞(cu_m)` carrier of the
cutoff coefficient `a_L = ν Id + k_L`: the amplitude of the stream carrier plus
the deterministic shift `ν` (a nonnegative shift is absorbed in the tail, since
`|ν + X| ≤ ν + |X| ≤ t(ν + A)` whenever `|X| ≤ t A` and `t ≥ 1`). -/
def coeffLinftyGammaTwoAmplitude (nu C : ℝ) (d L m : ℕ) : ℝ :=
  nu + streamCutoffLinftyGammaTwoAmplitude C d L m

/-- The stretched-exponential triangle constant is at least one. -/
private theorem one_le_gammaTriangleConst_two : (1 : ℝ) ≤ gammaTriangleConst 2 := by
  rw [gammaTriangleConst]
  have h2 : ((2 : ℝ) ^ ((12 : ℕ) : ℝ)) ≤ (gammaGrowthConst 2) ^ ((12 : ℕ) : ℝ) :=
    Real.rpow_le_rpow (by norm_num) (two_le_gammaGrowthConst 2) (by norm_num)
  have h3 : (4 : ℝ) * ((2 : ℝ) ^ ((12 : ℕ) : ℝ)) ≤
      (4 : ℝ) * ((gammaGrowthConst 2) ^ ((12 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h4 : (1 : ℝ) ≤ (4 : ℝ) * ((2 : ℝ) ^ ((12 : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]
    norm_num
  exact le_trans h4 h3

/-- The deterministic shift of a `Γ₂`-tailed variable: if `X` has tail amplitude
`A ≥ 0` then `ν + X` has tail amplitude `ν + A`, because for `t ≥ 1`
`|ν + X ω| ≤ ν + |X ω| ≤ ν + t A ≤ t (ν + A)`. This is the bridge that turns the
`Γ₂` tail of the stream carrier into the `Γ₂` tail of the carrier of
`a_L = ν Id + k_L` with an explicit amplitude; the CoarseGraining library only provides
`IsBigO.const_mul` (scaling) and the triangle inequality. -/
theorem isBigO_gammaSigma_const_add_of_isBigO
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω}
    [MeasureTheory.IsFiniteMeasure mu] {X : Ω → ℝ} {nu A : ℝ}
    (hnu : 0 ≤ nu)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma 2) X A) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma 2)
      (fun omega => nu + X omega) (nu + A) := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have hsub : IndependentSums.absTailEvent (fun omega => nu + X omega) ((nu + A) * t) ⊆
      IndependentSums.absTailEvent X (A * t) := by
    intro ω hω
    simp only [IndependentSums.mem_absTailEvent] at hω ⊢
    by_contra hc
    push Not at hc
    have h1 : |nu + X ω| ≤ nu + |X ω| :=
      le_trans (abs_add_le nu (X ω)) (by rw [abs_of_nonneg hnu])
    have hte : nu + A * t ≤ (nu + A) * t := by
      have h1' : nu * 1 ≤ nu * t := mul_le_mul_of_nonneg_left ht hnu
      rw [mul_one] at h1'
      rw [add_mul]
      linarith only [h1']
    have h2 : nu + |X ω| ≤ nu + A * t := by linarith only [hc]
    exact absurd (le_trans (le_trans h1 h2) hte) (not_le.2 hω)
  refine (measureReal_mono hsub ?_).trans (isBigO_gammaSigma_iff.1 hX ht)
  exact measure_ne_top mu (IndependentSums.absTailEvent X (A * t))

/-! ## The `Γ₂` tail of the `L^∞(cu_m)` envelopes -/

/-- The large-cube increment envelope at scale zero vanishes: the finite shell
increment over the empty range `Finset.Ioc 0 0` is zero and the derivative
gauge over the same range is zero. -/
private theorem largeCubeIncrementSupBound_zero_scale (omega : ShellSeq d) (m : ℕ) :
    largeCubeIncrementSupBound 0 0 m omega = 0 := by
  refine le_antisymm
    (Finset.sup'_le (largeCubeSubcubes_nonempty d 0 m)
      (fun R : TriadicCube d ↦
        translatedIncrementSupBound (cubeCenter R) 0 0 omega) ?_)
    (largeCubeIncrementSupBound_nonneg 0 0 m omega)
  intro R hR
  show translatedIncrementSupBound (cubeCenter R) 0 0 omega ≤ 0
  rw [translatedIncrementSupBound_eq (cubeCenter R) 0 0 omega]
  have hsum : finiteShellIncrement omega 0 0 (cubeCenter R) = 0 := by
    rw [finiteShellIncrement_apply, Finset.Ioc_self 0, Finset.sum_empty]
  have hgauge : finiteShellDerivGauge 0 0
      (ShellField.translateSequence (cubeCenter R) omega) = 0 := by
    rw [finiteShellDerivGauge, Finset.Ioc_self 0, Finset.sum_empty]
  rw [hsum, matrixOperatorNorm_zero, hgauge]
  simp

/-- **The `Γ₂` tail of the `L^∞(cu_m)` envelope of the cutoff stream** (`e.kmn.Linfty`):
the measurable envelope `streamCutoffLargeCubeSupBound L m` of the
`cubeLpENorm … ∞` carrier of `k_L` on `cu_m` has the `Γ₂` tail at the amplitude
`streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d L m` for `L ≤ m`;
the envelope is the measurable bound on the
`cubeLpENorm … ∞` carrier of `k_L` on `cu_m`. -/
theorem isBigO_gammaSigma_streamCutoffLargeCubeSupBound
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {L m : ℕ} (hLm : L ≤ m) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦ streamCutoffLargeCubeSupBound L m omega)
      (streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d L m) := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · -- `L = 0`: the increment envelope vanishes, so the envelope is the single shell
    subst hL
    have hamp : shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ)) ≤
        streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d 0 m := by
      rw [streamCutoffLinftyGammaTwoAmplitude]
      simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul, mul_zero, add_zero]
      have h0 : 0 ≤ shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ)) :=
        mul_nonneg (le_trans zero_le_one (one_le_shellValueLargeCubeConst d))
          (Real.sqrt_nonneg _)
      have hstep : shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ)) * 1 ≤
          shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ)) * gammaTriangleConst 2 :=
        mul_le_mul_of_nonneg_left one_le_gammaTriangleConst_two h0
      calc shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ))
          = shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ)) * 1 :=
            (mul_one _).symm
        _ ≤ shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ)) *
            gammaTriangleConst 2 :=
            hstep
        _ = gammaTriangleConst 2 * (shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ))) :=
            mul_comm _ _
    have habs : ∀ omega : ShellSeq d,
        |streamCutoffLargeCubeSupBound 0 m omega| ≤
          |shellValueLargeCubeSupBound 0 m omega| := fun omega ↦ by
      rw [abs_of_nonneg (streamCutoffLargeCubeSupBound_nonneg 0 m omega),
        abs_of_nonneg (shellValueLargeCubeSupBound_nonneg 0 m omega),
        streamCutoffLargeCubeSupBound, largeCubeIncrementSupBound_zero_scale, add_zero]
    have hshellBig : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ shellValueLargeCubeSupBound 0 m omega)
        (streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d 0 m) :=
      (isBigOWith_iff_isBigO_of_nonneg
        (fun omega ↦ shellValueLargeCubeSupBound_nonneg 0 m omega)).1
        ((isBigOWith_gammaSigma_shellValueLargeCubeSupBound hPrefix hJ3 (Nat.zero_le m)).mono_scale
          hamp)
    exact hshellBig.of_abs_le habs
  · -- `0 < L ≤ m`: the triangle inequality over the two envelopes
    have hmpos : (0 : ℕ) < m := lt_of_lt_of_le hL hLm
    have hshellA : (0 : ℝ) < shellValueLargeCubeConst d *
        Real.sqrt (1 + ((m : ℕ) : ℝ)) := by
      refine mul_pos (lt_of_lt_of_le zero_lt_one (one_le_shellValueLargeCubeConst d)) ?_
      exact Real.sqrt_pos.2 (by linarith only [])
    have hincA : (0 : ℝ) < largeCubeLinftyConst d *
        (Real.sqrt ((L : ℕ) : ℝ) * Real.sqrt ((m : ℕ) : ℝ)) := by
      refine mul_pos (largeCubeLinftyConst_pos hPrefix) ?_
      exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hL))
        (Real.sqrt_pos.2 (by exact_mod_cast hmpos))
    have hshell : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ shellValueLargeCubeSupBound 0 m omega)
        (shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ))) := by
      exact (isBigOWith_iff_isBigO_of_nonneg
        (fun omega ↦ shellValueLargeCubeSupBound_nonneg 0 m omega)).1
        (isBigOWith_gammaSigma_shellValueLargeCubeSupBound hPrefix hJ3 (Nat.zero_le m))
    have hinc : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ largeCubeIncrementSupBound 0 L m omega)
        (largeCubeLinftyConst d * (Real.sqrt ((L : ℕ) : ℝ) * Real.sqrt ((m : ℕ) : ℝ))) := by
      exact (isBigOWith_iff_isBigO_of_nonneg
        (fun omega ↦ largeCubeIncrementSupBound_nonneg 0 L m omega)).1
        (isBigOWith_gammaSigma_largeCubeIncrementSupBound hPrefix hJ2 hJ3 hJ4 hL hLm)
    exact isBigO_gammaSigma_add_of_isBigO (sigma := 2) (by norm_num) hshellA hincA hshell hinc
      (measurable_shellValueLargeCubeSupBound 0 m)
      (measurable_largeCubeIncrementSupBound 0 L m)

/-- **The `Γ₂` tail of the `L^∞(cu_m)` envelope of the cutoff coefficient**: the
measurable envelope `coeffLinftySupBound nu L m` of `‖a_ℓ‖_{L^∞(cu_m)}` has the
`Γ₂` tail at the honest amplitude `coeffLinftyGammaTwoAmplitude nu
(largeCubeLinftyConst d) d L m` — the deterministic shift of the envelope of the
stream by `ν`, by the bridge `isBigO_gammaSigma_const_add_of_isBigO`. -/
theorem isBigO_gammaSigma_coeffLinftySupBound
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {nu : ℝ} (hnu : 0 ≤ nu) {L m : ℕ} (hLm : L ≤ m) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦ coeffLinftySupBound nu L m omega)
      (coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d L m) :=
  isBigO_gammaSigma_const_add_of_isBigO hnu
    (isBigO_gammaSigma_streamCutoffLargeCubeSupBound hPrefix hJ2 hJ3 hJ4 hLm)

/-! ## The annealed fourth moment of the `L^∞(cu_m)` carrier of the coefficient -/

end

end SuperdiffusionCLT.Section2.Estimates.Stream