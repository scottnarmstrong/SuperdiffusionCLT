/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.MeanValue
public import SuperdiffusionCLT.Probability.OrliczTriangle
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementHsClause
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyClause
public import SuperdiffusionCLT.Section2.Estimates.Stream.TranslatedIncrementLinfty

/-!
# The two-point shell envelope and the `L̲²` piece of the `H̲^s` clause

The paper estimates the Gagliardo
part of the normalized fractional norm of one shell by taking the bound

> `|j_k(x) − j_k(y)| ≤ O_{Γ₁}(C min{1, 3^{−k}|x−y|})`

**pointwise in the pair `(x, y)`** and only then integrating against the
Gagliardo kernel. That order matters: the supremum of `|j_k|` over the large
cube `cu_l` is only `O_{Γ₂}(√(l−k))`, so a bound read off the cube suprema
carries a factor `√(l−k)` and is not uniform in `l`, while the printed clause
`e.kmn.Hs` needs an amplitude `C 3^{−sn}` with no `l` in it.

This module proves the pointwise-in-the-pair input of that step, together with
the `L̲²` half of the two-piece reading of `‖·‖_{H̲^s}`.

## Main definitions

* `shellPairMinKernel`: the deterministic pair factor `min{1, 2·3^{−k}|x−y|}`.
* `shellPairEnvelope`: the two-point random envelope of one shell at a pair,
  built from the translated cube value norms at `x` and at `y` and the
  translated cube derivative norm at `x`.
* `shellPairEnvelopeConst`: its explicit `Γ₂` amplitude.
* `hsWeightGrowthConst`: the constant of `u 3^{−su} ≤ (e s log 3)⁻¹`.

## Main results

* `shellPairEnvelope`: the envelope bounding, for **every** pair
  `(x, y)`, `‖j_k(x) − j_k(y)‖ ≤ shellPairEnvelope k x y ω · min{1, 2·3^{−k}|x−y|}`.
  The far branch of the `min` uses the two translated value norms, the near
  branch the two-point mean value inequality of
  `Assumptions/ShellField/MeanValue.lean` on the segment, which for
  `|x−y| < 3^k/2` lies inside the translated cube `x + cu_k`.
* `isBigO_gammaSigma_shellPairEnvelope`: that envelope has the symmetric `Γ₂`
  tail at the amplitude `16384 (d + 3)`, **uniformly in the pair `(x, y)` and
  in the cube scale `l`**. This is the exact form the Jensen averaging over the translation
  parameter consumes.
* `exists_witness_cubeHsWeightLtwo_finiteShellIncrement`: the `L̲²` piece
  `3^{−sl} ‖k_m − k_n‖_{L̲²(cu_l)}` of the printed display,
  with a measurable witness whose `Γ₂` amplitude is `C 3^{−sn}`.
* `sum_Ioc_shellWeight_le`, `summable_shellWeight` and `tsum_shellWeight_le`:
  the geometric shell sums `∑_{k>n} 3^{−sk} ≤ 3^{−sn}(1 − 3^{−s})^{-1}` that
  the shell summations need.

## The obstruction in the Gagliardo-supremum clause

The clause `e.kmn.Hs.osc` as printed (and as stated in
`Frozen.Section2.streamIncrement_scale_estimates`) has the pointwise
domination quantified over **every** sample:

> `∀ omega, (⨆ M : {M // n < M}, [k_M − k_n]_{W̲^{s,2}(cu_l)}) ≤ ofReal (X omega)`.

The supremum runs over infinitely many `M`, and `ShellField d` bounds no shell
uniformly in the sequence index, so a sample whose shells do not decay makes
that supremum `⊤`. This happens at
the constant sequence `omega = fun _ => f`, where `k_M − k_n = (M − n) f` and
the seminorm is exactly `(M − n) [f]_{W̲^{s,2}(cu_l)}`: if that seminorm is
nonzero the supremum exceeds every real number, whatever the law `P` and
whatever `C`. The almost-sure form of the clause is unaffected (see
`gagliardoSupClause_of_shellLaws` in `IncrementGagliardoSup.lean`), so the clause must be read
almost surely.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## Elementary comparisons on the ambient carrier -/

/-! ## The two-point envelope of one shell -/

/-- The deterministic pair factor of the paper's pointwise bound, in the normalization
the envelope below realizes: the truncation
`min{1, 2·3^{−k} |x − y|}` of the Lipschitz profile of a shell of scale `k`. -/
def shellPairMinKernel (k : ℕ) (x y : Vec d) : ℝ :=
  min 1 (2 * ((3 : ℝ) ^ k)⁻¹ * euclideanDist x y)

/-- **The two-point envelope of shell `k` at the pair `(x, y)`.** It is built
from one-point data only: the value norm of the shell translated to `x`, the
value norm of the shell translated to `y`, and the derivative norm of the
shell translated to `x`, each read on the natural cube `cu_k` of the shell's
own scale. No supremum over the large cube `cu_l` enters, which is why its
tail below is uniform in `l`. -/
def shellPairEnvelope (k : ℕ) (x y : Vec d) (omega : ShellSeq d) : ℝ :=
  ShellField.shellCubeValueNorm k (ShellField.translate x (omega k)) +
    ShellField.shellCubeValueNorm k (ShellField.translate y (omega k)) +
    ((d : ℝ) + 1) * (3 : ℝ) ^ k *
      ShellField.shellCubeDerivNorm k (ShellField.translate x (omega k))

theorem shellPairEnvelope_nonneg (k : ℕ) (x y : Vec d) (omega : ShellSeq d) :
    0 ≤ shellPairEnvelope k x y omega := by
  have h1 := ShellField.shellCubeValueNorm_nonneg k (ShellField.translate x (omega k))
  have h2 := ShellField.shellCubeValueNorm_nonneg k (ShellField.translate y (omega k))
  have h3 := ShellField.shellCubeDerivNorm_nonneg k (ShellField.translate x (omega k))
  have h4 : (0 : ℝ) ≤ ((d : ℝ) + 1) * (3 : ℝ) ^ k := by positivity
  have h5 : (0 : ℝ) ≤ ((d : ℝ) + 1) * (3 : ℝ) ^ k *
      ShellField.shellCubeDerivNorm k (ShellField.translate x (omega k)) :=
    mul_nonneg h4 h3
  simp only [shellPairEnvelope]
  linarith only [h1, h2, h5]

theorem measurable_shellPairEnvelope (k : ℕ) (x y : Vec d) :
    Measurable (shellPairEnvelope k x y : ShellSeq d → ℝ) := by
  have hx : Measurable fun omega : ShellSeq d ↦
      ShellField.shellCubeValueNorm k (ShellField.translate x (omega k)) :=
    ((ShellField.shellCubeValueNorm_measurable k).comp
      (ShellField.measurable_translate x)).comp
        (ShellField.measurable_shellCoordinate k)
  have hy : Measurable fun omega : ShellSeq d ↦
      ShellField.shellCubeValueNorm k (ShellField.translate y (omega k)) :=
    ((ShellField.shellCubeValueNorm_measurable k).comp
      (ShellField.measurable_translate y)).comp
        (ShellField.measurable_shellCoordinate k)
  have hD : Measurable fun omega : ShellSeq d ↦
      ShellField.shellCubeDerivNorm k (ShellField.translate x (omega k)) :=
    ((ShellField.shellCubeDerivNorm_measurable k).comp
      (ShellField.measurable_translate x)).comp
        (ShellField.measurable_shellCoordinate k)
  exact (hx.add hy).add (measurable_const.mul hD)

/-- The explicit `Γ₂` amplitude of the two-point envelope: the upstream finite
triangle prefactor `16384` times the sum `1 + 1 + (d + 1)` of the three
one-point amplitudes. It depends on `d` only. -/
def shellPairEnvelopeConst (d : ℕ) : ℝ :=
  16384 * ((d : ℝ) + 3)

/-- A nonnegative variable with a one-sided `Γ_σ` tail has the symmetric one.
The `Iff` form `isBigOWith_iff_isBigO_of_nonneg` is not used here: on the shell
carrier its elaboration is expensive, while this one-directional form is
immediate from `IsBigOWith.of_le`. -/
private theorem isBigO_of_isBigOWith_of_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {Psi : ℝ → ℝ} {X : Omega → ℝ} {A : ℝ}
    (hnn : ∀ omega, 0 ≤ X omega) (h : IsBigOWith mu Psi X A) :
    IsBigO mu Psi X A :=
  h.of_le fun omega ↦ le_of_eq (abs_of_nonneg (hnn omega))

/-- The `Γ₂` triangle inequality for three summands, in the shape the
two-point envelope needs. It is stated for abstract variables so that the
`Fin 3` bookkeeping is done once. -/
private theorem isBigO_gammaSigma_add_three {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {X Y Z : Omega → ℝ} {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hXm : Measurable X) (hYm : Measurable Y) (hZm : Measurable Z)
    (hX : IsBigO mu (gammaSigma 2) X a) (hY : IsBigO mu (gammaSigma 2) Y b)
    (hZ : IsBigO mu (gammaSigma 2) Z c) :
    IsBigO mu (gammaSigma 2) (fun omega ↦ X omega + Y omega + Z omega)
      (16384 * (a + b + c)) := by
  have hsum := isBigO_gammaSigma_finset_sum_of_one_le (mu := mu)
    (Finset.univ : Finset (Fin 3)) (X := ![X, Y, Z]) (a := ![a, b, c])
    (sigma := 2) (by norm_num) ⟨0, Finset.mem_univ _⟩
    (by intro i _; fin_cases i <;> simpa using ‹_›)
    (by
      intro i _
      fin_cases i
      · simpa using hX
      · simpa using hY
      · simpa using hZ)
    (by
      intro i _
      fin_cases i
      · simpa using hXm
      · simpa using hYm
      · simpa using hZm)
  have hfun : (fun omega ↦ ∑ i : Fin 3, (![X, Y, Z]) i omega)
      = fun omega ↦ X omega + Y omega + Z omega := by
    funext omega
    simp [Fin.sum_univ_three]
  have hamp : ∑ i : Fin 3, (![a, b, c]) i = a + b + c := by
    simp [Fin.sum_univ_three]
  rw [hfun, hamp] at hsum
  exact hsum

/-- **The two-point envelope has a `Γ₂` tail uniform in the pair.** Each of its
three summands is a one-point observable of a single shell, transported to its
base point by the one-coordinate stationarity of `ShellLawPrefix` and bounded
by J3 at the amplitude `1` for the value norms and `3^{−k}` for the derivative
norm; the scale factor `(d + 1) 3^k` in front of the derivative norm cancels
the `3^{−k}`, so the amplitude does not depend on `k`, on the pair `(x, y)`,
or on any cube. -/
theorem isBigO_gammaSigma_shellPairEnvelope
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (k : ℕ) (x y : Vec d) :
    IsBigO P.toMeasure (gammaSigma 2) (shellPairEnvelope k x y)
      (shellPairEnvelopeConst d) := by
  have hvalueMeas : ∀ z : Vec d, Measurable fun omega : ShellSeq d ↦
      ShellField.shellCubeValueNorm k (ShellField.translate z (omega k)) := by
    intro z
    exact ((ShellField.shellCubeValueNorm_measurable k).comp
      (ShellField.measurable_translate z)).comp
        (ShellField.measurable_shellCoordinate k)
  have hvalue : ∀ z : Vec d, IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d ↦
        ShellField.shellCubeValueNorm k (ShellField.translate z (omega k))) 1 := by
    intro z
    have hOrigin : IsBigOWith P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d ↦ ShellField.shellCubeValueNorm k (omega k)) 1 :=
      (hJ3.isBigOWith_gammaSigma_j3Observable_coordinate k).of_le
        fun F ↦ ShellField.shellCubeValueNorm_le_j3Observable k (F k)
    have hTrans : IsBigOWith P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d ↦
          ShellField.shellCubeValueNorm k (ShellField.translate z (omega k))) 1 :=
      hPrefix.isBigOWith_gammaSigma_shellObservable_translate k z
        (F := ShellField.shellCubeValueNorm k)
        (ShellField.shellCubeValueNorm_measurable k) hOrigin
    exact isBigO_of_isBigOWith_of_nonneg
      (fun omega ↦ ShellField.shellCubeValueNorm_nonneg k
        (ShellField.translate z (omega k))) hTrans
  have hderivMeas : Measurable fun omega : ShellSeq d ↦
      ((d : ℝ) + 1) * (3 : ℝ) ^ k *
        ShellField.shellCubeDerivNorm k (ShellField.translate x (omega k)) :=
    measurable_const.mul
      (((ShellField.shellCubeDerivNorm_measurable k).comp
        (ShellField.measurable_translate x)).comp
          (ShellField.measurable_shellCoordinate k))
  have hderiv : IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d ↦ ((d : ℝ) + 1) * (3 : ℝ) ^ k *
        ShellField.shellCubeDerivNorm k (ShellField.translate x (omega k)))
      ((d : ℝ) + 1) := by
    have hbase : IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d ↦
          ShellField.shellCubeDerivNorm k (ShellField.translate x (omega k)))
        (((3 : ℝ) ^ k)⁻¹) :=
      isBigO_of_isBigOWith_of_nonneg
        (fun omega ↦ ShellField.shellCubeDerivNorm_nonneg k
          (ShellField.translate x (omega k)))
        (isBigOWith_gammaSigma_shellCubeDerivNorm_translate hPrefix hJ3
          (le_refl k) x)
    have hmul := hbase.const_mul
      (c := ((d : ℝ) + 1) * (3 : ℝ) ^ k) (by positivity)
    have hid : ((d : ℝ) + 1) * (3 : ℝ) ^ k * ((3 : ℝ) ^ k)⁻¹ = (d : ℝ) + 1 := by
      field_simp
    rw [hid] at hmul
    simpa only [mul_assoc] using hmul
  have hthree := isBigO_gammaSigma_add_three
    (mu := P.toMeasure) (a := 1) (b := 1) (c := (d : ℝ) + 1)
    one_pos one_pos (by positivity)
    (hvalueMeas x) (hvalueMeas y) hderivMeas (hvalue x) (hvalue y) hderiv
  have hamp : (16384 : ℝ) * (1 + 1 + ((d : ℝ) + 1)) = shellPairEnvelopeConst d := by
    simp only [shellPairEnvelopeConst]
    ring
  rw [hamp] at hthree
  exact hthree

/-! ## The `L̲²` piece of the `H̲^s` clause -/

/-- The value of `sup_{u ≥ 0} u 3^{−su}`, the growth constant that absorbs the
factor `l − n` of the `L^∞` envelope into the weight `3^{−sl}`. -/
def hsWeightGrowthConst (s : ℝ) : ℝ :=
  (Real.exp 1 * s * Real.log 3)⁻¹

/-- `u 3^{−su} ≤ (e s log 3)^{-1}` for `u ≥ 0` and `s > 0`: the elementary
maximization behind the `l`-uniformity of the `L̲²` piece. -/
theorem mul_rpow_three_neg_le_hsWeightGrowthConst {s u : ℝ} (hs : 0 < s)
    (hu : 0 ≤ u) :
    u * (3 : ℝ) ^ (-(s * u)) ≤ hsWeightGrowthConst s := by
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrpow : (3 : ℝ) ^ (-(s * u)) = Real.exp (-(s * u * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have ht0 : 0 ≤ s * u * Real.log 3 :=
    mul_nonneg (mul_nonneg hs.le hu) hL.le
  have hkey : (s * u * Real.log 3) * Real.exp (-(s * u * Real.log 3)) ≤
      Real.exp (-1) := by
    have h1 : s * u * Real.log 3 ≤ Real.exp (s * u * Real.log 3 - 1) := by
      have h := Real.add_one_le_exp (s * u * Real.log 3 - 1)
      linarith only [h]
    calc (s * u * Real.log 3) * Real.exp (-(s * u * Real.log 3))
        ≤ Real.exp (s * u * Real.log 3 - 1) *
            Real.exp (-(s * u * Real.log 3)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = Real.exp (-1) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hexp : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hpos : 0 < Real.exp 1 * s * Real.log 3 := by
    have := Real.exp_pos 1
    positivity
  rw [hrpow, hsWeightGrowthConst, inv_eq_one_div, le_div_iff₀ hpos]
  calc u * Real.exp (-(s * u * Real.log 3)) * (Real.exp 1 * s * Real.log 3)
      = Real.exp 1 *
          ((s * u * Real.log 3) * Real.exp (-(s * u * Real.log 3))) := by ring
    _ ≤ Real.exp 1 * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left hkey (Real.exp_nonneg 1)
    _ = 1 := hexp

/-- The scale weight of the `H̲^s` norm on the natural cube `cu_l`. -/
private theorem cubeHsWeight_originCube (d l : ℕ) (s : ℝ) :
    cubeHsWeight (originCube d (l : ℤ)) s =
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (l : ℝ)))) := by
  rw [cubeHsWeight, cubeScaleFactor_originCube]
  congr 1
  rw [← Real.rpow_intCast (3 : ℝ) (l : ℤ),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

private theorem enorm_eq_ofReal_matrixOperatorNorm (A : Mat d) :
    ‖A‖ₑ = ENNReal.ofReal (matrixOperatorNorm A) := by
  rw [matrixOperatorNorm_eq_l2_opNorm, ofReal_norm]

/-- The normalized `L̲²` norm of a finite increment on `cu_l` is bounded by the
same supremum envelope as the `L^∞` norm, because the normalized cube measure
is a probability measure. -/
theorem cubeLpENorm_two_finiteShellIncrement_le_largeCubeIncrementSupBound
    (omega : ShellSeq d) {n m l : ℕ} (hnl : n ≤ l) :
    cubeLpENorm (originCube d (l : ℤ)) 2
      (fun x => finiteShellIncrement omega n m x) ≤
      ENNReal.ofReal (largeCubeIncrementSupBound n m l omega) := by
  have hae : ∀ᵐ x ∂(normalizedCubeMeasure (originCube d (l : ℤ))),
      ‖finiteShellIncrement omega n m x‖ₑ ≤
        ENNReal.ofReal (largeCubeIncrementSupBound n m l omega) := by
    have h0 : ∀ᵐ x ∂(volume.restrict (cubeSet (originCube d (l : ℤ)))),
        ‖finiteShellIncrement omega n m x‖ₑ ≤
          ENNReal.ofReal (largeCubeIncrementSupBound n m l omega) := by
      filter_upwards
        [ae_restrict_mem (measurableSet_cubeSet (originCube d (l : ℤ)))]
        with x hx
      rw [enorm_eq_ofReal_matrixOperatorNorm]
      exact ENNReal.ofReal_le_ofReal
        (matrixOperatorNorm_finiteShellIncrement_le_largeCubeIncrementSupBound
          omega hnl hx)
    exact Measure.ae_smul_measure h0 _
  have hcont : Continuous (fun x : Vec d ↦ finiteShellIncrement omega n m x) := by
    have hfun : (fun x : Vec d ↦ finiteShellIncrement omega n m x) =
        fun x : Vec d ↦ ∑ k ∈ Finset.Ioc n m, (omega k) x := by
      funext x
      rw [finiteShellIncrement_apply]
      rfl
    rw [hfun]
    exact continuous_finsetSum _ fun k _ ↦ (omega k).1.1.continuous
  have h := eLpNorm_le_of_ae_enorm_bound
    (μ := normalizedCubeMeasure (originCube d (l : ℤ))) (p := 2)
    hcont.aestronglyMeasurable hae
  show eLpNorm (fun x : Vec d => finiteShellIncrement omega n m x) 2
    (normalizedCubeMeasure (originCube d (l : ℤ))) ≤ _
  simpa only [normalizedCubeMeasure_apply_univ, ENNReal.one_rpow, smul_eq_mul,
    mul_one] using h

/-- **The `L̲²` piece of the `H̲^s` clause**, the first summand of the printed
two-piece bound. Its
witness is the `L^∞` envelope of the increment rescaled by the cube weight
`3^{−sl}`, and its `Γ₂` amplitude is `C 3^{−sn}`: the envelope
amplitude `√(m−n) √(l−n)` is at most `l − n`, and `(l − n) 3^{−s(l−n)}` is
bounded by `hsWeightGrowthConst s`, uniformly in `l`. -/
theorem exists_witness_cubeHsWeightLtwo_finiteShellIncrement
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {s : ℝ} (hs : 0 < s) {n m l : ℕ} (hnm : n < m)
    (hml : m ≤ l) {C : ℝ}
    (hC : largeCubeLinftyConst d * hsWeightGrowthConst s ≤ C) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 2) X (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
      ∀ omega : ShellSeq d,
        cubeHsWeight (originCube d (l : ℤ)) s *
            cubeLpENorm (originCube d (l : ℤ)) 2
              (fun x => finiteShellIncrement omega n m x) ≤
          ENNReal.ofReal (X omega) := by
  have hnl : n ≤ l := le_trans hnm.le hml
  have hweightpos : (0 : ℝ) < (3 : ℝ) ^ (-(s * (l : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨fun omega => (3 : ℝ) ^ (-(s * (l : ℝ))) *
      largeCubeIncrementSupBound n m l omega,
    measurable_const.mul (measurable_largeCubeIncrementSupBound n m l), ?_, ?_⟩
  · have hbase : IsBigO P.toMeasure (gammaSigma 2)
        (largeCubeIncrementSupBound n m l)
        (largeCubeLinftyConst d *
          (Real.sqrt ((m - n : ℕ) : ℝ) * Real.sqrt ((l - n : ℕ) : ℝ))) :=
      isBigO_of_isBigOWith_of_nonneg (largeCubeIncrementSupBound_nonneg n m l)
        (isBigOWith_gammaSigma_largeCubeIncrementSupBound hPrefix hJ2 hJ3 hJ4
          hnm hml)
    refine (hbase.const_mul (c := (3 : ℝ) ^ (-(s * (l : ℝ))))
      hweightpos.le).mono_scale ?_
    have hsplit : (3 : ℝ) ^ (-(s * (l : ℝ))) =
        (3 : ℝ) ^ (-(s * (n : ℝ))) * (3 : ℝ) ^ (-(s * ((l - n : ℕ) : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      have hcast : ((l - n : ℕ) : ℝ) = (l : ℝ) - (n : ℝ) := Nat.cast_sub hnl
      rw [hcast]
      ring
    have hsqrt : Real.sqrt ((m - n : ℕ) : ℝ) * Real.sqrt ((l - n : ℕ) : ℝ) ≤
        ((l - n : ℕ) : ℝ) := by
      have hmn : ((m - n : ℕ) : ℝ) ≤ ((l - n : ℕ) : ℝ) := by
        have : m - n ≤ l - n := Nat.sub_le_sub_right hml n
        exact_mod_cast this
      calc Real.sqrt ((m - n : ℕ) : ℝ) * Real.sqrt ((l - n : ℕ) : ℝ)
          ≤ Real.sqrt ((l - n : ℕ) : ℝ) * Real.sqrt ((l - n : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmn) (Real.sqrt_nonneg _)
        _ = ((l - n : ℕ) : ℝ) :=
            Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hgrowth := mul_rpow_three_neg_le_hsWeightGrowthConst (s := s)
      (u := ((l - n : ℕ) : ℝ)) hs (Nat.cast_nonneg _)
    have hLnn : 0 ≤ largeCubeLinftyConst d := by
      have := largeCubeLinftyConst_pos hPrefix
      linarith only [this]
    have hnpow : (0 : ℝ) < (3 : ℝ) ^ (-(s * (n : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    calc (3 : ℝ) ^ (-(s * (l : ℝ))) *
          (largeCubeLinftyConst d *
            (Real.sqrt ((m - n : ℕ) : ℝ) * Real.sqrt ((l - n : ℕ) : ℝ)))
        ≤ (3 : ℝ) ^ (-(s * (l : ℝ))) *
            (largeCubeLinftyConst d * ((l - n : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hweightpos.le
          exact mul_le_mul_of_nonneg_left hsqrt hLnn
      _ = largeCubeLinftyConst d *
            (((l - n : ℕ) : ℝ) * (3 : ℝ) ^ (-(s * ((l - n : ℕ) : ℝ)))) *
              (3 : ℝ) ^ (-(s * (n : ℝ))) := by
          rw [hsplit]
          ring
      _ ≤ largeCubeLinftyConst d * hsWeightGrowthConst s *
            (3 : ℝ) ^ (-(s * (n : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ hnpow.le
          exact mul_le_mul_of_nonneg_left hgrowth hLnn
      _ ≤ C * (3 : ℝ) ^ (-(s * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hC hnpow.le
  · intro omega
    have hle :=
      cubeLpENorm_two_finiteShellIncrement_le_largeCubeIncrementSupBound
        (omega := omega) (n := n) (m := m) (l := l) hnl
    calc cubeHsWeight (originCube d (l : ℤ)) s *
          cubeLpENorm (originCube d (l : ℤ)) 2
            (fun x => finiteShellIncrement omega n m x)
        = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (l : ℝ)))) *
            cubeLpENorm (originCube d (l : ℤ)) 2
              (fun x => finiteShellIncrement omega n m x) := by
          rw [cubeHsWeight_originCube]
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (l : ℝ)))) *
            ENNReal.ofReal (largeCubeIncrementSupBound n m l omega) :=
          mul_le_mul_right hle _
      _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (l : ℝ))) *
            largeCubeIncrementSupBound n m l omega) :=
          (ENNReal.ofReal_mul hweightpos.le).symm

/-! ## The geometric shell sums -/

/-- The shell weight `3^{−sk}` as a power of the ratio `3^{−s}`. -/
theorem rpow_neg_mul_natCast_eq_pow (s : ℝ) (k : ℕ) :
    (3 : ℝ) ^ (-(s * (k : ℝ))) = ((3 : ℝ) ^ (-s)) ^ k := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-s)) k,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

private theorem shellRatio_lt_one {s : ℝ} (hs : 0 < s) :
    (3 : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.2 hs)

/-- The finite shell sum
`∑_{n < k ≤ m} 3^{−sk} ≤ 3^{−sn} (1 − 3^{−s})^{-1}`, uniformly in `m`. -/
theorem sum_Ioc_shellWeight_le {s : ℝ} (hs : 0 < s) (n m : ℕ) :
    ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (-(s * (k : ℝ))) ≤
      (3 : ℝ) ^ (-(s * (n : ℝ))) * (1 - (3 : ℝ) ^ (-s))⁻¹ := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-s) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-s) < 1 := shellRatio_lt_one hs
  have hIoc : Finset.Ioc n m = Finset.Ico (n + 1) (m + 1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hsum : ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (-(s * (k : ℝ)))
      = ((3 : ℝ) ^ (-s)) ^ (n + 1) *
        ∑ i ∈ Finset.range (m - n), ((3 : ℝ) ^ (-s)) ^ i := by
    rw [hIoc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_add_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rpow_neg_mul_natCast_eq_pow, ← pow_add]
  rw [hsum, rpow_neg_mul_natCast_eq_pow]
  have htail : ∑ i ∈ Finset.range (m - n), ((3 : ℝ) ^ (-s)) ^ i ≤
      (1 - (3 : ℝ) ^ (-s))⁻¹ := by
    have hsummable := summable_geometric_of_lt_one hr0 hr1
    have hle := hsummable.sum_le_tsum (Finset.range (m - n))
      (fun i _ => pow_nonneg hr0 i)
    rwa [tsum_geometric_of_lt_one hr0 hr1] at hle
  have hpow : ((3 : ℝ) ^ (-s)) ^ (n + 1) ≤ ((3 : ℝ) ^ (-s)) ^ n :=
    pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ n)
  have hinv : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-s))⁻¹ := by
    have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by linarith only [hr1]
    positivity
  calc ((3 : ℝ) ^ (-s)) ^ (n + 1) *
        ∑ i ∈ Finset.range (m - n), ((3 : ℝ) ^ (-s)) ^ i
      ≤ ((3 : ℝ) ^ (-s)) ^ (n + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ :=
        mul_le_mul_of_nonneg_left htail (pow_nonneg hr0 _)
    _ ≤ ((3 : ℝ) ^ (-s)) ^ n * (1 - (3 : ℝ) ^ (-s))⁻¹ :=
        mul_le_mul_of_nonneg_right hpow hinv

/-- The shell weights above a given scale are summable. -/
theorem summable_shellWeight {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Summable fun j : ℕ => (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ))) := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-s) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-s) < 1 := shellRatio_lt_one hs
  have hcongr : (fun j : ℕ => (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ))))
      = fun j : ℕ => ((3 : ℝ) ^ (-s)) ^ (n + 1) * ((3 : ℝ) ^ (-s)) ^ j := by
    funext j
    rw [rpow_neg_mul_natCast_eq_pow, ← pow_add]
  rw [hcongr]
  exact (summable_geometric_of_lt_one hr0 hr1).mul_left _

/-- The infinite shell sum
`∑_{k > n} 3^{−sk} ≤ 3^{−sn} (1 − 3^{−s})^{-1}`. -/
theorem tsum_shellWeight_le {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∑' j : ℕ, (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ))) ≤
      (3 : ℝ) ^ (-(s * (n : ℝ))) * (1 - (3 : ℝ) ^ (-s))⁻¹ := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-s) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-s) < 1 := shellRatio_lt_one hs
  have hcongr : (fun j : ℕ => (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ))))
      = fun j : ℕ => ((3 : ℝ) ^ (-s)) ^ (n + 1) * ((3 : ℝ) ^ (-s)) ^ j := by
    funext j
    rw [rpow_neg_mul_natCast_eq_pow, ← pow_add]
  have hinv : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-s))⁻¹ := by
    have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by linarith only [hr1]
    positivity
  rw [hcongr, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1,
    rpow_neg_mul_natCast_eq_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ n)) hinv

/-! ## The obstruction in the Gagliardo-supremum clause -/

end

end SuperdiffusionCLT.Section2.Estimates.Stream
