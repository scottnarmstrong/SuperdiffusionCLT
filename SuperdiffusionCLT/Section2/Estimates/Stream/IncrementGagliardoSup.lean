/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.GammaSigmaTsum
public import SuperdiffusionCLT.Probability.OrliczMoments
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementHsClauseD

/-!
# The Gagliardo supremum over the scales above a fixed shell

This module proves clause (e) of the statement
`Frozen.Section2.streamIncrement_scale_estimates` in its almost-sure
reading: for all `l n : ℕ` a
measurable witness `X` with `X = O_{Γ₂}(C 3^{−sn})` and

`⨆_{M > n} [k_M − k_n]_{W̲^{s,2}(cu_l)} ≤ ofReal (X ω)` almost surely,

the constant `C` depending on `d` and `s` only.

## The route

The witness is the **infinite** shell sum `X ω = ∑'_j G_{n+1+j} ω`, with `G_k`
the one-shell Gagliardo witness of shell `k` on `cu_l`, so that for every
`M > n` the finite sum over the shells of `(n, M]` is a partial sum of a
nonnegative series, hence at most `X ω` where the series converges. Three
ingredients are needed.

* **The one-shell display at every scale.** `IncrementHsClauseD` supplies it for
  a shell whose index `k = r + 1` satisfies `r ≤ l`. Clause (e) also needs the
  shells with `l < r`, which clauses (a)-(d) never see because their
  shell range `(n, m]` is bounded by `m ≤ l`. For those the cube `cu_l` sits
  inside the **open** shell cube `cu_k`, so the field has a pair-uniform sup
  bound and a pair-uniform Lipschitz constant there and the deterministic
  kernel estimate `cubeEuclideanGagliardoESeminorm_le_of_sup_lipschitz` of
  `IncrementHsClause` applies directly; the weighted arithmetic-geometric mean
  inequality turns its product `(2A)^{1-s}((d+1)B)^s` into the shell weight
  `3^{-sk}` times a single envelope. The two branches are glued by
  `shellGagliardoAllWitness`.
* **The `Γ₂` tail of the series** is the infinite triangle inequality
  `Probability.GammaSigmaTsum.isBigO_gammaSigma_tsum_of_one_le`, at the
  geometric amplitudes summed by `IncrementHsClauseB.tsum_shellWeight_le`.
* **The almost-sure convergence of the series.** The infinite triangle
  inequality carries no convergence clause — where the series diverges its
  `tsum` value is `0`. Convergence almost everywhere comes from the first-moment
  bound `Probability.OrliczMoments` for a `Γ₂`-tailed variable: the sum of the
  expectations of the nonnegative summands is at most `(1 + Γ(3/2)) ∑_k A_k`,
  finite, so by Tonelli the series is almost everywhere finite.

## Main definitions and results

* `cubeEuclideanGagliardoESeminorm_finset_sum_le`: subadditivity of the
  Gagliardo seminorm over a finite sum of fields.
* `shellGagliardoFarEnvelope`, `shellGagliardoFarWitness`,
  `cubeEuclideanGagliardoESeminorm_shell_le_far`: the one-shell witness and
  display for a shell finer than the cube.
* `shellGagliardoAllWitness`,
  `cubeEuclideanGagliardoESeminorm_shell_le_all`,
  `isBigO_gammaSigma_shellGagliardoAllWitness`: the one-shell display and its
  tail at every pair of scales.
* `gagliardoSupWitness`, `ae_summable_shellGagliardoAllWitness`,
  `iSup_cubeEuclideanGagliardoESeminorm_le_of_summable`: the series, its
  almost-sure convergence and the deterministic pathwise form on that event.
* `gagliardoSupClause_of_shellLaws`: **clause (e)**.
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

/-! ## Subadditivity of the Gagliardo seminorm over a finite sum -/

section Sum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Gagliardo difference kernel is additive, hence commutes with a finite
sum of fields. -/
theorem euclideanGagliardoKernel_finset_sum {ι : Type*} (s : ℝ) (q : ℝ≥0∞)
    (t : Finset ι) (f : ι → Vec d → E) :
    euclideanGagliardoKernel s q (fun x => ∑ i ∈ t, f i x)
      = ∑ i ∈ t, euclideanGagliardoKernel s q (f i) := by
  funext z
  rw [Finset.sum_apply]
  show (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / q.toReal))) •
      ((∑ i ∈ t, f i z.1) - ∑ i ∈ t, f i z.2)
    = ∑ i ∈ t,
      (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / q.toReal))) • (f i z.1 - f i z.2)
  rw [← Finset.smul_sum, Finset.sum_sub_distrib]

/-- **Subadditivity of the Gagliardo seminorm over a finite sum.** The seminorm
is an `eLpNorm` of the difference kernel, which is additive in the field, so
Minkowski's inequality `eLpNorm_sum_le` applies. -/
theorem cubeEuclideanGagliardoESeminorm_finset_sum_le {ι : Type*}
    {Q : TriadicCube d} {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q) (t : Finset ι)
    (f : ι → Vec d → E)
    (_hf : ∀ i ∈ t, AEStronglyMeasurable (euclideanGagliardoKernel s q (f i))
      (Gagliardo.gagliardoCubeMeasure Q)) :
    cubeEuclideanGagliardoESeminorm Q s q (fun x => ∑ i ∈ t, f i x) ≤
      ∑ i ∈ t, cubeEuclideanGagliardoESeminorm Q s q (f i) := by
  rw [cubeEuclideanGagliardoESeminorm, euclideanGagliardoKernel_finset_sum]
  exact eLpNorm_sum_le hq

end Sum

/-- The Gagliardo kernel of a shell field is almost everywhere strongly
measurable for the Gagliardo product measure. -/
theorem aestronglyMeasurable_euclideanGagliardoKernel_shellField
    (Q : TriadicCube d) (s : ℝ) (j : ShellField d) :
    AEStronglyMeasurable
      (euclideanGagliardoKernel s 2 (fun x : Vec d => j x))
      (Gagliardo.gagliardoCubeMeasure Q) := by
  refine Measurable.aestronglyMeasurable ?_
  have hrad : Measurable fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / ((2 : ℝ≥0∞)).toReal)) := by
    show Measurable fun z : Vec d × Vec d =>
      Real.sqrt (∑ i, (z.1 - z.2) i * (z.1 - z.2) i) ^
        (-(s + (d : ℝ) / ((2 : ℝ≥0∞)).toReal))
    fun_prop
  have hc : Continuous fun z : Vec d × Vec d =>
      (j : Vec d → Mat d) z.1 - (j : Vec d → Mat d) z.2 :=
    (j.1.1.continuous.comp continuous_fst).sub (j.1.1.continuous.comp continuous_snd)
  show Measurable fun z : Vec d × Vec d =>
    (euclideanDist z.1 z.2 ^ (-(s + (d : ℝ) / ((2 : ℝ≥0∞)).toReal))) •
      ((j : Vec d → Mat d) z.1 - (j : Vec d → Mat d) z.2)
  exact hrad.smul hc.measurable

/-! ## The one-shell display for a shell finer than the cube -/

/-- The half-open natural cube of scale `l` sits inside the **open** natural
cube of any strictly larger natural scale. -/
theorem cubeSet_originCube_subset_openCubeSet {l k : ℕ} (hlk : l < k) :
    cubeSet (originCube d (l : ℤ)) ⊆ openCubeSet (originCube d (k : ℤ)) := by
  intro x hx
  have hpow : (3 : ℝ) ^ l < (3 : ℝ) ^ k :=
    pow_lt_pow_right₀ (by norm_num) hlk
  rw [mem_cubeSet_originCube_iff] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  rw [zpow_natCast] at hlo hhi
  rw [zpow_natCast]
  constructor <;> linarith only [hlo, hhi, hpow]

/-- **The pair-uniform envelope of one shell on a cube it strictly contains.**
When the cube `cu_l` sits inside the open shell cube `cu_k` the shell has, on
`cu_l`, the sup bound `shellCubeValueNorm k` and the Lipschitz constant
`d · shellCubeDerivNorm k`; this envelope is the sum of twice the first and of
`3^k (d + 1)` times the second, the rescaling that makes the weighted
arithmetic-geometric mean inequality produce the shell weight `3^{-sk}`. -/
def shellGagliardoFarEnvelope (k : ℕ) (omega : ShellSeq d) : ℝ :=
  2 * ShellField.shellCubeValueNorm k (omega k) +
    ((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k *
      ShellField.shellCubeDerivNorm k (omega k)

theorem shellGagliardoFarEnvelope_nonneg (k : ℕ) (omega : ShellSeq d) :
    0 ≤ shellGagliardoFarEnvelope (d := d) k omega := by
  have h1 := ShellField.shellCubeValueNorm_nonneg k (omega k)
  have h2 := ShellField.shellCubeDerivNorm_nonneg k (omega k)
  have h3 : (0 : ℝ) ≤ ((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k := by positivity
  have h4 : (0 : ℝ) ≤ ((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k *
      ShellField.shellCubeDerivNorm k (omega k) := mul_nonneg h3 h2
  rw [shellGagliardoFarEnvelope]
  linarith only [h1, h4]

theorem measurable_shellGagliardoFarEnvelope (k : ℕ) :
    Measurable (shellGagliardoFarEnvelope (d := d) k) := by
  have hV : Measurable fun omega : ShellSeq d =>
      ShellField.shellCubeValueNorm k (omega k) :=
    (ShellField.shellCubeValueNorm_measurable k).comp
      (ShellField.measurable_shellCoordinate k)
  have hD : Measurable fun omega : ShellSeq d =>
      ShellField.shellCubeDerivNorm k (omega k) :=
    (ShellField.shellCubeDerivNorm_measurable k).comp
      (ShellField.measurable_shellCoordinate k)
  exact (measurable_const.mul hV).add (measurable_const.mul hD)

/-- **The one-shell witness for a shell finer than the cube.** -/
def shellGagliardoFarWitness (s : ℝ) (k : ℕ) (omega : ShellSeq d) : ℝ :=
  Real.sqrt (gagliardoOscillationConst d s) * (3 : ℝ) ^ (-(s * (k : ℝ))) *
    shellGagliardoFarEnvelope k omega

theorem shellGagliardoFarWitness_nonneg (s : ℝ) (k : ℕ) (omega : ShellSeq d) :
    0 ≤ shellGagliardoFarWitness (d := d) s k omega := by
  refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) ?_)
    (shellGagliardoFarEnvelope_nonneg k omega)
  exact Real.rpow_nonneg (by norm_num) _

theorem measurable_shellGagliardoFarWitness (s : ℝ) (k : ℕ) :
    Measurable (shellGagliardoFarWitness (d := d) s k) :=
  measurable_const.mul (measurable_shellGagliardoFarEnvelope k)

/-- The scale bookkeeping of the far branch: the Lipschitz factor
`((d+1) · d · shellCubeDerivNorm)` raised to `s` is the rescaled envelope
summand times the shell weight `3^{-sk}`. -/
private theorem far_lipschitz_rpow (dim k : ℕ) {s D : ℝ} (hD : 0 ≤ D) :
    (((dim : ℝ) + 1) * ((dim : ℝ) * D)) ^ s
      = (((dim : ℝ) + 1) * (dim : ℝ) * (3 : ℝ) ^ k * D) ^ s *
        (3 : ℝ) ^ (-(s * (k : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hv : (0 : ℝ) ≤ ((dim : ℝ) + 1) * (dim : ℝ) * (3 : ℝ) ^ k * D := by positivity
  have hinv : (0 : ℝ) ≤ ((3 : ℝ) ^ k)⁻¹ := by positivity
  have hsplit : ((dim : ℝ) + 1) * ((dim : ℝ) * D)
      = (((dim : ℝ) + 1) * (dim : ℝ) * (3 : ℝ) ^ k * D) * ((3 : ℝ) ^ k)⁻¹ := by
    have hne : ((3 : ℝ) ^ k) ≠ 0 := by positivity
    field_simp
  have hpow : (((3 : ℝ) ^ k)⁻¹) ^ s = (3 : ℝ) ^ (-(s * (k : ℝ))) := by
    rw [show ((3 : ℝ) ^ k)⁻¹ = (3 : ℝ) ^ (-(k : ℝ)) by
      rw [Real.rpow_neg h3.le, Real.rpow_natCast],
      ← Real.rpow_mul h3.le]
    congr 1
    ring
  rw [hsplit, Real.mul_rpow hv hinv, hpow]

/-- **The one-shell display for `l < k`.** On a cube strictly inside the open
shell cube the field has a pair-uniform sup bound and a pair-uniform Lipschitz
constant, so the deterministic kernel estimate applies; the weighted
arithmetic-geometric mean inequality turns the product
`(2A)^{1-s} ((d+1)B)^s` into the shell weight times the envelope. -/
theorem cubeEuclideanGagliardoESeminorm_shell_le_far {l k : ℕ} (hlk : l < k)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (omega : ShellSeq d) :
    cubeEuclideanGagliardoESeminorm (originCube d (l : ℤ)) s 2
        (fun x => (omega k) x) ≤
      ENNReal.ofReal (shellGagliardoFarWitness s k omega) := by
  set A : ℝ := ShellField.shellCubeValueNorm k (omega k) with hA_def
  set D : ℝ := ShellField.shellCubeDerivNorm k (omega k) with hD_def
  have hA : 0 ≤ A := ShellField.shellCubeValueNorm_nonneg k (omega k)
  have hD : 0 ≤ D := ShellField.shellCubeDerivNorm_nonneg k (omega k)
  have hB : (0 : ℝ) ≤ (d : ℝ) * D := by positivity
  have hsub := cubeSet_originCube_subset_openCubeSet (d := d) hlk
  have hsup : ∀ x ∈ cubeSet (originCube d (l : ℤ)), ‖(omega k) x‖ ≤ A := by
    intro x hx
    have h := ShellField.matrixOperatorNorm_apply_le_shellCubeValueNorm k
      (omega k) ⟨x, hsub hx⟩
    rwa [matrixOperatorNorm_eq_l2_opNorm] at h
  have hlip : ∀ x ∈ cubeSet (originCube d (l : ℤ)),
      ∀ y ∈ cubeSet (originCube d (l : ℤ)),
        ‖(omega k) x - (omega k) y‖ ≤ (d : ℝ) * D * euclideanDist x y := by
    intro x hx y hy
    have h := ShellField.matrixOperatorNorm_sub_le_of_derivNorm_le_on_openCubeSet
      (omega k) (originCube d (k : ℤ)) D
      (fun z hz => ShellField.matrixDerivativeNorm_deriv_le_shellCubeDerivNorm k
        (omega k) hz) (hsub hx) (hsub hy)
    rwa [matrixOperatorNorm_eq_l2_opNorm] at h
  refine (cubeEuclideanGagliardoESeminorm_le_of_sup_lipschitz hs hs1 hA hB hsup
    hlip).trans (ENNReal.ofReal_le_ofReal ?_)
  have hgeom : (2 * A) ^ (1 - s) * (((d : ℝ) + 1) * ((d : ℝ) * D)) ^ s
      ≤ shellGagliardoFarEnvelope k omega * (3 : ℝ) ^ (-(s * (k : ℝ))) := by
    have hv : (0 : ℝ) ≤ ((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k * D := by positivity
    have hu : (0 : ℝ) ≤ 2 * A := by linarith only [hA]
    have hmean := Real.geom_mean_le_arith_mean2_weighted
      (by linarith only [hs1] : (0 : ℝ) ≤ 1 - s) hs.le hu hv (by ring)
    have hw : (1 - s) * (2 * A) +
        s * (((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k * D)
        ≤ shellGagliardoFarEnvelope k omega := by
      rw [shellGagliardoFarEnvelope]
      have h1 : (1 - s) * (2 * A) ≤ 2 * A := by nlinarith only [hs, hA]
      have h2 : s * (((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k * D)
          ≤ ((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k * D := by
        nlinarith only [hs1, hv, hs]
      linarith only [h1, h2]
    have hkpos : (0 : ℝ) < (3 : ℝ) ^ (-(s * (k : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    calc (2 * A) ^ (1 - s) * (((d : ℝ) + 1) * ((d : ℝ) * D)) ^ s
        = ((2 * A) ^ (1 - s) *
            (((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k * D) ^ s) *
            (3 : ℝ) ^ (-(s * (k : ℝ))) := by
          rw [far_lipschitz_rpow d k hD]
          ring
      _ ≤ shellGagliardoFarEnvelope k omega * (3 : ℝ) ^ (-(s * (k : ℝ))) :=
          mul_le_mul_of_nonneg_right (hmean.trans hw) hkpos.le
  have hKnn : (0 : ℝ) ≤ Real.sqrt (gagliardoOscillationConst d s) :=
    Real.sqrt_nonneg _
  calc Real.sqrt (gagliardoOscillationConst d s) * (2 * A) ^ (1 - s) *
        (((d : ℝ) + 1) * ((d : ℝ) * D)) ^ s
      = Real.sqrt (gagliardoOscillationConst d s) *
          ((2 * A) ^ (1 - s) * (((d : ℝ) + 1) * ((d : ℝ) * D)) ^ s) := by ring
    _ ≤ Real.sqrt (gagliardoOscillationConst d s) *
          (shellGagliardoFarEnvelope k omega * (3 : ℝ) ^ (-(s * (k : ℝ)))) :=
        mul_le_mul_of_nonneg_left hgeom hKnn
    _ = shellGagliardoFarWitness s k omega := by
        rw [shellGagliardoFarWitness]
        ring

/-! ## The `Γ₂` tail of the far branch -/

/-- A nonnegative variable with a one-sided `Γ_σ` tail has the symmetric one. -/
private theorem isBigO_of_isBigOWith_of_nonneg {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {Psi : ℝ → ℝ} {X : Omega → ℝ} {A : ℝ}
    (hnn : ∀ omega, 0 ≤ X omega) (h : IsBigOWith mu Psi X A) :
    IsBigO mu Psi X A :=
  h.of_le fun omega ↦ le_of_eq (abs_of_nonneg (hnn omega))

/-- The `Γ₂` triangle inequality for two summands. -/
private theorem isBigO_gammaSigma_add_two {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {X Y : Omega → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : IsBigO mu (gammaSigma 2) X a) (hY : IsBigO mu (gammaSigma 2) Y b) :
    IsBigO mu (gammaSigma 2) (fun omega => X omega + Y omega)
      (16384 * (a + b)) := by
  have hsum := isBigO_gammaSigma_finset_sum_of_one_le (mu := mu)
    (Finset.univ : Finset (Fin 2)) (X := ![X, Y]) (a := ![a, b])
    (sigma := 2) (by norm_num) ⟨0, Finset.mem_univ _⟩
    (by intro i _; fin_cases i <;> [simpa using ha; simpa using hb])
    (by intro i _; fin_cases i <;> [simpa using hX; simpa using hY])
    (by intro i _; fin_cases i <;> [simpa using hXm; simpa using hYm])
  have hfun : (fun omega ↦ ∑ i : Fin 2, (![X, Y]) i omega)
      = fun omega ↦ X omega + Y omega := by
    funext omega; simp [Fin.sum_univ_two]
  have hamp : ∑ i : Fin 2, (![a, b]) i = a + b := by simp [Fin.sum_univ_two]
  rw [hfun, hamp] at hsum
  exact hsum

/-- The explicit `Γ₂` amplitude of the far envelope: the upstream finite
triangle prefactor `16384` times the sum `2 + ((d + 1) d + 1)` of the two
one-point amplitudes, the `+ 1` keeping the derivative amplitude positive in
dimension zero, where that term vanishes. It depends on `d` only. -/
def shellGagliardoFarEnvelopeConst (d : ℕ) : ℝ :=
  16384 * (3 + ((d : ℝ) + 1) * (d : ℝ))

/-- **The far envelope has a `Γ₂` tail uniform in the shell index.** The value
norm is bounded by the J3 observable at amplitude `1`, and the rescaled
derivative norm at amplitude `3^{-k}`, so the factor `(d + 1) d 3^k` in front of
it cancels the scale. -/
theorem isBigO_gammaSigma_shellGagliardoFarEnvelope (hJ3 : ShellLawJ3 d P) (k : ℕ) :
    IsBigO P.toMeasure (gammaSigma 2) (shellGagliardoFarEnvelope (d := d) k)
      (shellGagliardoFarEnvelopeConst d) := by
  have hVm : Measurable fun omega : ShellSeq d =>
      ShellField.shellCubeValueNorm k (omega k) :=
    (ShellField.shellCubeValueNorm_measurable k).comp
      (ShellField.measurable_shellCoordinate k)
  have hDm : Measurable fun omega : ShellSeq d =>
      ShellField.shellCubeDerivNorm k (omega k) :=
    (ShellField.shellCubeDerivNorm_measurable k).comp
      (ShellField.measurable_shellCoordinate k)
  have hV : IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d =>
        2 * ShellField.shellCubeValueNorm k (omega k)) 2 := by
    have hbase : IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d =>
          ShellField.shellCubeValueNorm k (omega k)) 1 :=
      isBigO_of_isBigOWith_of_nonneg
        (fun omega ↦ ShellField.shellCubeValueNorm_nonneg k (omega k))
        ((hJ3.isBigOWith_gammaSigma_j3Observable_coordinate k).of_le
          fun F ↦ ShellField.shellCubeValueNorm_le_j3Observable k (F k))
    simpa using hbase.const_mul (c := (2 : ℝ)) (by norm_num)
  have hD : IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d =>
        ((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k *
          ShellField.shellCubeDerivNorm k (omega k))
      (((d : ℝ) + 1) * (d : ℝ)) := by
    have hbase : IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d =>
          ShellField.shellCubeDerivNorm k (omega k)) (((3 : ℝ) ^ k)⁻¹) :=
      isBigO_of_isBigOWith_of_nonneg
        (fun omega ↦ ShellField.shellCubeDerivNorm_nonneg k (omega k))
        (isBigOWith_gammaSigma_shellCubeDerivNorm_coordinate hJ3 k)
    have hmul := hbase.const_mul
      (c := ((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k) (by positivity)
    have hid : ((d : ℝ) + 1) * (d : ℝ) * (3 : ℝ) ^ k * ((3 : ℝ) ^ k)⁻¹
        = ((d : ℝ) + 1) * (d : ℝ) := by
      field_simp
    rwa [hid] at hmul
  have hd1 : (0 : ℝ) < ((d : ℝ) + 1) * (d : ℝ) + 1 := by positivity
  have htwo := isBigO_gammaSigma_add_two (mu := P.toMeasure)
    (a := 2) (b := ((d : ℝ) + 1) * (d : ℝ) + 1) (by norm_num) hd1
    (measurable_const.mul hVm) (measurable_const.mul hDm) hV
    (hD.mono_scale (by linarith only [hd1]))
  refine htwo.mono_scale (le_of_eq ?_)
  rw [shellGagliardoFarEnvelopeConst]
  ring

/-- **The `Γ₂` tail of the far one-shell witness.** -/
theorem isBigO_gammaSigma_shellGagliardoFarWitness (hJ3 : ShellLawJ3 d P) (s : ℝ)
    (k : ℕ) :
    IsBigO P.toMeasure (gammaSigma 2) (shellGagliardoFarWitness (d := d) s k)
      (Real.sqrt (gagliardoOscillationConst d s) * shellGagliardoFarEnvelopeConst d *
        (3 : ℝ) ^ (-(s * (k : ℝ)))) := by
  have hc : (0 : ℝ) ≤ Real.sqrt (gagliardoOscillationConst d s) *
      (3 : ℝ) ^ (-(s * (k : ℝ))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  have h := (isBigO_gammaSigma_shellGagliardoFarEnvelope hJ3 k).const_mul hc
  refine h.mono_scale (le_of_eq ?_)
  ring

/-! ## The one-shell display at every pair of scales -/

/-- The explicit constant of the one-shell display valid at every pair of
scales: the maximum of the constant of the coarse branch, proved in
`IncrementHsClauseD`, and of the far-branch constant. It depends on `d` and `s`
only. -/
def shellGagliardoAllConst (d : ℕ) (s : ℝ) : ℝ :=
  max (shellGagliardoConst d s)
    (Real.sqrt (gagliardoOscillationConst d s) * shellGagliardoFarEnvelopeConst d)

theorem shellGagliardoAllConst_pos {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    0 < shellGagliardoAllConst d s :=
  lt_of_lt_of_le (shellGagliardoConst_pos (d := d) hs hs1) (le_max_left _ _)

/-- **The one-shell witness at every pair of scales**: the witness of
`IncrementHsClauseD` when the shell is coarser than the cube's subdivision, and
the far witness otherwise. -/
def shellGagliardoAllWitness (s : ℝ) (r l : ℕ) (omega : ShellSeq d) : ℝ :=
  if r ≤ l then shellGagliardoWitness s r l omega
    else shellGagliardoFarWitness s (r + 1) omega

/-- On a shell coarser than the cube's subdivision the combined witness is the
witness of `IncrementHsClauseD`. -/
theorem shellGagliardoAllWitness_of_le (s : ℝ) {r l : ℕ} (h : r ≤ l) :
    shellGagliardoAllWitness (d := d) s r l = shellGagliardoWitness s r l := by
  funext omega
  rw [shellGagliardoAllWitness, ite_eq_left h]

/-- On a shell finer than the cube the combined witness is the far witness. -/
theorem shellGagliardoAllWitness_of_lt (s : ℝ) {r l : ℕ} (h : l < r) :
    shellGagliardoAllWitness (d := d) s r l = shellGagliardoFarWitness s (r + 1) := by
  funext omega
  rw [shellGagliardoAllWitness, ite_eq_right (by omega : ¬ r ≤ l)]

theorem shellGagliardoAllWitness_nonneg (s : ℝ) (r l : ℕ) (omega : ShellSeq d) :
    0 ≤ shellGagliardoAllWitness (d := d) s r l omega := by
  rcases le_or_gt r l with h | h
  · rw [shellGagliardoAllWitness_of_le s h]
    exact shellGagliardoWitness_nonneg s r l omega
  · rw [shellGagliardoAllWitness_of_lt s h]
    exact shellGagliardoFarWitness_nonneg s (r + 1) omega

theorem measurable_shellGagliardoAllWitness (s : ℝ) (r l : ℕ) :
    Measurable (shellGagliardoAllWitness (d := d) s r l) := by
  rcases le_or_gt r l with h | h
  · rw [shellGagliardoAllWitness_of_le s h]
    exact measurable_shellGagliardoWitness s r l
  · rw [shellGagliardoAllWitness_of_lt s h]
    exact measurable_shellGagliardoFarWitness s (r + 1)

/-- **The one-shell display at every pair of scales.** -/
theorem cubeEuclideanGagliardoESeminorm_shell_le_all (r l : ℕ) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (omega : ShellSeq d) :
    cubeEuclideanGagliardoESeminorm (originCube d (l : ℤ)) s 2
        (fun x => (omega (r + 1)) x) ≤
      ENNReal.ofReal (shellGagliardoAllWitness s r l omega) := by
  rcases le_or_gt r l with h | h
  · rw [shellGagliardoAllWitness_of_le s h]
    exact cubeEuclideanGagliardoESeminorm_shell_le h hs hs1 omega
  · rw [shellGagliardoAllWitness_of_lt s h]
    exact cubeEuclideanGagliardoESeminorm_shell_le_far
      (by omega : l < r + 1) hs hs1 omega

/-- **The `Γ₂` tail of the one-shell display at every pair of scales**, uniform
in the cube scale `l`. -/
theorem isBigO_gammaSigma_shellGagliardoAllWitness
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (r l : ℕ) :
    IsBigO P.toMeasure (gammaSigma 2) (shellGagliardoAllWitness s r l)
      (shellGagliardoAllConst d s * (3 : ℝ) ^ (-(s * (((r + 1 : ℕ)) : ℝ)))) := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (-(s * (((r + 1 : ℕ)) : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rcases le_or_gt r l with h | h
  · rw [shellGagliardoAllWitness_of_le s h]
    refine (isBigO_gammaSigma_shellGagliardoWitness hPrefix hJ3 hs hs1 h).mono_scale ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
  · rw [shellGagliardoAllWitness_of_lt s h]
    refine (isBigO_gammaSigma_shellGagliardoFarWitness hJ3 s (r + 1)).mono_scale ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpow.le

/-! ## The shell series and its deterministic pathwise bound -/

/-- **The witness of clause (e)**: the infinite sum of the one-shell witnesses
over the shells above `n`, read on the cube `cu_l`. Where the series diverges
its value is `0`; the almost-sure convergence is
`ae_summable_shellGagliardoAllWitness`. -/
def gagliardoSupWitness (s : ℝ) (n l : ℕ) (omega : ShellSeq d) : ℝ :=
  ∑' j : ℕ, shellGagliardoAllWitness s (n + j) l omega

/-- A nonnegative real series has the same sum as the associated `ℝ≥0∞` series,
including where it diverges: there the real `tsum` is `0` and the `ℝ≥0∞` one is
`⊤`, whose `toReal` is `0`. -/
private theorem tsum_eq_toReal_tsum_ofReal {iota : Type*} [Countable iota]
    {g : iota → ℝ} (hg : ∀ i, 0 ≤ g i) :
    ∑' i, g i = (∑' i, ENNReal.ofReal (g i)).toReal := by
  by_cases hs : Summable g
  · rw [← ENNReal.ofReal_tsum_of_nonneg hg hs,
      ENNReal.toReal_ofReal (tsum_nonneg hg)]
  · have htop : (∑' i, ENNReal.ofReal (g i)) = ⊤ := by
      by_contra hne
      refine hs ?_
      have hsummable := ENNReal.summable_toReal hne
      refine hsummable.congr fun i => ?_
      exact ENNReal.toReal_ofReal (hg i)
    rw [tsum_eq_zero_of_not_summable hs, htop, ENNReal.toReal_top]

/-- Measurability of the sum of a countable family of nonnegative measurable
functions, through the `ℝ≥0∞` sum. -/
private theorem measurable_tsum_of_nonneg {iota : Type*} [Countable iota]
    {Omega : Type*} [MeasurableSpace Omega] {g : iota → Omega → ℝ}
    (hg0 : ∀ i omega, 0 ≤ g i omega) (hgm : ∀ i, Measurable (g i)) :
    Measurable fun omega => ∑' i, g i omega := by
  have hfun : (fun omega => ∑' i, g i omega)
      = fun omega => (∑' i, ENNReal.ofReal (g i omega)).toReal :=
    funext fun omega => tsum_eq_toReal_tsum_ofReal fun i => hg0 i omega
  rw [hfun]
  exact (Measurable.tsum fun i => (hgm i).ennreal_ofReal).ennreal_toReal

theorem measurable_gagliardoSupWitness (s : ℝ) (n l : ℕ) :
    Measurable (gagliardoSupWitness (d := d) s n l) :=
  measurable_tsum_of_nonneg
    (fun j omega => shellGagliardoAllWitness_nonneg s (n + j) l omega)
    (fun j => measurable_shellGagliardoAllWitness s (n + j) l)

/-- The finite shell increment above `n`, written as a sum over the shells
indexed from the bottom of the range. -/
private theorem finiteShellIncrement_eq_range_sum (omega : ShellSeq d) (n M : ℕ)
    (x : Vec d) :
    finiteShellIncrement omega n M x
      = ∑ j ∈ Finset.range (M - n), (omega (n + j + 1)) x := by
  have h : finiteShellIncrement omega n M x = ∑ k ∈ Finset.Ioc n M, (omega k) x := by
    rw [finiteShellIncrement_apply]
    rfl
  rw [h]
  have hIoc : Finset.Ioc n M = Finset.Ico (n + 1) (M + 1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_add_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.add_right_comm]

/-- **The deterministic pathwise form of clause (e).** At a sample at which the
shell series converges, the Gagliardo seminorm on `cu_l` of every finite
increment `k_M − k_n` with `M > n` is at most the sum of the series: the
seminorm is subadditive over the shells of `(n, M]`, and that finite sum is a
partial sum of a nonnegative convergent series. -/
theorem iSup_cubeEuclideanGagliardoESeminorm_le_of_summable {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (n l : ℕ) {omega : ShellSeq d}
    (hsum : Summable fun j : ℕ => shellGagliardoAllWitness s (n + j) l omega) :
    (⨆ M : {M : ℕ // n < M},
      cubeEuclideanGagliardoESeminorm (originCube d (l : ℤ)) s 2
        (fun x => finiteShellIncrement omega n M.1 x)) ≤
      ENNReal.ofReal (gagliardoSupWitness s n l omega) := by
  refine iSup_le fun M => ?_
  have hfe : (fun x : Vec d => finiteShellIncrement omega n M.1 x)
      = fun x : Vec d => ∑ j ∈ Finset.range (M.1 - n), (omega (n + j + 1)) x :=
    funext fun x => finiteShellIncrement_eq_range_sum omega n M.1 x
  rw [hfe]
  calc cubeEuclideanGagliardoESeminorm (originCube d (l : ℤ)) s 2
          (fun x : Vec d => ∑ j ∈ Finset.range (M.1 - n), (omega (n + j + 1)) x)
      ≤ ∑ j ∈ Finset.range (M.1 - n),
          cubeEuclideanGagliardoESeminorm (originCube d (l : ℤ)) s 2
            (fun x : Vec d => (omega (n + j + 1)) x) :=
        cubeEuclideanGagliardoESeminorm_finset_sum_le (by norm_num) _ _
          (fun j _ => aestronglyMeasurable_euclideanGagliardoKernel_shellField
            (originCube d (l : ℤ)) s (omega (n + j + 1)))
    _ ≤ ∑ j ∈ Finset.range (M.1 - n),
          ENNReal.ofReal (shellGagliardoAllWitness s (n + j) l omega) :=
        Finset.sum_le_sum fun j _ =>
          cubeEuclideanGagliardoESeminorm_shell_le_all (n + j) l hs hs1 omega
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (M.1 - n),
          shellGagliardoAllWitness s (n + j) l omega) :=
        (ENNReal.ofReal_sum_of_nonneg
          (fun j _ => shellGagliardoAllWitness_nonneg s (n + j) l omega)).symm
    _ ≤ ENNReal.ofReal (gagliardoSupWitness s n l omega) :=
        ENNReal.ofReal_le_ofReal
          (hsum.sum_le_tsum (Finset.range (M.1 - n))
            (fun j _ => shellGagliardoAllWitness_nonneg s (n + j) l omega))

/-! ## Almost-sure convergence of the shell series -/

/-- The first moment of a nonnegative `Γ₂`-tailed variable, in the `ℝ≥0∞` form
the Tonelli exchange needs: `∫⁻ ofReal X ≤ ofReal (A (1 + Γ(3/2)))`. -/
private theorem lintegral_ofReal_le_of_isBigO_gammaSigma_two {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {A : ℝ} (hA : 0 < A) (hX0 : ∀ omega, 0 ≤ X omega)
    (hXm : Measurable X) (hX : IsBigO mu (gammaSigma 2) X A) :
    ∫⁻ omega, ENNReal.ofReal (X omega) ∂mu ≤
      ENNReal.ofReal (A * (1 + Real.Gamma ((1 : ℝ) / 2 + 1))) := by
  have hfun : (fun omega => |X omega| ^ (((1 : ℕ)) : ℝ)) = X := by
    funext omega
    rw [Nat.cast_one, Real.rpow_one, abs_of_nonneg (hX0 omega)]
  have hint := integrable_abs_rpow_of_isBigO_gammaSigma_two hA hXm.aemeasurable hX 1
  have hmom := abs_moment_le_of_isBigO_gammaSigma_two hA hXm.aemeasurable hX 1
  rw [hfun] at hint hmom
  rw [Nat.cast_one, Real.rpow_one] at hmom
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hX0)]
  exact ENNReal.ofReal_le_ofReal hmom

/-- **The shell series converges almost surely.** The infinite triangle
inequality carries no convergence clause, and the clause needs one: the
supremum over `M > n` is dominated by the sum of the series only where the
series converges. The convergence is obtained from the first moment of a
`Γ₂`-tailed variable: by Tonelli the expectation of the series is at most
`(1 + Γ(3/2))` times the summable amplitude sum, so the series is almost
everywhere finite. -/
theorem ae_summable_shellGagliardoAllWitness
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (n l : ℕ) :
    ∀ᵐ omega ∂P.toMeasure,
      Summable fun j : ℕ => shellGagliardoAllWitness s (n + j) l omega := by
  have hCpos := shellGagliardoAllConst_pos (d := d) hs hs1
  have hcpos : (0 : ℝ) < 1 + Real.Gamma ((1 : ℝ) / 2 + 1) := by
    have hG : 0 < Real.Gamma ((1 : ℝ) / 2 + 1) :=
      Real.Gamma_pos_of_pos (by norm_num)
    linarith only [hG]
  have hApos : ∀ j : ℕ, 0 < shellGagliardoAllConst d s *
      (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ))) := fun j =>
    mul_pos hCpos (Real.rpow_pos_of_pos (by norm_num) _)
  have hAsummable : Summable fun j : ℕ => shellGagliardoAllConst d s *
      (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ))) :=
    (summable_shellWeight hs n).mul_left _
  have hmeas : ∀ j : ℕ,
      Measurable (shellGagliardoAllWitness (d := d) s (n + j) l) := fun j =>
    measurable_shellGagliardoAllWitness s (n + j) l
  have htail : ∀ j : ℕ, IsBigO P.toMeasure (gammaSigma 2)
      (shellGagliardoAllWitness s (n + j) l)
      (shellGagliardoAllConst d s *
        (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ)))) := by
    intro j
    have h := isBigO_gammaSigma_shellGagliardoAllWitness hPrefix hJ3 hs hs1 (n + j) l
    rwa [show (n + j + 1 : ℕ) = (n + 1 + j : ℕ) from by omega] at h
  have hlint : ∀ j : ℕ,
      ∫⁻ omega, ENNReal.ofReal (shellGagliardoAllWitness s (n + j) l omega)
          ∂P.toMeasure ≤
        ENNReal.ofReal ((shellGagliardoAllConst d s *
          (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ)))) *
            (1 + Real.Gamma ((1 : ℝ) / 2 + 1))) := fun j =>
    lintegral_ofReal_le_of_isBigO_gammaSigma_two (hApos j)
      (fun omega => shellGagliardoAllWitness_nonneg s (n + j) l omega)
      (hmeas j) (htail j)
  have hmeasO : ∀ j : ℕ, Measurable fun omega : ShellSeq d =>
      ENNReal.ofReal (shellGagliardoAllWitness s (n + j) l omega) := fun j =>
    (hmeas j).ennreal_ofReal
  have hmeasE : Measurable fun omega : ShellSeq d =>
      ∑' j : ℕ, ENNReal.ofReal (shellGagliardoAllWitness s (n + j) l omega) :=
    Measurable.tsum hmeasO
  have hfinite :
      ∫⁻ omega, (∑' j : ℕ,
          ENNReal.ofReal (shellGagliardoAllWitness s (n + j) l omega)) ∂P.toMeasure ≤
        ENNReal.ofReal ((∑' j : ℕ, shellGagliardoAllConst d s *
          (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ)))) *
            (1 + Real.Gamma ((1 : ℝ) / 2 + 1))) := by
    rw [lintegral_tsum fun j => (hmeasO j).aemeasurable]
    calc ∑' j : ℕ,
          ∫⁻ omega, ENNReal.ofReal (shellGagliardoAllWitness s (n + j) l omega)
            ∂P.toMeasure
        ≤ ∑' j : ℕ, ENNReal.ofReal ((shellGagliardoAllConst d s *
            (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ)))) *
              (1 + Real.Gamma ((1 : ℝ) / 2 + 1))) := ENNReal.tsum_le_tsum hlint
      _ = ENNReal.ofReal (∑' j : ℕ, (shellGagliardoAllConst d s *
            (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ)))) *
              (1 + Real.Gamma ((1 : ℝ) / 2 + 1))) :=
          (ENNReal.ofReal_tsum_of_nonneg
            (fun j => mul_nonneg (hApos j).le hcpos.le)
            (hAsummable.mul_right _)).symm
      _ = ENNReal.ofReal ((∑' j : ℕ, shellGagliardoAllConst d s *
            (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ)))) *
              (1 + Real.Gamma ((1 : ℝ) / 2 + 1))) := by
          rw [tsum_mul_right]
  have hne : (∫⁻ omega, (∑' j : ℕ,
      ENNReal.ofReal (shellGagliardoAllWitness s (n + j) l omega)) ∂P.toMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfinite
  filter_upwards [ae_lt_top hmeasE hne] with omega homega
  have hsummable := ENNReal.summable_toReal homega.ne
  refine hsummable.congr fun j => ?_
  exact ENNReal.toReal_ofReal (shellGagliardoAllWitness_nonneg s (n + j) l omega)

/-! ## Clause (e) -/

/-- **The `Γ₂` tail of the shell series**, at the amplitude `C 3^{-sn}`,
uniformly in the cube scale `l`. -/
theorem isBigO_gammaSigma_gagliardoSupWitness
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) (n l : ℕ) :
    IsBigO P.toMeasure (gammaSigma 2) (gagliardoSupWitness s n l)
      (16384 * (shellGagliardoAllConst d s * (1 - (3 : ℝ) ^ (-s))⁻¹) *
        (3 : ℝ) ^ (-(s * (n : ℝ)))) := by
  have hCpos := shellGagliardoAllConst_pos (d := d) hs hs1
  have hratio : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by
    have h1 : (3 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
    linarith only [h1]
  have hApos : ∀ j : ℕ, 0 ≤ shellGagliardoAllConst d s *
      (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ))) := fun j =>
    (mul_pos hCpos (Real.rpow_pos_of_pos (by norm_num) _)).le
  have hAsummable : Summable fun j : ℕ => shellGagliardoAllConst d s *
      (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ))) :=
    (summable_shellWeight hs n).mul_left _
  have htail : ∀ j : ℕ, IsBigO P.toMeasure (gammaSigma 2)
      (shellGagliardoAllWitness s (n + j) l)
      (shellGagliardoAllConst d s *
        (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ)))) := by
    intro j
    have h := isBigO_gammaSigma_shellGagliardoAllWitness hPrefix hJ3 hs hs1 (n + j) l
    rwa [show (n + j + 1 : ℕ) = (n + 1 + j : ℕ) from by omega] at h
  have hsum := isBigO_gammaSigma_tsum_of_one_le (mu := P.toMeasure)
    (sigma := 2) (by norm_num) hAsummable hApos
    (fun j => measurable_shellGagliardoAllWitness s (n + j) l) htail
  refine hsum.mono_scale ?_
  have hnpow : (0 : ℝ) < (3 : ℝ) ^ (-(s * (n : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hgeom : (∑' j : ℕ, shellGagliardoAllConst d s *
        (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ))))
      ≤ shellGagliardoAllConst d s *
        ((3 : ℝ) ^ (-(s * (n : ℝ))) * (1 - (3 : ℝ) ^ (-s))⁻¹) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_shellWeight_le hs n) hCpos.le
  calc (16384 : ℝ) * ∑' j : ℕ, shellGagliardoAllConst d s *
          (3 : ℝ) ^ (-(s * ((n + 1 + j : ℕ) : ℝ)))
      ≤ 16384 * (shellGagliardoAllConst d s *
          ((3 : ℝ) ^ (-(s * (n : ℝ))) * (1 - (3 : ℝ) ^ (-s))⁻¹)) :=
        mul_le_mul_of_nonneg_left hgeom (by norm_num)
    _ = 16384 * (shellGagliardoAllConst d s * (1 - (3 : ℝ) ^ (-s))⁻¹) *
          (3 : ℝ) ^ (-(s * (n : ℝ))) := by ring

/-- The explicit constant of clause (e): the `Γ₂` triangle prefactor `16384` of
the infinite sum rule times the one-shell constant summed geometrically. It
depends on `d` and `s` only, and in particular not on `l`, `n`, `p` or the
law. -/
def gagliardoSupConst (d : ℕ) (s : ℝ) : ℝ :=
  16384 * (shellGagliardoAllConst d s * (1 - (3 : ℝ) ^ (-s))⁻¹)

/-- **The Gagliardo-supremum clause of the scale estimates**, the Gagliardo
supremum `e.kmn.Hs.osc`,
in its almost-sure form (the printed pointwise form is false, see below): for all
`l n : ℕ` there is a measurable witness with a `Γ₂` tail at the amplitude `C 3^{−sn}` dominating,
almost surely, the supremum over all `M > n` of the Gagliardo seminorm of
`k_M − k_n` on `cu_l`.

The constant `gagliardoSupConst d s` depends on `d` and `s` only, so the
quantifier order — `C` chosen after `s` and `p` and before `P` — is respected;
the `L^p` datum `p` and the laws `J1`, `J2`, `J4` are
carried in the signature for shape compatibility and are not used.

The pointwise form of the same clause is false (see the module docstring of
`IncrementHsClauseB`); the almost-sure form proved here is the correct reading, and the full-measure
event on which the domination holds is the convergence event of the shell
series, `ae_summable_shellGagliardoAllWitness`. -/
theorem gagliardoSupClause_of_shellLaws
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (s p : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hp : (1 : ℝ) ≤ p) (C : ℝ)
    (hC : gagliardoSupConst d s ≤ C) (n l : ℕ) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 2) X (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
      ∀ᵐ omega ∂P.toMeasure,
        (⨆ M : {M : ℕ // n < M},
          cubeEuclideanGagliardoESeminorm (originCube d (l : ℤ)) s 2
            (fun x => finiteShellIncrement omega n M.1 x)) ≤
          ENNReal.ofReal (X omega) := by
  -- The `J1`, `J2` and `J4` laws and the `L^p` datum `p` are
  -- referenced here only so that the signature carries the quantifier
  -- shape of clause (e).
  have _shapeJ1 := hJ1
  have _shapeJ2 := hJ2
  have _shapeJ4 := hJ4
  have _shapeP := hp
  refine ⟨gagliardoSupWitness s n l, measurable_gagliardoSupWitness s n l, ?_, ?_⟩
  · refine (isBigO_gammaSigma_gagliardoSupWitness hPrefix hJ3 hs hs1 n l).mono_scale ?_
    exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by norm_num) _)
  · filter_upwards [ae_summable_shellGagliardoAllWitness hPrefix hJ3 hs hs1 n l]
      with omega hsum
    exact iSup_cubeEuclideanGagliardoESeminorm_le_of_summable hs hs1 n l hsum

end

end SuperdiffusionCLT.Section2.Estimates.Stream
