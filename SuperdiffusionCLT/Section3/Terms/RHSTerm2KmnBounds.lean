/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RBounds
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMoment
public import SuperdiffusionCLT.Section2.Estimates.Stream.DerivativeConcentration
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivLargeCube
public import SuperdiffusionCLT.Section2.Norms.CubeCarrierIdents
public import SuperdiffusionCLT.Section2.Annealed.Integrability

/-!
# The annealed `L̲⁴` bounds of the stream increment and of its gradient

The paper uses a pair of annealed
`L̲⁴` bounds on the stream increment `k_{L'} − k_ℓ` and on its gradient, which it
combines with `e.nablaw.Lt` and the product rule to obtain
`e.RHS.term2.R.bounds`; they enter the proof of that display as
explicit hypotheses `hKa` and `hGa`, and this
module proves them from the stream-increment estimates of Chapter 2.

Value route (`hKa`): the normalized moment display `e.kmn.bounds`, quantified over
every cube, is proved as `isBigOWith_gammaSigma_finiteShellIncrementPthMoment`:
for every cube `Q`,
`⨍_Q ‖(k_{L'} − k_ℓ)‖⁴ ≤ O_{Gamma_{1/2}}(e γ_{1/2} C⁴ (L' − ℓ)²)` at the index
`2/p = 1/2` of `p = 4`; the first-moment conversion at index `1/2` turns the
`Gamma_{1/2}` tail into `E[⨍_Q ‖(k_{L'} − k_ℓ)‖⁴]^{1/4} ≤
γ_{1/2}^{1/2} e^{1/2} C (L' − ℓ)^{1/2}`, with the carrier identification
`cubeLpENorm_eq_rpow_volumeAverage_matrixOperatorNorm`
reading the normalized `L̲⁴` norm of
the density `KN` as the fourth root of the normalized average of the fourth
power of the pointwise operator norm.

Gradient route (`hGa`): the gradient of the increment is the sum of the stored
shell derivatives over `k ∈ (ℓ, L']`, which the derivative control `J3` reads
at scale `3^{-k}` shell by shell.  Stationarity transports each shell's control
to the deterministic translate by the point of evaluation, so every point `x`
carries the one-shell `Gamma₂` tail `‖∇j_k(x)‖ ≤ O_{Gamma₂}(3^{-k})`; the
generalized `Gamma₂` triangle inequality of the CoarseGraining library sums the `L' − ℓ` shells at
the geometric tail scale `3^{-ℓ}` (`sum_Ioc_inv_pow_three_le`).  Raising the
sum to the fourth power moves the index to `Gamma_{1/2}` (the power rule
`e.powerofGammasigma`), the averaging lemma transfers the tail to the
normalized cube average, and the same first-moment conversion gives
`3^ℓ E[⨍_{cu_m} ‖∇(k_{L'} − k_ℓ)‖⁴]^{1/4} ≤ (γ_{1/2}² e γt₂⁴)^{1/4}`, a
scale-free constant: the `3^{-ℓ}` of the triangle step cancels the `3^ℓ` of
the display, with no `√(m − ℓ)` factor.  The canonical density of the gradient
is `GNcan omega x = ‖∑_{k ∈ (ℓ, L']} ∇j_k(x)‖`, the exact induced norm of the
reconstructed derivative (`finiteShellIncrement_hasFDerivAt_sum_shellDeriv`);
the hypothesis `hGNle` of the main theorem pins the free density `GN` to it
pointwise.

Main results: `annealed_four_root_le_of_isBigOWith` (the first-moment
conversion at a general stretched-exponential index, shared by both routes),
`annealed_L4_increment_le` and `annealed_L4_increment_gradient_le` (the two
annealed `L̲⁴` bounds), with the common constant
`max (knValueAnnealedConst d) knGradientAnnealedConst`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The first-moment conversion at a general index -/
/-- **The annealed fourth root from a stretched-exponential tail.**  If the
fourth power of the extended-real density `F` is pointwise at most the `ofReal`
of a nonnegative random variable `Y` whose one-sided tail is
`Y ≤ O_{Γ_σ}(K)`, then the annealed `L⁴` root of `F` is at most the fourth root
of `γ_σ K`.  This is the first-moment conversion of the paper in the
exact shape both routes below use: the `Gamma_{1/2}` tail of the cube average
of the fourth power enters as `IsBigOWith … (gammaSigma (1/2)) … K` with `K`
the realized amplitude, and the fourth root of `gammaMomentConst (1/2) * K` is
the annealed `L̲⁴` root. -/
theorem annealed_four_root_le_of_isBigOWith {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {sigma K : ℝ}
    (hsigma : 0 < sigma) (hK : 0 < K) {Y : Omega → ℝ}
    (hYnn : ∀ omega : Omega, 0 ≤ Y omega) (hYm : AEMeasurable Y mu)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y K)
    {F : Omega → ℝ≥0∞} (hF : ∀ omega : Omega, F omega ^ (4 : ℕ) ≤ ENNReal.ofReal (Y omega)) :
    (∫⁻ omega : Omega, F omega ^ (4 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 4) ≤
      (IndependentSums.gammaMomentConst sigma * K) ^ ((1 : ℝ) / 4) := by
  have hgrowth := IndependentSums.hasGammaMomentGrowthWith_of_isBigOWith_gammaSigma
    (μ := mu) (Y := Y) (K := K) (σ := sigma) hsigma hK hYnn hYm hY
  have hstep := (IndependentSums.hasGammaMomentGrowthWith_iff_of_nonneg
    (μ := mu) (σ := sigma) (M := IndependentSums.gammaMomentConst sigma * K)
    (Y := Y) hYnn).1 hgrowth (le_rfl : (1 : ℝ) ≤ 1)
  obtain ⟨hint, hbound⟩ := hstep
  have hYint : Integrable Y mu := by
    simpa only [Real.rpow_one] using hint
  have hbound1 : ∫ omega : Omega, Y omega ∂mu ≤
      IndependentSums.gammaMomentConst sigma * K := by
    have h3 := hbound
    rw [Real.one_rpow] at h3
    simpa using h3
  have hmono1 : (∫⁻ omega : Omega, F omega ^ (4 : ℕ) ∂mu) ≤
      ∫⁻ omega : Omega, ENNReal.ofReal (Y omega) ∂mu := lintegral_mono hF
  have hmono2 : ∫⁻ omega : Omega, ENNReal.ofReal (Y omega) ∂mu =
      ENNReal.ofReal (∫ omega : Omega, Y omega ∂mu) :=
    (ofReal_integral_eq_lintegral_ofReal hYint
      (Filter.Eventually.of_forall hYnn)).symm
  have hmono : (∫⁻ omega : Omega, F omega ^ (4 : ℕ) ∂mu) ≤
      ENNReal.ofReal (IndependentSums.gammaMomentConst sigma * K) := by
    refine hmono1.trans ?_
    rw [hmono2]
    exact ENNReal.ofReal_le_ofReal hbound1
  refine Real.rpow_le_rpow ENNReal.toReal_nonneg ?_ (by norm_num)
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmono).trans ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (IndependentSums.gammaMomentConst_pos
    hsigma).le hK.le)]

/-! ## Measurability of the cube average of the fourth power -/
/-- The normalized cube average of the `p`-th power of the pointwise increment
size is a measurable observable on the shell sequence: the joint measurability
of the `p`-th power on `Vec d × ShellSeq d` feeds
`measurable_volumeAverage_of_measurable_uncurry`. -/
theorem aemeasurable_volumeAverage_rpow_matrixOperatorNorm_finiteShellIncrement
    (P : ProbabilityMeasure (ShellSeq d)) (n m : ℕ) {p : ℝ} (hp : (0 : ℝ) ≤ p)
    (Q : TriadicCube d) :
    AEMeasurable (fun omega : ShellSeq d =>
      volumeAverage (cubeSet Q) (fun x =>
        matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)) P.toMeasure :=
  (measurable_volumeAverage_of_measurable_uncurry
    (fun (x : Vec d) (omega : ShellSeq d) =>
      matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)
    (measurable_uncurry_matrixOperatorNorm_rpow_finiteShellIncrement n m hp)
    (cubeSet Q)).aemeasurable

/-! ## Elementary exponent identities -/
/-- `(a ^ (1/4)) ^ 4 = a` for a nonnegative real `a`. -/
theorem real_pow_quarter_four (a : ℝ) (ha : 0 ≤ a) :
    (a ^ ((4 : ℝ)⁻¹)) ^ (4 : ℝ) = a := by
  have hstep := Real.rpow_mul ha ((4 : ℝ)⁻¹) 4
  have hex : ((4 : ℝ)⁻¹) * 4 = 1 := by norm_num
  rw [hex, Real.rpow_one] at hstep
  exact hstep.symm

/-! ## The pointwise domination of the fourth power of the normalized norm -/
/-- The `p`-th power of a continuous nonnegative real field is integrable on
the volume restricted to the half-open cube: the continuous field is bounded on
the closed ball around the cube center.  This is the real-valued form of
`integrable_norm_rpow_of_continuous` (`Section2/Norms/CubeCarrierIdents.lean`),
which needs the elementwise norm instance rather than the `ℓ²` operator norm
instance keyed in the carrier identification. -/
theorem integrable_rpow_of_continuous_cube (Q : TriadicCube d) {p : ℝ}
    (hp : (1 : ℝ) ≤ p) (g : Vec d → ℝ) (hgc : Continuous g)
    (hg0 : ∀ x : Vec d, 0 ≤ g x) :
    Integrable (fun x : Vec d => g x ^ p) (normalizedCubeMeasure Q) := by
  have hp0 : (0 : ℝ) ≤ p := zero_le_one.trans hp
  have hgm : AEStronglyMeasurable (fun x : Vec d => g x ^ p)
      (volume.restrict (cubeSet Q)) :=
    (hgc.rpow_const fun _ => Or.inr hp0).aestronglyMeasurable
  have hcomp : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    isCompact_closedBall _ _
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := hcomp.exists_isMaxOn
    ⟨cubeCenter Q, Metric.mem_closedBall_self (cubeRadius_nonneg Q)⟩
    (f := g) hgc.continuousOn
  have hfin : IsFiniteMeasure (volume.restrict (cubeSet Q)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_cubeSet_lt_top Q⟩
  have hint : Integrable (fun x : Vec d => g x ^ p)
      (volume.restrict (cubeSet Q)) :=
    Integrable.mono' (integrable_const (g x₀ ^ p)) hgm (by
      filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hg0 x) p)]
      exact Real.rpow_le_rpow (hg0 x) (hx₀max (cubeSet_subset_closedBall Q hx)) hp0)
  have hctop : (ENNReal.ofReal ((cubeVolume Q)⁻¹)) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hsm : normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • (volume.restrict (cubeSet Q)) := rfl
  rw [hsm]
  exact hint.smul_measure hctop

/-- The carrier step, in real-valued form: the fourth power of the normalized
`L̲⁴` norm of a nonnegative real density dominated pointwise by a continuous
nonnegative real field is at most the `ofReal` of the normalized average of the
fourth power of that field.  The dominating field is kept real-valued so that
no matrix-norm instance enters. -/
theorem cubeLpENorm_four_le_ofReal_volumeAverage (Q : TriadicCube d)
    (f : Vec d → ℝ) (g0 : Vec d → ℝ)
    (hf0 : ∀ x : Vec d, 0 ≤ f x)
    (hfm : MeasureTheory.AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (hfle : ∀ x : Vec d, f x ≤ g0 x)
    (hg0nn : ∀ x : Vec d, 0 ≤ g0 x)
    (hgc : Continuous g0) :
    cubeLpENorm Q 4 f ^ (4 : ℕ) ≤
      ENNReal.ofReal (volumeAverage (cubeSet Q)
        (fun x => g0 x ^ (4 : ℝ))) := by
  have hq : (4 : ℝ≥0∞) = ENNReal.ofReal ((4 : ℝ)) := by norm_num
  have hmono : cubeLpENorm Q 4 f ≤ cubeLpENorm Q 4 g0 :=
    cubeLpENorm_mono_enorm hfm (fun x => by
      have h1 : ‖f x‖ = f x := by rw [Real.norm_eq_abs]; exact abs_of_nonneg (hf0 x)
      have h2 : ‖g0 x‖ = g0 x := by rw [Real.norm_eq_abs]; exact abs_of_nonneg (hg0nn x)
      rw [h1, h2]
      exact hfle x)
  have hcarrier' : cubeLpENorm Q (ENNReal.ofReal ((4 : ℝ))) g0 =
      ENNReal.ofReal ((volumeAverage (cubeSet Q)
        (fun x => g0 x ^ (4 : ℝ))) ^ ((4 : ℝ)⁻¹)) :=
    eLpNorm_eq_ofReal_rpow_volumeAverage Q (by norm_num) g0
      (fun x => g0 x ^ (4 : ℝ)) hgc.aestronglyMeasurable
      (fun x => by
        show ‖g0 x‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (g0 x ^ (4 : ℝ))
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hg0nn x),
          ENNReal.ofReal_rpow_of_nonneg (hg0nn x)
            (by norm_num : (0 : ℝ) ≤ (4 : ℝ))])
      (fun x => Real.rpow_nonneg (hg0nn x) 4)
      (integrable_rpow_of_continuous_cube Q (by norm_num) g0 hgc hg0nn)
  rw [← hq] at hcarrier'
  have hcarrier : cubeLpENorm Q 4 g0 =
      ENNReal.ofReal ((volumeAverage (cubeSet Q)
        (fun x => g0 x ^ (4 : ℝ))) ^ ((4 : ℝ)⁻¹)) := hcarrier'
  have havg0 : 0 ≤ volumeAverage (cubeSet Q)
      (fun x => g0 x ^ (4 : ℝ)) :=
    volumeAverage_cubeSet_nonneg Q
      (fun x => Real.rpow_nonneg (hg0nn x) 4)
  calc cubeLpENorm Q 4 f ^ (4 : ℕ) ≤ (cubeLpENorm Q 4 g0) ^ (4 : ℕ) :=
        pow_le_pow_left' hmono 4
    _ = ENNReal.ofReal (volumeAverage (cubeSet Q)
          (fun x => g0 x ^ (4 : ℝ))) := by
        rw [hcarrier, ← ENNReal.ofReal_pow (Real.rpow_nonneg havg0 ((4 : ℝ)⁻¹)),
          ← Real.rpow_natCast, Nat.cast_ofNat, real_pow_quarter_four _ havg0]

/-! ## The value route: the annealed `L̲⁴` bound of the increment -/
/-- The realized constant of the value route: the fourth root of
`γ_{1/2} · e · (γ_{1/2} · (streamLinftyConst d)⁴)`, i.e.
`γ_{1/2}^{1/2} e^{1/4} streamLinftyConst d`. -/
def knValueAnnealedConst (d : ℕ) : ℝ :=
  IndependentSums.gammaMomentConst ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) *
    (Real.exp 1) ^ ((1 : ℝ) / 4) * streamLinftyConst d

/-- `(a ^ 4) ^ (1/4) = a` for a nonnegative real `a`. -/
theorem real_pow_four_rpow_quarter (a : ℝ) (ha : 0 ≤ a) :
    (a ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = a := by
  have hstep := Real.rpow_mul ha 4 ((1 : ℝ) / 4)
  have hex : (4 : ℝ) * ((1 : ℝ) / 4) = 1 := by norm_num
  rw [hex, Real.rpow_one] at hstep
  exact hstep.symm

/-- **The annealed `L̲⁴` bound of the stream increment**: for
a nonnegative density `KN` dominated pointwise by the operator norm of the
increment `k_m − k_n`, `n < m`, and every cube `Q`,
`(∫⁻ omega, ‖KN omega‖⁴_{L̲⁴(Q)} ∂P).toReal^{1/4} ≤
γ_{1/2}^{1/2} e^{1/4} C (m − n)^{1/2}`.  The route is the normalized moment
display `e.kmn.bounds` (`isBigOWith_gammaSigma_finiteShellIncrementPthMoment`)
at `p = 4`, index `Gamma_{1/2}`, followed by the first-moment conversion
`annealed_four_root_le_of_isBigOWith`. -/
theorem annealed_L4_increment_le (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) {n m : ℕ} (hnm : n < m)
    (f : ShellSeq d → Vec d → ℝ) (hf0 : ∀ (omega : ShellSeq d) (x : Vec d),
      0 ≤ f omega x)
    (hfle : ∀ (omega : ShellSeq d) (x : Vec d),
      f omega x ≤ matrixOperatorNorm (finiteShellIncrement omega n m x))
    (Q : TriadicCube d)
    (hfm : ∀ omega : ShellSeq d,
      MeasureTheory.AEStronglyMeasurable (f omega) (normalizedCubeMeasure Q)) :
    (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4 (f omega) ^ (4 : ℕ)
        ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4) ≤
      knValueAnnealedConst d * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
  have hu : (0 : ℝ) ≤ ((m - n : ℕ) : ℝ) := Nat.cast_nonneg (m - n : ℕ)
  have hnp1 : (1 : ℕ) ≤ m - n := by omega
  have hu1 : (1 : ℝ) ≤ ((m - n : ℕ) : ℝ) := by exact_mod_cast hnp1
  have hsqrtp : 0 < Real.sqrt (((m - n : ℕ) : ℝ)) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hu1)
  have hsqrt0 : 0 ≤ Real.sqrt (((m - n : ℕ) : ℝ)) := hsqrtp.le
  have hS0 : 0 ≤ streamLinftyConst d := (streamLinftyConst_pos hPrefix).le
  have hC0 : 0 ≤ knValueAnnealedConst d := by
    refine mul_nonneg (mul_nonneg ?_ (Real.rpow_nonneg (Real.exp_nonneg 1) _)) ?_
    · exact Real.rpow_nonneg (IndependentSums.gammaMomentConst_pos
        (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).le _
    · exact (streamLinftyConst_pos hPrefix).le
  -- the tail estimate at p = 4
  have hprov := isBigOWith_gammaSigma_finiteShellIncrementPthMoment
    (P := P) hPrefix hJ2 hJ3 hJ4 (p := (4 : ℝ)) (by norm_num) hnm Q
  rw [show ((2 : ℝ) / 4) = ((1 : ℝ) / 2) from by norm_num] at hprov
  -- the pointwise domination of the fourth power
  have hF := fun (omega : ShellSeq d) =>
    cubeLpENorm_four_le_ofReal_volumeAverage Q (f omega)
      (fun x => matrixOperatorNorm (finiteShellIncrement omega n m x))
      (hf0 omega) (hfm omega) (hfle omega) (fun x => matrixOperatorNorm_nonneg _)
      (continuous_matrixOperatorNorm_finiteShellIncrement omega n m)
  have hconv := annealed_four_root_le_of_isBigOWith
    (mu := P.toMeasure) (sigma := ((1 : ℝ) / 2))
    (K := Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
      (streamLinftyConst d * Real.sqrt (((m - n : ℕ) : ℝ))) ^ (4 : ℝ)))
    (by norm_num) (mul_pos (Real.exp_pos 1)
      (mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
        (Real.rpow_pos_of_pos (mul_pos (streamLinftyConst_pos hPrefix) hsqrtp) 4)))
    (Y := fun omega : ShellSeq d => volumeAverage (cubeSet Q) (fun x =>
      matrixOperatorNorm (finiteShellIncrement omega n m x) ^ (4 : ℝ)))
    (fun omega => volumeAverage_cubeSet_nonneg Q
      (fun x => Real.rpow_nonneg (matrixOperatorNorm_nonneg _) 4))
    (aemeasurable_volumeAverage_rpow_matrixOperatorNorm_finiteShellIncrement
      P n m (by norm_num) Q) hprov hF
  -- the fourth root of the amplitude is the realized constant times the scale
  refine hconv.trans ?_
  have hgamma0 : 0 ≤ IndependentSums.gammaMomentConst ((1 : ℝ) / 2) :=
    (IndependentSums.gammaMomentConst_pos (by norm_num)).le
  have hexp0 : 0 ≤ (Real.exp 1) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (Real.exp_nonneg 1) ((1 : ℝ) / 4)
  have hexp4 : ((Real.exp 1) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) = Real.exp 1 := by
    rw [← Real.rpow_mul (Real.exp_nonneg 1) ((1 : ℝ) / 4) 4]
    have hex : ((1 : ℝ) / 4) * 4 = 1 := by norm_num
    rw [hex, Real.rpow_one]
  have hgamma4 : (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2)) ^
      (4 : ℝ) = IndependentSums.gammaMomentConst ((1 : ℝ) / 2) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hgamma0 ((1 : ℝ) / 2) 4]
    have hex : ((1 : ℝ) / 2) * 4 = 2 := by norm_num
    rw [hex]
  have hCk4 : knValueAnnealedConst d ^ (4 : ℝ) =
      IndependentSums.gammaMomentConst ((1 : ℝ) / 2) ^ (2 : ℝ) * Real.exp 1 *
        streamLinftyConst d ^ (4 : ℝ) := by
    have hdef : knValueAnnealedConst d =
        IndependentSums.gammaMomentConst ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) *
          (Real.exp 1) ^ ((1 : ℝ) / 4) * streamLinftyConst d := rfl
    rw [hdef, Real.mul_rpow
      (mul_nonneg (Real.rpow_nonneg hgamma0 ((1 : ℝ) / 2)) hexp0) hS0,
      Real.mul_rpow (Real.rpow_nonneg hgamma0 ((1 : ℝ) / 2)) hexp0, hgamma4, hexp4]
  have hquarter : (((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ^ (4 : ℝ) =
      ((m - n : ℕ) : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hu ((1 : ℝ) / 2) 4]
    have hex : ((1 : ℝ) / 2) * 4 = 2 := by norm_num
    rw [hex]
  have hsq : Real.sqrt (((m - n : ℕ) : ℝ)) = ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.sqrt_eq_rpow _
  have huq : 0 ≤ ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg hu ((1 : ℝ) / 2)
  have hgam2 : IndependentSums.gammaMomentConst ((1 : ℝ) / 2) ^ (2 : ℝ) =
      IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
        IndependentSums.gammaMomentConst ((1 : ℝ) / 2) := by
    rw [Real.rpow_two, pow_two]
  have hamp : IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
      (Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
        (streamLinftyConst d * Real.sqrt (((m - n : ℕ) : ℝ))) ^ (4 : ℝ))) =
      (knValueAnnealedConst d * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ^ (4 : ℝ) := by
    rw [Real.mul_rpow hS0 hsqrt0, hsq, hquarter,
      Real.mul_rpow hC0 huq, hquarter, hCk4, hgam2]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [hamp, real_pow_four_rpow_quarter _ (mul_nonneg hC0 huq)]

/-! ## Measurability of the summed one-shell derivative norms -/
/-- Measurability of one shell's exact induced derivative norm at a fixed
point: the evaluation of the stored derivative at a fixed point is continuous
in the shell and the exact induced norm is continuous. -/
theorem measurable_matrixDerivativeNorm_shellDeriv_coordinate (k : ℕ)
    (x : Vec d) :
    Measurable (fun omega : ShellSeq d ↦
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) :=
  (ShellField.matrixDerivativeNorm_continuous.comp
    (ShellField.continuous_eval_deriv x)).measurable.comp
      (ShellField.measurable_shellCoordinate k)

/-- Continuity in the point of the summed exact induced derivative norms of
the shells of an interval: each summand is continuous. -/
theorem continuous_matrixDerivativeNorm_sum_shellDeriv (omega : ShellSeq d)
    (n m : ℕ) :
    Continuous (fun x : Vec d ↦ ∑ k ∈ Finset.Ioc n m,
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) :=
  continuous_finsetSum _ fun k _ ↦
    ShellField.matrixDerivativeNorm_continuous.comp
      ((ShellField.deriv (omega k)).continuous)

/-- Joint measurability of the summed exact induced derivative norms of the
shells of an interval: the family is continuous in the point for every shell
sequence and measurable in the shell sequence for every point. -/
theorem measurable_uncurry_matrixDerivativeNorm_sum_shellDeriv (n m : ℕ) :
    Measurable (Function.uncurry
      (fun (x : Vec d) (omega : ShellSeq d) ↦
        ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun omega ↦ continuous_matrixDerivativeNorm_sum_shellDeriv omega n m)
    (fun x ↦ Finset.measurable_sum (Finset.Ioc n m) fun k _ ↦
      measurable_matrixDerivativeNorm_shellDeriv_coordinate k x)

/-- The fourth power of the summed exact induced derivative norms is jointly
measurable: `t ↦ t ^ 4` is continuous on the nonnegative reals. -/
theorem measurable_uncurry_rpow_matrixDerivativeNorm_sum_shellDeriv (n m : ℕ) :
    Measurable (Function.uncurry
      (fun (x : Vec d) (omega : ShellSeq d) ↦
        (∑ k ∈ Finset.Ioc n m,
            ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^
          (4 : ℝ))) :=
  (Real.continuous_rpow_const (by norm_num)).measurable.comp
    (measurable_uncurry_matrixDerivativeNorm_sum_shellDeriv n m)

/-! ## The lower bounds of the realized constants -/
/-- The moment constant of the `Γ_σ` class is at least one: it is `2e` times a
maximum that contains the summand `1`. -/
theorem one_le_gammaMomentConst (σ : ℝ) :
    (1 : ℝ) ≤ IndependentSums.gammaMomentConst σ := by
  show (1 : ℝ) ≤
      (2 * Real.exp 1) * max 1 ((2 / (σ * Real.exp 1)) ^ σ⁻¹)
  have h2e : (1 : ℝ) ≤ 2 * Real.exp 1 := by
    linarith only [(Real.one_lt_exp_iff).mpr (by norm_num : (0 : ℝ) < 1)]
  calc (1 : ℝ) = (1 : ℝ) * 1 := by ring
    _ ≤ 2 * Real.exp 1 * 1 := by linarith only [h2e]
    _ ≤ (2 * Real.exp 1) * max 1 ((2 / (σ * Real.exp 1)) ^ σ⁻¹) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _)
        (le_trans zero_le_one h2e)

/-- The triangle constant of the `Γ_σ` class is at least one: it is four times
the twelfth power of `gammaGrowthConst σ`, which is at least `2`. -/
theorem one_le_gammaTriangleConst (σ : ℝ) :
    (1 : ℝ) ≤ IndependentSums.gammaTriangleConst σ := by
  have hg : (1 : ℝ) ≤ IndependentSums.gammaGrowthConst σ :=
    le_trans (by norm_num) (IndependentSums.two_le_gammaGrowthConst σ)
  show (1 : ℝ) ≤ 4 * IndependentSums.gammaGrowthConst σ ^ (12 : ℝ)
  have hstep : ((1 : ℝ) * (1 : ℝ)) ≤
      4 * IndependentSums.gammaGrowthConst σ ^ (12 : ℝ) :=
    mul_le_mul (by norm_num : (1 : ℝ) ≤ 4)
      (le_trans (by norm_num) (Real.one_le_rpow hg (by norm_num)))
      zero_le_one (by norm_num : (0 : ℝ) ≤ 4)
  calc (1 : ℝ) = (1 : ℝ) * (1 : ℝ) := by ring
    _ ≤ 4 * IndependentSums.gammaGrowthConst σ ^ (12 : ℝ) := hstep

/-- The realized constant of the gradient route: the fourth root of
`γ_{1/2} · (e · (γ_{1/2} · γt₂⁴))`, i.e. `γ_{1/2}^{1/2} e^{1/4} γt₂`, where
`γt₂ = gammaTriangleConst 2` is the constant of the `Γ₂` triangle inequality.
It is dimension-free: the `3^{-ℓ}` tail scale of the triangle step cancels the
`3^ℓ` of the display. -/
def knGradientAnnealedConst : ℝ :=
  (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
      (Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
        IndependentSums.gammaTriangleConst 2 ^ (4 : ℝ)))) ^ ((1 : ℝ) / 4)

/-- The realized constant of the gradient route is at least one. -/
theorem one_le_knGradientAnnealedConst : (1 : ℝ) ≤ knGradientAnnealedConst := by
  have hγ : (1 : ℝ) ≤ IndependentSums.gammaMomentConst ((1 : ℝ) / 2) :=
    one_le_gammaMomentConst _
  have hγt : (1 : ℝ) ≤ IndependentSums.gammaTriangleConst 2 :=
    one_le_gammaTriangleConst 2
  have hgt4 : (1 : ℝ) ≤
      IndependentSums.gammaTriangleConst 2 ^ (4 : ℝ) :=
    Real.one_le_rpow hγt (by norm_num)
  have hinner : (1 : ℝ) ≤ IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
      IndependentSums.gammaTriangleConst 2 ^ (4 : ℝ) := by
    simpa using mul_le_mul hγ hgt4 zero_le_one (zero_le_one.trans hγ)
  have hmid : (1 : ℝ) ≤ Real.exp 1 *
      (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
        IndependentSums.gammaTriangleConst 2 ^ (4 : ℝ)) := by
    simpa using mul_le_mul
      (le_of_lt ((Real.one_lt_exp_iff).mpr (by norm_num : (0 : ℝ) < 1))) hinner
      zero_le_one (Real.exp_nonneg 1)
  have hprod : (1 : ℝ) ≤ IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
      (Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
        IndependentSums.gammaTriangleConst 2 ^ (4 : ℝ))) := by
    simpa using mul_le_mul hγ hmid zero_le_one (zero_le_one.trans hγ)
  exact Real.one_le_rpow hprod (by norm_num)

/-! ## The gradient route: the annealed `L̲⁴` bound of the increment gradient -/
/-- **The annealed `L̲⁴` bound of the stream increment gradient**:
for a nonnegative density `GN` dominated pointwise by the summed
one-shell exact induced derivative norms of the increment `k_m − k_n`, `n < m`,
and every cube `Q`,
`3^n · (∫⁻ omega, ‖GN omega‖⁴_{L̲⁴(Q)} ∂P).toReal^{1/4} ≤
(γ_{1/2}² e γt₂⁴)^{1/4} = knGradientAnnealedConst`.  The route is the per-shell
translated `Gamma₂` envelope at the deterministic centre `x`
(`isBigOWith_gammaSigma_translatedShellDerivSupBound`, stationarity only), the
`Γ₂` triangle over the shells of the interval
(`isBigO_finset_sum_of_isBigO_gammaSigma` with the geometric tail
`sum_Ioc_inv_pow_three_le`), the power rule at `p = 4`
(`isBigOWith_gammaSigma_rpow_fwd`, index `2/4 = 1/2`), the averaging lemma
`isBigOWith_gammaSigma_volumeAverage`, and the first-moment conversion
`annealed_four_root_le_of_isBigOWith`; the `3^{-ℓ}` tail scale of the triangle
step cancels the `3^ℓ` of the display. -/
theorem annealed_L4_increment_gradient_le (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {n m : ℕ} (hnm : n < m)
    (g : ShellSeq d → Vec d → ℝ)
    (hg0 : ∀ (omega : ShellSeq d) (x : Vec d), 0 ≤ g omega x)
    (hgle : ∀ (omega : ShellSeq d) (x : Vec d),
      g omega x ≤ ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
    (Q : TriadicCube d)
    (hgm : ∀ omega : ShellSeq d,
      MeasureTheory.AEStronglyMeasurable (g omega) (normalizedCubeMeasure Q)) :
    ((3 : ℝ) ^ ((n : ℕ) : ℝ)) *
      (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4 (g omega) ^ (4 : ℕ)
        ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4) ≤ knGradientAnnealedConst := by
  set A : ℝ := ((3 : ℝ) ^ (n : ℕ))⁻¹ with hAdef
  have hApos : (0 : ℝ) < A := by
    rw [hAdef]
    exact inv_pos.mpr (pow_pos (by norm_num) n)
  have hA0 : (0 : ℝ) ≤ A := hApos.le
  have hgt0 : (0 : ℝ) ≤ IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos.le
  have hgamma0 : (0 : ℝ) ≤ IndependentSums.gammaMomentConst ((1 : ℝ) / 2) :=
    (IndependentSums.gammaMomentConst_pos (by norm_num)).le
  -- the pointwise sum of one-shell norms is nonnegative
  have hsumnn : ∀ (omega : ShellSeq d) (x : Vec d),
      0 ≤ ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x) :=
    fun omega x => Finset.sum_nonneg fun k _ =>
      ShellField.matrixDerivativeNorm_nonneg _
  -- every point carries the one-shell `Gamma₂` tail at the centre `x` itself
  have hterm : ∀ (k : ℕ) (x : Vec d),
      IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
        (((3 : ℝ) ^ k)⁻¹) := by
    intro k x
    have hx : x - x ∈ cubeSet (originCube d ((k : ℕ) : ℤ)) := by
      rw [sub_self]
      exact openCubeSet_subset_cubeSet _ (zero_mem_openCubeSet_originCube k)
    exact (isBigOWith_gammaSigma_translatedShellDerivSupBound hPrefix hJ3 k x).of_le
      (fun omega ↦ matrixDerivativeNorm_deriv_le_translatedShellDerivSupBound
        omega k x hx)
  -- the `Gamma₂` triangle over the shells, at the geometric tail scale
  have hsum : ∀ x : Vec d,
      IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
        (IndependentSums.gammaTriangleConst 2 * A) := by
    intro x
    have hbigO : ∀ k ∈ Finset.Ioc n m,
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
          (fun omega : ShellSeq d ↦
            ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
          (((3 : ℝ) ^ k)⁻¹) :=
      fun k _ ↦ (isBigOWith_iff_isBigO_of_nonneg
        (fun omega ↦ ShellField.matrixDerivativeNorm_nonneg _)).mp (hterm k x)
    have htriangle := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := P.toMeasure)
      (s := Finset.Ioc n m)
      (X := fun (k : ℕ) (omega : ShellSeq d) ↦
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
      (a := fun k : ℕ ↦ ((3 : ℝ) ^ k)⁻¹) (σ := 2) (hσ := by norm_num)
      (hs := Finset.nonempty_Ioc.mpr hnm)
      (ha := fun k _ ↦ inv_pos.mpr (pow_pos (by norm_num) k)) (hX := hbigO)
      (hXm := fun k _ ↦ measurable_matrixDerivativeNorm_shellDeriv_coordinate k x)
    have hwith : IndependentSums.IsBigOWith P.toMeasure
        (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
        (IndependentSums.gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc n m,
          ((3 : ℝ) ^ k)⁻¹) :=
      (isBigOWith_iff_isBigO_of_nonneg (fun omega ↦ hsumnn omega x)).mpr htriangle
    refine hwith.mono_scale (mul_le_mul_of_nonneg_left
      (sum_Ioc_inv_pow_three_le hnm.le) hgt0)
  -- the power rule: the fourth power moves the index to `Gamma_{1/2}`
  have hpow : ∀ x : Vec d,
      IndependentSums.IsBigOWith P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 2))
        (fun omega : ShellSeq d ↦
          (∑ k ∈ Finset.Ioc n m,
            ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^
            (4 : ℝ))
        ((IndependentSums.gammaTriangleConst 2 * A) ^ (4 : ℝ)) := by
    intro x
    have h := isBigOWith_gammaSigma_rpow_fwd
      (mu := P.toMeasure)
      (X := fun omega : ShellSeq d ↦ ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
      (K := IndependentSums.gammaTriangleConst 2 * A) (σ := 2) (p := (4 : ℝ))
      (hp := by norm_num) (hK := by positivity)
      (hX := fun omega ↦ hsumnn omega x) (hXK := hsum x)
    rwa [show ((2 : ℝ) / 4) = ((1 : ℝ) / 2) from by norm_num] at h
  -- the averaging step over the cube
  have hU0 : volume (cubeSet Q) ≠ 0 := by
    have hvolpos : (0 : ℝ) < (volume (cubeSet Q)).toReal := by
      rw [volume_cubeSet_toReal]
      exact cubeVolume_pos Q
    intro h
    rw [h] at hvolpos
    simp at hvolpos
  have hUtop : volume (cubeSet Q) ≠ ⊤ :=
    ne_of_lt (volume_cubeSet_lt_top Q)
  have havg := isBigOWith_gammaSigma_volumeAverage
    (mu := P.toMeasure) (U := cubeSet Q)
    (Y := fun (x : Vec d) (omega : ShellSeq d) ↦
      (∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^
        (4 : ℝ))
    (sigma := ((1 : ℝ) / 2))
    (A := (IndependentSums.gammaTriangleConst 2 * A) ^ (4 : ℝ))
    (by norm_num)
    (Real.rpow_pos_of_pos
      (mul_pos IndependentSums.gammaTriangleConst_pos hApos) 4)
    hU0 hUtop (fun x omega ↦ Real.rpow_nonneg (hsumnn omega x) 4)
    (measurable_uncurry_rpow_matrixDerivativeNorm_sum_shellDeriv n m) hpow
  -- the first-moment conversion
  have hmeas : AEMeasurable (fun omega : ShellSeq d =>
      volumeAverage (cubeSet Q) (fun x ↦
        (∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^
          (4 : ℝ))) P.toMeasure :=
    (measurable_volumeAverage_of_measurable_uncurry _
      (measurable_uncurry_rpow_matrixDerivativeNorm_sum_shellDeriv n m)
      (cubeSet Q)).aemeasurable
  have hF : ∀ omega : ShellSeq d,
      cubeLpENorm Q 4 (g omega) ^ (4 : ℕ) ≤
        ENNReal.ofReal (volumeAverage (cubeSet Q) (fun x ↦
          (∑ k ∈ Finset.Ioc n m,
            ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^
            (4 : ℝ))) :=
    fun omega ↦ cubeLpENorm_four_le_ofReal_volumeAverage Q (g omega)
      (fun x ↦ ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
      (hg0 omega) (hgm omega) (hgle omega) (fun x ↦ hsumnn omega x)
      (continuous_matrixDerivativeNorm_sum_shellDeriv omega n m)
  have hconv := annealed_four_root_le_of_isBigOWith
    (mu := P.toMeasure) (sigma := ((1 : ℝ) / 2))
    (K := Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
      (IndependentSums.gammaTriangleConst 2 * A) ^ (4 : ℝ)))
    (by norm_num)
    (mul_pos (Real.exp_pos 1)
      (mul_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
        (Real.rpow_pos_of_pos
          (mul_pos IndependentSums.gammaTriangleConst_pos hApos) 4)))
    (Y := fun omega : ShellSeq d => volumeAverage (cubeSet Q) (fun x ↦
      (∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^
        (4 : ℝ)))
    (fun omega => volumeAverage_cubeSet_nonneg Q
      (fun x ↦ Real.rpow_nonneg (hsumnn omega x) 4)) hmeas havg hF
  -- the amplitude root is the realized constant times the tail scale
  have hamp : (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
      (Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
        (IndependentSums.gammaTriangleConst 2 * A) ^ (4 : ℝ)))) ^
      ((1 : ℝ) / 4) = knGradientAnnealedConst * A := by
    have hdef : knGradientAnnealedConst = (IndependentSums.gammaMomentConst
        ((1 : ℝ) / 2) * (Real.exp 1 * (IndependentSums.gammaMomentConst
          ((1 : ℝ) / 2) * IndependentSums.gammaTriangleConst 2 ^ (4 : ℝ)))) ^
      ((1 : ℝ) / 4) := rfl
    have hsplit : (IndependentSums.gammaTriangleConst 2 * A) ^ (4 : ℝ) =
        IndependentSums.gammaTriangleConst 2 ^ (4 : ℝ) * A ^ (4 : ℝ) :=
      Real.mul_rpow hgt0 hA0
    have hgroup : IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
        (Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
          (IndependentSums.gammaTriangleConst 2 ^ (4 : ℝ) * A ^ (4 : ℝ)))) =
      (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) * (Real.exp 1 *
        (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
          IndependentSums.gammaTriangleConst 2 ^ (4 : ℝ)))) * A ^ (4 : ℝ) := by
      ring
    have hquarterA : (A ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = A :=
      real_pow_four_rpow_quarter _ hA0
    calc (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) * (Real.exp 1 *
          (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
            (IndependentSums.gammaTriangleConst 2 * A) ^ (4 : ℝ)))) ^
        ((1 : ℝ) / 4)
        = ((IndependentSums.gammaMomentConst ((1 : ℝ) / 2) * (Real.exp 1 *
            (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
              IndependentSums.gammaTriangleConst 2 ^ (4 : ℝ)))) *
          A ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by rw [hsplit, hgroup]
      _ = knGradientAnnealedConst * A := by
          rw [hdef, Real.mul_rpow
            (mul_nonneg hgamma0 (mul_nonneg (Real.exp_nonneg 1)
              (mul_nonneg hgamma0 (Real.rpow_nonneg hgt0 4))))
            (Real.rpow_nonneg hA0 4), hquarterA]
  have hroot : (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4 (g omega) ^ (4 : ℕ)
      ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4) ≤ knGradientAnnealedConst * A :=
    hconv.trans (le_of_eq hamp)
  have hthree : ((3 : ℝ) ^ ((n : ℕ) : ℝ)) * (knGradientAnnealedConst * A) =
      knGradientAnnealedConst := by
    rw [Real.rpow_natCast, hAdef]
    calc ((3 : ℝ) ^ (n : ℕ)) *
        (knGradientAnnealedConst * ((3 : ℝ) ^ (n : ℕ))⁻¹)
        = (((3 : ℝ) ^ (n : ℕ)) * ((3 : ℝ) ^ (n : ℕ))⁻¹) *
          knGradientAnnealedConst := by
          rw [mul_comm knGradientAnnealedConst (((3 : ℝ) ^ (n : ℕ))⁻¹),
            ← mul_assoc]
      _ = knGradientAnnealedConst := by
          rw [mul_inv_cancel₀ (pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0)),
            one_mul]
  calc ((3 : ℝ) ^ ((n : ℕ) : ℝ)) *
      (∫⁻ omega : ShellSeq d, cubeLpENorm Q 4 (g omega) ^ (4 : ℕ)
        ∂P.toMeasure).toReal ^ ((1 : ℝ) / 4)
      ≤ ((3 : ℝ) ^ ((n : ℕ) : ℝ)) * (knGradientAnnealedConst * A) :=
        mul_le_mul_of_nonneg_left hroot
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ (3 : ℝ)) _)
    _ = knGradientAnnealedConst := hthree

end