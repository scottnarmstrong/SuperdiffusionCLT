/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMoment
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependenceRestriction

/-!
# Sub-cube moments of the finite increment are restriction-lane local

The improvement of the normalized `p`-th moment display on cubes above the
cutoff scale (display `e.kl.bounds.large`)
splits the average over `cu_l` into the averages over the
`3^{d(l-m)}` sub-cubes of scale `m` and applies the concentration inequality of
`p.concentration` to the centred sub-cube variables. That
step needs two deterministic inputs, both supplied here.

The first is the exact partition identity: the normalized average of an
integrable function over a triadic cube is the plain average of its normalized
averages over the descendants at any depth, because the half-open cube
realizations tile exactly and all descendants at one depth have one volume.

The second is locality. The paper reads `k_m - k_n` as a field with range
of dependence `sqrt d 3^m`, and the concentration step needs the
sub-cube moment `⨍_R |k_m - k_n|^p` to be an observable of the shells
`0, ..., m` read only on `R`. The restriction-lane assumption
`ShellLawJ1Restriction` supplies independence for the pointwise-restriction sigma-field
`ShellField.shellRestrictionSigma`, in which point evaluations inside the
observation set are measurable; the sub-cube moment is an *integral* of a
nonlinear function of those point values, so the passage from the point
evaluations to the integral is a genuine step. It is carried out here through
the Riemann sums over the descendant centres: for a continuous integrand these
converge to the normalized average, every centre of a descendant of `R` lies in
`R`, and a limit superior of measurable functions is measurable.

The resulting lane is the join `blockLane m` of the shell lanes of the shells
`0, ..., m`, exactly the lane in which
`SuperdiffusionCLT.Section3.HighContrast.indep_blockLane` turns the
assumptions into independence.

## Main definitions

* `blockCubeLane`: the restriction lane of a cube, joined over the shells
  `0, ..., m`.
* `finiteShellIncrementCubePthMoment`: the normalized `p`-th moment of the
  pointwise increment size over a triadic cube.

## Main results

* `volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants`: the partition
  identity.
* `tendsto_descendantCenterAverage`: the Riemann sums over the descendant
  centres converge to the normalized average.
* `measurable_blockCubeLane_finiteShellIncrementCubePthMoment`: the sub-cube
  moment is an observable of the lane of its own cube.
* `iIndepFun_finiteShellIncrementCubePthMoment`: mutual independence of the sub-cube moments
  over a pairwise separated finite family of cubes, from `ShellLawJ1Restriction` and `ShellLawJ2`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.HighContrast

noncomputable section

variable {d : ℕ}

/-! ## Elementary cube facts -/

/-- The centre of a triadic cube lies in its half-open realization. -/
theorem cubeCenter_mem_cubeSet (Q : TriadicCube d) : cubeCenter Q ∈ cubeSet Q := by
  intro i
  have hs : 0 < cubeScaleFactor Q := by
    simpa only [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale
  refine ⟨?_, ?_⟩
  · show ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤
      (Q.index i : ℝ) * cubeScaleFactor Q
    nlinarith only [hs]
  · show (Q.index i : ℝ) * cubeScaleFactor Q <
      ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q
    nlinarith only [hs]

/-- The Lebesgue measure of the half-open realization of a triadic cube is
nonzero. -/
theorem volume_cubeSet_ne_zero (Q : TriadicCube d) :
    volume (cubeSet Q) ≠ 0 := by
  intro h
  have hpos := volume_cubeSet_toReal_pos Q
  rw [h] at hpos
  simp only [ENNReal.toReal_zero, lt_self_iff_false] at hpos

/-- A continuous function is integrable on the half-open realization of a
triadic cube: the cube is bounded, so the function is integrable on its compact
closure. -/
theorem integrableOn_cubeSet_of_continuous (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : Continuous g) : IntegrableOn g (cubeSet Q) volume :=
  (hg.locallyIntegrable.integrableOn_isCompact
      (isBounded_cubeSet Q).isCompact_closure).mono_set subset_closure

/-- The radius of a depth-`i` descendant of `Q`. -/
theorem cubeRadius_of_mem_descendantsAtDepth {Q R : TriadicCube d} {i : ℕ}
    (hR : R ∈ descendantsAtDepth Q i) :
    cubeRadius R = (1 / 2 : ℝ) * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ i)⁻¹) := by
  have hscale : R.scale = Q.scale - i := scale_eq_sub_of_mem_descendantsAtDepth hR
  rw [cubeRadius, cubeScaleFactor, hscale, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0),
    zpow_natCast]
  ring

/-- A normalized average is bounded by any pointwise bound of the integrand on
the averaging set. -/
theorem abs_volumeAverage_le {U : Set (Vec d)} (hUne : volume U ≠ 0)
    (hUtop : volume U ≠ ⊤) {f : Vec d → ℝ} {C : ℝ}
    (hbound : ∀ x ∈ U, |f x| ≤ C) : |volumeAverage U f| ≤ C := by
  have hvpos : 0 < (volume U).toReal := ENNReal.toReal_pos hUne hUtop
  have hint : |∫ x in U, f x| ≤ C * (volume U).toReal := by
    have h1 : ‖∫ x in U, f x‖ ≤ C * (volume : Measure (Vec d)).real U := by
      refine norm_setIntegral_le_of_norm_le_const (lt_of_le_of_ne le_top hUtop) ?_
      intro x hx
      rw [Real.norm_eq_abs]
      exact hbound x hx
    rwa [Real.norm_eq_abs, measureReal_def] at h1
  rw [volumeAverage, abs_mul, abs_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg),
    inv_mul_le_iff₀ hvpos]
  exact hint.trans_eq (by ring)

/-- Subtracting a constant from the integrand subtracts it from the normalized
average over a triadic cube. -/
theorem volumeAverage_cubeSet_sub_const (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : IntegrableOn g (cubeSet Q) volume) (a : ℝ) :
    volumeAverage (cubeSet Q) (fun x ↦ g x - a) =
      volumeAverage (cubeSet Q) g - a := by
  have hvpos : 0 < (volume (cubeSet Q)).toReal := by
    rw [volume_cubeSet_toReal]; exact cubeVolume_pos Q
  have hconst : IntegrableOn (fun _ : Vec d ↦ a) (cubeSet Q) volume :=
    integrableOn_const (volume_cubeSet_lt_top Q).ne
  rw [volumeAverage, volumeAverage, integral_sub hg hconst, setIntegral_const,
    smul_eq_mul, mul_sub, measureReal_def, ← mul_assoc,
    inv_mul_cancel₀ hvpos.ne', one_mul]

/-! ## The exact partition identity -/

/-- **The descendant partition of a normalized cube average.** The half-open
realizations of the depth-`j` descendants of `Q` tile `cubeSet Q` exactly and
all have one volume, so the normalized average over `Q` is the plain average of
the normalized averages over the descendants. -/
theorem volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants
    (Q : TriadicCube d) (j : ℕ) {f : Vec d → ℝ}
    (hf : ∀ R ∈ descendantsAtDepth Q j, IntegrableOn f (cubeSet R) volume) :
    volumeAverage (cubeSet Q) f =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, volumeAverage (cubeSet R) f := by
  classical
  obtain ⟨R0, hR0⟩ := descendantsAtDepth_nonempty Q j
  have hvolQ : cubeVolume Q = ((descendantsAtDepth Q j).card : ℝ) * cubeVolume R0 :=
    cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hR0
  have hint : ∫ x in cubeSet Q, f x =
      ∑ R ∈ descendantsAtDepth Q j, ∫ x in cubeSet R, f x := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    exact integral_biUnion_finset _ (fun R _ ↦ measurableSet_cubeSet R)
      (pairwiseDisjoint_descendantsAtDepth Q j) hf
  have hsum : ∑ R ∈ descendantsAtDepth Q j, ∫ x in cubeSet R, f x =
      cubeVolume R0 * ∑ R ∈ descendantsAtDepth Q j, volumeAverage (cubeSet R) f := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun R hR ↦ ?_
    have hvR : cubeVolume R = cubeVolume R0 :=
      cubeVolume_eq_of_mem_descendantsAtDepth hR hR0
    rw [volumeAverage, volume_cubeSet_toReal, hvR, ← mul_assoc,
      mul_inv_cancel₀ (cubeVolume_pos R0).ne', one_mul]
  rw [volumeAverage, volume_cubeSet_toReal, hint, hsum, hvolQ, mul_inv, mul_assoc,
    ← mul_assoc (cubeVolume R0)⁻¹, inv_mul_cancel₀ (cubeVolume_pos R0).ne', one_mul]

/-! ## Riemann sums over the descendant centres -/

/-- The Riemann sum of `g` over the centres of the depth-`i` descendants of a
triadic cube. -/
def descendantCenterAverage (Q : TriadicCube d) (i : ℕ) (g : Vec d → ℝ) : ℝ :=
  ((descendantsAtDepth Q i).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth Q i, g (cubeCenter R)

/-- **The Riemann sums over the descendant centres converge.** For a continuous
integrand the plain average of the values at the centres of the depth-`i`
descendants converges to the normalized average over the cube, because the
descendants shrink and the integrand is uniformly continuous on the compact
closure of the cube. -/
theorem tendsto_descendantCenterAverage (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : Continuous g) :
    Filter.Tendsto (fun i : ℕ ↦ descendantCenterAverage Q i g) Filter.atTop
      (nhds (volumeAverage (cubeSet Q) g)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hKc : IsCompact (closure (cubeSet Q)) := (isBounded_cubeSet Q).isCompact_closure
  have huc : UniformContinuousOn g (closure (cubeSet Q)) :=
    hKc.uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨delta, hdelta, hdg⟩ := huc (eps / 2) (half_pos heps)
  have hc : 0 < (1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hdelta hc)
    (by norm_num : (1 : ℝ) / 3 < 1)
  refine ⟨N, fun i hi ↦ ?_⟩
  have hsmall : (1 / 2 : ℝ) * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ i)⁻¹) < delta := by
    have hmono : ((1 : ℝ) / 3) ^ i ≤ ((1 : ℝ) / 3) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
    have hstep : ((1 : ℝ) / 3) ^ i < delta / ((1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale) :=
      lt_of_le_of_lt hmono hN
    have hrw : (1 / 2 : ℝ) * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ i)⁻¹) =
        ((1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale) * ((1 : ℝ) / 3) ^ i := by
      rw [div_pow, one_pow]
      ring
    rw [hrw]
    calc ((1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale) * ((1 : ℝ) / 3) ^ i
        < ((1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale) *
            (delta / ((1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale)) :=
          mul_lt_mul_of_pos_left hstep hc
      _ = delta := by field_simp
  have hcardpos : 0 < ((descendantsAtDepth Q i).card : ℝ) := by
    exact_mod_cast (descendantsAtDepth_nonempty Q i).card_pos
  have hterm : ∀ R ∈ descendantsAtDepth Q i,
      |g (cubeCenter R) - volumeAverage (cubeSet R) g| ≤ eps / 2 := by
    intro R hR
    have hsub : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
    have hcR : cubeCenter R ∈ cubeSet R := cubeCenter_mem_cubeSet R
    have hbound : ∀ x ∈ cubeSet R, |g x - g (cubeCenter R)| ≤ eps / 2 := by
      intro x hx
      have hxK : x ∈ closure (cubeSet Q) := subset_closure (hsub hx)
      have hcK : cubeCenter R ∈ closure (cubeSet Q) := subset_closure (hsub hcR)
      have hdist : dist x (cubeCenter R) < delta := by
        have h1 : dist x (cubeCenter R) ≤ cubeRadius R := by
          simpa only [Metric.mem_closedBall] using cubeSet_subset_closedBall R hx
        rw [cubeRadius_of_mem_descendantsAtDepth hR] at h1
        exact lt_of_le_of_lt h1 hsmall
      have hlt := hdg x hxK (cubeCenter R) hcK hdist
      rw [Real.dist_eq] at hlt
      exact hlt.le
    have hav := abs_volumeAverage_le (U := cubeSet R) (volume_cubeSet_ne_zero R)
      (volume_cubeSet_lt_top R).ne (f := fun x ↦ g x - g (cubeCenter R))
      (C := eps / 2) hbound
    rw [volumeAverage_cubeSet_sub_const R
      (integrableOn_cubeSet_of_continuous R hg)] at hav
    rw [abs_sub_comm]
    exact hav
  have hdec : volumeAverage (cubeSet Q) g =
      ((descendantsAtDepth Q i).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q i, volumeAverage (cubeSet R) g :=
    volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants Q i
      (fun R _ ↦ integrableOn_cubeSet_of_continuous R hg)
  rw [Real.dist_eq, descendantCenterAverage, hdec, ← mul_sub,
    ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hcardpos.le)]
  have hsum : |∑ R ∈ descendantsAtDepth Q i,
      (g (cubeCenter R) - volumeAverage (cubeSet R) g)| ≤
      ((descendantsAtDepth Q i).card : ℝ) * (eps / 2) := by
    calc |∑ R ∈ descendantsAtDepth Q i,
            (g (cubeCenter R) - volumeAverage (cubeSet R) g)|
        ≤ ∑ R ∈ descendantsAtDepth Q i,
            |g (cubeCenter R) - volumeAverage (cubeSet R) g| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _R ∈ descendantsAtDepth Q i, (eps / 2) := Finset.sum_le_sum hterm
      _ = ((descendantsAtDepth Q i).card : ℝ) * (eps / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc ((descendantsAtDepth Q i).card : ℝ)⁻¹ *
        |∑ R ∈ descendantsAtDepth Q i,
          (g (cubeCenter R) - volumeAverage (cubeSet R) g)|
      ≤ ((descendantsAtDepth Q i).card : ℝ)⁻¹ *
          (((descendantsAtDepth Q i).card : ℝ) * (eps / 2)) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hcardpos.le)
    _ = eps / 2 := by rw [← mul_assoc, inv_mul_cancel₀ hcardpos.ne', one_mul]
    _ < eps := by linarith only [heps]


/-! ## The restriction lane of a cube -/

/-- The pointwise-restriction lane of a cube, joined over the shells
`0, ..., m`: the information that the infrared cutoff at scale `3 ^ m` can read
on the cube. -/
@[instance_reducible]
def blockCubeLane (m : ℕ) (Q : TriadicCube d) : MeasurableSpace (ShellSeq d) :=
  blockLane m
    (ShellField.shellRestrictionSigma (cubeSet Q) (measurableSet_cubeSet Q))

/-- Point evaluation inside the observation set is a restriction-lane
observable of a shell field. -/
theorem measurable_shellRestrictionSigma_apply_entry {U : Set (Vec d)}
    (hU : MeasurableSet U) {x : Vec d} (hx : x ∈ U) (i k : Fin d) :
    Measurable[ShellField.shellRestrictionSigma U hU]
      (fun jf : ShellField d ↦ jf x i k) := by
  have hfactor : (fun jf : ShellField d ↦ jf x i k) =
      fun jf : ShellField d ↦
        (restrictReg U hU (ShellField.forgetShell jf)) x i k := by
    funext jf
    rw [restrictReg_apply_entry, Set.indicator_of_mem hx,
      ShellField.forgetShell_apply]
  rw [hfactor]
  exact (measurable_apply_entry x i k).comp (measurable_restrictReg_forgetShell U hU)

/-- Point evaluation inside a cube, read through a shell no coarser than the
cutoff scale, is an observable of the cube's lane. -/
theorem measurable_blockCubeLane_apply_entry {m : ℕ} (Q : TriadicCube d) {k : ℕ}
    (hk : k ≤ m) {x : Vec d} (hx : x ∈ cubeSet Q) (i j : Fin d) :
    Measurable[blockCubeLane m Q] (fun omega : ShellSeq d ↦ (omega k) x i j) := by
  have h1 := measurable_shellRestrictionSigma_apply_entry
    (measurableSet_cubeSet Q) hx i j
  have hcoord : @Measurable (ShellSeq d) (ShellField d)
      (shellLane k
        (ShellField.shellRestrictionSigma (cubeSet Q) (measurableSet_cubeSet Q)))
      (ShellField.shellRestrictionSigma (cubeSet Q) (measurableSet_cubeSet Q))
      (fun omega : ShellSeq d ↦ omega k) := Measurable.of_comap_le le_rfl
  exact (h1.comp hcoord).mono (shellLane_le_blockLane hk _) le_rfl

/-- The increment at a point of a cube is an observable of the cube's lane. -/
theorem measurable_blockCubeLane_finiteShellIncrement {n m : ℕ}
    (Q : TriadicCube d) {x : Vec d} (hx : x ∈ cubeSet Q) :
    Measurable[blockCubeLane m Q]
      (fun omega : ShellSeq d ↦ finiteShellIncrement omega n m x) := by
  refine @measurable_matrix_of_entries d (ShellSeq d) (blockCubeLane m Q) _ ?_
  intro i j
  have hentry : (fun omega : ShellSeq d ↦ finiteShellIncrement omega n m x i j) =
      fun omega : ShellSeq d ↦ ∑ l ∈ Finset.Ioc n m, (omega l) x i j := by
    funext omega
    exact finiteShellIncrement_apply_entry omega n m x i j
  rw [hentry]
  exact Finset.measurable_sum _ fun l hl ↦
    measurable_blockCubeLane_apply_entry Q (Finset.mem_Ioc.mp hl).2 hx i j

/-! ## The sub-cube moment -/

/-- The normalized `p`-th moment of the pointwise increment size over a triadic
cube: the manuscript's `⨍_R |k_m - k_n|^p`. -/
def finiteShellIncrementCubePthMoment (n m : ℕ) (p : ℝ) (Q : TriadicCube d)
    (omega : ShellSeq d) : ℝ :=
  volumeAverage (cubeSet Q)
    (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)

theorem finiteShellIncrementCubePthMoment_nonneg (n m : ℕ) (p : ℝ)
    (Q : TriadicCube d) (omega : ShellSeq d) :
    0 ≤ finiteShellIncrementCubePthMoment n m p Q omega := by
  rw [finiteShellIncrementCubePthMoment, volumeAverage]
  exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
    (integral_nonneg fun x ↦ Real.rpow_nonneg (matrixOperatorNorm_nonneg _) p)

/-- **The sub-cube moment is an observable of the cube's lane.** The integrand
is continuous in the spatial variable, so the Riemann sums over the centres of
the descendants of the cube converge to the moment; every such centre lies in
the cube, so each Riemann sum is a lane observable by
`measurable_blockCubeLane_finiteShellIncrement`, and a limit superior of lane
observables is a lane observable. -/
theorem measurable_blockCubeLane_finiteShellIncrementCubePthMoment
    (n m : ℕ) {p : ℝ} (hp : (0 : ℝ) ≤ p) (Q : TriadicCube d) :
    Measurable[blockCubeLane m Q] (finiteShellIncrementCubePthMoment n m p Q) := by
  classical
  have hstep : ∀ i : ℕ, Measurable[blockCubeLane m Q]
      (fun omega : ShellSeq d ↦ descendantCenterAverage Q i
        (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p)) := by
    intro i
    refine Measurable.const_mul (Finset.measurable_sum _ fun R hR ↦ ?_) _
    have hcenter : cubeCenter R ∈ cubeSet Q :=
      cubeSet_subset_of_mem_descendantsAtDepth hR (cubeCenter_mem_cubeSet R)
    exact ((Real.continuous_rpow_const hp).measurable.comp
      (ShellField.continuous_matrixOperatorNorm.measurable.comp
        (measurable_blockCubeLane_finiteShellIncrement Q hcenter)))
  have hlim : finiteShellIncrementCubePthMoment n m p Q =
      fun omega : ShellSeq d ↦ Filter.limsup
        (fun i : ℕ ↦ descendantCenterAverage Q i
          (fun x ↦ matrixOperatorNorm (finiteShellIncrement omega n m x) ^ p))
        Filter.atTop := by
    funext omega
    refine (Filter.Tendsto.limsup_eq ?_).symm
    exact tendsto_descendantCenterAverage Q
      ((continuous_matrixOperatorNorm_finiteShellIncrement omega n m).rpow_const
        fun _ ↦ Or.inr hp)
  rw [hlim]
  exact Measurable.limsup hstep

/-! ## Independence of the lanes of separated cubes -/

/-- The pointwise-restriction lane grows with its observation set. -/
theorem shellRestrictionSigma_mono {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hV : MeasurableSet V) (hUV : U ⊆ V) :
    ShellField.shellRestrictionSigma U hU ≤ ShellField.shellRestrictionSigma V hV := by
  have hcomap : ∀ (W : Set (Vec d)) (hW : MeasurableSet W),
      ShellField.shellRestrictionSigma W hW =
        MeasurableSpace.comap (ShellField.forgetShell (d := d))
          (RestrictionSigmaR W hW) := by
    intro W hW
    rw [ShellField.shellRestrictionSigma, RestrictionSigmaR,
      MeasurableSpace.comap_comp]
    rfl
  rw [hcomap U hU, hcomap V hV]
  exact MeasurableSpace.comap_mono (RestrictionSigmaR_mono hU hV hUV)

/-- The joined lane grows with its observation set. -/
theorem blockLane_shellRestrictionSigma_mono {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V) (m : ℕ) :
    blockLane m (ShellField.shellRestrictionSigma U hU) ≤
      blockLane m (ShellField.shellRestrictionSigma V hV) :=
  iSup₂_mono fun _ _ ↦ MeasurableSpace.comap_mono (shellRestrictionSigma_mono hU hV hUV)

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- **Mutual independence of the joined restriction lanes of a pairwise
separated finite family.** The restriction-lane range of dependence
`ShellLawJ1Restriction` and the shell independence `ShellLawJ2` give the pairwise
statement `indep_blockLane`; the family form follows by reading one member
against the union of the remaining ones, which is separated from it and whose
lane contains theirs. -/
theorem iIndep_blockLane_shellRestrictionSigma {iota : Type*}
    (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (m : ℕ)
    {U : iota → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j ↦ ShellField.AreShellSeparated m (U i) (U j)) :
    iIndep (fun i ↦ blockLane m (ShellField.shellRestrictionSigma (U i) (hU i)))
      P.toMeasure := by
  classical
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hUnion : MeasurableSet (⋃ j ∈ s, U j) :=
        Finset.measurableSet_biUnion _ fun j _ ↦ hU j
      have hsep_union : ShellField.AreShellSeparated m (U i) (⋃ j ∈ s, U j) := by
        refine ShellField.areShellSeparated_biUnion_right (U := U i) (V := U) ?_
        intro j hj
        exact hsep (by intro hij; exact hi (hij ▸ hj))
      have hs_meas : MeasurableSet[blockLane m
          (ShellField.shellRestrictionSigma (⋃ j ∈ s, U j) hUnion)] (⋂ j ∈ s, f j) := by
        refine Finset.measurableSet_biInter (m := blockLane m
          (ShellField.shellRestrictionSigma (⋃ j ∈ s, U j) hUnion)) s fun j hj ↦ ?_
        refine blockLane_shellRestrictionSigma_mono (hU j) hUnion ?_ m (f j)
          (hf j (Finset.mem_insert_of_mem hj))
        intro x hx
        exact Set.mem_biUnion hj hx
      have hpair : Indep
          (blockLane m (ShellField.shellRestrictionSigma (U i) (hU i)))
          (blockLane m (ShellField.shellRestrictionSigma (⋃ j ∈ s, U j) hUnion))
          P.toMeasure := by
        refine indep_blockLane hJ2 (fun W hW ↦ ShellField.shellRestrictionSigma W hW)
          (fun W hW ↦ ShellField.shellRestrictionSigma_le W hW) (hU i) hUnion m ?_
        intro n hn
        refine hJ1.restriction_range_dependence n (U i) (⋃ j ∈ s, U j) (hU i) hUnion ?_
        intro x y hx hy
        exact le_trans (by gcongr; norm_num) (hsep_union hx hy)
      have h_inter : P.toMeasure (f i ∩ ⋂ j ∈ s, f j) =
          P.toMeasure (f i) * P.toMeasure (⋂ j ∈ s, f j) :=
        (Indep_iff _ _ _).1 hpair (f i) (⋂ j ∈ s, f j)
          (hf i (Finset.mem_insert_self i s)) hs_meas
      calc P.toMeasure (⋂ j ∈ insert i s, f j)
          = P.toMeasure (f i ∩ ⋂ j ∈ s, f j) := by rw [Finset.set_biInter_insert]
        _ = P.toMeasure (f i) * P.toMeasure (⋂ j ∈ s, f j) := h_inter
        _ = P.toMeasure (f i) * ∏ j ∈ s, P.toMeasure (f j) := by
            rw [ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]
        _ = ∏ j ∈ insert i s, P.toMeasure (f j) := by rw [Finset.prod_insert hi]

/-- **The observable form**: random variables that are observables of the
joined restriction lanes of a pairwise separated family are mutually
independent. -/
theorem iIndepFun_of_blockLane_shellRestrictionSigma {iota : Type*}
    {beta : iota → Type*} [∀ i, MeasurableSpace (beta i)]
    (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (m : ℕ)
    {U : iota → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    {X : ∀ i, ShellSeq d → beta i}
    (hX : ∀ i, @Measurable (ShellSeq d) (beta i)
      (blockLane m (ShellField.shellRestrictionSigma (U i) (hU i))) inferInstance (X i))
    (hsep : Pairwise fun i j ↦ ShellField.AreShellSeparated m (U i) (U j)) :
    iIndepFun X P.toMeasure := by
  classical
  rw [iIndepFun_iff_iIndep, iIndep_iff]
  intro s f hf
  exact (iIndep_iff
    (fun i ↦ blockLane m (ShellField.shellRestrictionSigma (U i) (hU i))) _).1
    (iIndep_blockLane_shellRestrictionSigma hJ1 hJ2 m hU hsep) s
    fun i hi ↦ (Measurable.comap_le (hX i)) (f i) (hf i hi)

/-- **The sub-cube moments of a pairwise separated family of scale-`m` cubes
are mutually independent.** This is the paper's use of the range of
dependence `sqrt d 3^m` of `k_m - k_n` inside the concentration
step of display `e.kl.bounds.large`. -/
theorem iIndepFun_finiteShellIncrementCubePthMoment {iota : Type*}
    (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (n m : ℕ) {p : ℝ}
    (hp : (0 : ℝ) ≤ p) {Q : iota → TriadicCube d}
    (hscale : ∀ i, (Q i).scale = (m : ℤ))
    (hne : Function.Injective Q)
    (hcolor : ∀ i j, ShellField.cubeShellColor (Q i) = ShellField.cubeShellColor (Q j)) :
    iIndepFun (fun (i : iota) (omega : ShellSeq d) ↦
      finiteShellIncrementCubePthMoment n m p (Q i) omega) P.toMeasure := by
  refine iIndepFun_of_blockLane_shellRestrictionSigma hJ1 hJ2 m
    (U := fun i ↦ cubeSet (Q i)) (fun i ↦ measurableSet_cubeSet (Q i))
    (fun i ↦ measurable_blockCubeLane_finiteShellIncrementCubePthMoment n m hp (Q i))
    ?_
  intro i j hij
  exact ShellField.areShellSeparated_cubeSet_of_cubeShellColor_eq (hscale i) (hscale j)
    (hcolor i j) (fun hcon ↦ hij (hne hcon))

end

end SuperdiffusionCLT.Section2.Estimates.Stream
