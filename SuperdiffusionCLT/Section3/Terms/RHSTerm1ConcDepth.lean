/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepthB
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1AnalyticB

/-!
# The second-moment identity behind the concentration clause `_hConcDepth`

`SuperdiffusionCLT.Section3.Terms.ConcDepthClause` is the depth-resolved
concentration of the localized field `a_ℓ ∇ũ_n − q̃` (in `e.RHS.term1` of the
paper).  Its printed derivation is short:

> For `k ≥ ℓ`, each `3^k`-cube is decomposed into aligned `3^ℓ`-blocks.  After
> splitting these blocks into a bounded number of sublattices, the `O(3^ℓ)` range
> of dependence allows us to apply Proposition `p.concentration`, and the
> definition of `q̃` centers every such block by stationarity.

The quantitative content of that sentence is the identity

`E[(average of n centered observables)²] = n⁻¹ · (average of the second moments)`

for pairwise independent centered observables, applied to the `n = 3^{d (k-ℓ)}`
block averages inside one scale-`k` cube: the `3^{-d (k-ℓ)_+}` decay of the
printed clause *is* the `n⁻¹` of this identity, and the reference measure on the
right is the field's own `L̲²` energy (the block second moments are bounded by
the block energies, whose average is the whole-cube energy).  This module proves
that identity, and its `ℝ≥0∞` consequence in the shape the clause consumes.

## Main results

* `integral_sq_finsetAverage_eq_of_pairwise` — the second-moment identity for a
  finset average of pairwise independent, mean-zero, `L²` real observables.
  Unconditional: its only inputs are the pairwise independence, the `L²`
  membership and the mean-zero condition.
* `lintegral_ofReal_sq_finsetAverage_eq_of_pairwise` — the same at the `ℝ≥0∞`
  level as an **equality**, `∫⁻ ofReal((s-average)²) = ofReal(|s|⁻²) · ∑ i, ∫⁻ ofReal(X i²)`.
  The identity is `|s|⁻² · ∑` and not the weaker `|s|⁻¹ · max`, which is what
  makes the `1/|s|` gain of the printed decay sharp.
* `lintegral_ofReal_descendantsAverage` — the `ℝ≥0∞` exchange of a
  `descendantsAverage` with the annealed integral, for nonnegative observable
  families that are measurable in the sample.
* The **sublattice-to-cube step**: if a whole-cube average factors as the average of
  `|s|` sub-averages whose sum of energies is `|s|` times the whole-cube energy,
  then the annealed second moment of the whole-cube average is at most `|s|⁻¹`
  times the annealed whole-cube energy.  This is the Jensen step by which the
  bounded number of sublattices of the printed argument is absorbed at constant
  `1`.
* `concDepthField` — the observable field `a_ℓ ∇ũ_n − q̃` whose depth moment is
  `ConcDepthClause`.
* `memLp_hilbertifyVecField_concDepthField` — that field is `L̲²` on `cu_m` at
  every shell sequence, from the `MemVectorL2` closure of the glued
  gradient and the cutoff pairing.  This **discharges** the membership
  hypothesis of the reduction below.
* `depthClause_of_perCubeConcentration` — the clause at an arbitrary field from
  the per-cube concentration on every depth-`j` descendant, with the descendant
  averaging and the `vecSqAvg` tiling removed.
* `concDepthClause_of_perCubeConcentration` — `ConcDepthClause d nu hnu S P e Cc`
  from the per-cube concentration of `concDepthField` plus the two sample
  measurabilities.  The membership hypothesis is no longer carried.
* `aemeasurable_ofReal_vecNormSq_volumeAverageVec_concDepthField` and
  `aemeasurable_ofReal_vecSqAvg_concDepthField` — the two sample measurabilities
  at the observable field, obtained from the companion module
  `RHSTerm1ConcDepthB`; they are not residues.
* `concDepthClause_of_hconc` — `ConcDepthClause d nu hnu S P e Cc` from the
  per-cube concentration **alone**.

## The exact residual

After the reductions below, `ConcDepthClause` is equivalent to one named
statement, which is not a moment estimate:

* `hconc` — the per-cube concentration on each depth-`j` descendant `R`, i.e.
  the average of `3^{d (m-j-ℓ)}` centred `3^ℓ`-block averages obeys the `n⁻¹`
  decay.  The exponent `m-j-ℓ` is exactly the number of subdivision levels from
  the depth-`j` descendant (side `3^{m-j}`) down to a `3^ℓ`-block, so the
  clause's decay `3^{-d (m-j-ℓ)}` *is* the block count and the exponent
  truncates to `0` (factor `1`, no concentration) once `j > m-ℓ`, when the
  descendant holds at most one block.  Its inputs are the next three items (none
  of which is proved in this module):
  * the mean-zero condition at the **translated** blocks:
    `SublatticeConcentrationDepth.integral_fluxBlockAverageVec_eq_qVector` and
    `qVector_apply` center the block observable only at the centred cube `cu_ℓ`;
    the stationarity identity `E[(a_ℓ ∇ũ_n)_{cubeSet R}] = q̃` for a translated
    block `R` is a separate input;
  * the **lane measurability** of each block observable in the `σ`-algebra of
    the block's shell lane, the input of `iIndepFun_of_blockLane_shellRestrictionSigma`;
  * the **block-partition identification** of the descendant cube average with
    the finset average of its aligned block averages;
    `volumeAverageVec_eq_descendantsAverage_memLp` gives the descendant-average
    form, and the partition into `3^{d (m-j-ℓ)}` blocks is that identity read
    inside the descendant.

The former residues `hmeasA` (sample measurability of
`omega ↦ ofReal (vecNormSq (volumeAverageVec (cubeSet R) (concDepthField …)))`)
and `hmeasB` (sample measurability of
`omega ↦ ofReal (vecSqAvg R (concDepthField …))`) are discharged in
`RHSTerm1ConcDepthB`: the descendant cube mean is the inner product of the
cut-off coefficient row class with the glued `L²(cu_m)` class minus the drift,
and the descendant square average is the inverse cube volume times the squared
`L²(cu_m)` norm of the zero-extension of the pairing class, a continuous
function (the diagonal indicator multiplier) of the measurable pairing class.

## Why the amplitude rule does not reach the clause

`SublatticeConcentrationDepth` supplies the per-sublattice rule and the annealed
envelope, and an annealed *moment* bound for the term-1 flux block observable.
Neither reaches `ConcDepthClause`, and the
reason is a genuine mismatch of reference quantities, not a missing estimate.
The moment bound bounds the second moment of a sublattice average of the
block observables by the **square of the deterministic amplitude**

`nu⁻¹ · √(vecNormSq F) · coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d ℓ m + |q̃| + 1`,

times `1/|s|`.  The clause instead requires the bound to be by the field's *own*
annealed energy `∫⁻ ofReal(vecSqAvg (cu_m) ·)` with the same `1/|s|` gain.  The
two are not comparable in either direction: the amplitude is a bound on the
coefficient cutoff and does not control the glued gradient's realized energy
from below, so a small realized field satisfies the clause with a small
right-hand side while the amplitude stays fixed.  Passing the amplitude through
therefore cannot prove the clause at a scale-independent constant; this is why
the reduction of the clause to a numeric gate had to pay the factor
`3^{d (m-ℓ)}`.  The printed derivation avoids this by centering: `q̃` is defined
so that every block average is mean zero (`integral_volumeAverageVec_...` type
stationarity identities of the coarse centering and
`SublatticeConcentrationDepth.integral_fluxBlockAverageVec_eq_qVector`), and a
mean-zero average has second moment `n⁻¹` times the average of its summands'
second moments — the energy, not the amplitude.

What separates this identity from the clause is therefore purely the block
bookkeeping named in the previous section.  The per-block Jensen step
`E‖(field)_b‖² ≤ E(‖field‖² averaged on b)` is proved
(`RHSTerm1Analytic.vecDepthSqMoment_le_vecSqAvg_of_memVectorL2` and its per-block
form), and the average of the block energies over the blocks of a descendant is
the descendant's energy by `vecSqAvg_eq_descendantsAverage_memLp`, so the right
side of the identity is the field's own annealed energy as the clause requires.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The second-moment identity for a finset average of centered observables -/

/-- **The variance of a finset average of pairwise independent mean-zero
observables.**  For a finite family `X` indexed by `s`, pairwise independent
(`hpair`), square-integrable (`hmem`) and centered (`hmean`), the second moment
of the finset average is the `|s|⁻²` multiple of the sum of the summands' second
moments.  This is the identity whose `|s|⁻¹` reading on the right is the
`3^{-d (k-ℓ)_+}` decay of the printed concentration clause of `e.RHS.term1`. -/
theorem integral_sq_finsetAverage_eq_of_pairwise
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Finset ι} {X : ι → Ω → ℝ}
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hmem : ∀ i ∈ s, MeasureTheory.MemLp (X i) 2 μ)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    ∫ ω, (((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) ^ 2 ∂μ =
      ((s.card : ℝ)⁻¹) ^ 2 * ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ := by
  have hpair' : Set.Pairwise ↑s fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ :=
    fun i hi j hj hij => hpair i hi j hj hij
  have hint : ∀ i ∈ s, MeasureTheory.Integrable (fun ω => X i ω) μ :=
    fun i hi => (hmem i hi).integrable (by norm_num)
  have hYmem : MeasureTheory.MemLp (fun ω => ∑ i ∈ s, X i ω) 2 μ :=
    MeasureTheory.memLp_finsetSum s hmem
  have hYmean : ∫ ω, (∑ i ∈ s, X i ω) ∂μ = 0 := by
    rw [MeasureTheory.integral_finsetSum s hint]
    exact Finset.sum_eq_zero fun i hi => hmean i hi
  have hYsq : ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ := by
    have hfun : (∑ i ∈ s, X i) = fun ω => ∑ i ∈ s, X i ω :=
      funext fun ω => Finset.sum_apply ω s X
    have h1 : ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ =
        ProbabilityTheory.variance (fun ω => ∑ i ∈ s, X i ω) μ :=
      (ProbabilityTheory.variance_of_integral_eq_zero hYmem.aemeasurable hYmean).symm
    have h2 : ProbabilityTheory.variance (fun ω => ∑ i ∈ s, X i ω) μ =
        ∑ i ∈ s, ProbabilityTheory.variance (X i) μ := by
      rw [← hfun]
      exact ProbabilityTheory.IndepFun.variance_sum hmem hpair'
    have h3 : ∀ i ∈ s, ProbabilityTheory.variance (X i) μ = ∫ ω, (X i ω) ^ 2 ∂μ :=
      fun i hi => ProbabilityTheory.variance_of_integral_eq_zero
        (hmem i hi).aemeasurable (hmean i hi)
    rw [h1, h2]
    exact Finset.sum_congr rfl fun i hi => h3 i hi
  have hfac : ∀ ω : Ω,
      (((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) ^ 2 =
        ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, X i ω) ^ 2 := fun ω => by ring
  calc ∫ ω, (((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) ^ 2 ∂μ
      = ∫ ω, ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, X i ω) ^ 2 ∂μ := by simp_rw [hfac]
    _ = ((s.card : ℝ)⁻¹) ^ 2 * ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ :=
        MeasureTheory.integral_const_mul _ _
    _ = ((s.card : ℝ)⁻¹) ^ 2 * ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ := by rw [hYsq]

/-- **The `ℝ≥0∞` form of the second-moment identity, at the sharp `|s|⁻²`
scale.**  The `ℝ≥0∞` second moment of the finset average is exactly `|s|⁻²`
times the sum of the `ℝ≥0∞` second moments of the summands.  This is the
per-cube concentration step of the printed argument: with `|s| = 3^{d (m-j-ℓ)}`
blocks, the `|s|⁻²` here pairs with the factor `|s|` of the block tiling to give
the decay `3^{-d (m-j-ℓ)}` of `ConcDepthClause`.  The `|s|⁻¹` form would lose a
factor `|s|` and with it the whole decay. -/
theorem lintegral_ofReal_sq_finsetAverage_eq_of_pairwise
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {s : Finset ι} {X : ι → Ω → ℝ}
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hmem : ∀ i ∈ s, MeasureTheory.MemLp (X i) 2 μ)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    (∫⁻ ω, ENNReal.ofReal ((((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) ^ 2) ∂μ) =
      ENNReal.ofReal (((s.card : ℝ)⁻¹) ^ 2) *
        ∑ i ∈ s, ∫⁻ ω, ENNReal.ofReal ((X i ω) ^ 2) ∂μ := by
  have hYmem : MeasureTheory.MemLp (fun ω => ∑ i ∈ s, X i ω) 2 μ :=
    MeasureTheory.memLp_finsetSum s hmem
  have hint_f : MeasureTheory.Integrable
      (fun ω => (((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) ^ 2) μ :=
    (hYmem.const_mul ((s.card : ℝ)⁻¹)).integrable_sq
  have hnn : 0 ≤ᵐ[μ] fun ω => (((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hid := integral_sq_finsetAverage_eq_of_pairwise hpair hmem hmean
  have hnn' : ∀ i ∈ s, 0 ≤ ∫ ω, (X i ω) ^ 2 ∂μ :=
    fun i _ => MeasureTheory.integral_nonneg fun ω => sq_nonneg _
  calc (∫⁻ ω, ENNReal.ofReal ((((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) ^ 2) ∂μ)
      = ENNReal.ofReal (∫ ω, (((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω) ^ 2 ∂μ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_f hnn).symm
    _ = ENNReal.ofReal
          (((s.card : ℝ)⁻¹) ^ 2 * ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) := by rw [hid]
    _ = ENNReal.ofReal (((s.card : ℝ)⁻¹) ^ 2) *
          ENNReal.ofReal (∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂μ) :=
        ENNReal.ofReal_mul (sq_nonneg _)
    _ = ENNReal.ofReal (((s.card : ℝ)⁻¹) ^ 2) *
          ∑ i ∈ s, ENNReal.ofReal (∫ ω, (X i ω) ^ 2 ∂μ) := by
        rw [ENNReal.ofReal_sum_of_nonneg hnn']
    _ = ENNReal.ofReal (((s.card : ℝ)⁻¹) ^ 2) *
          ∑ i ∈ s, ∫⁻ ω, ENNReal.ofReal ((X i ω) ^ 2) ∂μ := by
        refine congrArg (fun t => ENNReal.ofReal (((s.card : ℝ)⁻¹) ^ 2) * t)
          (Finset.sum_congr rfl fun i hi => ?_)
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          ((hmem i hi).integrable_sq)
          (Filter.Eventually.of_forall fun ω => sq_nonneg _)

/-! ## The descendant average commutes with the annealed integral -/

/-- **The descendant average commutes with the annealed integral.**  For a
nonnegative family `B` over the depth-`j` descendants of a cube, the `ℝ≥0∞`
integral of the descendant average is the average of the integrals.  This is the
finitary Fubini step that turns the per-cube concentration of each descendant
into the averaged clause; it needs no positivity of the descendant count. -/
theorem lintegral_ofReal_descendantsAverage {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Q : TriadicCube d) (j : ℕ)
    {B : TriadicCube d → Ω → ℝ}
    (hmeas : ∀ R ∈ descendantsAtDepth Q j,
      AEMeasurable (fun ω => ENNReal.ofReal (B R ω)) μ)
    (hnonneg : ∀ R ∈ descendantsAtDepth Q j, ∀ ω, 0 ≤ B R ω) :
    ∫⁻ ω, ENNReal.ofReal (descendantsAverage Q j (fun R => B R ω)) ∂μ =
      ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j, ∫⁻ ω, ENNReal.ofReal (B R ω) ∂μ := by
  have hcongr : ∀ ω : Ω,
      ENNReal.ofReal (descendantsAverage Q j (fun R => B R ω)) =
        ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtDepth Q j, ENNReal.ofReal (B R ω) := by
    intro ω
    rw [descendantsAverage, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),
      ENNReal.ofReal_sum_of_nonneg (fun R hR => hnonneg R hR ω)]
  calc ∫⁻ ω, ENNReal.ofReal (descendantsAverage Q j (fun R => B R ω)) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtDepth Q j, ENNReal.ofReal (B R ω) ∂μ :=
        lintegral_congr hcongr
    _ = ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
          ∫⁻ ω, ∑ R ∈ descendantsAtDepth Q j, ENNReal.ofReal (B R ω) ∂μ :=
        MeasureTheory.lintegral_const_mul'' _
          ((Finset.aemeasurable_sum _ hmeas).congr
            (Filter.Eventually.of_forall fun ω => Finset.sum_apply ω _ _))
    _ = ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtDepth Q j, ∫⁻ ω, ENNReal.ofReal (B R ω) ∂μ := by
        rw [MeasureTheory.lintegral_finsetSum' _ hmeas]

/-! ## The concentration of a cube average from its block decomposition -/

/-! ## The averaged clause from the per-cube concentration

The per-cube concentration of the printed argument bounds the second moment of
the average of the observable field on each `3^k`-cube by the field's energy on
that cube, with the block-count decay.  The clause `ConcDepthClause` is the same
bound after averaging over the `3^{d (m-k)}` such cubes.  The averaging is
`lintegral_ofReal_descendantsAverage` applied to the depth moment and, in the
reverse direction, to the `vecSqAvg` tiling
`vecSqAvg_eq_descendantsAverage_memLp`; no analytic content is added. -/

/-- The observable field whose depth moment is `ConcDepthClause`: `a_ℓ ∇ũ_n − q̃`. -/
def concDepthField [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) (e : Vec d) (omega : ShellSeq d) : Vec d → Vec d :=
  fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
    (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) omega x)
    - qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)

/-- **The observable field is `L̲²` on `cu_m` at every shell sequence.**  This
discharges the membership hypothesis `hMem` of
`depthClause_of_perCubeConcentration` at the observable field: the glued
gradient is `L²` on every triadic cube (`memVectorL2_openCubeSet_gluedGradientField`),
the cutoff pairing preserves it (`memVectorL2_matVecMul_coefficientCutoff`), and
subtracting the constant `q̃` does too. -/
theorem memLp_hilbertifyVecField_concDepthField [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (omega : ShellSeq d) :
    MemLp (hilbertifyVecField (concDepthField hnu P S e omega)) 2
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
  have hG : MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
      (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) omega) :=
    memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m _ omega _
  have hA := memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
    (originCube d (S.m : ℤ)) hG
  have hsub := hA.sub (memVectorL2_const
    (U := openCubeSet (originCube d (S.m : ℤ)))
    (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)))
  exact SuperdiffusionCLT.Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2 hsub

/-- **The depth-moment clause at every depth from the per-cube concentration.**
For any field `F` that is `L̲²` on `cu_m` and whose cube average on *every*
depth-`j` descendant obeys the per-cube concentration with the block-count decay,
the averaged depth moment obeys the same bound with the same constant `Cc`.  This
removes the descendant averaging and the `vecSqAvg` tiling from the obligation
`_hConcDepth`; the concentration input
`hconc` is the per-cube statement the printed argument obtains by applying
Proposition `p.concentration` to the `3^{d (m-j-ℓ)}` centred block averages. -/
theorem depthClause_of_perCubeConcentration [NeZero d]
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) {Cc : ℝ}
    (F : ShellSeq d → Vec d → Vec d)
    (hMem : ∀ omega : ShellSeq d, MemLp (hilbertifyVecField (F omega)) 2
      (normalizedCubeMeasure (originCube d (S.m : ℤ))))
    (hconc : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
      (∫⁻ omega, ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet R) (F omega)))
          ∂P.toMeasure) ≤
        ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
          (∫⁻ omega, ENNReal.ofReal (vecSqAvg R (F omega)) ∂P.toMeasure))
    (hmeasA : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
      AEMeasurable (fun omega =>
        ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet R) (F omega)))) P.toMeasure)
    (hmeasB : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
      AEMeasurable (fun omega => ENNReal.ofReal (vecSqAvg R (F omega))) P.toMeasure) :
    ∀ j : ℕ,
      (∫⁻ omega, ENNReal.ofReal
          (vecDepthSqMoment (originCube d (S.m : ℤ)) j (F omega)) ∂P.toMeasure) ≤
        ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
          (∫⁻ omega, ENNReal.ofReal
            (vecSqAvg (originCube d (S.m : ℤ)) (F omega)) ∂P.toMeasure) := by
  intro j
  have hN : ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j, ∀ omega : ShellSeq d,
      0 ≤ vecNormSq (volumeAverageVec (cubeSet R) (F omega)) :=
    fun _ _ _ => vecNormSq_nonneg _
  have hN2 : ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j, ∀ omega : ShellSeq d,
      0 ≤ vecSqAvg R (F omega) := fun R _ _ => vecSqAvg_nonneg R (F _)
  have hExchA := lintegral_ofReal_descendantsAverage (μ := P.toMeasure)
    (originCube d (S.m : ℤ)) j
    (B := fun R omega => vecNormSq (volumeAverageVec (cubeSet R) (F omega)))
    (fun R hR => hmeasA j R hR) hN
  have hExchB := lintegral_ofReal_descendantsAverage (μ := P.toMeasure)
    (originCube d (S.m : ℤ)) j
    (B := fun R omega => vecSqAvg R (F omega)) (fun R hR => hmeasB j R hR) hN2
  have htileFun : (fun omega : ShellSeq d =>
        ENNReal.ofReal (vecSqAvg (originCube d (S.m : ℤ)) (F omega))) =
      fun omega : ShellSeq d => ENNReal.ofReal
        (descendantsAverage (originCube d (S.m : ℤ)) j (fun R => vecSqAvg R (F omega))) :=
    funext fun omega => by
      rw [vecSqAvg_eq_descendantsAverage_memLp (originCube d (S.m : ℤ)) j (hMem omega)]
  calc (∫⁻ omega, ENNReal.ofReal
          (vecDepthSqMoment (originCube d (S.m : ℤ)) j (F omega)) ∂P.toMeasure)
      = ∫⁻ omega, ENNReal.ofReal (descendantsAverage (originCube d (S.m : ℤ)) j
          (fun R => vecNormSq (volumeAverageVec (cubeSet R) (F omega)))) ∂P.toMeasure := by
        simp only [vecDepthSqMoment]
    _ = ENNReal.ofReal (((descendantsAtDepth (originCube d (S.m : ℤ)) j).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
            ∫⁻ omega, ENNReal.ofReal
              (vecNormSq (volumeAverageVec (cubeSet R) (F omega))) ∂P.toMeasure := hExchA
    _ ≤ ENNReal.ofReal (((descendantsAtDepth (originCube d (S.m : ℤ)) j).card : ℝ)⁻¹) *
          ∑ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
            ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
              ∫⁻ omega, ENNReal.ofReal (vecSqAvg R (F omega)) ∂P.toMeasure :=
        mul_le_mul_right (Finset.sum_le_sum fun R hR => hconc j R hR) _
    _ = ENNReal.ofReal (((descendantsAtDepth (originCube d (S.m : ℤ)) j).card : ℝ)⁻¹) *
          (ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
            ∑ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
              ∫⁻ omega, ENNReal.ofReal (vecSqAvg R (F omega)) ∂P.toMeasure) := by
        rw [← Finset.mul_sum]
    _ = ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
          (ENNReal.ofReal (((descendantsAtDepth (originCube d (S.m : ℤ)) j).card : ℝ)⁻¹) *
            ∑ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
              ∫⁻ omega, ENNReal.ofReal (vecSqAvg R (F omega)) ∂P.toMeasure) := by
        rw [mul_left_comm]
    _ = ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
          ∫⁻ omega, ENNReal.ofReal (descendantsAverage (originCube d (S.m : ℤ)) j
            (fun R => vecSqAvg R (F omega))) ∂P.toMeasure := by rw [hExchB]
    _ = ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
          ∫⁻ omega, ENNReal.ofReal
            (vecSqAvg (originCube d (S.m : ℤ)) (F omega)) ∂P.toMeasure := by
        rw [← htileFun]

/-- **The concentration clause `_hConcDepth` from the per-cube concentration.**
`ConcDepthClause` is `depthClause_of_perCubeConcentration` at the observable field
`a_ℓ ∇ũ_n − q̃ = concDepthField`: the clause follows from the per-cube
concentration of that field on every depth-`j` descendant of `cu_m`. -/
theorem concDepthClause_of_perCubeConcentration [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) {Cc : ℝ}
    (hconc : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
      (∫⁻ omega, ENNReal.ofReal
          (vecNormSq (volumeAverageVec (cubeSet R) (concDepthField hnu P S e omega)))
          ∂P.toMeasure) ≤
        ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
          (∫⁻ omega, ENNReal.ofReal
            (vecSqAvg R (concDepthField hnu P S e omega)) ∂P.toMeasure))
    (hmeasA : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
      AEMeasurable (fun omega => ENNReal.ofReal
        (vecNormSq (volumeAverageVec (cubeSet R) (concDepthField hnu P S e omega))))
        P.toMeasure)
    (hmeasB : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
      AEMeasurable (fun omega => ENNReal.ofReal
        (vecSqAvg R (concDepthField hnu P S e omega))) P.toMeasure) :
    ConcDepthClause d nu hnu S P e Cc :=
  fun j => depthClause_of_perCubeConcentration S P (concDepthField hnu P S e)
    (fun omega => memLp_hilbertifyVecField_concDepthField hnu P S e omega)
    hconc hmeasA hmeasB j

/-! ## The two sample measurabilities at the observable field -/

/-- **`hmeasA` at the observable field.**  The depth-`j` descendant cube mean of
`a_ℓ ∇ũ_n − q̃` is measurable in the sample, so its `ℝ≥0∞` image is.  This is
`RHSTerm1ConcDepthB.aemeasurable_ofReal_vecNormSq_volumeAverageVec_pairingField`
at the pinned data of the clause. -/
theorem aemeasurable_ofReal_vecNormSq_volumeAverageVec_concDepthField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (j : ℕ) {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j) :
    AEMeasurable (fun omega : ShellSeq d => ENNReal.ofReal
      (vecNormSq (volumeAverageVec (cubeSet R) (concDepthField hnu P S e omega))))
      P.toMeasure :=
  aemeasurable_ofReal_vecNormSq_volumeAverageVec_pairingField hnu P S.ell S.n S.m j
    (fluxSlot nu S.LPrime P S.n e)
    (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)) hR

/-- **`hmeasB` at the observable field.**  The depth-`j` descendant square
average of `a_ℓ ∇ũ_n − q̃` is measurable in the sample.  This is
`RHSTerm1ConcDepthB.aemeasurable_ofReal_vecSqAvg_pairingField` at the pinned
data of the clause. -/
theorem aemeasurable_ofReal_vecSqAvg_concDepthField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (j : ℕ) {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j) :
    AEMeasurable (fun omega : ShellSeq d => ENNReal.ofReal
      (vecSqAvg R (concDepthField hnu P S e omega))) P.toMeasure :=
  aemeasurable_ofReal_vecSqAvg_pairingField hnu P S.ell S.n S.m j
    (fluxSlot nu S.LPrime P S.n e)
    (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)) hR

/-- **The concentration clause `_hConcDepth` from the per-cube concentration
alone.**  Both sample measurabilities of
`concDepthClause_of_perCubeConcentration` are discharged at the observable field
by `aemeasurable_ofReal_vecNormSq_volumeAverageVec_concDepthField` and
`aemeasurable_ofReal_vecSqAvg_concDepthField`, and the `L̲²(cu_m)` membership by
`memLp_hilbertifyVecField_concDepthField`, so `ConcDepthClause` follows from
`hconc` and nothing else. -/
theorem concDepthClause_of_hconc [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) {Cc : ℝ}
    (hconc : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j,
      (∫⁻ omega, ENNReal.ofReal
          (vecNormSq (volumeAverageVec (cubeSet R) (concDepthField hnu P S e omega)))
          ∂P.toMeasure) ≤
        ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
          (∫⁻ omega, ENNReal.ofReal
            (vecSqAvg R (concDepthField hnu P S e omega)) ∂P.toMeasure)) :
    ConcDepthClause d nu hnu S P e Cc :=
  concDepthClause_of_perCubeConcentration hnu S P e hconc
    (fun j _ hR => aemeasurable_ofReal_vecNormSq_volumeAverageVec_concDepthField hnu P S e j hR)
    (fun j _ hR => aemeasurable_ofReal_vecSqAvg_concDepthField hnu P S e j hR)

end

end SuperdiffusionCLT.Section3.Terms
