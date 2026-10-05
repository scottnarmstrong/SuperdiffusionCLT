/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB
public import SuperdiffusionCLT.Probability.OrliczPower
public import SuperdiffusionCLT.Probability.OrliczProduct
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Probability.OrliczMoments
public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsStationary
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergy

/-!
# The per-shell estimates and the shell-average moments of `l.LHS.term1`

The scale-by-scale half of the proof of `e.nabla.w.lower.bound`, and the second
moment of the shell cube averages that its last step needs.

For one shell `r` and the pigeonhole cube `cu_M` the printed argument is

1. the two weak norms of the shell flux `j_r p` on `cu_M`
   (`e.jk.Hminus.endpoint` and the `L̲⁴` bound of the proof of `l.LHS.term1`),
   together with the cube average `(j_r p)_{cu_M}` (`e.jk.spatialavg`);
2. the deterministic weak Neumann-minus-Dirichlet comparison
   `e.abstract.response.ND.weak`, applied to the *centered*
   flux — legitimate because constants disappear under the divergence
   (`e.#centered-flux-responses`, proved as
   `isCubeDirichletResponse_sub_const_iff`); and
3. the Orlicz bookkeeping `e.powerofGammasigma` and `e.multGammasig` that turns
   the product of the two weak norms into a single `O_{Γ₂}` amplitude — the
   two exponents `1/5` and `4/5` produce the indices `Γ_{10}` and `Γ_{5/2}`,
   whose product index is `(10 · 5/2)/(10 + 5/2) = 2`, which is why the printed
   right-hand side of `e.wNr.vs.wDr.r.small` is again a `Γ₂` amplitude.

The two weak-norm displays of step 1 enter here as explicit hypotheses in their
exact applied shapes (an amplitude, a measurable bounding observable, and the
pointwise domination), never as a proposition-valued definition.

## Main results

* `volumeAverageVec_cubeSet_matVecMul_shellReg`, `volumeAverageVec_shellFlux`:
  `(j_r p)_{cu_M}` read through the spatial-average carrier
  `ShellField.shellSpatialAverage`.
* `memVectorL2_shellFlux`,
  `isCubeDirichletResponse_shellFlux_sub_volumeAverage_iff`: the Dirichlet
  response of `j_r p` is the Dirichlet response of the centered flux.
* `isBigO_gammaSigma_rpow_mul_add`: the Orlicz bookkeeping of step 3.
* `shellResponseGapConst`: the constant of the per-shell display
  `e.wNr.vs.wDr.r.small` for `r < M`.
* `integrable_sq_of_isBigO_gammaSigma_two`,
  `integral_sq_le_of_isBigO_gammaSigma_two`,
  `memLp_two_of_isBigO_gammaSigma_two`: the second moment of a `Γ₂`
  observable, the case `k = 2` of the printed layer-cake bound.
* `integral_shellFluxAverage_apply_eq_zero`: the zero-mean step of
  `e.average.error.energy`, from the negation clause of
  `ShellLawJ4`.
* `iIndepFun_shellFluxAverage_apply`: `a.j.indy` read on the cube averages.
* `integral_vecNormSq_sum_shellFluxAverage_le`: `e.average.error.energy` itself.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The cube average of a shell flux -/

/-- Every shell field is continuous, hence integrable entry by entry on a
triadic cube. -/
theorem integrableOn_cubeSet_shell_entry (Q : TriadicCube d)
    (j : ShellField d) (i k : Fin d) :
    IntegrableOn (fun x => j x i k) (cubeSet Q) volume := by
  have hc : Continuous fun x : Vec d => j x i k :=
    (continuous_apply k).comp ((continuous_apply i).comp j.1.1.continuous)
  exact (hc.continuousOn.integrableOn_compact
    ((isBounded_cubeSet Q).isCompact_closure)).mono_set subset_closure

/-- On a triadic cube the ambient normalized average is the cube average. -/
theorem volumeAverage_cubeSet (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = cubeAverage Q f := by
  rw [volumeAverage, cubeAverage, volume_cubeSet_toReal]

/-- **`(j_r p)_{cu_M}`**, the cube average of the shell flux, is the
matrix spatial average `ShellField.shellSpatialAverage` applied to `p`.

This is the identification that lets the printed proof read the average term of
`e.abstract.response.ND.weak` through `e.jk.spatialavg` and, in the last step,
through the negation half of `ShellLawJ4`. -/
theorem volumeAverageVec_cubeSet_matVecMul_shellReg
    (M : ℤ) (r : ℕ) (omega : ShellSeq d) (p : Vec d) :
    volumeAverageVec (cubeSet (originCube d M))
        (fun x => matVecMul (shellReg omega r x) p) =
      matVecMul (ShellField.shellSpatialAverage M 0 (omega r)) p := by
  funext i
  have hint : ∀ k : Fin d, IntegrableOn
      (fun x => shellReg omega r x i k * p k) (cubeSet (originCube d M)) volume :=
    fun k => (integrableOn_cubeSet_shell_entry (originCube d M) (omega r) i k).mul_const _
  have hsplit : ∫ x in cubeSet (originCube d M),
        (∑ k, shellReg omega r x i k * p k) ∂volume =
      ∑ k, ∫ x in cubeSet (originCube d M), shellReg omega r x i k * p k ∂volume :=
    integral_finsetSum _ fun k _ => hint k
  have havg : ShellField.shellSpatialAverage M 0 (omega r) i =
      fun k => cubeAverage (originCube d M) (fun x => shellReg omega r x i k) := by
    funext k
    simp only [ShellField.shellSpatialAverage,
      ShellField.translatedShellCubeAverage, cubeAverageMat, add_zero]
    rfl
  show volumeAverage (cubeSet (originCube d M))
      (fun x => matVecMul (shellReg omega r x) p i) = _
  simp only [matVecMul, havg]
  rw [volumeAverage_cubeSet, cubeAverage, hsplit, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const, cubeAverage]
  ring

/-! ## The shell flux and its cube average -/

/-- **`j_r p`**, the flux of the single shell `r` in the direction `p`. -/
def shellFlux (omega : ShellSeq d) (r : ℕ) (p : Vec d) : Vec d → Vec d :=
  fun x => matVecMul (shellReg omega r x) p

/-- **`(j_r p)_{cu_M}`**, the cube average of `shellFlux`, read through the
matrix spatial average. -/
def shellFluxAverage (M : ℤ) (omega : ShellSeq d) (r : ℕ) (p : Vec d) : Vec d :=
  matVecMul (ShellField.shellSpatialAverage M 0 (omega r)) p

theorem volumeAverageVec_shellFlux (M : ℤ) (r : ℕ) (omega : ShellSeq d)
    (p : Vec d) :
    volumeAverageVec (cubeSet (originCube d M)) (shellFlux omega r p) =
      shellFluxAverage M omega r p :=
  volumeAverageVec_cubeSet_matVecMul_shellReg M r omega p

/-- A shell flux is square integrable on the open cube: it is continuous, hence
bounded on the bounded cube. -/
theorem memVectorL2_shellFlux (Q : TriadicCube d) (r : ℕ) (omega : ShellSeq d)
    (p : Vec d) :
    MemVectorL2 (openCubeSet Q) (shellFlux omega r p) := by
  have hcont : Continuous (shellFlux omega r p) := by
    rw [continuous_pi_iff]
    intro i
    simp only [shellFlux, matVecMul]
    refine continuous_finsetSum _ fun k _ => ?_
    exact ((continuous_apply k).comp
      ((continuous_apply i).comp (omega r).1.1.continuous)).mul continuous_const
  obtain ⟨C, hC⟩ :=
    (isBounded_openCubeSet Q).isCompact_closure.exists_bound_of_continuousOn
      hcont.continuousOn
  refine MemLp.of_bound hcont.aestronglyMeasurable C ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_openCubeSet Q)] with x hx
  exact hC x (subset_closure hx)

/-- **`#centered-flux-responses` for a shell flux**: constants disappear under the
divergence, so the Dirichlet response of `j_r p` in `cu_M` is exactly the
Dirichlet response of the centered flux `j_r p − (j_r p)_{cu_M}`.

This is `isCubeDirichletResponse_sub_const_iff` at the constant
`(j_r p)_{cu_M}`, with the square integrability of the shell flux supplied by
`memVectorL2_shellFlux`. -/
theorem isCubeDirichletResponse_shellFlux_sub_volumeAverage_iff
    {Q : TriadicCube d} {r : ℕ} {omega : ShellSeq d} {p : Vec d}
    {w : H10Function (openCubeSet Q)} :
    IsCubeDirichletResponse Q (shellFlux omega r p) w ↔
      IsCubeDirichletResponse Q
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet Q) (shellFlux omega r p)) w :=
  isCubeDirichletResponse_sub_const_iff (memVectorL2_shellFlux Q r omega p) _

/-! ## The Orlicz bookkeeping of the two exponents -/

/-- **`e.powerofGammasigma` and `e.multGammasig` at the exponents `1/5` and
`4/5`**.  The two powers turn a `Γ₂`
amplitude into `Γ_{10}` and `Γ_{5/2}` amplitudes, whose product index is
`(10 · 5/2)/(10 + 5/2) = 2`; adding the third `Γ₂` term through the
two-term triangle rule keeps the index `2`, which is why the printed conclusion
`e.wNr.vs.wDr.r.small` is again a `Γ₂` bound. -/
theorem isBigO_gammaSigma_rpow_mul_add
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {Za Zb Zc : Omega → ℝ} {A B C : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hZa : ∀ w, 0 ≤ Za w) (hZb : ∀ w, 0 ≤ Zb w)
    (hZam : Measurable Za) (hZbm : Measurable Zb) (hZcm : Measurable Zc)
    (ha : IsBigO mu (gammaSigma 2) Za A)
    (hb : IsBigO mu (gammaSigma 2) Zb B)
    (hc : IsBigO mu (gammaSigma 2) Zc C) :
    IsBigO mu (gammaSigma 2)
      (fun w => Za w ^ ((1 : ℝ) / 5) * Zb w ^ ((4 : ℝ) / 5) + Zc w)
      (gammaTriangleConst 2 *
        (orliczProductConst 10 (5 / 2) *
          (A ^ ((1 : ℝ) / 5) * B ^ ((4 : ℝ) / 5)) + C)) := by
  have h1 : IsBigO mu (gammaSigma 10)
      (fun w => Za w ^ ((1 : ℝ) / 5)) (A ^ ((1 : ℝ) / 5)) := by
    have h := isBigO_gammaSigma_rpow_fwd (mu := mu) (X := Za) (K := A) (σ := 2)
      (p := (1 : ℝ) / 5) (by norm_num) hA.le hZa ha
    simpa only [show (2 : ℝ) / ((1 : ℝ) / 5) = 10 by norm_num] using h
  have h2 : IsBigO mu (gammaSigma (5 / 2))
      (fun w => Zb w ^ ((4 : ℝ) / 5)) (B ^ ((4 : ℝ) / 5)) := by
    have h := isBigO_gammaSigma_rpow_fwd (mu := mu) (X := Zb) (K := B) (σ := 2)
      (p := (4 : ℝ) / 5) (by norm_num) hB.le hZb hb
    simpa only [show (2 : ℝ) / ((4 : ℝ) / 5) = 5 / 2 by norm_num] using h
  have h3 : IsBigO mu (gammaSigma 2)
      (fun w => Za w ^ ((1 : ℝ) / 5) * Zb w ^ ((4 : ℝ) / 5))
      (orliczProductConst 10 (5 / 2) *
        (A ^ ((1 : ℝ) / 5) * B ^ ((4 : ℝ) / 5))) := by
    have h := isBigO_gammaSigma_mul (mu := mu) (σ₁ := 10) (σ₂ := 5 / 2)
      (by norm_num) (by norm_num) (Real.rpow_nonneg hA.le _)
      (Real.rpow_nonneg hB.le _) h1 h2
    simpa only [show (10 : ℝ) * (5 / 2) / (10 + 5 / 2) = 2 by norm_num] using h
  refine isBigO_gammaSigma_add_of_isBigO (by norm_num) ?_ hC h3 hc
    ((hZam.pow_const _).mul (hZbm.pow_const _)) hZcm
  have hp := orliczProductConst_pos 10 (5 / 2)
  have hA5 : (0 : ℝ) < A ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hA _
  have hB5 : (0 : ℝ) < B ^ ((4 : ℝ) / 5) := Real.rpow_pos_of_pos hB _
  positivity

/-! ## The per-shell display `e.wNr.vs.wDr.r.small` -/

/-- The constant of the printed display `e.wNr.vs.wDr.r.small`,
assembled from the a priori response constant `Cnd`
(`e.abstract.response.ND.weak`), the two weak-norm constants `Chm`
(`e.jk.Hminus.endpoint`) and `Cl4` (the `L̲⁴` bound of the proof of
`l.LHS.term1`), the spatial-average constant `Cav` (`e.jk.spatialavg`) and the two Orlicz
constants of `e.multGammasig` and `l.Gamma.sigma.triangle`. -/
def shellResponseGapConst (Cnd Chm Cl4 Cav : ℝ) : ℝ :=
  Cnd * (gammaTriangleConst 2 *
    (orliczProductConst 10 (5 / 2) *
      (Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5)) + Cav))

/-! ## Second moments of a `Γ₂` observable -/

section Moments

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable [IsProbabilityMeasure mu]

/-- A `Γ₂` observable has an integrable square. -/
theorem integrable_sq_of_isBigO_gammaSigma_two {X : Omega → ℝ} {A : ℝ}
    (hA : 0 < A) (hXm : AEMeasurable X mu)
    (hX : IsBigO mu (gammaSigma 2) X A) :
    Integrable (fun omega => X omega ^ 2) mu := by
  have h := integrable_abs_rpow_of_isBigO_gammaSigma_two hA hXm hX 2
  have hfun : (fun omega => |X omega| ^ ((2 : ℕ) : ℝ)) =
      fun omega => X omega ^ 2 := by
    funext omega
    rw [Real.rpow_natCast, sq_abs]
  rwa [hfun] at h

/-- **The second moment of a `Γ₂` observable**, the case `k = 2` of the
layer-cake bound of the paper. -/
theorem integral_sq_le_of_isBigO_gammaSigma_two {X : Omega → ℝ} {A : ℝ}
    (hA : 0 < A) (hXm : AEMeasurable X mu)
    (hX : IsBigO mu (gammaSigma 2) X A) :
    ∫ omega, X omega ^ 2 ∂mu ≤ A ^ 2 * (1 + Real.Gamma 2) := by
  have h := abs_moment_le_of_isBigO_gammaSigma_two hA hXm hX 2
  have hfun : (fun omega => |X omega| ^ ((2 : ℕ) : ℝ)) =
      fun omega => X omega ^ 2 := by
    funext omega
    rw [Real.rpow_natCast, sq_abs]
  rw [hfun] at h
  have hA2 : A ^ ((2 : ℕ) : ℝ) = A ^ 2 := Real.rpow_natCast A 2
  have hg : ((2 : ℕ) : ℝ) / 2 + 1 = 2 := by norm_num
  rwa [hA2, hg] at h

/-- A `Γ₂` observable is square integrable. -/
theorem memLp_two_of_isBigO_gammaSigma_two {X : Omega → ℝ} {A : ℝ}
    (hA : 0 < A) (hXm : AEStronglyMeasurable X mu)
    (hX : IsBigO mu (gammaSigma 2) X A) :
    MemLp X 2 mu :=
  (memLp_two_iff_integrable_sq hXm).2
    (integrable_sq_of_isBigO_gammaSigma_two hA hXm.aemeasurable hX)

end Moments

/-! ## The average error of `e.average.error.energy` -/

section AverageError

variable {P : ProbabilityMeasure (ShellSeq d)}

theorem measurable_shellFluxAverage_apply (M : ℤ) (r : ℕ) (p : Vec d)
    (i : Fin d) :
    Measurable fun omega : ShellSeq d => shellFluxAverage M omega r p i :=
  (measurable_pi_apply i).comp (measurable_matVecMul_shellSpatialAverage r M 0 p)

/-- **The zero-mean step of `e.average.error.energy`**: the
paper's "zero-mean consequence of the dihedral symmetry assumption
`a.j.iso`", coordinate by coordinate.  Whole-sequence negation is a symmetry of
the law (the `negation` clause of `ShellLawJ4`) and turns the cube
average `(j_r p)_{cu_M}` into its own negative, so its expectation vanishes. -/
theorem integral_shellFluxAverage_apply_eq_zero (hJ4 : ShellLawJ4 d P)
    (M : ℤ) (r : ℕ) (p : Vec d) (i : Fin d) :
    ∫ omega : ShellSeq d, shellFluxAverage M omega r p i ∂P.toMeasure = 0 := by
  refine integral_eq_zero_of_negateSequence_neg hJ4
    (measurable_shellFluxAverage_apply M r p i).aestronglyMeasurable
    fun omega => ?_
  show shellFluxAverage M (ShellField.negateSequence omega) r p i =
    -shellFluxAverage M omega r p i
  simp only [shellFluxAverage, ShellField.negateSequence_apply,
    ShellField.shellSpatialAverage_negate, matVecMul_neg_left, Pi.neg_apply]

/-- **`a.j.indy` read on the cube averages**: the coordinates
of `(j_r p)_{cu_M}` are measurable functions of the single shell `r`, so the
mutual independence of the shells makes them mutually independent. -/
theorem iIndepFun_shellFluxAverage_apply (hJ2 : ShellLawJ2 d P) (M : ℤ)
    (p : Vec d) (i : Fin d) :
    iIndepFun (fun (r : ℕ) (omega : ShellSeq d) =>
      shellFluxAverage M omega r p i) P.toMeasure :=
  hJ2.independent.comp
    (fun _ : ℕ => fun j : ShellField d =>
      matVecMul (ShellField.shellSpatialAverage M 0 j) p i)
    (fun _ => (measurable_pi_apply i).comp
      (measurable_matVecMul_left
        (ShellField.measurable_shellSpatialAverage M 0) p))

/-- The manuscript's `|v|²` in the two spellings the files use. -/
theorem vecNorm_sq_eq_vecNormSq (v : Vec d) :
    vecNorm v ^ 2 = vecNormSq v := by
  have h : ‖HilbertVec.ofVec v‖ ^ (2 : ℕ) = vecNormSq v := by
    rw [HilbertVec.norm_sq_eq_sum_sq]
    simp [vecNormSq, vecDot, sq]
  exact h

/-- Each coordinate of a cube average carrying a `Γ₂` amplitude is square
integrable. -/
theorem memLp_two_shellFluxAverage_apply {M : ℤ} {r : ℕ} {p : Vec d} {A : ℝ}
    (hA : 0 < A) {Z : ShellSeq d → ℝ} (hZm : Measurable Z)
    (hZbig : IsBigO P.toMeasure (gammaSigma 2) Z A)
    (hZbound : ∀ omega, vecNorm (shellFluxAverage M omega r p) ≤ Z omega)
    (i : Fin d) :
    MemLp (fun omega : ShellSeq d => shellFluxAverage M omega r p i) 2
      P.toMeasure := by
  refine (memLp_two_of_isBigO_gammaSigma_two hA hZm.aestronglyMeasurable
    hZbig).of_le
    (measurable_shellFluxAverage_apply M r p i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  exact le_trans (le_trans (HilbertVec.abs_apply_le_norm
    (HilbertVec.ofVec (shellFluxAverage M omega r p)) i) (hZbound omega))
    (le_abs_self _)

/-- The squared length of the sum of the cube averages is integrable. -/
theorem integrable_vecNormSq_sum_shellFluxAverage (M : ℤ) (s : Finset ℕ)
    (p : Vec d) (A : ℕ → ℝ) (hApos : ∀ r ∈ s, 0 < A r) (Z : ℕ → ShellSeq d → ℝ)
    (hZm : ∀ r, Measurable (Z r))
    (hZbig : ∀ r ∈ s, IsBigO P.toMeasure (gammaSigma 2) (Z r) (A r))
    (hZbound : ∀ (r : ℕ) (omega : ShellSeq d),
      vecNorm (shellFluxAverage M omega r p) ≤ Z r omega) :
    Integrable (fun omega : ShellSeq d =>
      vecNormSq (∑ r ∈ s, shellFluxAverage M omega r p)) P.toMeasure := by
  classical
  have hmem : ∀ i : Fin d, MemLp
      (fun omega : ShellSeq d => ∑ r ∈ s, shellFluxAverage M omega r p i) 2
      P.toMeasure := by
    intro i
    have h := memLp_finsetSum' (μ := P.toMeasure) (p := 2) s
      (f := fun (r : ℕ) (omega : ShellSeq d) => shellFluxAverage M omega r p i)
      (fun r hr => memLp_two_shellFluxAverage_apply (hApos r hr) (hZm r)
        (hZbig r hr) (fun omega => hZbound r omega) i)
    refine MemLp.ae_eq (Filter.Eventually.of_forall fun omega => ?_) h
    simp only [Finset.sum_apply]
  have heq : ∀ omega : ShellSeq d,
      vecNormSq (∑ r ∈ s, shellFluxAverage M omega r p) =
        ∑ i, (∑ r ∈ s, shellFluxAverage M omega r p i) ^ 2 := by
    intro omega
    show ∑ i, (∑ r ∈ s, shellFluxAverage M omega r p) i *
      (∑ r ∈ s, shellFluxAverage M omega r p) i = _
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.sum_apply, sq]
  refine (integrable_finsetSum Finset.univ
    fun i _ => (hmem i).integrable_sq).congr
    (Filter.Eventually.of_forall fun omega => ?_)
  exact (heq omega).symm

/-- **`e.average.error.energy`**:

`E|Σ_{r ∈ s} (j_r p)_{cu_M}|² ≤ (1 + Γ(2)) Σ_{r ∈ s} A_r²`.

The cross terms vanish because different shells are independent (`a.j.indy`,
`ShellLawJ2`) and each cube average is centered (the zero-mean
consequence of `a.j.iso`, the negation clause of `ShellLawJ4`); the
diagonal terms are the second moments supplied by `e.jk.spatialavg`, carried
here as the amplitudes `A r` with their bounding observables `Z r`.

At the shells `r ≥ M` of the printed proof the display `e.jk.spatialavg` has
amplitude `A r = C|p|`, so the right-hand side is `C(1 + L' − M)|p|²`, which is
the printed conclusion. -/
theorem integral_vecNormSq_sum_shellFluxAverage_le (hJ2 : ShellLawJ2 d P)
    (hJ4 : ShellLawJ4 d P) (M : ℤ) (s : Finset ℕ) (p : Vec d) (A : ℕ → ℝ)
    (hApos : ∀ r ∈ s, 0 < A r) (Z : ℕ → ShellSeq d → ℝ)
    (hZm : ∀ r, Measurable (Z r))
    (hZbig : ∀ r ∈ s, IsBigO P.toMeasure (gammaSigma 2) (Z r) (A r))
    (hZbound : ∀ (r : ℕ) (omega : ShellSeq d),
      vecNorm (shellFluxAverage M omega r p) ≤ Z r omega) :
    ∫ omega : ShellSeq d,
        vecNormSq (∑ r ∈ s, shellFluxAverage M omega r p) ∂P.toMeasure ≤
      (1 + Real.Gamma 2) * ∑ r ∈ s, A r ^ 2 := by
  classical
  set Y : ℕ → Fin d → ShellSeq d → ℝ :=
    fun r i omega => shellFluxAverage M omega r p i with hYdef
  set D : ℕ → ℕ → ShellSeq d → ℝ :=
    fun r t omega => ∑ i, Y r i omega * Y t i omega with hDdef
  have hZsq : ∀ r ∈ s, Integrable (fun omega => Z r omega ^ 2) P.toMeasure :=
    fun r hr => integrable_sq_of_isBigO_gammaSigma_two (hApos r hr)
      (hZm r).aemeasurable (hZbig r hr)
  have hYmem : ∀ r ∈ s, ∀ i : Fin d, MemLp (Y r i) 2 P.toMeasure :=
    fun r hr i => memLp_two_shellFluxAverage_apply (hApos r hr) (hZm r)
      (hZbig r hr) (fun omega => hZbound r omega) i
  have hDint : ∀ r ∈ s, ∀ t ∈ s, Integrable (D r t) P.toMeasure := by
    intro r hr t ht
    exact integrable_finsetSum _ fun i _ =>
      (hYmem r hr i).integrable_mul (hYmem t ht i)
  have hexpand : ∀ omega : ShellSeq d,
      vecNormSq (∑ r ∈ s, shellFluxAverage M omega r p) =
        ∑ r ∈ s, ∑ t ∈ s, D r t omega := by
    intro omega
    show ∑ i, (∑ r ∈ s, shellFluxAverage M omega r p) i *
        (∑ r ∈ s, shellFluxAverage M omega r p) i = _
    simp only [Finset.sum_apply, hDdef, hYdef, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
  have hcross : ∀ r ∈ s, ∀ t ∈ s, r ≠ t →
      ∫ omega, D r t omega ∂P.toMeasure = 0 := by
    intro r _ t _ hrt
    rw [hDdef]
    refine (integral_finsetSum _ fun i _ =>
      (hYmem r ‹r ∈ s› i).integrable_mul (hYmem t ‹t ∈ s› i)).trans ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    have hindep := (iIndepFun_shellFluxAverage_apply hJ2 M p i).indepFun hrt
    show ∫ omega, shellFluxAverage M omega r p i *
      shellFluxAverage M omega t p i ∂P.toMeasure = 0
    rw [hindep.integral_fun_mul_eq_mul_integral
      (measurable_shellFluxAverage_apply M r p i).aestronglyMeasurable
      (measurable_shellFluxAverage_apply M t p i).aestronglyMeasurable,
      integral_shellFluxAverage_apply_eq_zero hJ4 M r p i, zero_mul]
  have hdiag : ∀ r ∈ s, ∫ omega, D r r omega ∂P.toMeasure ≤
      A r ^ 2 * (1 + Real.Gamma 2) := by
    intro r hr
    have hDeq : ∀ omega : ShellSeq d,
        D r r omega = vecNormSq (shellFluxAverage M omega r p) := fun _ => rfl
    have hDdom : Integrable (D r r) P.toMeasure := hDint r hr r hr
    have hmono : ∫ omega, D r r omega ∂P.toMeasure ≤
        ∫ omega, Z r omega ^ 2 ∂P.toMeasure := by
      refine integral_mono hDdom (hZsq r hr) fun omega => ?_
      rw [hDeq omega, ← vecNorm_sq_eq_vecNormSq]
      have h0 : (0 : ℝ) ≤ vecNorm (shellFluxAverage M omega r p) :=
        norm_nonneg (HilbertVec.ofVec (shellFluxAverage M omega r p))
      exact pow_le_pow_left₀ h0 (hZbound r omega) 2
    exact hmono.trans (integral_sq_le_of_isBigO_gammaSigma_two (hApos r hr)
      (hZm r).aemeasurable (hZbig r hr))
  calc ∫ omega : ShellSeq d,
        vecNormSq (∑ r ∈ s, shellFluxAverage M omega r p) ∂P.toMeasure
      = ∑ r ∈ s, ∑ t ∈ s, ∫ omega, D r t omega ∂P.toMeasure := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hexpand),
          integral_finsetSum _ fun r hr =>
            integrable_finsetSum _ fun t ht => hDint r hr t ht]
        exact Finset.sum_congr rfl fun r hr =>
          integral_finsetSum _ fun t ht => hDint r hr t ht
    _ = ∑ r ∈ s, ∫ omega, D r r omega ∂P.toMeasure := by
        refine Finset.sum_congr rfl fun r hr => ?_
        refine Finset.sum_eq_single r (fun t ht hne => hcross r hr t ht (Ne.symm hne))
          (fun hns => absurd hr hns)
    _ ≤ ∑ r ∈ s, A r ^ 2 * (1 + Real.Gamma 2) :=
        Finset.sum_le_sum hdiag
    _ = (1 + Real.Gamma 2) * ∑ r ∈ s, A r ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => mul_comm _ _

end AverageError

end

end SuperdiffusionCLT.Section3.Setup
