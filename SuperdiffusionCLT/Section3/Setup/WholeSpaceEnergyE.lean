/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.ResponseLinearity
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyD

/-!
# The `r ≥ M` shell branch and the summation step of `l.LHS.term1`

The second half of the scale-by-scale estimate of `e.nabla.w.lower.bound`, and
the summation that produces the display `e.wN.wD.with.average.error`.

* The branch `r ≥ m`.  The print sets
  `ṽ_r = w̃_r + (j_r p)_{cu_m}·x` and observes that `ṽ_r` is the Neumann
  response of the *centered* flux `j_r p − (j_r p)_{cu_m}`, while `w_r` is also
  its Dirichlet response.  Both halves are proved: the Neumann one is
  `isCubeNeumannResponse_sub_const` of
  `Section3/ResponseFields/ResponseLinearity.lean`, the Dirichlet one is
  `isCubeDirichletResponse_shellFlux_sub_volumeAverage_iff` of the companion
  module `WholeSpaceEnergyC.lean`.  Applying `e.abstract.response.ND.weak` to
  the centered flux, whose own cube average is zero, removes the average term
  of that display outright, and the two remaining weak norms combine through
  the same Orlicz product rule as in the branch `r < m`.
* The summation.  By the linearity of the two response
  problems in the flux — `isCubeDirichletResponse_finsetSum` and
  `isCubeNeumannResponse_finsetSum` — together with the uniqueness of the two
  response gradients, `∇w̃ − ∇w` agrees almost everywhere with
  `Σ_r (∇w̃_r + b_r − ∇w_r) − Σ_r b_r` for any choice of shift vectors `b_r`.
  Taking `b_r = 0` for `r < m` and `b_r = (j_r p)_{cu_m}` for `r ≥ m` is
  exactly the print's "retaining only the average part of the scales `r ≥ m`",
  and the triangle inequality in `L̲²(cu_m)` gives the printed display.

The displays `e.jk.Hminus.endpoint` (in its `r ≥ m` Poincaré form), the `L̲⁴`
bound of the proof of `l.LHS.term1` and `e.jk.spatialavg` enter as explicit
hypotheses in their exact applied shapes, as they do in `WholeSpaceEnergyC.lean`.

## Main results

* `vecCubeLpENorm_const`, `vecCubeLpENorm_finsetSum_le`: the two `L̲²`
  ingredients of the summation.
* `shellResponseGapGeConst`: the constant of the per-shell display for `r ≥ M`.
* `vecCubeLpENorm_grad_sub_le_of_shellBranches`: the summation step, in the
  shape of `e.wN.wD.with.average.error`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Two `L̲²` ingredients -/

/-- The normalized `L̲^q` norm of a constant field is its Euclidean magnitude:
the normalized cube measure is a probability measure. -/
theorem vecCubeLpENorm_const (Q : TriadicCube d) (q : ℝ≥0∞) (hq : q ≠ 0)
    (c : Vec d) :
    vecCubeLpENorm Q q (fun _ => c) = ENNReal.ofReal (vecNorm c) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  show eLpNorm (fun _ : Vec d => HilbertVec.ofVec c) q (normalizedCubeMeasure Q) =
    ENNReal.ofReal (vecNorm c)
  rw [eLpNorm_const _ hq (NeZero.ne' _).symm]
  rw [measure_univ, ENNReal.one_rpow, mul_one, ← ofReal_norm]
  rfl

theorem hilbertifyVecField_finsetSum {ι : Type*} (s : Finset ι)
    (G : ι → Vec d → Vec d) :
    hilbertifyVecField (fun x => ∑ r ∈ s, G r x) =
      fun x => ∑ r ∈ s, hilbertifyVecField (G r) x := by
  funext x
  exact map_sum (HilbertVec.linearEquivVec d).symm _ _

theorem aestronglyMeasurable_hilbertifyVecField_finsetSum {ι : Type*}
    {Q : TriadicCube d} (s : Finset ι) {G : ι → Vec d → Vec d}
    (hG : ∀ r ∈ s, AEStronglyMeasurable (hilbertifyVecField (G r))
      (normalizedCubeMeasure Q)) :
    AEStronglyMeasurable (hilbertifyVecField (fun x => ∑ r ∈ s, G r x))
      (normalizedCubeMeasure Q) := by
  rw [hilbertifyVecField_finsetSum]
  refine (Finset.aestronglyMeasurable_sum (μ := normalizedCubeMeasure Q) s hG).congr ?_
  filter_upwards with x
  rw [Finset.sum_apply]

/-- **The triangle inequality in `L̲^q(cu_M)` for a finite sum of fields.** -/
theorem vecCubeLpENorm_finsetSum_le {ι : Type*} {Q : TriadicCube d} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (s : Finset ι) {G : ι → Vec d → Vec d}
    (hG : ∀ r ∈ s, AEStronglyMeasurable (hilbertifyVecField (G r))
      (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q q (fun x => ∑ r ∈ s, G r x) ≤
      ∑ r ∈ s, vecCubeLpENorm Q q (G r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [vecCubeLpENorm_zero]
  | insert a t ha ih =>
      have hGa := hG a (Finset.mem_insert_self a t)
      have hGt : ∀ r ∈ t, AEStronglyMeasurable (hilbertifyVecField (G r))
          (normalizedCubeMeasure Q) := fun r hr =>
        hG r (Finset.mem_insert_of_mem hr)
      have hrw : (fun x => ∑ r ∈ insert a t, G r x) =
          fun x => G a x + ∑ r ∈ t, G r x := by
        funext x
        rw [Finset.sum_insert ha]
      rw [hrw, Finset.sum_insert ha]
      refine le_trans (vecCubeLpENorm_add_le hq hGa
        (aestronglyMeasurable_hilbertifyVecField_finsetSum t hGt)) ?_
      exact add_le_add le_rfl (ih hGt)

/-! ## The per-shell display for `r ≥ M` -/

/-- Square integrability of the shell flux gives integrability of each of its
components on the open cube. -/
theorem integrableOn_shellFlux_component (Q : TriadicCube d) (r : ℕ)
    (omega : ShellSeq d) (p : Vec d) (i : Fin d) :
    IntegrableOn (fun x => shellFlux omega r p x i) (openCubeSet Q) volume :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).integrable_comp
    ((memVectorL2_shellFlux Q r omega p).integrable (by norm_num))

/-- **The centered shell flux has zero cube average.**  This is what removes the
average term of `e.abstract.response.ND.weak` in the branch `r ≥ M`. -/
theorem volumeAverageVec_shellFlux_sub_volumeAverage (M : ℕ) (r : ℕ)
    (omega : ShellSeq d) (p : Vec d) :
    volumeAverageVec (cubeSet (originCube d (M : ℤ)))
        (fun x => shellFlux omega r p x - shellFluxAverage (M : ℤ) omega r p) = 0 := by
  funext i
  rw [show volumeAverageVec (cubeSet (originCube d (M : ℤ)))
      (fun x => shellFlux omega r p x - shellFluxAverage (M : ℤ) omega r p) i =
      volumeAverage (cubeSet (originCube d (M : ℤ)))
        (fun x => shellFlux omega r p x i -
          shellFluxAverage (M : ℤ) omega r p i) from rfl,
    volumeAverage_cubeSet_eq_openCubeSet,
    volumeAverage_sub_const (volume_openCubeSet_ne_zero _)
      (volume_openCubeSet_ne_top _)
      (integrableOn_shellFlux_component (originCube d (M : ℤ)) r omega p i)]
  have h2 : volumeAverage (openCubeSet (originCube d (M : ℤ)))
      (fun x => shellFlux omega r p x i) =
      shellFluxAverage (M : ℤ) omega r p i := by
    rw [← volumeAverage_cubeSet_eq_openCubeSet]
    exact congrFun (volumeAverageVec_shellFlux (d := d) (M : ℤ) r omega p) i
  rw [h2]
  simp

/-- **`e.powerofGammasigma` and `e.multGammasig` at the exponents `1/5` and
`4/5`**, without the third additive term: in the branch `r ≥ M` the average
term of `e.abstract.response.ND.weak` is absent, so the product of the two weak
norms is already the whole amplitude. -/
theorem isBigO_gammaSigma_rpow_mul
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {Za Zb : Omega → ℝ} {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hZa : ∀ w, 0 ≤ Za w) (hZb : ∀ w, 0 ≤ Zb w)
    (ha : IsBigO mu (gammaSigma 2) Za A) (hb : IsBigO mu (gammaSigma 2) Zb B) :
    IsBigO mu (gammaSigma 2)
      (fun w => Za w ^ ((1 : ℝ) / 5) * Zb w ^ ((4 : ℝ) / 5))
      (orliczProductConst 10 (5 / 2) *
        (A ^ ((1 : ℝ) / 5) * B ^ ((4 : ℝ) / 5))) := by
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
  have h := isBigO_gammaSigma_mul (mu := mu) (σ₁ := 10) (σ₂ := 5 / 2)
    (by norm_num) (by norm_num) (Real.rpow_nonneg hA.le _)
    (Real.rpow_nonneg hB.le _) h1 h2
  simpa only [show (10 : ℝ) * (5 / 2) / (10 + 5 / 2) = 2 by norm_num] using h

/-- The constant of the printed display, assembled from the
a priori response constant `Cnd` (`e.abstract.response.ND.weak`), the two
centered weak-norm constants `Chm` (the `r ≥ M` form of
`e.jk.Hminus.endpoint`) and `Cl4` (the `L̲⁴` bound of the proof of
`l.LHS.term1`), and the Orlicz product constant of `e.multGammasig`. -/
def shellResponseGapGeConst (Cnd Chm Cl4 : ℝ) : ℝ :=
  Cnd * (orliczProductConst 10 (5 / 2) *
    (Chm ^ ((1 : ℝ) / 5) * Cl4 ^ ((4 : ℝ) / 5)))

/-! ## The summation step `e.wN.wD.with.average.error` -/

theorem aestronglyMeasurable_hilbertifyVecField {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q) := by
  have h : AEStronglyMeasurable (hilbertifyVecField F)
      (volume.restrict (openCubeSet Q)) :=
    (memHilbertVectorL2_hilbertifyVecField hF).aestronglyMeasurable
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact h.smul_measure _

/-- **The summation step.**

By the linearity of the two response problems in the flux the responses of
`Σ_{r ∈ s} j_r p` have, almost everywhere on the cube, the gradients
`Σ_r ∇w̃_r` and `Σ_r ∇w_r`; so for any choice of shift vectors `b_r`,

`∇w̃ − ∇w = Σ_r (∇w̃_r + b_r − ∇w_r) − Σ_r b_r`

almost everywhere, and the triangle inequality in `L̲²(cu_M)` gives the printed
display.  Taking `b_r = 0` for `r < M` and `b_r = (j_r p)_{cu_M}` for `r ≥ M`
is the print's "retaining only the average part of the scales `r ≥ m`": the two
per-shell branches (`r < M` and `r ≥ M`) bound
exactly the terms `‖∇w̃_r + b_r − ∇w_r‖_{L̲²(cu_M)}`. -/
theorem vecCubeLpENorm_grad_sub_le_of_shellBranches {Q : TriadicCube d}
    (s : Finset ℕ) (p : Vec d) (omega : ShellSeq d)
    {wD : H10Function (openCubeSet Q)} {wN : H1MeanZeroFunction (openCubeSet Q)}
    (wDr : ℕ → H10Function (openCubeSet Q))
    (wNr : ℕ → H1MeanZeroFunction (openCubeSet Q))
    (hwD : IsCubeDirichletResponse Q
      (fun x => ∑ r ∈ s, shellFlux omega r p x) wD)
    (hwN : IsCubeNeumannResponse Q
      (fun x => ∑ r ∈ s, shellFlux omega r p x) wN)
    (hwDr : ∀ r ∈ s, IsCubeDirichletResponse Q (shellFlux omega r p) (wDr r))
    (hwNr : ∀ r ∈ s, IsCubeNeumannResponse Q (shellFlux omega r p) (wNr r))
    (b : ℕ → Vec d) (Zgap : ℕ → ℝ) (hZgap0 : ∀ r ∈ s, 0 ≤ Zgap r)
    (hZgapBound : ∀ r ∈ s, vecCubeLpENorm Q 2
      (fun x => (wNr r).toH1Function.grad x + b r -
        (wDr r).toH1Function.grad x) ≤ ENNReal.ofReal (Zgap r)) :
    vecCubeLpENorm Q 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      ENNReal.ofReal ((∑ r ∈ s, Zgap r) + vecNorm (∑ r ∈ s, b r)) := by
  classical
  have hFmem : ∀ r ∈ s, MemVectorL2 (openCubeSet Q) (shellFlux omega r p) :=
    fun r _ => memVectorL2_shellFlux Q r omega p
  have hW := isCubeDirichletResponse_finsetSum (F := fun r => shellFlux omega r p)
    (w := wDr) s hFmem hwDr
  have hV := isCubeNeumannResponse_finsetSum (F := fun r => shellFlux omega r p)
    (w := wNr) s hFmem hwNr
  have haeD := grad_ae_eq_of_isCubeDirichletResponse hwD hW
  have haeN := grad_ae_eq_of_isCubeNeumannResponse hwN hV
  -- the almost-everywhere identification of the gradient gap
  have hae : (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x)
      =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => (∑ r ∈ s, ((wNr r).toH1Function.grad x + b r -
        (wDr r).toH1Function.grad x)) + (-(∑ r ∈ s, b r)) := by
    filter_upwards [haeD, haeN] with x hxD hxN
    rw [hxD, hxN, h10FinsetSum_grad, h1MeanZeroFinsetSum_grad]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    abel
  rw [vecCubeLpENorm_congr_openCubeSet_ae hae]
  -- the triangle inequality
  have hmem : ∀ r ∈ s, MemVectorL2 (openCubeSet Q)
      (fun x => (wNr r).toH1Function.grad x + b r -
        (wDr r).toH1Function.grad x) := fun r _ =>
    ((wNr r).toH1Function.grad_memVectorL2.add (memVectorL2_const (b r))).sub
      (wDr r).toH1Function.grad_memVectorL2
  have hsumMem : MemVectorL2 (openCubeSet Q)
      (fun x => ∑ r ∈ s, ((wNr r).toH1Function.grad x + b r -
        (wDr r).toH1Function.grad x)) := by
    refine memVectorL2_finsetSum (F := fun r x => (wNr r).toH1Function.grad x +
      b r - (wDr r).toH1Function.grad x) s hmem
  have hstep := vecCubeLpENorm_add_le (Q := Q) (q := 2) (one_le_two)
    (aestronglyMeasurable_hilbertifyVecField hsumMem)
    (aestronglyMeasurable_hilbertifyVecField
      (memVectorL2_const (-(∑ r ∈ s, b r))))
  refine le_trans hstep ?_
  have hconst : vecCubeLpENorm Q 2 (fun _ : Vec d => -(∑ r ∈ s, b r)) =
      ENNReal.ofReal (vecNorm (∑ r ∈ s, b r)) := by
    rw [show (fun _ : Vec d => -(∑ r ∈ s, b r)) =
        fun x => -((fun _ : Vec d => ∑ r ∈ s, b r) x) from rfl,
      vecCubeLpENorm_neg, vecCubeLpENorm_const Q 2 (by norm_num)]
  have htri := vecCubeLpENorm_finsetSum_le (Q := Q) (q := 2) (one_le_two) s
    (G := fun r x => (wNr r).toH1Function.grad x + b r -
      (wDr r).toH1Function.grad x)
    (fun r hr => aestronglyMeasurable_hilbertifyVecField (hmem r hr))
  have hsumle : ∑ r ∈ s, vecCubeLpENorm Q 2
      (fun x => (wNr r).toH1Function.grad x + b r -
        (wDr r).toH1Function.grad x) ≤
      ENNReal.ofReal (∑ r ∈ s, Zgap r) := by
    refine le_trans (Finset.sum_le_sum hZgapBound) ?_
    exact le_of_eq (ENNReal.ofReal_sum_of_nonneg hZgap0).symm
  rw [hconst, ENNReal.ofReal_add (Finset.sum_nonneg hZgap0)
    (vecNorm_nonneg _)]
  exact add_le_add (le_trans htri hsumle) le_rfl

/-! ## Matrix-vector multiplication and finite sums -/

/-- Matrix-vector multiplication is additive in a finite sum of matrices. -/
theorem matVecMul_finsetSum {ι : Type*} (s : Finset ι) (A : ι → Mat d)
    (p : Vec d) :
    matVecMul (∑ r ∈ s, A r) p = ∑ r ∈ s, matVecMul (A r) p := by
  funext i
  simp only [matVecMul, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **The shell decomposition of the flux**:
`(k_m − k_n)p = Σ_{r = n+1}^{m} j_r p`. -/
theorem matVecMul_streamCutoff_sub_eq_sum_shellFlux (omega : ShellSeq d)
    {n m : ℕ} (hnm : n ≤ m) (p : Vec d) (x : Vec d) :
    matVecMul (streamCutoff omega m x - streamCutoff omega n x) p =
      ∑ r ∈ Finset.Ioc n m, shellFlux omega r p x := by
  rw [← finiteShellIncrement_apply_eq_streamCutoff_sub omega hnm x,
    finiteShellIncrement, RegCoeffField.finset_sum_apply, matVecMul_finsetSum]
  rfl

end

end SuperdiffusionCLT.Section3.Setup
