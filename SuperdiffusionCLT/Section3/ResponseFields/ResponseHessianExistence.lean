/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.DirichletResponse
public import SuperdiffusionCLT.Section3.ResponseFields.Regbounds
public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates
public import SuperdiffusionCLT.Sobolev.DirichletW2pDivergence

/-!
# The weak Hessian of the Dirichlet response `w` of `e.def.w`

The paper defines the Dirichlet response
`w ∈ H²(cu_m)` of `e.def.w` as the zero-trace weak solution of

`−Δw = ∇·((k_{L'} − k_{ℓ'}) p)` in `cu_m`.

Downstream reductions of the Section 3 statements quantify over a weak
Hessian of `w`, `HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
(w omega).toH1Function` for every `omega`, and need it *produced*, not assumed:
the statement of `l.w.basic.regbounds` carries the binder
`HD : ∀ omega, HasWeakHessianOn …` as a hypothesis of its Hessian clause, and a
consumer of that statement has to choose one.

## The route

The response `w omega` of `e.def.w` is the Dirichlet response, in the sense of
`Section3/ResponseFields/Definitions.IsCubeDirichletResponse`, of the flux

`F = (k_{L'} − k_{ℓ'}) p = fun x => matVecMul (streamCutoff omega LPrime x -
  streamCutoff omega ellPrime x) p`

on the open cube `openCubeSet (originCube d m)`; the identification is
`Setup.isDirichletResponse_iff_isCubeDirichletResponse` (`Iff.rfl`), and the
flux field is exactly `Setup.dirichletRhsField`.

The divergence-form Calderón-Zygmund endpoint
`Sobolev/DirichletW2pDivergence.exists_cubeDirichletResponseHessianLpEstimate`
produces a weak Hessian of every Dirichlet response of a flux whose weak
Jacobian is `L̲² ∩ L̲^p`.  Its four data hypotheses are supplied at this flux:

* `F` is continuous (`Setup.continuous_dirichletRhsField`), hence
  `MemLp F 2` against the normalized cube measure — continuity plus boundedness
  on the cube, the private bridge below.
* the weak Jacobian is the classical one `streamFluxWeakGradient
  omega ellPrime LPrime p`, a weak gradient because
  the flux is `C¹` (`hasWeakGradientOn_streamFluxWeakGradient`);
* that Jacobian is continuous as a `HilbertMat`-valued field
  (`Regbounds.continuous_streamFluxJacobian`), hence `MemLp` at every
  exponent, in particular at `2`.

No `L̲^p` finiteness beyond continuity on the bounded cube is used, and the
ordering hypothesis is `ℓ' ≤ L'`, available from the defining relations of the
scale selection alone (`ScaleSelection.ellPrime_add_h` and `ScaleSelection.LPrime_eq`).

## Main results

* `exists_hasWeakHessianOn_dirichletResponse`: for every shell sequence, every
  ordered pair of cutoff levels, every cube index, every vector and every
  response `w` of the flux `(k_{L'} − k_{ℓ'})p`, a weak Hessian of `w` exists.
* `exists_hasWeakHessianOn_dirichletResponse_family`: the binder of the
  statement of `l.w.basic.regbounds`, produced: for a scale selection `S` and a family `w omega` of
  responses, the family of weak Hessians `HD : ∀ omega, HasWeakHessianOn …`
  exists, in the `Nonempty` form from which `Classical.choice` extracts it.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.ResponseFields

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Sobolev
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-! ## `L^q` data from continuity on a cube -/

/-- A continuous field of any normed carrier lies in every `L^q` of an open
triadic cube: the cube sits in a compact ball on which the field is bounded and
has finite measure. -/
private theorem memLp_openCubeSet_of_continuous {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {q : ℝ≥0∞} {f : Vec d → E} (hf : Continuous f) :
    MemLp f q (volume.restrict (openCubeSet Q)) := by
  have hsub : openCubeSet Q ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
    rw [← ball_cubeCenter_eq_openCubeSet Q]
    exact Metric.ball_subset_closedBall
  have hK : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    ProperSpace.isCompact_closedBall _ _
  have hbdd : BddAbove ((fun y : Vec d => ‖f y‖) ''
      Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    hK.bddAbove_image hf.norm.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable
    (sSup ((fun y : Vec d => ‖f y‖) ''
      Metric.closedBall (cubeCenter Q) (cubeRadius Q))) ?_
  filter_upwards
    [MeasureTheory.ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with y hy
  exact le_csSup hbdd (Set.mem_image_of_mem _ (hsub hy))

/-- The same against the normalized cube measure, which differs from the
restricted volume by one finite factor. -/
private theorem memLp_normalizedCubeMeasure_of_continuous {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) {q : ℝ≥0∞} {f : Vec d → E}
    (hf : Continuous f) : MemLp f q (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact (memLp_openCubeSet_of_continuous Q hf).smul_measure ENNReal.ofReal_ne_top

/-! ## The weak Hessian of the response of `e.def.w` -/

/-- **The Dirichlet response of `e.def.w` carries a weak Hessian.** The flux
`F = (k_{L'} − k_{ℓ'})p` is `C¹` with the classical Jacobian
`streamFluxWeakGradient`, and both are bounded on the cube, so the
divergence-form Calderón-Zygmund endpoint of
`Sobolev/DirichletW2pDivergence.lean` at the exponent `2` produces a
`HasWeakHessianOn` witness for `w`.  Nothing is assumed beyond the response
equation `e.def.w` and the ordering `ℓ' ≤ L'` of the cutoff levels. -/
theorem exists_hasWeakHessianOn_dirichletResponse (hd : 2 ≤ d)
    (omega : ShellSeq d) {LPrime ellPrime m : ℕ} (hab : ellPrime ≤ LPrime)
    (p : Vec d) (w : H10Function (openCubeSet (originCube d (m : ℤ))))
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    Nonempty (HasWeakHessianOn (openCubeSet (originCube d (m : ℤ)))
      w.toH1Function) := by
  obtain ⟨_C, _hCtop, hC⟩ :=
    exists_cubeDirichletResponseHessianLpEstimate hd 2 (by norm_num) (by norm_num)
  have hflux : Continuous (dirichletRhsField omega LPrime ellPrime p) :=
    continuous_dirichletRhsField omega LPrime ellPrime p
  obtain ⟨H, _, _⟩ := hC (m : ℤ)
    (dirichletRhsField omega LPrime ellPrime p)
    (streamFluxWeakGradient omega ellPrime LPrime p)
    (memLp_normalizedCubeMeasure_of_continuous _ hflux)
    (fun i => hasWeakGradientOn_streamFluxWeakGradient omega hab p i
      (openCubeSet (originCube d (m : ℤ))))
    (memLp_normalizedCubeMeasure_of_continuous _
      (continuous_streamFluxJacobian omega hab p))
    (memLp_normalizedCubeMeasure_of_continuous _
      (continuous_streamFluxJacobian omega hab p))
    w ((isDirichletResponse_iff_isCubeDirichletResponse omega LPrime ellPrime m p
      w).mp hw)
  exact ⟨H⟩

/-! ## The weak-Hessian binder of `l.w.basic.regbounds` -/

/-- **The weak-Hessian binder of `l.w.basic.regbounds`.** For
a family `w omega` of Dirichlet responses of `e.def.w` on `cu_m` at the scales
of a scale selection, the family
`HD : ∀ omega, HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
(w omega).toH1Function` exists, in the `Nonempty` form from which
`Classical.choice` extracts the binder. -/
theorem exists_hasWeakHessianOn_dirichletResponse_family (hd : 2 ≤ d)
    (S : ScaleSelection) (p : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    Nonempty (∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
        (w omega).toH1Function) := by
  have hab : S.ellPrime ≤ S.LPrime := by
    have h1 := S.ellPrime_add_h
    have h2 := S.LPrime_eq
    omega
  exact ⟨fun omega =>
    Classical.choice (exists_hasWeakHessianOn_dirichletResponse hd omega hab p
      (w omega) (hw omega))⟩

end