/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2MeasurabilityB
public import SuperdiffusionCLT.Section3.Terms.EllsepDriftB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm4Anchors

/-!
# The weak gradient of the transported field `R = (k_{L'} − k_ℓ) ∇w`

The display `e.RHS.term2.R.bounds` is reached in the paper by "Combining this with
`e.nablaw.Lt` and the product rule gives": the Jacobian `∇R` of the transported field
`R = (k_{L'} − k_ℓ)ᵗ∇w` exists weakly on `cu_m` and is the
product-rule sum `(∇(k_{L'} − k_ℓ))∇w + (k_{L'} − k_ℓ)∇²w`.

This module proves the two weak-gradient statements about the response flux `R` that
the proof of `l.RHS.term2` needs:

* item 1 — a field `DR : ShellSeq d → Fin d → Vec d → Vec d` that is a weak
  gradient of `R` on `cu_m`, component by component; and
* item 2 — the square-integrability of its Jacobian, read as a `HilbertMat`
  field against the restricted volume measure of `cu_m`.

## The route

Everything needed is already available:

* the coefficient difference
  `(coefficientCutoff nu omega L').toCoeffField − (coefficientCutoff nu omega ℓ).toCoeffField`
  is the stream increment `k_{L'} − k_ℓ` (`coefficientCutoff_toCoeffField_sub_streamCutoff`
  below; the common `ν Id` summand cancels), which is of class `C¹`
  (`contDiff_streamCutoff_sub_entry`);
* the weak product rule for `x ↦ K x ∇u` with `K` of class `C¹` and `u` carrying
  a weak Hessian is available
  (`Section3/Terms/EllsepDrift.hasWeakJacobianOn_matVecMul_of_contDiff_one`), and
  `EllsepDriftB.streamGradJacobian` is the Jacobian it produces for the stream
  increment, with its `L̲²(cu_m)` coordinatewise integrability
  (`gradMemL2On_streamGradJacobian`);
* a weak Hessian of the Dirichlet response `w` is constructed per sample by
  `Section3/Terms/RHSTerm4Anchors.exists_hasWeakHessianOn_of_isDirichletResponse`
  from the divergence-form Calderón-Zygmund endpoint at the exponent `2`;
  the `L̲²` membership of its entries is part of the `HasWeakHessianOn`
  structure itself, so no a priori anchor is consumed here.

The Jacobian of `R` is then assembled pointwise as

`∂_k (K∇w)_i = ∑_j ((∂_k K_{ij}) ∂_j w + K_{ij} ∂_k∂_j w)`,

exactly the printed product rule; the entries being `L̲²` coordinatewise and
finitely many, the `HilbertMat`-carrier Jacobian is `L̲²` by the pi-type
`L^p` criterion composed with the continuous linear identification
`HilbertMat.continuousLinearEquivMat`.

No norm bound and no finiteness or measurability clause is
attempted here.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The cutoff difference in stream form -/

/-- The difference of the two cutoff coefficient fields is the difference of the
two stream fields: the common constant summand `ν Id` of the infrared cutoff
cancels, and no ordering of the two scales is needed. -/
theorem coefficientCutoff_toCoeffField_sub_streamCutoff (nu : ℝ) (omega : ShellSeq d)
    (a b : ℕ) (x : Vec d) :
    (coefficientCutoff nu omega b).toCoeffField x -
        (coefficientCutoff nu omega a).toCoeffField x =
      streamCutoff omega b x - streamCutoff omega a x := by
  simp only [coefficientCutoff, RegCoeffField.toCoeffField_apply,
    RegCoeffField.add_apply, RegCoeffField.constRegCoeffField_apply]
  abel

/-- The two scales of `e.scales.ordering` that the stream increment needs: the
large scale `L'` exceeds the low shell `ℓ`, and it exceeds the intermediate
shell `ℓ'` of the response equation. -/
theorem ell_le_LPrime_of_scalesOrdering {S : ScaleSelection}
    (hSorder : ScalesOrdering S) : S.ell ≤ S.LPrime := by
  have h1 := hSorder.ell_lt_ellPrime
  have h2 := hSorder.ellPrime_lt_m
  have h3 := hSorder.m_lt_LPrime
  omega

theorem ellPrime_le_LPrime_of_scalesOrdering {S : ScaleSelection}
    (hSorder : ScalesOrdering S) : S.ellPrime ≤ S.LPrime := by
  have h1 := hSorder.ell_lt_ellPrime
  have h2 := hSorder.ellPrime_lt_m
  have h3 := hSorder.m_lt_LPrime
  omega

/-! ## The weak gradient and its `L²` Jacobian -/

/-- **The weak Jacobian of `R = (k_{L'} − k_ℓ) ∇w`**, the product rule:
for a weak-Hessian witness `H` of the response, sample by sample, the
`k`-th weak derivative of the `i`-th component of
`R = (k_{L'} − k_ℓ) ∇w` is
`∑_j ((k_{L'} − k_ℓ)_{ij} ∂_k∂_j w + ∂_j w (∂_k (k_{L'} − k_ℓ))_{ij})`.

This is the Jacobian `EllsepDriftB.streamGradJacobian` of the stream
increment applied to the gradient of the response; it is *defined* here with
the two scales of `e.scale.selection` to fix the `DR` the reduction
consumes. -/
def rfieldWeakJacobian (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (H : ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ))) (w omega).toH1Function) :
    ShellSeq d → Fin d → Vec d → Vec d :=
  fun omega => streamGradJacobian omega S.ell S.LPrime (H omega)

/-- **The weak-gradient datum.** With a weak-Hessian witness of
the response chosen per sample, every component of
`R = (k_{L'} − k_ℓ) ∇w` has the weak gradient `rfieldWeakJacobian` on `cu_m`.
The proof is the weak product rule
`hasWeakJacobianOn_matVecMul_of_contDiff_one` for the `C¹` stream increment,
read through `hasWeakJacobianOn_streamGradJacobian` and the cancellation of the
common `ν Id` summand of the two cutoffs. -/
theorem rfieldWeakJacobian_hasWeakGradientOn (nu : ℝ) (S : ScaleSelection)
    (hSorder : ScalesOrdering S)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (H : ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ))) (w omega).toH1Function) :
    ∀ (omega : ShellSeq d) (i : Fin d),
      HasWeakGradientOn (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
              (coefficientCutoff nu omega S.ell).toCoeffField x)
            ((w omega).toH1Function.grad x)) i)
        (rfieldWeakJacobian S w H omega i) := by
  intro omega i
  have hK : (fun x : Vec d =>
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
            (coefficientCutoff nu omega S.ell).toCoeffField x)
          ((w omega).toH1Function.grad x)) i)
      = fun x : Vec d =>
        (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
          ((w omega).toH1Function.grad x)) i := by
    funext x
    exact congrArg (fun A => matVecMul A ((w omega).toH1Function.grad x) i)
      (coefficientCutoff_toCoeffField_sub_streamCutoff nu omega S.ell S.LPrime x)
  rw [hK]
  unfold rfieldWeakJacobian
  exact hasWeakJacobianOn_streamGradJacobian omega
    (ell_le_LPrime_of_scalesOrdering hSorder) (H omega) i

/-- **The `L²` Jacobian.** For a fixed sample, the Jacobian
`rfieldWeakJacobian` read as a `HilbertMat` field over `cu_m` against the
restricted volume measure is square-integrable.  Each of its `d²` entries is
`L̲²(cu_m)` (`gradMemL2On_streamGradJacobian`, through the `L̲²` membership of
the weak-Hessian entries and of `∇w`), so the pi-type `L^p` criterion
(`MeasureTheory.memLp_pi_iff`, read twice on `Mat d = Fin d → Fin d → ℝ`)
assembles the `Mat`-valued field, and the continuous linear identification
`HilbertMat.continuousLinearEquivMat` carries it to the `HilbertMat` carrier. -/
theorem memLp_rfieldWeakJacobian (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (H : ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ))) (w omega).toH1Function)
    (omega : ShellSeq d) :
    MemLp (fun x => HilbertMat.ofMat (fun i j => rfieldWeakJacobian S w H omega i x j)) 2
      (volume.restrict (openCubeSet (originCube d (S.m : ℤ)))) := by
  have hellell := ell_le_LPrime_of_scalesOrdering hSorder
  have hEnt : ∀ i j : Fin d,
      MemLp (fun x : Vec d => rfieldWeakJacobian S w H omega i x j) 2
        (volume.restrict (openCubeSet (originCube d (S.m : ℤ)))) :=
    fun i j => gradMemL2On_streamGradJacobian omega hellell (H omega) i j
  have hMat : MemLp (fun x : Vec d =>
      (fun i j : Fin d => rfieldWeakJacobian S w H omega i x j : Mat d)) 2
      (volume.restrict (openCubeSet (originCube d (S.m : ℤ)))) :=
    MeasureTheory.MemLp.of_eval fun i =>
      MeasureTheory.MemLp.of_eval fun j => hEnt i j
  exact (HilbertMat.continuousLinearEquivMat d).symm.toContinuousLinearMap.comp_memLp' hMat

/-- **The two weak-gradient statements for `R`, at the statement's own
data.**  These are: the weak-gradient field `DR` of `R = (k_{L'} − k_ℓ)ᵗ∇w` on `cu_m`
and the `L²` membership of its Jacobian read as a `HilbertMat` field.  The other
requirements on `R` (the two annealed-norm finiteness clauses, the two measurability
clauses and the display `e.RHS.term2.R.bounds`) and the remaining ingredients of the proof
of `l.RHS.term2` are not addressed here.

The weak-Hessian witness of the response is constructed per sample from the
divergence-form Calderón-Zygmund endpoint at the exponent `2`
(`exists_hasWeakHessianOn_of_isDirichletResponse`). -/
theorem exists_rfieldWeakJacobian (d : ℕ) [NeZero d] (hd : 2 ≤ d) (nu : ℝ)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (p : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    ∃ DR : ShellSeq d → Fin d → Vec d → Vec d,
      (∀ (omega : ShellSeq d) (i : Fin d),
        HasWeakGradientOn (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                (coefficientCutoff nu omega S.ell).toCoeffField x)
              ((w omega).toH1Function.grad x)) i) (DR omega i)) ∧
      (∀ omega : ShellSeq d,
        MemLp (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) 2
          (volume.restrict (openCubeSet (originCube d (S.m : ℤ))))) := by
  have hellPrimeLPrime := ellPrime_le_LPrime_of_scalesOrdering hSorder
  have H : ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ))) (w omega).toH1Function :=
    fun omega =>
      Classical.choice (exists_hasWeakHessianOn_of_isDirichletResponse hd omega
        hellPrimeLPrime p (w omega) (hw omega))
  exact ⟨rfieldWeakJacobian S w H,
    rfieldWeakJacobian_hasWeakGradientOn nu S hSorder w H,
    fun omega => memLp_rfieldWeakJacobian S hSorder w H omega⟩

end

end SuperdiffusionCLT.Section3.Terms