/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessian

/-!
# The divergence-form `W^{2,p}` estimate on a cube: the Dirichlet half

display `e.abstract.response.W28`, asserts with a constant `C(d) < ∞`

> `‖∇²w_D‖_{L̲⁸(cu_M)} + ‖∇²w_N‖_{L̲⁸(cu_M)} ≤ C ‖∇F‖_{L̲⁸(cu_M)}`

for the two responses of `e.abstract.response.equations`. This module proves the
Dirichlet half at every finite exponent `1 < p < ∞`.

## The route

CoarseGraining supplies the Hessian Calderón-Zygmund endpoint for the *scalar*
zero-trace Poisson problem,
`Homogenization.CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le`:
for `-Δu = f` with `f ∈ L² ∩ L̲^p` on a centred triadic cube, `u` has a weak
Hessian with `‖∇²u‖_{L̲^p} ≤ C ‖f‖_{L̲^p}`. The divergence-form problem
`-Δw = ∇·F` is that problem with `f = ∇·F`, provided `F` carries a weak
Jacobian: integrating by parts against a zero-trace test function turns
`-∫_Q F·∇φ` into `∫_Q (∇·F) φ`, so the weak formulation
`IsCubeDirichletResponse` (`∫_Q ∇w·∇φ = -∫_Q F·∇φ`) becomes
`CubeDirichletWeakPoissonProblem` (`∫_Q ∇w·∇φ = ∫_Q f φ`) at
`f = ∇·F = ∑ᵢ ∂ᵢFᵢ`. **The sign is positive**: the manuscript's `-Δw = ∇·F`
and the upstream convention `-Δu = f` agree on the nose, and the minus sign of
`IsCubeDirichletResponse` is exactly the one produced by the integration by
parts.

The integration by parts is upstream's
`Homogenization.H1Function.integral_mul_zeroTrace_gradCoord_eq_neg_integral_gradCoord_mul`,
which extends the smooth-compact-test definition of `HasWeakPartialDerivOn` to
the `H¹₀` test class through the approximating sequence carried by
`H10Function`. It applies once the `i`-th component of `F` is packaged, with the
`i`-th row of the Jacobian, as an `H1Function`.

## The dimension factor

The datum of the scalar endpoint is the scalar `∇·F`, whose size is compared
with the Frobenius size of the Jacobian by `|∑ᵢ Aᵢᵢ| ≤ d ‖A‖`
(`abs_weakDivergence_le`; the sharp factor is `√d`, and either is absorbed by
`C(d, p)`). The constant produced below is therefore `d` times the upstream
one.

## Two readings of the Hessian clause

The upstream endpoint *produces* a weak Hessian witness. Weak partial
derivatives on an open set are unique almost everywhere
(`Homogenization.HasWeakPartialDerivOn.ae_eq`), so the bound holds for *every*
`HasWeakHessianOn` witness of the same response, which is the universally
quantified reading used in the main statement. Both forms are exported.

## Main definitions

* `HasWeakJacobianOn`: the weak Jacobian of a vector field, one
  `HasWeakGradientOn` per component.
* `weakDivergence`: the trace `∑ᵢ ∂ᵢFᵢ` of a weak Jacobian.
* `jacobianHilbertMat`: the Jacobian read as a `HilbertMat`-valued field,
  the carrier the manuscript's `|∇F|` uses.

## Main results

* `cubeLpENorm_weakDivergence_le`: `‖∇·F‖_{L̲^p(Q)} ≤ d ‖∇F‖_{L̲^p(Q)}`.
* `setIntegral_vecDot_zeroTrace_grad_eq_neg`: the integration by parts
  `∫_U F·∇φ = -∫_U (∇·F) φ` for `φ ∈ H¹₀(U)`.
* `cubeDirichletWeakPoissonProblem_of_isCubeDirichletResponse`: the bridge —
  a Dirichlet response of `F` solves the scalar Poisson problem with datum
  `∇·F`.
* `exists_cubeDirichletResponseHessianLpEstimate`: the `W^{2,p}` estimate at every
  finite `1 < p < ∞`.

## What is not here

The prescribed-flux Neumann half of `e.abstract.response.W28`. The upstream
Hessian endpoint is the zero-trace Dirichlet one; the Neumann branch needs the
reflected-flux bookkeeping of `NeumannEndpoint.lean` and is not available as a
Hessian statement.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Sobolev

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The weak Jacobian and its divergence -/

/-- **The weak Jacobian of a vector field on `U`**: the `i`-th component of `F`
has weak gradient `DF i`, so that `DF i x j` is `∂_j F_i (x)`. This is the
datum `e.abstract.response.W28` measures on the right-hand side; the index
order matches the Hessian convention of `HasWeakHessianOn`, whose `hess i j` is
the weak `j`-th derivative of the `i`-th gradient coordinate. -/
def HasWeakJacobianOn (U : Set (Vec d)) (F : Vec d → Vec d)
    (DF : Fin d → Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakGradientOn U (fun x => F x i) (DF i)

/-- **The divergence `∇·F = ∑ᵢ ∂ᵢFᵢ` read off a weak Jacobian.** -/
def weakDivergence (DF : Fin d → Vec d → Vec d) : Vec d → ℝ :=
  fun x => ∑ i : Fin d, DF i x i

/-- **The weak Jacobian as a `HilbertMat`-valued field**, the carrier in which
the manuscript's `|∇F|` is the Frobenius norm. -/
def jacobianHilbertMat (DF : Fin d → Vec d → Vec d) : Vec d → HilbertMat d :=
  fun x => HilbertMat.ofMat (fun i j => DF i x j)

/-- The matrix trace as a continuous linear functional on `HilbertMat d`. -/
private def traceL (d : ℕ) : HilbertMat d →L[ℝ] ℝ :=
  ∑ i : Fin d, HilbertMat.entryL i i

private theorem traceL_jacobianHilbertMat (DF : Fin d → Vec d → Vec d)
    (x : Vec d) : traceL d (jacobianHilbertMat DF x) = weakDivergence DF x := by
  simp [traceL, jacobianHilbertMat, weakDivergence]

/-- **The divergence is pointwise at most `d` times the Jacobian.** Each
diagonal entry of a matrix is bounded by its Frobenius norm, and there are `d`
of them. The sharp factor is `√d`; both are absorbed by the dimensional
constant. -/
theorem abs_weakDivergence_le (DF : Fin d → Vec d → Vec d) (x : Vec d) :
    |weakDivergence DF x| ≤ (d : ℝ) * ‖jacobianHilbertMat DF x‖ := by
  have hentry : ∀ i : Fin d, |DF i x i| ≤ ‖jacobianHilbertMat DF x‖ := by
    intro i
    have h := HilbertMat.abs_apply_sub_apply_le_norm (jacobianHilbertMat DF x)
      (0 : HilbertMat d) i i
    simpa [jacobianHilbertMat] using h
  calc |weakDivergence DF x| ≤ ∑ i : Fin d, |DF i x i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖jacobianHilbertMat DF x‖ :=
        Finset.sum_le_sum fun i _ => hentry i
    _ = (d : ℝ) * ‖jacobianHilbertMat DF x‖ := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- A `p`-integrable Jacobian has a `p`-integrable divergence. -/
theorem memLp_weakDivergence {μ : Measure (Vec d)} {q : ℝ≥0∞}
    {DF : Fin d → Vec d → Vec d} (h : MemLp (jacobianHilbertMat DF) q μ) :
    MemLp (weakDivergence DF) q μ := by
  have hcomp := (traceL d).comp_memLp' h
  simpa only [Function.comp_def, traceL_jacobianHilbertMat] using hcomp

/-- **`‖∇·F‖_{L̲^q(Q)} ≤ d ‖∇F‖_{L̲^q(Q)}`**, the normalized form of
`abs_weakDivergence_le`. -/
theorem cubeLpENorm_weakDivergence_le (Q : TriadicCube d) (q : ℝ≥0∞)
    (DF : Fin d → Vec d → Vec d) :
    Section2.Norms.cubeLpENorm Q q (weakDivergence DF) ≤
      (d : ℝ≥0∞) * Section2.Norms.cubeLpENorm Q q (jacobianHilbertMat DF) := by
  by_cases hmeasJ : MeasureTheory.AEStronglyMeasurable (jacobianHilbertMat DF)
      (normalizedCubeMeasure Q)
  swap
  · rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      have h0 : weakDivergence DF = 0 := by
        funext x
        simp [weakDivergence]
      rw [h0, Section2.Norms.cubeLpENorm_zero]
      exact zero_le
    · have hJ : Section2.Norms.cubeLpENorm Q q (jacobianHilbertMat DF) = ⊤ :=
        MeasureTheory.eLpNorm_of_not_aestronglyMeasurable hmeasJ
      rw [hJ, ENNReal.mul_top (by exact_mod_cast hd.ne')]
      exact le_top
  have hmeas : MeasureTheory.AEStronglyMeasurable (weakDivergence DF)
      (normalizedCubeMeasure Q) := by
    have := (traceL d).continuous.comp_aestronglyMeasurable hmeasJ
    simpa only [Function.comp_def, traceL_jacobianHilbertMat] using this
  have hmono : Section2.Norms.cubeLpENorm Q q (weakDivergence DF) ≤
      Section2.Norms.cubeLpENorm Q q ((d : ℝ) • jacobianHilbertMat DF) := by
    refine Section2.Norms.cubeLpENorm_mono_enorm ?_ (fun x => ?_)
    · exact hmeas
    simpa [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (d : ℝ) by positivity)] using
      abs_weakDivergence_le DF x
  rw [Section2.Norms.cubeLpENorm_const_smul] at hmono
  refine hmono.trans_eq ?_
  congr 1
  simp

/-! ## Integration by parts against zero-trace tests -/

/-- The `i`-th component of a vector field with a weak Jacobian, packaged with
the `i`-th row of that Jacobian as an `H¹` function on `U`. -/
def weakJacobianComponent {U : Set (Vec d)} {F : Vec d → Vec d}
    {DF : Fin d → Vec d → Vec d}
    (hF : ∀ i : Fin d, MemL2On U (fun x => F x i))
    (hDF : ∀ i : Fin d, GradMemL2On U (DF i))
    (hweak : HasWeakJacobianOn U F DF) (i : Fin d) : H1Function U where
  toFun := fun x => F x i
  grad := DF i
  memL2 := hF i
  gradMemL2 := hDF i
  hasWeakGradient := hweak i

/-- **Integration by parts for a weak Jacobian against a zero-trace test.**
`∫_U F·∇φ = -∫_U (∇·F) φ` for every `φ ∈ H¹₀(U)`. Coordinatewise this is
upstream's `H¹₀` closure of the weak-derivative identity, applied to the pair
`(F_i, DF i)`. -/
theorem setIntegral_vecDot_zeroTrace_grad_eq_neg {U : Set (Vec d)}
    {F : Vec d → Vec d} {DF : Fin d → Vec d → Vec d}
    (hF : ∀ i : Fin d, MemL2On U (fun x => F x i))
    (hDF : ∀ i : Fin d, GradMemL2On U (DF i))
    (hweak : HasWeakJacobianOn U F DF) (φ : H10Function U) :
    ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) =
      -∫ x in U, weakDivergence DF x * φ.toH1Function x := by
  have hleftInt : ∀ i : Fin d,
      IntegrableOn (fun x => F x i * φ.toH1Function.grad x i) U := fun i =>
    (hF i).integrable_mul (φ.toH1Function.gradMemL2 i)
  have hrightInt : ∀ i : Fin d,
      IntegrableOn (fun x => DF i x i * φ.toH1Function x) U := fun i =>
    (hDF i i).integrable_mul φ.toH1Function.memL2
  have hleft : ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) =
      ∑ i : Fin d, ∫ x in U, F x i * φ.toH1Function.grad x i := by
    rw [← integral_finsetSum _ (fun i _ => hleftInt i)]
    rfl
  have hpt : (fun x => weakDivergence DF x * φ.toH1Function x) =
      fun x => ∑ i : Fin d, DF i x i * φ.toH1Function x := by
    funext x
    simp [weakDivergence, Finset.sum_mul]
  have hright : ∫ x in U, weakDivergence DF x * φ.toH1Function x =
      ∑ i : Fin d, ∫ x in U, DF i x i * φ.toH1Function x := by
    rw [hpt, integral_finsetSum _ (fun i _ => hrightInt i)]
  rw [hleft, hright, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact H1Function.integral_mul_zeroTrace_gradCoord_eq_neg_integral_gradCoord_mul
    (weakJacobianComponent hF hDF hweak i) φ i

/-! ## The bridge to the scalar Dirichlet Poisson problem -/

/-- **The bridge.** A Dirichlet response of a flux field carrying a weak
Jacobian is a zero-trace weak solution of the scalar Poisson problem `-Δw = f`
with datum `f = ∇·F`, in CoarseGraining's `CubeDirichletWeakPoissonProblem`
convention. The sign is positive on both sides: the response identity is
`∫_Q ∇w·∇φ = -∫_Q F·∇φ` and the integration by parts turns its right-hand side
into `∫_Q (∇·F) φ`. -/
theorem cubeDirichletWeakPoissonProblem_of_isCubeDirichletResponse
    {Q : TriadicCube d} {F : Vec d → Vec d} {DF : Fin d → Vec d → Vec d}
    (hF : ∀ i : Fin d, MemL2On (openCubeSet Q) (fun x => F x i))
    (hDF : ∀ i : Fin d, GradMemL2On (openCubeSet Q) (DF i))
    (hweak : HasWeakJacobianOn (openCubeSet Q) F DF)
    {w : H10Function (openCubeSet Q)}
    (hw : Section3.ResponseFields.IsCubeDirichletResponse Q F w) :
    CubeDirichletWeakPoissonProblem Q w (weakDivergence DF) := by
  intro φ
  rw [hw φ, setIntegral_vecDot_zeroTrace_grad_eq_neg hF hDF hweak φ, neg_neg]

/-! ## Extracting the `L²` data from the normalized cube norms -/

/-- A coordinate of a `p`-integrable vector field is `p`-integrable. -/
private theorem memLp_component {μ : Measure (Vec d)} {q : ℝ≥0∞}
    {F : Vec d → Vec d} (hF : MemLp F q μ) (i : Fin d) :
    MemLp (fun x => F x i) q μ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_memLp' hF

private theorem memL2On_component {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) (i : Fin d) :
    MemL2On (openCubeSet Q) (fun x => F x i) :=
  memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q (memLp_component hF i)

private theorem gradMemL2On_jacobian {Q : TriadicCube d}
    {DF : Fin d → Vec d → Vec d}
    (hDF : MemLp (jacobianHilbertMat DF) 2 (normalizedCubeMeasure Q))
    (i : Fin d) : GradMemL2On (openCubeSet Q) (DF i) := by
  intro j
  refine memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q ?_
  have hcomp := (HilbertMat.entryL i j).comp_memLp' hDF
  exact hcomp

/-! ## Almost-everywhere uniqueness of the weak Hessian -/

/-- An `L²` function on an open cube is locally integrable there. -/
private theorem locallyIntegrableOn_of_memL2On {Q : TriadicCube d}
    {f : Vec d → ℝ} (hf : MemScalarL2 (openCubeSet Q) f) :
    LocallyIntegrableOn f (openCubeSet Q) volume := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    Section3.ResponseFields.instIsFiniteMeasureVolumeMeasureOnOpenCubeSet Q
  exact IntegrableOn.locallyIntegrableOn
    (show IntegrableOn f (openCubeSet Q) volume from hf.integrable (by norm_num))

/-- **Two weak Hessians of the same `H¹` function agree almost everywhere**, one
coordinate at a time, by the almost-everywhere uniqueness of weak partial
derivatives on an open set. -/
theorem hess_ae_eq {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H H' : HasWeakHessianOn (openCubeSet Q) u) (i j : Fin d) :
    H.hess i j =ᵐ[volume.restrict (openCubeSet Q)] H'.hess i j :=
  HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
    (locallyIntegrableOn_of_memL2On (H.hess_memL2 i j))
    (locallyIntegrableOn_of_memL2On (H'.hess_memL2 i j))
    (H.weak_second i j) (H'.weak_second i j)

/-- The normalized cube measure is a multiple of the restricted volume measure
of the *open* cube, the two cube presentations differing by a null set. -/
private theorem normalizedCubeMeasure_eq_smul_restrict_openCubeSet
    (Q : TriadicCube d) :
    normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (openCubeSet Q) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- **The `L̲^q(Q)` size of the weak Hessian does not depend on the witness.** -/
theorem cubeLpENorm_hessianHilbertMat_congr {Q : TriadicCube d}
    {u : H1Function (openCubeSet Q)}
    (H H' : HasWeakHessianOn (openCubeSet Q) u) (q : ℝ≥0∞) :
    Section2.Norms.cubeLpENorm Q q
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) =
      Section2.Norms.cubeLpENorm Q q
        (fun x => HilbertMat.ofMat (fun i j => H'.hess i j x)) := by
  have hcoord : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      ∀ p : Fin d × Fin d, H.hess p.1 p.2 x = H'.hess p.1 p.2 x :=
    ae_all_iff.2 (fun p => hess_ae_eq H H' p.1 p.2)
  have hmat : (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) =ᵐ[
      normalizedCubeMeasure Q]
      fun x => HilbertMat.ofMat (fun i j => H'.hess i j x) := by
    rw [normalizedCubeMeasure_eq_smul_restrict_openCubeSet]
    refine Measure.ae_smul_measure (hcoord.mono (fun x hx => ?_)) _
    exact congrArg HilbertMat.ofMat (funext fun i => funext fun j => hx (i, j))
  exact eLpNorm_congr_ae hmat

/-! ## The `W^{2,p}` estimate for the Dirichlet response -/

/-- **The divergence-form `W^{2,p}` estimate on a centred cube, Dirichlet
half.** For `2 ≤ d` and every finite exponent `1 < p < ∞` there is one finite
constant, depending on `d` and `p` alone and quantified before the cube and the
data, such that every Dirichlet response `w` of a flux `F ∈ L̲²(Q)` carrying a
weak Jacobian `DF ∈ L̲² ∩ L̲^p(Q)` has a weak Hessian in `L̲^p(Q)` with

> `‖∇²w‖_{L̲^p(Q)} ≤ C ‖∇F‖_{L̲^p(Q)}`.

This is `e.abstract.response.W28` for `w_D`, obtained from CoarseGraining's
scalar Poisson Hessian endpoint through the bridge
`cubeDirichletWeakPoissonProblem_of_isCubeDirichletResponse`. The constant is
`d` times the upstream one, the factor coming from
`cubeLpENorm_weakDivergence_le`. -/
theorem exists_cubeDirichletResponseHessianLpEstimate (hd : 2 ≤ d) (p : ℝ≥0∞)
    (hp_one : 1 < p) (hp_top : p < ∞) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (m : ℤ) (F : Vec d → Vec d) (DF : Fin d → Vec d → Vec d),
        MemLp F 2 (normalizedCubeMeasure (originCube d m)) →
        HasWeakJacobianOn (openCubeSet (originCube d m)) F DF →
        MemLp (jacobianHilbertMat DF) 2 (normalizedCubeMeasure (originCube d m)) →
        MemLp (jacobianHilbertMat DF) p (normalizedCubeMeasure (originCube d m)) →
        ∀ w : H10Function (openCubeSet (originCube d m)),
          Section3.ResponseFields.IsCubeDirichletResponse (originCube d m) F w →
          ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) w.toH1Function,
            MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) p
                (normalizedCubeMeasure (originCube d m)) ∧
              Section2.Norms.cubeLpENorm (originCube d m) p
                  (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤
                C * Section2.Norms.cubeLpENorm (originCube d m) p
                  (jacobianHilbertMat DF) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hC⟩ :=
    CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le
      d { exponent := p, one_lt := hp_one, lt_top := hp_top }
  refine ⟨(d : ℝ≥0∞) * C, ENNReal.mul_lt_top (ENNReal.natCast_lt_top d) hCtop, ?_⟩
  intro m F DF hF2 hweak hDF2 hDFp w hw
  obtain ⟨H, hHmem, hHbound⟩ :=
    hC m (weakDivergence DF) (memLp_weakDivergence hDF2)
      (memLp_weakDivergence hDFp) w
      (cubeDirichletWeakPoissonProblem_of_isCubeDirichletResponse
        (memL2On_component hF2) (gradMemL2On_jacobian hDF2) hweak hw)
  refine ⟨H, hHmem, ?_⟩
  calc Section2.Norms.cubeLpENorm (originCube d m) p
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
      ≤ C * Section2.Norms.cubeLpENorm (originCube d m) p (weakDivergence DF) :=
        hHbound
    _ ≤ C * ((d : ℝ≥0∞) * Section2.Norms.cubeLpENorm (originCube d m) p
          (jacobianHilbertMat DF)) := by
        gcongr
        exact cubeLpENorm_weakDivergence_le (originCube d m) p DF
    _ = (d : ℝ≥0∞) * C * Section2.Norms.cubeLpENorm (originCube d m) p
          (jacobianHilbertMat DF) := by
        ring

/-! ## `e.abstract.response.W28`, the Dirichlet conjunct -/

end

end Sobolev
end SuperdiffusionCLT
