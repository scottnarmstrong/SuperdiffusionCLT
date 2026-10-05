/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCarriers
public import SuperdiffusionCLT.Section3.Terms.GluedField
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscUnweighted
public import SuperdiffusionCLT.Section2.Norms.NegativeHatOrderOne
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube

/-!
# The mean-zero dual: the centred test class of the duality step of `e.RHS.term3.B`

The duality step of the proof of `e.RHS.term3.B` pairs two objects.  On the left
stands the **centred** gradient `∇w − (∇w)_{z+cu_n}`, whose mean over the cube
`z + cu_n` vanishes by construction; on the right stands the flux
`a_{L'}(∇u_m − ∇u_{n,z})`.  The printed first factor,
`[∇w − (∇w)_{z+cu_n}]_{\underline H^1(z+cu_n)}`, is the bracket
seminorm `[f]_{\underline W^{1,p}(U)} := ‖∇f‖_{\underline L^p(U)}` — on
`U = z + cu_n` it is `‖∇²w‖_{\underline L²(U)}`, with no power of `3` and no
zeroth-order summand.

This module builds the negative norm whose **dual partner is that seminorm**:
the supremum of the pairing against the class of *centred* test gradient fields
`G = ∇g − (∇g)_Q` with `‖∇G‖_{\underline L²(Q)} = ‖∇²g‖_{\underline L²(Q)} ≤ 1`
(`CentredSeminormTestField`, `centredSeminormNegNorm`).  The class is
**scale-bounded**: every member is mean zero on `Q`, so the per-cube Poincare
inequality `poincare_per_cube` bounds `‖G‖_{\underline L²(Q)}` by
`3^{Q.scale}·C_d·‖∇G‖_{\underline L²(Q)} ≤ 3^{Q.scale}·C_d`, and the pairing
against an `L²(Q)` field is therefore bounded: the supremum defining the norm
is finite (`centredSeminormNegNorm_le_hessScaled`).

A **linear** potential `g(x) = c·x` gives `∇g − (∇g)_Q = 0`, so the centring
annihilates it: linear potentials are admissible members of the class that
contribute nothing to the supremum, and they cannot witness unboundedness.  That
is the point of centring the test class, and it is what separates it from a test
class on which only `‖∇g‖` is controlled.

## The two printed displays at this carrier

* the printed duality, `centredSeminormDuality`: for every response `w`
  with a weak Hessian `H` and every `L²(Q)` flux `F`,
  `|⍍_Q (∇w − (∇w)_Q)·F| ≤ ‖∇²w‖_{\underline L²(Q)} · ‖F‖`, where `‖F‖` is the
  centred-class norm of this module; the coefficient is exactly the printed
  `‖∇²w‖_{\underline L²(Q)}`, and no power of `3` appears;
* the per-cube Poincare step, `centredSeminormAt_avsum_le_hessCubeThree`,
  with constant **one**: the average of the cubed seminorm over the scale-`n`
  sub-cubes is dominated by the cubed normalized `L³` Hessian norm of `cu_m`,
  with no scale factor.

## Relation to the neighbouring seminorm carriers

The seminorm carriers below are named `centredSeminormCarrier` /
`centredSeminormAt` rather than reusing the names of the adjacent unweighted
carrier module, so that the two can be imported together without a name clash.
They are the same quantity: the normalized `L²` norm of the weak Hessian in real
form, with no power of `3` and no zeroth-order summand.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal
open SuperdiffusionCLT.Section2.Norms
  (hilbertMat_ofMat_smul)

noncomputable section

variable {d : ℕ}

/-! ## Scaling and restricting a weak Hessian witness -/

/-- **A weak Hessian witness scales.**  If `H` witnesses the weak Hessian of `u`,
then `c * H.hess` witnesses the weak Hessian of `c • u`: the gradient of `c • u`
is `fun x => c • u.grad x`, so the weak second-derivative identity of `H` is the
one needed after multiplying both sides by `c`. -/
noncomputable def hasWeakHessianOn_const_mul {Q : TriadicCube d}
    {u : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u) (c : ℝ) :
    HasWeakHessianOn (openCubeSet Q) (c • u) where
  hess := fun i j x => c * H.hess i j x
  hess_memL2 := by
    intro i j
    simpa only [smul_eq_mul] using (H.hess_memL2 i j).const_mul c
  weak_second := by
    intro i j φ hφ hφs hφ_sub
    have h := H.weak_second i j φ hφ hφs hφ_sub
    have hpt : ∀ x : Vec d, (c • u).grad x i * (fderiv ℝ φ x) (basisVec j)
        = c * (u.grad x i * (fderiv ℝ φ x) (basisVec j)) := by
      intro x
      rw [H1Function.smul_grad]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hpt2 : ∀ x : Vec d, (c * H.hess i j x) * φ x = c * (H.hess i j x * φ x) := by
      intro x
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul, h,
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt2),
      MeasureTheory.integral_const_mul]
    ring

/-- The coordinate fields of the scaled witness are the scaled coordinate fields. -/
@[simp] theorem hasWeakHessianOn_const_mul_hess {Q : TriadicCube d}
    {u : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u) (c : ℝ) :
    (hasWeakHessianOn_const_mul H c).hess = fun i j x => c * H.hess i j x :=
  rfl

/-- **A weak Hessian witness restricts to an open sub-cube.**  The coordinate
fields are unchanged; the integration-by-parts identity restricts because the
test functions are already supported in the smaller cube. -/
noncomputable def hasWeakHessianOn_restrict {Q R : TriadicCube d}
    {v : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) v)
    (hRopen : IsOpen (openCubeSet R)) (hRV : openCubeSet R ⊆ openCubeSet Q) :
    HasWeakHessianOn (openCubeSet R) (v.restrict hRopen hRV) where
  hess := H.hess
  hess_memL2 := fun i j => memL2On_mono hRV (H.hess_memL2 i j)
  weak_second := fun i j => (H.weak_second i j).restrict hRopen hRV

/-- A constant factor comes out of a volume-normalized vector average. -/
theorem volumeAverageVec_const_smul (U : Set (Vec d)) (c : ℝ) (f : Vec d → Vec d) :
    volumeAverageVec U (fun x => c • f x) = c • volumeAverageVec U f := by
  funext i
  simp only [volumeAverageVec, Pi.smul_apply, smul_eq_mul]
  rw [Section2.Norms.volumeAverage_const_mul]

/-! ## The centred seminorm test class -/

/-- **The centred seminorm test class** of the duality step: an `H¹` potential on
the open cube together with a weak Hessian witness whose normalized `L²`
seminorm is at most one.  Its centred gradient `∇g − (∇g)_Q`
(`CentredSeminormTestField.toField`) is the test gradient field that the printed
duality pairs the flux against.  A linear potential is an admissible member with
`∇g − (∇g)_Q = 0`. -/
structure CentredSeminormTestField (Q : TriadicCube d) where
  /-- The potential whose centred gradient is the test field. -/
  pot : H1Function (openCubeSet Q)
  /-- Its weak Hessian witness. -/
  hess : HasWeakHessianOn (openCubeSet Q) pot
  /-- The seminorm level `‖∇²g‖_{\underline L²(Q)} ≤ 1`. -/
  seminorm_le_one : Section2.Norms.cubeLpENorm Q 2
    (fun x => HilbertMat.ofMat (fun i j => hess.hess i j x)) ≤ 1

/-- The test gradient field of a class member: `∇g − (∇g)_Q`.  It is mean zero
on the cube by construction, so a linear potential contributes the zero field. -/
def CentredSeminormTestField.toField {Q : TriadicCube d}
    (T : CentredSeminormTestField Q) : Vec d → Vec d :=
  fun x => T.pot.grad x - volumeAverageVec (openCubeSet Q) T.pot.grad

/-- Every member of the class is an `L²(Q)` field. -/
theorem memLp_hilbertifyVecField_toField {Q : TriadicCube d}
    (T : CentredSeminormTestField Q) :
    MemLp (hilbertifyVecField T.toField) 2 (normalizedCubeMeasure Q) :=
  memLp_hilbertifyVecField_grad_sub_const T.pot
    (volumeAverageVec (openCubeSet Q) T.pot.grad)

/-- **A class member built from an arbitrary scaled response.**  Every `H¹`
potential with a weak Hessian whose *scaled* seminorm level `‖c‖ₑ · ‖∇²g‖` drops
to at most one yields an admissible centred test field, namely the centred
gradient of `c • g`.  This is how the class is used: the printed centred gradient
`∇w − (∇w)_Q` divided by its own seminorm is a member. -/
noncomputable def centredSeminormTestField_ofScaled {Q : TriadicCube d}
    {w : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) w) (c : ℝ)
    (hc : ‖c‖ₑ * Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤ 1) :
    CentredSeminormTestField Q where
  pot := c • w
  hess := hasWeakHessianOn_const_mul H c
  seminorm_le_one := by
    change Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => c * H.hess i j x)) ≤ 1
    have hfun : (fun x : Vec d => HilbertMat.ofMat (fun i j => c * H.hess i j x))
        = c • (fun x : Vec d => HilbertMat.ofMat (fun i j => H.hess i j x)) := by
      funext x
      exact hilbertMat_ofMat_smul c (fun i j => H.hess i j x)
    rw [hfun, Section2.Norms.cubeLpENorm_const_smul]
    exact hc

/-- The test field of the member built from `(w, H, c)` is `c` times the centred
gradient of `w`. -/
theorem toField_ofScaled {Q : TriadicCube d} {w : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) w) (c : ℝ)
    (hc : ‖c‖ₑ * Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤ 1) :
    (centredSeminormTestField_ofScaled H c hc).toField
      = fun x => c • (w.grad x - volumeAverageVec (openCubeSet Q) w.grad) := by
  funext x
  show (c • w).grad x - volumeAverageVec (openCubeSet Q) (c • w).grad
      = c • (w.grad x - volumeAverageVec (openCubeSet Q) w.grad)
  rw [H1Function.smul_grad, volumeAverageVec_const_smul, smul_sub]

/-- The pairing against the member built from `(w, H, c)` is `c` times the
pairing against the centred gradient of `w`. -/
theorem volumeAverage_vecDot_toField_ofScaled {Q : TriadicCube d} (F : Vec d → Vec d)
    {w : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) w) (c : ℝ)
    (hc : ‖c‖ₑ * Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤ 1) :
    volumeAverage (cubeSet Q)
        (fun x => vecDot (F x) ((centredSeminormTestField_ofScaled H c hc).toField x))
      = c * volumeAverage (cubeSet Q)
          (fun x => vecDot (F x) (w.grad x - volumeAverageVec (openCubeSet Q) w.grad)) := by
  rw [toField_ofScaled]
  have hfun : (fun x : Vec d => vecDot (F x)
        (c • (w.grad x - volumeAverageVec (openCubeSet Q) w.grad)))
      = fun x : Vec d => c * vecDot (F x)
        (w.grad x - volumeAverageVec (openCubeSet Q) w.grad) := by
    funext x
    rw [vecDot_smul_right]
  rw [hfun, Section2.Norms.volumeAverage_const_mul]

/-! ## The centred-class negative norm -/

/-- **The centred-class negative norm of the duality step**: the supremum of the
pairing `⍍_Q F·G` over the centred test gradient fields `G` of the class
`CentredSeminormTestField`, i.e. over `G = ∇g − (∇g)_Q` with
`‖∇G‖_{\underline L²(Q)} = ‖∇²g‖_{\underline L²(Q)} ≤ 1`.  Its dual partner is
exactly the seminorm carrier `centredSeminormCarrier`. -/
def centredSeminormNegNorm (Q : TriadicCube d) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ⨆ T : CentredSeminormTestField Q,
    ENNReal.ofReal (volumeAverage (cubeSet Q) (fun x => vecDot (F x) (T.toField x)))

/-- Each admissible centred test field bounds the norm from below. -/
theorem le_centredSeminormNegNorm {Q : TriadicCube d} (F : Vec d → Vec d)
    (T : CentredSeminormTestField Q) :
    ENNReal.ofReal (volumeAverage (cubeSet Q) (fun x => vecDot (F x) (T.toField x))) ≤
      centredSeminormNegNorm Q F :=
  le_iSup_of_le T le_rfl

/-- A bound valid on every member bounds the norm. -/
theorem centredSeminormNegNorm_le {Q : TriadicCube d} {F : Vec d → Vec d} {c : ℝ≥0∞}
    (h : ∀ T : CentredSeminormTestField Q,
      ENNReal.ofReal (volumeAverage (cubeSet Q) (fun x => vecDot (F x) (T.toField x))) ≤ c) :
    centredSeminormNegNorm Q F ≤ c :=
  iSup_le h

/-! ## Finiteness of the centred-class negative norm -/

/-- The Hilbert-matrix realization of a weak Hessian is `L²` for the normalized
cube measure. -/
theorem memLp_hessianHilbertMat_normalizedCubeMeasure {Q : TriadicCube d}
    {v : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) v) :
    MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) 2
      (normalizedCubeMeasure Q) := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  rw [MeasureTheory.memLp_piLp_iff]
  intro j
  simpa only [Function.comp_apply, HilbertMat.ofMat, HilbertVec.ofVec, PiLp.toLp_apply]
    using H.hess_memLp_normalizedCubeMeasure Q i j

/-- **The per-cube Poincare inequality at the seminorm carrier.**  The centred
gradient `∇v − (∇v)_Q` is mean zero on `Q`, so `poincare_per_cube` bounds its
`L²(Q)` norm by `3^{Q.scale}·C_d` times the seminorm `‖∇²v‖_{\underline L²(Q)}`.
This is what makes the class `CentredSeminormTestField` bounded: on a member the
seminorm is at most one, so the class sits in the ball of radius `3^{Q.scale}·C_d`. -/
theorem vecCubeLpENorm_centredGrad_le_hess {Q : TriadicCube d}
    {v : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) v) :
    vecCubeLpENorm Q 2 (fun x => v.grad x - volumeAverageVec (openCubeSet Q) v.grad) ≤
      ENNReal.ofReal (cubeScaleFactor Q *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        Section2.Norms.cubeLpENorm Q 2
          (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) :=
  poincare_per_cube (Q := Q) (F := v.grad) (DF := fun i x j => H.hess i j x)
    (fun i => { toFun := fun x => v.grad x i
                grad := fun x j => H.hess i j x
                memL2 := v.gradMemL2 i
                gradMemL2 := fun j => H.hess_memL2 i j
                hasWeakGradient := fun j => H.weak_second i j })
    (fun _ => rfl) (fun _ => rfl)

/-- The Poincare bound on a member of the class, with the class's seminorm level
`≤ 1` used. -/
theorem vecCubeLpENorm_toField_le {Q : TriadicCube d}
    (T : CentredSeminormTestField Q) :
    vecCubeLpENorm Q 2 T.toField ≤
      ENNReal.ofReal (cubeScaleFactor Q *
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant) := by
  refine le_trans (vecCubeLpENorm_centredGrad_le_hess T.hess) ?_
  calc ENNReal.ofReal (cubeScaleFactor Q *
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        Section2.Norms.cubeLpENorm Q 2
          (fun x => HilbertMat.ofMat (fun i j => T.hess.hess i j x))
      ≤ ENNReal.ofReal (cubeScaleFactor Q *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) * 1 :=
        mul_le_mul' le_rfl T.seminorm_le_one
    _ = ENNReal.ofReal (cubeScaleFactor Q *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) := mul_one _

/-- **Finiteness: the centred-class negative norm is dominated by `L²(Q)`.**
Every member of the class is mean zero on `Q` and has seminorm at most one, so by
`vecCubeLpENorm_toField_le` its `L²(Q)` norm is at most `3^{Q.scale}·C_d`;
Cauchy-Schwarz then bounds every pairing by
`‖F‖_{\underline L²(Q)} · 3^{Q.scale}·C_d`.  In particular the supremum defining
the norm is finite on every `L²(Q)` field. -/
theorem centredSeminormNegNorm_le_hessScaled {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    centredSeminormNegNorm Q F ≤
      vecCubeLpENorm Q 2 F * ENNReal.ofReal (cubeScaleFactor Q *
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant) := by
  set C : ℝ := cubeScaleFactor Q * (originCubeMeanZeroH1CoerciveEstimate d 0).constant
    with hCdef
  have hcf : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale
  have hC0 : 0 ≤ C :=
    mul_nonneg (le_of_lt hcf) (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  refine centredSeminormNegNorm_le fun T => ?_
  have hGmem := memLp_hilbertifyVecField_toField T
  have hCS := abs_volumeAverage_vecDot_le_mul hF hGmem
  have hGle : (vecCubeLpENorm Q 2 T.toField).toReal ≤ C :=
    ENNReal.toReal_le_of_le_ofReal hC0 (vecCubeLpENorm_toField_le T)
  have hreal : |volumeAverage (cubeSet Q) (fun x => vecDot (F x) (T.toField x))| ≤
      (vecCubeLpENorm Q 2 F).toReal * C :=
    le_trans hCS (mul_le_mul_of_nonneg_left hGle ENNReal.toReal_nonneg)
  calc ENNReal.ofReal (volumeAverage (cubeSet Q) (fun x => vecDot (F x) (T.toField x)))
      ≤ ENNReal.ofReal ((vecCubeLpENorm Q 2 F).toReal * C) :=
        ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) hreal)
    _ = ENNReal.ofReal ((vecCubeLpENorm Q 2 F).toReal) * ENNReal.ofReal C :=
        ENNReal.ofReal_mul ENNReal.toReal_nonneg
    _ ≤ vecCubeLpENorm Q 2 F * ENNReal.ofReal C :=
        mul_le_mul' ENNReal.ofReal_toReal_le le_rfl

/-- The centred-class negative norm of an `L²(Q)` field is finite. -/
theorem centredSeminormNegNorm_ne_top {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    centredSeminormNegNorm Q F ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (centredSeminormNegNorm_le_hessScaled hF)
  refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
  have h : vecCubeLpENorm Q 2 F
      = eLpNorm (hilbertifyVecField F) 2 (normalizedCubeMeasure Q) := rfl
  rw [h]
  exact hF.eLpNorm_lt_top.ne

/-! ## The seminorm carrier and display (a): the duality -/

/-- **The seminorm carrier** `‖∇²v‖_{\underline L²(Q)}` of the response on
the cube `Q`, in real form.  No power of `3`, and no zeroth-order summand. -/
def centredSeminormCarrier {Q : TriadicCube d} {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) : ℝ :=
  (Section2.Norms.cubeLpENorm Q 2
    (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))).toReal

theorem centredSeminormCarrier_nonneg {Q : TriadicCube d}
    {v : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) v) :
    0 ≤ centredSeminormCarrier H :=
  ENNReal.toReal_nonneg

/-- **The duality step of `e.RHS.term3.B` at the seminorm carrier.**
For a response `w` with weak Hessian `H` and an `L²(Q)` flux `F`, the pairing of the
printed centred first factor `∇w − (∇w)_Q` against `F` is bounded by the printed
coefficient `centredSeminormCarrier H = ‖∇²w‖_{\underline L²(Q)}` times the centred-class
norm of `F`.

The proof is the homogeneity of the class: on `B := ‖∇²w‖_{\underline L²(Q)} > 0`
the centred gradient `∇w − (∇w)_Q` divided by `B` *is* a member of the class
(`centredSeminormTestField_ofScaled` with `c := B⁻¹`), so its pairing against `F`
is at most the supremum; the other sign is the member with `c := -B⁻¹`.  On
`B = 0` the Poincare bound makes the centred gradient vanish in `L²(Q)`, and
Cauchy-Schwarz gives the bound. -/
theorem centredSeminormDuality {Q : TriadicCube d} {w : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) w) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    ENNReal.ofReal |volumeAverage (cubeSet Q) (fun x => vecDot
        (w.grad x - volumeAverageVec (openCubeSet Q) w.grad) (F x))| ≤
      ENNReal.ofReal (centredSeminormCarrier H) * centredSeminormNegNorm Q F := by
  set B : ℝ := centredSeminormCarrier H with hBdef
  set Y : ℝ := volumeAverage (cubeSet Q) (fun x => vecDot
    (w.grad x - volumeAverageVec (openCubeSet Q) w.grad) (F x)) with hYdef
  have hB0 : 0 ≤ B := centredSeminormCarrier_nonneg H
  have hMfin : Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≠ ⊤ :=
    (memLp_hessianHilbertMat_normalizedCubeMeasure H).eLpNorm_lt_top.ne
  have hMval : Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) = ENNReal.ofReal B :=
    (ENNReal.ofReal_toReal hMfin).symm
  rcases eq_or_lt_of_le hB0 with hBz | hBpos
  · -- `B = 0`: the centred gradient vanishes in `L²(Q)`
    have hBzero : B = 0 := hBz.symm
    have hM0 : Section2.Norms.cubeLpENorm Q 2
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) = 0 := by
      rw [hMval, hBzero, ENNReal.ofReal_zero]
    have hzero : vecCubeLpENorm Q 2
        (fun x => w.grad x - volumeAverageVec (openCubeSet Q) w.grad) = 0 := by
      have hP := vecCubeLpENorm_centredGrad_le_hess H
      rw [hM0] at hP
      exact le_antisymm (le_trans hP (by rw [mul_zero])) bot_le
    have hGmem := memLp_hilbertifyVecField_grad_sub_const w
      (volumeAverageVec (openCubeSet Q) w.grad)
    have hCS := abs_volumeAverage_vecDot_le_mul hGmem hF
    rw [hzero, ENNReal.toReal_zero, zero_mul] at hCS
    rw [hBzero, ENNReal.ofReal_zero, zero_mul]
    exact le_of_eq (ENNReal.ofReal_eq_zero.2 hCS)
  · -- `B > 0`: the class is used at the normalizing scale
    have hBne : B ≠ 0 := ne_of_gt hBpos
    have hcpos : 0 < B⁻¹ := inv_pos.mpr hBpos
    set c : ℝ := B⁻¹ with hcdef
    have hc0 : 0 ≤ c := le_of_lt hcpos
    have hBc : B * c = 1 := mul_inv_cancel₀ hBne
    have hcB : c * B = 1 := by rw [mul_comm, hBc]
    have hclevel : ‖c‖ₑ * Section2.Norms.cubeLpENorm Q 2
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤ 1 := by
      rw [hMval, Real.enorm_eq_ofReal hc0, ← ENNReal.ofReal_mul hc0, hcB]
      simp
    have hclevel' : ‖(-c)‖ₑ * Section2.Norms.cubeLpENorm Q 2
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤ 1 := by
      rwa [enorm_neg]
    have hpos : Y ≤ B * (centredSeminormNegNorm Q F).toReal := by
      have hpair :=
        le_centredSeminormNegNorm F (centredSeminormTestField_ofScaled H c hclevel)
      rw [volumeAverage_vecDot_toField_ofScaled F H c hclevel] at hpair
      have hswap : (fun x : Vec d => vecDot (F x)
            (w.grad x - volumeAverageVec (openCubeSet Q) w.grad))
          = fun x : Vec d => vecDot
            (w.grad x - volumeAverageVec (openCubeSet Q) w.grad) (F x) :=
        funext fun x => vecDot_comm _ _
      rw [hswap, ← hYdef] at hpair
      have hreal : c * Y ≤ (centredSeminormNegNorm Q F).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal (centredSeminormNegNorm_ne_top hF)).1 hpair
      calc Y = B * (c * Y) := by rw [← mul_assoc, hBc, one_mul]
        _ ≤ B * (centredSeminormNegNorm Q F).toReal :=
            mul_le_mul_of_nonneg_left hreal hB0
    have hneg : -Y ≤ B * (centredSeminormNegNorm Q F).toReal := by
      have hpair :=
        le_centredSeminormNegNorm F (centredSeminormTestField_ofScaled H (-c) hclevel')
      rw [volumeAverage_vecDot_toField_ofScaled F H (-c) hclevel'] at hpair
      have hswap : (fun x : Vec d => vecDot (F x)
            (w.grad x - volumeAverageVec (openCubeSet Q) w.grad))
          = fun x : Vec d => vecDot
            (w.grad x - volumeAverageVec (openCubeSet Q) w.grad) (F x) :=
        funext fun x => vecDot_comm _ _
      rw [hswap, ← hYdef] at hpair
      have hreal : (-c) * Y ≤ (centredSeminormNegNorm Q F).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal (centredSeminormNegNorm_ne_top hF)).1 hpair
      have hBc' : B * (-c) = -1 := by
        rw [mul_neg, hBc]
      calc -Y = B * ((-c) * Y) := by rw [← mul_assoc, hBc', neg_one_mul]
        _ ≤ B * (centredSeminormNegNorm Q F).toReal :=
            mul_le_mul_of_nonneg_left hreal hB0
    have habs : |Y| ≤ B * (centredSeminormNegNorm Q F).toReal :=
      abs_le.2 ⟨by simpa using neg_le_neg hneg, hpos⟩
    calc ENNReal.ofReal |Y|
        ≤ ENNReal.ofReal (B * (centredSeminormNegNorm Q F).toReal) :=
          ENNReal.ofReal_le_ofReal habs
      _ = ENNReal.ofReal B * ENNReal.ofReal ((centredSeminormNegNorm Q F).toReal) :=
          ENNReal.ofReal_mul hB0
      _ ≤ ENNReal.ofReal B * centredSeminormNegNorm Q F :=
          mul_le_mul' le_rfl ENNReal.ofReal_toReal_le

/-- **The seminorm carrier on a sub-cube `R`**: the same quantity as
`centredSeminormCarrier`, evaluated at the cube `R`. -/
def centredSeminormAt {m : ℕ} {v : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) v)
    (R : TriadicCube d) : ℝ :=
  (Section2.Norms.cubeLpENorm R 2
    (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))).toReal

theorem centredSeminormAt_nonneg {m : ℕ}
    {v : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) v) (R : TriadicCube d) :
    0 ≤ centredSeminormAt H R :=
  ENNReal.toReal_nonneg

/-- **The printed duality on every sub-cube of `cu_m`.**  This is
`centredSeminormDuality` at a sub-cube `R` of `largeCubeSubcubes d n m`: the
response is restricted to `openCubeSet R` (the restriction keeps both the value
and the gradient representative, and `hasWeakHessianOn_restrict` keeps the
coordinate fields of the weak Hessian), so the coefficient is the per-cube
seminorm `centredSeminormAt H R = ‖∇²v‖_{\underline L²(R)}` of the printed duality. -/
theorem centredSeminormDuality_subcube {n m : ℕ}
    {v : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) v)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d n m) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R)) :
    ENNReal.ofReal |volumeAverage (cubeSet R) (fun x => vecDot
        (v.grad x - volumeAverageVec (openCubeSet R) v.grad) (F x))| ≤
      ENNReal.ofReal (centredSeminormAt H R) * centredSeminormNegNorm R F := by
  have hR' := hR
  rw [largeCubeSubcubes_eq_descendantsAtDepth (d := d) n m] at hR'
  have hsub : openCubeSet R ⊆ openCubeSet (originCube d (m : ℤ)) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR'
  have h := centredSeminormDuality
    (Q := R) (w := v.restrict (isOpen_openCubeSet R) hsub)
    (hasWeakHessianOn_restrict H (isOpen_openCubeSet R) hsub) hF
  simp only [centredSeminormAt, centredSeminormCarrier] at h ⊢
  exact h

/-! ## Display (b) at the same carrier -/

/-- **The per-cube Poincare step at the seminorm carrier, with
constant one.**  The average of the cubed seminorms `centredSeminormAt H R` over
the scale-`n` sub-cubes of `cu_m` is dominated by the cubed normalized `L³`
Hessian norm of `cu_m`, with no scale factor and no constant at all: the
zeroth-order `H̲¹` norm, which would cost `termTwoPoincareConst d · 3^n`, is
absent from the seminorm.  This is the constant-one lemma
`oscH1SeminormAt_avsum_le_hessCubeThree` of the neighbouring unweighted module:
`centredSeminormAt` and its carrier `oscH1SeminormAt` are the *same* definition
(the normalized `L²` norm of the Hilbert-matrix Hessian, in real form), so the
two statements are definitionally equal and this one is a citation, not a
re-proof. -/
theorem centredSeminormAt_avsum_le_hessCubeThree {n m : ℕ}
    {v : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) v) :
    ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)⁻¹) *
        ∑ R ∈ largeCubeSubcubes d n m, (ENNReal.ofReal (centredSeminormAt H R)) ^ (3 : ℕ) ≤
      (Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 3
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))) ^ (3 : ℕ) :=
  oscH1SeminormAt_avsum_le_hessCubeThree H

end

end SuperdiffusionCLT.Section3.Terms
