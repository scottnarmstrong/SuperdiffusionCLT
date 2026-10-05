/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinfty
public import SuperdiffusionCLT.Section3.ResponseFields.Norms

/-!
# The upper-shell gradient display and the centered upper-shell flux

The paper records, after the regularity assumption `a.j.reg` and before
`l.ellip.k.scales.estimates`, the display

> `‖∇(k_m − k_n)‖_{L^∞(cu_n)} = O_{Γ₂}(3^{-n})`   (`e.nabla.kmn.Linfty`)

for every `n < m`.  **The cube is the small one**: `cu_n ⊆ cu_k` for every
shell index `k ∈ (n, m]`, so each single-shell derivative norm is read on its
own natural cube, where the `ShellLawJ3` observable
`√d 3^k ‖∇ j_k‖_{L^∞(cu_k)}` controls it at scale `3^{-k}`; the geometric sum
over `k ∈ (n, m]` gives `3^{-n}`.  No union bound over sub-cubes and no
`(m − n)^{1/2}` loss occur, in contrast with the large-cube clauses
`e.kmn.Lp`/`e.kmn.Linfty` of `l.ellip.k.scales.estimates`, whose cube `cu_l`
satisfies `l ≥ m` instead.

The proof of `l.w.basic.regbounds` uses the display at the
shifted pair: the flux `F = (k_{L'} − k_{ℓ'})p` is split at `m − 1`, and the
upper shell `(k_{L'} − k_{m-1})p` is estimated on `cu_m` by

> `‖F_upper − (F_upper)_{cu_m}‖_{L̲^8(cu_m)} ≤ ∑_{k=m}^{L'} 3^m ‖∇ j_k‖_{L^∞(cu_m)}`,

i.e. a Poincaré step at scale `3^m` followed by the display on `cu_m` for the
shells `k ≥ m`.  This module therefore proves the display in the exact
generality both readings need: the cube index `n` and the shell interval
`(a, b]` are independent, subject to `n ≤ a + 1` (equivalently `n ≤ k` for
every shell `k` of the interval), which is `n = a` for `e.nabla.kmn.Linfty`
itself and `n = m`, `a = m − 1` for the upper shell of the response bound.

## The carriers

The shell increment `k_b − k_a` is `finiteShellIncrement`, and the
subtraction form `finiteShellIncrement_apply_eq_streamCutoff_sub` identifies it
with the difference `k_b(x) − k_a(x)` of the `streamCutoff` fields in
which `IsDirichletResponse` (`Section3/Setup/Scales.lean`) writes its flux.
Every statement below about the flux is phrased in the `streamCutoff`
difference, so that a consumer of `IsDirichletResponse` needs no reshaping.

## Main definitions

* `upperShellDerivGauge`: `∑_{k ∈ (a,b]} ‖∇ j_k‖_{L^∞(cu_n)}`, the measurable
  envelope of the display.
* `upperShellFluxSupBound`: the pointwise envelope of `(k_b − k_a)p` centered
  at the cube centre, `C(d) 3^n |p| ·` the gauge.

## Main results

* `isBigOWith_gammaSigma_upperShellDerivGauge`: `e.nabla.kmn.Linfty`.
* `vecNorm_streamFlux_sub_center_le`: the pointwise bound of the centered
  upper-shell flux by `upperShellFluxSupBound`.
* `vecCubeLpENorm_le_of_forall_mem_openCubeSet`: the `L̲^q(cu_n)` size of a field from a
  pointwise bound.

## References

* The paper: `e.nabla.kmn.Linfty`, `e.k-n.reg.with.gamma`, `l.w.basic.regbounds`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.ResponseFields

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The upper-shell derivative gauge -/

/-- `∑_{k ∈ (a,b]} ‖∇ j_k‖_{L^∞(cu_n)}`, the envelope of `e.nabla.kmn.Linfty`
on the cube `cu_n`.  The individual terms are the exact cube carriers
`shellCubeDerivNorm`, read on the **common** cube `cu_n`; the intended range of
the parameters is `n ≤ a + 1`, where every shell of the interval has its own
natural cube containing `cu_n`. -/
def upperShellDerivGauge (n a b : ℕ) (omega : ShellSeq d) : ℝ :=
  ∑ k ∈ Finset.Ioc a b, ShellField.shellCubeDerivNorm n (omega k)

theorem upperShellDerivGauge_nonneg (n a b : ℕ) (omega : ShellSeq d) :
    0 ≤ upperShellDerivGauge n a b omega :=
  Finset.sum_nonneg fun k _ => ShellField.shellCubeDerivNorm_nonneg n (omega k)

theorem measurable_upperShellDerivGauge (n a b : ℕ) :
    Measurable (upperShellDerivGauge n a b : ShellSeq d → ℝ) :=
  Finset.measurable_sum _ fun k _ =>
    measurable_shellCubeDerivNorm_coordinate n k

/-- At every point of `cu_n` the exact induced norm of the reconstructed
derivative of `k_b − k_a` is bounded by the gauge. -/
theorem matrixDerivativeNorm_sum_shellDeriv_le_upperShellDerivGauge
    (omega : ShellSeq d) (n a b : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) ≤
      upperShellDerivGauge n a b omega := by
  refine (matrixDerivativeNorm_finset_sum_le (Finset.Ioc a b)
    (fun k => ShellField.deriv (omega k) x)).trans ?_
  exact Finset.sum_le_sum fun k _ =>
    ShellField.matrixDerivativeNorm_deriv_le_shellCubeDerivNorm n (omega k) hx

/-- **The `Γ₂` tail of the upper-shell derivative gauge.** The hypothesis `ShellLawJ3`
gives each shell `k` of the interval the amplitude `3^{-k}` on its own natural
cube `cu_k`; since `n ≤ a + 1 ≤ k`, the cube `cu_n` is contained in `cu_k` and
`shellCubeDerivNorm_mono` transports the bound.  The geometric sum
`∑_{k>a} 3^{-k} ≤ 3^{-a}` and the `Γ₂` triangle inequality give the
stated amplitude. -/
theorem isBigOWith_gammaSigma_upperShellDerivGauge
    (hJ3 : ShellLawJ3 d P) {n a b : ℕ} (hna : n ≤ a + 1) (hab : a < b) :
    IsBigOWith P.toMeasure (gammaSigma 2) (upperShellDerivGauge n a b)
      (gammaTriangleConst 2 * ((3 : ℝ) ^ a)⁻¹) := by
  have hs : (Finset.Ioc a b).Nonempty := Finset.nonempty_Ioc.mpr hab
  have hbigO : ∀ k ∈ Finset.Ioc a b,
      IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d => ShellField.shellCubeDerivNorm n (omega k))
        (((3 : ℝ) ^ k)⁻¹) := by
    intro k hk
    have hnk : n ≤ k := le_trans hna (Finset.mem_Ioc.mp hk).1
    have hsmall :
        IsBigOWith P.toMeasure (gammaSigma 2)
          (fun omega : ShellSeq d => ShellField.shellCubeDerivNorm n (omega k))
          (((3 : ℝ) ^ k)⁻¹) :=
      (isBigOWith_gammaSigma_shellCubeDerivNorm_coordinate hJ3 k).of_le
        (fun omega => ShellField.shellCubeDerivNorm_mono hnk (omega k))
    exact
      (isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := gammaSigma 2)
        (X := fun omega : ShellSeq d =>
          ShellField.shellCubeDerivNorm n (omega k))
        (A := ((3 : ℝ) ^ k)⁻¹)
        (fun omega =>
          ShellField.shellCubeDerivNorm_nonneg n (omega k))).1 hsmall
  have hfinite := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.Ioc a b)
    (X := fun (k : ℕ) (omega : ShellSeq d) =>
      ShellField.shellCubeDerivNorm n (omega k))
    (a := fun k : ℕ => ((3 : ℝ) ^ k)⁻¹) (σ := 2)
    (by norm_num) hs (fun k _ => by positivity) hbigO
    (fun k _ => measurable_shellCubeDerivNorm_coordinate n k)
  have hwith :
      IsBigOWith P.toMeasure (gammaSigma 2) (upperShellDerivGauge n a b)
        (gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc a b, ((3 : ℝ) ^ k)⁻¹) := by
    refine
      (isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := gammaSigma 2)
        (X := upperShellDerivGauge n a b)
        (A := gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc a b, ((3 : ℝ) ^ k)⁻¹)
        (upperShellDerivGauge_nonneg n a b)).2 ?_
    exact hfinite
  refine hwith.mono_scale
    (mul_le_mul_of_nonneg_left ?_ gammaTriangleConst_pos.le)
  exact sum_Ioc_inv_pow_three_le hab.le

/-! ## `e.nabla.kmn.Linfty` -/

/-- The stream-cutoff difference is the finite shell increment, as a
function. -/
theorem streamCutoff_sub_eq_finiteShellIncrement (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) :
    (fun y : Vec d => streamCutoff omega b y - streamCutoff omega a y) =
      (finiteShellIncrement omega a b : Vec d → Mat d) :=
  funext fun y =>
    (finiteShellIncrement_apply_eq_streamCutoff_sub omega hab y).symm

/-- The derivative of `k_b − k_a` at any point is the sum of the stored shell
derivatives. -/
theorem hasFDerivAt_streamCutoff_sub (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (x : Vec d) :
    HasFDerivAt (fun y : Vec d => streamCutoff omega b y - streamCutoff omega a y)
      (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) x := by
  rw [streamCutoff_sub_eq_finiteShellIncrement omega hab]
  exact finiteShellIncrement_hasFDerivAt_sum_shellDeriv omega a b x

/-! ## The mean-value envelope of the centered upper-shell increment -/

private def matEntryCLM (i l : Fin d) : Mat d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) l).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => Fin d → ℝ) i)

@[simp] private theorem matEntryCLM_apply (i l : Fin d) (A : Mat d) :
    matEntryCLM i l A = A i l := rfl

/-- **The entrywise mean-value estimate for the upper shell.** Along the
segment from the cube centre, the entries of `k_b − k_a` move by at most the
gauge times the Euclidean distance to the centre.  This is the
finite-increment mean-value argument run with the *upper-shell* gauge, i.e.
with the cube index `n` decoupled from the lower endpoint `a` of the shell
interval. -/
theorem abs_entry_finiteShellIncrement_sub_center_le_gauge
    (omega : ShellSeq d) (n a b : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) (i l : Fin d) :
    |finiteShellIncrement omega a b x i l -
        finiteShellIncrement omega a b 0 i l| ≤
      upperShellDerivGauge n a b omega * vecNorm x := by
  set f : ℝ → ℝ := fun t =>
    matEntryCLM i l (finiteShellIncrement omega a b (t • x)) with hf
  set f' : ℝ → ℝ := fun t =>
    matEntryCLM i l
      ((∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) (t • x)) x) with hf'
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (f' t) (Set.Icc (0 : ℝ) 1) t := by
    intro t _
    have hpath : HasDerivAt (fun s : ℝ => s • x) x t := by
      have h1 := (hasDerivAt_id t).smul_const x
      rw [one_smul] at h1
      exact h1
    have hsum :=
      finiteShellIncrement_hasFDerivAt_sum_shellDeriv omega a b (t • x)
    exact (((matEntryCLM i l).hasFDerivAt).comp_hasDerivAt t
      (hsum.comp_hasDerivAt t hpath)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖f' t‖ ≤ upperShellDerivGauge n a b omega * vecNorm x := by
    intro t ht
    have htx : t • x ∈ openCubeSet (originCube d (n : ℤ)) :=
      smul_mem_openCubeSet_originCube ⟨ht.1, ht.2.le⟩ hx
    calc
      ‖f' t‖ =
          |((∑ k ∈ Finset.Ioc a b,
            ShellField.deriv (omega k) (t • x)) x) i l| := rfl
      _ ≤ matrixOperatorNorm
          ((∑ k ∈ Finset.Ioc a b,
            ShellField.deriv (omega k) (t • x)) x) :=
        abs_entry_le_matrixOperatorNorm _ _ _
      _ ≤ ShellField.matrixDerivativeNorm
            (∑ k ∈ Finset.Ioc a b,
              ShellField.deriv (omega k) (t • x)) * vecNorm x :=
        matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm _ _
      _ ≤ upperShellDerivGauge n a b omega * vecNorm x :=
        mul_le_mul_of_nonneg_right
          (matrixDerivativeNorm_sum_shellDeriv_le_upperShellDerivGauge
            omega n a b htx)
          (vecNorm_nonneg x)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩)
  have hf1 : f 1 = finiteShellIncrement omega a b x i l := by
    simp only [hf, one_smul]
    rfl
  have hf0 : f 0 = finiteShellIncrement omega a b 0 i l := by
    simp only [hf, zero_smul]
    rfl
  rw [hf1, hf0] at hmean
  simpa only [Real.norm_eq_abs, sub_zero, mul_one] using hmean

/-- The exact Euclidean operator norm of the centered upper-shell increment on
`cu_n`. -/
theorem matrixOperatorNorm_finiteShellIncrement_sub_center_le
    (omega : ShellSeq d) (n a b : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    matrixOperatorNorm
        (finiteShellIncrement omega a b x - finiteShellIncrement omega a b 0) ≤
      (d : ℝ) ^ 2 * (upperShellDerivGauge n a b omega * vecNorm x) := by
  have hentries :
      ∑ i : Fin d, ∑ l : Fin d,
        |(finiteShellIncrement omega a b x -
            finiteShellIncrement omega a b 0) i l - (0 : Mat d) i l| ≤
        (d : ℝ) ^ 2 * (upperShellDerivGauge n a b omega * vecNorm x) := by
    calc
      ∑ i : Fin d, ∑ l : Fin d,
          |(finiteShellIncrement omega a b x -
              finiteShellIncrement omega a b 0) i l - (0 : Mat d) i l| ≤
          ∑ _i : Fin d, ∑ _l : Fin d,
            upperShellDerivGauge n a b omega * vecNorm x :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => by
          simpa only [Matrix.sub_apply, Matrix.zero_apply, sub_zero] using
            abs_entry_finiteShellIncrement_sub_center_le_gauge omega n a b hx i l
      _ = (d : ℝ) ^ 2 * (upperShellDerivGauge n a b omega * vecNorm x) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc]
        ring
  refine (matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries
    (finiteShellIncrement omega a b x - finiteShellIncrement omega a b 0)
    (0 : Mat d)).trans ?_
  simpa only [matrixOperatorNorm_zero, zero_add] using hentries

/-! ## The centered upper-shell flux -/

/-- The dimensional constant of the centered upper-shell flux envelope,
`d² √d / 2`: the `d²` is the entrywise-to-Euclidean conversion of the operator
norm, and the `√d / 2` is the Euclidean radius of `cu_n` in units of `3^n`. -/
def upperShellFluxConst (d : ℕ) : ℝ := (d : ℝ) ^ 2 * Real.sqrt d / 2

theorem upperShellFluxConst_nonneg (d : ℕ) : 0 ≤ upperShellFluxConst d := by
  unfold upperShellFluxConst
  positivity

/-- The pointwise envelope on `cu_n` of the upper-shell flux `(k_b − k_a)p`
centered at the cube centre: `C(d) 3^n |p|` times the derivative gauge.  This
is the paper's `3^m ‖∇ j_k‖_{L^∞(cu_m)}` summed over the upper shells
(proof of `l.w.basic.regbounds`). -/
def upperShellFluxSupBound (n a b : ℕ) (p : Vec d) (omega : ShellSeq d) : ℝ :=
  upperShellFluxConst d * (3 : ℝ) ^ n * vecNorm p *
    upperShellDerivGauge n a b omega

theorem upperShellFluxSupBound_nonneg (n a b : ℕ) (p : Vec d)
    (omega : ShellSeq d) : 0 ≤ upperShellFluxSupBound n a b p omega := by
  refine mul_nonneg (mul_nonneg (mul_nonneg (upperShellFluxConst_nonneg d) ?_)
    (vecNorm_nonneg p)) (upperShellDerivGauge_nonneg n a b omega)
  positivity

theorem measurable_upperShellFluxSupBound (n a b : ℕ) (p : Vec d) :
    Measurable (upperShellFluxSupBound n a b p : ShellSeq d → ℝ) :=
  (measurable_upperShellDerivGauge n a b).const_mul _

/-- **The pointwise Poincaré step of the upper shell** (proof of `l.w.basic.regbounds`): on `cu_n`
the upper-shell flux differs from its value at the cube centre by at most
`C(d) 3^n |p| ∑_{k ∈ (a,b]} ‖∇ j_k‖_{L^∞(cu_n)}`. -/
theorem vecNorm_streamFlux_sub_center_le (omega : ShellSeq d) (n a b : ℕ)
    (p : Vec d) {x : Vec d} (hx : x ∈ openCubeSet (originCube d (n : ℤ)))
    (hab : a ≤ b) :
    vecNorm (matVecMul (streamCutoff omega b x - streamCutoff omega a x) p -
        matVecMul (streamCutoff omega b 0 - streamCutoff omega a 0) p) ≤
      upperShellFluxSupBound n a b p omega := by
  have hxrepr := congrFun (streamCutoff_sub_eq_finiteShellIncrement omega hab) x
  have h0repr := congrFun (streamCutoff_sub_eq_finiteShellIncrement omega hab) 0
  rw [hxrepr, h0repr]
  have hsub : matVecMul (finiteShellIncrement omega a b x) p -
      matVecMul (finiteShellIncrement omega a b 0) p =
      matVecMul (finiteShellIncrement omega a b x -
        finiteShellIncrement omega a b 0) p := by
    funext i
    simp only [matVecMul, Matrix.sub_apply, Pi.sub_apply,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsub]
  refine (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _).trans ?_
  refine (mul_le_mul_of_nonneg_right
    (matrixOperatorNorm_finiteShellIncrement_sub_center_le omega n a b hx)
    (vecNorm_nonneg p)).trans ?_
  have hgauge := upperShellDerivGauge_nonneg n a b omega
  have hx3 : vecNorm x ≤ Real.sqrt d * ((3 : ℝ) ^ n / 2) :=
    vecNorm_le_of_mem_openCubeSet_originCube hx
  have hstep :
      (d : ℝ) ^ 2 * (upperShellDerivGauge n a b omega * vecNorm x) ≤
        (d : ℝ) ^ 2 *
          (upperShellDerivGauge n a b omega * (Real.sqrt d * ((3 : ℝ) ^ n / 2))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx3 hgauge)
      (sq_nonneg (d : ℝ))
  refine (mul_le_mul_of_nonneg_right hstep (vecNorm_nonneg p)).trans_eq ?_
  unfold upperShellFluxSupBound upperShellFluxConst
  ring

/-! ## The normalized cube norms of the centered upper-shell flux -/

/-- On a cube the normalized `L^q` norm is bounded by any pointwise bound valid
on the open cube: the normalized cube measure is a probability measure carried
by the half-open cube, which agrees with the open cube up to a null set. -/
theorem cubeLpENorm_le_of_forall_mem_openCubeSet {E : Type*}
    [NormedAddCommGroup E] {Q : TriadicCube d} {q : ℝ≥0∞} {f : Vec d → E}
    {c : ℝ} (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q))
    (h : ∀ x ∈ openCubeSet Q, ‖f x‖ ≤ c) :
    Section2.Norms.cubeLpENorm Q q f ≤ ENNReal.ofReal c := by
  have hae : ∀ᵐ x ∂(normalizedCubeMeasure Q), ‖f x‖ₑ ≤ ENNReal.ofReal c := by
    have h0 : ∀ᵐ x ∂(volume.restrict (cubeSet Q)),
        ‖f x‖ₑ ≤ ENNReal.ofReal c := by
      rw [Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q)]
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (h x hx)
    exact Measure.ae_smul_measure h0 _
  have hbound := eLpNorm_le_of_ae_enorm_bound (p := q) hf hae
  simpa only [cubeLpENorm, ge_iff_le, normalizedCubeMeasure_apply_univ Q, ENNReal.one_rpow, smul_eq_mul, mul_one]
    using hbound

/-- The vector-field reading of the previous bound, with the Euclidean
magnitude. -/
theorem vecCubeLpENorm_le_of_forall_mem_openCubeSet {Q : TriadicCube d}
    {q : ℝ≥0∞} {F : Vec d → Vec d} {c : ℝ}
    (hF : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q))
    (h : ∀ x ∈ openCubeSet Q, vecNorm (F x) ≤ c) :
    vecCubeLpENorm Q q F ≤ ENNReal.ofReal c :=
  cubeLpENorm_le_of_forall_mem_openCubeSet (f := hilbertifyVecField F) hF h

theorem continuous_matVecMul_comp {A : Vec d → Mat d} (hA : Continuous A) (p : Vec d) :
    Continuous fun x => matVecMul (A x) p := by
  refine continuous_pi fun i => ?_
  exact continuous_finsetSum _ fun j _ =>
    (((continuous_apply j).comp ((continuous_apply i).comp hA))).mul continuous_const

/-! ## The cube average as a centering -/

theorem volume_openCubeSet_ne_zero (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ 0 := by
  rw [← measure_congr (cubeSet_ae_eq_openCubeSet Q)]
  exact volume_cubeSet_ne_zero Q

theorem volume_openCubeSet_ne_top (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ ⊤ := by
  rw [← measure_congr (cubeSet_ae_eq_openCubeSet Q)]
  exact (isBounded_cubeSet Q).measure_lt_top.ne

/-- Subtracting a constant from an integrand subtracts it from the normalized
average. -/
theorem volumeAverage_sub_const {U : Set (Vec d)} (hUne : volume U ≠ 0)
    (hUtop : volume U ≠ ⊤) {f : Vec d → ℝ}
    (hf : IntegrableOn f U volume) (c : ℝ) :
    volumeAverage U (fun x => f x - c) = volumeAverage U f - c := by
  have hvpos : 0 < (volume U).toReal := ENNReal.toReal_pos hUne hUtop
  have hcint : IntegrableOn (fun _ : Vec d => c) U volume :=
    integrableOn_const hUtop
  unfold volumeAverage
  rw [integral_sub hf hcint, setIntegral_const, smul_eq_mul, measureReal_def,
    mul_sub]
  rw [show (volume U).toReal⁻¹ * ((volume U).toReal * c) = c by field_simp]

/-- The half-open and open cube averages agree: the two sets differ by a null
set.  The apriori anchor writes its centering against `cubeSet`; every estimate
below is proved on `openCubeSet`.  Private repetition of the bridge kept public
in `Section3.ResponseFields.LpEstimates` (`volumeAverage_cubeSet_eq_openCubeSet`);
`private` so that a module may import both halves of Section 3. -/
private theorem volumeAverage_cubeSet_eq_openCubeSet (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) f = volumeAverage (openCubeSet Q) f := by
  unfold volumeAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    measure_congr (cubeSet_ae_eq_openCubeSet Q)]

theorem volumeAverageVec_cubeSet_eq_openCubeSet (Q : TriadicCube d)
    (F : Vec d → Vec d) :
    volumeAverageVec (cubeSet Q) F = volumeAverageVec (openCubeSet Q) F := by
  funext i
  exact volumeAverage_cubeSet_eq_openCubeSet Q (fun x => F x i)

theorem abs_apply_le_vecNorm (v : Vec d) (i : Fin d) : |v i| ≤ vecNorm v := by
  refine abs_le_of_sq_le_sq ?_ (vecNorm_nonneg v)
  rw [vecNorm_sq_eq_vecNormSq]
  simpa only [pow_two] using sq_apply_le_vecNormSq v i

theorem vecNorm_le_sqrt_dim_mul (v : Vec d) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ i, |v i| ≤ A) : vecNorm v ≤ Real.sqrt d * A := by
  have hsq : vecNormSq v ≤ (d : ℝ) * A ^ 2 := by
    calc
      vecNormSq v = ∑ i, v i * v i := rfl
      _ ≤ ∑ _i : Fin d, A ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi := h i
        have hsq' : (v i) ^ 2 ≤ A ^ 2 := by
          rw [sq_le_sq]
          simpa only [abs_of_nonneg hA] using hi
        simpa only [pow_two] using hsq'
      _ = (d : ℝ) * A ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : 0 ≤ Real.sqrt d * A := mul_nonneg (Real.sqrt_nonneg _) hA
  have hsq2 : vecNorm v ^ 2 ≤ (Real.sqrt d * A) ^ 2 := by
    rw [vecNorm_sq_eq_vecNormSq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    exact hsq
  have hfin := Real.sqrt_le_sqrt hsq2
  rwa [Real.sqrt_sq (vecNorm_nonneg v), Real.sqrt_sq hB] at hfin

theorem vecNorm_eq_norm_ofVec (v : Vec d) : vecNorm v = ‖HilbertVec.ofVec v‖ :=
  rfl

theorem vecNorm_sub_le_add (u v : Vec d) :
    vecNorm (u - v) ≤ vecNorm u + vecNorm v := by
  have h : HilbertVec.ofVec (u - v) = HilbertVec.ofVec u - HilbertVec.ofVec v :=
    map_sub (HilbertVec.linearEquivVec d).symm u v
  rw [vecNorm_eq_norm_ofVec, vecNorm_eq_norm_ofVec, vecNorm_eq_norm_ofVec, h]
  exact norm_sub_le _ _

/-- **The cube average is a near-optimal centering.** If a field lies within
`A` of a constant `c` on the open cube, then its cube average lies within
`√d A` of `c`; consequently the field centered at its cube average lies within
`(1 + √d) A` of zero.  This is the step that lets the printed proof center the
flux at `(F)_{cu_m}` while every estimate is proved against the value at the
cube centre. -/
theorem vecNorm_volumeAverageVec_sub_const_le {Q : TriadicCube d}
    {F : Vec d → Vec d}
    (hF : ∀ i, IntegrableOn (fun x => F x i) (openCubeSet Q) volume)
    {c : Vec d} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ x ∈ openCubeSet Q, vecNorm (F x - c) ≤ A) :
    vecNorm (volumeAverageVec (openCubeSet Q) F - c) ≤ Real.sqrt d * A := by
  refine vecNorm_le_sqrt_dim_mul _ hA fun i => ?_
  have hcoord : volumeAverageVec (openCubeSet Q) F i - c i =
      volumeAverage (openCubeSet Q) (fun x => F x i - c i) := by
    rw [volumeAverage_sub_const (volume_openCubeSet_ne_zero Q)
      (volume_openCubeSet_ne_top Q) (hF i) (c i)]
    rfl
  rw [show (volumeAverageVec (openCubeSet Q) F - c) i =
      volumeAverageVec (openCubeSet Q) F i - c i from rfl, hcoord]
  refine abs_volumeAverage_le (volume_openCubeSet_ne_zero Q)
    (volume_openCubeSet_ne_top Q) fun x hx => ?_
  exact le_trans (abs_apply_le_vecNorm (F x - c) i) (h x hx)

/-! ## Continuity and integrability of the upper-shell flux -/

theorem continuous_streamCutoff_sub (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) :
    Continuous (fun x : Vec d =>
      streamCutoff omega b x - streamCutoff omega a x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  exact (hasFDerivAt_streamCutoff_sub omega hab x).continuousAt

theorem continuous_streamFlux_apply (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (p : Vec d) (i : Fin d) :
    Continuous (fun x : Vec d =>
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) p i) :=
  continuous_finsetSum Finset.univ fun l _ =>
    ((matEntryCLM i l).continuous.comp
      (continuous_streamCutoff_sub omega hab)).mul continuous_const

theorem integrableOn_streamFlux_apply (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (p : Vec d) (Q : TriadicCube d) (i : Fin d) :
    IntegrableOn (fun x : Vec d =>
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) p i)
      (openCubeSet Q) volume := by
  have hb : Bornology.IsBounded (openCubeSet Q) :=
    (isBounded_cubeSet Q).subset (openCubeSet_subset_cubeSet Q)
  exact (((continuous_streamFlux_apply omega hab p i).continuousOn
    ).integrableOn_compact hb.isCompact_closure).mono_set subset_closure

end

end SuperdiffusionCLT.Section3.ResponseFields
