/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB
public import SuperdiffusionCLT.Section3.Setup.Scales

/-!
# The flux estimates behind `l.w.basic.regbounds`

In the proof of `e.nablaw.Lt` of the paper, the response `w` of `e.def.w` is the
Dirichlet response of the flux `F = (k_{L'} − k_{ℓ'})p` on `cu_m`, and the printed
proof bounds the three response norms by the three parenthesized flux quantities

* `‖F − (F)_{cu_m}‖_{L̲^8(cu_m)}`,
* `‖∇F‖_{L̲^8(cu_m)}`, and
* `‖F − (F)_{cu_m}‖_{H̲^{1/2}(cu_m)}`,

after splitting the stream increment at the scale `m − 1` into the lower shell
`k_{m−1} − k_{ℓ'}` (a large-cube quantity, controlled by the shell-increment
scale estimates) and the upper shell `k_{L'} − k_{m−1}` (a small-cube quantity,
controlled by the shell derivative display `e.nabla.kmn.Linfty` proved in
`RegboundsInputs.lean`).

This module collects the flux-side material of that proof:

* the two Orlicz bookkeeping lemmas the assembly needs (a deterministic
  constant has a `Γ_σ` tail, and passing to `|·|` does not change one);
* the continuity of the flux and of its classical Jacobian, which is what the
  `L̲^q` triangle inequality needs on the normalized cube measure;
* the additive split of the flux and of its Jacobian at an intermediate scale;
* the pointwise domination `|Mp| ≤ ‖M‖ |p|` in the `L̲^q` and Gagliardo norms,
  which converts the matrix-valued shell-increment estimates into estimates for
  the vector-valued flux; and
* the first parenthesized term of the printed proof, `‖F − (F)_{cu_m}‖_{L̲^q}`,
  together with the second one, `‖∇F‖_{L̲^8}`.

The `H̲^{1/2}` term and the assembly are in `RegboundsB.lean`.
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
open SuperdiffusionCLT.Section3.Setup
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## Orlicz bookkeeping -/

/-- Measurability of the absolute value of a real random variable. -/
theorem measurable_abs_of {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega → ℝ} (h : Measurable X) : Measurable fun omega => |X omega| := by
  fun_prop

/-- Passing to the absolute value does not change a `Γ_σ` tail: the relation is
defined through `|X|` already. -/
theorem isBigO_gammaSigma_abs {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {sigma A : ℝ} {X : Omega → ℝ} :
    IsBigO mu (gammaSigma sigma) (fun omega => |X omega|) A ↔
      IsBigO mu (gammaSigma sigma) X A := by
  simp only [IsBigO, abs_abs]

/-- A deterministic constant has every `Γ_σ` amplitude that dominates it. -/
theorem isBigO_gammaSigma_const {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (sigma : ℝ) {c A : ℝ} (h : |c| ≤ A) :
    IsBigO mu (gammaSigma sigma) (fun _ : Omega => c) A := by
  intro t ht
  have hA : 0 ≤ A := le_trans (abs_nonneg c) h
  have hAt : A ≤ A * t := le_mul_of_one_le_right hA ht
  have hempty : upperTailEvent (fun omega : Omega => |(fun _ : Omega => c) omega|)
      (A * t) = (∅ : Set Omega) := by
    ext omega
    simp only [mem_upperTailEvent, Set.mem_empty_iff_false, iff_false, not_lt]
    exact le_trans h hAt
  rw [hempty, measureReal_empty]
  rw [gammaSigma_inv]
  exact (Real.exp_pos _).le

/-! ## Continuity of the flux and of its classical Jacobian -/

/-- The flux `(k_b − k_a)p` is continuous. -/
theorem continuous_streamFlux (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (p : Vec d) :
    Continuous (fun x : Vec d =>
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) p) :=
  continuous_pi fun i => continuous_streamFlux_apply omega hab p i

/-- A continuous vector field is almost everywhere strongly measurable in the
Euclidean Hilbert reading, for every measure. -/
theorem aestronglyMeasurable_hilbertifyVecField_of_continuous
    {F : Vec d → Vec d} (hF : Continuous F) (mu : Measure (Vec d)) :
    AEStronglyMeasurable (hilbertifyVecField F) mu :=
  (((HilbertVec.ofVecL d).continuous).comp hF).aestronglyMeasurable

/-- The classical Jacobian of the flux is continuous: each flux component is
`C¹`, so its Fréchet derivative is continuous, and the Hilbert matrix carrier is
a continuous linear image of the algebraic one. -/
theorem continuous_streamFluxJacobian (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (p : Vec d) :
    Continuous (fun x : Vec d =>
      HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega a b p i x j)) := by
  have hmat : Continuous (fun x : Vec d =>
      (fun i j => streamFluxWeakGradient omega a b p i x j : Mat d)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((ContinuousLinearMap.apply ℝ ℝ (basisVec j)).continuous).comp
      ((contDiff_streamFlux_apply omega hab p i).continuous_fderiv (by simp))
  exact ((HilbertMat.continuousLinearEquivMat d).symm.continuous).comp hmat

/-! ## The split of the flux at an intermediate scale -/

/-- The stream flux splits additively at any intermediate cutoff level. -/
theorem streamFlux_split (omega : ShellSeq d) (a c b : ℕ) (p : Vec d) (x : Vec d) :
    matVecMul (streamCutoff omega b x - streamCutoff omega a x) p =
      matVecMul (streamCutoff omega b x - streamCutoff omega c x) p +
        matVecMul (streamCutoff omega c x - streamCutoff omega a x) p := by
  rw [← add_matVecMul]
  congr 1
  abel

/-- The classical Jacobian of the flux splits at any intermediate cutoff level
of the shell interval. -/
theorem streamFluxWeakGradient_split (omega : ShellSeq d) {a c b : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b) (p : Vec d) (i : Fin d) (x : Vec d) (j : Fin d) :
    streamFluxWeakGradient omega a b p i x j =
      streamFluxWeakGradient omega c b p i x j +
        streamFluxWeakGradient omega a c p i x j := by
  rw [streamFluxWeakGradient_apply omega (hac.trans hcb) p i x j,
    streamFluxWeakGradient_apply omega hcb p i x j,
    streamFluxWeakGradient_apply omega hac p i x j,
    ← Finset.sum_Ioc_consecutive (fun k => ShellField.deriv (omega k) x) hac hcb,
    add_apply, add_matVecMul]
  simp only [Pi.add_apply]
  exact add_comm _ _

/-- The Hilbert-matrix carrier of the previous split. -/
theorem hilbertMat_streamFluxWeakGradient_split (omega : ShellSeq d) {a c b : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b) (p : Vec d) (x : Vec d) :
    HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega a b p i x j) =
      HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega c b p i x j) +
        HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega a c p i x j) := by
  refine HilbertMat.ext fun i j => ?_
  show streamFluxWeakGradient omega a b p i x j =
    streamFluxWeakGradient omega c b p i x j +
      streamFluxWeakGradient omega a c p i x j
  exact streamFluxWeakGradient_split omega hac hcb p i x j

/-! ## `|Mp| ≤ ‖M‖ |p|` in the normalized cube norms -/

private theorem enorm_vecNorm (p : Vec d) :
    ‖vecNorm p‖ₑ = ENNReal.ofReal (vecNorm p) := by
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (vecNorm_nonneg p)]

private theorem norm_hilbertifyVecField_sub (F : Vec d → Vec d) (x y : Vec d) :
    ‖hilbertifyVecField F x - hilbertifyVecField F y‖ = vecNorm (F x - F y) := by
  have h : hilbertifyVecField F x - hilbertifyVecField F y =
      HilbertVec.ofVec (F x - F y) :=
    (map_sub (HilbertVec.linearEquivVec d).symm (F x) (F y)).symm
  rw [h]
  exact (vecNorm_eq_norm_ofVec (F x - F y)).symm

/-- **The flux in `L̲^q` is dominated by the shell increment.** The pointwise
bound `|Mp| ≤ ‖M‖ |p|`, integrated on the normalized cube
measure. -/
theorem vecCubeLpENorm_streamFlux_le (Q : TriadicCube d) (q : ℝ≥0∞)
    (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b) (p : Vec d) :
    vecCubeLpENorm Q q
        (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) p) ≤
      ENNReal.ofReal (vecNorm p) *
        Section2.Norms.cubeLpENorm Q q
          (fun x => (finiteShellIncrement omega a b x : Mat d)) := by
  have hsmul := Section2.Norms.cubeLpENorm_const_smul Q q (vecNorm p)
    (fun x : Vec d => (finiteShellIncrement omega a b x : Mat d))
  rw [enorm_vecNorm] at hsmul
  rw [← hsmul]
  show Section2.Norms.cubeLpENorm Q q (hilbertifyVecField _) ≤ _
  have hc : Continuous fun x : Vec d =>
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) p :=
    continuous_matVecMul_comp
      ((continuous_streamCutoff_apply omega b).sub (continuous_streamCutoff_apply omega a)) p
  refine Section2.Norms.cubeLpENorm_mono_enorm
    (aestronglyMeasurable_hilbertifyVecField_of_continuous hc _) fun x => ?_
  rw [norm_hilbertifyVecField_apply]
  have hK : (finiteShellIncrement omega a b x : Mat d) =
      streamCutoff omega b x - streamCutoff omega a x :=
    finiteShellIncrement_apply_eq_streamCutoff_sub omega hab x
  have hnorm :
      ‖(vecNorm p • fun z : Vec d => (finiteShellIncrement omega a b z : Mat d)) x‖ =
        vecNorm p *
          matrixOperatorNorm (streamCutoff omega b x - streamCutoff omega a x) := by
    show ‖vecNorm p • (finiteShellIncrement omega a b x : Mat d)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (vecNorm_nonneg p), hK,
      matrixOperatorNorm_eq_l2_opNorm]
  rw [hnorm, mul_comm]
  exact vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ p

/-- **The centered flux's Gagliardo seminorm is dominated by the shell
increment's.** Constants cancel in the increments, so the centering plays no
role. -/
theorem cubeEuclideanGagliardoESeminorm_streamFlux_sub_const_le (Q : TriadicCube d)
    (s : ℝ) (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b) (p : Vec d) (c : Vec d) :
    Section2.Norms.cubeEuclideanGagliardoESeminorm Q s 2
        (hilbertifyVecField fun x =>
          matVecMul (streamCutoff omega b x - streamCutoff omega a x) p - c) ≤
      ENNReal.ofReal (vecNorm p) *
        Section2.Norms.cubeEuclideanGagliardoESeminorm Q s 2
          (fun x => (finiteShellIncrement omega a b x : Mat d)) := by
  have hsmul := Section2.Norms.cubeEuclideanGagliardoESeminorm_const_smul Q s 2
    (vecNorm p) (fun x : Vec d => (finiteShellIncrement omega a b x : Mat d))
  rw [enorm_vecNorm] at hsmul
  rw [← hsmul]
  have hc : Continuous fun x : Vec d =>
      matVecMul (streamCutoff omega b x - streamCutoff omega a x) p :=
    continuous_matVecMul_comp
      ((continuous_streamCutoff_apply omega b).sub (continuous_streamCutoff_apply omega a)) p
  refine Section2.Norms.cubeEuclideanGagliardoESeminorm_mono_enorm
    (Section2.Norms.aestronglyMeasurable_euclideanGagliardoKernel
      (aestronglyMeasurable_hilbertifyVecField_of_continuous (hc.sub continuous_const) _))
    fun x y => ?_
  rw [norm_hilbertifyVecField_sub]
  have hKx : (finiteShellIncrement omega a b x : Mat d) =
      streamCutoff omega b x - streamCutoff omega a x :=
    finiteShellIncrement_apply_eq_streamCutoff_sub omega hab x
  have hKy : (finiteShellIncrement omega a b y : Mat d) =
      streamCutoff omega b y - streamCutoff omega a y :=
    finiteShellIncrement_apply_eq_streamCutoff_sub omega hab y
  have hnorm :
      ‖(vecNorm p • fun z : Vec d => (finiteShellIncrement omega a b z : Mat d)) x -
          (vecNorm p • fun z : Vec d => (finiteShellIncrement omega a b z : Mat d)) y‖ =
        vecNorm p *
          matrixOperatorNorm ((streamCutoff omega b x - streamCutoff omega a x) -
            (streamCutoff omega b y - streamCutoff omega a y)) := by
    show ‖vecNorm p • (finiteShellIncrement omega a b x : Mat d) -
      vecNorm p • (finiteShellIncrement omega a b y : Mat d)‖ = _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (vecNorm_nonneg p), hKx, hKy, matrixOperatorNorm_eq_l2_opNorm]
  rw [hnorm, mul_comm]
  have hsplit :
      (matVecMul (streamCutoff omega b x - streamCutoff omega a x) p - c) -
          (matVecMul (streamCutoff omega b y - streamCutoff omega a y) p - c) =
        matVecMul ((streamCutoff omega b x - streamCutoff omega a x) -
          (streamCutoff omega b y - streamCutoff omega a y)) p := by
    rw [sub_sub_sub_cancel_right]
    exact (sub_matVecMul (streamCutoff omega b x - streamCutoff omega a x)
      (streamCutoff omega b y - streamCutoff omega a y) p).symm
  rw [hsplit]
  exact vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ p

/-! ## The scale arithmetic of the amplitudes -/

/-- `h ≥ 1` gives `h^{1/2} ≥ 1`. -/
theorem one_le_rpow_h {S : ScaleSelection} (hS : ScalesOrdering S) :
    (1 : ℝ) ≤ ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
  have h1 : (1 : ℝ) ≤ ((S.h : ℕ) : ℝ) := by
    exact_mod_cast scalesOrdering_one_le_h hS
  simpa using Real.one_le_rpow h1 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)

theorem rpow_h_pos {S : ScaleSelection} (hS : ScalesOrdering S) :
    (0 : ℝ) < ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
  lt_of_lt_of_le zero_lt_one (one_le_rpow_h hS)

/-- `3^m (3^{m−1})^{-1} = 3`, the only place the cube scale of the upper shell
enters the amplitude. -/
theorem pow_three_m_mul_inv_pred {S : ScaleSelection} (hS : ScalesOrdering S) :
    (3 : ℝ) ^ S.m * ((3 : ℝ) ^ (S.m - 1))⁻¹ = 3 := by
  have hm : S.m - 1 + 1 = S.m := by
    have := hS.ellPrime_lt_m
    omega
  have hne : ((3 : ℝ) ^ (S.m - 1)) ≠ 0 := by positivity
  have hpow : (3 : ℝ) ^ S.m = (3 : ℝ) ^ (S.m - 1) * 3 := by
    conv_lhs => rw [← hm]
    rw [pow_succ]
  rw [hpow]
  field_simp

/-- `(3^{m−1})^{-1} ≤ 3^{-ℓ'}`, since `ℓ' ≤ m − 1`. -/
theorem inv_pow_three_pred_le_rpow_neg_ellPrime {S : ScaleSelection}
    (hS : ScalesOrdering S) :
    ((3 : ℝ) ^ (S.m - 1))⁻¹ ≤ (3 : ℝ) ^ (-(S.ellPrime : ℝ)) := by
  have hle : S.ellPrime ≤ S.m - 1 := by
    have := hS.ellPrime_lt_m
    omega
  have h1 : ((3 : ℝ) ^ (S.m - 1))⁻¹ = (3 : ℝ) ^ (-(((S.m - 1 : ℕ)) : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  rw [h1]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : ((S.ellPrime : ℕ) : ℝ) ≤ ((S.m - 1 : ℕ) : ℝ) := by exact_mod_cast hle
  linarith only [this]

/-- `h ≤ 3^h`, in the real form used to absorb `h^{1/2}` into `3^{h/2}`. -/
theorem nat_le_rpow_three {k : ℕ} : ((k : ℕ) : ℝ) ≤ (3 : ℝ) ^ ((k : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  have hnat : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
  exact_mod_cast hnat.le

/-- **The absorption of `h^{1/2}` by the `H̲^{1/2}` weight**: the printed last
step of `l.w.basic.regbounds`, `3^{ℓ'/2} 3^{-m/2} h^{1/2} ≤ 1` under
`m = ℓ' + h`. -/
theorem cubeHsWeight_mul_rpow_h_le (S : ScaleSelection) :
    ((3 : ℝ) ^ (S.m : ℤ)) ^ (-((1 : ℝ) / 2)) * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤
      (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hzp : ((3 : ℝ) ^ (S.m : ℤ)) = (3 : ℝ) ^ ((S.m : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    norm_cast
  have hweight : ((3 : ℝ) ^ (S.m : ℤ)) ^ (-((1 : ℝ) / 2)) =
      (3 : ℝ) ^ (-(((S.m : ℕ) : ℝ) / 2)) := by
    rw [hzp, ← Real.rpow_mul h3.le]
    ring_nf
  have hsplit : ((S.m : ℕ) : ℝ) = ((S.ellPrime : ℕ) : ℝ) + ((S.h : ℕ) : ℝ) := by
    have := S.ellPrime_add_h
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this.symm
  have hfac : (3 : ℝ) ^ (-(((S.m : ℕ) : ℝ) / 2)) =
      (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)) * (3 : ℝ) ^ (-(((S.h : ℕ) : ℝ) / 2)) := by
    rw [← Real.rpow_add h3, hsplit]
    ring_nf
  have hkey : (3 : ℝ) ^ (-(((S.h : ℕ) : ℝ) / 2)) * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ 1 := by
    have hhle : ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ (3 : ℝ) ^ (((S.h : ℕ) : ℝ) / 2) := by
      have hmono := Real.rpow_le_rpow (Nat.cast_nonneg S.h)
        (nat_le_rpow_three (k := S.h)) (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
      have hpow : ((3 : ℝ) ^ ((S.h : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) =
          (3 : ℝ) ^ (((S.h : ℕ) : ℝ) / 2) := by
        rw [← Real.rpow_mul h3.le]
        ring_nf
      rwa [hpow] at hmono
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(((S.h : ℕ) : ℝ) / 2)) :=
      Real.rpow_pos_of_pos h3 _
    have hmul := mul_le_mul_of_nonneg_left hhle hpos.le
    refine hmul.trans (le_of_eq ?_)
    rw [← Real.rpow_add h3]
    norm_num
  rw [hweight, hfac, mul_assoc]
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)) :=
    Real.rpow_pos_of_pos h3 _
  calc (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)) *
        ((3 : ℝ) ^ (-(((S.h : ℕ) : ℝ) / 2)) * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ≤
      (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)) * 1 :=
        mul_le_mul_of_nonneg_left hkey hpos.le
    _ = (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)) := mul_one _

/-! ## The `Γ₂` triangle inequality in the normalization used below -/

/-- The two-term `Γ₂` triangle inequality with both summands replaced by their
absolute values, at strictly positive amplitudes. -/
theorem isBigO_gammaSigma_abs_add_pos {X Y : ShellSeq d → ℝ} {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : IsBigO P.toMeasure (gammaSigma 2) X A)
    (hY : IsBigO P.toMeasure (gammaSigma 2) Y B) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega => |X omega| + |Y omega|)
      (gammaTriangleConst 2 * (A + B)) :=
  isBigO_gammaSigma_add_of_isBigO (by norm_num) hA hB
    (isBigO_gammaSigma_abs.2 hX) (isBigO_gammaSigma_abs.2 hY)
    (measurable_abs_of hXm) (measurable_abs_of hYm)

/-- The same, with both amplitudes first increased to strictly positive ones.
This is the form used when one summand is a deterministic shift whose amplitude
may vanish. -/
theorem isBigO_gammaSigma_abs_add {X Y : ShellSeq d → ℝ} {A B : ℝ}
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX : IsBigO P.toMeasure (gammaSigma 2) X A)
    (hY : IsBigO P.toMeasure (gammaSigma 2) Y B) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega => |X omega| + |Y omega|)
      (gammaTriangleConst 2 * ((|A| + 1) + (|B| + 1))) :=
  isBigO_gammaSigma_abs_add_pos (by positivity) (by positivity) hXm hYm
    (hX.mono_scale ((le_abs_self A).trans (le_add_of_nonneg_right zero_le_one)))
    (hY.mono_scale ((le_abs_self B).trans (le_add_of_nonneg_right zero_le_one)))

/-- The shifted shell-increment bound `C t + X` repackaged as a single
nonnegative measurable witness with a strictly positive `Γ₂` amplitude. -/
theorem isBigO_gammaSigma_shift {Ck tk Ak : ℝ} (htk : 0 ≤ tk)
    {Xk : ShellSeq d → ℝ} (hXkm : Measurable Xk)
    (hXkO : IsBigO P.toMeasure (gammaSigma 2) Xk Ak) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega => |Ck| * tk + |Xk omega|)
      (gammaTriangleConst 2 * ((|Ck| * tk + 1) + (|Ak| + 1))) := by
  have hct : (0 : ℝ) ≤ |Ck| * tk := mul_nonneg (abs_nonneg Ck) htk
  have hconst : IsBigO P.toMeasure (gammaSigma 2)
      (fun _ : ShellSeq d => |Ck| * tk) (|Ck| * tk) :=
    isBigO_gammaSigma_const _ _ (le_of_eq (abs_of_nonneg hct))
  have hsum := isBigO_gammaSigma_abs_add (P := P)
    (X := fun _ : ShellSeq d => |Ck| * tk) (Y := Xk)
    measurable_const hXkm hconst hXkO
  have hrw : (fun omega : ShellSeq d => |(|Ck| * tk)| + |Xk omega|) =
      fun omega : ShellSeq d => |Ck| * tk + |Xk omega| := by
    funext omega
    rw [abs_of_nonneg hct]
  rw [hrw, abs_of_nonneg hct] at hsum
  exact hsum

/-! ## The constants of the upper shell -/

/-- The amplitude constant of the upper-shell contribution to the first and
third parenthesized terms: the small-cube estimate of `RegboundsInputs.lean` at
the scales `(m, m − 1, L')`, whose `3^m (3^{m-1})^{-1}` collapses to `3`. -/
def regboundsUpperConst (d : ℕ) : ℝ :=
  3 * ((1 + Real.sqrt d) * (upperShellFluxConst d * gammaTriangleConst 2))

theorem regboundsUpperConst_nonneg (d : ℕ) : 0 ≤ regboundsUpperConst d := by
  have h1 : (0 : ℝ) ≤ upperShellFluxConst d := upperShellFluxConst_nonneg d
  have h2 : (0 : ℝ) < gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos (σ := 2)
  have h3 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  rw [regboundsUpperConst]
  positivity

/-- The amplitude constant of the upper-shell contribution to the second
parenthesized term (the Jacobian), with a harmless `+1` making it positive for
every dimension. -/
def regboundsJacobianConst (d : ℕ) : ℝ :=
  Real.sqrt d * gammaTriangleConst 2 + 1

theorem regboundsJacobianConst_pos (d : ℕ) : 0 < regboundsJacobianConst d := by
  have h2 : (0 : ℝ) < gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos (σ := 2)
  have h3 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  rw [regboundsJacobianConst]
  positivity

/-! ## Normalizing the shell-increment `L̲^q` estimate -/

/-- The gate's `L̲^q` clause at `(ℓ', m − 1, m)` has the shape
`‖k_{m−1} − k_{ℓ'}‖_{L̲^q(cu_m)} ≤ C (m−1−ℓ')^{1/2} + X` with
`X = O_{Γ₂}(A)` and `|A| ≤ α (m−1−ℓ')^{1/2}`.  Since `m − ℓ' = h`, this
repackages it as a single nonnegative measurable witness whose `Γ₂` amplitude
is a constant multiple of `h^{1/2}`, with the constant depending only on `C`
and `α`. -/
theorem exists_normalized_witness_gateLp {S : ScaleSelection}
    {q : ℝ≥0∞} {C alpha A : ℝ} (halpha : 0 ≤ alpha) (hSh : 1 ≤ S.h)
    {X : ShellSeq d → ℝ} (hXm : Measurable X)
    (hXO : IsBigO P.toMeasure (gammaSigma 2) X A)
    (hAle : |A| ≤ alpha * (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2))
    (hXle : ∀ omega : ShellSeq d,
      Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) q
          (fun x => (finiteShellIncrement omega S.ellPrime (S.m - 1) x : Mat d)) ≤
        ENNReal.ofReal
          (C * (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega)) :
    ∃ Y : ShellSeq d → ℝ, Measurable Y ∧ (∀ omega, 0 ≤ Y omega) ∧
      IsBigO P.toMeasure (gammaSigma 2) Y
        ((gammaTriangleConst 2 * ((|C| + 1) + (alpha + 1))) *
          ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ∧
      ∀ omega : ShellSeq d,
        Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) q
            (fun x => (finiteShellIncrement omega S.ellPrime (S.m - 1) x : Mat d)) ≤
          ENNReal.ofReal (Y omega) := by
  set t : ℝ := (((S.m - 1) - S.ellPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) with htdef
  set hh : ℝ := ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) with hhdef
  have ht0 : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hth : t ≤ hh := scaleSelection_rpow_pred_m_sub_ellPrime_le S (by norm_num)
  have hh1 : (1 : ℝ) ≤ hh := by
    have h1 : (1 : ℝ) ≤ ((S.h : ℕ) : ℝ) := by exact_mod_cast hSh
    rw [hhdef]
    simpa using Real.one_le_rpow h1 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
  have hgpos : (0 : ℝ) < gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos (σ := 2)
  refine ⟨fun omega => |C| * t + |X omega|,
    Measurable.const_add (measurable_abs_of hXm) _, ?_, ?_, ?_⟩
  · exact fun omega => by
      have := mul_nonneg (abs_nonneg C) ht0
      linarith only [this, abs_nonneg (X omega)]
  · refine (isBigO_gammaSigma_shift (P := P) ht0 hXm hXO).mono_scale ?_
    have h1 : |C| * t + 1 ≤ (|C| + 1) * hh := by
      have hA1 : |C| * t ≤ |C| * hh := mul_le_mul_of_nonneg_left hth (abs_nonneg C)
      have hA2 : (1 : ℝ) ≤ 1 * hh := by linarith only [hh1]
      linarith only [hA1, hA2]
    have h2 : |A| + 1 ≤ (alpha + 1) * hh := by
      have hA1 : |A| ≤ alpha * hh := hAle.trans (mul_le_mul_of_nonneg_left hth halpha)
      have hA2 : (1 : ℝ) ≤ 1 * hh := by linarith only [hh1]
      linarith only [hA1, hA2]
    have hsum : (|C| * t + 1) + (|A| + 1) ≤ ((|C| + 1) + (alpha + 1)) * hh := by
      have : ((|C| + 1) + (alpha + 1)) * hh = (|C| + 1) * hh + (alpha + 1) * hh := by
        ring
      rw [this]
      linarith only [h1, h2]
    calc gammaTriangleConst 2 * ((|C| * t + 1) + (|A| + 1)) ≤
        gammaTriangleConst 2 * (((|C| + 1) + (alpha + 1)) * hh) :=
          mul_le_mul_of_nonneg_left hsum hgpos.le
      _ = gammaTriangleConst 2 * ((|C| + 1) + (alpha + 1)) * hh := by ring
  · intro omega
    refine (hXle omega).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : C * t ≤ |C| * t := mul_le_mul_of_nonneg_right (le_abs_self C) ht0
    linarith only [h1, le_abs_self (X omega)]

/-! ## The centered flux in `L̲^q(cu_m)` -/

/-- **The first parenthesized term of `l.w.basic.regbounds`**, at the exponent `q` for
which a shell-increment estimate is supplied.

The flux `F = (k_{L'} − k_{ℓ'})p`, centered at the cube average of its upper
shell, is split at the scale `m − 1`: the upper shell is the small-cube
estimate `exists_witness_vecCubeLpENorm_streamFlux_sub_volumeAverage`, whose
amplitude carries no `h`; the lower shell is dominated by `|p|` times the
supplied large-cube `L̲^q` bound for `k_{m−1} − k_{ℓ'}`.  The amplitude of the
sum is `|p| h^{1/2}` times a constant depending only on `d` and on the
lower-shell constant. -/
theorem exists_witness_vecCubeLpENorm_centeredFlux
    (hJ3 : ShellLawJ3 d P) {S : ScaleSelection} (hS : ScalesOrdering S)
    {p : Vec d} (hp : 0 < vecNorm p) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {Bk : ℝ} (hBk : 0 < Bk) {Yk : ShellSeq d → ℝ} (hYkm : Measurable Yk)
    (hYknn : ∀ omega, 0 ≤ Yk omega)
    (hYkO : IsBigO P.toMeasure (gammaSigma 2) Yk
      (Bk * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2)))
    (hYkle : ∀ omega : ShellSeq d,
      Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) q
          (fun x => (finiteShellIncrement omega S.ellPrime (S.m - 1) x : Mat d)) ≤
        ENNReal.ofReal (Yk omega)) :
    ∃ Y : ShellSeq d → ℝ, Measurable Y ∧ (∀ omega, 0 ≤ Y omega) ∧
      IsBigO P.toMeasure (gammaSigma 2) Y
        ((gammaTriangleConst 2 * ((regboundsUpperConst d + 1) + Bk)) *
          (vecNorm p * ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2))) ∧
      ∀ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) q
            (fun x =>
              matVecMul (streamCutoff omega S.LPrime x -
                streamCutoff omega S.ellPrime x) p -
              volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
                (fun y => matVecMul (streamCutoff omega S.LPrime y -
                  streamCutoff omega (S.m - 1) y) p)) ≤
          ENNReal.ofReal (Y omega) := by
  have hlow : S.ellPrime ≤ S.m - 1 := by
    have := hS.ellPrime_lt_m
    omega
  have hup : S.m - 1 ≤ S.LPrime := by
    have := hS.m_lt_LPrime
    omega
  set hh : ℝ := ((S.h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) with hhdef
  have hh1 : (1 : ℝ) ≤ hh := one_le_rpow_h hS
  have hhpos : (0 : ℝ) < hh := rpow_h_pos hS
  have hkappa : (0 : ℝ) ≤ regboundsUpperConst d := regboundsUpperConst_nonneg d
  obtain ⟨Zup, hZupm, hZupO, hZuple⟩ :=
    exists_witness_vecCubeLpENorm_streamFlux_sub_volumeAverage (P := P) hJ3 p
      (scaleSelection_m_le_pred_m_add_one S) (scalesOrdering_pred_m_lt_LPrime hS)
  have hZup' : IsBigO P.toMeasure (gammaSigma 2) Zup
      ((regboundsUpperConst d + 1) * (vecNorm p * hh)) := by
    refine hZupO.mono_scale ?_
    have hkey : (1 + Real.sqrt d) *
        (upperShellFluxConst d * (3 : ℝ) ^ S.m * vecNorm p *
          (gammaTriangleConst 2 * ((3 : ℝ) ^ (S.m - 1))⁻¹)) =
        vecNorm p * ((1 + Real.sqrt d) * (upperShellFluxConst d *
          gammaTriangleConst 2 * ((3 : ℝ) ^ S.m * ((3 : ℝ) ^ (S.m - 1))⁻¹))) := by
      ring
    rw [hkey, pow_three_m_mul_inv_pred hS]
    have hEq : vecNorm p * ((1 + Real.sqrt d) *
        (upperShellFluxConst d * gammaTriangleConst 2 * 3)) =
        regboundsUpperConst d * vecNorm p := by
      rw [regboundsUpperConst]; ring
    rw [hEq]
    have hstep : regboundsUpperConst d * vecNorm p ≤
        (regboundsUpperConst d + 1) * (vecNorm p * 1) := by
      have : regboundsUpperConst d * vecNorm p ≤
          (regboundsUpperConst d + 1) * vecNorm p :=
        mul_le_mul_of_nonneg_right (by linarith only []) hp.le
      linarith only [this]
    refine hstep.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hkappa])
    exact mul_le_mul_of_nonneg_left hh1 hp.le
  have hYk' : IsBigO P.toMeasure (gammaSigma 2)
      (fun omega => vecNorm p * Yk omega) (Bk * (vecNorm p * hh)) := by
    refine (hYkO.const_mul hp.le).mono_scale (le_of_eq ?_)
    ring
  have hYknn' : ∀ omega : ShellSeq d, 0 ≤ vecNorm p * Yk omega := fun omega =>
    mul_nonneg hp.le (hYknn omega)
  have hYkm' : Measurable (fun omega : ShellSeq d => vecNorm p * Yk omega) :=
    Measurable.const_mul hYkm _
  refine ⟨fun omega => |Zup omega| + vecNorm p * Yk omega,
    Measurable.add (measurable_abs_of hZupm) hYkm', ?_, ?_, ?_⟩
  · exact fun omega => by linarith only [abs_nonneg (Zup omega), hYknn' omega]
  · have hApos : (0 : ℝ) < (regboundsUpperConst d + 1) * (vecNorm p * hh) := by
      have h1 : (0 : ℝ) < regboundsUpperConst d + 1 := by linarith only [hkappa]
      exact mul_pos h1 (mul_pos hp hhpos)
    have hBpos : (0 : ℝ) < Bk * (vecNorm p * hh) := mul_pos hBk (mul_pos hp hhpos)
    have hsum := isBigO_gammaSigma_abs_add_pos (P := P) (X := Zup)
      (Y := fun omega => vecNorm p * Yk omega) hApos hBpos hZupm hYkm' hZup' hYk'
    have habs : (fun omega : ShellSeq d =>
        |Zup omega| + |vecNorm p * Yk omega|) =
        fun omega : ShellSeq d => |Zup omega| + vecNorm p * Yk omega := by
      funext omega
      rw [abs_of_nonneg (hYknn' omega)]
    rw [habs] at hsum
    refine hsum.mono_scale (le_of_eq ?_)
    ring
  · intro omega
    have hfield : (fun x : Vec d =>
        matVecMul (streamCutoff omega S.LPrime x -
          streamCutoff omega S.ellPrime x) p -
          volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
            (fun y => matVecMul (streamCutoff omega S.LPrime y -
              streamCutoff omega (S.m - 1) y) p)) =
        fun x : Vec d =>
          (matVecMul (streamCutoff omega S.LPrime x -
            streamCutoff omega (S.m - 1) x) p -
            volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
              (fun y => matVecMul (streamCutoff omega S.LPrime y -
                streamCutoff omega (S.m - 1) y) p)) +
          matVecMul (streamCutoff omega (S.m - 1) x -
            streamCutoff omega S.ellPrime x) p := by
      funext x
      rw [streamFlux_split omega S.ellPrime (S.m - 1) S.LPrime p x]
      abel
    rw [hfield]
    refine le_trans (vecCubeLpENorm_add_le (Q := originCube d (S.m : ℤ)) hq
      (aestronglyMeasurable_hilbertifyVecField_of_continuous
        ((continuous_streamFlux omega hup p).sub continuous_const) _)
      (aestronglyMeasurable_hilbertifyVecField_of_continuous
        (continuous_streamFlux omega hlow p) _)) ?_
    have hA : vecCubeLpENorm (originCube d (S.m : ℤ)) q
        (fun x => matVecMul (streamCutoff omega S.LPrime x -
            streamCutoff omega (S.m - 1) x) p -
          volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
            (fun y => matVecMul (streamCutoff omega S.LPrime y -
              streamCutoff omega (S.m - 1) y) p)) ≤
        ENNReal.ofReal |Zup omega| :=
      le_trans (hZuple q omega) (ENNReal.ofReal_le_ofReal (le_abs_self _))
    have hB' : vecCubeLpENorm (originCube d (S.m : ℤ)) q
        (fun x => matVecMul (streamCutoff omega (S.m - 1) x -
          streamCutoff omega S.ellPrime x) p) ≤
        ENNReal.ofReal (vecNorm p * Yk omega) := by
      refine le_trans (vecCubeLpENorm_streamFlux_le _ q omega hlow p) ?_
      refine le_trans (mul_le_mul' le_rfl (hYkle omega)) ?_
      rw [← ENNReal.ofReal_mul (vecNorm_nonneg p)]
    refine le_trans (add_le_add hA hB') ?_
    rw [← ENNReal.ofReal_add (abs_nonneg _) (hYknn' omega)]
/-! ## The Jacobian of the flux in `L̲^8(cu_m)` -/

/-- **The second parenthesized term of `l.w.basic.regbounds`**.  The Jacobian of
`F = (k_{L'} − k_{ℓ'})p` is split at the scale `m − 1`: the shells `k ≥ m` are
the small-cube estimate `exists_witness_cubeLpENorm_streamFluxWeakGradient`,
whose amplitude is `√d |p| 3^{-(m-1)} ≤ √d |p| 3^{-ℓ'}`; the shells below the
cube scale are the supplied large-cube bound. -/
theorem exists_witness_cubeLpENorm_fluxJacobian
    (hJ3 : ShellLawJ3 d P) {S : ScaleSelection} (hS : ScalesOrdering S)
    {p : Vec d} (hp : 0 < vecNorm p)
    {Cn : ℝ} (hCn : 0 < Cn) {Yn : ShellSeq d → ℝ} (hYnm : Measurable Yn)
    (hYnnn : ∀ omega, 0 ≤ Yn omega)
    (hYnO : IsBigO P.toMeasure (gammaSigma 2) Yn
      (Cn * (vecNorm p * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))))
    (hYnle : ∀ omega : ShellSeq d,
      Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j =>
            streamFluxWeakGradient omega S.ellPrime (S.m - 1) p i x j)) ≤
        ENNReal.ofReal (Yn omega)) :
    ∃ Y : ShellSeq d → ℝ, Measurable Y ∧ (∀ omega, 0 ≤ Y omega) ∧
      IsBigO P.toMeasure (gammaSigma 2) Y
        ((gammaTriangleConst 2 * (regboundsJacobianConst d + Cn)) *
          (vecNorm p * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) ∧
      ∀ omega : ShellSeq d,
        Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
            (fun x => HilbertMat.ofMat (fun i j =>
              streamFluxWeakGradient omega S.ellPrime S.LPrime p i x j)) ≤
          ENNReal.ofReal (Y omega) := by
  have hlow : S.ellPrime ≤ S.m - 1 := by
    have := hS.ellPrime_lt_m
    omega
  have hup : S.m - 1 ≤ S.LPrime := by
    have := hS.m_lt_LPrime
    omega
  have hgpos : (0 : ℝ) < gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos (σ := 2)
  set dec : ℝ := (3 : ℝ) ^ (-(S.ellPrime : ℝ)) with hdecdef
  have hdecpos : 0 < dec := by
    rw [hdecdef]
    exact Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨Zj, hZjm, hZjO, hZjle⟩ :=
    exists_witness_cubeLpENorm_streamFluxWeakGradient (P := P) hJ3 p
      (scaleSelection_m_le_pred_m_add_one S) (scalesOrdering_pred_m_lt_LPrime hS)
  have hZj' : IsBigO P.toMeasure (gammaSigma 2) Zj
      (regboundsJacobianConst d * (vecNorm p * dec)) := by
    refine hZjO.mono_scale ?_
    have hEq : Real.sqrt d * vecNorm p *
        (gammaTriangleConst 2 * ((3 : ℝ) ^ (S.m - 1))⁻¹) =
        (Real.sqrt d * gammaTriangleConst 2) *
          (vecNorm p * ((3 : ℝ) ^ (S.m - 1))⁻¹) := by ring
    rw [hEq]
    have hfac : (0 : ℝ) ≤ Real.sqrt d * gammaTriangleConst 2 :=
      mul_nonneg (Real.sqrt_nonneg _) hgpos.le
    have hstep : vecNorm p * ((3 : ℝ) ^ (S.m - 1))⁻¹ ≤ vecNorm p * dec := by
      rw [hdecdef]
      exact mul_le_mul_of_nonneg_left
        (inv_pow_three_pred_le_rpow_neg_ellPrime hS) hp.le
    have h1 : (Real.sqrt d * gammaTriangleConst 2) *
        (vecNorm p * ((3 : ℝ) ^ (S.m - 1))⁻¹) ≤
        (Real.sqrt d * gammaTriangleConst 2) * (vecNorm p * dec) :=
      mul_le_mul_of_nonneg_left hstep hfac
    refine h1.trans ?_
    rw [regboundsJacobianConst]
    have h2 : (0 : ℝ) ≤ vecNorm p * dec := mul_nonneg hp.le hdecpos.le
    linarith only [h2]
  refine ⟨fun omega => |Zj omega| + Yn omega,
    Measurable.add (measurable_abs_of hZjm) hYnm, ?_, ?_, ?_⟩
  · exact fun omega => by linarith only [abs_nonneg (Zj omega), hYnnn omega]
  · have hsum := isBigO_gammaSigma_abs_add_pos (P := P) (X := Zj) (Y := Yn)
      (mul_pos (regboundsJacobianConst_pos d) (mul_pos hp hdecpos))
      (mul_pos hCn (mul_pos hp hdecpos)) hZjm hYnm hZj' hYnO
    have habs : (fun omega : ShellSeq d => |Zj omega| + |Yn omega|) =
        fun omega : ShellSeq d => |Zj omega| + Yn omega := by
      funext omega
      rw [abs_of_nonneg (hYnnn omega)]
    rw [habs] at hsum
    refine hsum.mono_scale (le_of_eq ?_)
    ring
  · intro omega
    have hfield : (fun x : Vec d =>
        HilbertMat.ofMat (fun i j =>
          streamFluxWeakGradient omega S.ellPrime S.LPrime p i x j)) =
        fun x : Vec d =>
          HilbertMat.ofMat (fun i j =>
            streamFluxWeakGradient omega (S.m - 1) S.LPrime p i x j) +
          HilbertMat.ofMat (fun i j =>
            streamFluxWeakGradient omega S.ellPrime (S.m - 1) p i x j) := by
      funext x
      exact hilbertMat_streamFluxWeakGradient_split omega hlow hup p x
    rw [hfield]
    refine le_trans (Section2.Norms.cubeLpENorm_add_le (Q := originCube d (S.m : ℤ))
      (by norm_num : (1 : ℝ≥0∞) ≤ 8)
      (continuous_streamFluxJacobian omega hup p).aestronglyMeasurable
      (continuous_streamFluxJacobian omega hlow p).aestronglyMeasurable) ?_
    refine le_trans (add_le_add
      (le_trans (hZjle 8 omega) (ENNReal.ofReal_le_ofReal (le_abs_self _)))
      (hYnle omega)) ?_
    rw [← ENNReal.ofReal_add (abs_nonneg _) (hYnnn omega)]

end

end SuperdiffusionCLT.Section3.ResponseFields
