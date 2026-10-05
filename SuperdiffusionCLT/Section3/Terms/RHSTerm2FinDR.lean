/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RFiniteB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2DispersionFinal
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2KmnBounds
public import SuperdiffusionCLT.Section3.Terms.ResponseHessianMeasurableB
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Frozen.Section3.WBasicRegbounds
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2FinalB

/-!
# The finiteness of the weak Jacobian of `R`

## Summary

This module discharges the residue `hFinDR` of `l.RHS.term2` — the clause
`hFinDR` of the named-witness reduction of `l.RHS.term2`: the finiteness of the annealed squared
`L̲²(cu_m)` norm of the weak
Jacobian `DR` of `R = (k_{L'} − k_ℓ) ∇w` at the named witness
`canonicalRJacobian`, with **no residual and no carried hypothesis** beyond the
standing shell laws `ShellLawPrefix`, `ShellLawJ1Restriction`, `ShellLawJ2`, `ShellLawJ3`,
`ShellLawJ4`, the dimension hypotheses `d`, `2 ≤ d`, the scale ordering
`ScalesOrdering S`, and the response `w` with `IsDirichletResponse`.

The paper writes
> `Combining this with~\eqref{e.nablaw.Lt} and the product rule gives`
and the display `e.RHS.term2.R.bounds` follows.  The product
rule is not printed as a formula; the formalization reads it at the
Hilbert–Schmidt density (`RHSTerm2DispersionFinal.streamGradJacobian_norm_le`,
formalized below as `canonicalRJacobian_norm_le_finDR`).  The four densities are
then dominated in the sample by the two clauses of the anchor
`Frozen.Section3.w_basic_regbounds` (`e.nablaw.Lt`) through their **measurable
tail witnesses**: the increment and the summed gradient at `Γ_{1/2}` (the
moment display `isBigOWith_gammaSigma_finiteShellIncrementPthMoment` at
`p = 4`, and `gradientSum_volumeAverage_two_ne_top`), and `‖∇²w‖`, `|∇w|` at
`Γ₂`.  The sample pairing is Cauchy–Schwarz `(2,2)` at the measurable witnesses
with a factor `4` for the two summands (`lintegral_sq_ne_top_of_two_tails`); the
cube step is Hölder `(4,4) → 2` (`cubeLpENorm_two_le_mul_four_add`).  Both are
pointwise per sample, so the clause `hMeasDR` of that reduction is **not**
consumed here.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Probability
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal
open scoped BigOperators Matrix

noncomputable section

variable {d : ℕ}

/-- The scalar density form: the `L̲^q(Q)` norm of a field valued in a normed
space is the `L̲^q(Q)` norm of its pointwise norm. -/
private theorem cubeLpENorm_norm_field_eq_finDR {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (q : ℝ≥0∞) (g : Vec d → E)
    (hg : AEStronglyMeasurable g (normalizedCubeMeasure Q)) :
    cubeLpENorm Q q (fun x => ‖g x‖) = cubeLpENorm Q q g :=
  le_antisymm (cubeLpENorm_mono_enorm (f := fun x => ‖g x‖) hg.norm fun x => by simp)
    (cubeLpENorm_mono_enorm (g := fun x => ‖g x‖) hg fun x => by simp)

/-- The fourth root step: `x ^ 4 ≤ y` implies `x ^ 2 ≤ y ^ (1/2)`. -/
private theorem sq_le_rpow_half_of_pow_four_le_finDR {x y : ℝ≥0∞}
    (h : x ^ (4 : ℕ) ≤ y) : x ^ (2 : ℕ) ≤ y ^ ((1 : ℝ) / 2) := by
  have hbase : (x ^ (4 : ℕ)) ^ ((1 : ℝ) / 2) = (x ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) :=
    congrArg (fun t : ℝ≥0∞ => t ^ ((1 : ℝ) / 2)) (ENNReal.rpow_natCast x 4).symm
  have h2 : x ^ (2 : ℝ) = (x ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  calc x ^ (2 : ℕ) = x ^ (2 : ℝ) := (ENNReal.rpow_natCast x 2).symm
    _ = (x ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := h2
    _ = (x ^ (4 : ℕ)) ^ ((1 : ℝ) / 2) := hbase.symm
    _ ≤ y ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow h (by norm_num)

/-- The square-root envelope: `y ^ (1/2) ≤ 1 + y` for every `y : ℝ≥0∞`. -/
private theorem rpow_half_le_one_add_finDR (y : ℝ≥0∞) : y ^ ((1 : ℝ) / 2) ≤ 1 + y := by
  rcases le_total y 1 with h | h
  · have h1 : y ^ ((1 : ℝ) / 2) ≤ (1 : ℝ≥0∞) ^ ((1 : ℝ) / 2) :=
      ENNReal.rpow_le_rpow h (by norm_num)
    rw [ENNReal.one_rpow] at h1
    exact h1.trans le_self_add
  · have h1 : y ^ ((1 : ℝ) / 2) ≤ y ^ (1 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le h (by norm_num)
    rw [ENNReal.rpow_one] at h1
    exact h1.trans le_add_self

/-- The square of a sum of two extended reals is at most four times the sum of
the squares. -/
private theorem add_sq_le_four_finDR (a b : ℝ≥0∞) :
    (a + b) ^ (2 : ℕ) ≤ 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by
  have hab : a * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    rcases le_total a b with h | h
    · calc a * b ≤ b * b := mul_le_mul' h le_rfl
        _ = b ^ (2 : ℕ) := (pow_two b).symm
        _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_add_self
    · calc a * b ≤ a * a := mul_le_mul' le_rfl h
        _ = a ^ (2 : ℕ) := (pow_two a).symm
        _ ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := le_self_add
  have haa : a * a ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    simp only [pow_two]
    exact le_self_add
  have hbb : b * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    simp only [pow_two]
    exact le_add_self
  have hba : b * a ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    rw [mul_comm]; exact hab
  calc (a + b) ^ (2 : ℕ) = (a + b) * (a + b) := pow_two _
    _ = (a * a + b * a) + (a * b + b * b) := by
        rw [add_mul, mul_add, mul_add]; abel
    _ ≤ ((a ^ (2 : ℕ) + b ^ (2 : ℕ)) + (a ^ (2 : ℕ) + b ^ (2 : ℕ))) +
        ((a ^ (2 : ℕ) + b ^ (2 : ℕ)) + (a ^ (2 : ℕ) + b ^ (2 : ℕ))) :=
        add_le_add (add_le_add haa hba) (add_le_add hab hbb)
    _ = 4 * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) := by ring

/-- **Finiteness of an annealed `L²` moment from four `Γ`-tails.**  An `N`
dominated pointwise by `A · B + A' · B'` has finite annealed second moment as
soon as `A⁴`, `A'⁴` are dominated by the `ofReal` of measurable witnesses with
finite second moments and `B`, `B'` by the `ofReal` of measurable witnesses with
finite second and fourth moments — **no measurability of `A`, `B`, `A'`, `B'`
is required**.  The summands are separated by `add_sq_le_four_finDR` (a factor
four); each piece is then the single-product step `lintegral_sq_ne_top_of_tails`
written out, the pairing of the product rule at the weak Jacobian. -/
private theorem lintegral_sq_ne_top_of_two_tails {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {N A B A' B' : Omega → ℝ≥0∞} {ZK ZW ZK' ZW' : Omega → ℝ}
    (hZKm : AEMeasurable ZK mu) (hZWm : AEMeasurable ZW mu)
    (hZKm' : AEMeasurable ZK' mu) (hZWm' : AEMeasurable ZW' mu)
    (hN : ∀ omega : Omega, N omega ≤ A omega * B omega + A' omega * B' omega)
    (hA4 : ∀ omega : Omega, A omega ^ (4 : ℕ) ≤ ENNReal.ofReal (ZK omega))
    (hBle : ∀ omega : Omega, B omega ≤ ENNReal.ofReal (ZW omega))
    (hA4' : ∀ omega : Omega, A' omega ^ (4 : ℕ) ≤ ENNReal.ofReal (ZK' omega))
    (hBle' : ∀ omega : Omega, B' omega ≤ ENNReal.ofReal (ZW' omega))
    (hZK2 : (∫⁻ omega : Omega, ENNReal.ofReal (ZK omega) ^ (2 : ℕ) ∂mu) ≠ ⊤)
    (hZW2 : (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) ≠ ⊤)
    (hZW4 : (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (4 : ℕ) ∂mu) ≠ ⊤)
    (hZK2' : (∫⁻ omega : Omega, ENNReal.ofReal (ZK' omega) ^ (2 : ℕ) ∂mu) ≠ ⊤)
    (hZW2' : (∫⁻ omega : Omega, ENNReal.ofReal (ZW' omega) ^ (2 : ℕ) ∂mu) ≠ ⊤)
    (hZW4' : (∫⁻ omega : Omega, ENNReal.ofReal (ZW' omega) ^ (4 : ℕ) ∂mu) ≠ ⊤) :
    (∫⁻ omega : Omega, N omega ^ (2 : ℕ) ∂mu) ≠ ⊤ := by
  have hX : AEMeasurable (fun omega : Omega => ENNReal.ofReal (ZK omega)) mu :=
    hZKm.ennreal_ofReal
  have hX' : AEMeasurable (fun omega : Omega => ENNReal.ofReal (ZK' omega)) mu :=
    hZKm'.ennreal_ofReal
  have hY : AEMeasurable (fun omega : Omega => ENNReal.ofReal (ZW omega)) mu :=
    hZWm.ennreal_ofReal
  have hY' : AEMeasurable (fun omega : Omega => ENNReal.ofReal (ZW' omega)) mu :=
    hZWm'.ennreal_ofReal
  have hY2 : AEMeasurable (fun omega : Omega => ENNReal.ofReal (ZW omega) ^ (2 : ℕ)) mu :=
    hY.pow_const 2
  have hY2' : AEMeasurable (fun omega : Omega => ENNReal.ofReal (ZW' omega) ^ (2 : ℕ)) mu :=
    hY'.pow_const 2
  have hA2 : ∀ omega : Omega, A omega ^ (2 : ℕ) ≤ 1 + ENNReal.ofReal (ZK omega) :=
    fun omega => (sq_le_rpow_half_of_pow_four_le_finDR (hA4 omega)).trans
      (rpow_half_le_one_add_finDR _)
  have hA2' : ∀ omega : Omega, A' omega ^ (2 : ℕ) ≤ 1 + ENNReal.ofReal (ZK' omega) :=
    fun omega => (sq_le_rpow_half_of_pow_four_le_finDR (hA4' omega)).trans
      (rpow_half_le_one_add_finDR _)
  have hpoint : ∀ omega : Omega, N omega ^ (2 : ℕ) ≤
      4 * ((1 + ENNReal.ofReal (ZK omega)) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ)) +
        4 * ((1 + ENNReal.ofReal (ZK' omega)) * ENNReal.ofReal (ZW' omega) ^ (2 : ℕ)) := by
    intro omega
    have hstep : A omega ^ (2 : ℕ) * B omega ^ (2 : ℕ) ≤
        (1 + ENNReal.ofReal (ZK omega)) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) :=
      mul_le_mul' (hA2 omega) (pow_le_pow_left' (hBle omega) 2)
    have hstep' : A' omega ^ (2 : ℕ) * B' omega ^ (2 : ℕ) ≤
        (1 + ENNReal.ofReal (ZK' omega)) * ENNReal.ofReal (ZW' omega) ^ (2 : ℕ) :=
      mul_le_mul' (hA2' omega) (pow_le_pow_left' (hBle' omega) 2)
    calc N omega ^ (2 : ℕ) ≤ (A omega * B omega + A' omega * B' omega) ^ (2 : ℕ) :=
          pow_le_pow_left' (hN omega) 2
      _ ≤ 4 * ((A omega * B omega) ^ (2 : ℕ) + (A' omega * B' omega) ^ (2 : ℕ)) :=
          add_sq_le_four_finDR _ _
      _ = 4 * (A omega ^ (2 : ℕ) * B omega ^ (2 : ℕ) +
            A' omega ^ (2 : ℕ) * B' omega ^ (2 : ℕ)) := by rw [mul_pow, mul_pow]
      _ ≤ 4 * ((1 + ENNReal.ofReal (ZK omega)) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) +
            (1 + ENNReal.ofReal (ZK' omega)) * ENNReal.ofReal (ZW' omega) ^ (2 : ℕ)) :=
          mul_le_mul' le_rfl (add_le_add hstep hstep')
      _ = 4 * ((1 + ENNReal.ofReal (ZK omega)) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ)) +
            4 * ((1 + ENNReal.ofReal (ZK' omega)) * ENNReal.ofReal (ZW' omega) ^ (2 : ℕ)) := by
          rw [mul_add]
  have hP1m : AEMeasurable (fun omega : Omega =>
      (1 + ENNReal.ofReal (ZK omega)) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ)) mu :=
    (aemeasurable_const.add hX).mul hY2
  have hmain : (∫⁻ omega : Omega, N omega ^ (2 : ℕ) ∂mu) ≤
      4 * (∫⁻ omega : Omega,
          (1 + ENNReal.ofReal (ZK omega)) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) +
        4 * (∫⁻ omega : Omega,
          (1 + ENNReal.ofReal (ZK' omega)) * ENNReal.ofReal (ZW' omega) ^ (2 : ℕ) ∂mu) := by
    refine (lintegral_mono hpoint).trans ?_
    rw [lintegral_add_left' (hP1m.const_mul 4) _]
    exact add_le_add (le_of_eq (lintegral_const_mul' 4 _ (by norm_num)))
      (le_of_eq (lintegral_const_mul' 4 _ (by norm_num)))
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    exact ⟨by norm_num, by norm_num⟩
  have hpow4 : ∀ (Z : Omega → ℝ), (∫⁻ omega : Omega,
        (fun o : Omega => ENNReal.ofReal (Z o) ^ (2 : ℕ)) omega ^ (2 : ℝ) ∂mu) =
      ∫⁻ omega : Omega, ENNReal.ofReal (Z omega) ^ (4 : ℕ) ∂mu := by
    intro Z
    refine lintegral_congr fun omega => ?_
    show (ENNReal.ofReal (Z omega) ^ (2 : ℕ)) ^ (2 : ℝ) = ENNReal.ofReal (Z omega) ^ (4 : ℕ)
    have h1 : (ENNReal.ofReal (Z omega) ^ (2 : ℕ)) ^ (2 : ℝ) =
        (ENNReal.ofReal (Z omega) ^ (2 : ℝ)) ^ (2 : ℝ) :=
      congrArg (fun t : ℝ≥0∞ => t ^ (2 : ℝ))
        (ENNReal.rpow_natCast (ENNReal.ofReal (Z omega)) 2).symm
    have h2 : (ENNReal.ofReal (Z omega) ^ (2 : ℝ)) ^ (2 : ℝ) =
        ENNReal.ofReal (Z omega) ^ (4 : ℕ) := by
      rw [← ENNReal.rpow_mul, show (2 : ℝ) * 2 = (4 : ℝ) by norm_num]
      exact ENNReal.rpow_natCast (ENNReal.ofReal (Z omega)) 4
    exact h1.trans h2
  have hpow2 : ∀ (Z : Omega → ℝ), (∫⁻ omega : Omega,
        (fun o : Omega => ENNReal.ofReal (Z o)) omega ^ (2 : ℝ) ∂mu) =
      ∫⁻ omega : Omega, ENNReal.ofReal (Z omega) ^ (2 : ℕ) ∂mu := by
    intro Z
    refine lintegral_congr fun omega => ?_
    show ENNReal.ofReal (Z omega) ^ (2 : ℝ) = ENNReal.ofReal (Z omega) ^ (2 : ℕ)
    exact ENNReal.rpow_natCast (ENNReal.ofReal (Z omega)) 2
  have hXY : (∫⁻ omega : Omega,
        ENNReal.ofReal (ZK omega) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) ≤
      (∫⁻ omega : Omega, ENNReal.ofReal (ZK omega) ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) *
        (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (4 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) := by
    refine (ENNReal.lintegral_mul_le_Lp_mul_Lq mu hconj hX hY2).trans (le_of_eq ?_)
    rw [hpow2 ZK, hpow4 ZW]
  have hXY' : (∫⁻ omega : Omega,
        ENNReal.ofReal (ZK' omega) * ENNReal.ofReal (ZW' omega) ^ (2 : ℕ) ∂mu) ≤
      (∫⁻ omega : Omega, ENNReal.ofReal (ZK' omega) ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) *
        (∫⁻ omega : Omega, ENNReal.ofReal (ZW' omega) ^ (4 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) := by
    refine (ENNReal.lintegral_mul_le_Lp_mul_Lq mu hconj hX' hY2').trans (le_of_eq ?_)
    rw [hpow2 ZK', hpow4 ZW']
  have hsplit : (∫⁻ omega : Omega, (1 + ENNReal.ofReal (ZK omega)) *
        ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) =
      (∫⁻ omega : Omega, ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) +
        ∫⁻ omega : Omega, ENNReal.ofReal (ZK omega) *
          ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu := by
    rw [← lintegral_add_left' hY2 (fun omega : Omega =>
      ENNReal.ofReal (ZK omega) * ENNReal.ofReal (ZW omega) ^ (2 : ℕ))]
    refine lintegral_congr fun omega => ?_
    rw [add_mul, one_mul]
  have hsplit' : (∫⁻ omega : Omega, (1 + ENNReal.ofReal (ZK' omega)) *
        ENNReal.ofReal (ZW' omega) ^ (2 : ℕ) ∂mu) =
      (∫⁻ omega : Omega, ENNReal.ofReal (ZW' omega) ^ (2 : ℕ) ∂mu) +
        ∫⁻ omega : Omega, ENNReal.ofReal (ZK' omega) *
          ENNReal.ofReal (ZW' omega) ^ (2 : ℕ) ∂mu := by
    rw [← lintegral_add_left' hY2' (fun omega : Omega =>
      ENNReal.ofReal (ZK' omega) * ENNReal.ofReal (ZW' omega) ^ (2 : ℕ))]
    refine lintegral_congr fun omega => ?_
    rw [add_mul, one_mul]
  have hZKmul : (∫⁻ omega : Omega, ENNReal.ofReal (ZK omega) *
      ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hZK2)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hZW4)) hXY
  have hZKmul' : (∫⁻ omega : Omega, ENNReal.ofReal (ZK' omega) *
      ENNReal.ofReal (ZW' omega) ^ (2 : ℕ) ∂mu) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hZK2')
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hZW4')) hXY'
  have hP1fin : (∫⁻ omega : Omega, (1 + ENNReal.ofReal (ZK omega)) *
      ENNReal.ofReal (ZW omega) ^ (2 : ℕ) ∂mu) ≠ ⊤ := by
    rw [hsplit]
    exact ENNReal.add_ne_top.2 ⟨hZW2, hZKmul⟩
  have hP2fin : (∫⁻ omega : Omega, (1 + ENNReal.ofReal (ZK' omega)) *
      ENNReal.ofReal (ZW' omega) ^ (2 : ℕ) ∂mu) ≠ ⊤ := by
    rw [hsplit']
    exact ENNReal.add_ne_top.2 ⟨hZW2', hZKmul'⟩
  refine ne_top_of_le_ne_top ?_ hmain
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (by norm_num) hP1fin, ENNReal.mul_ne_top (by norm_num) hP2fin⟩

/-- **The product rule at the canonical witness of `hFinDR`.**  The Frobenius
norm of `canonicalRJacobian d hd S hSorder p w hw omega` at `x` is at most
`‖k_{L'} − k_ℓ‖(x) · ‖∇²w‖(x) + √d · ‖∑_{k ∈ (ℓ,L']} ∇j_k (x)‖ · |∇w (x)|`,
`‖·‖` being the induced operator norm `ShellField.matrixDerivativeNorm`; it is
`RHSTerm2DispersionFinal.streamGradJacobian_norm_le` after unfolding
`canonicalRJacobian` and `rfieldWeakJacobian`.  The hypotheses are not vacuous:
any `omega`, any `x`, and the witness `RHSTerm2Analytic.rfieldHessianWitness`
satisfy them. -/
theorem canonicalRJacobian_norm_le_finDR (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (p : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega))
    (omega : ShellSeq d) (x : Vec d) :
    ‖HilbertMat.ofMat (fun i j =>
        canonicalRJacobian d hd S hSorder p w hw omega i x j)‖ ≤
      matrixOperatorNorm (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) *
          ‖HilbertMat.ofMat (fun j k =>
            (hasWeakHessianOnSymm (isOpen_openCubeSet (originCube d (S.m : ℤ)))
              (rfieldHessianWitness d hd S hSorder p w hw omega)).hess j k x)‖ +
        Real.sqrt d *
          ShellField.matrixDerivativeNorm
            (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x) *
          vecNorm ((w omega).toH1Function.grad x) := by
  simpa only [canonicalRJacobian, rfieldWeakJacobian] using
    streamGradJacobian_norm_le omega (ell_le_LPrime_of_scalesOrdering hSorder)
      (rfieldHessianWitness d hd S hSorder p w hw omega) x

/-! ## The `Γ_{1/2}` tail of the summed shell gradients

The density `∑_{k ∈ (ℓ,L']} ‖∇j_k‖` of the product rule carries the `Γ_{1/2}`
tail of the stream-increment moment display `e.kmn.bounds`, through the
per-shell concentration of `a.j.reg` and the `Γ₂` triangle over the shells
(`RHSTerm2KmnBounds.annealed_L4_increment_gradient_le`, re-run here for the
finiteness half). -/

/-- **The `Γ_{1/2}` tail of the summed one-shell gradient norms.**  The normed
cube average of the fourth power of `∑_{k ∈ (n,m]} ‖∇j_k‖` satisfies
`O_{Γ_{1/2}}` at the amplitude `e · γ_{1/2} · (γ₂ · 3^{-n})⁴`. -/
theorem gradientSum_volumeAverage_isBigOWith (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {n m : ℕ} (hnm : n < m)
    (Q : TriadicCube d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (fun omega : ShellSeq d => volumeAverage (cubeSet Q)
        (fun x : Vec d => (∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ)))
      (Real.exp 1 * (IndependentSums.gammaMomentConst ((1 : ℝ) / 2) *
        (IndependentSums.gammaTriangleConst 2 * ((3 : ℝ) ^ n)⁻¹) ^ (4 : ℝ))) := by
  set A : ℝ := ((3 : ℝ) ^ n)⁻¹ with hAdef
  have hApos : (0 : ℝ) < A := by
    rw [hAdef]
    exact inv_pos.mpr (pow_pos (by norm_num) n)
  have hsumnn : ∀ (omega : ShellSeq d) (x : Vec d),
      0 ≤ ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x) :=
    fun omega x => Finset.sum_nonneg fun k _ =>
      ShellField.matrixDerivativeNorm_nonneg _
  -- every point carries the one-shell `Γ₂` tail at the centre `x` itself
  have hterm : ∀ (k : ℕ) (x : Vec d),
      IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
        (((3 : ℝ) ^ k)⁻¹) := by
    intro k x
    have hx : x - x ∈ cubeSet (originCube d ((k : ℕ) : ℤ)) := by
      rw [sub_self]
      exact openCubeSet_subset_cubeSet _ (zero_mem_openCubeSet_originCube k)
    exact (isBigOWith_gammaSigma_translatedShellDerivSupBound hPrefix hJ3 k x).of_le
      (fun omega ↦ matrixDerivativeNorm_deriv_le_translatedShellDerivSupBound
        omega k x hx)
  -- the `Γ₂` triangle over the shells, at the geometric tail scale
  have hsum : ∀ x : Vec d,
      IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
        (IndependentSums.gammaTriangleConst 2 * A) := by
    intro x
    have hbigO : ∀ k ∈ Finset.Ioc n m,
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
          (fun omega : ShellSeq d ↦
            ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
          (((3 : ℝ) ^ k)⁻¹) :=
      fun k _ ↦ (isBigOWith_iff_isBigO_of_nonneg
        (fun omega ↦ ShellField.matrixDerivativeNorm_nonneg _)).mp (hterm k x)
    have htriangle := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := P.toMeasure)
      (s := Finset.Ioc n m)
      (X := fun (k : ℕ) (omega : ShellSeq d) ↦
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
      (a := fun k : ℕ ↦ ((3 : ℝ) ^ k)⁻¹) (σ := 2) (hσ := by norm_num)
      (hs := Finset.nonempty_Ioc.mpr hnm)
      (ha := fun k _ ↦ inv_pos.mpr (pow_pos (by norm_num) k)) (hX := hbigO)
      (hXm := fun k _ ↦ measurable_matrixDerivativeNorm_shellDeriv_coordinate k x)
    have hwith : IndependentSums.IsBigOWith P.toMeasure
        (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d ↦ ∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
        (IndependentSums.gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc n m,
          ((3 : ℝ) ^ k)⁻¹) :=
      (isBigOWith_iff_isBigO_of_nonneg (fun omega ↦ hsumnn omega x)).mpr htriangle
    refine hwith.mono_scale (mul_le_mul_of_nonneg_left
      (sum_Ioc_inv_pow_three_le hnm.le)
      IndependentSums.gammaTriangleConst_pos.le)
  -- the power rule: the fourth power moves the index to `Γ_{1/2}`
  have hpow : ∀ x : Vec d,
      IndependentSums.IsBigOWith P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 2))
        (fun omega : ShellSeq d ↦
          (∑ k ∈ Finset.Ioc n m,
            ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^
            (4 : ℝ))
        ((IndependentSums.gammaTriangleConst 2 * A) ^ (4 : ℝ)) := by
    intro x
    have h := isBigOWith_gammaSigma_rpow_fwd
      (mu := P.toMeasure)
      (X := fun omega : ShellSeq d ↦ ∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
      (K := IndependentSums.gammaTriangleConst 2 * A) (σ := 2) (p := (4 : ℝ))
      (hp := by norm_num)
      (hK := (mul_pos IndependentSums.gammaTriangleConst_pos hApos).le)
      (hX := fun omega ↦ hsumnn omega x) (hXK := hsum x)
    rwa [show ((2 : ℝ) / 4) = ((1 : ℝ) / 2) from by norm_num] at h
  -- the averaging step over the cube
  have hU0 : volume (cubeSet Q) ≠ 0 := by
    have hvolpos : (0 : ℝ) < (volume (cubeSet Q)).toReal := by
      rw [volume_cubeSet_toReal]
      exact cubeVolume_pos Q
    intro h
    rw [h] at hvolpos
    simp at hvolpos
  have hUtop : volume (cubeSet Q) ≠ ⊤ :=
    ne_of_lt (volume_cubeSet_lt_top Q)
  exact isBigOWith_gammaSigma_volumeAverage
    (mu := P.toMeasure) (U := cubeSet Q)
    (Y := fun (x : Vec d) (omega : ShellSeq d) ↦
      (∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^
        (4 : ℝ))
    (sigma := ((1 : ℝ) / 2))
    (A := (IndependentSums.gammaTriangleConst 2 * A) ^ (4 : ℝ))
    (by norm_num)
    (Real.rpow_pos_of_pos
      (mul_pos IndependentSums.gammaTriangleConst_pos hApos) 4)
    hU0 hUtop (fun x omega ↦ Real.rpow_nonneg (hsumnn omega x) 4)
    (measurable_uncurry_rpow_matrixDerivativeNorm_sum_shellDeriv n m) hpow

/-- **Finiteness of the annealed second moment of the summed gradient tail.**
The witness of `gradientSum_volumeAverage_isBigOWith` has a finite annealed
square. -/
theorem gradientSum_volumeAverage_two_ne_top (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {n m : ℕ} (hnm : n < m)
    (Q : TriadicCube d) :
    (∫⁻ omega : ShellSeq d, ENNReal.ofReal (volumeAverage (cubeSet Q)
        (fun x : Vec d => (∑ k ∈ Finset.Ioc n m,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^
            (4 : ℝ))) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ := by
  have hmeas : AEMeasurable (fun omega : ShellSeq d => volumeAverage (cubeSet Q)
      (fun x : Vec d => (∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^
          (4 : ℝ))) P.toMeasure :=
    (measurable_volumeAverage_of_measurable_uncurry
      (fun (x : Vec d) (omega : ShellSeq d) => (∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ))
      (measurable_uncurry_rpow_matrixDerivativeNorm_sum_shellDeriv n m)
      (cubeSet Q)).aemeasurable
  have hnn : ∀ omega : ShellSeq d, 0 ≤ volumeAverage (cubeSet Q)
      (fun x : Vec d => (∑ k ∈ Finset.Ioc n m,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ)) :=
    fun omega => SuperdiffusionCLT.Section2.Norms.volumeAverage_cubeSet_nonneg Q
      (fun x => Real.rpow_nonneg (Finset.sum_nonneg fun k _ =>
        ShellField.matrixDerivativeNorm_nonneg _) 4)
  exact annealed_ofReal_pow_ne_top_of_gammaSigma (mu := P.toMeasure)
    (sigma := ((1 : ℝ) / 2)) (by norm_num) hnn hmeas _
    (gradientSum_volumeAverage_isBigOWith P hPrefix hJ3 hnm Q) (by norm_num : 1 ≤ 2)

/-- Scaling a tail witness by a constant `c ≥ 0` preserves the finiteness of its
annealed `n`-th moment. -/
private theorem lintegral_ofReal_const_mul_pow_ne_top {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {Z : Omega → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ)
    (h : (∫⁻ omega : Omega, ENNReal.ofReal (Z omega) ^ n ∂mu) ≠ ⊤) :
    (∫⁻ omega : Omega, ENNReal.ofReal (c * Z omega) ^ n ∂mu) ≠ ⊤ := by
  have hone : ENNReal.ofReal c ^ n ≠ ⊤ := by
    rw [← ENNReal.ofReal_pow hc]
    exact ENNReal.ofReal_ne_top
  have hcongr : (fun omega : Omega => ENNReal.ofReal (c * Z omega) ^ n) =
      fun omega : Omega => ENNReal.ofReal c ^ n * ENNReal.ofReal (Z omega) ^ n := by
    funext omega
    rw [ENNReal.ofReal_mul hc, mul_pow]
  rw [hcongr, lintegral_const_mul' (ENNReal.ofReal c ^ n)
    (fun omega : Omega => ENNReal.ofReal (Z omega) ^ n) hone]
  exact ENNReal.mul_ne_top hone h

/-- **`hFinDR` with no carried hypothesis.**  The weak Jacobian `DR` of
`R = (k_{L'} − k_ℓ) ∇w` at the witness `canonicalRJacobian` has a finite
annealed squared `L̲²(cu_m)` norm, with **no** hypothesis beyond the standing
shell laws, the dimension hypotheses, the scale ordering `ScalesOrdering S`, and
the response `w` with `IsDirichletResponse`.  The four densities of
`canonicalRJacobian_norm_le_finDR` are `A = ‖k_{L'} − k_ℓ‖_{L̲⁴}`, `B = ‖∇²w‖_{L̲⁴}`
(at the `Γ₂` witness `Zh` of the anchor's second clause), `A' = ‖√d ∑ ∇j_k‖_{L̲⁴}`
(at `d² · ZG`, `ZG` from `gradientSum_volumeAverage_isBigOWith`) and
`B' = |∇w|_{L̲⁴}` (at the anchor's first witness `Zw`); the cube step is Hölder
`(4,4) → 2` and the sample step Cauchy–Schwarz `(2,2)` at the measurable
witnesses, both pointwise per sample, so the clause `hMeasDR` is not consumed. -/
theorem term2_hFinDR_integrability (d : ℕ) [NeZero d] (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d) (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    (∫⁻ omega : ShellSeq d,
        cubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => HilbertMat.ofMat (fun i j =>
            canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
              w hw omega i x j)) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ := by
  -- the standing scale fact
  have hnm : S.ell < S.LPrime := by
    have h1 := hSorder.ell_lt_ellPrime
    have h2 := hSorder.ellPrime_lt_m
    have h3 : S.LPrime = S.m + 2 * S.a := S.LPrime_eq
    omega
  have helle : S.ell ≤ S.LPrime := hnm.le
  -- the two clauses of the anchor
  obtain ⟨Cwb, _hCwb, hClauses⟩ :=
    SuperdiffusionCLT.Frozen.Section3.w_basic_regbounds d hd
  obtain ⟨hGradClause, hHessClause, -⟩ := hClauses nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4
    S hSorder e he (testVector nu S.LPrime P S.n e) rfl w hw
  obtain ⟨Zw, hZwm, hZwO, hZwdom⟩ := hGradClause
  -- the symmetrized canonical Hessian witness the product rule carries
  set HD : (∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ))) (w omega).toH1Function) :=
    fun omega => hasWeakHessianOnSymm (isOpen_openCubeSet (originCube d (S.m : ℤ)))
      (rfieldHessianWitness d hd S hSorder (testVector nu S.LPrime P S.n e) w hw omega)
    with hHD
  obtain ⟨Zh, hZhm, hZhO, hZhdom0⟩ := hHessClause HD
  have hZhdom : ∀ omega : ShellSeq d, cubeLpENorm (originCube d (S.m : ℤ)) 8
      (fun x => HilbertMat.ofMat (fun j k => (HD omega).hess j k x)) ≤
      ENNReal.ofReal (Zh omega) := fun omega => hZhdom0 omega
  -- the four densities of the product rule
  let A : ShellSeq d → ℝ≥0∞ := fun omega => cubeLpENorm (originCube d (S.m : ℤ)) 4
    (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x))
  let B : ShellSeq d → ℝ≥0∞ := fun omega => cubeLpENorm (originCube d (S.m : ℤ)) 4
    (fun x : Vec d => ‖HilbertMat.ofMat (fun j k => (HD omega).hess j k x)‖)
  let A' : ShellSeq d → ℝ≥0∞ := fun omega => cubeLpENorm (originCube d (S.m : ℤ)) 4
    (fun x : Vec d => Real.sqrt d * ShellField.matrixDerivativeNorm
      (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x))
  let B' : ShellSeq d → ℝ≥0∞ := fun omega => cubeLpENorm (originCube d (S.m : ℤ)) 4
    (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x))
  let N : ShellSeq d → ℝ≥0∞ := fun omega => cubeLpENorm (originCube d (S.m : ℤ)) 2
    (fun x => HilbertMat.ofMat (fun i j =>
      canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e) w hw omega i x j))
  -- the witnesses of the sample pairing
  let ZK : ShellSeq d → ℝ := fun omega => volumeAverage (cubeSet (originCube d (S.m : ℤ)))
    (fun x : Vec d =>
      matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) ^ (4 : ℝ))
  let ZG : ShellSeq d → ℝ := fun omega => volumeAverage (cubeSet (originCube d (S.m : ℤ)))
    (fun x : Vec d => (∑ k ∈ Finset.Ioc S.ell S.LPrime,
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ))
  have hAe : ∀ omega : ShellSeq d, A omega = cubeLpENorm (originCube d (S.m : ℤ)) 4
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x)) :=
    fun _ => rfl
  have hBe : ∀ omega : ShellSeq d, B omega = cubeLpENorm (originCube d (S.m : ℤ)) 4
      (fun x : Vec d => ‖HilbertMat.ofMat (fun j k => (HD omega).hess j k x)‖) :=
    fun _ => rfl
  have hA'e : ∀ omega : ShellSeq d, A' omega = cubeLpENorm (originCube d (S.m : ℤ)) 4
      (fun x : Vec d => Real.sqrt d * ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x)) :=
    fun _ => rfl
  have hB'e : ∀ omega : ShellSeq d, B' omega = cubeLpENorm (originCube d (S.m : ℤ)) 4
      (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x)) :=
    fun _ => rfl
  have hNe : ∀ omega : ShellSeq d, N omega = cubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun x => HilbertMat.ofMat (fun i j =>
        canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e) w hw omega i x j)) :=
    fun _ => rfl
  have hZKe : ∀ omega : ShellSeq d, ZK omega = volumeAverage (cubeSet (originCube d (S.m : ℤ)))
      (fun x : Vec d =>
        matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) ^ (4 : ℝ)) :=
    fun _ => rfl
  have hZGe : ∀ omega : ShellSeq d, ZG omega = volumeAverage (cubeSet (originCube d (S.m : ℤ)))
      (fun x : Vec d => (∑ k ∈ Finset.Ioc S.ell S.LPrime,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ)) :=
    fun _ => rfl
  have hZKfun : ZK = fun omega : ShellSeq d =>
      volumeAverage (cubeSet (originCube d (S.m : ℤ)))
        (fun x : Vec d =>
          matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) ^ (4 : ℝ)) :=
    funext hZKe
  have hZGfun : ZG = fun omega : ShellSeq d =>
      volumeAverage (cubeSet (originCube d (S.m : ℤ)))
        (fun x : Vec d => (∑ k ∈ Finset.Ioc S.ell S.LPrime,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ)) :=
    funext hZGe
  -- nonnegativity of the four densities
  have hKN0 : ∀ (omega : ShellSeq d) (x : Vec d), 0 ≤
      matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) :=
    fun _ _ => matrixOperatorNorm_nonneg _
  have hHH0 : ∀ (omega : ShellSeq d) (x : Vec d), 0 ≤
      ‖HilbertMat.ofMat (fun j k => (HD omega).hess j k x)‖ := fun _ _ => norm_nonneg _
  have hGN0 : ∀ (omega : ShellSeq d) (x : Vec d), 0 ≤ Real.sqrt d *
      ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x) :=
    fun _ _ => mul_nonneg (Real.sqrt_nonneg d) (ShellField.matrixDerivativeNorm_nonneg _)
  have hWG0 : ∀ (omega : ShellSeq d) (x : Vec d), 0 ≤
      vecNorm ((w omega).toH1Function.grad x) := fun _ _ => vecNorm_nonneg _
  -- cube measurability of the four densities
  have hKNm : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) :=
    fun omega => (continuous_matrixOperatorNorm_finiteShellIncrement omega S.ell S.LPrime)
      |>.aestronglyMeasurable
  have hGNcont : ∀ omega : ShellSeq d, Continuous (fun x : Vec d =>
      ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x)) :=
    fun omega => ShellField.matrixDerivativeNorm_continuous.comp
      (continuous_finsetSum _ fun k _ => (ShellField.deriv (omega k)).continuous)
  have hGNm : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (fun x : Vec d => Real.sqrt d * ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) :=
    fun omega => (continuous_const.mul (hGNcont omega)).aestronglyMeasurable
  have hWGh : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (hilbertifyVecField ((w omega).toH1Function.grad))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (memHilbertVectorL2_hilbertifyVecField
      ((w omega).toH1Function.grad_memVectorL2)).aestronglyMeasurable.smul_measure _
  have hWGm : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (fun x : Vec d => vecNorm ((w omega).toH1Function.grad x))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    refine (hWGh omega).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    exact norm_hilbertifyVecField_apply _ x
  have hHHg : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (fun x : Vec d => HilbertMat.ofMat (fun j k => (HD omega).hess j k x))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := by
    intro omega
    have hEnt : ∀ i j : Fin d, MemLp (fun x : Vec d => (HD omega).hess i j x) 2
        (volume.restrict (openCubeSet (originCube d (S.m : ℤ)))) :=
      fun i j => (HD omega).hess_memL2 i j
    have hH : MemLp (fun x : Vec d =>
        HilbertMat.ofMat (fun i j => (HD omega).hess i j x)) 2
        (volume.restrict (openCubeSet (originCube d (S.m : ℤ)))) :=
      memLp_hilbertMat_ofMat (U := openCubeSet (originCube d (S.m : ℤ))) hEnt
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact hH.aestronglyMeasurable.smul_measure _
  have hHHm : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (fun x : Vec d => ‖HilbertMat.ofMat (fun j k => (HD omega).hess j k x)‖)
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) :=
    fun omega => (hHHg omega).norm
  -- the four dominions by the tail witnesses
  have hA4 : ∀ omega : ShellSeq d, A omega ^ (4 : ℕ) ≤ ENNReal.ofReal (ZK omega) := by
    intro omega
    rw [hAe omega, hZKe omega]
    exact cubeLpENorm_four_le_ofReal_volumeAverage (originCube d (S.m : ℤ))
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x))
      (fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x))
      (fun x => matrixOperatorNorm_nonneg _) (hKNm omega) (fun x => le_rfl)
      (fun x => matrixOperatorNorm_nonneg _)
      (continuous_matrixOperatorNorm_finiteShellIncrement omega S.ell S.LPrime)
  have hBle : ∀ omega : ShellSeq d, B omega ≤ ENNReal.ofReal (Zh omega) := by
    intro omega
    rw [hBe omega]
    refine (cubeLpENorm_mono_exponent (originCube d (S.m : ℤ))
      (show (4 : ℝ≥0∞) ≤ 8 by norm_num) (hHHm omega)).trans ?_
    rw [cubeLpENorm_norm_field_eq_finDR _ _ _ (hHHg omega)]
    exact hZhdom omega
  have hA4' : ∀ omega : ShellSeq d, A' omega ^ (4 : ℕ) ≤
      ENNReal.ofReal (((d : ℝ) ^ 2) * ZG omega) := by
    intro omega
    rw [hA'e omega]
    have hsm : (fun x : Vec d => Real.sqrt d * ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x)) =
      (Real.sqrt d) • (fun x : Vec d => ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x)) := rfl
    rw [hsm, cubeLpENorm_const_smul]
    have hsq : ‖(Real.sqrt d : ℝ)‖ₑ = ENNReal.ofReal (Real.sqrt d) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg d)]
    rw [hsq, mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg d)]
    have hsq4 : (Real.sqrt d) ^ (4 : ℕ) = (d : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul (Real.sqrt d) 2 2,
        Real.sq_sqrt (Nat.cast_nonneg d)]
    rw [hsq4]
    refine (mul_le_mul' le_rfl
      (cubeLpENorm_four_le_ofReal_volumeAverage (originCube d (S.m : ℤ))
        (fun x : Vec d => ShellField.matrixDerivativeNorm
          (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x))
        (fun x : Vec d => ∑ k ∈ Finset.Ioc S.ell S.LPrime,
          ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x))
        (fun x => ShellField.matrixDerivativeNorm_nonneg _)
        (hGNcont omega).aestronglyMeasurable
        (fun x => SuperdiffusionCLT.Section2.Estimates.Stream.matrixDerivativeNorm_finset_sum_le
          (Finset.Ioc S.ell S.LPrime) (fun k => ShellField.deriv (omega k) x))
        (fun x => Finset.sum_nonneg fun k _ => ShellField.matrixDerivativeNorm_nonneg _)
        (continuous_matrixDerivativeNorm_sum_shellDeriv omega S.ell S.LPrime))).trans
      (le_of_eq (ENNReal.ofReal_mul (by positivity)).symm)
  have hBle' : ∀ omega : ShellSeq d, B' omega ≤ ENNReal.ofReal (Zw omega) := by
    intro omega
    rw [hB'e omega]
    refine (cubeLpENorm_mono_exponent (originCube d (S.m : ℤ))
      (show (4 : ℝ≥0∞) ≤ 8 by norm_num) (hWGm omega)).trans ?_
    rw [cubeLpENorm_vecNorm_eq_vecCubeLpENorm _ _ _ (hWGh omega)]
    exact hZwdom omega
  -- the finitenesses of the four tail witnesses
  have hZKm : AEMeasurable ZK P.toMeasure := by
    rw [hZKfun]
    exact aemeasurable_volumeAverage_rpow_matrixOperatorNorm_finiteShellIncrement P
      S.ell S.LPrime (by norm_num) (originCube d (S.m : ℤ))
  have hZKnn : ∀ omega : ShellSeq d, 0 ≤ ZK omega := by
    intro omega
    rw [hZKe omega]
    exact SuperdiffusionCLT.Section2.Norms.volumeAverage_cubeSet_nonneg _
      (fun x : Vec d => Real.rpow_nonneg (matrixOperatorNorm_nonneg _) 4)
  have hprov := isBigOWith_gammaSigma_finiteShellIncrementPthMoment (P := P) hPrefix hJ2 hJ3
    hJ4 (p := (4 : ℝ)) (by norm_num) hnm (originCube d (S.m : ℤ))
  rw [show ((2 : ℝ) / 4) = ((1 : ℝ) / 2) from by norm_num] at hprov
  have hZK2 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (ZK omega) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    annealed_ofReal_pow_ne_top_of_gammaSigma (mu := P.toMeasure)
      (sigma := ((1 : ℝ) / 2)) (by norm_num) hZKnn hZKm _
      (by simpa only using hprov) (by norm_num : 1 ≤ 2)
  have hZGmeas : Measurable ZG := by
    rw [hZGfun]
    exact measurable_volumeAverage_of_measurable_uncurry
      (fun (x : Vec d) (omega : ShellSeq d) => (∑ k ∈ Finset.Ioc S.ell S.LPrime,
        ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)) ^ (4 : ℝ))
      (measurable_uncurry_rpow_matrixDerivativeNorm_sum_shellDeriv S.ell S.LPrime)
      (cubeSet (originCube d (S.m : ℤ)))
  have hZG2 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (ZG omega) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    gradientSum_volumeAverage_two_ne_top P hPrefix hJ3 hnm (originCube d (S.m : ℤ))
  have hZK'm : AEMeasurable (fun omega : ShellSeq d => ((d : ℝ) ^ 2) * ZG omega)
      P.toMeasure := (hZGmeas.const_mul _).aemeasurable
  have hZK2' : (∫⁻ omega : ShellSeq d,
      ENNReal.ofReal (((d : ℝ) ^ 2) * ZG omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ :=
    lintegral_ofReal_const_mul_pow_ne_top (Z := ZG) (c := (d : ℝ) ^ 2)
      (by positivity) 2 hZG2
  have hZwnn : ∀ omega : ShellSeq d, 0 ≤ |Zw omega| := fun _ => abs_nonneg _
  have hZwabsm : AEMeasurable (fun omega : ShellSeq d => |Zw omega|) P.toMeasure :=
    Measurable.comp_aemeasurable continuous_abs.measurable hZwm.aemeasurable
  have hZw2 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (|Zw omega|) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    annealed_ofReal_pow_ne_top_of_gammaSigma (mu := P.toMeasure) (sigma := 2)
      (by norm_num) hZwnn hZwabsm _ hZwO (by norm_num : 1 ≤ 2)
  have hZw4 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (|Zw omega|) ^ (4 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    annealed_ofReal_pow_ne_top_of_gammaSigma (mu := P.toMeasure) (sigma := 2)
      (by norm_num) hZwnn hZwabsm _ hZwO (by norm_num : 1 ≤ 4)
  have hZW2 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zw omega) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top hZw2 (lintegral_mono fun omega =>
      pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_abs_self _)) 2)
  have hZW4 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zw omega) ^ (4 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top hZw4 (lintegral_mono fun omega =>
      pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_abs_self _)) 4)
  have hZhnn : ∀ omega : ShellSeq d, 0 ≤ |Zh omega| := fun _ => abs_nonneg _
  have hZhabsm : AEMeasurable (fun omega : ShellSeq d => |Zh omega|) P.toMeasure :=
    Measurable.comp_aemeasurable continuous_abs.measurable hZhm.aemeasurable
  have hZh2 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (|Zh omega|) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    annealed_ofReal_pow_ne_top_of_gammaSigma (mu := P.toMeasure) (sigma := 2)
      (by norm_num) hZhnn hZhabsm _ hZhO (by norm_num : 1 ≤ 2)
  have hZh4 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (|Zh omega|) ^ (4 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    annealed_ofReal_pow_ne_top_of_gammaSigma (mu := P.toMeasure) (sigma := 2)
      (by norm_num) hZhnn hZhabsm _ hZhO (by norm_num : 1 ≤ 4)
  have hZH2 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zh omega) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top hZh2 (lintegral_mono fun omega =>
      pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_abs_self _)) 2)
  have hZH4 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (Zh omega) ^ (4 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top hZh4 (lintegral_mono fun omega =>
      pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_abs_self _)) 4)
  -- the cube Hölder step of the product rule
  have hN : ∀ omega : ShellSeq d, N omega ≤ A omega * B omega + A' omega * B' omega := by
    intro omega
    have hfx : ∀ x : Vec d,
        ‖HilbertMat.ofMat (fun i j =>
          canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
            w hw omega i x j)‖ ≤
        matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x) *
            ‖HilbertMat.ofMat (fun j k => (HD omega).hess j k x)‖ +
          (Real.sqrt d * ShellField.matrixDerivativeNorm
              (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x)) *
            vecNorm ((w omega).toH1Function.grad x) := by
      intro x
      have hpt := canonicalRJacobian_norm_le_finDR d hd S hSorder
        (testVector nu S.LPrime P S.n e) w hw omega x
      rw [← finiteShellIncrement_apply_eq_streamCutoff_sub omega helle x] at hpt
      simpa only [hHD] using hpt
    rw [hNe omega, hAe omega, hBe omega, hA'e omega, hB'e omega]
    exact cubeLpENorm_two_le_mul_four_add (Q := originCube d (S.m : ℤ))
      (f := fun x : Vec d => HilbertMat.ofMat (fun i j =>
        canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
          w hw omega i x j))
      (u := fun x : Vec d => matrixOperatorNorm (finiteShellIncrement omega S.ell S.LPrime x))
      (v := fun x : Vec d => ‖HilbertMat.ofMat (fun j k => (HD omega).hess j k x)‖)
      (u' := fun x : Vec d => Real.sqrt d * ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc S.ell S.LPrime, ShellField.deriv (omega k) x))
      (v' := fun x : Vec d => vecNorm ((w omega).toH1Function.grad x))
      (hKN0 omega) (hHH0 omega) (hGN0 omega) (hWG0 omega)
      (hKNm omega) (hHHm omega) (hGNm omega) (hWGm omega)
      (by
        rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
        exact ((canonicalRJacobian_hasWeakGradientOn d hd nu S hSorder
          (testVector nu S.LPrime P S.n e) w hw).2 omega).aestronglyMeasurable.smul_measure _)
      hfx
  exact lintegral_sq_ne_top_of_two_tails (mu := P.toMeasure) (N := N) (A := A) (B := B)
    (A' := A') (B' := B') (ZK := ZK) (ZW := Zh)
    (ZK' := fun omega : ShellSeq d => ((d : ℝ) ^ 2) * ZG omega) (ZW' := Zw)
    hZKm hZhm.aemeasurable hZK'm hZwm.aemeasurable hN hA4 hBle hA4' hBle'
    hZK2 hZH2 hZH4 hZK2' hZW2 hZW4

end

end SuperdiffusionCLT.Section3.Terms
