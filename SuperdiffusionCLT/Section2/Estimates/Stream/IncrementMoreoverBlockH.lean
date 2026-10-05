/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.CubeCarrierIdents
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockF

/-!
# The pointwise ellipticity clause of the "Moreover" block

The statement `e.a.ellipticity.pointwise` and its proof sketch: for every `x`,

`|k(x) - k(0)|² ≤ C (log (K_σ² + |x|²))^{2(1+σ)}`.

## The route

The print telescopes through the nested cubes between `K_σ` and `3^r` with
`3^r ≍ K_σ + |x|`. Only two ingredients are needed, and both are elementary
once the scale is chosen:

* **The centring is irrelevant to a difference.** `centeredStreamField` is the
  series `∑_k (j_k - (j_k)_U)`, so on the summability guard
  `centeredStreamField ω U x - centeredStreamField ω U y = ∑_k (j_k(x) - j_k(y))`,
  which does not mention `U` (`centeredStreamField_sub_centring`). In
  particular the difference at the centring cube `cu_0` equals the same
  difference at any cube `cu_m`.
* **The `L∞` term of `e.Xm.deff` is a genuine pointwise bound.** The
  clause bounds an essential supremum; since the field is continuous on the
  guard (`continuous_centeredStreamField`) and the normalized cube measure has
  the same null sets as Lebesgue measure restricted to the cube, the bound
  holds at every point of the open cube
  (`norm_le_of_cubeLpENorm_top_le`).

With `m := ⌈log R / log 3⌉ + 1` and `R := K_σ + |x|` one has `K_σ ≤ 3^m` and
`3^m ≥ 3 R`, so `x` and `0` both lie in the open cube `cu_m`, and

`|k(x) - k(0)| ≤ 2 ‖k - (k)_{cu_m}‖_{L∞(cu_m)} ≤ 2 m δ m^σ = 2 δ m^{1+σ}`.

Since `K_σ ≥ 27` one has `m ≤ (5/3) log R / log 3 ≤ (5/3) log R`, and
`2 log R ≤ log 2 + log(K_σ² + |x|²) ≤ (7/6) log(K_σ² + |x|²)` because
`K_σ² + |x|² ≥ 729`. Hence `m ≤ (35/36) L ≤ L` with
`L := log (K_σ² + |x|²)`, and with `δ ≤ 1` the squared bound is
`4 L^{2(1+σ)}`. **The constant is the absolute constant `4`.**

## What this theorem consumes

Only the **first** term of the `e.Xm.deff` display,
in the form

`ofReal (m⁻¹) * cubeLpENorm cu_m ∞ (k - (k)_{cu_m}) ≤ ofReal (δ m^σ)`

for every `m` with `K ≤ 3^m`, which is implied by the three-term clause
because all three summands are nonnegative in `ℝ≥0∞`. It does **not** consume
the second or third term, and in particular it is independent of the
un-normalized hatted negative norm.

## Main results

* `summable_centeredShellTerm_originCube`: the defining series converges at
  every point of the ambient space on the guard.
* `centeredStreamField_sub_eq_tsum`, `centeredStreamField_sub_centring`: the
  centring-independence of `k(x) - k(y)`.
* `norm_le_of_cubeLpENorm_top_le`: an `L∞` bound on a cube is a pointwise bound
  on the open cube for a continuous field.
* `matrixOperatorNorm_centeredStreamField_le_of_minimalScale`: the pointwise
  form of the first term of the block.
* `sq_matrixOperatorNorm_centeredStreamField_sub_le`: the clause
  `e.a.ellipticity.pointwise`, with the constant `4`.

## References

* `e.a.ellipticity.pointwise`, `e.Xm.deff`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The centring-independence of a difference -/

section Elementwise

open scoped Matrix.Norms.Elementwise

/-- **The defining series converges at every point of the ambient space.** The
centring cube is `cu_m`, but the point may be anywhere: it lies in some larger
open cube `cu_i`, on which `norm_centeredShellTerm_le_openCubeSet` supplies the
Weierstrass majorant. -/
theorem summable_centeredShellTerm_originCube (omega : ShellSeq d)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    (m : ℕ) (x : Vec d) :
    Summable fun k : ℕ =>
      centeredShellTerm omega (cubeSet (originCube d (m : ℤ))) k x := by
  obtain ⟨i, hmi, hxi⟩ := exists_lt_mem_openCubeSet_originCube (d := d) m x
  refine Summable.of_norm_bounded
    (g := fun k : ℕ => Real.sqrt d * (3 : ℝ) ^ i *
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    ((hguard i).mul_left _) fun k => ?_
  exact norm_centeredShellTerm_le_openCubeSet hmi omega k hxi

/-- **A difference of values of the centered field is the series of the
differences of the shells**: the centring constants cancel. -/
theorem centeredStreamField_sub_eq_tsum (omega : ShellSeq d)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    (m : ℕ) (x y : Vec d) :
    centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x -
        centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y =
      ∑' k : ℕ, (shellReg omega k x - shellReg omega k y) := by
  have hx := summable_centeredShellTerm_originCube omega hguard m x
  have hy := summable_centeredShellTerm_originCube omega hguard m y
  rw [centeredStreamField_eq_tsum, centeredStreamField_eq_tsum,
    ← Summable.tsum_sub hx hy]
  refine tsum_congr fun k => ?_
  simp only [centeredShellTerm]
  abel

/-- **The centring-independence of `k(x) - k(y)`.** This is what makes the
clause at the centring cube `cu_0` accessible from the estimates at the
cube `cu_m`. -/
theorem centeredStreamField_sub_centring (omega : ShellSeq d)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    (m n : ℕ) (x y : Vec d) :
    centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x -
        centeredStreamField omega (cubeSet (originCube d (m : ℤ))) y =
      centeredStreamField omega (cubeSet (originCube d (n : ℤ))) x -
        centeredStreamField omega (cubeSet (originCube d (n : ℤ))) y := by
  rw [centeredStreamField_sub_eq_tsum omega hguard m x y,
    centeredStreamField_sub_eq_tsum omega hguard n x y]

end Elementwise

/-! ## From the essential supremum to the pointwise value -/

/-- **An `L∞` bound on a cube is a pointwise bound on the open cube** for a
continuous field: the normalized cube measure is a positive multiple of
Lebesgue measure restricted to the cube, and a nonempty open subset of the cube
has positive Lebesgue measure. -/
theorem norm_le_of_cubeLpENorm_top_le {E : Type*} [NormedAddCommGroup E]
    {Q : TriadicCube d} {f : Vec d → E} (hf : Continuous f) {r : ℝ}
    (hr : 0 ≤ r) (hbound : cubeLpENorm Q ∞ f ≤ ENNReal.ofReal r)
    {x : Vec d} (hx : x ∈ openCubeSet Q) : ‖f x‖ ≤ r := by
  by_contra hcon
  rw [not_le] at hcon
  set V : Set (Vec d) := openCubeSet Q ∩ (fun y : Vec d => ‖f y‖) ⁻¹' Set.Ioi r
    with hV
  have hVopen : IsOpen V :=
    (isOpen_openCubeSet Q).inter (isOpen_Ioi.preimage hf.norm)
  have hxV : x ∈ V := ⟨hx, hcon⟩
  have hVpos : 0 < volume V := hVopen.measure_pos volume ⟨x, hxV⟩
  have hVsub : V ⊆ cubeSet Q := fun y hy => openCubeSet_subset_cubeSet Q hy.1
  have hrestrict : 0 < (volume.restrict (cubeSet Q)) V := by
    rw [Measure.restrict_apply hVopen.measurableSet,
      Set.inter_eq_left.mpr hVsub]
    exact hVpos
  have hnorm : ∀ᵐ y ∂(normalizedCubeMeasure Q), ‖f y‖ₑ ≤ ENNReal.ofReal r := by
    have h1 : ∀ᵐ y ∂(normalizedCubeMeasure Q),
        ‖f y‖ₑ ≤ eLpNormEssSup f (normalizedCubeMeasure Q) :=
      enorm_ae_le_eLpNormEssSup f _
    filter_upwards [h1] with y hy
    refine le_trans hy ?_
    have hb2 := hbound
    unfold cubeLpENorm at hb2
    rw [eLpNorm_exponent_top hf.aestronglyMeasurable] at hb2
    exact hb2
  have hae : ∀ᵐ y ∂(volume.restrict (cubeSet Q)),
      ‖f y‖ₑ ≤ ENNReal.ofReal r :=
    Homogenization.Gagliardo.ae_normalizedCubeMeasure_iff.1 hnorm
  have hnotmem : ∀ᵐ y ∂(volume.restrict (cubeSet Q)), y ∉ V := by
    filter_upwards [hae] with y hy hyV
    have hle : ‖f y‖ ≤ r := by
      rw [← ofReal_norm] at hy
      exact (ENNReal.ofReal_le_ofReal_iff hr).1 hy
    exact absurd hyV.2 (not_lt.2 hle)
  have hzero : (volume.restrict (cubeSet Q)) V = 0 := by
    simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hnotmem
  exact (ne_of_gt hrestrict) hzero

/-! ## The pointwise ellipticity clause -/

section Pointwise

open scoped Matrix.Norms.L2Operator

/-- **The first term of the block, pointwise.** The `L∞` clause
`m⁻¹ ‖k - (k)_{cu_m}‖_{L∞(cu_m)} ≤ δ m^σ` is an essential supremum; on the
summability guard the field is continuous, so the bound holds at every point of
the open cube. -/
theorem matrixOperatorNorm_centeredStreamField_le_of_minimalScale
    {omega : ShellSeq d} {delta sigma : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    (hdelta : 0 ≤ delta)
    (hfirst : ENNReal.ofReal ((m : ℝ)⁻¹) *
        cubeLpENorm (originCube d (m : ℤ)) ∞
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
      ENNReal.ofReal (delta * (m : ℝ) ^ sigma))
    {z : Vec d} (hz : z ∈ openCubeSet (originCube d (m : ℤ))) :
    matrixOperatorNorm
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ))) z) ≤
      (m : ℝ) * (delta * (m : ℝ) ^ sigma) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hrnn : 0 ≤ (m : ℝ) * (delta * (m : ℝ) ^ sigma) := by
    have : (0 : ℝ) ≤ (m : ℝ) ^ sigma := Real.rpow_nonneg hmR.le sigma
    positivity
  have hLinf : cubeLpENorm (originCube d (m : ℤ)) ∞
      (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
      ENNReal.ofReal ((m : ℝ) * (delta * (m : ℝ) ^ sigma)) := by
    have hmul := mul_le_mul' (le_refl (ENNReal.ofReal ((m : ℝ)))) hfirst
    rw [← mul_assoc, ← ENNReal.ofReal_mul hmR.le,
      mul_inv_cancel₀ (ne_of_gt hmR), ENNReal.ofReal_one, one_mul,
      ← ENNReal.ofReal_mul hmR.le] at hmul
    exact hmul
  exact norm_le_of_cubeLpENorm_top_le
    (continuous_centeredStreamField omega hguard) hrnn hLinf hz

/-- **The clause `e.a.ellipticity.pointwise`**, with the absolute
constant `4`.

The hypotheses are exactly: the floor `27 ≤ K` of the print's construction, the
summability guard, and the **first** term of the `e.Xm.deff`
display at every scale `m` with `K ≤ 3^m`. -/
theorem sq_matrixOperatorNorm_centeredStreamField_sub_le
    {omega : ShellSeq d} {delta sigma K : ℝ} (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hsigma : 0 < sigma) (hK : (27 : ℝ) ≤ K)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    (hfirst : ∀ m : ℕ, K ≤ (3 : ℝ) ^ m →
      ENNReal.ofReal ((m : ℝ)⁻¹) *
          cubeLpENorm (originCube d (m : ℤ)) ∞
            (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
        ENNReal.ofReal (delta * (m : ℝ) ^ sigma))
    (x : Vec d) :
    matrixOperatorNorm
        (centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) x -
          centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) 0) ^ 2 ≤
      4 * Real.log (K ^ 2 + vecNormSq x) ^ (2 * (1 + sigma)) := by
  set v : ℝ := vecNormSq x with hv
  have hv0 : 0 ≤ v := vecNormSq_nonneg x
  set rx : ℝ := Real.sqrt v with hrx
  have hrx0 : 0 ≤ rx := Real.sqrt_nonneg v
  have hrxsq : rx ^ 2 = v := Real.sq_sqrt hv0
  set R : ℝ := K + rx with hR
  have hR27 : (27 : ℝ) ≤ R := by rw [hR]; linarith only [hK, hrx0]
  have hRpos : (0 : ℝ) < R := by linarith only [hR27]
  have hlog3 : (1 : ℝ) < Real.log 3 := one_lt_log_three
  have hlog3pos : (0 : ℝ) < Real.log 3 := lt_trans zero_lt_one hlog3
  have hlog27 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogR27 : Real.log 27 ≤ Real.log R :=
    Real.log_le_log (by norm_num) hR27
  have hlogRpos : (0 : ℝ) < Real.log R := by
    linarith only [hlogR27, hlog27, hlog3]
  set y : ℝ := Real.log R / Real.log 3 with hy
  have hy3 : (3 : ℝ) ≤ y := by
    rw [hy, le_div_iff₀ hlog3pos]
    linarith only [hlogR27, hlog27]
  set m : ℕ := ⌈y⌉₊ + 1 with hm
  have hm1 : 1 ≤ m := by rw [hm]; omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have h3y : (3 : ℝ) ^ y = R := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hcancel : Real.log 3 * y = Real.log R := by
      rw [hy]
      field_simp
    rw [hcancel]
    exact Real.exp_log hRpos
  have hceilpow : R ≤ (3 : ℝ) ^ (⌈y⌉₊ : ℕ) := by
    have h1 : (3 : ℝ) ^ y ≤ (3 : ℝ) ^ ((⌈y⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil y)
    rw [h3y, Real.rpow_natCast] at h1
    exact h1
  have h3m : 3 * R ≤ (3 : ℝ) ^ m := by
    rw [hm, pow_succ]
    linarith only [hceilpow]
  have hKle : K ≤ (3 : ℝ) ^ m := by
    rw [hR] at h3m
    linarith only [h3m, hrx0, hK]
  have hrxR : rx ≤ R := by rw [hR]; linarith only [hK]
  have habs : ∀ i : Fin d, |x i| ≤ rx := by
    intro i
    have hsq : x i ^ (2 : ℕ) ≤ v := sq_apply_le_vecNormSq x i
    rw [hrx, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hxmem : x ∈ openCubeSet (originCube d (m : ℤ)) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have h1 := abs_le.1 (habs i)
    rw [zpow_natCast]
    constructor
    · linarith only [h1.1, hrxR, h3m, hRpos]
    · linarith only [h1.2, hrxR, h3m, hRpos]
  have h0mem : (0 : Vec d) ∈ openCubeSet (originCube d (m : ℤ)) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have h3mpos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
    rw [zpow_natCast]
    simp only [Pi.zero_apply]
    constructor <;> linarith only [h3mpos]
  set T : ℝ := (m : ℝ) * (delta * (m : ℝ) ^ sigma) with hT
  have hTx := matrixOperatorNorm_centeredStreamField_le_of_minimalScale hm1
    hguard hdelta.le (hfirst m hKle) hxmem
  have hT0 := matrixOperatorNorm_centeredStreamField_le_of_minimalScale hm1
    hguard hdelta.le (hfirst m hKle) h0mem
  have hcentring :
      centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) x -
          centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) 0 =
        centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x -
          centeredStreamField omega (cubeSet (originCube d (m : ℤ))) 0 := by
    have hgen := centeredStreamField_sub_centring omega hguard 0 m x 0
    simpa only [Nat.cast_zero] using hgen
  have htriangle := norm_sub_le
    (centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x)
    (centeredStreamField omega (cubeSet (originCube d (m : ℤ))) 0)
  simp only [norm_eq_matrixOperatorNorm] at htriangle
  have hsub : matrixOperatorNorm
      (centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) x -
        centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) 0) ≤
      2 * T := by
    rw [hcentring]
    linarith only [htriangle, hTx, hT0]
  have hSnn : (0 : ℝ) ≤ matrixOperatorNorm
      (centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) x -
        centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) 0) :=
    matrixOperatorNorm_nonneg _
  have hsq : matrixOperatorNorm
      (centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) x -
        centeredStreamField omega (cubeSet (originCube d (0 : ℤ))) 0) ^ 2 ≤
      (2 * T) ^ 2 := pow_le_pow_left₀ hSnn hsub 2
  refine le_trans hsq ?_
  -- the arithmetic of the scale
  set L : ℝ := Real.log (K ^ 2 + v) with hL
  have hKsq : (729 : ℝ) ≤ K ^ 2 + v := by nlinarith only [hK, hv0]
  have hlog729 : Real.log 729 = 6 * Real.log 3 := by
    rw [show (729 : ℝ) = 3 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hL6 : (6 : ℝ) < L := by
    have h1 : Real.log 729 ≤ L := Real.log_le_log (by norm_num) hKsq
    linarith only [h1, hlog729, hlog3]
  have hRsq : R ^ 2 ≤ 2 * (K ^ 2 + v) := by
    rw [hR, ← hrxsq]
    nlinarith only [sq_nonneg (K - rx)]
  have hlogR2 : 2 * Real.log R ≤ Real.log 2 + L := by
    have h1 : Real.log (R ^ 2) ≤ Real.log (2 * (K ^ 2 + v)) :=
      Real.log_le_log (by positivity) hRsq
    rw [Real.log_pow, Real.log_mul (by norm_num)
      (by linarith only [hKsq] : K ^ 2 + v ≠ 0)] at h1
    push_cast at h1
    linarith only [h1]
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [this]
  have hlogRlt : Real.log R < 7 * L / 12 := by
    linarith only [hlogR2, hlog2le, hL6]
  have hylogR : y ≤ Real.log R := by
    rw [hy, div_le_iff₀ hlog3pos]
    nlinarith only [hlog3, hlogRpos]
  have hmy : (m : ℝ) < y + 2 := by
    have hceil := Nat.ceil_lt_add_one (le_trans (by norm_num) hy3 : (0 : ℝ) ≤ y)
    rw [hm]
    push_cast
    linarith only [hceil]
  have hmL : (m : ℝ) ≤ L := by
    have h1 : y + 2 ≤ 5 / 3 * y := by linarith only [hy3]
    have h2 : (5 : ℝ) / 3 * y ≤ 5 / 3 * Real.log R := by linarith only [hylogR]
    have h3 : (5 : ℝ) / 3 * Real.log R < 5 / 3 * (7 * L / 12) := by
      linarith only [hlogRlt]
    linarith only [hmy, h1, h2, h3, hL6]
  have hmpow : (m : ℝ) ^ (2 * (1 + sigma)) =
      (m : ℝ) ^ (2 : ℕ) * ((m : ℝ) ^ sigma) ^ (2 : ℕ) := by
    have h2 : ((m : ℝ) ^ sigma) ^ (2 : ℕ) = (m : ℝ) ^ (sigma * 2) := by
      rw [Real.rpow_mul hmR.le, Real.rpow_two]
    rw [h2, show 2 * (1 + sigma) = (2 : ℝ) + sigma * 2 by ring,
      Real.rpow_add hmR, Real.rpow_two]
  have hTsq : (2 * T) ^ 2 = 4 * delta ^ 2 * (m : ℝ) ^ (2 * (1 + sigma)) := by
    rw [hT, hmpow]
    ring
  rw [hTsq]
  have hexp : (0 : ℝ) ≤ 2 * (1 + sigma) := by linarith only [hsigma]
  have hpowle : (m : ℝ) ^ (2 * (1 + sigma)) ≤ L ^ (2 * (1 + sigma)) :=
    Real.rpow_le_rpow hmR.le hmL hexp
  have hpownn : (0 : ℝ) ≤ (m : ℝ) ^ (2 * (1 + sigma)) :=
    Real.rpow_nonneg hmR.le _
  have hd2 : delta ^ 2 ≤ 1 := by nlinarith only [hdelta, hdelta1]
  nlinarith only [hpowle, hpownn, hd2, hdelta]

end Pointwise

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
