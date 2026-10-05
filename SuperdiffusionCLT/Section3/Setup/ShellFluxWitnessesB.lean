/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ShellFluxWitnesses
public import SuperdiffusionCLT.Assumptions.ShellField.MeanValue
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivLargeCube

/-!
# The scale-free endpoint witness of the shells above the cube scale

The second display of the proof of `l.LHS.term1`: for `r >= m`,

> `‖ j_r p - (j_r p)_{cu_m} ‖_{Hminusul(cu_m)}
>    <= C |p| 3^m ‖∇ j_r‖_{L^∞(cu_m)} <= O_{Gamma₂}( C |p| 3^{-(r-m)} )`.

The print derives it from Poincare's inequality and `a.j.reg`, not from
`e.jk.Hminus.endpoint`, which is stated only for cube scales
above the shell scale and therefore covers the complementary range `r < m`.

The route taken here is the deterministic one the print takes.  On `cu_m` the
shell `j_r` is Lipschitz with constant `d * shellCubeDerivNorm m (omega r)`
(`ShellField.matrixOperatorNorm_sub_le_of_derivNorm_le_on_cubeSet` together
with `matrixDerivativeNorm_deriv_le_shellCubeDerivNorm_cubeSet`, both valid for
every shell index and every cube scale), the cube has Euclidean radius
`sqrt d * 3^m / 2`, and centring costs a factor two.  So the centred flux is
bounded on `cu_m` by

`shellFluxLipBound m p r omega
  = d * sqrt d * 3^m * |p| * shellCubeDerivNorm m (omega r)`

in **every** normalized `L̲^q` norm with `1 ≤ q`, hence also in the order-one
hatted negative norm `vecHatNegENormOrderOne`.  The `Gamma₂` tail of
`shellCubeDerivNorm m (omega r)` is at `3^{-r}` for `m ≤ r`
(`isBigOWith_gammaSigma_shellCubeDerivNorm_coordinate` with
`ShellField.shellCubeDerivNorm_mono`), so the envelope has its tail at
`d * sqrt d * |p| * 3^{-(r-m)}`: the amplitude is **scale free**, with a
constant depending on `d` alone.

This is the replacement for the value-envelope route of `ShellFluxWitnesses.lean`,
whose amplitude `shellFluxValueEnvelopeAmplitude d m
= shellValueLargeCubeConst d * sqrt (1 + m)` grows with the cube scale because
it passes through an `L^∞` union bound over the `3^{d(m-r)}` subcubes.

## Main results

* `shellFluxLipBound`, `shellFluxLipConst`;
* `vecCubeLpENorm_shellFlux_sub_le_lipBound`, the deterministic bound in every
  normalized `L̲^q` norm with `1 ≤ q`;
* `vecHatNegENormOrderOne_shellFlux_sub_le_lipBound`, its order-one hatted form;
* `isBigO_gammaSigma_shellFluxLipBound`, the `Gamma₂` tail;
* `exists_shellFluxHatNegWitness_scaleFree`, the packaged four-clause family in
  the shape the `l.LHS.term1` reduction consumes.
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
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ} {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The geometry of the half-open natural cube -/

/-- Every point of the half-open natural cube `cu_m` has Euclidean norm at most
`sqrt d * 3^m / 2`.  The open-cube form is
`vecNorm_le_of_mem_openCubeSet_originCube`; the
half-open cube adds the lower face, on which the same bound holds with
equality in one coordinate. -/
private theorem vecNorm_le_of_mem_cubeSet_originCube {m : ℕ} {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    vecNorm x ≤ Real.sqrt d * ((3 : ℝ) ^ m / 2) := by
  have hcube := mem_cubeSet_originCube_iff.mp hx
  simp only [zpow_natCast] at hcube
  set R : ℝ := (3 : ℝ) ^ m / 2 with hR
  have hR_nonneg : 0 ≤ R := by rw [hR]; positivity
  have hsq : vecNormSq x ≤ (d : ℝ) * R ^ 2 := by
    have hstep : ∀ i : Fin d, x i * x i ≤ R ^ 2 := by
      intro i
      obtain ⟨hlo, hhi⟩ := hcube i
      have hlo' : -R ≤ x i := by rw [hR]; linarith only [hlo]
      have hhi' : x i ≤ R := by rw [hR]; linarith only [hhi]
      have habs : |x i| ≤ R := (abs_le).2 ⟨hlo', hhi'⟩
      have hsquare : (x i) ^ 2 ≤ R ^ 2 := by
        rw [sq_le_sq]
        simpa only [abs_of_nonneg hR_nonneg] using habs
      simpa only [pow_two] using hsquare
    calc vecNormSq x = ∑ i, x i * x i := rfl
      _ ≤ ∑ _i : Fin d, R ^ 2 := Finset.sum_le_sum fun i _ => hstep i
      _ = (d : ℝ) * R ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hB : 0 ≤ Real.sqrt d * R := mul_nonneg (Real.sqrt_nonneg _) hR_nonneg
  have hsq' : vecNorm x ^ 2 ≤ (Real.sqrt d * R) ^ 2 := by
    rw [vecNorm_sq_eq_vecNormSq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    exact hsq
  have hsqrt := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq (vecNorm_nonneg x), Real.sqrt_sq hB] at hsqrt

/-- The origin belongs to every half-open natural cube. -/
private theorem zero_mem_cubeSet_originCube (d m : ℕ) :
    (0 : Vec d) ∈ cubeSet (originCube d (m : ℤ)) := by
  rw [mem_cubeSet_originCube_iff]
  intro i
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
  refine ⟨?_, ?_⟩
  · show (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (m : ℤ) ≤ (0 : Vec d) i
    have : (0 : Vec d) i = 0 := rfl
    rw [this]
    linarith only [hpow]
  · show (0 : Vec d) i < (1 / 2 : ℝ) * (3 : ℝ) ^ (m : ℤ)
    have : (0 : Vec d) i = 0 := rfl
    rw [this]
    linarith only [hpow]

/-! ## The deterministic Lipschitz envelope of the centred shell flux -/

/-- The scale-free deterministic envelope of the centred shell flux on `cu_m`:
the Lipschitz constant of the shell on the cube times the cube diameter times
the direction magnitude, with the centring factor two already included. -/
def shellFluxLipBound (m : ℕ) (p : Vec d) (r : ℕ) (omega : ShellSeq d) : ℝ :=
  (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ m * Book.Ch02.vecNorm p *
    ShellField.shellCubeDerivNorm m (omega r)

/-- The dimension-only constant of the scale-free endpoint amplitude. -/
def shellFluxLipConst (d : ℕ) : ℝ := (d : ℝ) * Real.sqrt d

theorem shellFluxLipConst_nonneg (d : ℕ) : 0 ≤ shellFluxLipConst d := by
  rw [shellFluxLipConst]
  positivity

theorem shellFluxLipBound_nonneg (m : ℕ) (p : Vec d) (r : ℕ)
    (omega : ShellSeq d) : 0 ≤ shellFluxLipBound m p r omega := by
  rw [shellFluxLipBound]
  have h1 : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ m := by positivity
  exact mul_nonneg (mul_nonneg h1 (Book.Ch02.vecNorm_nonneg p))
    (ShellField.shellCubeDerivNorm_nonneg m (omega r))

theorem measurable_shellFluxLipBound (m : ℕ) (p : Vec d) (r : ℕ) :
    Measurable (shellFluxLipBound m p r : ShellSeq d → ℝ) := by
  show Measurable fun omega : ShellSeq d =>
    (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ m * Book.Ch02.vecNorm p *
      ShellField.shellCubeDerivNorm m (omega r)
  exact measurable_const.mul
    ((ShellField.shellCubeDerivNorm_measurable m).comp
      (ShellField.measurable_shellCoordinate r))

/-- **The two-point bound of the shell flux on `cu_m`**: the mean value
inequality on the half-open cube against the cube derivative norm of the shell,
composed with the cube radius. -/
theorem vecNorm_shellFlux_sub_origin_le (omega : ShellSeq d) (m r : ℕ)
    (p : Vec d) {x : Vec d} (hx : x ∈ cubeSet (originCube d (m : ℤ))) :
    vecNorm (shellFlux omega r p x - shellFlux omega r p 0) ≤
      (d : ℝ) * ShellField.shellCubeDerivNorm m (omega r) *
        (Real.sqrt d * ((3 : ℝ) ^ m / 2)) * Book.Ch02.vecNorm p := by
  have hreg : ∀ y : Vec d, shellReg omega r y = (omega r) y := by
    intro y
    simp only [shellReg, ShellField.forgetShell_apply]
  have hsub : shellFlux omega r p x - shellFlux omega r p 0 =
      matVecMul ((omega r) x - (omega r) 0) p := by
    simp only [shellFlux, hreg]
    funext i
    simp only [matVecMul, Pi.sub_apply, Matrix.sub_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsub]
  have hop := vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm
    ((omega r) x - (omega r) 0) p
  have hB : ∀ z ∈ cubeSet (originCube d (m : ℤ)),
      ShellField.matrixDerivativeNorm (ShellField.deriv (omega r) z) ≤
        ShellField.shellCubeDerivNorm m (omega r) := fun z hz =>
    matrixDerivativeNorm_deriv_le_shellCubeDerivNorm_cubeSet m (omega r) hz
  have hmv := ShellField.matrixOperatorNorm_sub_le_of_derivNorm_le_on_cubeSet
    (omega r) (originCube d (m : ℤ))
    (ShellField.shellCubeDerivNorm m (omega r)) hB hx
    (zero_mem_cubeSet_originCube d m)
  have hdist : euclideanDist x 0 ≤ Real.sqrt d * ((3 : ℝ) ^ m / 2) := by
    have hx0 : euclideanDist x (0 : Vec d) = Book.Ch02.vecNorm x := by
      rw [euclideanDist, euclideanNorm, sub_zero,
        ShellField.vecNorm_eq_sqrt_vecNormSq]
    rw [hx0]
    exact vecNorm_le_of_mem_cubeSet_originCube hx
  have hdnn : (0 : ℝ) ≤ (d : ℝ) * ShellField.shellCubeDerivNorm m (omega r) :=
    mul_nonneg (Nat.cast_nonneg d) (ShellField.shellCubeDerivNorm_nonneg m (omega r))
  have hstep : matrixOperatorNorm ((omega r) x - (omega r) 0) ≤
      (d : ℝ) * ShellField.shellCubeDerivNorm m (omega r) *
        (Real.sqrt d * ((3 : ℝ) ^ m / 2)) :=
    le_trans hmv (mul_le_mul_of_nonneg_left hdist hdnn)
  exact le_trans hop (mul_le_mul_of_nonneg_right hstep (Book.Ch02.vecNorm_nonneg p))

/-! ## The deterministic clause in the normalized norms -/

/-- **The centred shell flux on `cu_m`, in every normalized `L̲^q` norm with
`1 ≤ q`.**  Centring by the cube average costs a factor two against centring by
the value at the origin (`vecCubeLpENorm_sub_volumeAverageVec_le`), and the
origin-centred flux is bounded pointwise on `cu_m` by half the envelope
(`vecNorm_shellFlux_sub_origin_le`). -/
theorem vecCubeLpENorm_shellFlux_sub_le_lipBound {q : ℝ≥0∞} (hq : 1 ≤ q)
    (m r : ℕ) (omega : ShellSeq d) (p : Vec d) :
    vecCubeLpENorm (originCube d (m : ℤ)) q
      (fun x => shellFlux omega r p x -
        volumeAverageVec (cubeSet (originCube d (m : ℤ))) (shellFlux omega r p)) ≤
      ENNReal.ofReal (shellFluxLipBound m p r omega) := by
  classical
  have hFcont : Continuous (shellFlux omega r p) :=
    continuous_shellFlux' omega r p
  have hGL2 : MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (fun x => shellFlux omega r p x - shellFlux omega r p 0) :=
    memVectorL2_sub_const (shellFlux omega r p 0)
      (memVectorL2_shellFlux (originCube d (m : ℤ)) r omega p)
  have havgG : volumeAverageVec (cubeSet (originCube d (m : ℤ)))
        (fun x => shellFlux omega r p x - shellFlux omega r p 0) =
      volumeAverageVec (openCubeSet (originCube d (m : ℤ)))
        (fun x => shellFlux omega r p x - shellFlux omega r p 0) :=
    volumeAverageVec_cubeSet_eq_openCubeSet _ _
  have hsubavg : volumeAverageVec (cubeSet (originCube d (m : ℤ)))
        (fun x => shellFlux omega r p x - shellFlux omega r p 0) =
      volumeAverageVec (cubeSet (originCube d (m : ℤ))) (shellFlux omega r p) -
        shellFlux omega r p 0 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverageVec_sub_const
      (originCube d (m : ℤ)) hFcont (shellFlux omega r p 0)
  have hfun : (fun x => shellFlux omega r p x -
        volumeAverageVec (cubeSet (originCube d (m : ℤ))) (shellFlux omega r p)) =
      (fun x => (fun y => shellFlux omega r p y - shellFlux omega r p 0) x -
        volumeAverageVec (openCubeSet (originCube d (m : ℤ)))
          (fun y => shellFlux omega r p y - shellFlux omega r p 0)) := by
    funext x
    rw [← havgG, hsubavg]
    funext i
    simp only [Pi.sub_apply]
    ring
  have hhalf0 : (0 : ℝ) ≤ (d : ℝ) * ShellField.shellCubeDerivNorm m (omega r) *
      (Real.sqrt d * ((3 : ℝ) ^ m / 2)) * Book.Ch02.vecNorm p := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) ?_) ?_)
      (Book.Ch02.vecNorm_nonneg p)
    · exact ShellField.shellCubeDerivNorm_nonneg m (omega r)
    · positivity
  have hpt : vecCubeLpENorm (originCube d (m : ℤ)) q
        (fun x => shellFlux omega r p x - shellFlux omega r p 0) ≤
      ENNReal.ofReal ((d : ℝ) * ShellField.shellCubeDerivNorm m (omega r) *
        (Real.sqrt d * ((3 : ℝ) ^ m / 2)) * Book.Ch02.vecNorm p) :=
    vecCubeLpENorm_le_ofReal_of_forall_le hhalf0
      (((HilbertVec.ofVecL d).continuous).comp
        (hFcont.sub continuous_const)).aestronglyMeasurable
      (fun x hx => vecNorm_shellFlux_sub_origin_le omega m r p hx)
  have hdouble : (2 : ℝ≥0∞) *
        ENNReal.ofReal ((d : ℝ) * ShellField.shellCubeDerivNorm m (omega r) *
          (Real.sqrt d * ((3 : ℝ) ^ m / 2)) * Book.Ch02.vecNorm p) =
      ENNReal.ofReal (shellFluxLipBound m p r omega) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by
      simp only [ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [shellFluxLipBound]
    ring
  rw [hfun]
  refine le_trans (vecCubeLpENorm_sub_volumeAverageVec_le hq hGL2) ?_
  exact le_trans (mul_le_mul_of_nonneg_left hpt (by norm_num))
    (le_of_eq hdouble)

/-- **The centred shell flux on `cu_m`, in the order-one hatted negative
norm.**  The order-one hatted norm of an `L̲²` field is at most its `L̲²` norm
(`vecHatNegENormOrderOne_le_vecCubeLpENorm`). -/
theorem vecHatNegENormOrderOne_shellFlux_sub_le_lipBound (m r : ℕ) (omega : ShellSeq d)
    (p : Vec d) :
    vecHatNegENormOrderOne (originCube d (m : ℤ))
      (fun x => shellFlux omega r p x -
        volumeAverageVec (cubeSet (originCube d (m : ℤ))) (shellFlux omega r p)) ≤
      ENNReal.ofReal (shellFluxLipBound m p r omega) := by
  classical
  have havg : volumeAverageVec (cubeSet (originCube d (m : ℤ)))
        (shellFlux omega r p) =
      volumeAverageVec (openCubeSet (originCube d (m : ℤ)))
        (shellFlux omega r p) :=
    volumeAverageVec_cubeSet_eq_openCubeSet _ (shellFlux omega r p)
  have hmemLp : MemLp (hilbertifyVecField
      (fun x : Vec d => shellFlux omega r p x -
        volumeAverageVec (openCubeSet (originCube d (m : ℤ)))
          (shellFlux omega r p)))
      2 (normalizedCubeMeasure (originCube d (m : ℤ))) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (memHilbertVectorL2_hilbertifyVecField
      (memVectorL2_sub_const (volumeAverageVec
        (openCubeSet (originCube d (m : ℤ))) (shellFlux omega r p))
        (memVectorL2_shellFlux (originCube d (m : ℤ)) r omega p))).smul_measure
      ENNReal.ofReal_ne_top
  have hhat : vecHatNegENormOrderOne (originCube d (m : ℤ))
      (fun x => shellFlux omega r p x -
        volumeAverageVec (openCubeSet (originCube d (m : ℤ)))
          (shellFlux omega r p)) ≤
      vecCubeLpENorm (originCube d (m : ℤ)) 2
        (fun x => shellFlux omega r p x -
          volumeAverageVec (openCubeSet (originCube d (m : ℤ)))
            (shellFlux omega r p)) :=
    vecHatNegENormOrderOne_le_vecCubeLpENorm hmemLp
  rw [havg]
  refine le_trans hhat ?_
  rw [← havg]
  exact vecCubeLpENorm_shellFlux_sub_le_lipBound (by norm_num) m r omega p

/-! ## The `Gamma₂` tail of the envelope -/

/-- The ratio of the cube weight to the shell weight is the printed decay. -/
private theorem threePow_mul_inv_eq_rpow_neg {m r : ℕ} (hmr : m ≤ r) :
    (3 : ℝ) ^ m * ((3 : ℝ) ^ r)⁻¹ = (3 : ℝ) ^ (-(((r - m : ℕ)) : ℝ)) := by
  have hsplit : (3 : ℝ) ^ r = (3 : ℝ) ^ m * (3 : ℝ) ^ (r - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hmr]
  have h3m : ((3 : ℝ) ^ m) ≠ 0 := by positivity
  have hrpow : (3 : ℝ) ^ (-(((r - m : ℕ)) : ℝ)) = ((3 : ℝ) ^ (r - m))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  rw [hrpow, hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ h3m, one_mul]

/-- The deterministic factor of the envelope, rescaled to the printed
amplitude. -/
private theorem shellFluxLip_amplitude_le {d : ℕ} {m r : ℕ} (hmr : m ≤ r)
    (p : Vec d) {Cge : ℝ} (hCge : shellFluxLipConst d ≤ Cge) :
    (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ m * Book.Ch02.vecNorm p *
        ((3 : ℝ) ^ r)⁻¹ ≤
      Cge * Book.Ch02.vecNorm p * (3 : ℝ) ^ (-(((r - m : ℕ)) : ℝ)) := by
  have hpow := threePow_mul_inv_eq_rpow_neg (m := m) (r := r) hmr
  have hwnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((r - m : ℕ)) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hcoef : (d : ℝ) * Real.sqrt d * Book.Ch02.vecNorm p ≤
      Cge * Book.Ch02.vecNorm p := by
    have h := mul_le_mul_of_nonneg_right hCge (Book.Ch02.vecNorm_nonneg p)
    rwa [shellFluxLipConst] at h
  have hleft : (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ m * Book.Ch02.vecNorm p *
        ((3 : ℝ) ^ r)⁻¹ =
      ((d : ℝ) * Real.sqrt d * Book.Ch02.vecNorm p) *
        ((3 : ℝ) ^ m * ((3 : ℝ) ^ r)⁻¹) := by ring
  rw [hleft, hpow]
  exact mul_le_mul_of_nonneg_right hcoef hwnn

/-- The cube-`m` derivative norm of a shell of index `r ≥ m` has the shell's
own `Gamma₂` tail at `3^{-r}`. -/
theorem isBigO_gammaSigma_shellCubeDerivNorm_at (hJ3 : ShellLawJ3 d P)
    {m r : ℕ} (hmr : m ≤ r) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d => ShellField.shellCubeDerivNorm m (omega r))
      (((3 : ℝ) ^ r)⁻¹) := by
  have hbase : IsBigOWith P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d => ShellField.shellCubeDerivNorm m (omega r))
      (((3 : ℝ) ^ r)⁻¹) :=
    (SuperdiffusionCLT.Section2.Estimates.Stream.isBigOWith_gammaSigma_shellCubeDerivNorm_coordinate
        hJ3 r).of_le
      (fun omega => ShellField.shellCubeDerivNorm_mono hmr (omega r))
  exact (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (mu := P.toMeasure) (Psi := gammaSigma 2)
    (X := fun omega : ShellSeq d => ShellField.shellCubeDerivNorm m (omega r))
    (A := ((3 : ℝ) ^ r)⁻¹)
    (fun omega => ShellField.shellCubeDerivNorm_nonneg m (omega r))).1 hbase

/-- **The scale-free `Gamma₂` tail of the endpoint envelope**.  For `m ≤ r` the
cube-`m` derivative norm of shell `r` is dominated by the shell's own-cube derivative
norm, whose `Gamma₂` tail is at `3^{-r}`; multiplying by the deterministic
factor `d * sqrt d * 3^m * |p|` gives the amplitude
`d * sqrt d * |p| * 3^{-(r-m)}`, which involves the cube scale only through the
printed decay. -/
theorem isBigO_gammaSigma_shellFluxLipBound (hJ3 : ShellLawJ3 d P)
    {m r : ℕ} (hmr : m ≤ r) (p : Vec d) {Cge : ℝ}
    (hCge : shellFluxLipConst d ≤ Cge) :
    IsBigO P.toMeasure (gammaSigma 2) (shellFluxLipBound m p r)
      (Cge * Book.Ch02.vecNorm p * (3 : ℝ) ^ (-((r - m : ℕ) : ℝ))) := by
  have hc0 : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ m *
      Book.Ch02.vecNorm p := by
    have h1 : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ m := by positivity
    exact mul_nonneg h1 (Book.Ch02.vecNorm_nonneg p)
  exact ((isBigO_gammaSigma_shellCubeDerivNorm_at hJ3 hmr).const_mul hc0).mono_scale
    (shellFluxLip_amplitude_le hmr p hCge)

/-! ## The packaged witness family -/

/-- **The `Ĥ̲^{-1}` endpoint witness family for the shells above the cube
scale, with a scale-free constant.**  This is the four-clause group the
`l.LHS.term1` reduction consumes as `hZhmGe`
(in `Section3/Terms/LHSTerm1FrozenReduction.lean`), with the
constant depending on `d` alone.  Its statement is that binder verbatim.

The witness is `shellFluxLipBound`, built from the print's own `r ≥ m` route
(Poincare plus `a.j.reg`); no value envelope and no union
bound over subcubes occur, so no largeness gate on the constant appears. -/
theorem exists_shellFluxHatNegWitness_scaleFree (hJ3 : ShellLawJ3 d P)
    (S : ScaleSelection) (p : Vec d) (Cge : ℝ)
    (hCge : shellFluxLipConst d ≤ Cge) :
    ∃ ZhmGe : ℕ → ShellSeq d → ℝ,
      (∀ r omega, 0 ≤ ZhmGe r omega) ∧
      (∀ r, Measurable (ZhmGe r)) ∧
      (∀ r ∈ Finset.Ioc S.m S.LPrime,
        IsBigO P.toMeasure (gammaSigma 2) (ZhmGe r)
          (Cge * Book.Ch02.vecNorm p *
            (3 : ℝ) ^ (-((r - S.m : ℕ) : ℝ)))) ∧
      (∀ r ∈ Finset.Ioc S.m S.LPrime, ∀ omega : ShellSeq d,
        vecHatNegENormOrderOne (originCube d (S.m : ℤ))
          (fun x => shellFlux omega r p x -
            volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
              (shellFlux omega r p)) ≤
          ENNReal.ofReal (ZhmGe r omega)) := by
  classical
  refine ⟨fun r => shellFluxLipBound S.m p r, ?_, ?_, ?_, ?_⟩
  · exact fun r omega => shellFluxLipBound_nonneg S.m p r omega
  · exact fun r => measurable_shellFluxLipBound S.m p r
  · intro r hr
    exact isBigO_gammaSigma_shellFluxLipBound hJ3
      (le_of_lt (Finset.mem_Ioc.mp hr).1) p hCge
  · intro r _hr omega
    exact vecHatNegENormOrderOne_shellFlux_sub_le_lipBound S.m r omega p

end

end SuperdiffusionCLT.Section3.Setup
