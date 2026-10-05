/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyOrderOneB
public import SuperdiffusionCLT.Section3.ResponseFields.Regbounds
public import SuperdiffusionCLT.Section5.Carriers.BlockOffset
public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsAprioriOrderOne
public import SuperdiffusionCLT.Frozen.Section2.StreamIncrementScaleEstimates
public import SuperdiffusionCLT.Probability.OrliczTriangle
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependenceRestriction

/-!
# The weak bound of `e.response.energy`

The flux `hshellFlux` of the shell field is the scaled sum of the shell fluxes `j_r e`,
`m - h < r ≤ m`.  This file bounds, for `|e| = 1` and the cube `cu_Kc` with `m ≤ Kc`:

* `hshellFlux_hatNeg_isBigO`: `‖F - (F)‖_{Ĥ⁻¹(cu_Kc)} = O_{Γ₂}(C σ̄_{m-h}⁻¹ (1+(Kc-m)) 3^{-(Kc-m)})`,
  from the order-one endpoint (a correction of the printed text; see `ERRATA.md`) and the
  finite `Γ₂` triangle rule;
* `hshellFlux_avg_isBigO`: the same amplitude for `|(F)_{cu_Kc}|`;
* `hshellFlux_L4_isBigO`: `‖F - (F)‖_{L̲⁴(cu_Kc)} = O_{Γ₂}(C σ̄_{m-h}⁻¹ h^{1/2})`, from the
  `L^p` increment clause at `p = 4`.

The second-moment bound for the Neumann-minus-Dirichlet gradient is in `EnergyWeakB`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields

variable {d : ℕ}

theorem ofReal_sum_le_sum_ofReal {ι : Type*} (t : Finset ι) (a : ι → ℝ) :
    ENNReal.ofReal (∑ r ∈ t, a r) ≤ ∑ r ∈ t, ENNReal.ofReal (a r) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

/-- A finite sum comes out of a normalized cube average of continuous integrands. -/
theorem volumeAverage_cubeSet_sum_of_continuous (Q : TriadicCube d) {ι : Type*}
    (t : Finset ι) (f : ι → Vec d → ℝ) (hf : ∀ r ∈ t, Continuous (f r)) :
    volumeAverage (cubeSet Q) (fun x => ∑ r ∈ t, f r x) =
      ∑ r ∈ t, volumeAverage (cubeSet Q) (f r) := by
  classical
  simp only [volumeAverage]
  rw [MeasureTheory.integral_finsetSum _
    (fun r hr => SuperdiffusionCLT.Section2.Estimates.Stream.integrableOn_cubeSet_of_continuous
      Q (hf r hr)), Finset.mul_sum]

/-- The order-one hatted negative norm is subadditive on finite sums of continuous fields,
and homogeneous for nonnegative scalars. -/
theorem vecHatNegENormOrderOne_smul_sum_le (Q : TriadicCube d) {ι : Type*} (t : Finset ι)
    (G : ι → Vec d → Vec d) (hG : ∀ r ∈ t, Continuous (G r)) {c : ℝ} (hc : 0 ≤ c) :
    vecHatNegENormOrderOne Q (fun x => c • ∑ r ∈ t, G r x) ≤
      ENNReal.ofReal c * ∑ r ∈ t, vecHatNegENormOrderOne Q (G r) := by
  classical
  refine vecHatNegENormOrderOne_le fun g hg => ?_
  have hGc : Continuous (euclideanGradient g) :=
    SuperdiffusionCLT.Section2.Estimates.Stream.continuous_euclideanGradient' hg.contDiff
  have hpt : ∀ x, vecGradientPairingDensity (fun x => c • ∑ r ∈ t, G r x) g x =
      c * ∑ r ∈ t, vecGradientPairingDensity (G r) g x := by
    intro x
    simp only [SuperdiffusionCLT.Section2.Norms.vecGradientPairingDensity_eq_vecDot,
      vecDot, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcont : ∀ r ∈ t, Continuous (vecGradientPairingDensity (G r) g) := by
    intro r hr
    have : vecGradientPairingDensity (G r) g =
        fun x => vecDot (G r x) (euclideanGradient g x) :=
      funext fun x =>
        SuperdiffusionCLT.Section2.Norms.vecGradientPairingDensity_eq_vecDot _ _ x
    rw [this]
    exact SuperdiffusionCLT.Section2.Estimates.Stream.continuous_vecDot (hG r hr) hGc
  have havg : volumeAverage (cubeSet Q)
      (vecGradientPairingDensity (fun x => c • ∑ r ∈ t, G r x) g) =
      c * ∑ r ∈ t, volumeAverage (cubeSet Q) (vecGradientPairingDensity (G r) g) := by
    rw [show vecGradientPairingDensity (fun x => c • ∑ r ∈ t, G r x) g =
        fun x => c * ∑ r ∈ t, vecGradientPairingDensity (G r) g x from funext hpt,
      SuperdiffusionCLT.Section2.Norms.volumeAverage_const_mul,
      volumeAverage_cubeSet_sum_of_continuous Q t _ hcont]
  rw [havg, ENNReal.ofReal_mul hc]
  refine mul_le_mul' le_rfl ((ofReal_sum_le_sum_ofReal _ _).trans ?_)
  exact Finset.sum_le_sum fun r _ => le_vecHatNegENormOrderOne _ hg


/-! ## The geometric sum of the shell amplitudes -/

theorem sum_two_thirds_pow_Ioc_le (a m : ℕ) :
    ∑ r ∈ Finset.Ioc a m, ((2 : ℝ) / 3) ^ (m - r) ≤ 3 := by
  classical
  have hinj : Set.InjOn (fun r : ℕ => m - r) (Finset.Ioc a m : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_Ioc.1 (by exact_mod_cast hx)
    have hy' := Finset.mem_Ioc.1 (by exact_mod_cast hy)
    simp only at hxy
    omega
  have himg : (Finset.Ioc a m).image (fun r => m - r) ⊆ Finset.range (m + 1) := by
    intro j hj
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_range.2 (by omega)
  have h1 : ∑ r ∈ Finset.Ioc a m, ((2 : ℝ) / 3) ^ (m - r) =
      ∑ j ∈ (Finset.Ioc a m).image (fun r => m - r), ((2 : ℝ) / 3) ^ j :=
    (Finset.sum_image hinj).symm
  rw [h1]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg himg
    (fun j _ _ => by positivity)) ?_
  rw [geom_sum_eq (by norm_num : (2 : ℝ) / 3 ≠ 1)]
  have hpow : 0 ≤ ((2 : ℝ) / 3) ^ (m + 1) := by positivity
  rw [div_le_iff_of_neg (by norm_num : (2 : ℝ) / 3 - 1 < 0)]
  linarith only [hpow]

theorem one_add_le_two_pow (j : ℕ) : (1 : ℝ) + j ≤ 2 ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
      push_cast
      rw [pow_succ]
      have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      linarith only [ih, this]

theorem poly_geom_term_le (Delta j : ℕ) :
    (1 + (((Delta + j : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Delta + j : ℕ)) : ℝ)) ≤
      ((1 + (Delta : ℝ)) * (3 : ℝ) ^ (-(Delta : ℝ))) * ((2 : ℝ) / 3) ^ j := by
  have h3 : ∀ n : ℕ, (3 : ℝ) ^ (-(n : ℝ)) = ((3 : ℝ) ^ n)⁻¹ := fun n => by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [h3, h3]
  have hj := one_add_le_two_pow j
  have hD : (0 : ℝ) ≤ Delta := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hle : (1 + ((Delta + j : ℕ) : ℝ)) ≤ (1 + (Delta : ℝ)) * 2 ^ j := by
    push_cast
    nlinarith only [hj, hD, hj0]
  have hq : (0 : ℝ) < (3 : ℝ) ^ Delta := by positivity
  rw [pow_add, mul_inv, div_pow]
  have e1 : ((1 + (Delta : ℝ)) * ((3 : ℝ) ^ Delta)⁻¹) * (2 ^ j / 3 ^ j) =
      (1 + (Delta : ℝ)) * 2 ^ j * (((3 : ℝ) ^ Delta)⁻¹ * ((3 : ℝ) ^ j)⁻¹) := by
    rw [div_eq_mul_inv]; ring
  rw [e1]
  have hpos : (0 : ℝ) ≤ ((3 : ℝ) ^ Delta)⁻¹ * ((3 : ℝ) ^ j)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_right hle hpos


theorem sum_shell_amplitude_le (a m Kc : ℕ) (hmK : m ≤ Kc) :
    ∑ r ∈ Finset.Ioc a m, (1 + (((Kc - r : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - r : ℕ)) : ℝ)) ≤
      3 * ((1 + (((Kc - m : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - m : ℕ)) : ℝ))) := by
  set W : ℝ := (1 + (((Kc - m : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - m : ℕ)) : ℝ)) with hW
  have hterm : ∀ r ∈ Finset.Ioc a m,
      (1 + (((Kc - r : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - r : ℕ)) : ℝ)) ≤
        W * ((2 : ℝ) / 3) ^ (m - r) := by
    intro r hr
    have hrm : r ≤ m := (Finset.mem_Ioc.1 hr).2
    have : Kc - r = (Kc - m) + (m - r) := by omega
    rw [this]
    exact poly_geom_term_le (Kc - m) (m - r)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  calc W * ∑ r ∈ Finset.Ioc a m, ((2 : ℝ) / 3) ^ (m - r) ≤ W * 3 :=
        mul_le_mul_of_nonneg_left (sum_two_thirds_pow_Ioc_le a m) hW0
    _ = 3 * W := mul_comm _ _

/-! ## The flux decomposition and its average -/

theorem volumeAverageVec_cubeSet_sum_of_continuous (Q : TriadicCube d) {ι : Type*}
    (t : Finset ι) (G : ι → Vec d → Vec d) (hG : ∀ r ∈ t, Continuous (G r)) :
    volumeAverageVec (cubeSet Q) (fun x => ∑ r ∈ t, G r x) =
      ∑ r ∈ t, volumeAverageVec (cubeSet Q) (G r) := by
  funext i
  simp only [volumeAverageVec, Finset.sum_apply]
  exact volumeAverage_cubeSet_sum_of_continuous Q t (fun r x => G r x i)
    (fun r hr => (continuous_apply i).comp (hG r hr))

theorem volumeAverageVec_const_smul' (U : Set (Vec d)) (c : ℝ) (f : Vec d → Vec d) :
    volumeAverageVec U (fun x => c • f x) = c • volumeAverageVec U f := by
  funext i
  simp only [volumeAverageVec, Pi.smul_apply, smul_eq_mul]
  rw [SuperdiffusionCLT.Section2.Norms.volumeAverage_const_mul]

/-- The flux of `e.setup.w` as the scaled sum of the shell fluxes. -/
theorem hshellFlux_eq_smul_sum [NeZero d] (nu : ℝ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    {m h : ℕ} (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (e : Vec d) :
    hshellFlux nu P m h omega e = fun x =>
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu (m - h) P)⁻¹ •
        ∑ r ∈ Finset.Ioc (m - h) m,
          SuperdiffusionCLT.Section3.Setup.shellFlux omega r e x := by
  funext x
  rw [hshellFlux]
  congr 1
  exact SuperdiffusionCLT.Section3.Setup.matVecMul_streamCutoff_sub_eq_sum_shellFlux
    omega (Nat.sub_le m h) e x


open SuperdiffusionCLT.Section2.Cutoff SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open Homogenization.IndependentSums

/-- **The weak bound of `e.response.energy`**: `‖F‖_{Ĥ⁻¹(cu_Kc)}` for the centred shell flux
`F = hshellFlux`, through the E2 endpoint and the finite `Γ₂` triangle rule. -/
theorem hshellFlux_hatNeg_isBigO [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : ℝ), 0 < nu →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P → ∀ (m h Kc : ℕ), 1 ≤ h → h ≤ m → m ≤ Kc →
      ∀ e : Vec d, vecNormSq e = 1 →
      ∃ Z : ShellSeq d → ℝ, (∀ omega, 0 ≤ Z omega) ∧ Measurable Z ∧
        IsBigO P.toMeasure (gammaSigma 2) Z
          (C * (sigmaBarInfinite nu (m - h) P)⁻¹ *
            ((1 + (((Kc - m : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - m : ℕ)) : ℝ)))) ∧
        ∀ omega, vecHatNegENormOrderOne (originCube d (Kc : ℤ))
            (fun x => hshellFlux nu P m h omega e x -
              volumeAverageVec (cubeSet (originCube d (Kc : ℤ)))
                (hshellFlux nu P m h omega e)) ≤ ENNReal.ofReal (Z omega) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hCend : 0 < SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst d := by
    have htri : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
    have hCdm : 0 < Section2.Norms.cubeDepthMomentTailConst d 2 :=
      Section2.Norms.cubeDepthMomentTailConst_pos hd0 2
    have hCsv : 0 < SuperdiffusionCLT.Section2.Estimates.Stream.shellValueLargeCubeConst d :=
      SuperdiffusionCLT.Section2.Estimates.Stream.shellValueLargeCubeConst_pos_of_pos hd0
    have hCms : 0 < SuperdiffusionCLT.Section2.Estimates.Stream.multiscaleOrderOneConst d :=
      lt_of_lt_of_le zero_lt_one
        (SuperdiffusionCLT.Section2.Estimates.Stream.one_le_multiscaleOrderOneConst d)
    have hCav : 0 < SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d :=
      Section2.Norms.spatialAverageTailConst_pos hd0
    rw [SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst]
    positivity
  refine ⟨16384 * SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst d * 3,
    by positivity, ?_⟩
  intro nu hnu P hPrefix hJ1 hJ2 hJ3 hJ4 m h Kc h1 hhm hmK e he
  have hJ1' : ShellLawJ1 d P := SuperdiffusionCLT.Section3.HighContrast.shellLawJ1_of_shellLawJ1Restriction hJ1
  have hS : 0 < sigmaBarInfinite nu (m - h) P :=
    sigmaBarInfinite_pos hnu (m - h) hPrefix hJ2 hJ3 hJ4
  set S := sigmaBarInfinite nu (m - h) P with hSdef
  have hen : vecNorm e = 1 := by
    have h2 := vecNorm_sq_eq_vecNormSq (d := d) e
    rw [he] at h2
    have h0 := vecNorm_nonneg e
    nlinarith only [h2, h0]
  have hen0 : 0 < vecNorm e := by rw [hen]; exact one_pos
  set t : Finset ℕ := Finset.Ioc (m - h) m with htdef
  have ht : t.Nonempty := ⟨m, Finset.mem_Ioc.2 ⟨by omega, le_rfl⟩⟩
  have hrK : ∀ r ∈ t, r ≤ Kc := fun r hr => (Finset.mem_Ioc.1 hr).2.trans hmK
  set Zr : ℕ → ShellSeq d → ℝ := fun r omega =>
    SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusBound r Kc e omega with hZr
  refine ⟨fun omega => S⁻¹ * ∑ r ∈ t, Zr r omega, ?_, ?_, ?_, ?_⟩
  · intro omega
    refine mul_nonneg (inv_nonneg.2 hS.le) (Finset.sum_nonneg fun r _ => ?_)
    exact SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusBound_nonneg r Kc e omega
  · refine Measurable.const_mul (Finset.measurable_sum t fun r _ => ?_) _
    exact SuperdiffusionCLT.Section2.Estimates.Stream.measurable_shellHminusBound r Kc e
  · have hbig : ∀ r ∈ t, IsBigO P.toMeasure (gammaSigma 2) (Zr r)
        (SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst d * vecNorm e *
          ((1 + (((Kc - r : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - r : ℕ)) : ℝ)))) := fun r hr =>
      SuperdiffusionCLT.Section2.Estimates.Stream.isBigO_gammaSigma_shellHminusBound
        hPrefix hJ1' hJ3 hJ4 hd (hrK r hr) hen0
    have hpos : ∀ r ∈ t, 0 < SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst d *
        vecNorm e * ((1 + (((Kc - r : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - r : ℕ)) : ℝ))) := by
      intro r _
      have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(((Kc - r : ℕ)) : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have h3 : (0 : ℝ) < 1 + (((Kc - r : ℕ)) : ℝ) := by positivity
      positivity
    have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_finset_sum_of_one_le (mu := P.toMeasure) t
      (by norm_num : (1 : ℝ) ≤ 2) ht hpos hbig
      (fun r _ => SuperdiffusionCLT.Section2.Estimates.Stream.measurable_shellHminusBound
        r Kc e)
    have hscaled := hsum.const_mul (c := S⁻¹) (inv_nonneg.2 hS.le)
    refine hscaled.mono_scale ?_
    have hsumeq : ∑ i ∈ t, SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst d *
        vecNorm e * ((1 + (((Kc - i : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - i : ℕ)) : ℝ))) =
        SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst d *
          ∑ i ∈ t, ((1 + (((Kc - i : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - i : ℕ)) : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hen, mul_one]
    rw [hsumeq]
    have hsa := sum_shell_amplitude_le (m - h) m Kc hmK
    have hcoef : 0 ≤ S⁻¹ * (16384 *
        SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst d) := by
      positivity
    calc S⁻¹ * (16384 * (SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst d *
          ∑ i ∈ t, ((1 + (((Kc - i : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - i : ℕ)) : ℝ)))))
        = S⁻¹ * (16384 * SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst d) *
            ∑ i ∈ t, ((1 + (((Kc - i : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - i : ℕ)) : ℝ))) := by
          ring
      _ ≤ S⁻¹ * (16384 * SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusConst d) *
            (3 * ((1 + (((Kc - m : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - m : ℕ)) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hsa hcoef
      _ = _ := by ring
  · intro omega
    have hcont : ∀ r ∈ t, Continuous (SuperdiffusionCLT.Section3.Setup.shellFlux omega r e) :=
      fun r _ => SuperdiffusionCLT.Section2.Estimates.Stream.continuous_shellFlux' omega r e
    have hcont' : ∀ r ∈ t, Continuous (fun x =>
        SuperdiffusionCLT.Section3.Setup.shellFlux omega r e x -
          volumeAverageVec (cubeSet (originCube d (Kc : ℤ)))
            (SuperdiffusionCLT.Section3.Setup.shellFlux omega r e)) :=
      fun r hr => (hcont r hr).sub continuous_const
    rw [hshellFlux_eq_smul_sum nu P omega e]
    rw [volumeAverageVec_const_smul', volumeAverageVec_cubeSet_sum_of_continuous _ t _ hcont]
    have hcen : (fun x => S⁻¹ • ∑ r ∈ t, SuperdiffusionCLT.Section3.Setup.shellFlux omega r e x -
        S⁻¹ • ∑ r ∈ t, volumeAverageVec (cubeSet (originCube d (Kc : ℤ)))
          (SuperdiffusionCLT.Section3.Setup.shellFlux omega r e)) =
        fun x => S⁻¹ • ∑ r ∈ t, (SuperdiffusionCLT.Section3.Setup.shellFlux omega r e x -
          volumeAverageVec (cubeSet (originCube d (Kc : ℤ)))
            (SuperdiffusionCLT.Section3.Setup.shellFlux omega r e)) := by
      funext x
      rw [Finset.sum_sub_distrib, smul_sub]
    rw [hcen]
    refine (vecHatNegENormOrderOne_smul_sum_le _ t _ hcont' (inv_nonneg.2 hS.le)).trans ?_
    have hZ0 : ∀ r ∈ t, 0 ≤ Zr r omega := fun r _ =>
      SuperdiffusionCLT.Section2.Estimates.Stream.shellHminusBound_nonneg r Kc e omega
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hS.le), ENNReal.ofReal_sum_of_nonneg hZ0]
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun r hr => ?_)
    exact SuperdiffusionCLT.Section2.Estimates.Stream.vecHatNegENormOrderOne_centeredShellFlux_le
      hd0 omega (hrK r hr) e


theorem isBigO_gammaSigma_const {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {c A : ℝ} (hc : 0 ≤ c) (hA : c ≤ A) :
    IsBigO mu (gammaSigma 2) (fun _ : Omega => c) A := by
  intro t ht
  have hempty : upperTailEvent (fun _ : Omega => |c|) (A * t) = ∅ := by
    ext w
    simp only [upperTailEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    rw [abs_of_nonneg hc]
    nlinarith only [hA, hc, ht]
  rw [hempty]
  simp only [MeasureTheory.measureReal_empty, gammaSigma_apply]
  positivity

theorem one_add_mul_three_pow_le_one (n : ℕ) :
    (1 + (n : ℝ)) * (3 : ℝ) ^ (-(n : ℝ)) ≤ 1 := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have h := one_add_le_two_pow n
  have h2 : (2 : ℝ) ^ n ≤ 3 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hp : (0 : ℝ) < 3 ^ n := by positivity
  rw [← div_eq_mul_inv, div_le_one hp]
  linarith only [h, h2]

/-- The average of the flux is `Γ₂`-small (the spatial-average input `e.jk.spatialavg`). -/
theorem hshellFlux_avg_isBigO [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : ℝ), 0 < nu →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P → ∀ (m h Kc : ℕ), 1 ≤ h → h ≤ m → m ≤ Kc →
      ∀ e : Vec d, vecNormSq e = 1 →
      ∃ Z : ShellSeq d → ℝ, (∀ omega, 0 ≤ Z omega) ∧ Measurable Z ∧
        IsBigO P.toMeasure (gammaSigma 2) Z
          (C * (sigmaBarInfinite nu (m - h) P)⁻¹ *
            ((1 + (((Kc - m : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - m : ℕ)) : ℝ)))) ∧
        ∀ omega, vecNorm (volumeAverageVec (cubeSet (originCube d (Kc : ℤ)))
                (hshellFlux nu P m h omega e)) ≤ Z omega := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hCav : 0 < SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d :=
    Section2.Norms.spatialAverageTailConst_pos hd0
  refine ⟨16384 * SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d * 3,
    by positivity, ?_⟩
  intro nu hnu P hPrefix hJ1 hJ2 hJ3 hJ4 m h Kc h1 hhm hmK e he
  have hJ1' : ShellLawJ1 d P := SuperdiffusionCLT.Section3.HighContrast.shellLawJ1_of_shellLawJ1Restriction hJ1
  have hS : 0 < sigmaBarInfinite nu (m - h) P :=
    sigmaBarInfinite_pos hnu (m - h) hPrefix hJ2 hJ3 hJ4
  set S := sigmaBarInfinite nu (m - h) P with hSdef
  have hen : vecNorm e = 1 := by
    have h2 := vecNorm_sq_eq_vecNormSq (d := d) e
    rw [he] at h2
    have h0 := vecNorm_nonneg e
    nlinarith only [h2, h0]
  set t : Finset ℕ := Finset.Ioc (m - h) m with htdef
  have ht : t.Nonempty := ⟨m, Finset.mem_Ioc.2 ⟨by omega, le_rfl⟩⟩
  set Zr : ℕ → ShellSeq d → ℝ := fun r omega =>
    vecNorm (SuperdiffusionCLT.Section3.Setup.shellFluxAverage (Kc : ℤ) omega r e) with hZr
  refine ⟨fun omega => S⁻¹ * ∑ r ∈ t, Zr r omega, ?_, ?_, ?_, ?_⟩
  · intro omega
    exact mul_nonneg (inv_nonneg.2 hS.le) (Finset.sum_nonneg fun r _ => vecNorm_nonneg _)
  · exact Measurable.const_mul (Finset.measurable_sum t fun r _ =>
      SuperdiffusionCLT.Section2.Estimates.Stream.measurable_vecNorm_shellFluxAverage
        (Kc : ℤ) r e) _
  · have hbig : ∀ r ∈ t, IsBigO P.toMeasure (gammaSigma 2) (Zr r)
        (SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d * vecNorm e *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * (((Kc - r : ℕ)) : ℝ))) := fun r _ =>
      SuperdiffusionCLT.Section2.Estimates.Stream.isBigO_gammaSigma_vecNorm_shellFluxAverage
        hPrefix hJ1' hJ3 hJ4 Kc r e
    have hpos : ∀ r ∈ t, 0 < SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d *
        vecNorm e * (3 : ℝ) ^ (-((d : ℝ) / 2) * (((Kc - r : ℕ)) : ℝ)) := by
      intro r _
      have h2 : (0 : ℝ) < (3 : ℝ) ^ (-((d : ℝ) / 2) * (((Kc - r : ℕ)) : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have h0 : 0 < vecNorm e := by rw [hen]; exact one_pos
      positivity
    have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_finset_sum_of_one_le
      (mu := P.toMeasure) t (by norm_num : (1 : ℝ) ≤ 2) ht hpos hbig
      (fun r _ => SuperdiffusionCLT.Section2.Estimates.Stream.measurable_vecNorm_shellFluxAverage
        (Kc : ℤ) r e)
    have hscaled := hsum.const_mul (c := S⁻¹) (inv_nonneg.2 hS.le)
    refine hscaled.mono_scale ?_
    have hterm : ∀ r ∈ t, SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d *
        vecNorm e * (3 : ℝ) ^ (-((d : ℝ) / 2) * (((Kc - r : ℕ)) : ℝ)) ≤
        SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d *
          ((1 + (((Kc - r : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - r : ℕ)) : ℝ))) := by
      intro r _
      rw [hen, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ hCav.le
      have hk : (0 : ℝ) ≤ (((Kc - r : ℕ)) : ℝ) := Nat.cast_nonneg _
      have hdd : (1 : ℝ) ≤ (d : ℝ) / 2 := by
        have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith only [this]
      have hexp : -((d : ℝ) / 2) * (((Kc - r : ℕ)) : ℝ) ≤ -(((Kc - r : ℕ)) : ℝ) := by
        nlinarith only [hdd, hk]
      have h3 : (3 : ℝ) ^ (-((d : ℝ) / 2) * (((Kc - r : ℕ)) : ℝ)) ≤
          (3 : ℝ) ^ (-(((Kc - r : ℕ)) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      have h4 : (1 : ℝ) ≤ 1 + (((Kc - r : ℕ)) : ℝ) := by linarith only [hk]
      have h5 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((Kc - r : ℕ)) : ℝ)) := by positivity
      nlinarith only [h3, h4, h5]
    have hsa := sum_shell_amplitude_le (m - h) m Kc hmK
    have hle : ∑ i ∈ t, SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d *
            vecNorm e * (3 : ℝ) ^ (-((d : ℝ) / 2) * (((Kc - i : ℕ)) : ℝ)) ≤
        SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d *
            ∑ i ∈ t, ((1 + (((Kc - i : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - i : ℕ)) : ℝ))) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
    have hcoef : 0 ≤ S⁻¹ * (16384 *
        SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d) := by
      positivity
    calc S⁻¹ * (16384 * ∑ i ∈ t, SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d *
            vecNorm e * (3 : ℝ) ^ (-((d : ℝ) / 2) * (((Kc - i : ℕ)) : ℝ)))
        ≤ S⁻¹ * (16384 * (SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d *
            ∑ i ∈ t, ((1 + (((Kc - i : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - i : ℕ)) : ℝ))))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by norm_num))
            (inv_nonneg.2 hS.le)
      _ = S⁻¹ * (16384 * SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d) *
            ∑ i ∈ t, ((1 + (((Kc - i : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - i : ℕ)) : ℝ))) := by ring
      _ ≤ S⁻¹ * (16384 * SuperdiffusionCLT.Section2.Estimates.Stream.spatialAverageTailConst d) *
            (3 * ((1 + (((Kc - m : ℕ)) : ℝ)) * (3 : ℝ) ^ (-(((Kc - m : ℕ)) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hsa hcoef
      _ = _ := by ring
  · intro omega
    have hcont : ∀ r ∈ t, Continuous (SuperdiffusionCLT.Section3.Setup.shellFlux omega r e) :=
      fun r _ => SuperdiffusionCLT.Section2.Estimates.Stream.continuous_shellFlux' omega r e
    rw [hshellFlux_eq_smul_sum nu P omega e, volumeAverageVec_const_smul',
      volumeAverageVec_cubeSet_sum_of_continuous _ t _ hcont]
    have hav : ∀ r ∈ t, volumeAverageVec (cubeSet (originCube d (Kc : ℤ)))
        (SuperdiffusionCLT.Section3.Setup.shellFlux omega r e) =
        SuperdiffusionCLT.Section3.Setup.shellFluxAverage (Kc : ℤ) omega r e :=
      fun r _ => SuperdiffusionCLT.Section3.Setup.volumeAverageVec_shellFlux _ r omega e
    rw [Finset.sum_congr rfl hav]
    show ‖HilbertVec.ofVec (S⁻¹ • ∑ r ∈ t,
      SuperdiffusionCLT.Section3.Setup.shellFluxAverage (Kc : ℤ) omega r e)‖ ≤ _
    have hsm : HilbertVec.ofVec (S⁻¹ • ∑ r ∈ t,
        SuperdiffusionCLT.Section3.Setup.shellFluxAverage (Kc : ℤ) omega r e) =
        S⁻¹ • ∑ r ∈ t, HilbertVec.ofVec
          (SuperdiffusionCLT.Section3.Setup.shellFluxAverage (Kc : ℤ) omega r e) := by
      have h1 := (HilbertVec.ofVecL d).map_smul S⁻¹ (∑ r ∈ t,
        SuperdiffusionCLT.Section3.Setup.shellFluxAverage (Kc : ℤ) omega r e)
      have h2 := map_sum (HilbertVec.ofVecL d) (fun r =>
        SuperdiffusionCLT.Section3.Setup.shellFluxAverage (Kc : ℤ) omega r e) t
      exact h1.trans (by rw [h2]; rfl)
    rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hS)]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.2 hS.le)


theorem vecNorm_neg_eq (v : Vec d) : vecNorm (-v) = vecNorm v := by
  rw [vecNorm_eq_norm_ofVec, vecNorm_eq_norm_ofVec]
  have : HilbertVec.ofVec (-v) = -HilbertVec.ofVec v := map_neg (HilbertVec.ofVecL d) v
  rw [this, norm_neg]

/-- The `L⁴` bound of the centred flux, from the `L^p` increment clause at `p = 4`. -/
theorem hshellFlux_L4_isBigO [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : ℝ), 0 < nu →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P → ∀ (m h Kc : ℕ), 1 ≤ h → h ≤ m → m ≤ Kc →
      ∀ e : Vec d, vecNormSq e = 1 →
      ∃ Z : ShellSeq d → ℝ, (∀ omega, 0 ≤ Z omega) ∧ Measurable Z ∧
        IsBigO P.toMeasure (gammaSigma 2) Z
          (C * (sigmaBarInfinite nu (m - h) P)⁻¹ * (h : ℝ) ^ ((1 : ℝ) / 2)) ∧
        ∀ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 4
            (fun x => hshellFlux nu P m h omega e x -
              volumeAverageVec (cubeSet (originCube d (Kc : ℤ)))
                (hshellFlux nu P m h omega e)) ≤ ENNReal.ofReal (Z omega) := by
  classical
  obtain ⟨Ca, hCa, hAvg⟩ := hshellFlux_avg_isBigO (d := d) hd
  obtain ⟨C₂, hV⟩ := SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d
  obtain ⟨C₀, C₁, hV2⟩ := hV (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨CL, hV3⟩ := hV2 4 (by norm_num)
  have htri : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
  set tri := gammaTriangleConst 2 with htridef
  refine ⟨tri * (tri * ((|CL| + 1) + (4 * |CL| + 1)) + Ca), by positivity, ?_⟩
  intro nu hnu P hPrefix hJ1 hJ2 hJ3 hJ4 m h Kc h1 hhm hmK e he
  have hS : 0 < sigmaBarInfinite nu (m - h) P :=
    sigmaBarInfinite_pos hnu (m - h) hPrefix hJ2 hJ3 hJ4
  set S := sigmaBarInfinite nu (m - h) P with hSdef
  have hen : vecNorm e = 1 := by
    have h2 := vecNorm_sq_eq_vecNormSq (d := d) e
    rw [he] at h2
    have h0 := vecNorm_nonneg e
    nlinarith only [h2, h0]
  obtain ⟨Za, hZa0, hZam, hZabig, hZabd⟩ := hAvg nu hnu P hPrefix hJ1 hJ2 hJ3 hJ4 m h Kc h1 hhm hmK e he
  obtain ⟨hmain, _⟩ := hV3 P hPrefix hJ1 hJ2 hJ3 hJ4
  have hlt : m - h < m := by omega
  obtain ⟨X, hXm, hXbig, hXbd⟩ := (hmain Kc m (m - h) hlt hmK).2.1
  have hmh : m - (m - h) = h := by omega
  rw [hmh] at hXbig hXbd
  set u : ℝ := (h : ℝ) ^ ((1 : ℝ) / 2) with hudef
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast h1
  have hu1 : 1 ≤ u := Real.one_le_rpow hh1 (by norm_num)
  have hCL : 0 ≤ |CL| := abs_nonneg _
  set Dl : ℕ := Kc - m with hDl
  have hW1 := one_add_mul_three_pow_le_one Dl
  have hSi : 0 < S⁻¹ := inv_pos.2 hS
  -- amplitudes
  have hb1 : IsBigO P.toMeasure (gammaSigma 2) (fun _ : ShellSeq d => S⁻¹ * (|CL| * u))
      (S⁻¹ * ((|CL| + 1) * u)) :=
    isBigO_gammaSigma_const (by positivity) (by
      refine mul_le_mul_of_nonneg_left ?_ hSi.le
      nlinarith only [hu1, hCL])
  have hXabs : IsBigO P.toMeasure (gammaSigma 2) (fun ω => S⁻¹ * |X ω|)
      (S⁻¹ * ((4 * |CL| + 1) * u)) := by
    have hX' : IsBigO P.toMeasure (gammaSigma 2) (fun ω => |X ω|) (CL * (4 : ℝ) ^ ((1 : ℝ) / 2) *
        (h : ℝ) ^ ((1 : ℝ) / 2) * (3 : ℝ) ^ (-((d : ℝ) / (2 * 4) * ((Kc - m : ℕ) : ℝ)))) := by
      have := hXbig
      simpa only [IsBigO, abs_abs] using this
    refine (hX'.const_mul (c := S⁻¹) hSi.le).mono_scale ?_
    refine mul_le_mul_of_nonneg_left ?_ hSi.le
    have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ 4 := by
      calc (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ (4 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := Real.rpow_one 4
    have h3 : (3 : ℝ) ^ (-((d : ℝ) / (2 * 4) * ((Kc - m : ℕ) : ℝ))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : 0 ≤ (d : ℝ) / (2 * 4) * ((Kc - m : ℕ) : ℝ) := by positivity
      linarith only [this]
    have h30 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((d : ℝ) / (2 * 4) * ((Kc - m : ℕ) : ℝ))) := by positivity
    have h40 : (0 : ℝ) ≤ (4 : ℝ) ^ ((1 : ℝ) / 2) := by positivity
    have hu0 : 0 ≤ u := by positivity
    calc CL * (4 : ℝ) ^ ((1 : ℝ) / 2) * u * (3 : ℝ) ^ (-((d : ℝ) / (2 * 4) * ((Kc - m : ℕ) : ℝ)))
        ≤ |CL| * (4 : ℝ) ^ ((1 : ℝ) / 2) * u * 1 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) h40) le_rfl
            hu0 (by positivity)) h3 h30 (by positivity)
      _ ≤ |CL| * 4 * u := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hCL) hu0
      _ ≤ (4 * |CL| + 1) * u := by nlinarith only [hu0]
  have hZaA : IsBigO P.toMeasure (gammaSigma 2) Za (S⁻¹ * (Ca * u)) := by
    refine hZabig.mono_scale ?_
    have hSa : 0 ≤ S⁻¹ := hSi.le
    have hW0 : (0 : ℝ) ≤ (1 + (Dl : ℝ)) * (3 : ℝ) ^ (-(Dl : ℝ)) := by positivity
    calc Ca * S⁻¹ * ((1 + (Dl : ℝ)) * (3 : ℝ) ^ (-(Dl : ℝ))) ≤ Ca * S⁻¹ * u := by
          refine mul_le_mul_of_nonneg_left (hW1.trans hu1) (by positivity)
      _ = S⁻¹ * (Ca * u) := by ring
  have hs12 := SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO (by norm_num : (0 : ℝ) < 2)
    (by positivity : 0 < S⁻¹ * ((|CL| + 1) * u)) (by positivity : 0 < S⁻¹ * ((4 * |CL| + 1) * u))
    hb1 hXabs measurable_const ((continuous_abs.measurable.comp hXm).const_mul _)
  have hs123 := SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO (by norm_num : (0 : ℝ) < 2)
    (by positivity : 0 < tri * (S⁻¹ * ((|CL| + 1) * u) + S⁻¹ * ((4 * |CL| + 1) * u)))
    (by positivity : 0 < S⁻¹ * (Ca * u)) hs12 hZaA
    (measurable_const.add ((continuous_abs.measurable.comp hXm).const_mul _)) hZam
  refine ⟨fun ω => (S⁻¹ * (|CL| * u) + S⁻¹ * |X ω|) + Za ω, ?_, ?_, ?_, ?_⟩
  · intro ω; have := hZa0 ω; positivity
  · exact (measurable_const.add ((continuous_abs.measurable.comp hXm).const_mul _)).add hZam
  · refine hs123.mono_scale (le_of_eq ?_)
    ring
  · intro ω
    have hcont : Continuous (hshellFlux nu P m h ω e) := by
      rw [hshellFlux_eq_smul_sum nu P ω e]
      exact (continuous_finsetSum _ fun r _ =>
        SuperdiffusionCLT.Section2.Estimates.Stream.continuous_shellFlux' ω r e).const_smul S⁻¹
    have hmeas1 := aestronglyMeasurable_hilbertifyVecField_of_continuous hcont
      (normalizedCubeMeasure (originCube d (Kc : ℤ)))
    have hmeas2 := aestronglyMeasurable_hilbertifyVecField_of_continuous
      (continuous_const : Continuous fun _ : Vec d =>
        -volumeAverageVec (cubeSet (originCube d (Kc : ℤ))) (hshellFlux nu P m h ω e))
      (normalizedCubeMeasure (originCube d (Kc : ℤ)))
    have hsub : (fun x => hshellFlux nu P m h ω e x -
        volumeAverageVec (cubeSet (originCube d (Kc : ℤ))) (hshellFlux nu P m h ω e)) =
        fun x => hshellFlux nu P m h ω e x +
          (-volumeAverageVec (cubeSet (originCube d (Kc : ℤ))) (hshellFlux nu P m h ω e)) := by
      funext x; rw [sub_eq_add_neg]
    rw [hsub]
    refine (vecCubeLpENorm_add_le (by norm_num) hmeas1 hmeas2).trans ?_
    rw [SuperdiffusionCLT.Section3.Setup.vecCubeLpENorm_const _ (4 : ENNReal) (by norm_num) _, vecNorm_neg_eq]
    have hF4 : vecCubeLpENorm (originCube d (Kc : ℤ)) 4 (hshellFlux nu P m h ω e) ≤
        ENNReal.ofReal (S⁻¹ * (|CL| * u) + S⁻¹ * |X ω|) := by
      have hfe : hshellFlux nu P m h ω e = fun x => S⁻¹ •
          matVecMul (SuperdiffusionCLT.Frozen.Section2.streamCutoff ω m x -
            SuperdiffusionCLT.Frozen.Section2.streamCutoff ω (m - h) x) e := rfl
      rw [hfe, vecCubeLpENorm_const_smul]
      have hst := vecCubeLpENorm_streamFlux_le (originCube d (Kc : ℤ)) 4 ω (Nat.sub_le m h) e
      have hbd := hXbd ω
      have h4 : (ENNReal.ofReal 4) = (4 : ENNReal) := by norm_num
      rw [h4] at hbd
      rw [hen, ENNReal.ofReal_one, one_mul] at hst
      have hnorm : ‖S⁻¹‖ₑ = ENNReal.ofReal S⁻¹ := by
        rw [← ofReal_norm, Real.norm_of_nonneg hSi.le]
      rw [hnorm]
      refine (mul_le_mul' le_rfl (hst.trans hbd)).trans ?_
      rw [← ENNReal.ofReal_mul hSi.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have : CL * h ^ ((1 : ℝ) / 2) + X ω ≤ |CL| * u + |X ω| := by
        rw [hudef]
        exact add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
          (le_abs_self _)
      calc S⁻¹ * (CL * h ^ ((1 : ℝ) / 2) + X ω) ≤ S⁻¹ * (|CL| * u + |X ω|) :=
            mul_le_mul_of_nonneg_left this hSi.le
        _ = _ := by ring
    have hA : ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet (originCube d (Kc : ℤ)))
        (hshellFlux nu P m h ω e))) ≤ ENNReal.ofReal (Za ω) :=
      ENNReal.ofReal_le_ofReal (hZabd ω)
    refine (add_le_add hF4 hA).trans ?_
    rw [← ENNReal.ofReal_add (by have := hZa0 ω; positivity) (hZa0 ω)]

end SuperdiffusionCLT.Section5
