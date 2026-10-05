/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldRegularity
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivLargeCubeB
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# Logarithmic growth of the gradient and the divergence of the recentred stream

For a shell law with stationarity (`ShellLawPrefix`) and `ShellLawJ3`: almost surely
`‖∇k(x)‖ ≤ C (1 + log (2 + |x|))`, hence the same bound for the divergence field
`∑_i ∂_i k_{ij}`, which is moreover continuous.

Inputs.  For the shells above the cube scale the Gaussian tail of the J3 observable at the
threshold `3^{n/2}` with Borel-Cantelli (`eventually_shellCubeDerivNorm_le_scale`); for the
shells `0, …, m` on `cu_m` the `Γ₂` large-cube envelopes (stationarity and J3), combined
by a Borel-Cantelli lemma for `Γ₂` tails at the threshold `√(m+1)`.  Borel-Cantelli needs no
measurability of the events.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section6
open scoped Matrix.Norms.Elementwise ENNReal

noncomputable section

variable {d : ℕ}

/-- **Borel-Cantelli for `Γ₂` tails.**  If `X m = O_{Γ₂}(A m)` for every `m`, then almost surely
`X m ≤ A m √(m+1)` for all large `m`.  No measurability of the variables is needed. -/
theorem fieldReg_ae_eventually_le_gamma {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} {A : ℕ → ℝ}
    (h : ∀ m : ℕ, IndependentSums.IsBigOWith μ (IndependentSums.gammaSigma 2) (X m) (A m)) :
    ∀ᵐ omega ∂μ, ∀ᶠ m in atTop, X m omega ≤ A m * Real.sqrt ((m : ℝ) + 1) := by
  have hbound : ∀ m : ℕ, μ (IndependentSums.upperTailEvent (X m) (A m * Real.sqrt ((m : ℝ) + 1))) ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
    intro m
    have h1 : 1 ≤ Real.sqrt ((m : ℝ) + 1) := by
      exact Real.one_le_sqrt.2 (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have h2 := IndependentSums.isBigOWith_gammaSigma_iff.1 (h m) h1
    have h3 : Real.sqrt ((m : ℝ) + 1) ^ (2 : ℝ) = (m : ℝ) + 1 := by
      rw [Real.rpow_two, Real.sq_sqrt (by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])]
    rw [h3] at h2
    have h4 : Real.exp (-((m : ℝ) + 1)) ≤ Real.exp (-(m : ℝ)) :=
      Real.exp_le_exp.2 (by linarith only [])
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (h2.trans h4)
  have hne : (∑' m : ℕ, μ (IndependentSums.upperTailEvent (X m)
      (A m * Real.sqrt ((m : ℝ) + 1)))) ≠ ⊤ := by
    have hle : (∑' m : ℕ, μ (IndependentSums.upperTailEvent (X m)
        (A m * Real.sqrt ((m : ℝ) + 1)))) ≤
        ENNReal.ofReal (∑' m : ℕ, Real.exp (-(m : ℝ))) :=
      calc _ ≤ ∑' m : ℕ, ENNReal.ofReal (Real.exp (-(m : ℝ))) := ENNReal.tsum_le_tsum hbound
        _ = _ := (ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.exp_nonneg _)
            Real.summable_exp_neg_nat).symm
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have hmem := MeasureTheory.ae_eventually_notMem (μ := μ)
    (s := fun m : ℕ => IndependentSums.upperTailEvent (X m)
      (A m * Real.sqrt ((m : ℝ) + 1))) hne
  filter_upwards [hmem] with omega homega
  filter_upwards [homega] with m hm
  exact le_of_not_gt hm

/-- Almost surely, the two large-cube derivative envelopes at shell scale `0` grow at most
linearly in the cube scale `m`. -/
theorem fieldReg_ae_envelope_le {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      shellDerivLargeCubeSupBound 0 m omega + shellDerivLargeCubeSumSupBound 0 m m omega ≤
        (shellDerivLargeCubeConst d + shellDerivLargeCubeSumConst d) * ((m : ℝ) + 1) := by
  have h1 := fieldReg_ae_eventually_le_gamma (μ := P.toMeasure)
    (X := fun m : ℕ => (shellDerivLargeCubeSupBound 0 m : ShellSeq d → ℝ))
    (A := fun m : ℕ => shellDerivLargeCubeConst d * ((3 : ℝ) ^ 0)⁻¹ *
      Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))))
    (fun m => isBigOWith_gammaSigma_shellDerivLargeCubeSupBound hPrefix hJ3 (Nat.zero_le m))
  have h2 := fieldReg_ae_eventually_le_gamma (μ := P.toMeasure)
    (X := fun m : ℕ => (shellDerivLargeCubeSumSupBound 0 m m : ShellSeq d → ℝ))
    (A := fun m : ℕ => shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ 0)⁻¹ *
      Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))))
    (fun m => isBigOWith_gammaSigma_shellDerivLargeCubeSumSupBound hPrefix hJ3
      (Nat.zero_le m) le_rfl)
  filter_upwards [h1, h2] with omega e1 e2
  obtain ⟨M, hM⟩ := eventually_atTop.1 (e1.and e2)
  refine ⟨M, fun m hm => ?_⟩
  obtain ⟨a1, a2⟩ := hM m hm
  have hs : Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 := by
    rw [Nat.sub_zero, add_comm (1 : ℝ), ← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
  have hs' : ∀ c : ℝ, c * ((3 : ℝ) ^ 0)⁻¹ * Real.sqrt (1 + (((m - 0 : ℕ) : ℝ))) *
      Real.sqrt ((m : ℝ) + 1) = c * ((m : ℝ) + 1) := by
    intro c
    rw [mul_assoc, mul_assoc, hs]; simp
  simp only [hs'] at a1 a2
  linarith only [a1, a2]

/-- The sum of the shells `0, …, m` at a point of `cu_m` is controlled by the two envelopes. -/
theorem fieldReg_norm_partial_deriv_le (omega : ShellSeq d) (m : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (m : ℤ))) :
    ‖∑ k ∈ Finset.range (m + 1), ShellField.deriv (omega k) x‖ ≤
      Real.sqrt d * (shellDerivLargeCubeSupBound 0 m omega +
        shellDerivLargeCubeSumSupBound 0 m m omega) := by
  have hsplit : ∑ k ∈ Finset.range (m + 1), ShellField.deriv (omega k) x =
      ShellField.deriv (omega 0) x + ∑ k ∈ Finset.Ioc 0 m, ShellField.deriv (omega k) x := by
    have hI : Finset.Ioc 0 m = Finset.Ico 1 (m + 1) := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [Finset.range_eq_Ico, hI, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have h1 := matrixDerivativeNorm_deriv_le_shellDerivLargeCubeSupBound_open omega
    (Nat.zero_le m) hx
  have h2 := matrixDerivativeNorm_le_shellDerivLargeCubeSumSupBound omega (a := 0) (b := m)
    le_rfl (openCubeSet_subset_cubeSet _ hx)
  have h3 := ShellField.matrixDerivativeNorm_add_le (ShellField.deriv (omega 0) x)
    (∑ k ∈ Finset.Ioc 0 m, ShellField.deriv (omega k) x)
  rw [hsplit]
  refine (fieldReg_norm_le_sqrt_mul_mdn _).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith only [h1, h2, h3]) (Real.sqrt_nonneg _)

/-- The shells above the cube scale: each is controlled by its own cube norm. -/
theorem fieldReg_norm_tail_deriv_le (omega : ShellSeq d) (m : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (m : ℤ)))
    (hscale : ∀ k : ℕ, m + 1 ≤ k →
      ShellField.shellCubeDerivNorm k (omega k) ≤ shellDerivTailScale ^ k) :
    ‖∑' i : ℕ, ShellField.deriv (omega (i + (m + 1))) x‖ ≤
      Real.sqrt d * (1 - shellDerivTailScale)⁻¹ := by
  have hgeo : HasSum (fun i : ℕ => shellDerivTailScale ^ i) (1 - shellDerivTailScale)⁻¹ :=
    hasSum_geometric_of_lt_one shellDerivTailScale_nonneg shellDerivTailScale_lt_one
  have hterm : ∀ i : ℕ, ‖ShellField.deriv (omega (i + (m + 1))) x‖ ≤
      Real.sqrt d * shellDerivTailScale ^ i := by
    intro i
    have hxk : x ∈ openCubeSet (originCube d ((i + (m + 1) : ℕ) : ℤ)) :=
      openCubeSet_originCube_subset (by omega) hx
    have h1 := (fieldReg_norm_le_sqrt_mul_mdn (ShellField.deriv (omega (i + (m + 1))) x)).trans
      (mul_le_mul_of_nonneg_left
        (ShellField.matrixDerivativeNorm_deriv_le_shellCubeDerivNorm _ _ hxk) (Real.sqrt_nonneg _))
    have h2 := hscale (i + (m + 1)) (by omega)
    have h3 : shellDerivTailScale ^ (i + (m + 1)) ≤ shellDerivTailScale ^ i := by
      rw [pow_add]
      exact mul_le_of_le_one_right (pow_nonneg shellDerivTailScale_nonneg i)
        (pow_le_one₀ shellDerivTailScale_nonneg shellDerivTailScale_lt_one.le)
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h3) (Real.sqrt_nonneg _))
  have h := tsum_of_norm_bounded (hgeo.mul_left (Real.sqrt d)) hterm
  exact h

/-- **The cube bound.**  On `cu_m`, the gradient is bounded by `√d` times the envelope plus the
geometric remainder, once the derivative series is summable on `cu_m` and the cube norms of the
shells above `m` obey the scale `3^{-k/2}`. -/
theorem fieldReg_norm_fullStreamDeriv_le_cube (omega : ShellSeq d) (m : ℕ)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k))
    (hscale : ∀ k : ℕ, m + 1 ≤ k →
      ShellField.shellCubeDerivNorm k (omega k) ≤ shellDerivTailScale ^ k)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (m : ℤ))) :
    ‖fullStreamDeriv omega x‖ ≤
      Real.sqrt d * (shellDerivLargeCubeSupBound 0 m omega +
        shellDerivLargeCubeSumSupBound 0 m m omega) +
        Real.sqrt d * (1 - shellDerivTailScale)⁻¹ := by
  have hsx : Summable fun n : ℕ => ShellField.deriv (omega n) x :=
    Summable.of_norm_bounded ((hsum).mul_left (Real.sqrt d))
      fun n => norm_shellDeriv_le_originCube omega n m hx
  have h := hsx.sum_add_tsum_nat_add (m + 1)
  have hfs : fullStreamDeriv omega x = ∑' n : ℕ, ShellField.deriv (omega n) x := rfl
  rw [hfs, ← h]
  exact (norm_add_le _ _).trans (add_le_add (fieldReg_norm_partial_deriv_le omega m hx)
    (fieldReg_norm_tail_deriv_le omega m hx hscale))

/-- **Almost-sure growth of the gradient by cube scale.**  There is a random `C` with
`‖∇k(x)‖ ≤ C (m + 1)` for every `x` in the natural open cube `cu_m` and every `m`.  The tail
of J3 used is the Gaussian tail of the observable at `3^{n/2}` (the series beyond the cube
scale), and the stationarity-based `Γ₂` envelope of the shells below the cube scale. -/
theorem fieldReg_ae_cube_growth {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      ∀ x ∈ openCubeSet (originCube d (m : ℤ)),
        ‖fullStreamDeriv omega x‖ ≤ C * ((m : ℝ) + 1) := by
  filter_upwards [fieldReg_ae_envelope_le hPrefix hJ3, eventually_shellCubeDerivNorm_le_scale hJ3,
    ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega hY hev hg
  obtain ⟨M, hM⟩ := hY
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hc1 : 0 ≤ shellDerivLargeCubeConst d := (one_le_shellDerivLargeCubeConst d).trans' zero_le_one
  have hc2 : 0 ≤ shellDerivLargeCubeSumConst d := (shellDerivLargeCubeSumConst_pos hPrefix).le
  have hinv : 0 ≤ (1 - shellDerivTailScale)⁻¹ :=
    inv_nonneg.2 (by linarith only [shellDerivTailScale_lt_one])
  set c : ℝ := Real.sqrt d * (shellDerivLargeCubeConst d + shellDerivLargeCubeSumConst d) +
    Real.sqrt d * (1 - shellDerivTailScale)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hcube : ∀ m : ℕ, max M N ≤ m → ∀ x ∈ openCubeSet (originCube d (m : ℤ)),
      ‖fullStreamDeriv omega x‖ ≤ c * ((m : ℝ) + 1) := by
    intro m hm x hx
    have h1 := fieldReg_norm_fullStreamDeriv_le_cube omega m (hg m)
      (fun k hk => hN k ((le_max_right M N).trans (hm.trans (by omega)))) hx
    have h2 := hM m ((le_max_left M N).trans hm)
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hr : 0 ≤ Real.sqrt d * (1 - shellDerivTailScale)⁻¹ := by positivity
    have h3 : Real.sqrt d * (shellDerivLargeCubeSupBound 0 m omega +
        shellDerivLargeCubeSumSupBound 0 m m omega) ≤
        Real.sqrt d * ((shellDerivLargeCubeConst d + shellDerivLargeCubeSumConst d) *
          ((m : ℝ) + 1)) := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    have h4 : Real.sqrt d * (1 - shellDerivTailScale)⁻¹ ≤
        Real.sqrt d * (1 - shellDerivTailScale)⁻¹ * ((m : ℝ) + 1) :=
      le_mul_of_one_le_right hr hm1
    calc ‖fullStreamDeriv omega x‖ ≤ _ := h1
      _ ≤ Real.sqrt d * ((shellDerivLargeCubeConst d + shellDerivLargeCubeSumConst d) *
          ((m : ℝ) + 1)) + Real.sqrt d * (1 - shellDerivTailScale)⁻¹ * ((m : ℝ) + 1) := by
          linarith only [h3, h4]
      _ = c * ((m : ℝ) + 1) := by rw [hc]; ring
  refine ⟨c * ((max M N : ℕ) + 1 : ℝ), by positivity, fun m x hx => ?_⟩
  have hM1 : (1 : ℝ) ≤ ((max M N : ℕ) : ℝ) + 1 := by
    linarith only [(Nat.cast_nonneg (max M N) : (0 : ℝ) ≤ ((max M N : ℕ) : ℝ))]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith only [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rcases le_total (max M N) m with hm | hm
  · refine (hcube m hm x hx).trans ?_
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc0 hM1) (by linarith only [hm1])
  · have hx' : x ∈ openCubeSet (originCube d ((max M N : ℕ) : ℤ)) :=
      openCubeSet_originCube_subset hm hx
    refine (hcube (max M N) le_rfl x hx').trans ?_
    exact le_mul_of_one_le_right (by positivity) hm1

/-- Every point lies in a natural cube whose index is logarithmic in the point. -/
theorem fieldReg_exists_cube_log (x : Vec d) :
    ∃ m : ℕ, x ∈ openCubeSet (originCube d (m : ℤ)) ∧
      (m : ℝ) + 1 ≤ 3 * (1 + Real.log (2 + ‖x‖)) := by
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hpos : 0 < 2 * ‖x‖ + 1 := by linarith only [hx0]
  set y : ℝ := Real.logb 3 (2 * ‖x‖ + 1) with hy
  have hy0 : 0 ≤ y := Real.logb_nonneg (by norm_num) (by linarith only [hx0])
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith only [this]
  refine ⟨⌊y⌋₊ + 1, ?_, ?_⟩
  · have h1 : y < ((⌊y⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one y
    have h2 : (3 : ℝ) ^ y < (3 : ℝ) ^ (((⌊y⌋₊ + 1 : ℕ) : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
    rw [hy, Real.rpow_logb (by norm_num) (by norm_num) hpos, Real.rpow_natCast] at h2
    rw [mem_openCubeSet_originCube_iff]
    intro j
    have hxj : |x j| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
    rw [zpow_natCast]
    rw [abs_le] at hxj
    constructor <;> linarith only [hxj.1, hxj.2, h2, hx0]
  · have hL0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith only [hx0])
    have hfl : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ y + 1 := by
      push_cast; linarith only [Nat.floor_le hy0]
    have hyl : y ≤ Real.log (2 * ‖x‖ + 1) := by
      rw [hy, Real.logb]
      exact div_le_self (Real.log_nonneg (by linarith only [hx0])) hlog3.le
    have hlog2 : Real.log (2 * ‖x‖ + 1) ≤ 1 + Real.log (2 + ‖x‖) := by
      have h1 : Real.log (2 * ‖x‖ + 1) ≤ Real.log (2 * (2 + ‖x‖)) :=
        Real.log_le_log hpos (by linarith only [hx0])
      rw [Real.log_mul (by norm_num) (by linarith only [hx0])] at h1
      have := Real.log_two_lt_d9
      norm_num at this
      linarith only [h1, this]
    push_cast at hfl ⊢
    linarith only [hfl, hyl, hlog2, hL0]

/-- **Logarithmic growth of the gradient of the recentred stream.**  Almost surely there is `C`
with `‖∇k(x)‖ ≤ C (1 + log (2 + |x|))` for all `x`. -/
theorem fieldReg_ae_log_growth_fullStreamDeriv {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d,
      ‖fullStreamDeriv omega x‖ ≤ C * (1 + Real.log (2 + ‖x‖)) := by
  filter_upwards [fieldReg_ae_cube_growth hPrefix hJ3] with omega ⟨C, hC0, hC⟩
  refine ⟨3 * C, by positivity, fun x => ?_⟩
  obtain ⟨m, hm, hm'⟩ := fieldReg_exists_cube_log x
  calc ‖fullStreamDeriv omega x‖ ≤ C * ((m : ℝ) + 1) := hC m x hm
    _ ≤ C * (3 * (1 + Real.log (2 + ‖x‖))) := mul_le_mul_of_nonneg_left hm' hC0
    _ = 3 * C * (1 + Real.log (2 + ‖x‖)) := by ring

/-! ## The divergence of the recentred stream -/

/-- The divergence field `(∇·k)_j = ∑_i ∂_i k_{ij}`, read off the gradient `fullStreamDeriv`. -/
def fieldReg_divergence (omega : ShellSeq d) (x : Vec d) (j : Fin d) : ℝ :=
  ∑ i : Fin d, fullStreamDeriv omega x (Pi.single i 1) i j

theorem fieldReg_abs_divergence_le (omega : ShellSeq d) (x : Vec d) (j : Fin d) :
    |fieldReg_divergence omega x j| ≤ (d : ℝ) * ‖fullStreamDeriv omega x‖ := by
  have hterm : ∀ i : Fin d, |fullStreamDeriv omega x (Pi.single i 1) i j| ≤
      ‖fullStreamDeriv omega x‖ := by
    intro i
    have h1 := (Matrix.norm_entry_le_entrywise_sup_norm _ :
      ‖(fullStreamDeriv omega x (Pi.single i 1)) i j‖ ≤ ‖fullStreamDeriv omega x (Pi.single i 1)‖)
    have h2 : ‖fullStreamDeriv omega x (Pi.single i 1)‖ ≤
        ‖fullStreamDeriv omega x‖ * ‖(Pi.single i 1 : Vec d)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h3 : ‖(Pi.single i 1 : Vec d)‖ = 1 := by
      rw [Pi.norm_single]; simp
    rw [h3, mul_one] at h2
    simpa only [Real.norm_eq_abs] using h1.trans h2
  calc |fieldReg_divergence omega x j| ≤ ∑ i : Fin d, |fullStreamDeriv omega x (Pi.single i 1) i j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖fullStreamDeriv omega x‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) * ‖fullStreamDeriv omega x‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Growth of the divergence of the recentred stream.**  Almost surely, `∇·k` is continuous
(in particular locally bounded) and `|(∇·k)_j(x)| ≤ C (1 + log (2 + |x|))`. -/
theorem fieldReg_ae_log_growth_divergence {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      (∀ j : Fin d, Continuous fun x : Vec d => fieldReg_divergence omega x j) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (j : Fin d),
        |fieldReg_divergence omega x j| ≤ C * (1 + Real.log (2 + ‖x‖)) := by
  filter_upwards [fieldReg_ae_log_growth_fullStreamDeriv hPrefix hJ3,
    ae_continuous_fullStreamDeriv hJ3] with omega ⟨C, hC0, hC⟩ hcont
  refine ⟨fun j => ?_, (d : ℝ) * C, by positivity, fun x j => ?_⟩
  · refine continuous_finsetSum _ fun i _ => ?_
    have h1 : Continuous fun x : Vec d => fullStreamDeriv omega x (Pi.single i 1) :=
      (ContinuousLinearMap.apply ℝ (Mat d) (Pi.single i 1 : Vec d)).continuous.comp hcont
    exact (continuous_apply j).comp ((continuous_apply i).comp h1)
  · refine (fieldReg_abs_divergence_le omega x j).trans ?_
    calc (d : ℝ) * ‖fullStreamDeriv omega x‖ ≤ (d : ℝ) * (C * (1 + Real.log (2 + ‖x‖))) :=
          mul_le_mul_of_nonneg_left (hC x) (Nat.cast_nonneg d)
      _ = (d : ℝ) * C * (1 + Real.log (2 + ‖x‖)) := by ring

/-! ## Satisfiability witnesses -/

example (hd : 2 ≤ d) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d,
        ‖fullStreamDeriv omega x‖ ≤ C * (1 + Real.log (2 + ‖x‖)) :=
  fieldReg_ae_log_growth_fullStreamDeriv
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw

example (hd : 2 ≤ d) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      (∀ j : Fin d, Continuous fun x : Vec d => fieldReg_divergence omega x j) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (j : Fin d),
        |fieldReg_divergence omega x j| ≤ C * (1 + Real.log (2 + ‖x‖)) :=
  fieldReg_ae_log_growth_divergence
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw

end

end SuperdiffusionCLT.Section8
