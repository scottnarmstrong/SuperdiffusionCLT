/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.RecursionLinearWeakNorm

/-!
# The weighted Step 3 recursion, part 1: constants and real-variable lemmas

The weighted recursion (`Step3/RecursionWC.lean`) keeps the weighted sums of C6's general form
`akhcPrime_expected_energy_le` (`WeakNorms/PrimeD.lean`) with a fixed base scale `k`, instead of
collapsing them into one window drop. This file holds

* the explicit constants: `akhcRW_Benergy` (the energy coefficient, read off from the
  coefficients of `akhcPrime_expected_energy_le`, of the per-scale drop bound
  `akhcPrime_tau_le`, of the per-scale variance bound `akhcVA_variance_again_prime` and of the
  constant tail `akhcPrime_constTail_le`), `akhcRW_Bw` (the recursion coefficient) and
  `akhcRW_UpsPort` (the `ω²` coefficient: the variance constant at `p_Ψ := η` plus the
  second-moment constant of `M⁺` from `akhcMM_Mplus_secondMoment_le`);
* the monotonicity of `n ↦ n - ℓ(n)` above `L₁` (`akhcRW_sub_lag_mono`);
* the reindexing of the integer-indexed weighted sums (`akhcRW_sum_Icc_int`);
* the pure real assembly (`akhcRW_assembly`).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

noncomputable section

/-! ## The constants -/

/-- The geometric weight bound `G_w := (1 - 3^{-(1/2 - s')})⁻¹ ≥ Σ_{n ≤ m} 3^{-(1/2-s')(m-n)}`. -/
noncomputable def akhcRW_Gs (s' : ℝ) : ℝ :=
  (1 - Real.rpow (3 : ℝ) (-(1 / 2 - s')))⁻¹

/-- The energy coefficient. With `C` the maximizer constant, `c_K` the port's maximizer
constant, `G_w` the weight bound, `A := 512 d²` (the quadratic coefficient of
`akhcProtoD_variance_quadratic`) and `U := (1/2 - s')⁻²` (the low-scale tail factor):
`4 G_w (A + G_w) + 8 C² c_K G_w (2 + G_w/2 + 2(A + G_w) + 2 G_w (A + 1)) + 160 C² c_K U + 16 C²`. -/
noncomputable def akhcRW_Benergy (d : ℕ) (s' rho : ℝ) : ℝ :=
  4 * akhcRW_Gs s' * (512 * (d : ℝ) ^ 2 + akhcRW_Gs s') +
    8 * Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
        SuperdiffusionCLT.AKHC61.WeakNorms.akhcWeakC2_maximizerConst s' rho *
        akhcRW_Gs s' *
      (2 + akhcRW_Gs s' / 2 + 2 * (512 * (d : ℝ) ^ 2 + akhcRW_Gs s') +
        2 * akhcRW_Gs s' * (512 * (d : ℝ) ^ 2 + 1)) +
    160 * Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
        SuperdiffusionCLT.AKHC61.WeakNorms.akhcWeakC2_maximizerConst s' rho *
        ((1 / 2 - s')⁻¹) ^ 2 +
    16 * Homogenization.Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2

/-- The weighted recursion's coefficient `B_w := (linConst/2 + prodConst) · 16 · Benergy`. -/
noncomputable def akhcRW_Bw (d : ℕ) [NeZero d] (s' rho : ℝ) : ℝ :=
  (SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d / 2 +
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d) *
    (16 * akhcRW_Benergy d s' rho)

/-- The variance part of the `ω²` coefficient: `akhcVA_variance_again_prime` at `p_Ψ := η`,
with `Θ_{n-ℓ(n)}² ≤ 4`: `32 · 4 · (2d)² (η/(η-2)) K_Ψ^{3⌈η⌉²}`. -/
noncomputable def akhcRW_UpsVar (d : ℕ) (eta KPsi : ℝ) : ℝ :=
  128 * ((2 * (d : ℝ)) ^ 2 * ((eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2)))

/-- The `M⁺` part of the `ω²` coefficient (`akhcMM_Mplus_secondMoment_le`):
`(η/(η-2)) K_Ψ^{3⌈η⌉²} K_Ψ^{6⌈η⌉²/η} (1 - 3^{-(2ρ - 2d/η)})⁻¹`. -/
noncomputable def akhcRW_UpsMM (d : ℕ) (eta rho KPsi : ℝ) : ℝ :=
  (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) * KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) *
    (1 - (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)))⁻¹

/-- The full `ω²` coefficient `Υ^{port} := UpsVar + UpsMM`. -/
noncomputable def akhcRW_UpsPort (d : ℕ) (eta rho KPsi : ℝ) : ℝ :=
  akhcRW_UpsVar d eta KPsi + akhcRW_UpsMM d eta rho KPsi

theorem akhcRW_Gs_nonneg {s' : ℝ} (hhi : s' < 1 / 2) : 0 ≤ akhcRW_Gs s' := by
  unfold akhcRW_Gs
  have h : Real.rpow (3 : ℝ) (-(1 / 2 - s')) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hhi])
  exact inv_nonneg.2 (by linarith only [h])

theorem akhcRW_UpsVar_nonneg (d : ℕ) {eta KPsi : ℝ} (heta2 : 2 < eta) (hKPsi : 1 ≤ KPsi) :
    0 ≤ akhcRW_UpsVar d eta KPsi := by
  unfold akhcRW_UpsVar
  have h1 : 0 ≤ eta / (eta - 2) := div_nonneg (by linarith only [heta2]) (by linarith only [heta2])
  have h2 : 0 ≤ KPsi ^ (3 * ⌈eta⌉₊ ^ 2) := pow_nonneg (by linarith only [hKPsi]) _
  positivity

theorem akhcRW_UpsMM_nonneg (d : ℕ) {eta rho KPsi : ℝ} (heta2 : 2 < eta) (hKPsi : 1 ≤ KPsi)
    (hc : 0 < 2 * rho - 2 * (d : ℝ) / eta) : 0 ≤ akhcRW_UpsMM d eta rho KPsi := by
  unfold akhcRW_UpsMM
  have h1 : 0 ≤ eta / (eta - 2) := div_nonneg (by linarith only [heta2]) (by linarith only [heta2])
  have hK0 : 0 ≤ KPsi := by linarith only [hKPsi]
  have h2 : 0 ≤ KPsi ^ (3 * ⌈eta⌉₊ ^ 2) := pow_nonneg hK0 _
  have h3 : 0 ≤ KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) := Real.rpow_nonneg hK0 _
  have h4 : (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hc])
  have h5 : 0 ≤ (1 - (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)))⁻¹ :=
    inv_nonneg.2 (by linarith only [h4])
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h5

/-! ## The lag `ℓ(n) = ⌈L₁ log(L₂ n)⌉` grows by at most one per scale above `L₁` -/

/-- **`n ↦ n - ℓ(n)` is monotone on `[L₁, ∞)`.** For `L₁ ≤ k ≤ n`,
`ℓ(n) ≤ ℓ(k) + ⌈L₁ log(n/k)⌉ ≤ ℓ(k) + (n - k)`, since `L₁ log(n/k) ≤ L₁ (n-k)/k ≤ n - k`. -/
theorem akhcRW_sub_lag_mono {L1 L2 : ℝ} (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) {k n : ℕ}
    (hkL1 : L1 ≤ (k : ℝ)) (hkn : k ≤ n) :
    k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k ≤
      n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith only [hL1, hkL1]
  have hkn' : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hkn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hk0 hkn'
  have hL20 : (0 : ℝ) < L2 := by linarith only [hL2]
  have hlog : Real.log (L2 * (n : ℝ)) =
      Real.log (L2 * (k : ℝ)) + Real.log ((n : ℝ) / (k : ℝ)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hlogle : Real.log ((n : ℝ) / (k : ℝ)) ≤ (n : ℝ) / (k : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hL10 : (0 : ℝ) ≤ L1 := by linarith only [hL1]
  have hdiv : L1 / (k : ℝ) ≤ 1 := (div_le_one hk0).2 hkL1
  have hsub0 : (0 : ℝ) ≤ (n : ℝ) - (k : ℝ) := by linarith only [hkn']
  have hstep : L1 * Real.log ((n : ℝ) / (k : ℝ)) ≤ (n : ℝ) - (k : ℝ) := by
    have h1 : L1 * Real.log ((n : ℝ) / (k : ℝ)) ≤ L1 * ((n : ℝ) / (k : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hlogle hL10
    have h2 : L1 * ((n : ℝ) / (k : ℝ) - 1) = L1 / (k : ℝ) * ((n : ℝ) - (k : ℝ)) := by
      field_simp
    have h3 : L1 / (k : ℝ) * ((n : ℝ) - (k : ℝ)) ≤ (n : ℝ) - (k : ℝ) :=
      mul_le_of_le_one_left hsub0 hdiv
    linarith only [h1, h2, h3]
  have hceilk : L1 * Real.log (L2 * (k : ℝ)) ≤
      (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k : ℝ) :=
    Nat.le_ceil _
  have hlagn : SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n ≤
      SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k + (n - k) := by
    unfold SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag
    refine Nat.ceil_le.2 ?_
    have hcast : (((⌈L1 * Real.log (L2 * (k : ℝ))⌉₊ + (n - k) : ℕ)) : ℝ) =
        (⌈L1 * Real.log (L2 * (k : ℝ))⌉₊ : ℝ) + ((n : ℝ) - (k : ℝ)) := by
      rw [Nat.cast_add, Nat.cast_sub hkn]
    rw [hcast, hlog, mul_add]
    have hceilk' : L1 * Real.log (L2 * (k : ℝ)) ≤ (⌈L1 * Real.log (L2 * (k : ℝ))⌉₊ : ℝ) :=
      Nat.le_ceil _
    linarith only [hceilk', hstep]
  omega

/-! ## Reindexing the integer-indexed sums -/

/-- `Σ_{n ∈ (k, m] ⊂ ℤ} f(n.toNat) = Σ_{n ∈ (k, m] ⊂ ℕ} f n`. -/
theorem akhcRW_sum_Icc_int (k m : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ), f (Int.toNat n) =
      ∑ n ∈ Finset.Icc (k + 1) m, f n := by
  refine Finset.sum_nbij' (fun n => Int.toNat n) (fun n => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    have h := Finset.mem_Icc.1 hn
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩ <;> omega
  · intro n hn
    have h := Finset.mem_Icc.1 hn
    refine Finset.mem_Icc.2 ⟨?_, ?_⟩ <;> omega
  · intro n hn
    have h := Finset.mem_Icc.1 hn
    show ((Int.toNat n : ℕ) : ℤ) = n
    omega
  · intro n _
    simp
  · intro n _
    rfl

/-- On `(k, m]`, the mismatch weight is the real power `3^{-(1/2-s')(m-n)}`. -/
theorem akhcRW_w_eq (s' : ℝ) {k m : ℕ} {n : ℤ} (hn : n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ)) :
    SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_w (1 / 2) s' (m : ℤ) n =
      (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - ((Int.toNat n : ℕ) : ℝ))) := by
  have h := Finset.mem_Icc.1 hn
  unfold SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_w
  have hle : Int.toNat n ≤ m := by omega
  have hcast : ((Int.toNat ((m : ℤ) - n) : ℕ) : ℝ) = (m : ℝ) - ((Int.toNat n : ℕ) : ℝ) := by
    have : Int.toNat ((m : ℤ) - n) = m - Int.toNat n := by omega
    rw [this, Nat.cast_sub hle]
  rw [hcast]
  rfl

/-- A weighted integer-indexed sum is the real-power-weighted natural-indexed sum. -/
theorem akhcRW_wsum_eq (s' : ℝ) (k m : ℕ) (g : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_w (1 / 2) s' (m : ℤ) n * g (Int.toNat n) =
      ∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) * g n := by
  rw [← akhcRW_sum_Icc_int k m
    (fun nn => (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (nn : ℝ))) * g nn)]
  exact Finset.sum_congr rfl fun n hn => by rw [akhcRW_w_eq s' hn]

/-- The weighted sum of `A g + U` splits as `A Σ w g + S_w U`. -/
theorem akhcRW_wsum_split (s' : ℝ) (k m : ℕ) (g : ℕ → ℝ) (A U : ℝ) :
    ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_w (1 / 2) s' (m : ℤ) n *
          (A * g (Int.toNat n) + U) =
      A * ∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) * g n +
        SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_wSum (1 / 2) s' (m : ℤ) (k : ℤ) * U := by
  rw [← akhcRW_wsum_eq s' k m g]
  unfold SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_wSum
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-! ## The pure real assembly -/

/-- **The weighted assembly, pure real form.** The right-hand side of
`akhcPrime_expected_energy_le` at `ε = 1`, under the per-piece bounds, is at most
`16 · Benergy · S`. Here `X` and `Y` are the weighted and the top-scale variance budgets,
`SD` the weighted drop sum, `M` the `M⁺` budget, `T = 3^{-(1-2s')(m-k)}` the low-scale tail,
and `S` any common majorant. -/
theorem akhcRW_assembly {IA ID IF IG θ Sw κ Bj U2 CT C cK Gs A Uc T SD Mm X Y S : ℝ}
    (hS0 : 0 ≤ S) (hA : 0 ≤ A) (hcK : 0 ≤ cK) (hUc : 0 ≤ Uc)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hX : X ≤ (A + Gs) * S) (hY : Y ≤ (A + 1) * S)
    (hSD : SD ≤ S) (hMmS : Mm ≤ S) (hTS : T ≤ S) (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (hIA : IA ≤ Gs * (4 * X)) (hID : ID ≤ 2 * SD) (hIG0 : 0 ≤ IG) (hIG : IG ≤ Mm)
    (hIF : IF ≤ X + Gs * Y) (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 8 * cK) (hSw0 : 0 ≤ Sw) (hSw : Sw ≤ Gs)
    (hBj0 : 0 ≤ Bj) (hBj : Bj ≤ 5) (hU2 : U2 = Uc * T) (hCT : CT ≤ 16 * T) :
    16 * (IA + C ^ 2 * κ * Sw * (ID + 1 / 2 * Sw * IG + θ / 1 * IF) +
        C ^ 2 * U2 * κ * (Bj * (2 * (1 + IG))) + C ^ 2 * CT) ≤
      16 * (4 * Gs * (A + Gs) +
          8 * C ^ 2 * cK * Gs * (2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) +
          160 * C ^ 2 * cK * Uc + 16 * C ^ 2) * S := by
  have hGs0 : 0 ≤ Gs := hSw0.trans hSw
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have hMm0 : 0 ≤ Mm := hIG0.trans hIG
  -- (i) the node-16 piece
  have h1 : IA ≤ 4 * Gs * (A + Gs) * S := by
    have := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ Gs * 4)
    calc IA ≤ Gs * (4 * X) := hIA
      _ = Gs * 4 * X := by ring
      _ ≤ Gs * 4 * ((A + Gs) * S) := this
      _ = 4 * Gs * (A + Gs) * S := by ring
  -- (ii) the mismatch piece
  have hinner : ID + 1 / 2 * Sw * IG + θ / 1 * IF ≤
      (2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) * S := by
    have a1 : Sw * IG ≤ Gs * Mm := mul_le_mul hSw hIG hIG0 hGs0
    have a2 : Gs * Mm ≤ Gs * S := mul_le_mul_of_nonneg_left hMmS hGs0
    have a3 : θ * IF ≤ θ * (X + Gs * Y) := mul_le_mul_of_nonneg_left hIF hθ0
    have a4 : θ * (X + Gs * Y) ≤ 2 * (X + Gs * Y) :=
      mul_le_mul_of_nonneg_right hθ2 (by positivity)
    have a5 : Gs * Y ≤ Gs * ((A + 1) * S) := mul_le_mul_of_nonneg_left hY hGs0
    have hdiv : θ / 1 * IF = θ * IF := by rw [div_one]
    have e : (2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) * S =
        2 * S + 1 / 2 * (Gs * S) + 2 * ((A + Gs) * S + Gs * ((A + 1) * S)) := by ring
    have e2 : 1 / 2 * Sw * IG = 1 / 2 * (Sw * IG) := by ring
    rw [e, hdiv, e2]
    linarith only [hID, hSD, a1, a2, a3, a4, a5, hX]
  have hinner0 : 0 ≤ (2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) * S := by positivity
  have hκSw : κ * Sw ≤ 8 * cK * Gs := mul_le_mul hκ hSw hSw0 (by positivity)
  have h2 : C ^ 2 * κ * Sw * (ID + 1 / 2 * Sw * IG + θ / 1 * IF) ≤
      8 * C ^ 2 * cK * Gs * (2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) * S := by
    have b1 := mul_le_mul_of_nonneg_left hinner (by positivity : (0 : ℝ) ≤ C ^ 2 * κ * Sw)
    have b2 : C ^ 2 * (κ * Sw) ≤ C ^ 2 * (8 * cK * Gs) := mul_le_mul_of_nonneg_left hκSw hC2
    have b3 := mul_le_mul_of_nonneg_right b2 hinner0
    calc C ^ 2 * κ * Sw * (ID + 1 / 2 * Sw * IG + θ / 1 * IF)
        ≤ C ^ 2 * κ * Sw * ((2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) * S) := b1
      _ = C ^ 2 * (κ * Sw) * ((2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) * S) := by ring
      _ ≤ C ^ 2 * (8 * cK * Gs) * ((2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) * S) := b3
      _ = _ := by ring
  -- (iii) the low-scale tail
  have h3 : C ^ 2 * U2 * κ * (Bj * (2 * (1 + IG))) ≤ 160 * C ^ 2 * cK * Uc * S := by
    have c1 : Bj * (2 * (1 + IG)) ≤ 5 * (2 * (1 + Mm)) :=
      mul_le_mul hBj (by linarith only [hIG]) (by linarith only [hIG0]) (by norm_num)
    have c0 : 0 ≤ Bj * (2 * (1 + IG)) := mul_nonneg hBj0 (by linarith only [hIG0])
    have c2 : κ * (Bj * (2 * (1 + IG))) ≤ 8 * cK * (5 * (2 * (1 + Mm))) :=
      mul_le_mul hκ c1 c0 (by positivity)
    have c3 : T * (1 + Mm) ≤ 2 * S := by
      have : T * Mm ≤ 1 * Mm := mul_le_mul_of_nonneg_right hT1 hMm0
      linarith only [this, hTS, hMmS]
    have c4 : U2 * (κ * (Bj * (2 * (1 + IG)))) ≤ Uc * T * (8 * cK * (5 * (2 * (1 + Mm)))) := by
      rw [hU2]
      exact mul_le_mul_of_nonneg_left c2 (mul_nonneg hUc hT0)
    have c5 : Uc * T * (8 * cK * (5 * (2 * (1 + Mm)))) = 80 * (Uc * cK) * (T * (1 + Mm)) := by
      ring
    have c6 : 80 * (Uc * cK) * (T * (1 + Mm)) ≤ 80 * (Uc * cK) * (2 * S) :=
      mul_le_mul_of_nonneg_left c3 (by positivity)
    have c7 : U2 * (κ * (Bj * (2 * (1 + IG)))) ≤ 160 * cK * Uc * S := by
      have := c4.trans (c5 ▸ c6)
      linarith only [this]
    have c8 := mul_le_mul_of_nonneg_left c7 hC2
    calc C ^ 2 * U2 * κ * (Bj * (2 * (1 + IG))) = C ^ 2 * (U2 * (κ * (Bj * (2 * (1 + IG))))) := by
          ring
      _ ≤ C ^ 2 * (160 * cK * Uc * S) := c8
      _ = 160 * C ^ 2 * cK * Uc * S := by ring
  -- (iv) the constant tail
  have h4 : C ^ 2 * CT ≤ 16 * C ^ 2 * S := by
    have d1 : CT ≤ 16 * S := by linarith only [hCT, hTS]
    have := mul_le_mul_of_nonneg_left d1 hC2
    linarith only [this]
  have hsum : IA + C ^ 2 * κ * Sw * (ID + 1 / 2 * Sw * IG + θ / 1 * IF) +
      C ^ 2 * U2 * κ * (Bj * (2 * (1 + IG))) + C ^ 2 * CT ≤
      (4 * Gs * (A + Gs) +
          8 * C ^ 2 * cK * Gs * (2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) +
          160 * C ^ 2 * cK * Uc + 16 * C ^ 2) * S := by
    have e : (4 * Gs * (A + Gs) +
          8 * C ^ 2 * cK * Gs * (2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) +
          160 * C ^ 2 * cK * Uc + 16 * C ^ 2) * S =
        4 * Gs * (A + Gs) * S +
          8 * C ^ 2 * cK * Gs * (2 + Gs / 2 + 2 * (A + Gs) + 2 * Gs * (A + 1)) * S +
          160 * C ^ 2 * cK * Uc * S + 16 * C ^ 2 * S := by ring
    rw [e]
    linarith only [h1, h2, h3, h4]
  have := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 16)
  linarith only [this]

end

end SuperdiffusionCLT.AKHC61.Step3
