/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.WeakNormSqE
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Basic
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.RHS

/-!
# Package C6, part 1: the samplewise square of the weak-norm maximizer bound

Node 7 (`l.weaknorms.prime`) in route-W form. This file squares
`CoarseGraining`'s deterministic weak-norm maximizer bound
(`weakNormsMaximizerGradient_homogenizationScale`,
`weakNormsMaximizerFlux_homogenizationScale`) and weights the gradient and flux
squares by `c` and `c⁻¹` (in the application `c = σ̂_k`, the source's
`M₀ = diag(m₀, m₀⁻¹)`, `m₀ = b₀ # s_{*,0}`).

The random ellipticity factors enter only linearly through `1 + M`
(package B3/D, `akhcWeakD_*`): `λ⁻¹ ≤ K_l (1 + M)`, `Λ ≤ K_u (1 + M)`,
`J(cu_m) ≤ (1 + M) B_J`. In the mismatch term the product `(1 + M)·defect`
is split by `M·x ≤ (ε/2) M² + x²/(2ε)`, so that only second moments of `M`
and of the additivity defect are needed (the defect is never bounded by
`1 + 3^{ρ(m-n)} M`, which would force `ρ < 1/2`).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

open Homogenization MeasureTheory

noncomputable section

/-! ## Pure real arithmetic -/

/-- `(x + y + z + w)² ≤ 4 (x² + y² + z² + w²)`. -/
theorem akhcPrime_sq_add4_le (x y z w : ℝ) :
    (x + y + z + w) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  nlinarith only [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - w), sq_nonneg (y - z),
    sq_nonneg (y - w), sq_nonneg (z - w)]

/-- Squaring `G ≤ 2 (A + C X + C Y + C Z)` for a nonnegative `G`. -/
theorem akhcPrime_sq_of_le {G A X Y Z C : ℝ} (hG : 0 ≤ G)
    (h : G ≤ 2 * (A + C * X + C * Y + C * Z)) :
    G ^ 2 ≤ 16 * (A ^ 2 + C ^ 2 * X ^ 2 + C ^ 2 * Y ^ 2 + C ^ 2 * Z ^ 2) := by
  have h1 : G ^ 2 ≤ (2 * (A + C * X + C * Y + C * Z)) ^ 2 := pow_le_pow_left₀ hG h 2
  have h2 := akhcPrime_sq_add4_le A (C * X) (C * Y) (C * Z)
  have h3 : (2 * (A + C * X + C * Y + C * Z)) ^ 2 = 4 * (A + C * X + C * Y + C * Z) ^ 2 := by
    ring
  have h4 : (C * X) ^ 2 = C ^ 2 * X ^ 2 := by ring
  have h5 : (C * Y) ^ 2 = C ^ 2 * Y ^ 2 := by ring
  have h6 : (C * Z) ^ 2 = C ^ 2 * Z ^ 2 := by ring
  rw [h4, h5, h6] at h2
  linarith only [h1, h2, h3]

/-- `(√x)² ≤ y` from `x ≤ y`, `0 ≤ y`. -/
theorem akhcPrime_sqrt_sq_le {x y : ℝ} (hxy : x ≤ y) (hy : 0 ≤ y) : Real.sqrt x ^ 2 ≤ y := by
  have h := Real.sqrt_le_sqrt hxy
  have h0 := Real.sqrt_nonneg x
  calc Real.sqrt x ^ 2 ≤ Real.sqrt y ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = y := Real.sq_sqrt hy

/-- The Young split of the mismatch product: `(1 + M) x ≤ x + (ε/2) M² + x²/(2ε)`. -/
theorem akhcPrime_young {M x ε : ℝ} (hε : 0 < ε) :
    (1 + M) * x ≤ x + ε / 2 * M ^ 2 + x ^ 2 / (2 * ε) := by
  have hkey : ε / 2 * M ^ 2 + x ^ 2 / (2 * ε) - M * x = (ε * M - x) ^ 2 / (2 * ε) := by
    field_simp
    ring
  have hnn : 0 ≤ (ε * M - x) ^ 2 / (2 * ε) := div_nonneg (sq_nonneg _) (by positivity)
  nlinarith only [hkey, hnn]

/-- `(1 + M)² ≤ 2 (1 + M²)`. -/
theorem akhcPrime_one_add_sq_le (M : ℝ) : (1 + M) ^ 2 ≤ 2 * (1 + M ^ 2) := by
  nlinarith only [sq_nonneg (M - 1)]

/-- **The squared maximizer bound, pure form.** If
`G ≤ 2 (A + C (√l · D) + C (u · √l · √J) + C K₀)` with `l ≤ K N`, `J ≤ N B`,
`D² ≤ S_w S_d`, then `G² ≤ 16 (A² + C² (K N)(S_w S_d) + C² u² (K N)(N B) + C² K₀²)`. -/
theorem akhcPrime_rhs_sq_le {G A l D J u K0 C K N B Sw Sd : ℝ} (hG : 0 ≤ G)
    (hle : G ≤ 2 * (A + C * (Real.sqrt l * D) + C * (u * Real.sqrt l * Real.sqrt J) + C * K0))
    (hl : l ≤ K * N) (hKN : 0 ≤ K * N) (hJ : J ≤ N * B) (hNB : 0 ≤ N * B)
    (hDsq : D ^ 2 ≤ Sw * Sd) :
    G ^ 2 ≤ 16 * (A ^ 2 + C ^ 2 * ((K * N) * (Sw * Sd)) +
      C ^ 2 * (u ^ 2 * ((K * N) * (N * B))) + C ^ 2 * K0 ^ 2) := by
  have h := akhcPrime_sq_of_le hG hle
  have hsl := akhcPrime_sqrt_sq_le hl hKN
  have hsJ := akhcPrime_sqrt_sq_le hJ hNB
  have hsl0 := Real.sqrt_nonneg l
  have hsJ0 := Real.sqrt_nonneg J
  have hX : (Real.sqrt l * D) ^ 2 ≤ (K * N) * (Sw * Sd) := by
    rw [mul_pow]
    exact mul_le_mul hsl hDsq (sq_nonneg _) hKN
  have hY : (u * Real.sqrt l * Real.sqrt J) ^ 2 ≤ u ^ 2 * ((K * N) * (N * B)) := by
    rw [mul_pow, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hsl hsJ (sq_nonneg _) hKN) (sq_nonneg u)
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have hX' := mul_le_mul_of_nonneg_left hX hC2
  have hY' := mul_le_mul_of_nonneg_left hY hC2
  linarith only [h, hX', hY']

/-! ## The samplewise squared bounds -/

/-- The mismatch weight `3^{-(s-s')(m-n)}`. -/
noncomputable def akhcPrime_w (s s' : ℝ) (m n : ℤ) : ℝ :=
  Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - n) : ℝ))

/-- The low-scale tail factor `(s-s')⁻¹ 3^{-(s-s')(m-k)}`. -/
noncomputable def akhcPrime_u (s s' : ℝ) (m k : ℤ) : ℝ :=
  (s - s')⁻¹ * Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - k) : ℝ))

/-- The weighted defect sum `Σ_n w_n · defect_n` over `n ∈ (k, m]`. -/
noncomputable def akhcPrime_defSum {d : ℕ} [NeZero d] (s s' : ℝ) (m k : ℤ) (p q : Vec d)
    (a : RegCoeffField d) : ℝ :=
  ∑ n ∈ Finset.Icc (k + 1) m, akhcPrime_w s s' m n *
    Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale m n p q a

/-- The total mismatch weight `Σ_n w_n` over `n ∈ (k, m]`. -/
noncomputable def akhcPrime_wSum (s s' : ℝ) (m k : ℤ) : ℝ :=
  ∑ n ∈ Finset.Icc (k + 1) m, akhcPrime_w s s' m n

theorem akhcPrime_w_nonneg (s s' : ℝ) (m n : ℤ) : 0 ≤ akhcPrime_w s s' m n :=
  Real.rpow_nonneg (by norm_num) _

theorem akhcPrime_wSum_nonneg (s s' : ℝ) (m k : ℤ) : 0 ≤ akhcPrime_wSum s s' m k :=
  Finset.sum_nonneg fun n _ => akhcPrime_w_nonneg s s' m n

/-- The additivity defect is nonnegative at every a.e.-elliptic sample. -/
theorem akhcPrime_defect_nonneg {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) {m n : ℤ} (hnm : n ≤ m) (p q : Vec d) :
    0 ≤ Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale m n p q a := by
  have h := Book.Ch04.restrictionResponseJObservableCubeSet_le_descendantsAverage_of_aelocallyUniformlyEllipticField
    ha hnm p q
  unfold Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
  linarith only [h]

/-- The Cauchy step for the mismatch sum. -/
theorem akhcPrime_mismatchSum_sq_le {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) (s s' : ℝ) (m k : ℤ) (p q : Vec d) :
    (∑ n ∈ Finset.Icc (k + 1) m,
        Real.rpow (3 : ℝ) (-(s - s') * (Int.toNat (m - n) : ℝ)) *
          Real.sqrt (Book.Ch05.Section53.WeakNormsMaximizer.responseDefectAverageAtScale
            m n p q a)) ^ 2 ≤
      akhcPrime_wSum s s' m k * akhcPrime_defSum s s' m k p q a :=
  Book.Ch05.Section53.JUpperBoundCoarseFluctuations.sq_sum_mul_sqrt_le_sum_mul_sum_mul _ _ _
    (fun _ _ => akhcPrime_w_nonneg s s' m _)
    (fun _ hn => akhcPrime_defect_nonneg ha (Finset.mem_Icc.1 hn).2 p q)

/-- **Samplewise squared gradient bound.** Under `λ⁻¹ ≤ K N` and `J(cu_m) ≤ N B`. -/
theorem akhcPrime_gradient_sq_le {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) {m k : ℤ} (hkm : k < m) {s s' : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hlo : s / 2 ≤ s') (hhi : s' < s) (p q p0 : Vec d) {K N B : ℝ}
    (hl : (Book.Ch04.lambdaSqCoeffField (originCube d m) s' (.finite 1) a)⁻¹ ≤ K * N)
    (hKN : 0 ≤ K * N)
    (hJ : Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a ≤ N * B)
    (hNB : 0 ≤ N * B) :
    (Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet (originCube d m) s p q p0
        a.toFun) ^ 2 ≤
      16 * ((Book.Ch05.Section53.WeakNormsMaximizer.gradientAverageTermAtScale m k s p q p0 a) ^ 2 +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
          ((K * N) * (akhcPrime_wSum s s' m k * akhcPrime_defSum s s' m k p q a)) +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
          (akhcPrime_u s s' m k ^ 2 * ((K * N) * (N * B))) +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
          (Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale m k s p0) ^ 2) := by
  have hle := Book.Ch05.Section53.WeakNormsMaximizer.weakNormsMaximizerGradient_homogenizationScale
    a ha hkm hs hs1 hlo hhi p q p0
  unfold Book.Ch05.Section53.WeakNormsMaximizer.gradientRHSAtScale
    Book.Ch05.Section53.WeakNormsMaximizer.gradientMismatchTermAtScale
    Book.Ch05.Section53.WeakNormsMaximizer.gradientLowScaleTailAtScale at hle
  exact akhcPrime_rhs_sq_le (akhcWNSq_gradientWeakNorm_nonneg _ _ _ _ _ _) hle hl hKN hJ hNB
    (akhcPrime_mismatchSum_sq_le ha s s' m k p q)

/-- **Samplewise squared flux bound.** Under `Λ ≤ K N` and `J(cu_m) ≤ N B`. -/
theorem akhcPrime_flux_sq_le {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Book.Ch04.AELocallyUniformlyEllipticField a) {m k : ℤ} (hkm : k < m) {s s' : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hlo : s / 2 ≤ s') (hhi : s' < s) (p q q0 : Vec d) {K N B : ℝ}
    (hl : Book.Ch04.LambdaSqCoeffField (originCube d m) s' (.finite 1) a ≤ K * N)
    (hKN : 0 ≤ K * N)
    (hJ : Book.Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a ≤ N * B)
    (hNB : 0 ≤ N * B) :
    (Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet (originCube d m) s p q q0
        a.toFun) ^ 2 ≤
      16 * ((Book.Ch05.Section53.WeakNormsMaximizer.fluxAverageTermAtScale m k s p q q0 a) ^ 2 +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
          ((K * N) * (akhcPrime_wSum s s' m k * akhcPrime_defSum s s' m k p q a)) +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
          (akhcPrime_u s s' m k ^ 2 * ((K * N) * (N * B))) +
        Book.Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d ^ 2 *
          (Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale m k s q0) ^ 2) := by
  have hle := Book.Ch05.Section53.WeakNormsMaximizer.weakNormsMaximizerFlux_homogenizationScale
    a ha hkm hs hs1 hlo hhi p q q0
  unfold Book.Ch05.Section53.WeakNormsMaximizer.fluxRHSAtScale
    Book.Ch05.Section53.WeakNormsMaximizer.fluxMismatchTermAtScale
    Book.Ch05.Section53.WeakNormsMaximizer.fluxLowScaleTailAtScale at hle
  exact akhcPrime_rhs_sq_le (akhcWNSq_fluxWeakNorm_nonneg _ _ _ _ _ _) hle hl hKN hJ hNB
    (akhcPrime_mismatchSum_sq_le ha s s' m k p q)

end

end SuperdiffusionCLT.AKHC61.WeakNorms
