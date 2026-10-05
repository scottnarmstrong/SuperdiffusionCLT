/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SideFinal
public import SuperdiffusionCLT.Section3.Terms.SublatticeConcentrationDepth
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityB
public import SuperdiffusionCLT.Section3.Setup.MasterIdentityResidueB
public import SuperdiffusionCLT.Probability.OrliczMoments

/-!
# The two residual carriers of term 3's side leaves, at the enlarged cutoff

`Section3/Terms/RHSTerm3SideFinal.lean` reduces the three side leaves of term 3
to two residual binders: `hMemFlux`, the annealed square integrability of the
per-sub-cube cube mean of the cutoff flux of the glued-field difference, and
`hPair`, the `P`-integrability of the large-cube pairing of `∇w` with the same
flux.  Both are dominated by the `L^∞(cu_m)` envelope `coeffLinftySupBound nu L'
S.m` of the cutoff coefficient at the **enlarged** cutoff `L' = S.m + 2 S.a >
S.m`.

The obstruction named there is removable, and this module removes it:

* the `Γ₂` tail of the large-cube increment envelope is available at the pair of
  scales `(0, L', S.m)`, i.e. with the increment window running **past** the cube
  scale.  The earlier estimate carries `m ≤ l`, but its proof uses that hypothesis
  only to derive `n < l`; separating the two hypotheses gives the tail at the
  enlarged cutoff.  Consequently the whole chain of estimates transports from `L ≤ m`
  to `0 < m` (`integrable_coeffLinftySupBound_pow_four_at_B`).
* the sub-cube energy of the scale-`m` glued field on a scale-`n` sub-cube, and
  the resulting entry bound and annealed square integrability of the flux cube
  mean (`hMemFlux_discharged_B`);
* the large-cube Cauchy–Schwarz bound and `P`-integrability of the pairing
  (`hPair_discharged_B`).

Both discharges are stated for the data of `sideCondition_hcg_final` and
`sideCondition_hosc_final`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

section EnlargedCutoff

variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The `Γ₂` tail of the increment envelope past the cube scale -/

/-- The maximum rule of `IndependentSums` needs at least two summands; the
sub-cube family has `(3^d)^{l-n} ≥ 2` of them as soon as `n < l`. -/
private theorem two_le_largeCubeSubcubes_card_B {n l : ℕ} (hd : 0 < d)
    (hnl : n < l) : 2 ≤ (largeCubeSubcubes d n l).card := by
  have hgap : l - n ≠ 0 := by omega
  have hbase : 2 ≤ 3 ^ d := by
    calc (2 : ℕ) ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  rw [largeCubeSubcubes_card]
  exact hbase.trans (Nat.le_self_pow hgap _)

/-- The explicit dimensional factor of the maximum rule is positive in positive
dimension. -/
private theorem three_mul_log_three_pos_B (hd : 0 < d) :
    0 < 3 * (d : ℝ) * Real.log 3 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact mul_pos (by positivity) hlog

/-- The logarithm of the sub-cube count. -/
private theorem log_largeCubeSubcubes_card_B (d n l : ℕ) :
    Real.log ((largeCubeSubcubes d n l).card : ℝ) =
      ((l - n : ℕ) : ℝ) * ((d : ℝ) * Real.log 3) := by
  have hcard : ((largeCubeSubcubes d n l).card : ℝ) = ((3 : ℝ) ^ d) ^ (l - n) := by
    rw [largeCubeSubcubes_card]
    push_cast
    ring
  rw [hcard, Real.log_pow, Real.log_pow]

/-- The half-integer power as a square root. -/
private theorem rpow_two_inv_eq_sqrt_B (x : ℝ) : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, one_div]

/-- The half-power of the log factor of the maximum rule, in the shape the
envelope amplitude uses. -/
private theorem rpow_three_mul_log_card_B (hd : 0 < d) (n l : ℕ) :
    (3 * Real.log ((largeCubeSubcubes d n l).card : ℝ)) ^ (2 : ℝ)⁻¹ =
      Real.sqrt (3 * (d : ℝ) * Real.log 3) * Real.sqrt ((l - n : ℕ) : ℝ) := by
  have hbase : 3 * Real.log ((largeCubeSubcubes d n l).card : ℝ) =
      (3 * (d : ℝ) * Real.log 3) * ((l - n : ℕ) : ℝ) := by
    rw [log_largeCubeSubcubes_card_B]
    ring
  rw [rpow_two_inv_eq_sqrt_B, hbase,
    Real.sqrt_mul (three_mul_log_three_pos_B hd).le]

/-- **The `Γ₂` tail of the large-cube increment envelope with the two scale
hypotheses separated.**  The estimate
`isBigOWith_gammaSigma_largeCubeIncrementSupBound` carries `m ≤ l`, but its
proof only extracts `n < l` from it, which is why the estimate is available with
the increment window `(n, m]` running past the cube scale `l`: taking
`n = 0`, `m = L`, `l = m` bounds the increment envelope of `cu_m` at the
enlarged cutoff `L > m`. -/
theorem isBigOWith_gammaSigma_largeCubeIncrementSupBound_of_lt_B
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m l : ℕ} (hnm : n < m) (hnl : n < l) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (largeCubeIncrementSupBound n m l)
      (largeCubeLinftyConst d *
        (Real.sqrt ((m - n : ℕ) : ℝ) * Real.sqrt ((l - n : ℕ) : ℝ))) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hsup := IndependentSums.isBigOWith_gammaSigma_finset_sup'
    (μ := P.toMeasure) (largeCubeSubcubes d n l)
    (largeCubeSubcubes_nonempty d n l)
    (X := fun R (omega : ShellSeq d) ↦
      translatedIncrementSupBound (cubeCenter R) n m omega)
    (A := streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) (σ := 2)
    (by norm_num) (two_le_largeCubeSubcubes_card_B hd hnl)
    (fun R _ ↦ isBigOWith_gammaSigma_translatedIncrementSupBound
      hPrefix hJ2 hJ3 hJ4 hnm (cubeCenter R))
  have hscale :
      (3 * Real.log ((largeCubeSubcubes d n l).card : ℝ)) ^ (2 : ℝ)⁻¹ *
          (streamLinftyConst d * Real.sqrt ((m - n : ℕ) : ℝ)) =
        largeCubeLinftyConst d *
          (Real.sqrt ((m - n : ℕ) : ℝ) * Real.sqrt ((l - n : ℕ) : ℝ)) := by
    rw [rpow_three_mul_log_card_B hd n l, largeCubeLinftyConst]
    ring
  rw [hscale] at hsup
  exact hsup

/-- The increment envelope of `cu_m` at the increment window `(0, L]`, as an
annealed `Γ₂` tail: the separated-hypotheses estimate at `n = 0`, `m = L`,
`l = m`.  This is the half of the tail that the chain with `L ≤ m` could not reach,
because it needs `L > m`. -/
theorem isBigO_gammaSigma_largeCubeIncrementSupBound_at_B
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {L m : ℕ} (hL : 0 < L) (hm : 0 < m) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦ largeCubeIncrementSupBound 0 L m omega)
      (largeCubeLinftyConst d *
        (Real.sqrt ((L : ℕ) : ℝ) * Real.sqrt ((m : ℕ) : ℝ))) := by
  refine (isBigOWith_iff_isBigO_of_nonneg
    (fun omega ↦ largeCubeIncrementSupBound_nonneg 0 L m omega)).1 ?_
  simpa only [Nat.sub_zero] using
    (isBigOWith_gammaSigma_largeCubeIncrementSupBound_of_lt_B
      hPrefix hJ2 hJ3 hJ4 (n := 0) (m := L) (l := m) hL hm)

/-- The `Γ₂` tail of the stream-cutoff envelope of `cu_m` at the enlarged
cutoff: the estimate `isBigO_gammaSigma_streamCutoffLargeCubeSupBound`
with `L ≤ m` replaced by `0 < m`. -/
theorem isBigO_gammaSigma_streamCutoffLargeCubeSupBound_at_B
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {L m : ℕ} (hL : 0 < L) (hm : 0 < m) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦ streamCutoffLargeCubeSupBound L m omega)
      (streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d L m) := by
  have hshellA : (0 : ℝ) < shellValueLargeCubeConst d *
      Real.sqrt (1 + ((m : ℕ) : ℝ)) := by
    refine mul_pos (lt_of_lt_of_le zero_lt_one (one_le_shellValueLargeCubeConst d)) ?_
    exact Real.sqrt_pos.2 (by positivity)
  have hincA : (0 : ℝ) < largeCubeLinftyConst d *
      (Real.sqrt ((L : ℕ) : ℝ) * Real.sqrt ((m : ℕ) : ℝ)) := by
    refine mul_pos (largeCubeLinftyConst_pos hPrefix) ?_
    exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hL))
      (Real.sqrt_pos.2 (by exact_mod_cast hm))
  have hshell : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦ shellValueLargeCubeSupBound 0 m omega)
      (shellValueLargeCubeConst d * Real.sqrt (1 + ((m : ℕ) : ℝ))) :=
    (isBigOWith_iff_isBigO_of_nonneg
      (fun omega ↦ shellValueLargeCubeSupBound_nonneg 0 m omega)).1
      (isBigOWith_gammaSigma_shellValueLargeCubeSupBound hPrefix hJ3
        (k := 0) (m := m) (Nat.zero_le m))
  exact isBigO_gammaSigma_add_of_isBigO (sigma := 2) (by norm_num) hshellA hincA hshell
    (isBigO_gammaSigma_largeCubeIncrementSupBound_at_B hPrefix hJ2 hJ3 hJ4 hL hm)
    (measurable_shellValueLargeCubeSupBound 0 m)
    (measurable_largeCubeIncrementSupBound 0 L m)

/-- The `Γ₂` tail of the `L^∞(cu_m)` coefficient envelope at the enlarged
cutoff: the estimate `isBigO_gammaSigma_coeffLinftySupBound` with `L ≤ m`
replaced by `0 < m`, which is what the term-3 carriers need at
`L = S.LPrime > S.m`. -/
theorem isBigO_gammaSigma_coeffLinftySupBound_at_B
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 ≤ nu) {L m : ℕ} (hL : 0 < L) (hm : 0 < m) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ShellSeq d ↦ coeffLinftySupBound nu L m omega)
      (coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d L m) :=
  isBigO_gammaSigma_const_add_of_isBigO hnu
    (isBigO_gammaSigma_streamCutoffLargeCubeSupBound_at_B hPrefix hJ2 hJ3 hJ4 hL hm)

/-- The amplitude of the enlarged-cutoff tail is positive. -/
private theorem coeffLinftyGammaTwoAmplitude_pos_B
    (hPrefix : ShellLawPrefix d P) {nu : ℝ} (hnu : 0 ≤ nu) (L m : ℕ) :
    0 < coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d L m := by
  rw [coeffLinftyGammaTwoAmplitude, streamCutoffLinftyGammaTwoAmplitude]
  refine add_pos_of_nonneg_of_pos hnu (mul_pos gammaTriangleConst_pos ?_)
  exact add_pos_of_pos_of_nonneg
    (mul_pos (lt_of_lt_of_le zero_lt_one (one_le_shellValueLargeCubeConst d))
      (Real.sqrt_pos.2 (by
        have hmc : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le m
        linarith only [hmc])))
    (mul_nonneg (largeCubeLinftyConst_pos hPrefix).le
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- The integrability companion of the majorant moment bound above. -/
private theorem integrable_rpow_of_gammaTwo_majorant_B
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω}
    [MeasureTheory.IsProbabilityMeasure mu] {Y : Ω → ℝ} {A : ℝ}
    (hA : 0 < A) (hYnn : ∀ omega, 0 ≤ Y omega) (hYm : Measurable Y)
    (hY : IndependentSums.IsBigO mu (IndependentSums.gammaSigma 2) Y A) (k : ℕ) :
    MeasureTheory.Integrable (fun omega => Y omega ^ (k : ℝ)) mu := by
  have hYabs : (fun omega => |Y omega| ^ (k : ℝ)) = fun omega => Y omega ^ (k : ℝ) :=
    funext fun omega ↦ by rw [abs_of_nonneg (hYnn omega)]
  rw [hYabs.symm]
  exact integrable_abs_rpow_of_isBigO_gammaSigma_two hA hYm.aemeasurable hY k

/-- The fourth power of the enlarged-cutoff coefficient envelope is integrable
(in real-power form, the shape the Orlicz module exports). -/
theorem integrable_coeffLinftySupBound_rpow_four_at_B
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 ≤ nu) {L m : ℕ} (hL : 0 < L) (hm : 0 < m) :
    MeasureTheory.Integrable
      (fun omega : ShellSeq d ↦ coeffLinftySupBound nu L m omega ^ (4 : ℝ))
      P.toMeasure :=
  integrable_rpow_of_gammaTwo_majorant_B
    (A := coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d L m)
    (coeffLinftyGammaTwoAmplitude_pos_B (d := d) hPrefix hnu L m)
    (fun omega ↦ coeffLinftySupBound_nonneg nu hnu L m omega)
    (measurable_coeffLinftySupBound nu L m)
    (isBigO_gammaSigma_coeffLinftySupBound_at_B hPrefix hJ2 hJ3 hJ4 hnu hL hm) 4

/-- The natural-power form of the integrability above. -/
theorem integrable_coeffLinftySupBound_pow_four_at_B
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 ≤ nu) {L m : ℕ} (hL : 0 < L) (hm : 0 < m) :
    MeasureTheory.Integrable
      (fun omega : ShellSeq d ↦ coeffLinftySupBound nu L m omega ^ (4 : ℕ))
      P.toMeasure :=
  (integrable_coeffLinftySupBound_rpow_four_at_B hPrefix hJ2 hJ3 hJ4 hnu hL hm).congr
    (Filter.Eventually.of_forall fun omega ↦
      Real.rpow_natCast (coeffLinftySupBound nu L m omega) 4)

/-- The square of the enlarged-cutoff coefficient envelope is integrable. -/
theorem integrable_coeffLinftySupBound_sq_at_B
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 ≤ nu) {L m : ℕ} (hL : 0 < L) (hm : 0 < m) :
    MeasureTheory.Integrable
      (fun omega : ShellSeq d ↦ coeffLinftySupBound nu L m omega ^ (2 : ℕ))
      P.toMeasure :=
  (integrable_rpow_of_gammaTwo_majorant_B
    (A := coeffLinftyGammaTwoAmplitude nu (largeCubeLinftyConst d) d L m)
    (coeffLinftyGammaTwoAmplitude_pos_B (d := d) hPrefix hnu L m)
    (fun omega ↦ coeffLinftySupBound_nonneg nu hnu L m omega)
    (measurable_coeffLinftySupBound nu L m)
    (isBigO_gammaSigma_coeffLinftySupBound_at_B hPrefix hJ2 hJ3 hJ4 hnu hL hm) 2).congr
    (Filter.Eventually.of_forall fun omega ↦
      Real.rpow_natCast (coeffLinftySupBound nu L m omega) 2)

/-- The `ℝ≥0∞` lintegral of the square of the enlarged-cutoff envelope is
finite, the shape the finiteness carriers of the pairing engine consume. -/
theorem lintegral_coeffLinftySupBound_sq_ne_top_B
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 ≤ nu) {L m : ℕ} (hL : 0 < L) (hm : 0 < m) :
    (∫⁻ omega : ShellSeq d,
        (ENNReal.ofReal (coeffLinftySupBound nu L m omega)) ^ (2 : ℕ) ∂P.toMeasure)
      ≠ ⊤ := by
  have hInt := integrable_coeffLinftySupBound_sq_at_B hPrefix hJ2 hJ3 hJ4 hnu hL hm
  have hnn : ∀ omega : ShellSeq d, (0 : ℝ) ≤ coeffLinftySupBound nu L m omega ^ (2 : ℕ) :=
    fun omega => pow_nonneg (coeffLinftySupBound_nonneg nu hnu L m omega) 2
  have hfin := hInt.hasFiniteIntegral
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)] at hfin
  have hcongr : (∫⁻ omega : ShellSeq d,
        (ENNReal.ofReal (coeffLinftySupBound nu L m omega)) ^ (2 : ℕ) ∂P.toMeasure) =
      ∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (coeffLinftySupBound nu L m omega ^ (2 : ℕ)) ∂P.toMeasure :=
    lintegral_congr fun omega => (ENNReal.ofReal_pow (coeffLinftySupBound_nonneg nu hnu L m omega) 2).symm
  rw [hcongr]
  exact hfin.ne

end EnlargedCutoff

/-! ## The energy of the scale-`m` glued field on a scale-`n` sub-cube

The glued field at `k = m` is the single maximizer of the large cube, so its
energy on the whole large cube is `nu⁻² |F|²`; on a scale-`n` sub-cube the
normalized average picks up the volume ratio, which is the number of sub-cubes.
That ratio is the only place where the enlarged cutoff enters the *energy*
side of the two carriers: the operator envelope carries the enlarged scale, the
field itself does not. -/

/-- The squared Euclidean norm of a vector is bounded by the dimension times the
square of a common coordinate bound. -/
private theorem vecNormSq_le_card_mul_sq_B (v : Vec d) {K : ℝ} (_hK : 0 ≤ K)
    (h : ∀ i : Fin d, |v i| ≤ K) : vecNormSq v ≤ (d : ℝ) * K ^ 2 := by
  have hsum : vecNormSq v = ∑ i : Fin d, v i ^ 2 := by
    simp only [vecNormSq, vecDot, pow_two]
  rw [hsum]
  calc ∑ i : Fin d, v i ^ 2 ≤ ∑ _i : Fin d, K ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := pow_le_pow_left₀ (abs_nonneg (v i)) (h i) 2
        rwa [sq_abs] at h1
    _ = (d : ℝ) * K ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The energy of the scale-`m` glued field on a scale-`n` sub-cube of
`cu_m`.**  The average over the sub-cube is at most the number of sub-cubes
times the average over `cu_m`, on which the glued field is the single large-cube
maximizer, whose energy is `nu⁻² |F|²`. -/
theorem vecCubeLpENorm_gluedGradientField_self_subcube_B {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) {L n m : ℕ} (_hnm : n ≤ m) {F : Vec d}
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d n m) :
    (vecCubeLpENorm R 2 (gluedGradientField hnu L m m F omega)).toReal ≤
      Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
        (nu⁻¹ * Real.sqrt (vecNormSq F)) := by
  classical
  set V : Vec d → Vec d := gluedGradientField hnu L m m F omega with hVdef
  set Q : TriadicCube d := originCube d (m : ℤ) with hQdef
  set c : ℝ := nu⁻¹ * nu⁻¹ * vecNormSq F with hcdef
  have hnu0 : (0 : ℝ) < nu⁻¹ := inv_pos.2 hnu
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    exact mul_nonneg (mul_nonneg hnu0.le hnu0.le) (vecNormSq_nonneg F)
  have hcardpos : (0 : ℝ) < ((largeCubeSubcubes d n m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (largeCubeSubcubes_nonempty d n m)
  have hQmem : Q ∈ largeCubeSubcubes d m m := by
    rw [hQdef]
    exact originCube_mem_largeCubeSubcubes (le_refl m)
  have hglued : ∀ x ∈ openCubeSet Q,
      V x = cubeMaximizerGradient hnu omega L F Q x := by
    intro x hx
    rw [hVdef, hQdef]
    exact gluedGradientField_apply_of_mem_openCubeSet hnu L m m F omega hQmem hx
  have hQavg : volumeAverage (openCubeSet Q) (fun x => vecNormSq (V x)) ≤ c := by
    have heq : volumeAverage (openCubeSet Q) (fun x => vecNormSq (V x)) =
        volumeAverage (openCubeSet Q)
          (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F Q x)) := by
      refine congrArg
        (fun t : ℝ => (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ * t) ?_
      refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) ?_
      intro x hx
      exact congrArg vecNormSq (hglued x hx)
    rw [heq, hcdef]
    exact volumeAverage_vecNormSq_cubeMaximizerGradient_le hnu omega L F Q
  have hint : ∀ R' ∈ largeCubeSubcubes d n m,
      IntegrableOn (fun x => vecNormSq (V x)) (openCubeSet R') volume :=
    fun R' _ => integrableOn_vecNormSq_gluedGradientField hnu L m m F omega R'
  have hnn : ∀ R' ∈ largeCubeSubcubes d n m,
      0 ≤ volumeAverage (openCubeSet R') (fun x => vecNormSq (V x)) := by
    intro R' _
    rw [volumeAverage]
    refine mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) ?_
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg (V x))
  have hle_sum : volumeAverage (openCubeSet R) (fun x => vecNormSq (V x)) ≤
      ∑ R' ∈ largeCubeSubcubes d n m,
        volumeAverage (openCubeSet R') (fun x => vecNormSq (V x)) :=
    Finset.single_le_sum (fun R' hR' => hnn R' hR') hR
  have hsingle : volumeAverage (openCubeSet R) (fun x => vecNormSq (V x)) ≤
      ((largeCubeSubcubes d n m).card : ℝ) * c := by
    have havsum := volumeAverage_avsum_openCubeSet (n := n) (l := m)
      (f := fun x => vecNormSq (V x)) hint
    have hmul := mul_le_mul_of_nonneg_left hle_sum (le_of_lt (inv_pos.2 hcardpos))
    rw [← havsum] at hmul
    have hfinal : ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        volumeAverage (openCubeSet R) (fun x => vecNormSq (V x)) ≤ c :=
      le_trans hmul hQavg
    calc volumeAverage (openCubeSet R) (fun x => vecNormSq (V x))
        = ((largeCubeSubcubes d n m).card : ℝ) *
            (((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
              volumeAverage (openCubeSet R) (fun x => vecNormSq (V x))) := by
          rw [mul_inv_cancel_left₀ (ne_of_gt hcardpos)]
      _ ≤ ((largeCubeSubcubes d n m).card : ℝ) * c :=
          mul_le_mul_of_nonneg_left hfinal hcardpos.le
  have hmemV : MemVectorL2 (openCubeSet R) V :=
    memVectorL2_openCubeSet_gluedGradientField hnu L m m F omega R
  have hsq := vecCubeLpENorm_two_sq_le_of_volumeAverage_le (Q := R) hmemV hsingle
  have htoReal := vecCubeLpENorm_toReal_le_of_sq_le (G := V)
    (mul_nonneg hcardpos.le hc0) hsq
  have hsqrtc : Real.sqrt c = nu⁻¹ * Real.sqrt (vecNormSq F) := by
    rw [hcdef, Real.sqrt_mul (mul_nonneg hnu0.le hnu0.le),
      Real.sqrt_mul_self_eq_abs, abs_of_nonneg hnu0.le]
  calc (vecCubeLpENorm R 2 V).toReal
      ≤ Real.sqrt (((largeCubeSubcubes d n m).card : ℝ) * c) := htoReal
    _ = Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
          (nu⁻¹ * Real.sqrt (vecNormSq F)) := by
        rw [Real.sqrt_mul hcardpos.le, hsqrtc]

/-- **The energy of the glued-field difference on a scale-`n` sub-cube.**  The
scale-`n` glued field is the family estimate; the scale-`m` glued field is
the estimate above. -/
theorem vecCubeLpENorm_gluedGradientField_diff_subcube_B {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) {L n m : ℕ} (hnm : n ≤ m) {F : Vec d}
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d n m) :
    (vecCubeLpENorm R 2 (fun x =>
        gluedGradientField hnu L m m F omega x -
          gluedGradientField hnu L n m F omega x)).toReal ≤
      (Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) + 1) *
        (nu⁻¹ * Real.sqrt (vecNormSq F)) := by
  classical
  set Gm : Vec d → Vec d := gluedGradientField hnu L m m F omega with hGmdef
  set Gn : Vec d → Vec d := gluedGradientField hnu L n m F omega with hGndef
  have hmGm : MemLp (hilbertifyVecField Gm) 2 (normalizedCubeMeasure R) :=
    memLp_hilbertifyVecField_of_memVectorL2
      (memVectorL2_openCubeSet_gluedGradientField hnu L m m F omega R)
  have hmGn : MemLp (hilbertifyVecField Gn) 2 (normalizedCubeMeasure R) :=
    memLp_hilbertifyVecField_of_memVectorL2
      (memVectorL2_openCubeSet_gluedGradientField hnu L n m F omega R)
  have htri : vecCubeLpENorm R 2 (fun x => Gm x - Gn x) ≤
      vecCubeLpENorm R 2 Gm + vecCubeLpENorm R 2 Gn := by
    have h := vecCubeLpENorm_add_le (Q := R) (q := 2) (F := Gm)
      (G := fun x => - Gn x) (by norm_num) hmGm.aestronglyMeasurable
      hmGn.neg.aestronglyMeasurable
    simpa only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, vecCubeLpENorm_neg] using h
  have hfinGm : vecCubeLpENorm R 2 Gm ≠ ⊤ := hmGm.eLpNorm_lt_top.ne
  have hfinGn : vecCubeLpENorm R 2 Gn ≠ ⊤ := hmGn.eLpNorm_lt_top.ne
  have htoReal : (vecCubeLpENorm R 2 (fun x => Gm x - Gn x)).toReal ≤
      (vecCubeLpENorm R 2 Gm).toReal + (vecCubeLpENorm R 2 Gn).toReal := by
    have hsumtop : vecCubeLpENorm R 2 Gm + vecCubeLpENorm R 2 Gn ≠ ⊤ :=
      (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hfinGm,
        lt_top_iff_ne_top.2 hfinGn⟩).ne
    have h1 := ENNReal.toReal_mono hsumtop htri
    rwa [ENNReal.toReal_add hfinGm hfinGn] at h1
  have hA := vecCubeLpENorm_gluedGradientField_self_subcube_B (d := d) hnu omega
    (L := L) (n := n) (m := m) hnm (F := F) hR
  have hB := vecCubeLpENorm_gluedGradientField_family (d := d) hnu omega
    (L := L) (k := n) (m := m) hnm (F := F) hR
  calc (vecCubeLpENorm R 2 (fun x => Gm x - Gn x)).toReal
      ≤ (vecCubeLpENorm R 2 Gm).toReal + (vecCubeLpENorm R 2 Gn).toReal := htoReal
    _ ≤ Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
          (nu⁻¹ * Real.sqrt (vecNormSq F)) + (nu⁻¹ * Real.sqrt (vecNormSq F)) :=
        add_le_add hA hB
    _ = (Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) + 1) *
          (nu⁻¹ * Real.sqrt (vecNormSq F)) := by ring

/-! ## The per-coordinate envelope on the open sub-cube -/

/-- The coordinate pairing of a vector with the unit vector `e_i` is the `i`-th
coordinate. -/
private theorem vecDot_single_B (v : Vec d) (i : Fin d) :
    vecDot v (Pi.single i (1 : ℝ)) = v i := by
  simp [vecDot, Pi.single_apply]

/-- The Euclidean magnitude of the unit coordinate vector is one. -/
private theorem vecNorm_single_B (i : Fin d) : vecNorm (Pi.single i (1 : ℝ)) = 1 := by
  have hv0 : 0 ≤ vecNorm (Pi.single i (1 : ℝ)) := vecNorm_nonneg _
  have hsq : vecNorm (Pi.single i (1 : ℝ)) ^ 2 = 1 := by
    rw [SuperdiffusionCLT.Section3.Setup.vecNorm_sq_eq_vecNormSq]
    show vecDot (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) = 1
    simp [vecDot, Pi.single_apply]
  rw [show vecNorm (Pi.single i (1 : ℝ)) =
      Real.sqrt (vecNorm (Pi.single i (1 : ℝ)) ^ 2) from
    by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hv0], hsq, Real.sqrt_one]

/-- **The per-coordinate envelope on the open sub-cube, with an arbitrary energy
constant.**  For every triadic cube `Q` whose open realization sits in `cu_m`,
every coordinate `i` and every field `V` that is `L²` on `Q`,

> `|⍍_{Q} (a_L V)_i| ≤ ‖a_L‖_{L^∞(cu_m)} · C`

whenever the normalized cube norm of `V` is at most `C`.  The proof is the
pointwise operator bound on `cubeSet cu_m` paired with Cauchy–Schwarz on the
cube; the `L²` membership is transported to the normalized cube measure. -/
private theorem abs_volumeAverageVec_cutoff_entry_le_open_B {Q : TriadicCube d}
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) {L m : ℕ} {V : Vec d → Vec d}
    (i : Fin d) (hV : MemVectorL2 (openCubeSet Q) V)
    (hsub : openCubeSet Q ⊆ cubeSet (originCube d (m : ℤ))) {c : ℝ} (_hc : 0 ≤ c)
    (hn : (vecCubeLpENorm Q 2 V).toReal ≤ c) :
    |volumeAverageVec (openCubeSet Q)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x) (V x)) i| ≤
      coeffLinftySupBound nu L m omega * c := by
  classical
  set A : Vec d → Mat d := (coefficientCutoff nu omega L).toCoeffField with hAdef
  have hB0 : 0 ≤ coeffLinftySupBound nu L m omega :=
    coeffLinftySupBound_nonneg nu (le_of_lt hnu) L m omega
  have hmemHf : MemLp (hilbertifyVecField fun x => matVecMul (A x) (V x)) 2
      (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_of_memVectorL2
      (memVectorL2_matVecMul_coefficientCutoff hnu omega L Q hV)
  have hmemHG : MemLp (hilbertifyVecField V) 2 (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_of_memVectorL2 hV
  have hmemHb : MemLp (hilbertifyVecField fun _ : Vec d => Pi.single i (1 : ℝ)) 2
      (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const (HilbertVec.ofVec (Pi.single i (1 : ℝ)))
  have hcs := Section2.Norms.abs_volumeAverage_vecDot_le_mul
    (Q := Q) (a := fun x => matVecMul (A x) (V x))
    (b := fun _ : Vec d => Pi.single i (1 : ℝ)) hmemHf hmemHb
  rw [volumeAverage_cubeSet_eq_openCubeSet Q
    (fun x => vecDot (matVecMul (A x) (V x)) (Pi.single i (1 : ℝ)))] at hcs
  have havg : volumeAverageVec (openCubeSet Q) (fun x => matVecMul (A x) (V x)) i
      = volumeAverage (openCubeSet Q)
          (fun x => vecDot (matVecMul (A x) (V x)) (Pi.single i (1 : ℝ))) := by
    show volumeAverage (openCubeSet Q) (fun x => matVecMul (A x) (V x) i) = _
    exact congrArg (volumeAverage (openCubeSet Q))
      (funext fun x => (vecDot_single_B (matVecMul (A x) (V x)) i).symm)
  rw [← havg] at hcs
  have hq0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hone : (vecCubeLpENorm Q 2 fun _ : Vec d => Pi.single i (1 : ℝ)).toReal = 1 := by
    rw [vecCubeLpENorm_const_eq hq0, vecNorm_single_B]
    exact ENNReal.toReal_ofReal one_pos.le
  rw [hone, mul_one] at hcs
  have hftop : vecCubeLpENorm Q 2 (fun x => matVecMul (A x) (V x)) ≠ ⊤ :=
    ne_of_lt hmemHf.eLpNorm_lt_top
  have hprod : ENNReal.ofReal (coeffLinftySupBound nu L m omega) * vecCubeLpENorm Q 2 V
      < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmemHG.eLpNorm_lt_top
  have hOp : ∀ᵐ x ∂(normalizedCubeMeasure Q),
      matrixOperatorNorm (A x) ≤ coeffLinftySupBound nu L m omega := by
    rw [hAdef, normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact Measure.ae_smul_measure
      ((MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)).mono
        fun x hx =>
          matrixOperatorNorm_coefficientCutoff_le_coeffLinftySupBound nu hnu.le omega
            (hsub hx))
      (ENNReal.ofReal ((cubeVolume Q)⁻¹))
  have hscale : (vecCubeLpENorm Q 2 (fun x => matVecMul (A x) (V x))).toReal ≤
      coeffLinftySupBound nu L m omega * (vecCubeLpENorm Q 2 V).toReal := by
    have hprod' := vecCubeLpENorm_matVecMul_le 2 A V hB0 hmemHf.aestronglyMeasurable hOp
    exact (ENNReal.toReal_le_toReal hftop hprod.ne).2 hprod' |>.trans
      (by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0])
  calc |volumeAverageVec (openCubeSet Q)
        (fun x => matVecMul (A x) (V x)) i| ≤
      (vecCubeLpENorm Q 2 (fun x => matVecMul (A x) (V x))).toReal := hcs
    _ ≤ coeffLinftySupBound nu L m omega * c :=
      le_trans hscale (mul_le_mul_of_nonneg_left hn hB0)

/-! ## The `hMemFlux` carrier, discharged -/

/-- The Euclidean squared norm of a measurable vector-valued map is measurable. -/
private theorem measurable_vecNormSq_comp_B {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → Vec d} (hf : Measurable f) : Measurable fun omega => vecNormSq (f omega) := by
  have hcomp : ∀ i : Fin d, Measurable fun omega => f omega i :=
    fun i => (measurable_pi_apply i).comp hf
  show Measurable fun omega => vecDot (f omega) (f omega)
  simp only [vecDot]
  exact Finset.measurable_sum _ fun i _ => (hcomp i).mul (hcomp i)

/-- **The first residual of `sideCondition_hcg_final` and
`sideCondition_hosc_final`, discharged.**  The per-sub-cube cube mean of the
cutoff flux of the glued-field difference is annealed square integrable at the
enlarged cutoff `L' = S.LPrime > S.m`.  The carrier is dominated by the `L^∞`
envelope together with the scale-`n` energy of the difference, and the fourth
power of the envelope is integrable at the enlarged cutoff by
`integrable_coeffLinftySupBound_pow_four_at_B`. -/
theorem hMemFlux_discharged_B [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d) :
    ∀ R ∈ largeCubeSubcubes d S.n S.m, MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
          matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m
                (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y)))) 2 P.toMeasure := by
  classical
  intro R hR
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hFdef
  set c : ℝ := (Real.sqrt ((largeCubeSubcubes d S.n S.m).card : ℝ) + 1) *
    (nu⁻¹ * Real.sqrt (vecNormSq F)) with hcdef
  have hnm : S.n ≤ S.m := (ScalesOrdering.mem_pigeon_range hSorder).1.2
  have hmpos : 0 < S.m := lt_of_le_of_lt (Nat.zero_le _) hSorder.ellPrime_lt_m
  have hLpos : 0 < S.LPrime := lt_trans hmpos hSorder.m_lt_LPrime
  have hnu0 : (0 : ℝ) < nu⁻¹ := inv_pos.2 hnu
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    exact mul_nonneg (add_nonneg (Real.sqrt_nonneg _) zero_le_one)
      (mul_nonneg hnu0.le (Real.sqrt_nonneg _))
  have hmeas : Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
        matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m F omega y -
            gluedGradientField hnu S.LPrime S.n S.m F omega y)))) :=
    measurable_vecNormSq_comp_B
      (measurable_volumeAverageVec_coefficientCutoff_gluedDifference_final
        hnu P S e R hR)
  have hcoord : ∀ (omega : ShellSeq d) (i : Fin d),
      |volumeAverageVec (openCubeSet R) (fun y =>
        matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m F omega y -
            gluedGradientField hnu S.LPrime S.n S.m F omega y)) i| ≤
      coeffLinftySupBound nu S.LPrime S.m omega * c := by
    intro omega i
    refine abs_volumeAverageVec_cutoff_entry_le_open_B (Q := R) hnu omega i
      (V := fun y => gluedGradientField hnu S.LPrime S.m S.m F omega y -
        gluedGradientField hnu S.LPrime S.n S.m F omega y)
      ((memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m F omega R).sub
        (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega R))
      (Set.Subset.trans (openCubeSet_subset_cubeSet R)
        (cubeSet_subset_of_mem_largeCubeSubcubes hR)) hc0
      (vecCubeLpENorm_gluedGradientField_diff_subcube_B (d := d) hnu omega
        (L := S.LPrime) (n := S.n) (m := S.m) hnm (F := F) hR)
  have hnorm : ∀ omega : ShellSeq d,
      vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
        matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m F omega y -
            gluedGradientField hnu S.LPrime S.n S.m F omega y))) ≤
      ((d : ℝ) * c ^ 2) * (coeffLinftySupBound nu S.LPrime S.m omega) ^ 2 := by
    intro omega
    have hK : 0 ≤ coeffLinftySupBound nu S.LPrime S.m omega * c :=
      mul_nonneg (coeffLinftySupBound_nonneg nu hnu.le S.LPrime S.m omega) hc0
    have h := vecNormSq_le_card_mul_sq_B
      (volumeAverageVec (openCubeSet R) (fun y =>
        matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m F omega y -
            gluedGradientField hnu S.LPrime S.n S.m F omega y))) hK
      (fun i => hcoord omega i)
    calc vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
          matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m F omega y -
              gluedGradientField hnu S.LPrime S.n S.m F omega y)))
        ≤ (d : ℝ) * (coeffLinftySupBound nu S.LPrime S.m omega * c) ^ 2 := h
      _ = ((d : ℝ) * c ^ 2) * (coeffLinftySupBound nu S.LPrime S.m omega) ^ 2 := by ring
  refine (MeasureTheory.memLp_two_iff_integrable_sq
    (f := fun omega : ShellSeq d => vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
      matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m F omega y -
          gluedGradientField hnu S.LPrime S.n S.m F omega y))))
    hmeas.aestronglyMeasurable).2 ?_
  refine MeasureTheory.Integrable.mono'
    ((integrable_coeffLinftySupBound_pow_four_at_B hPrefix hJ2 hJ3 hJ4 hnu.le hLpos hmpos).const_mul
      (((d : ℝ) * c ^ 2) ^ 2))
    (hmeas.pow_const 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun omega => ?_
  have h1 : (0 : ℝ) ≤ vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
      matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m F omega y -
          gluedGradientField hnu S.LPrime S.n S.m F omega y))) := vecNormSq_nonneg _
  rw [Real.norm_of_nonneg (pow_nonneg h1 2)]
  calc (vecNormSq (volumeAverageVec (openCubeSet R) (fun y =>
          matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m F omega y -
              gluedGradientField hnu S.LPrime S.n S.m F omega y)))) ^ 2
      ≤ (((d : ℝ) * c ^ 2) * (coeffLinftySupBound nu S.LPrime S.m omega) ^ 2) ^ 2 :=
        pow_le_pow_left₀ h1 (hnorm omega) 2
    _ = ((d : ℝ) * c ^ 2) ^ 2 * (coeffLinftySupBound nu S.LPrime S.m omega) ^ 4 := by ring

end

end SuperdiffusionCLT.Section3.Terms
