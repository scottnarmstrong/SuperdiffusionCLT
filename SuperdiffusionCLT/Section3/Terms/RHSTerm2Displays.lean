/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputs
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB
public import Homogenization.Sobolev.Foundations.CubeCoerciveH1
public import Mathlib.Probability.Independence.Integration

/-!
# The displayed steps of `l.RHS.term2`

This module carries the two proof steps of `l.RHS.term2` that the paper names,
`l.RHS.term2#independence-decoupling` and `l.RHS.term2#poincare-per-cube`,
together with the measure-theoretic surface that the assembly of `RHSTerm2Main` uses:
transfer of `L²` data to a sub-cube, Cauchy-Schwarz on a cube and in the
sample, Jensen on a cube, the sub-cube decomposition of the squared normalized
norm, the three-term splitting of the cubewise lattice average,
and the bound on the *centred* cubewise average.

`poincare_per_cube` is the Poincare-Wirtinger inequality on one triadic cube in
the normalized `L̲²` reading: the coercive estimate
`Homogenization.scaledTranslatedCubeMeanZeroH1CoerciveEstimate`, applied to the
`d` components and reassembled into Euclidean magnitudes, so its constant is
`3^{scale} C_d`.  The `H¹` data of the components is an input: the paper's
`R = (k_{L'} − k_ℓ)ᵗ∇w` is `H¹` on each sub-cube by the product rule, which the
rendering of `l.RHS.term2` carries as the free binder `DR`.

`independence_decoupling` is the vanishing `E[(R)_{z+cu_n}·((∇ũ_n)_{z+cu_n} −
p̃)] = 0` in the proof of `l.RHS.term2`.  Its two inputs are stated in the shapes the paper
uses.  `hindep` is the independence of the two cube-mean vectors; the paper
obtains it from `a.j.indy` (`ShellLawJ2`), since `R` is measurable
with respect to `F_> = σ(j_r : r > ℓ)` — the cutoff difference `k_{L'} − k_ℓ`
uses only the shells in `(ℓ, L']`, and `∇w` solves `e.def.w`, whose forcing
`(k_{L'} − k_{ℓ'})p` uses only the shells in `(ℓ', L']` with `ℓ < ℓ'` — while
`∇ũ_n` is built from the cutoff `a_ℓ`, hence from the shells `r ≤ ℓ`.  Neither
measurability statement is available for the free binders of the rendered
lemma, nor, for the proxy, even for the glued field (its Chapter 2
canonical maximizer is produced by a choice; see `GluedField.lean`), so the
independence is an explicit hypothesis.  `hmean` is `E[(∇ũ_n)_{z+cu_n}] = p̃`
for the sub-cube `z`: the `p̃ = p`-type stationarity of the cube-wise means,
`p̃` being defined as the average over the *centred* cube `cu_n`
while the cancellation is needed on every translate.  For the glued
field the corresponding statement is
`integral_volumeAverageVec_gluedGradientField_eq_testVector`, proved on every
sub-cube of the family from `ShellLawPrefix` and `ShellLawJ2`; the
translation-invariance half of that proof,
`integral_sigmaStarInvCoarse_openCubeSet_eq`, applies verbatim at the
coefficient cutoff level `ℓ` of the proxy and closes the gap there too.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `L²` data on sub-cubes -/

/-- A vector field that is `L²` on the large open cube is `L²` on every
sub-cube of the scale-`n` family. -/
theorem memVectorL2_subcube {n m : ℕ} {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d n m) {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) F) :
    MemVectorL2 (openCubeSet z) F :=
  memVectorL2_mono (openCubeSet_subset_of_mem_descendantsAtDepth hz) hF

/-- `L^q` membership transfers from the large open cube to a sub-cube. -/
theorem memLp_subcube {E : Type*} [NormedAddCommGroup E] {n m : ℕ} {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d n m) {f : Vec d → E} {q : ℝ≥0∞}
    (hf : MemLp f q (volume.restrict (openCubeSet (originCube d (m : ℤ))))) :
    MemLp f q (volume.restrict (openCubeSet z)) :=
  hf.mono_measure
    (Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth hz))

/-- An `L²` field has finite normalized cube norm. -/
theorem cubeLpENorm_ne_top_of_memLp {E : Type*} [NormedAddCommGroup E]
    {Q : TriadicCube d} {f : Vec d → E}
    (hf : MemLp f 2 (volume.restrict (openCubeSet Q))) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 f ≠ ⊤ := by
  have hmem : MemLp f 2 (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hmem.eLpNorm_ne_top

/-- An `L²` vector field has finite normalized cube norm. -/
theorem vecCubeLpENorm_ne_top {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) : vecCubeLpENorm Q 2 F ≠ ⊤ :=
  cubeLpENorm_ne_top_of_memLp (memHilbertVectorL2_hilbertifyVecField hF)

/-- The pairing of two `L²` vector fields is integrable. -/
theorem integrableOn_vecDot {U : Set (Vec d)} {a b : Vec d → Vec d}
    (ha : MemVectorL2 U a) (hb : MemVectorL2 U b) :
    IntegrableOn (fun y => vecDot (a y) (b y)) U volume := by
  have h : (fun y => vecDot (a y) (b y)) = fun y => ∑ i, a y i * b y i := rfl
  rw [h]
  refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
  exact (memL2On_component_of_memVectorL2 ha i).integrable_mul
    (memL2On_component_of_memVectorL2 hb i)

/-! ## Cauchy-Schwarz in the sample -/

/-- **Cauchy-Schwarz in the sample**, in `ℝ≥0∞`: a real function dominated
pointwise by a product of two `ℝ≥0∞` factors has its integral dominated by the
product of the two `L²` norms of the factors. -/
theorem ofReal_abs_integral_le {α : Type*} [MeasurableSpace α] {mu : Measure α}
    {f : α → ℝ} {A B : α → ℝ≥0∞}
    (hA : AEMeasurable A mu) (hB : AEMeasurable B mu)
    (hbd : ∀ a, ENNReal.ofReal |f a| ≤ A a * B a) :
    ENNReal.ofReal |∫ a, f a ∂mu| ≤
      (∫⁻ a, A a ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) *
        (∫⁻ a, B a ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) := by
  by_cases hint : Integrable f mu
  · have h1 : ENNReal.ofReal |∫ a, f a ∂mu| ≤ ∫⁻ a, ‖f a‖ₑ ∂mu := by
      calc ENNReal.ofReal |∫ a, f a ∂mu|
          ≤ ENNReal.ofReal (∫ a, ‖f a‖ ∂mu) :=
            ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm f)
        _ = ∫⁻ a, ‖f a‖ₑ ∂mu := ofReal_integral_norm_eq_lintegral_enorm hint
    have h2 : ∫⁻ a, ‖f a‖ₑ ∂mu ≤ ∫⁻ a, A a * B a ∂mu := by
      refine lintegral_mono fun a => ?_
      rw [Real.enorm_eq_ofReal_abs]
      exact hbd a
    have h3 : ∫⁻ a, A a * B a ∂mu ≤
        (∫⁻ a, A a ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) *
          (∫⁻ a, B a ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq mu Real.HolderConjugate.two_two hA hB
    have hrw : ∀ g : α → ℝ≥0∞, (∫⁻ a, g a ^ (2 : ℝ) ∂mu) = ∫⁻ a, g a ^ (2 : ℕ) ∂mu := by
      intro g
      exact lintegral_congr fun a => by rw [← ENNReal.rpow_natCast (g a) 2]; norm_num
    rw [hrw A, hrw B] at h3
    exact le_trans h1 (le_trans h2 h3)
  · rw [integral_undef hint]
    simp

/-- The real form of `ofReal_abs_integral_le` against two explicit bounds on
the annealed `L²` norms of the factors. -/
theorem abs_integral_le_of_bound {α : Type*} [MeasurableSpace α] {mu : Measure α}
    {f : α → ℝ} {A B : α → ℝ≥0∞} {b₁ b₂ : ℝ}
    (hA : AEMeasurable A mu) (hB : AEMeasurable B mu)
    (hbd : ∀ a, ENNReal.ofReal |f a| ≤ A a * B a)
    (hAfin : (∫⁻ a, A a ^ (2 : ℕ) ∂mu) ≠ ⊤) (hBfin : (∫⁻ a, B a ^ (2 : ℕ) ∂mu) ≠ ⊤)
    (h₁ : (∫⁻ a, A a ^ (2 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 2) ≤ b₁)
    (h₂ : (∫⁻ a, B a ^ (2 : ℕ) ∂mu).toReal ^ ((1 : ℝ) / 2) ≤ b₂)
    (hb₁ : 0 ≤ b₁) :
    |∫ a, f a ∂mu| ≤ b₁ * b₂ := by
  have hkey := ofReal_abs_integral_le hA hB hbd
  have hAne : (∫⁻ a, A a ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAfin
  have hBne : (∫⁻ a, B a ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin
  have hmono := ENNReal.toReal_mono (ENNReal.mul_ne_top hAne hBne) hkey
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hmono
  refine hmono.trans (mul_le_mul h₁ h₂ ?_ hb₁)
  exact Real.rpow_nonneg ENNReal.toReal_nonneg _

/-! ## Cauchy-Schwarz and Jensen on a cube -/

/-- The absolute Cauchy-Schwarz bound on a cube, in `ℝ≥0∞`. -/
theorem ofReal_abs_volumeAverage_vecDot_le {Q : TriadicCube d} {a b : Vec d → Vec d}
    (ha : MemVectorL2 (openCubeSet Q) a) (hb : MemVectorL2 (openCubeSet Q) b) :
    ENNReal.ofReal |volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))| ≤
      vecCubeLpENorm Q 2 a * vecCubeLpENorm Q 2 b := by
  rcases le_total 0 (volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x))) with h | h
  · rw [abs_of_nonneg h]
    exact ofReal_volumeAverage_openCubeSet_vecDot_le ha hb
  · rw [abs_of_nonpos h]
    have hneg := ofReal_volumeAverage_openCubeSet_vecDot_le ha.neg hb
    have hng : vecCubeLpENorm Q 2 (-a) = vecCubeLpENorm Q 2 a := vecCubeLpENorm_neg Q 2 a
    rw [hng] at hneg
    have heq : volumeAverage (openCubeSet Q) (fun x => vecDot ((-a) x) (b x)) =
        -volumeAverage (openCubeSet Q) (fun x => vecDot (a x) (b x)) := by
      have h1 : volumeAverage (openCubeSet Q) (fun x => vecDot ((-a) x) (b x)) =
          volumeAverage (openCubeSet Q) (fun x => -vecDot (a x) (b x)) :=
        congrArg (volumeAverage (openCubeSet Q))
          (funext fun x => vecDot_neg_left (a x) (b x))
      rw [h1]
      simp only [volumeAverage, integral_neg, mul_neg]
    rw [heq] at hneg
    exact hneg

/-- **Jensen for a probability measure**: the squared Euclidean magnitude of a
vector-valued mean is at most the mean of the squared magnitudes. -/
theorem ofReal_vecNormSq_integral_le {α : Type*} [MeasurableSpace α] {mu : Measure α}
    [IsProbabilityMeasure mu] {V : α → Vec d}
    (hV : ∀ i : Fin d, Integrable (fun a => V a i) mu) :
    ENNReal.ofReal (vecNormSq (∫ a, V a ∂mu)) ≤
      ∫⁻ a, ENNReal.ofReal (vecNormSq (V a)) ∂mu := by
  classical
  have hone : ∫⁻ _a : α, (1 : ℝ≥0∞) ^ (2 : ℕ) ∂mu = 1 := by
    rw [one_pow, lintegral_const, one_mul, measure_univ]
  have hcomp : ∀ i : Fin d,
      ENNReal.ofReal (((∫ a, V a ∂mu) i) ^ (2 : ℕ)) ≤
        ∫⁻ a, ‖V a i‖ₑ ^ (2 : ℕ) ∂mu := by
    intro i
    have hAi : AEMeasurable (fun a : α => ‖V a i‖ₑ) mu := (hV i).aestronglyMeasurable.enorm
    have hb : ∀ a : α, ENNReal.ofReal |V a i| ≤ ‖V a i‖ₑ * 1 := by
      intro a
      rw [mul_one, Real.enorm_eq_ofReal_abs]
    have hkey := ofReal_abs_integral_le (mu := mu) (f := fun a : α => V a i)
      (A := fun a : α => ‖V a i‖ₑ) (B := fun _ : α => (1 : ℝ≥0∞))
      hAi aemeasurable_const hb
    rw [hone, ENNReal.one_rpow, mul_one] at hkey
    rw [MeasureTheory.eval_integral (f := V) hV i]
    calc ENNReal.ofReal ((∫ a, V a i ∂mu) ^ (2 : ℕ))
        = (ENNReal.ofReal |∫ a, V a i ∂mu|) ^ (2 : ℕ) := by
          rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      _ ≤ ((∫⁻ a, ‖V a i‖ₑ ^ (2 : ℕ) ∂mu) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) :=
          pow_le_pow_left' hkey 2
      _ = ∫⁻ a, ‖V a i‖ₑ ^ (2 : ℕ) ∂mu := by
          rw [← ENNReal.rpow_natCast (_ ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
          norm_num
  have hsum : ENNReal.ofReal (vecNormSq (∫ a, V a ∂mu)) =
      ∑ i : Fin d, ENNReal.ofReal (((∫ a, V a ∂mu) i) ^ (2 : ℕ)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    refine congrArg ENNReal.ofReal ?_
    show vecDot _ _ = _
    exact Finset.sum_congr rfl fun i _ => (sq _).symm
  have hlin : ∑ i : Fin d, ∫⁻ a, ‖V a i‖ₑ ^ (2 : ℕ) ∂mu =
      ∫⁻ a, ENNReal.ofReal (vecNormSq (V a)) ∂mu := by
    rw [← lintegral_finsetSum' _
      (fun i _ => ((hV i).aestronglyMeasurable.enorm).pow_const 2)]
    refine lintegral_congr fun a => ?_
    have hpt : ∀ b : Fin d, ‖V a b‖ₑ ^ (2 : ℕ) = ENNReal.ofReal ((V a b) ^ (2 : ℕ)) := by
      intro b
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => hpt b),
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (V a i))]
    refine congrArg ENNReal.ofReal ?_
    show _ = vecDot (V a) (V a)
    exact Finset.sum_congr rfl fun i _ => sq _
  rw [hsum, ← hlin]
  exact Finset.sum_le_sum fun i _ => hcomp i

/-- **Jensen on a cube**: the squared magnitude of the cube average of an `L²`
vector field is at most its squared normalized `L̲²` norm. -/
theorem ofReal_vecNormSq_volumeAverageVec_le {Q : TriadicCube d} {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet Q) G) :
    ENNReal.ofReal (vecNormSq (volumeAverageVec (openCubeSet Q) G)) ≤
      vecCubeLpENorm Q 2 G ^ (2 : ℕ) := by
  classical
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_ne le_top (volume_openCubeSet_ne_top Q)⟩
  have hV : ∀ i : Fin d, Integrable (fun x : Vec d => G x i) (normalizedCubeMeasure Q) := by
    intro i
    have hm : MemLp (fun x : Vec d => G x i) 2 (normalizedCubeMeasure Q) := by
      rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
      exact (memL2On_component_of_memVectorL2 hG i).smul_measure ENNReal.ofReal_ne_top
    exact hm.integrable (by norm_num)
  have hval : volumeAverageVec (openCubeSet Q) G = ∫ x, G x ∂normalizedCubeMeasure Q := by
    funext i
    rw [MeasureTheory.eval_integral (f := G) hV i]
    exact volumeAverage_openCubeSet_eq_integral_normalizedCubeMeasure Q (fun x => G x i)
  rw [hval, vecCubeLpENorm_two_sq Q G
    (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 hG)]
  refine le_trans (ofReal_vecNormSq_integral_le hV) ?_
  exact le_of_eq (lintegral_congr fun x => (enorm_ofVec_sq (G x)).symm)

/-- Subtracting a constant vector from a field subtracts it from the cube
average. -/
theorem volumeAverageVec_sub_const {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : ∀ i, IntegrableOn (fun x => F x i) (openCubeSet Q) volume) (c : Vec d) :
    volumeAverageVec (openCubeSet Q) (fun x => F x - c) =
      volumeAverageVec (openCubeSet Q) F - c := by
  funext i
  exact volumeAverage_sub_const (volume_openCubeSet_ne_zero Q) (volume_openCubeSet_ne_top Q)
    (hF i) (c i)

private theorem le_of_sq_le_sq' {a b : ℝ≥0∞} (h : a ^ (2 : ℕ) ≤ b ^ (2 : ℕ)) : a ≤ b := by
  by_contra hc
  push Not at hc
  exact absurd h (not_le.2 (ENNReal.pow_lt_pow_left (by norm_num) hc))

/-- **Centring at the cube mean costs a factor two.** -/
theorem vecCubeLpENorm_sub_average_le {Q : TriadicCube d} {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet Q) G) (c : Vec d) :
    vecCubeLpENorm Q 2 (fun x => G x - volumeAverageVec (openCubeSet Q) G) ≤
      2 * vecCubeLpENorm Q 2 (fun x => G x - c) := by
  have : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_ne le_top (volume_openCubeSet_ne_top Q)⟩
  have hHL2 : MemVectorL2 (openCubeSet Q) (fun x => G x - c) := memVectorL2_sub_const c hG
  have hint : ∀ i, IntegrableOn (fun x => G x i) (openCubeSet Q) volume := fun i =>
    (memL2On_component_of_memVectorL2 hG i).integrable (by norm_num)
  have havg : volumeAverageVec (openCubeSet Q) (fun x => G x - c) =
      volumeAverageVec (openCubeSet Q) G - c := volumeAverageVec_sub_const hint c
  have hrw : (fun x => G x - volumeAverageVec (openCubeSet Q) G) =
      fun x => (G x - c) + (-(volumeAverageVec (openCubeSet Q) (fun y => G y - c))) := by
    funext x
    rw [havg]
    abel
  have hconst : MemVectorL2 (openCubeSet Q)
      (fun _ : Vec d => -(volumeAverageVec (openCubeSet Q) (fun y => G y - c))) :=
    memVectorL2_const _
  have htri := vecCubeLpENorm_add_le (Q := Q) (q := 2)
      (F := fun x => G x - c)
      (G := fun _ : Vec d => -(volumeAverageVec (openCubeSet Q) (fun y => G y - c)))
      (by norm_num) (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 hHL2)
      (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 hconst)
  have hneg : vecCubeLpENorm Q 2
      (fun _ : Vec d => -(volumeAverageVec (openCubeSet Q) (fun y => G y - c))) =
      vecCubeLpENorm Q 2
        (fun _ : Vec d => volumeAverageVec (openCubeSet Q) (fun y => G y - c)) :=
    vecCubeLpENorm_neg Q 2
      (fun _ : Vec d => volumeAverageVec (openCubeSet Q) (fun y => G y - c))
  have hjen : vecCubeLpENorm Q 2
      (fun _ : Vec d => volumeAverageVec (openCubeSet Q) (fun y => G y - c)) ≤
      vecCubeLpENorm Q 2 (fun x => G x - c) := by
    refine le_of_sq_le_sq' ?_
    rw [vecCubeLpENorm_const_sq Q (volumeAverageVec (openCubeSet Q) (fun y => G y - c))]
    exact ofReal_vecNormSq_volumeAverageVec_le hHL2
  rw [hrw, two_mul]
  exact htri.trans (add_le_add le_rfl (hneg.trans_le hjen))

/-! ## The sub-cube decomposition of the squared normalized norm -/

/-- The squared normalized `L̲²` norm on the large cube is the plain average of
the squared normalized norms on the scale-`n` sub-cubes, in real form. -/
theorem sum_cubeLpENorm_sq_subcubes {E : Type*} [NormedAddCommGroup E] {n m : ℕ}
    (f : Vec d → E)
    (hfin : ∀ z ∈ largeCubeSubcubes d n m,
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2 f ≠ ⊤) :
    ∑ z ∈ largeCubeSubcubes d n m,
        ((SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2 f).toReal) ^ (2 : ℕ) =
      ((largeCubeSubcubes d n m).card : ℝ) *
        ((SuperdiffusionCLT.Section2.Norms.cubeLpENorm
          (originCube d (m : ℤ)) 2 f).toReal) ^ (2 : ℕ) := by
  classical
  have hdesc : descendantsAtDepth (originCube d (m : ℤ)) (m - n) = largeCubeSubcubes d n m := rfl
  have hid := cubeLpENorm_two_sq_eq_inv_card_mul_sum (Q := originCube d (m : ℤ)) (m - n) f
  rw [hdesc] at hid
  have hcardpos : (0 : ℝ) < ((largeCubeSubcubes d n m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (largeCubeSubcubes_nonempty d n m)
  have hStoReal : (∑ z ∈ largeCubeSubcubes d n m,
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2 f ^ (2 : ℕ)).toReal =
      ∑ z ∈ largeCubeSubcubes d n m,
        ((SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2 f).toReal) ^ (2 : ℕ) := by
    rw [ENNReal.toReal_sum (fun z hz => ENNReal.pow_ne_top (hfin z hz))]
    exact Finset.sum_congr rfl fun z _ => ENNReal.toReal_pow _ _
  have hcast := congrArg ENNReal.toReal hid
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, hStoReal,
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.2 hcardpos))] at hcast
  rw [hcast]
  field_simp

/-- The vector-field form of `sum_cubeLpENorm_sq_subcubes`. -/
theorem sum_vecCubeLpENorm_sq_subcubes {n m : ℕ} (F : Vec d → Vec d)
    (hfin : ∀ z ∈ largeCubeSubcubes d n m, vecCubeLpENorm z 2 F ≠ ⊤) :
    ∑ z ∈ largeCubeSubcubes d n m, ((vecCubeLpENorm z 2 F).toReal) ^ (2 : ℕ) =
      ((largeCubeSubcubes d n m).card : ℝ) *
        ((vecCubeLpENorm (originCube d (m : ℤ)) 2 F).toReal) ^ (2 : ℕ) :=
  sum_cubeLpENorm_sq_subcubes (hilbertifyVecField F) hfin

/-! ## The centred cubewise average -/

/-- **The centred cubewise average**: after subtracting the cube
mean of `Rf` and the cube mean of `UT` on each sub-cube, the lattice average of
the pairing is bounded by the two large-cube norms, with the Poincare constant
of the sub-cubes.  The three ingredients are the Cauchy-Schwarz inequality on a
sub-cube, the discrete Cauchy-Schwarz inequality over the lattice, and the
sub-cube decomposition `sum_cubeLpENorm_sq_subcubes`. -/
theorem centred_avsum_bound {n m : ℕ}
    {Rf UT : Vec d → Vec d} {DRm : Vec d → HilbertMat d} {pT : Vec d} {K : ℝ} (hK : 0 ≤ K)
    (hR : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) Rf)
    (hT : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) UT)
    (hDR : MemLp DRm 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)))))
    (hpoin : ∀ z ∈ largeCubeSubcubes d n m,
      vecCubeLpENorm z 2 (fun x => Rf x - volumeAverageVec (openCubeSet z) Rf) ≤
        ENNReal.ofReal K * SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2 DRm) :
    |((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d n m,
          volumeAverage (openCubeSet z)
            (fun y => vecDot (Rf y - volumeAverageVec (openCubeSet z) Rf)
              (UT y - volumeAverageVec (openCubeSet z) UT))| ≤
      2 * K *
        (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
          (originCube d (m : ℤ)) 2 DRm).toReal *
        (vecCubeLpENorm (originCube d (m : ℤ)) 2 (fun x => UT x - pT)).toReal := by
  classical
  have hcardpos : (0 : ℝ) < ((largeCubeSubcubes d n m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (largeCubeSubcubes_nonempty d n m)
  set A : TriadicCube d → ℝ := fun z =>
    (vecCubeLpENorm z 2 (fun x => Rf x - volumeAverageVec (openCubeSet z) Rf)).toReal with hA
  set B : TriadicCube d → ℝ := fun z =>
    (vecCubeLpENorm z 2 (fun x => UT x - volumeAverageVec (openCubeSet z) UT)).toReal with hB
  set D : TriadicCube d → ℝ := fun z =>
    (SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2 DRm).toReal with hD
  set E : TriadicCube d → ℝ := fun z =>
    (vecCubeLpENorm z 2 (fun x => UT x - pT)).toReal with hE
  have hterm : ∀ z ∈ largeCubeSubcubes d n m,
      |volumeAverage (openCubeSet z)
        (fun y => vecDot (Rf y - volumeAverageVec (openCubeSet z) Rf)
          (UT y - volumeAverageVec (openCubeSet z) UT))| ≤ A z * B z := by
    intro z hz
    have ha : MemVectorL2 (openCubeSet z)
        (fun x => Rf x - volumeAverageVec (openCubeSet z) Rf) :=
      memVectorL2_sub_const _ (memVectorL2_subcube hz hR)
    have hb : MemVectorL2 (openCubeSet z)
        (fun x => UT x - volumeAverageVec (openCubeSet z) UT) :=
      memVectorL2_sub_const _ (memVectorL2_subcube hz hT)
    exact abs_volumeAverage_openCubeSet_vecDot_le ha hb
      (vecCubeLpENorm_ne_top ha) (vecCubeLpENorm_ne_top hb)
  have hstep1 : |((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
      ∑ z ∈ largeCubeSubcubes d n m,
        volumeAverage (openCubeSet z)
          (fun y => vecDot (Rf y - volumeAverageVec (openCubeSet z) Rf)
            (UT y - volumeAverageVec (openCubeSet z) UT))| ≤
      ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d n m, A z * B z := by
    rw [abs_mul, abs_of_nonneg (le_of_lt (inv_pos.2 hcardpos))]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.2 hcardpos))
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hDfin : ∀ z ∈ largeCubeSubcubes d n m,
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2 DRm ≠ ⊤ :=
    fun z hz => cubeLpENorm_ne_top_of_memLp (memLp_subcube hz hDR)
  have hEfin : ∀ z ∈ largeCubeSubcubes d n m,
      vecCubeLpENorm z 2 (fun x => UT x - pT) ≠ ⊤ :=
    fun z hz => vecCubeLpENorm_ne_top (memVectorL2_sub_const pT (memVectorL2_subcube hz hT))
  have hAle : ∀ z ∈ largeCubeSubcubes d n m, A z ≤ K * D z := by
    intro z hz
    have hle := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hDfin z hz)) (hpoin z hz)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] at hle
  have hBle : ∀ z ∈ largeCubeSubcubes d n m, B z ≤ 2 * E z := by
    intro z hz
    have hle := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by norm_num) (hEfin z hz))
      (vecCubeLpENorm_sub_average_le (memVectorL2_subcube hz hT) pT)
    rwa [ENNReal.toReal_mul, show ((2 : ℝ≥0∞)).toReal = (2 : ℝ) by norm_num] at hle
  have hAsum : ∑ z ∈ largeCubeSubcubes d n m, A z ^ (2 : ℕ) ≤
      K ^ (2 : ℕ) * (((largeCubeSubcubes d n m).card : ℝ) *
        (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
          (originCube d (m : ℤ)) 2 DRm).toReal ^ (2 : ℕ)) := by
    rw [← sum_cubeLpENorm_sq_subcubes (n := n) DRm hDfin, Finset.mul_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    calc A z ^ (2 : ℕ) ≤ (K * D z) ^ (2 : ℕ) :=
          pow_le_pow_left₀ ENNReal.toReal_nonneg (hAle z hz) 2
      _ = K ^ (2 : ℕ) * D z ^ (2 : ℕ) := by rw [mul_pow]
  have hBsum : ∑ z ∈ largeCubeSubcubes d n m, B z ^ (2 : ℕ) ≤
      (2 : ℝ) ^ (2 : ℕ) * (((largeCubeSubcubes d n m).card : ℝ) *
        (vecCubeLpENorm (originCube d (m : ℤ)) 2 (fun x => UT x - pT)).toReal ^ (2 : ℕ)) := by
    rw [← sum_vecCubeLpENorm_sq_subcubes (n := n) (fun x => UT x - pT) hEfin, Finset.mul_sum]
    refine Finset.sum_le_sum fun z hz => ?_
    calc B z ^ (2 : ℕ) ≤ (2 * E z) ^ (2 : ℕ) :=
          pow_le_pow_left₀ ENNReal.toReal_nonneg (hBle z hz) 2
      _ = (2 : ℝ) ^ (2 : ℕ) * E z ^ (2 : ℕ) := by rw [mul_pow]
  set Dm : ℝ := (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
    (originCube d (m : ℤ)) 2 DRm).toReal with hDm
  set Em : ℝ := (vecCubeLpENorm (originCube d (m : ℤ)) 2 (fun x => UT x - pT)).toReal with hEm
  have hDm0 : 0 ≤ Dm := ENNReal.toReal_nonneg
  have hEm0 : 0 ≤ Em := ENNReal.toReal_nonneg
  have hsqrtN : Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
      Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) =
      ((largeCubeSubcubes d n m).card : ℝ) := Real.mul_self_sqrt hcardpos.le
  have hsqA : Real.sqrt (∑ z ∈ largeCubeSubcubes d n m, A z ^ (2 : ℕ)) ≤
      K * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Dm := by
    have h1 := Real.sqrt_le_sqrt hAsum
    have h2 : K ^ (2 : ℕ) * (((largeCubeSubcubes d n m).card : ℝ) * Dm ^ (2 : ℕ)) =
        (K * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Dm) ^ (2 : ℕ) := by
      have hexp : (K * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Dm) ^ (2 : ℕ) =
          K ^ (2 : ℕ) * (Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
            Real.sqrt ((largeCubeSubcubes d n m).card : ℝ)) * Dm ^ (2 : ℕ) := by ring
      rw [hexp, hsqrtN]
      ring
    rw [h2, Real.sqrt_sq (mul_nonneg (mul_nonneg hK (Real.sqrt_nonneg _)) hDm0)] at h1
    exact h1
  have hsqB : Real.sqrt (∑ z ∈ largeCubeSubcubes d n m, B z ^ (2 : ℕ)) ≤
      2 * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Em := by
    have h1 := Real.sqrt_le_sqrt hBsum
    have h2 : (2 : ℝ) ^ (2 : ℕ) * (((largeCubeSubcubes d n m).card : ℝ) * Em ^ (2 : ℕ)) =
        (2 * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Em) ^ (2 : ℕ) := by
      have hexp : (2 * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Em) ^ (2 : ℕ) =
          (2 : ℝ) ^ (2 : ℕ) * (Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
            Real.sqrt ((largeCubeSubcubes d n m).card : ℝ)) * Em ^ (2 : ℕ) := by ring
      rw [hexp, hsqrtN]
      ring
    rw [h2, Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hEm0)] at h1
    exact h1
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (largeCubeSubcubes d n m) A B
  have hprod : Real.sqrt (∑ z ∈ largeCubeSubcubes d n m, A z ^ (2 : ℕ)) *
      Real.sqrt (∑ z ∈ largeCubeSubcubes d n m, B z ^ (2 : ℕ)) ≤
      (K * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Dm) *
        (2 * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Em) :=
    mul_le_mul hsqA hsqB (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg hK (Real.sqrt_nonneg _)) hDm0)
  have harith : ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
      ((K * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Dm) *
        (2 * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Em)) = 2 * K * Dm * Em := by
    have hre : ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        ((K * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Dm) *
          (2 * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Em)) =
        ((Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
            Real.sqrt ((largeCubeSubcubes d n m).card : ℝ)) *
          ((largeCubeSubcubes d n m).card : ℝ)⁻¹) * (2 * K * Dm * Em) := by ring
    rw [hre, hsqrtN, mul_inv_cancel₀ hcardpos.ne', one_mul]
  calc |((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d n m,
          volumeAverage (openCubeSet z)
            (fun y => vecDot (Rf y - volumeAverageVec (openCubeSet z) Rf)
              (UT y - volumeAverageVec (openCubeSet z) UT))|
      ≤ ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
          ∑ z ∈ largeCubeSubcubes d n m, A z * B z := hstep1
    _ ≤ ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
          ((K * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Dm) *
            (2 * Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) * Em)) :=
        mul_le_mul_of_nonneg_left (hCS.trans hprod) (le_of_lt (inv_pos.2 hcardpos))
    _ = 2 * K * Dm * Em := harith

/-! ## `l.RHS.term2#poincare-per-cube` -/

/-- The squared normalized cube norm as an un-normalized lower integral. -/
private theorem cubeLpENorm_two_sq_eq {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (f : Vec d → E) (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2 f ^ (2 : ℕ) =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) *
        ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂(volume.restrict (openCubeSet Q)) := by
  rw [SuperdiffusionCLT.Section2.Norms.cubeLpENorm, eLpNorm_two_sq _ _ hf,
    normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet, lintegral_smul_measure,
    smul_eq_mul]

/-- Pointwise: the sum over the rows of the squared ambient (supremum) norms is
at most the squared Frobenius norm of the Jacobian. -/
private theorem sum_enorm_sq_le_hilbertMat (DF : Fin d → Vec d → Vec d) (x : Vec d) :
    ∑ i : Fin d, ‖DF i x‖ₑ ^ (2 : ℕ) ≤
      ‖HilbertMat.ofMat (fun i j => DF i x j)‖ₑ ^ (2 : ℕ) := by
  have hrow : ∀ i : Fin d, ‖DF i x‖ₑ ^ (2 : ℕ) ≤ ENNReal.ofReal (vecNormSq (DF i x)) := by
    intro i
    have hle : ‖DF i x‖ ≤ vecNorm (DF i x) :=
      (pi_norm_le_iff_of_nonneg (vecNorm_nonneg _)).2 fun j => abs_apply_le_vecNorm (DF i x) j
    calc ‖DF i x‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (‖DF i x‖ ^ (2 : ℕ)) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (vecNorm (DF i x) ^ (2 : ℕ)) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hle 2)
      _ = ENNReal.ofReal (vecNormSq (DF i x)) := by rw [vecNorm_sq_eq_vecNormSq]
  have hmat : ‖HilbertMat.ofMat (fun i j => DF i x j)‖ₑ ^ (2 : ℕ) =
      ENNReal.ofReal (∑ i : Fin d, vecNormSq (DF i x)) := by
    have h1 : ‖HilbertMat.ofMat (fun i j => DF i x j)‖ ^ (2 : ℕ) =
        ∑ i : Fin d, vecNormSq (DF i x) := by
      refine (norm_sq_hilbertMat_ofMat _).trans ?_
      exact Finset.sum_congr rfl fun i _ => rfl
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1]
  rw [hmat]
  refine le_trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow i) ?_
  exact le_of_eq (ENNReal.ofReal_sum_of_nonneg (fun i _ => vecNormSq_nonneg (DF i x))).symm

/-- **`l.RHS.term2#poincare-per-cube`**: the Poincare-Wirtinger inequality on one triadic
cube, in the normalized `L̲²` reading, for a vector field `F` whose components carry `H¹`
data `u i` with weak gradients `DF i`.  The constant is `3^{scale} C_d`, with
`C_d` the coercive constant of the centred unit cube; the input is
`Homogenization.scaledTranslatedCubeMeanZeroH1CoerciveEstimate`. -/
theorem poincare_per_cube {Q : TriadicCube d} {F : Vec d → Vec d} {DF : Fin d → Vec d → Vec d}
    (u : Fin d → H1Function (openCubeSet Q))
    (hval : ∀ i, (u i).toFun = fun x => F x i)
    (hgrad : ∀ i, (u i).grad = DF i) :
    vecCubeLpENorm Q 2 (fun x => F x - volumeAverageVec (openCubeSet Q) F) ≤
      ENNReal.ofReal (cubeScaleFactor Q *
          (originCubeMeanZeroH1CoerciveEstimate d 0).constant) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => HilbertMat.ofMat (fun i j => DF i x j)) := by
  classical
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  set C : ℝ := cubeScaleFactor Q * (originCubeMeanZeroH1CoerciveEstimate d 0).constant with hCdef
  have hCeq : (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q).constant = C :=
    scaledTranslatedCubeMeanZeroH1CoerciveEstimate_constant Q
  have hC0 : 0 ≤ C := hCeq ▸ (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q).constant_nonneg
  have hfun : ∀ i : Fin d, (u i).subAverage.toFun =
      fun x => (F x - volumeAverageVec (openCubeSet Q) F) i := by
    intro i
    funext x
    rw [H1Function.subAverage_apply (u i) x, hval i]
    rfl
  have hstep : ∀ i : Fin d,
      eLpNorm (fun x => (F x - volumeAverageVec (openCubeSet Q) F) i) 2
          (volume.restrict (openCubeSet Q)) ≤
        ENNReal.ofReal C * eLpNorm (DF i) 2 (volume.restrict (openCubeSet Q)) := by
    intro i
    have hb := (scaledTranslatedCubeMeanZeroH1CoerciveEstimate Q).bound_subAverage (u i)
    rw [hCeq] at hb
    have hL : ((u i).toMeanZero).valueL2Norm =
        (eLpNorm (u i).subAverage.toFun 2 (volume.restrict (openCubeSet Q))).toReal := by
      show ‖Homogenization.toScalarL2 ((u i).subAverage).memL2‖ = _
      exact MeasureTheory.Lp.norm_toLp _ ((u i).subAverage).memL2
    have hR : ‖(u i).gradToVectorL2‖ =
        (eLpNorm (u i).grad 2 (volume.restrict (openCubeSet Q))).toReal := by
      show ‖Homogenization.toVectorL2 (u i).grad_memVectorL2‖ = _
      exact MeasureTheory.Lp.norm_toLp _ (u i).grad_memVectorL2
    rw [hL, hR, hfun i, hgrad i] at hb
    have hXfin : eLpNorm (fun x => (F x - volumeAverageVec (openCubeSet Q) F) i) 2
        (volume.restrict (openCubeSet Q)) ≠ ⊤ := by
      have hmem := ((u i).subAverage).memL2
      rw [hfun i] at hmem
      exact hmem.eLpNorm_ne_top
    have hYfin : eLpNorm (DF i) 2 (volume.restrict (openCubeSet Q)) ≠ ⊤ := by
      have hmem := (u i).grad_memVectorL2
      rw [hgrad i] at hmem
      exact hmem.eLpNorm_ne_top
    calc eLpNorm (fun x => (F x - volumeAverageVec (openCubeSet Q) F) i) 2
          (volume.restrict (openCubeSet Q))
        = ENNReal.ofReal (eLpNorm (fun x => (F x - volumeAverageVec (openCubeSet Q) F) i) 2
            (volume.restrict (openCubeSet Q))).toReal := (ENNReal.ofReal_toReal hXfin).symm
      _ ≤ ENNReal.ofReal (C * (eLpNorm (DF i) 2 (volume.restrict (openCubeSet Q))).toReal) :=
          ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal C * eLpNorm (DF i) 2 (volume.restrict (openCubeSet Q)) := by
          rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_toReal hYfin]
  have hDFm : ∀ i : Fin d, AEStronglyMeasurable (DF i) (volume.restrict (openCubeSet Q)) := by
    intro i
    have hm := (u i).grad_memVectorL2.aestronglyMeasurable
    rw [hgrad i] at hm
    exact hm
  have hGm : ∀ i : Fin d, AEStronglyMeasurable
      (fun x : Vec d => (F x - volumeAverageVec (openCubeSet Q) F) i)
      (volume.restrict (openCubeSet Q)) := by
    intro i
    have hm := ((u i).subAverage).memL2.aestronglyMeasurable
    rw [hfun i] at hm
    exact hm
  have hmeasG : ∀ i : Fin d, AEMeasurable
      (fun x : Vec d => ‖(F x - volumeAverageVec (openCubeSet Q) F) i‖ₑ ^ (2 : ℕ))
      (volume.restrict (openCubeSet Q)) := by
    intro i
    have hm := ((u i).subAverage).memL2.aestronglyMeasurable
    rw [hfun i] at hm
    exact hm.enorm.pow_const 2
  have hmeasD : ∀ i : Fin d, AEMeasurable (fun x : Vec d => ‖DF i x‖ₑ ^ (2 : ℕ))
      (volume.restrict (openCubeSet Q)) := by
    intro i
    have hm := (u i).grad_memVectorL2.aestronglyMeasurable
    rw [hgrad i] at hm
    exact hm.enorm.pow_const 2
  have hI1 : ∫⁻ x, ENNReal.ofReal (vecNormSq (F x - volumeAverageVec (openCubeSet Q) F))
        ∂(volume.restrict (openCubeSet Q)) =
      ∑ i : Fin d, eLpNorm (fun x => (F x - volumeAverageVec (openCubeSet Q) F) i) 2
        (volume.restrict (openCubeSet Q)) ^ (2 : ℕ) := by
    have hpt : ∀ x : Vec d,
        ENNReal.ofReal (vecNormSq (F x - volumeAverageVec (openCubeSet Q) F)) =
          ∑ i : Fin d, ‖(F x - volumeAverageVec (openCubeSet Q) F) i‖ₑ ^ (2 : ℕ) := by
      intro x
      have hcomp : ∀ i : Fin d,
          ‖(F x - volumeAverageVec (openCubeSet Q) F) i‖ₑ ^ (2 : ℕ) =
            ENNReal.ofReal (((F x - volumeAverageVec (openCubeSet Q) F) i) ^ (2 : ℕ)) := by
        intro i
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hcomp i),
        ← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
      refine congrArg ENNReal.ofReal ?_
      show vecDot _ _ = _
      exact Finset.sum_congr rfl fun i _ => (sq _).symm
    rw [lintegral_congr hpt, lintegral_finsetSum' _ (fun i _ => hmeasG i)]
    exact Finset.sum_congr rfl fun i _ => (eLpNorm_two_sq _ _ (hGm i)).symm
  have hI2 : ∑ i : Fin d, eLpNorm (DF i) 2 (volume.restrict (openCubeSet Q)) ^ (2 : ℕ) ≤
      ∫⁻ x, ‖HilbertMat.ofMat (fun i j => DF i x j)‖ₑ ^ (2 : ℕ)
        ∂(volume.restrict (openCubeSet Q)) := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => eLpNorm_two_sq
      (volume.restrict (openCubeSet Q)) (DF i) (hDFm i)),
      ← lintegral_finsetSum' _ (fun i _ => hmeasD i)]
    exact lintegral_mono fun x => sum_enorm_sq_le_hilbertMat DF x
  have hchain : ∫⁻ x, ENNReal.ofReal (vecNormSq (F x - volumeAverageVec (openCubeSet Q) F))
        ∂(volume.restrict (openCubeSet Q)) ≤
      ENNReal.ofReal C ^ (2 : ℕ) *
        ∫⁻ x, ‖HilbertMat.ofMat (fun i j => DF i x j)‖ₑ ^ (2 : ℕ)
          ∂(volume.restrict (openCubeSet Q)) := by
    rw [hI1]
    calc ∑ i : Fin d, eLpNorm (fun x => (F x - volumeAverageVec (openCubeSet Q) F) i) 2
          (volume.restrict (openCubeSet Q)) ^ (2 : ℕ)
        ≤ ∑ i : Fin d, (ENNReal.ofReal C *
            eLpNorm (DF i) 2 (volume.restrict (openCubeSet Q))) ^ (2 : ℕ) :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left' (hstep i) 2
      _ = ENNReal.ofReal C ^ (2 : ℕ) *
            ∑ i : Fin d, eLpNorm (DF i) 2 (volume.restrict (openCubeSet Q)) ^ (2 : ℕ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => mul_pow _ _ 2
      _ ≤ ENNReal.ofReal C ^ (2 : ℕ) *
            ∫⁻ x, ‖HilbertMat.ofMat (fun i j => DF i x j)‖ₑ ^ (2 : ℕ)
              ∂(volume.restrict (openCubeSet Q)) :=
          mul_le_mul_of_nonneg_left hI2 zero_le
  refine le_of_sq_le_sq' ?_
  have hAvec : AEStronglyMeasurable
      (hilbertifyVecField (fun x => F x - volumeAverageVec (openCubeSet Q) F))
      (normalizedCubeMeasure Q) := by
    refine aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 (Q := Q) ?_
    refine MeasureTheory.MemLp.of_eval fun i => ?_
    have hmem := ((u i).subAverage).memL2
    rw [hfun i] at hmem
    exact hmem
  have hAmat : AEStronglyMeasurable (fun x => HilbertMat.ofMat (fun i j => DF i x j))
      (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    refine AEStronglyMeasurable.smul_measure ?_ _
    have hM : AEStronglyMeasurable (fun x => (fun i j => DF i x j : Mat d))
        (volume.restrict (openCubeSet Q)) :=
      (AEMeasurable.of_eval fun i => AEMeasurable.of_eval fun j =>
        (measurable_pi_apply j).comp_aemeasurable (hDFm i).aemeasurable).aestronglyMeasurable
    exact (HilbertMat.continuousLinearEquivMat d).symm.continuous.comp_aestronglyMeasurable hM
  have hLHS : vecCubeLpENorm Q 2 (fun x => F x - volumeAverageVec (openCubeSet Q) F) ^ (2 : ℕ) =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (vecNormSq (F x - volumeAverageVec (openCubeSet Q) F))
          ∂(volume.restrict (openCubeSet Q)) := by
    rw [vecCubeLpENorm, cubeLpENorm_two_sq_eq _ _ hAvec]
    exact congrArg (fun t => ENNReal.ofReal ((cubeVolume Q)⁻¹) * t)
      (lintegral_congr fun x => enorm_ofVec_sq _)
  rw [hLHS, mul_pow, cubeLpENorm_two_sq_eq _ _ hAmat]
  calc ENNReal.ofReal ((cubeVolume Q)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (vecNormSq (F x - volumeAverageVec (openCubeSet Q) F))
          ∂(volume.restrict (openCubeSet Q))
      ≤ ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          (ENNReal.ofReal C ^ (2 : ℕ) *
            ∫⁻ x, ‖HilbertMat.ofMat (fun i j => DF i x j)‖ₑ ^ (2 : ℕ)
              ∂(volume.restrict (openCubeSet Q))) :=
        mul_le_mul_of_nonneg_left hchain zero_le
    _ = ENNReal.ofReal C ^ (2 : ℕ) * (ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          ∫⁻ x, ‖HilbertMat.ofMat (fun i j => DF i x j)‖ₑ ^ (2 : ℕ)
            ∂(volume.restrict (openCubeSet Q))) := by ring

/-! ## `l.RHS.term2#independence-decoupling` -/

/-- **`l.RHS.term2#independence-decoupling`**: on a cube `Q`,
the expectation of the pairing of the cube mean of the `F_>`-measurable field
`Rf` against the centred cube mean of the low-shell field `UT` vanishes.  See
the module docstring for the two hypotheses. -/
theorem independence_decoupling {P : ProbabilityMeasure (ShellSeq d)} {Q : TriadicCube d}
    {Rf UT : ShellSeq d → Vec d → Vec d} {pT : Vec d}
    (hindep : ProbabilityTheory.IndepFun
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega))
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (UT omega)) P.toMeasure)
    (hRint : ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i) P.toMeasure)
    (hTint : ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (UT omega) i) P.toMeasure)
    (hmean : ∀ i : Fin d,
      ∫ omega : ShellSeq d, volumeAverageVec (openCubeSet Q) (UT omega) i ∂P.toMeasure = pT i) :
    ∫ omega : ShellSeq d,
        vecDot (volumeAverageVec (openCubeSet Q) (Rf omega))
          (volumeAverageVec (openCubeSet Q) (UT omega) - pT) ∂P.toMeasure = 0 := by
  classical
  have hcomp : ∀ i : Fin d, ProbabilityTheory.IndepFun
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i)
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (UT omega) i)
      P.toMeasure := fun i =>
    hindep.comp (measurable_pi_apply i) (measurable_pi_apply i)
  have hmul : ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i *
        volumeAverageVec (openCubeSet Q) (UT omega) i) P.toMeasure := fun i =>
    (hcomp i).integrable_mul (hRint i) (hTint i)
  have hexp : ∀ i : Fin d,
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i *
          (volumeAverageVec (openCubeSet Q) (UT omega) i - pT i)) =
        fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i *
          volumeAverageVec (openCubeSet Q) (UT omega) i -
          volumeAverageVec (openCubeSet Q) (Rf omega) i * pT i := by
    intro i
    funext omega
    ring
  have hint : ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i *
        (volumeAverageVec (openCubeSet Q) (UT omega) i - pT i)) P.toMeasure := by
    intro i
    rw [hexp i]
    exact (hmul i).sub ((hRint i).mul_const (pT i))
  have hterm : ∀ i : Fin d,
      ∫ omega : ShellSeq d, volumeAverageVec (openCubeSet Q) (Rf omega) i *
        (volumeAverageVec (openCubeSet Q) (UT omega) i - pT i) ∂P.toMeasure = 0 := by
    intro i
    rw [hexp i, integral_sub (hmul i) ((hRint i).mul_const (pT i)),
      (hcomp i).integral_fun_mul_eq_mul_integral (hRint i).aestronglyMeasurable
        (hTint i).aestronglyMeasurable, integral_mul_const, hmean i]
    show (∫ omega : ShellSeq d, volumeAverageVec (openCubeSet Q) (Rf omega) i ∂P.toMeasure) *
        pT i - (∫ omega : ShellSeq d,
          volumeAverageVec (openCubeSet Q) (Rf omega) i ∂P.toMeasure) * pT i = 0
    ring
  have hsplit : ∫ omega : ShellSeq d,
      vecDot (volumeAverageVec (openCubeSet Q) (Rf omega))
        (volumeAverageVec (openCubeSet Q) (UT omega) - pT) ∂P.toMeasure =
      ∑ i : Fin d, ∫ omega : ShellSeq d,
        volumeAverageVec (openCubeSet Q) (Rf omega) i *
          (volumeAverageVec (openCubeSet Q) (UT omega) i - pT i) ∂P.toMeasure :=
    integral_finsetSum _ (fun i _ => hint i)
  rw [hsplit]
  exact Finset.sum_eq_zero fun i _ => hterm i

end

end SuperdiffusionCLT.Section3.Terms
