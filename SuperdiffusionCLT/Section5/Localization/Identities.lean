/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Carriers.BlockOffsetMinimizerB

/-!
# The block pairing on `L²` states and the Euler-Lagrange identity

For an elliptic coefficient `a` on a finite-measure set `U`, the pairing
`Homogenization.blockPairingAverage U a X Y = ⨍_U X · A Y` of two `L²` block states is symmetric,
bilinear and nonnegative on the diagonal (`blockPairingAverage_comm`,
`blockPairingAverage_add_right_of_isBlockL2`, `blockPairingAverage_self_nonneg`), hence satisfies
Cauchy-Schwarz (`blockPairingAverage_sq_le`).

`blockPairingAverage_eq_zero_of_isBlockOffsetMinimizer` is the first-variation identity
`e.localization.euler`: a minimizer of the block energy over `IsBlockOffsetAdmissible U F` is
orthogonal, for the pairing, to every `L²` state with zero potential trace and zero solenoidal
normal trace. It holds for an arbitrary (non-constant) offset `F` with `L²` components.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}

/-- A block state with `L²` components on `U`. -/
def IsBlockL2 (U : Set (Vec d)) (X : BlockState d) : Prop :=
  MemVectorL2 U X.potential ∧ MemVectorL2 U X.flux

@[simp] theorem blockState_add_potential (X Y : BlockState d) (x : Vec d) :
    (X + Y).potential x = X.potential x + Y.potential x := rfl

@[simp] theorem blockState_add_flux (X Y : BlockState d) (x : Vec d) :
    (X + Y).flux x = X.flux x + Y.flux x := rfl

@[simp] theorem blockState_smul_potential (c : ℝ) (X : BlockState d) (x : Vec d) :
    (c • X).potential x = c • X.potential x := rfl

@[simp] theorem blockState_smul_flux (c : ℝ) (X : BlockState d) (x : Vec d) :
    (c • X).flux x = c • X.flux x := rfl

/-- A test field: the class `(L²_{pot,0} × L²_{sol,0})(U)` of the localization lemma. -/
def IsBlockTestField (U : Set (Vec d)) (Y : BlockState d) : Prop :=
  MemVectorL2 U Y.potential ∧ IsPotentialZeroTraceOn U Y.potential ∧
    MemVectorL2 U Y.flux ∧ IsSolenoidalZeroNormalTraceOn U Y.flux

theorem IsBlockL2.memBlockL2 {X : BlockState d} (h : IsBlockL2 U X) : MemBlockL2 U X.eval :=
  memBlockL2_eval_of_components h.1 h.2

theorem IsBlockL2.add {X Y : BlockState d} (hX : IsBlockL2 U X) (hY : IsBlockL2 U Y) :
    IsBlockL2 U (X + Y) :=
  ⟨hX.1.add hY.1, hX.2.add hY.2⟩

theorem IsBlockL2.smul {X : BlockState d} (hX : IsBlockL2 U X) (c : ℝ) :
    IsBlockL2 U (c • X) :=
  ⟨hX.1.const_smul c, hX.2.const_smul c⟩

theorem IsBlockTestField.isBlockL2 {Y : BlockState d} (h : IsBlockTestField U Y) :
    IsBlockL2 U Y :=
  ⟨h.1, h.2.2.1⟩

/-- A test field is the difference of two members of one admissible class. -/
theorem isBlockTestField_of_isBlockOffsetAdmissible {F X : BlockState d}
    (h : IsBlockOffsetAdmissible U F X) :
    IsBlockTestField U (X + (-1 : ℝ) • F) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : (X + (-1 : ℝ) • F).potential = fun x => X.potential x - F.potential x := by
    funext x; simp [sub_eq_add_neg]
  have e2 : (X + (-1 : ℝ) • F).flux = fun x => X.flux x - F.flux x := by
    funext x; simp [sub_eq_add_neg]
  rw [IsBlockTestField, e1, e2]
  exact ⟨h1, h2, h3, h4⟩

/-- Ellipticity and `L²` make the pairing integrand integrable. -/
theorem IsBlockL2.integrableOn_pair [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) {X Y : BlockState d} (hX : IsBlockL2 U X)
    (hY : IsBlockL2 U Y) : MeasureTheory.IntegrableOn (blockPairingIntegrand a X Y) U :=
  blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hX.memBlockL2
    hY.memBlockL2 hEll

/-- Symmetry of the pairing. -/
theorem blockPairingAverage_comm (U : Set (Vec d)) (a : CoeffField d) (X Y : BlockState d) :
    blockPairingAverage U a X Y = blockPairingAverage U a Y X := by
  have h : blockPairingIntegrand a X Y = blockPairingIntegrand a Y X := by
    funext x
    exact blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm (a x) _ _
  unfold blockPairingAverage
  rw [h]

/-- Nonnegativity of the diagonal pairing. -/
theorem blockPairingAverage_self_nonneg (hEll : IsEllipticFieldOn lam Lam U a)
    (X : BlockState d) : 0 ≤ blockPairingAverage U a X X := by
  unfold blockPairingAverage volumeAverage
  refine mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) ?_
  refine MeasureTheory.integral_nonneg_of_ae ?_
  have hmeas := measurableSet_of_isEllipticFieldOn hEll
  filter_upwards [(MeasureTheory.ae_restrict_iff' hmeas).2
    (Filter.Eventually.of_forall fun x hx => hx)] with x hx
  show 0 ≤ blockVecDot (X.potential x, X.flux x)
    (blockMatVecMul (blockMatrixOfCoeff (a x)) (X.potential x, X.flux x))
  by_cases h : (X.potential x, X.flux x) = 0
  · rw [h]
    simp [blockVecDot, vecDot]
  · exact (blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix (hEll.2 x hx) h).le

theorem blockPairingAverage_add_right_of_isBlockL2
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) {X Y Z : BlockState d} (hX : IsBlockL2 U X)
    (hY : IsBlockL2 U Y) (hZ : IsBlockL2 U Z) :
    blockPairingAverage U a X (Y + Z) =
      blockPairingAverage U a X Y + blockPairingAverage U a X Z :=
  blockPairingAverage_add_right U a X Y Z (hX.integrableOn_pair hEll hY)
    (hX.integrableOn_pair hEll hZ)

theorem blockPairingAverage_add_left_of_isBlockL2
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) {X Y Z : BlockState d} (hX : IsBlockL2 U X)
    (hY : IsBlockL2 U Y) (hZ : IsBlockL2 U Z) :
    blockPairingAverage U a (X + Y) Z =
      blockPairingAverage U a X Z + blockPairingAverage U a Y Z :=
  blockPairingAverage_add_left U a X Y Z (hX.integrableOn_pair hEll hZ)
    (hY.integrableOn_pair hEll hZ)

/-- Expansion of the quadratic form along a line. -/
theorem blockPairingAverage_line [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) {X Y : BlockState d} (hX : IsBlockL2 U X)
    (hY : IsBlockL2 U Y) (t : ℝ) :
    blockPairingAverage U a (X + t • Y) (X + t • Y) =
      blockPairingAverage U a X X + 2 * t * blockPairingAverage U a X Y +
        t ^ 2 * blockPairingAverage U a Y Y := by
  have htY := hY.smul t
  rw [blockPairingAverage_add_left_of_isBlockL2 hEll hX htY (hX.add htY),
    blockPairingAverage_add_right_of_isBlockL2 hEll hX hX htY,
    blockPairingAverage_add_right_of_isBlockL2 hEll htY hX htY,
    blockPairingAverage_smul_right, blockPairingAverage_smul_left,
    blockPairingAverage_smul_left, blockPairingAverage_smul_right,
    blockPairingAverage_comm U a Y X]
  ring

/-- Cauchy-Schwarz for the pairing. -/
theorem blockPairingAverage_sq_le [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) {X Y : BlockState d} (hX : IsBlockL2 U X)
    (hY : IsBlockL2 U Y) :
    blockPairingAverage U a X Y ^ 2 ≤
      blockPairingAverage U a X X * blockPairingAverage U a Y Y := by
  have h := discrim_le_zero (a := blockPairingAverage U a Y Y)
    (b := 2 * blockPairingAverage U a X Y) (c := blockPairingAverage U a X X) (fun t => by
      have := blockPairingAverage_self_nonneg (a := a) hEll (X + t • Y)
      rw [blockPairingAverage_line hEll hX hY t] at this
      linarith only [this])
  unfold discrim at h
  nlinarith only [h]

/-- The absolute value form of Cauchy-Schwarz with square roots. -/
theorem abs_blockPairingAverage_le [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) {X Y : BlockState d} (hX : IsBlockL2 U X)
    (hY : IsBlockL2 U Y) :
    |blockPairingAverage U a X Y| ≤
      Real.sqrt (blockPairingAverage U a X X) * Real.sqrt (blockPairingAverage U a Y Y) := by
  rw [← Real.sqrt_mul (blockPairingAverage_self_nonneg hEll X)]
  exact Real.abs_le_sqrt (blockPairingAverage_sq_le hEll hX hY)

/-- **`e.localization.euler`.** A minimizer over `F + (L²_{pot,0} × L²_{sol,0})(U)` is
orthogonal for the pairing to every test field. -/
theorem blockPairingAverage_eq_zero_of_isBlockOffsetMinimizer
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a) {F X Y : BlockState d} (hF : IsBlockL2 U F)
    (hX : IsBlockOffsetMinimizer a U F X) (hY : IsBlockTestField U Y) :
    blockPairingAverage U a X Y = 0 := by
  have hXL2 : IsBlockL2 U X :=
    ⟨hX.1.memVectorL2_potential hF.1, hX.1.memVectorL2_flux hF.2⟩
  have hadm : ∀ t : ℝ, IsBlockOffsetAdmissible U F (X + t • Y) := fun t => by
    obtain ⟨h1, h2, h3, h4⟩ := hX.1
    have e1 : (fun x => (X + t • Y).potential x - F.potential x) =
        (fun x => X.potential x - F.potential x) + t • Y.potential := by
      funext x; simp [add_sub_right_comm]
    have e2 : (fun x => (X + t • Y).flux x - F.flux x) =
        (fun x => X.flux x - F.flux x) + t • Y.flux := by
      funext x; simp [add_sub_right_comm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1]; exact h1.add (hY.1.const_smul t)
    · rw [e1]; exact isPotentialZeroTraceOn_add h2 (isPotentialZeroTraceOn_smul hY.2.1 t)
    · rw [e2]; exact h3.add (hY.2.2.1.const_smul t)
    · rw [e2]
      exact isSolenoidalZeroNormalTraceOn_add_of_memVectorL2 h3 (hY.2.2.1.const_smul t) h4
        (isSolenoidalZeroNormalTraceOn_smul hY.2.2.2 t)
  have hE : ∀ Z : BlockState d,
      volumeAverage U (blockEnergyDensity a Z) = (1 / 2 : ℝ) * blockPairingAverage U a Z Z :=
    fun Z => blockEnergyAverage_eq_half_blockPairingAverage_self U a Z
  have h := discrim_le_zero (a := (1 / 2 : ℝ) * blockPairingAverage U a Y Y)
    (b := blockPairingAverage U a X Y) (c := 0) (fun t => by
      have hm := hX.2 (X + t • Y) (hadm t)
      rw [hE, hE, blockPairingAverage_line hEll hXL2 hY.isBlockL2 t] at hm
      linarith only [hm])
  unfold discrim at h
  have h0 : blockPairingAverage U a X Y ^ 2 ≤ 0 := by linarith only [h]
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h0 (sq_nonneg _))

end SuperdiffusionCLT.Section5
