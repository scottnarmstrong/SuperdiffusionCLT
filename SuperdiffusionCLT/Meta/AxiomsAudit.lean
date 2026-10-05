/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

import SuperdiffusionCLT

/-!
# Axioms of the stated theorems

Prints the axioms of every theorem in the namespace `SuperdiffusionCLT.Frozen`, the formal statements of the
results of the paper. Each depends only on `propext`, `Classical.choice` and `Quot.sound`. The README gives the
command that runs this file after the library is built.
-/

#print axioms SuperdiffusionCLT.Frozen.Section2.coarseBlockMatrix_localization
#print axioms SuperdiffusionCLT.Frozen.Section2.cutoff_approximation
#print axioms SuperdiffusionCLT.Frozen.Section3.sigmaBar_le_sigmaBarStar_homogenization
#print axioms SuperdiffusionCLT.Frozen.Section3.sigmaBarStar_lower_bound
#print axioms SuperdiffusionCLT.Frozen.Section2.sigmaStarInv_mixing_minscale
#print axioms SuperdiffusionCLT.Frozen.Section2.localization_average
#print axioms SuperdiffusionCLT.Frozen.Section2.envelopeRescale_ellipticity
#print axioms SuperdiffusionCLT.Frozen.Section3.responseFields_stationary
#print axioms SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderZero
#print axioms SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates
#print axioms SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne
#print axioms SuperdiffusionCLT.Frozen.Section3.rhs_term1
#print axioms SuperdiffusionCLT.Frozen.Section3.rhs_term2
#print axioms SuperdiffusionCLT.Frozen.Section3.rhs_term4_constFirst
#print axioms SuperdiffusionCLT.Frozen.Section3.l_LHS_term1_constFirst
#print axioms SuperdiffusionCLT.Frozen.Section3.w_basic_regbounds
#print axioms SuperdiffusionCLT.Frozen.Section3.rhs_term3_constFirst
#print axioms SuperdiffusionCLT.Frozen.Section3.stationaryPotentialRealization
#print axioms SuperdiffusionCLT.Frozen.Section2.cutoff_localization
#print axioms SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3
#print axioms SuperdiffusionCLT.Frozen.Section4.mixing_below_cutoff
#print axioms SuperdiffusionCLT.Frozen.Section4.ellipticity_below_cutoff
#print axioms SuperdiffusionCLT.Frozen.Section4.homogenization_below_cutoff
#print axioms SuperdiffusionCLT.Frozen.Section4.sigmaBar_cutoff_comparison
#print axioms SuperdiffusionCLT.Frozen.Section4.mathcalE_bounds
#print axioms SuperdiffusionCLT.Frozen.Section4.minimal_scales
#print axioms SuperdiffusionCLT.Frozen.Section5.sigmaBar_approximate_recurrence
#print axioms SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds
#print axioms SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs
#print axioms SuperdiffusionCLT.Frozen.Section6.c1beta_sharp
#print axioms SuperdiffusionCLT.Frozen.Section6.c1beta
#print axioms SuperdiffusionCLT.Frozen.Section8.generators
#print axioms SuperdiffusionCLT.Frozen.Section8.exit_time_estimate
#print axioms SuperdiffusionCLT.Frozen.Section8.theoremA
#print axioms SuperdiffusionCLT.Frozen.Section7.superdiffusivity
#print axioms SuperdiffusionCLT.Frozen.Section7.large_scale_holder
#print axioms SuperdiffusionCLT.Frozen.Section7.interior_pointwise
#print axioms SuperdiffusionCLT.Frozen.Section7.whitney_poincare
