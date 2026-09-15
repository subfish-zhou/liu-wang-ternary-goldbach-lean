import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.CriticalMean
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.FamilyAssembly
import LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1.AuxiliaryDomain
import LiuWang.Proof.GlobalZeroDensity.Sharp.Consumer
import LiuWang.Proof.GlobalZeroDensity.Strip.Consumer
import LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.Consumer
import LiuWang.Proof.SourceRoute.Density.EnergyCount

set_option autoImplicit false
set_option pp.proofs false

noncomputable section

open LiuWang.Proof.Interfaces LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.NonprincipalDensityAdvance
open LiuWang.Proof.GlobalZeroDensity

namespace LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1

theorem principal_only_small_moduli (alpha y : ℝ) :
    familyCount 1 alpha y = count (1 : Character 1) alpha y ∧
      familyCount 2 alpha y = count (1 : Character 1) alpha y := by
  simp [familyCount_split]

theorem zero_length_critical_mean (y : ℝ) :
    LiuWang.Proof.GlobalZeroDensity.M y (1 / 2) (y * 0) = 0 := by
  simp [LiuWang.Proof.GlobalZeroDensity.M]

#print strictNonprincipalCount
#print mem_strict_values
#print closed_nonprincipal_le_strict
#print strictNonprincipalCount_one
#print strictNonprincipalCount_two
#print chenBound
#print continuous_chenBound
#print closed_nonprincipal_of_strict_bounds
#print closed_nonprincipal_of_chen
#print integral_mul_le_sqrt_means
#print critical_mean_schwarz
#print source_height_log_bounds
#print lemma_3_4_scalar
#print lemma_3_4_from_original_inputs
#print zeta_sq_of_3_36
#print zeta_inputs_of_3_36
#print lemma_3_4_from_3_36_and_chen24
#print principalSevenBound
#print principal_power_le_family
#print principal_log_powers
#print principal_plus_chen_le_sourceSeven
#print chenBound_nonneg
#print family_high_from_original_inputs
#print family_sourceSeven_from_original_inputs
#print complete_family_sourceSeven_from_original_inputs
#print principal_only_small_moduli
#print zero_length_critical_mean
#print source_height_ge_log_six
#print sourceDelta_eq_strip_delta
#print source_shift_in_lemma_3_5_domain
#print weightedMean_eq_original_integral

#print axioms strictNonprincipalCount
#print axioms mem_strict_values
#print axioms closed_nonprincipal_le_strict
#print axioms strictNonprincipalCount_one
#print axioms strictNonprincipalCount_two
#print axioms chenBound
#print axioms continuous_chenBound
#print axioms closed_nonprincipal_of_strict_bounds
#print axioms closed_nonprincipal_of_chen
#print axioms integral_mul_le_sqrt_means
#print axioms critical_mean_schwarz
#print axioms source_height_log_bounds
#print axioms lemma_3_4_scalar
#print axioms lemma_3_4_from_original_inputs
#print axioms zeta_sq_of_3_36
#print axioms zeta_inputs_of_3_36
#print axioms lemma_3_4_from_3_36_and_chen24
#print axioms principalSevenBound
#print axioms principal_power_le_family
#print axioms principal_log_powers
#print axioms principal_plus_chen_le_sourceSeven
#print axioms chenBound_nonneg
#print axioms family_high_from_original_inputs
#print axioms family_sourceSeven_from_original_inputs
#print axioms complete_family_sourceSeven_from_original_inputs
#print axioms principal_only_small_moduli
#print axioms zero_length_critical_mean
#print axioms source_height_ge_log_six
#print axioms sourceDelta_eq_strip_delta
#print axioms source_shift_in_lemma_3_5_domain
#print axioms weightedMean_eq_original_integral

#print LiuWang.Proof.GlobalZeroDensity.Q
#print LiuWang.Proof.GlobalZeroDensity.mem_cutoff
#print LiuWang.Proof.GlobalZeroDensity.M
#print LiuWang.Proof.GlobalZeroDensity.g
#print LiuWang.Proof.GlobalZeroDensity.weightedMean
#print LiuWang.Proof.GlobalZeroDensity.regularG_eq_g
#print LiuWang.Proof.GlobalZeroDensity.Strip.K
#print LiuWang.Proof.GlobalZeroDensity.Sharp.actual_detector_lemma_3_2
#print LiuWang.Proof.GlobalZeroDensity.Strip.actual_lemma_3_3
#print LiuWang.Proof.GlobalZeroDensity.Sharp.actual_detector_lemma_3_4
#print LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.actual_lemma_3_5
#print LiuWang.Proof.DirichletZeroCount.Applications.familyCount_le_sourceSeven_original_low
#print LiuWang.Proof.SourceRoute.Density.produced_closed_count_energy_unnormalized

#print axioms LiuWang.Proof.GlobalZeroDensity.Sharp.actual_detector_lemma_3_2
#print axioms LiuWang.Proof.GlobalZeroDensity.Strip.actual_lemma_3_3
#print axioms LiuWang.Proof.GlobalZeroDensity.Sharp.actual_detector_lemma_3_4
#print axioms LiuWang.Proof.GlobalZeroDensity.MeanInterpolation.actual_lemma_3_5
#print axioms LiuWang.Proof.DirichletZeroCount.Applications.familyCount_le_sourceSeven_original_low
#print axioms LiuWang.Proof.SourceRoute.Density.produced_closed_count_energy_unnormalized

end LiuWang.Proof.SourceRoute.Density.Restart.OriginalV1
