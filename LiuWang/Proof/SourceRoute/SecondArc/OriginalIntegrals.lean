import LiuWang.Proof.SourceRoute.SecondArc.SourceDomain
import LiuWang.Proof.SourceRoute.SecondArc.DensityRectangle

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.DirichletZeroCount
open LiuWang.Proof.DirichletZeroCount.Applications

namespace LiuWang.Proof.SourceRoute.SecondArc

theorem log_window_eq {N : ℕ} (hN : 0 < N) :
    Real.log (0.001 * (N : ℝ)) = sourceL N + Real.log (0.001 : ℝ) := by
  rw [Real.log_mul (by norm_num) (Nat.cast_pos.mpr hN).ne']
  exact add_comm _ _

theorem window_base_ge_one {N : ℕ} (hN : Real.exp 3100 ≤ (N : ℝ)) :
    1 ≤ 0.001 * (N : ℝ) := by
  have hlog : 0 ≤ Real.log (0.001 * (N : ℝ)) := by
    linarith [log_window_lower hN, sourceL_ge_3100 hN]
  have h := Real.exp_le_exp.mpr hlog
  simpa only [Real.exp_zero, Real.exp_log (by
    have hn := natCast_pos_of_exp_le hN
    positivity : 0 < 0.001 * (N : ℝ))] using h

/-- The middle-packet density-integral reduction underlying (5.7). -/
theorem source_57_middle_packet {N q a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖middlePacket N q a (omegaCutoff N q) (middleUpper N q) eta‖ ≤
      (10 * (N : ℝ) * Real.sqrt q / q.totient) *
        ((0.001 * (N : ℝ)) ^ (-(1 / 2) : ℝ) *
            bandMass q (1 / 2) (omegaCutoff N q) (middleUpper N q) +
          (∫ alpha in (1 / 2 : ℝ)..(59 / 60 : ℝ),
            alphaKernel (0.001 * (N : ℝ)) alpha *
              bandMass q alpha (omegaCutoff N q) (middleUpper N q)) +
          (1 / Real.sqrt (middleUpper N q)) *
            (∫ alpha in (59 / 60 : ℝ)..1,
              alphaKernel (0.001 * (N : ℝ)) alpha *
                (familyCount q alpha (middleUpper N q) : ℝ)) +
          (1 / 2 : ℝ) * ∫ y in (omegaCutoff N q)..(middleUpper N q),
            heightKernel y * ∫ alpha in (59 / 60 : ℝ)..1,
              alphaKernel (0.001 * (N : ℝ)) alpha * (familyCount q alpha y : ℝ)) := by
  have hh := middle_height_domain hN hq
  have hd := alpha_height_reduction (q := q) (window_base_ge_one hN)
    (by norm_num : (59 / 60 : ℝ) ≤ 1) hh.1 hh.2.1
  apply (source_53_packet hN ha eta).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith only [hd]

/-- The literal Theorem 7 integrand, not an assumed near-one count estimate. -/
theorem source_59_inner {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N)
    {y : ℝ} (hy : y ∈ Set.Icc (omegaCutoff N q) (middleUpper N q)) :
    (∫ alpha in (59 / 60 : ℝ)..(1 - (0.478 : ℝ) / Real.log ((q : ℝ) * y)),
      alphaKernel (0.001 * (N : ℝ)) alpha * sourceSevenBound q alpha y) ≤
      (254231 / Real.log ((q : ℝ) * y) + 33643) *
        (Real.log ((q : ℝ) * y)) ^ (6 : ℕ) * Real.exp (4 * 0.478) *
          ((sourceL N + Real.log (0.001 : ℝ)) /
            (sourceL N + Real.log (0.001 : ℝ) - 4 * Real.log ((q : ℝ) * y))) *
          Real.exp (-0.478 * (sourceL N + Real.log (0.001 : ℝ)) /
            Real.log ((q : ℝ) * y)) := by
  have hd := middle_log_domain hN hq hy
  have hi := sourceSeven_integral_le (by
    have hn := natCast_pos_of_exp_le hN
    positivity : 0 < 0.001 * (N : ℝ)) hd.1 hd.2.1 hd.2.2
    (by norm_num : (0 : ℝ) ≤ 0.478) (a := (59 / 60 : ℝ))
  rw [log_window_eq (nat_pos_of_exp_le hN)] at hi
  exact hi

theorem source_log_endpoints {N q : ℕ} [NeZero q] :
    Real.log ((q : ℝ) * omegaCutoff N q) = Real.log (3.36 * sourceL N ^ (3 : ℕ)) ∧
      Real.log ((q : ℝ) * middleUpper N q) =
        Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)) :=
  log_height_source_endpoints (Nat.cast_pos.mpr (NeZero.pos q))

theorem source_516_kernel_identity {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) :
    (112000 * (N : ℝ)) * ((Real.sqrt q / q.totient) *
      (∫ y in (omegaCutoff N q)..(middleUpper N q), heightKernel y *
        ∫ alpha in (1 - (0.478 : ℝ) / Real.log ((q : ℝ) * y))..
          (1 - (0.2067 : ℝ) / Real.log ((q : ℝ) * y)),
            alphaKernel (0.001 * (N : ℝ)) alpha)) =
      (112000 * (N : ℝ)) * ((q : ℝ) / q.totient) *
        ∫ z in Real.log (3.36 * sourceL N ^ (3 : ℕ))..
          Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)),
            Real.exp (-z / 2) *
              (Real.exp (-0.2067 * (sourceL N + Real.log (0.001 : ℝ)) / z) -
                Real.exp (-0.478 * (sourceL N + Real.log (0.001 : ℝ)) / z)) := by
  have hh := middle_height_domain hN hq
  rw [source_516_log_integral (Nat.cast_pos.mpr (NeZero.pos q))
    (by have hn := natCast_pos_of_exp_le hN; positivity) hh.1 (hh.1.trans_le hh.2.1),
    (source_log_endpoints (N := N) (q := q)).1,
    (source_log_endpoints (N := N) (q := q)).2, log_window_eq (nat_pos_of_exp_le hN)]
  ring

theorem source_517_kernel_identity {N q : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hq : (q : ℝ) ≤ sourceP N) (c₁ : ℝ) :
    (16 * (N : ℝ)) * ((Real.sqrt q / q.totient) *
      (∫ y in (omegaCutoff N q)..(middleUpper N q), heightKernel y *
        ∫ alpha in (1 - (0.2067 : ℝ) / Real.log ((q : ℝ) * y))..
          (1 - 1 / (c₁ * Real.log ((q : ℝ) * y))), alphaKernel (0.001 * (N : ℝ)) alpha)) =
      (16 * (N : ℝ)) * ((q : ℝ) / q.totient) *
        ∫ z in Real.log (3.36 * sourceL N ^ (3 : ℕ))..
          Real.log (10 * Real.pi * sourceL N ^ (7 : ℕ)),
            Real.exp (-z / 2) *
              (Real.exp (-(1 / c₁) * (sourceL N + Real.log (0.001 : ℝ)) / z) -
                Real.exp (-0.2067 * (sourceL N + Real.log (0.001 : ℝ)) / z)) := by
  have hh := middle_height_domain hN hq
  rw [source_517_log_integral (Nat.cast_pos.mpr (NeZero.pos q))
    (by have hn := natCast_pos_of_exp_le hN; positivity) hh.1 (hh.1.trans_le hh.2.1),
    (source_log_endpoints (N := N) (q := q)).1,
    (source_log_endpoints (N := N) (q := q)).2, log_window_eq (nat_pos_of_exp_le hN)]
  ring

end LiuWang.Proof.SourceRoute.SecondArc
