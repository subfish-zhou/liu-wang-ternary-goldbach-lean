import LiuWang.Proof.Campaign20260915.RSFiniteExtension.UpperCore
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_1423 : UpperReach 1423 13528227577132 := by
  have hr := row_1423
  have hl := log_bounds hr.1
    (by change logScale (1423 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1420) (H := 13455622351102) (u := 72605225954)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel) hl.2
    (by norm_num) upper_reach_1420

theorem upper_reach_1427 : UpperReach 1427 13600860873356 := by
  have hr := row_1427
  have hl := log_bounds hr.1
    (by change logScale (1427 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1423) (H := 13528227577132) (u := 72633296148)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel) hl.2
    (by norm_num) upper_reach_1423

theorem upper_reach_1429 : UpperReach 1429 13673508175185 := by
  have hr := row_1429
  have hl := log_bounds hr.1
    (by change logScale (1429 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1427) (H := 13600860873356) (u := 72647301753)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel) hl.2
    (by norm_num) upper_reach_1427

theorem upper_reach_1433 : UpperReach 1433 13746183429513 := by
  have hr := row_1433
  have hl := log_bounds hr.1
    (by change logScale (1433 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1429) (H := 13673508175185) (u := 72675254252)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel) hl.2
    (by norm_num) upper_reach_1429

theorem upper_reach_1439 : UpperReach 1439 13818900466631 := by
  have hr := row_1439
  have hl := log_bounds hr.1
    (by change logScale (1439 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1433) (H := 13746183429513) (u := 72717037042)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel) hl.2
    (by norm_num) upper_reach_1433

#print axioms upper_reach_1439

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
