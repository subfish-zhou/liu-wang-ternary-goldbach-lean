import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper029
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block030

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_7237 : UpperReach 7237 71422029383299 := by
  have hr := row_7237
  have hl := log_bounds hr.1
    (by change logScale (7237 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7229) (H := 71333159762906) (u := 88869620317)
    (by norm_num) (by norm_num) hr.1 gap_7237 hl.2
    (by norm_num) upper_reach_7229

theorem upper_reach_7243 : UpperReach 7243 71510907290985 := by
  have hr := row_7243
  have hl := log_bounds hr.1
    (by change logScale (7243 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7237) (H := 71422029383299) (u := 88877907610)
    (by norm_num) (by norm_num) hr.1 gap_7243 hl.2
    (by norm_num) upper_reach_7237

theorem upper_reach_7247 : UpperReach 7247 71599790719720 := by
  have hr := row_7247
  have hl := log_bounds hr.1
    (by change logScale (7247 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7243) (H := 71510907290985) (u := 88883428659)
    (by norm_num) (by norm_num) hr.1 gap_7247 hl.2
    (by norm_num) upper_reach_7243

theorem upper_reach_7253 : UpperReach 7253 71688682424318 := by
  have hr := row_7253
  have hl := log_bounds hr.1
    (by change logScale (7253 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7247) (H := 71599790719720) (u := 88891704522)
    (by norm_num) (by norm_num) hr.1 gap_7253 hl.2
    (by norm_num) upper_reach_7247

theorem upper_reach_7283 : UpperReach 7283 71777615405804 := by
  have hr := row_7283
  have hl := log_bounds hr.1
    (by change logScale (7283 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7253) (H := 71688682424318) (u := 88932981410)
    (by norm_num) (by norm_num) hr.1 gap_7283 hl.2
    (by norm_num) upper_reach_7253

theorem upper_reach_7297 : UpperReach 7297 71866567591686 := by
  have hr := row_7297
  have hl := log_bounds hr.1
    (by change logScale (7297 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7283) (H := 71777615405804) (u := 88952185806)
    (by norm_num) (by norm_num) hr.1 gap_7297 hl.2
    (by norm_num) upper_reach_7283

theorem upper_reach_7307 : UpperReach 7307 71955533472448 := by
  have hr := row_7307
  have hl := log_bounds hr.1
    (by change logScale (7307 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7297) (H := 71866567591686) (u := 88965880686)
    (by norm_num) (by norm_num) hr.1 gap_7307 hl.2
    (by norm_num) upper_reach_7297

theorem upper_reach_7309 : UpperReach 7309 72044502089937 := by
  have hr := row_7309
  have hl := log_bounds hr.1
    (by change logScale (7309 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7307) (H := 71955533472448) (u := 88968617413)
    (by norm_num) (by norm_num) hr.1 gap_7309 hl.2
    (by norm_num) upper_reach_7307

theorem upper_reach_7321 : UpperReach 7321 72133487112078 := by
  have hr := row_7321
  have hl := log_bounds hr.1
    (by change logScale (7321 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7309) (H := 72044502089937) (u := 88985022065)
    (by norm_num) (by norm_num) hr.1 gap_7321 hl.2
    (by norm_num) upper_reach_7309

theorem upper_reach_7331 : UpperReach 7331 72222485784235 := by
  have hr := row_7331
  have hl := log_bounds hr.1
    (by change logScale (7331 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7321) (H := 72133487112078) (u := 88998672081)
    (by norm_num) (by norm_num) hr.1 gap_7331 hl.2
    (by norm_num) upper_reach_7321

theorem upper_reach_7333 : UpperReach 7333 72311487184160 := by
  have hr := row_7333
  have hl := log_bounds hr.1
    (by change logScale (7333 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7331) (H := 72222485784235) (u := 89001399849)
    (by norm_num) (by norm_num) hr.1 gap_7333 hl.2
    (by norm_num) upper_reach_7331

theorem upper_reach_7349 : UpperReach 7349 72400510379490 := by
  have hr := row_7349
  have hl := log_bounds hr.1
    (by change logScale (7349 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7333) (H := 72311487184160) (u := 89023195254)
    (by norm_num) (by norm_num) hr.1 gap_7349 hl.2
    (by norm_num) upper_reach_7333

theorem upper_reach_7351 : UpperReach 7351 72489536295908 := by
  have hr := row_7351
  have hl := log_bounds hr.1
    (by change logScale (7351 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7349) (H := 72400510379490) (u := 89025916342)
    (by norm_num) (by norm_num) hr.1 gap_7351 hl.2
    (by norm_num) upper_reach_7349

theorem upper_reach_7369 : UpperReach 7369 72578586668860 := by
  have hr := row_7369
  have hl := log_bounds hr.1
    (by change logScale (7369 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7351) (H := 72489536295908) (u := 89050372876)
    (by norm_num) (by norm_num) hr.1 gap_7369 hl.2
    (by norm_num) upper_reach_7351

theorem upper_reach_7393 : UpperReach 7393 72667669557760 := by
  have hr := row_7393
  have hl := log_bounds hr.1
    (by change logScale (7393 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7369) (H := 72578586668860) (u := 89082888824)
    (by norm_num) (by norm_num) hr.1 gap_7393 hl.2
    (by norm_num) upper_reach_7369

theorem upper_reach_7411 : UpperReach 7411 72756776764424 := by
  have hr := row_7411
  have hl := log_bounds hr.1
    (by change logScale (7411 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7393) (H := 72667669557760) (u := 89107206588)
    (by norm_num) (by norm_num) hr.1 gap_7411 hl.2
    (by norm_num) upper_reach_7393

theorem upper_reach_7417 : UpperReach 7417 72845892063886 := by
  have hr := row_7417
  have hl := log_bounds hr.1
    (by change logScale (7417 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7411) (H := 72756776764424) (u := 89115299386)
    (by norm_num) (by norm_num) hr.1 gap_7417 hl.2
    (by norm_num) upper_reach_7411

theorem upper_reach_7433 : UpperReach 7433 72935028912178 := by
  have hr := row_7433
  have hl := log_bounds hr.1
    (by change logScale (7433 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7417) (H := 72845892063886) (u := 89136848216)
    (by norm_num) (by norm_num) hr.1 gap_7433 hl.2
    (by norm_num) upper_reach_7417

theorem upper_reach_7451 : UpperReach 7451 73024189947528 := by
  have hr := row_7451
  have hl := log_bounds hr.1
    (by change logScale (7451 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7433) (H := 72935028912178) (u := 89161035274)
    (by norm_num) (by norm_num) hr.1 gap_7451 hl.2
    (by norm_num) upper_reach_7433

theorem upper_reach_7457 : UpperReach 7457 73113359032248 := by
  have hr := row_7457
  have hl := log_bounds hr.1
    (by change logScale (7457 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7451) (H := 73024189947528) (u := 89169084644)
    (by norm_num) (by norm_num) hr.1 gap_7457 hl.2
    (by norm_num) upper_reach_7451

theorem upper_reach_7459 : UpperReach 7459 73202530798652 := by
  have hr := row_7459
  have hl := log_bounds hr.1
    (by change logScale (7459 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7457) (H := 73113359032248) (u := 89171766328)
    (by norm_num) (by norm_num) hr.1 gap_7459 hl.2
    (by norm_num) upper_reach_7457

theorem upper_reach_7477 : UpperReach 7477 73291726667906 := by
  have hr := row_7477
  have hl := log_bounds hr.1
    (by change logScale (7477 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7459) (H := 73202530798652) (u := 89195869178)
    (by norm_num) (by norm_num) hr.1 gap_7477 hl.2
    (by norm_num) upper_reach_7459

theorem upper_reach_7481 : UpperReach 7481 73380927885469 := by
  have hr := row_7481
  have hl := log_bounds hr.1
    (by change logScale (7481 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7477) (H := 73291726667906) (u := 89201217487)
    (by norm_num) (by norm_num) hr.1 gap_7481 hl.2
    (by norm_num) upper_reach_7477

theorem upper_reach_7487 : UpperReach 7487 73470137120136 := by
  have hr := row_7487
  have hl := log_bounds hr.1
    (by change logScale (7487 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 7481) (H := 73380927885469) (u := 89209234591)
    (by norm_num) (by norm_num) hr.1 gap_7487 hl.2
    (by norm_num) upper_reach_7481

#print axioms upper_reach_7487

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
