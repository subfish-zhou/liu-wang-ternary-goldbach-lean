import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper060
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block061

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_14177 : UpperReach 14177 140297002117900 := by
  have hr := row_14177
  have hl := log_bounds hr.1
    (by change logScale (14177 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14173) (H := 140201408355737) (u := 95593762087)
    (by norm_num) (by norm_num) hr.1 gap_14177 hl.2
    (by norm_num) upper_reach_14173

theorem upper_reach_14197 : UpperReach 14197 140392609977478 := by
  have hr := row_14197
  have hl := log_bounds hr.1
    (by change logScale (14197 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14177) (H := 140297002117900) (u := 95607859502)
    (by norm_num) (by norm_num) hr.1 gap_14197 hl.2
    (by norm_num) upper_reach_14177

theorem upper_reach_14207 : UpperReach 14207 140488224878318 := by
  have hr := row_14207
  have hl := log_bounds hr.1
    (by change logScale (14207 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14197) (H := 140392609977478) (u := 95614900764)
    (by norm_num) (by norm_num) hr.1 gap_14207 hl.2
    (by norm_num) upper_reach_14197

theorem upper_reach_14221 : UpperReach 14221 140583849628603 := by
  have hr := row_14221
  have hl := log_bounds hr.1
    (by change logScale (14221 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14207) (H := 140488224878318) (u := 95624750209)
    (by norm_num) (by norm_num) hr.1 gap_14221 hl.2
    (by norm_num) upper_reach_14207

theorem upper_reach_14243 : UpperReach 14243 140679489837014 := by
  have hr := row_14243
  have hl := log_bounds hr.1
    (by change logScale (14243 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14221) (H := 140583849628603) (u := 95640208335)
    (by norm_num) (by norm_num) hr.1 gap_14243 hl.2
    (by norm_num) upper_reach_14221

theorem upper_reach_14249 : UpperReach 14249 140775134257134 := by
  have hr := row_14249
  have hl := log_bounds hr.1
    (by change logScale (14249 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14243) (H := 140679489837014) (u := 95644420044)
    (by norm_num) (by norm_num) hr.1 gap_14249 hl.2
    (by norm_num) upper_reach_14243

theorem upper_reach_14251 : UpperReach 14251 140870780080762 := by
  have hr := row_14251
  have hl := log_bounds hr.1
    (by change logScale (14251 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14249) (H := 140775134257134) (u := 95645823552)
    (by norm_num) (by norm_num) hr.1 gap_14251 hl.2
    (by norm_num) upper_reach_14249

theorem upper_reach_14281 : UpperReach 14281 140966446933418 := by
  have hr := row_14281
  have hl := log_bounds hr.1
    (by change logScale (14281 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14251) (H := 140870780080762) (u := 95666852580)
    (by norm_num) (by norm_num) hr.1 gap_14281 hl.2
    (by norm_num) upper_reach_14251

theorem upper_reach_14293 : UpperReach 14293 141062122185319 := by
  have hr := row_14293
  have hl := log_bounds hr.1
    (by change logScale (14293 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14281) (H := 140966446933418) (u := 95675251825)
    (by norm_num) (by norm_num) hr.1 gap_14293 hl.2
    (by norm_num) upper_reach_14281

theorem upper_reach_14303 : UpperReach 14303 141157804431205 := by
  have hr := row_14303
  have hl := log_bounds hr.1
    (by change logScale (14303 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14293) (H := 141062122185319) (u := 95682245810)
    (by norm_num) (by norm_num) hr.1 gap_14303 hl.2
    (by norm_num) upper_reach_14293

theorem upper_reach_14321 : UpperReach 14321 141253499253951 := by
  have hr := row_14321
  have hl := log_bounds hr.1
    (by change logScale (14321 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14303) (H := 141157804431205) (u := 95694822670)
    (by norm_num) (by norm_num) hr.1 gap_14321 hl.2
    (by norm_num) upper_reach_14303

theorem upper_reach_14323 : UpperReach 14323 141349195473151 := by
  have hr := row_14323
  have hl := log_bounds hr.1
    (by change logScale (14323 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14321) (H := 141253499253951) (u := 95696219124)
    (by norm_num) (by norm_num) hr.1 gap_14323 hl.2
    (by norm_num) upper_reach_14321

theorem upper_reach_14327 : UpperReach 14327 141444894484672 := by
  have hr := row_14327
  have hl := log_bounds hr.1
    (by change logScale (14327 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14323) (H := 141349195473151) (u := 95699011445)
    (by norm_num) (by norm_num) hr.1 gap_14327 hl.2
    (by norm_num) upper_reach_14323

theorem upper_reach_14341 : UpperReach 14341 141540603263181 := by
  have hr := row_14341
  have hl := log_bounds hr.1
    (by change logScale (14341 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14327) (H := 141444894484672) (u := 95708778433)
    (by norm_num) (by norm_num) hr.1 gap_14341 hl.2
    (by norm_num) upper_reach_14327

theorem upper_reach_14347 : UpperReach 14347 141636316224624 := by
  have hr := row_14347
  have hl := log_bounds hr.1
    (by change logScale (14347 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14341) (H := 141540603263181) (u := 95712961367)
    (by norm_num) (by norm_num) hr.1 gap_14347 hl.2
    (by norm_num) upper_reach_14341

theorem upper_reach_14369 : UpperReach 14369 141732044508538 := by
  have hr := row_14369
  have hl := log_bounds hr.1
    (by change logScale (14369 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14347) (H := 141636316224624) (u := 95728283838)
    (by norm_num) (by norm_num) hr.1 gap_14369 hl.2
    (by norm_num) upper_reach_14347

theorem upper_reach_14387 : UpperReach 14387 141827785311580 := by
  have hr := row_14387
  have hl := log_bounds hr.1
    (by change logScale (14387 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14369) (H := 141732044508538) (u := 95740802966)
    (by norm_num) (by norm_num) hr.1 gap_14387 hl.2
    (by norm_num) upper_reach_14369

theorem upper_reach_14389 : UpperReach 14389 141923527504669 := by
  have hr := row_14389
  have hl := log_bounds hr.1
    (by change logScale (14389 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14387) (H := 141827785311580) (u := 95742193013)
    (by norm_num) (by norm_num) hr.1 gap_14389 hl.2
    (by norm_num) upper_reach_14387

theorem upper_reach_14401 : UpperReach 14401 142019278033987 := by
  have hr := row_14401
  have hl := log_bounds hr.1
    (by change logScale (14401 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14389) (H := 141923527504669) (u := 95750529242)
    (by norm_num) (by norm_num) hr.1 gap_14401 hl.2
    (by norm_num) upper_reach_14389

theorem upper_reach_14407 : UpperReach 14407 142115032728814 := by
  have hr := row_14407
  have hl := log_bounds hr.1
    (by change logScale (14407 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14401) (H := 142019278033987) (u := 95754694751)
    (by norm_num) (by norm_num) hr.1 gap_14407 hl.2
    (by norm_num) upper_reach_14401

theorem upper_reach_14411 : UpperReach 14411 142210790199684 := by
  have hr := row_14411
  have hl := log_bounds hr.1
    (by change logScale (14411 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14407) (H := 142115032728814) (u := 95757470794)
    (by norm_num) (by norm_num) hr.1 gap_14411 hl.2
    (by norm_num) upper_reach_14407

theorem upper_reach_14419 : UpperReach 14419 142306553220329 := by
  have hr := row_14419
  have hl := log_bounds hr.1
    (by change logScale (14419 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14411) (H := 142210790199684) (u := 95763020569)
    (by norm_num) (by norm_num) hr.1 gap_14419 hl.2
    (by norm_num) upper_reach_14411

theorem upper_reach_14423 : UpperReach 14423 142402319014707 := by
  have hr := row_14423
  have hl := log_bounds hr.1
    (by change logScale (14423 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14419) (H := 142306553220329) (u := 95765794302)
    (by norm_num) (by norm_num) hr.1 gap_14423 hl.2
    (by norm_num) upper_reach_14419

theorem upper_reach_14431 : UpperReach 14431 142498090354243 := by
  have hr := row_14431
  have hl := log_bounds hr.1
    (by change logScale (14431 : ℚ) ≤ 13; exact le_of_eq hr.2.1) hr.2.2
  exact upper_reach_next (a := 14423) (H := 142402319014707) (u := 95771339460)
    (by norm_num) (by norm_num) hr.1 gap_14431 hl.2
    (by norm_num) upper_reach_14423

#print axioms upper_reach_14431

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
