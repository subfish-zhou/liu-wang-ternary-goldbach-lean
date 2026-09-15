import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_160_0 : expNegUpper (3145070269067271304411 / 39850199714021904000 : ℝ) ≤ (26538440930578610684285943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (926291 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_160_1 : expNegUpper (100712932874845179840751 / 1275206390848700928000 : ℝ) ≤ (25107450047867212232249393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (231673 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_160 : rowCell 6 160 ≤ (7532129541506890708985567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26538440930578610684285943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25107450047867212232249393 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_160_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_160_1
  · norm_num [gridPoint]

theorem exp_6_161_0 : expNegUpper (101316591805430575112039 / 1282849789227848192000 : ℝ) ≤ (3138429993088177065833221 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (231673 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_161_1 : expNegUpper (2027767815941538390223 / 25656995784556963840 : ℝ) ≤ (1187040917513717425267369 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370839 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_161 : rowCell 6 161 ≤ (712411776395397272403409 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3138429993088177065833221 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1187040917513717425267369 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_161_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_161_1
  · norm_num [gridPoint]

theorem exp_6_162_0 : expNegUpper (2039885650246991125823 / 25810320518255011840 : ℝ) ≤ (11870404455186396137290337 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370839 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_162_1 : expNegUpper (102067199561729295899461 / 1290516025912750592000 : ℝ) ≤ (22436592503038452289130971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (927507 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_162 : rowCell 6 162 ≤ (3367297598575030315250891 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11870404455186396137290337 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22436592503038452289130971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_162_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_162_1
  · norm_num [gridPoint]

theorem exp_6_163_0 : expNegUpper (5403964774907803789871 / 68326584258074112000 : ℝ) ≤ (5609145921812411905353551 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (927507 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_163_1 : expNegUpper (1351965383699223101773 / 17081646064518528000 : ℝ) ≤ (42385597385688434670241431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11599 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_163 : rowCell 6 163 ≤ (6362987522859353496424647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5609145921812411905353551 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (42385597385688434670241431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_163_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_163_1
  · norm_num [gridPoint]

theorem exp_6_164_0 : expNegUpper (1033597464304653689903 / 13059170141998208000 : ℝ) ≤ (331137350999534502960971 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11599 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_164_1 : expNegUpper (4137396383506021829843 / 52236680567992832000 : ℝ) ≤ (1600596803890217461435027 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74267 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_164 : rowCell 6 164 ≤ (6008718566457421418952151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (331137350999534502960971 / 7812500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1600596803890217461435027 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_164_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_164_1
  · norm_num [gridPoint]

theorem exp_6_165_0 : expNegUpper (104047539626339493968467 / 1313651765801988608000 : ℝ) ≤ (2500931546419046816731409 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74267 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_165_1 : expNegUpper (52061915416798356331253 / 656825882900994304000 : ℝ) ≤ (18878602768984825938978869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (928759 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_165 : rowCell 6 165 ≤ (708901519380888451295581 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2500931546419046816731409 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18878602768984825938978869 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_165_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_165_1
  · norm_num [gridPoint]

theorem exp_6_166_0 : expNegUpper (52369360151604646835557 / 660704677854955776000 : ℝ) ≤ (18878595609805999796353341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (928759 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_166_1 : expNegUpper (20963228578263620642621 / 264281871141982310400 : ℝ) ≤ (35608523549665302542798171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (29037 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_166 : rowCell 6 166 ≤ (83592091179454123348393 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18878595609805999796353341 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35608523549665302542798171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_166_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_166_1
  · norm_num [gridPoint]

theorem exp_6_167_0 : expNegUpper (21086659690682682965461 / 265837956784717926400 : ℝ) ≤ (17804255101994465314524569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (29037 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_167_1 : expNegUpper (13188981969144170515867 / 166148722990448704000 : ℝ) ≤ (33564971799888203125629121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929613 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_167 : rowCell 6 167 ≤ (5044192455772958451753497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17804255101994465314524569 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33564971799888203125629121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_167_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_167_1
  · norm_num [gridPoint]

theorem exp_6_168_0 : expNegUpper (13266410508661313020763 / 167124131305377856000 : ℝ) ≤ (33564959366739226171491973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (929613 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_168_1 : expNegUpper (106210979411441142133063 / 1336993050443022848000 : ℝ) ≤ (790567131666033294351269 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (465023 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_168 : rowCell 6 168 ≤ (2376770806845292794117003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33564959366739226171491973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (790567131666033294351269 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_168_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_168_1
  · norm_num [gridPoint]

theorem exp_6_169_0 : expNegUpper (4273307485727168336663 / 53792766210728448000 : ℝ) ≤ (31622673689090255494365443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (465023 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_169_1 : expNegUpper (2138270477170401679211 / 26896383105364224000 : ℝ) ≤ (29777844857024688521176601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (930483 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_169 : rowCell 6 169 ≤ (223869048845554149637917 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31622673689090255494365443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29777844857024688521176601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_169_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_169_1
  · norm_num [gridPoint]

theorem exp_6_170_0 : expNegUpper (53768758833709087153891 / 676334049199577344000 : ℝ) ≤ (14888917040617259877981143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (930483 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_170_1 : expNegUpper (107619499086728836338461 / 1352668098399154688000 : ℝ) ≤ (28026685191894212994572939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (232731 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_170 : rowCell 6 170 ≤ (210757873957216582188243 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14888917040617259877981143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28026685191894212994572939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_170_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_170_1
  · norm_num [gridPoint]

theorem exp_6_171_0 : expNegUpper (108245785634346048568789 / 1360539879835853312000 : ℝ) ≤ (28026675166990509671113179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (232731 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_171_1 : expNegUpper (5416445754420302299793 / 68026993991792665600 : ℝ) ≤ (6591375397553338585904093 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1862737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_171 : rowCell 6 171 ≤ (793265279421322212860131 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (28026675166990509671113179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6591375397553338585904093 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_171_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_171_1
  · norm_num [gridPoint]

theorem exp_6_172_0 : expNegUpper (5447875051815073896433 / 68421724978915353600 : ℝ) ≤ (2636549226815652599938029 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1862737 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_172_1 : expNegUpper (109041781855890359661811 / 1368434499578307072000 : ℝ) ≤ (12395328143992289675145329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1863633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_172 : rowCell 6 172 ≤ (466294039164503476265293 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2636549226815652599938029 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12395328143992289675145329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_172_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_172_1
  · norm_num [gridPoint]

theorem exp_6_173_0 : expNegUpper (109672673865623109116459 / 1376351957626515968000 : ℝ) ≤ (24790647623444710058383889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1863633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_173_1 : expNegUpper (54879054690760212032689 / 688175978813257984000 : ℝ) ≤ (23298583927549893028065719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1864537 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_173 : rowCell 6 173 ≤ (219169373116718628361101 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24790647623444710058383889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23298583927549893028065719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_173_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_173_1
  · norm_num [gridPoint]

theorem exp_6_174_0 : expNegUpper (2848808106184505519 / 35723671070464000 : ℝ) ≤ (5824643969446080536630731 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1864537 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_174_1 : expNegUpper (5702085556523090887 / 71447342140928000 : ℝ) ≤ (2735724544207821520753667 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233181 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_174 : rowCell 6 174 ≤ (164744250922576711192021 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5824643969446080536630731 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2735724544207821520753667 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_174_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_174_1
  · norm_num [gridPoint]

theorem exp_6_175_0 : expNegUpper (111113431775719563892097 / 1392255388640199168000 : ℝ) ≤ (10942894439198217113677657 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233181 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_175_1 : expNegUpper (6950074167285774500101 / 87015961790012448000 : ℝ) ≤ (5137221688269962555214631 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1866367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_175 : rowCell 6 175 ≤ (3094374671951138316438063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10942894439198217113677657 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5137221688269962555214631 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_175_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_175_1
  · norm_num [gridPoint]

theorem exp_6_176_0 : expNegUpper (6989939802573230058629 / 87515085100354592000 : ℝ) ≤ (5137219953597435863959309 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1866367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_176_1 : expNegUpper (22385591286134317798483 / 280048272321134694400 : ℝ) ≤ (19284533174530980175081847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1867293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_176 : rowCell 6 176 ≤ (2904688262984081400629257 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5137219953597435863959309 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19284533174530980175081847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_176_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_176_1
  · norm_num [gridPoint]

theorem exp_6_177_0 : expNegUpper (22513627860668917345643 / 281650034575380582400 : ℝ) ≤ (241056584209148794755203 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1867293 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_177_1 : expNegUpper (56329113456135561818543 / 704125086438451456000 : ℝ) ≤ (18089501465799197048315769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1868227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_177 : rowCell 6 177 ≤ (136267385737851553469143 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (241056584209148794755203 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18089501465799197048315769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_177_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_177_1
  · norm_num [gridPoint]

theorem exp_6_178_0 : expNegUpper (56650374577288463995807 / 708140911226943744000 : ℝ) ≤ (18089495495334868506515757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1868227 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_178_1 : expNegUpper (113392008113709642664693 / 1416281822453887488000 : ℝ) ≤ (67842590657365006364767 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (116823 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_178 : rowCell 6 178 ≤ (1277943964783288849519491 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18089495495334868506515757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (67842590657365006364767 / 4000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_178_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_178_1
  · norm_num [gridPoint]

theorem exp_6_179_0 : expNegUpper (4561475055488294058293 / 56973452413465088000 : ℝ) ≤ (16960642129677894270130759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (116823 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_179_1 : expNegUpper (1141293100273257928043 / 14243363103366272000 : ℝ) ≤ (158949198773753224734161 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467529 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_179 : rowCell 6 179 ≤ (479171420044662255362771 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16960642129677894270130759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (158949198773753224734161 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_179_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_179_1
  · norm_num [gridPoint]

theorem exp_6_180_0 : expNegUpper (28694132748393625963603 / 358103409131280512000 : ℝ) ≤ (993432171806186468863563 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467529 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_180_1 : expNegUpper (114870142645458220784971 / 1432413636525122048000 : ℝ) ≤ (14889359686717359926043947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1871071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_180 : rowCell 6 180 ≤ (224481694959170701181817 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (993432171806186468863563 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14889359686717359926043947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_180_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_180_1
  · norm_num [gridPoint]

theorem exp_6_181_0 : expNegUpper (115519722966017031911939 / 1440513801019372032000 : ℝ) ≤ (14889354936634804083664351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1871071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_181_1 : expNegUpper (11561451596044557333577 / 144051380101937203200 : ℝ) ≤ (6970551556428256025118759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1872033 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_181 : rowCell 6 181 ≤ (65698215729173769135577 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14889354936634804083664351 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6970551556428256025118759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_181_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_181_1
  · norm_num [gridPoint]

theorem exp_6_182_0 : expNegUpper (611928748930913591363 / 7624404230628300800 : ℝ) ≤ (697054935754985692343429 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1872033 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_182_1 : expNegUpper (6124338945506657746619 / 76244042306283008000 : ℝ) ≤ (6523690585925269415418463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (936501 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_182 : rowCell 6 182 ≤ (984012100409405428562963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (697054935754985692343429 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6523690585925269415418463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_182_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_182_1
  · norm_num [gridPoint]

theorem exp_6_183_0 : expNegUpper (117016758978482801924569 / 1456782644925137408000 : ℝ) ≤ (6523688550992389396002167 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (936501 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_183_1 : expNegUpper (14639240581292454883001 / 182097830615642176000 : ℝ) ≤ (6102760028804673570469591 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (936989 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_183 : rowCell 6 183 ≤ (719321855088826361671 / 390625000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6523688550992389396002167 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6102760028804673570469591 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_183_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_183_1
  · norm_num [gridPoint]

theorem exp_6_184_0 : expNegUpper (588853115015916686689 / 7324756621683264000 : ℝ) ≤ (97644130341959218267351 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (936989 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_184_1 : expNegUpper (4714759200396945827983 / 58598052973466112000 : ℝ) ≤ (11412940981035286111488147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (937481 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_184 : rowCell 6 184 ≤ (215284890513969781205579 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (97644130341959218267351 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11412940981035286111488147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_184_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_184_1
  · norm_num [gridPoint]

theorem exp_6_185_0 : expNegUpper (118528064363313835327727 / 1473142842053923328000 : ℝ) ≤ (11412937499742690389772061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (937481 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_185_1 : expNegUpper (59313808017858581910763 / 736571421026961664000 : ℝ) ≤ (10417148140935444075059 / 976562500000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (117247 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_185 : rowCell 6 185 ≤ (1610100525124062452824307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11412937499742690389772061 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10417148140935444075059 / 976562500000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_185_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_185_1
  · norm_num [gridPoint]

theorem exp_6_186_0 : expNegUpper (59644546525606471311707 / 740678599038474496000 : ℝ) ≤ (5333578239273366289509313 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (117247 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_186_1 : expNegUpper (4775593708802353606357 / 59254287923077959680 : ℝ) ≤ (4982892871726308740113151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1876949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_186 : rowCell 6 186 ≤ (150457268423722018386121 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5333578239273366289509313 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4982892871726308740113151 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_186_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_186_1
  · norm_num [gridPoint]

theorem exp_6_187_0 : expNegUpper (4802148762368772238157 / 59583775696229191680 : ℝ) ≤ (9965782770453802354569523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1876949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_187_1 : expNegUpper (30038917513821830360209 / 372398598101432448000 : ℝ) ≤ (2326630358695195382775789 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1877953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_187 : rowCell 6 187 ≤ (87834608600407202961857 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9965782770453802354569523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2326630358695195382775789 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_187_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_187_1
  · norm_num [gridPoint]

theorem exp_6_188_0 : expNegUpper (30205488094917893012081 / 374463606260066432000 : ℝ) ≤ (4653259344516130780261851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1877953 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_188_1 : expNegUpper (120925108033741254396323 / 1497854425040265728000 : ℝ) ≤ (4343580306022005025585521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1878963 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_188 : rowCell 6 188 ≤ (1312115260830728786637557 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4653259344516130780261851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4343580306022005025585521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_188_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_188_1
  · norm_num [gridPoint]

theorem exp_6_189_0 : expNegUpper (4863752120196335505427 / 60245491839222272000 : ℝ) ≤ (1737431615435966853595703 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1878963 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_189_1 : expNegUpper (2433963332955185715089 / 30122745919611136000 : ℝ) ≤ (8105587199121363159671043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879981 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_189 : rowCell 6 189 ≤ (122454207277996749328127 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1737431615435966853595703 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8105587199121363159671043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_189_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_189_1
  · norm_num [gridPoint]

theorem exp_6_190_0 : expNegUpper (61184640463634199722521 / 757221502613301504000 : ℝ) ≤ (506599053741502154978699 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879981 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_190_1 : expNegUpper (122474855889680062244281 / 1514443005226603008000 : ℝ) ≤ (7559773574281991920555683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376201 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_190 : rowCell 6 190 ≤ (1142332011363396423174263 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (506599053741502154978699 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7559773574281991920555683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_190_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_190_1
  · norm_num [gridPoint]

theorem exp_6_191_0 : expNegUpper (123148396139090254205489 / 1522771552778404352000 : ℝ) ≤ (302390856655121069218003 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376201 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_191_1 : expNegUpper (385172455474506970609 / 4758661102432513600 : ℝ) ≤ (1761944696112284426304673 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470509 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_191 : rowCell 6 191 ≤ (213039136923040077260903 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (302390856655121069218003 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1761944696112284426304673 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_191_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_191_1
  · norm_num [gridPoint]

theorem sum_6_160_2 : blockSum (rowCell 6) 160 2 ≤ (14656247305460863433019657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_160) (by simpa only [blockSum_one] using cell_6_161) (by norm_num)

theorem sum_6_162_2 : blockSum (rowCell 6) 162 2 ≤ (13097582720009414126926429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_162) (by simpa only [blockSum_one] using cell_6_163) (by norm_num)

theorem sum_6_160_4 : blockSum (rowCell 6) 160 4 ≤ (13876915012735138779973043 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_160_2 sum_6_162_2 (by norm_num)

theorem sum_6_164_2 : blockSum (rowCell 6) 164 2 ≤ (11679930721504529029316799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_164) (by simpa only [blockSum_one] using cell_6_165) (by norm_num)

theorem sum_6_166_2 : blockSum (rowCell 6) 166 2 ≤ (10394086291258022346050649 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_166) (by simpa only [blockSum_one] using cell_6_167) (by norm_num)

theorem sum_6_164_4 : blockSum (rowCell 6) 164 4 ≤ (2759252126595318921920931 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_164_2 sum_6_166_2 (by norm_num)

theorem sum_6_160_8 : blockSum (rowCell 6) 160 8 ≤ (24913923519116414467656767 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_160_4 sum_6_164_4 (by norm_num)

theorem sum_6_168_2 : blockSum (rowCell 6) 168 2 ≤ (4615461295300834290496173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_168) (by simpa only [blockSum_one] using cell_6_169) (by norm_num)

theorem sum_6_170_2 : blockSum (rowCell 6) 170 2 ≤ (1636296775250188541613103 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_170) (by simpa only [blockSum_one] using cell_6_171) (by norm_num)

theorem sum_6_168_4 : blockSum (rowCell 6) 168 4 ≤ (17412406466852611289057861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_168_2 sum_6_170_2 (by norm_num)

theorem sum_6_172_2 : blockSum (rowCell 6) 172 2 ≤ (180926557079588146597499 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_172) (by simpa only [blockSum_one] using cell_6_173) (by norm_num)

theorem sum_6_174_2 : blockSum (rowCell 6) 174 2 ≤ (6389259690402672540278483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_174) (by simpa only [blockSum_one] using cell_6_175) (by norm_num)

theorem sum_6_172_4 : blockSum (rowCell 6) 172 4 ≤ (13626321973586198404178443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_172_2 sum_6_174_2 (by norm_num)

theorem sum_6_168_8 : blockSum (rowCell 6) 168 8 ≤ (1939920527527425605827269 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_168_4 sum_6_172_4 (by norm_num)

theorem sum_6_160_16 : blockSum (rowCell 6) 160 16 ≤ (40433287739335819314274919 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_160_8 sum_6_168_8 (by norm_num)

theorem sum_6_176_2 : blockSum (rowCell 6) 176 2 ≤ (5630035977741112470012117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_176) (by simpa only [blockSum_one] using cell_6_177) (by norm_num)

theorem sum_6_178_2 : blockSum (rowCell 6) 178 2 ≤ (4951745029789888975852837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_178) (by simpa only [blockSum_one] using cell_6_179) (by norm_num)

theorem sum_6_176_4 : blockSum (rowCell 6) 176 4 ≤ (5290890503765500722932477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_176_2 sum_6_178_2 (by norm_num)

theorem sum_6_180_2 : blockSum (rowCell 6) 180 2 ≤ (2173579926462633812078317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_180) (by simpa only [blockSum_one] using cell_6_181) (by norm_num)

theorem sum_6_182_2 : blockSum (rowCell 6) 182 2 ≤ (1904744074923103171501843 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_182) (by simpa only [blockSum_one] using cell_6_183) (by norm_num)

theorem sum_6_180_4 : blockSum (rowCell 6) 180 4 ≤ (1593095313041303509211 / 195312500000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_180_2 sum_6_182_2 (by norm_num)

theorem sum_6_176_8 : blockSum (rowCell 6) 176 8 ≤ (9369214505151237706512637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_176_4 sum_6_180_4 (by norm_num)

theorem sum_6_184_2 : blockSum (rowCell 6) 184 2 ≤ (3332379649235820702468939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_184) (by simpa only [blockSum_one] using cell_6_185) (by norm_num)

theorem sum_6_186_2 : blockSum (rowCell 6) 186 2 ≤ (1454963210921867715625461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_186) (by simpa only [blockSum_one] using cell_6_187) (by norm_num)

theorem sum_6_184_4 : blockSum (rowCell 6) 184 4 ≤ (6242306071079556133719861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_184_2 sum_6_186_2 (by norm_num)

theorem sum_6_188_2 : blockSum (rowCell 6) 188 2 ≤ (2536657333610696279918827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_188) (by simpa only [blockSum_one] using cell_6_189) (by norm_num)

theorem sum_6_190_2 : blockSum (rowCell 6) 190 2 ≤ (1103763847989298404739389 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_190) (by simpa only [blockSum_one] using cell_6_191) (by norm_num)

theorem sum_6_188_4 : blockSum (rowCell 6) 188 4 ≤ (948837005917858617879521 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_188_2 sum_6_190_2 (by norm_num)

theorem sum_6_184_8 : blockSum (rowCell 6) 184 8 ≤ (5493245550334424611558733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_184_4 sum_6_188_4 (by norm_num)

theorem sum_6_176_16 : blockSum (rowCell 6) 176 16 ≤ (1486246005548566231807137 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_176_8 sum_6_184_8 (by norm_num)

theorem sum_6_160_32 : blockSum (rowCell 6) 160 32 ≤ (55295747794821481632346289 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_160_16 sum_6_176_16 (by norm_num)

#print axioms sum_6_160_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
