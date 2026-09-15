import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_160_0 : expNegUpper (3106991976329223304411 / 39850199714021904000 : ℝ) ≤ (17250406851617210558418789 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459701 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_160_1 : expNegUpper (99498068374387707840751 / 1275206390848700928000 : ℝ) ≤ (130189682645326705000040999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839641 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_160 : rowCell 4 160 ≤ (19556869954048886939374587 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17250406851617210558418789 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (130189682645326705000040999 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_160_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_160_1
  · norm_num [gridPoint]

theorem exp_4_161_0 : expNegUpper (100094445570652975112039 / 1282849789227848192000 : ℝ) ≤ (130189631911748506329164981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1839641 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_161_1 : expNegUpper (2003397708589187670223 / 25656995784556963840 : ℝ) ≤ (122754402483689689129695627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840487 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_161 : rowCell 4 161 ≤ (18444906242521255364363849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (130189631911748506329164981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (122754402483689689129695627 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_161_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_161_1
  · norm_num [gridPoint]

theorem exp_4_162_0 : expNegUpper (2015369908208237845823 / 25810320518255011840 : ℝ) ≤ (122754355215052454934811059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1840487 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_162_1 : expNegUpper (100845053326951695899461 / 1290516025912750592000 : ℝ) ≤ (115683932778057436456616371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (92067 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_162 : rowCell 4 162 ≤ (2173391772794617761241367 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (122754355215052454934811059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (115683932778057436456616371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_162_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_162_1
  · norm_num [gridPoint]

theorem exp_4_163_0 : expNegUpper (101445902754150544007549 / 1298205100903408128000 : ℝ) ≤ (57841944379459080887393687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (92067 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_163_1 : expNegUpper (25380895514800822933687 / 324551275225852032000 : ℝ) ≤ (108964860315208831714150483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842201 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_163 : rowCell 4 163 ≤ (8190794307672918325592031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (57841944379459080887393687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (108964860315208831714150483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_163_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_163_1
  · norm_num [gridPoint]

theorem exp_4_164_0 : expNegUpper (1021266775942075769903 / 13059170141998208000 : ℝ) ≤ (108964819341734506788175463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1842201 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_164_1 : expNegUpper (4088219264742112709843 / 52236680567992832000 : ℝ) ≤ (51291962775560994149467771 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184307 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_164 : rowCell 4 164 ≤ (48207264190351829054717 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (108964819341734506788175463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51291962775560994149467771 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_164_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_164_1
  · norm_num [gridPoint]

theorem exp_4_165_0 : expNegUpper (102810829922921637968467 / 1313651765801988608000 : ℝ) ≤ (102583887430612436140154313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184307 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_165_1 : expNegUpper (51445380998669460331253 / 656825882900994304000 : ℝ) ≤ (96528050543960881743540209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (921973 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_165 : rowCell 4 165 ≤ (14519421406737660370794291 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (102583887430612436140154313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (96528050543960881743540209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_165_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_165_1
  · norm_num [gridPoint]

theorem exp_4_166_0 : expNegUpper (51749184866315686835557 / 660704677854955776000 : ℝ) ≤ (96528015094378587117591083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (921973 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_166_1 : expNegUpper (20715886637580049442621 / 264281871141982310400 : ℝ) ≤ (45392182016414453010088049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184483 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_166 : rowCell 4 166 ≤ (13658986974421592500088099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (96528015094378587117591083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45392182016414453010088049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_166_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_166_1
  · norm_num [gridPoint]

theorem exp_4_167_0 : expNegUpper (20837861403135086165461 / 265837956784717926400 : ℝ) ≤ (90784331082336982581844641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (184483 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_167_1 : expNegUpper (13033938147821930515867 / 166148722990448704000 : ℝ) ≤ (1333440996656346868545119 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1845721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_167 : rowCell 4 167 ≤ (6421580388952174685410843 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (90784331082336982581844641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1333440996656346868545119 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_167_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_167_1
  · norm_num [gridPoint]

theorem exp_4_168_0 : expNegUpper (13110456470549057020763 / 167124131305377856000 : ℝ) ≤ (85340193172515498233573053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1845721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_168_1 : expNegUpper (104966987973703158133063 / 1336993050443022848000 : ℝ) ≤ (5011452271611728363515089 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (92331 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_168 : rowCell 4 168 ≤ (6035058596465436848980321 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (85340193172515498233573053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5011452271611728363515089 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_168_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_168_1
  · norm_num [gridPoint]

theorem exp_4_169_0 : expNegUpper (4223256558844843856663 / 53792766210728448000 : ℝ) ≤ (80183207916513880387486719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (92331 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_169_1 : expNegUpper (2113317831072440719211 / 26896383105364224000 : ℝ) ≤ (18825318574845755520622077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1847527 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_169 : rowCell 4 169 ≤ (2834517034068173243245973 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (80183207916513880387486719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18825318574845755520622077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_169_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_169_1
  · norm_num [gridPoint]

theorem exp_4_170_0 : expNegUpper (53141301814099999153891 / 676334049199577344000 : ℝ) ≤ (75301247910414606230676267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1847527 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_170_1 : expNegUpper (106368225914670724338461 / 1352668098399154688000 : ℝ) ≤ (35341245603356871713459479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1848441 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_170 : rowCell 4 170 ≤ (1064526541368661230203349 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (75301247910414606230676267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35341245603356871713459479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_170_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_170_1
  · norm_num [gridPoint]

theorem exp_4_171_0 : expNegUpper (4651618727302948198643 / 59153907818950144000 : ℝ) ≤ (88353083403238853370697 / 1250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1848441 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_171_1 : expNegUpper (232769567498234499991 / 2957695390947507200 : ℝ) ≤ (16578833579106512492289977 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924681 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_171 : rowCell 4 171 ≤ (9990002735727000305939251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (88353083403238853370697 / 1250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16578833579106512492289977 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_171_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_171_1
  · norm_num [gridPoint]

theorem exp_4_172_0 : expNegUpper (5384765263138158696433 / 68421724978915353600 : ℝ) ≤ (66315311609732643680255327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924681 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_172_1 : expNegUpper (107783226949512119661811 / 1368434499578307072000 : ℝ) ≤ (7773569400139747943082031 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (185029 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_172 : rowCell 4 172 ≤ (187412348410801312217019 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (66315311609732643680255327 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7773569400139747943082031 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_172_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_172_1
  · norm_num [gridPoint]

theorem exp_4_173_0 : expNegUpper (108406837224924741116459 / 1376351957626515968000 : ℝ) ≤ (62188534152083869772816083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (185029 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_173_1 : expNegUpper (54247956803991060032689 / 688175978813257984000 : ℝ) ≤ (58291218441728243590220331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (925613 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_173 : rowCell 4 173 ≤ (1757098360533700061900643 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (62188534152083869772816083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58291218441728243590220331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_173_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_173_1
  · norm_num [gridPoint]

theorem exp_4_174_0 : expNegUpper (2816047396304287919 / 35723671070464000 : ℝ) ≤ (58291198937846059133570261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (925613 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_174_1 : expNegUpper (5636752052487046087 / 71447342140928000 : ℝ) ≤ (6826588561166732204160727 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852169 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_174 : rowCell 4 174 ≤ (257282948959196519924863 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58291198937846059133570261 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6826588561166732204160727 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_174_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_174_1
  · norm_num [gridPoint]

theorem exp_4_175_0 : expNegUpper (109840313400701067892097 / 1392255388640199168000 : ℝ) ≤ (13653172606246938772111521 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852169 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_175_1 : expNegUpper (6870731823044622500101 / 87015961790012448000 : ℝ) ≤ (12785683707581273864214167 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1853119 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_175 : rowCell 4 175 ≤ (7711780624257290881902639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13653172606246938772111521 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12785683707581273864214167 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_175_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_175_1
  · norm_num [gridPoint]

theorem exp_4_176_0 : expNegUpper (6910142349937070058629 / 87515085100354592000 : ℝ) ≤ (2557135905321633655283067 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1853119 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_176_1 : expNegUpper (22130967611130618598483 / 280048272321134694400 : ℝ) ≤ (47871335578140204155444533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1854077 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_176 : rowCell 4 176 ≤ (1444038750523582288664851 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2557135905321633655283067 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (47871335578140204155444533 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_176_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_176_1
  · norm_num [gridPoint]

theorem exp_4_177_0 : expNegUpper (22257547838801192545643 / 281650034575380582400 : ℝ) ≤ (47871320101807532985977399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1854077 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_177_1 : expNegUpper (55690733835046281818543 / 704125086438451456000 : ℝ) ≤ (22394439805758174651285283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1855041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_177 : rowCell 4 177 ≤ (1689216253123439358976603 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (47871320101807532985977399 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22394439805758174651285283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_177_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_177_1
  · norm_num [gridPoint]

theorem exp_4_178_0 : expNegUpper (56008354089039119995807 / 708140911226943744000 : ℝ) ≤ (44788865295706116834405641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1855041 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_178_1 : expNegUpper (112111608004371018664693 / 1416281822453887488000 : ℝ) ≤ (41886067375609926218476761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464003 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_178 : rowCell 4 178 ≤ (197512936325068367028863 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (44788865295706116834405641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41886067375609926218476761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_178_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_178_1
  · norm_num [gridPoint]

theorem exp_4_179_0 : expNegUpper (4509967781741943978293 / 56973452413465088000 : ℝ) ≤ (10471513534705664636317931 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464003 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_179_1 : expNegUpper (1128452690508271048043 / 14243363103366272000 : ℝ) ≤ (3915393045841875003780767 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1856991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_179 : rowCell 4 179 ≤ (2954754243096002548978087 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10471513534705664636317931 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3915393045841875003780767 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_179_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_179_1
  · norm_num [gridPoint]

theorem exp_4_180_0 : expNegUpper (28371302070688921963603 / 358103409131280512000 : ℝ) ≤ (9788479556096755326774803 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1856991 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_180_1 : expNegUpper (113582460801799468784971 / 1432413636525122048000 : ℝ) ≤ (18291915025378171282974821 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (232247 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_180 : rowCell 4 180 ≤ (5522864649856670042738703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9788479556096755326774803 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18291915025378171282974821 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_180_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_180_1
  · norm_num [gridPoint]

theorem exp_4_181_0 : expNegUpper (114224759388038151911939 / 1440513801019372032000 : ℝ) ≤ (2286488671759489665604523 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (232247 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_181_1 : expNegUpper (11432319324962675733577 / 144051380101937203200 : ℝ) ≤ (6833490878727315418918473 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (232371 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_181 : rowCell 4 181 ≤ (5159246403096174309917961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2286488671759489665604523 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6833490878727315418918473 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_181_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_181_1
  · norm_num [gridPoint]

theorem exp_4_182_0 : expNegUpper (11496785785173463835897 / 144863680381937715200 : ℝ) ≤ (34167443955789811127793749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (232371 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_182_1 : expNegUpper (115067476386647617185761 / 1448636803819377152000 : ℝ) ≤ (15948407656186731244005953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1859967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_182 : rowCell 4 182 ≤ (602183142555300269063211 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34167443955789811127793749 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15948407656186731244005953 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_182_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_182_1
  · norm_num [gridPoint]

theorem exp_4_183_0 : expNegUpper (115714513666183793924569 / 1456782644925137408000 : ℝ) ≤ (31896805677005987932966179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1859967 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_183_1 : expNegUpper (14476915025650086883001 / 182097830615642176000 : ℝ) ≤ (1190569757281207864568829 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1860973 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_183 : rowCell 4 183 ≤ (1124094784022544173906981 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31896805677005987932966179 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1190569757281207864568829 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_183_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_183_1
  · norm_num [gridPoint]

theorem exp_4_184_0 : expNegUpper (582323684118621326689 / 7324756621683264000 : ℝ) ≤ (1860264690062437013279607 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1860973 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_184_1 : expNegUpper (4662669387904985507983 / 58598052973466112000 : ℝ) ≤ (27762385664104419552444289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (372397 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_184 : rowCell 4 184 ≤ (4194892865889430527244329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1860264690062437013279607 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27762385664104419552444289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_184_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_184_1
  · norm_num [gridPoint]

theorem exp_4_185_0 : expNegUpper (117218537316694699327727 / 1473142842053923328000 : ℝ) ≤ (6940594365789558408557079 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (372397 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_185_1 : expNegUpper (58660864928129045910763 / 736571421026961664000 : ℝ) ≤ (6471048637387457525736701 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (372601 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_185 : rowCell 4 185 ≤ (244497264328669667194739 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6940594365789558408557079 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6471048637387457525736701 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_185_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_185_1
  · norm_num [gridPoint]

theorem exp_4_186_0 : expNegUpper (58987962568716871311707 / 740678599038474496000 : ℝ) ≤ (6471046747024291228902137 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (372601 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_186_1 : expNegUpper (4723212626937588166357 / 59254287923077959680 : ℝ) ≤ (24122927038441441752459957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1864031 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_186 : rowCell 4 186 ≤ (455820460385212927064373 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6471046747024291228902137 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24122927038441441752459957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_186_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_186_1
  · norm_num [gridPoint]

theorem exp_4_187_0 : expNegUpper (4749476411131201678157 / 59583775696229191680 : ℝ) ≤ (12061460034664933719919031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1864031 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_187_1 : expNegUpper (29710625535377030360209 / 372398598101432448000 : ℝ) ≤ (11236067640911391827651027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1865063 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_187 : rowCell 4 187 ≤ (1698876649475546684533793 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12061460034664933719919031 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11236067640911391827651027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_187_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_187_1
  · norm_num [gridPoint]

theorem exp_4_188_0 : expNegUpper (29875375682893061012081 / 374463606260066432000 : ℝ) ≤ (11236064430564625985676653 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1865063 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_188_1 : expNegUpper (119608299252801990396323 / 1497854425040265728000 : ℝ) ≤ (20925660006555065102584981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (933051 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_188 : rowCell 4 188 ≤ (1582302877216238105580101 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11236064430564625985676653 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20925660006555065102584981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_188_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_188_1
  · norm_num [gridPoint]

theorem exp_4_189_0 : expNegUpper (4810788499585959825427 / 60245491839222272000 : ℝ) ≤ (837026163735475223562033 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (933051 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_189_1 : expNegUpper (2407554339993199155089 / 30122745919611136000 : ℝ) ≤ (19477623039344364970643687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466787 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_189 : rowCell 4 189 ≤ (2946243268338061364441357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (837026163735475223562033 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19477623039344364970643687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_189_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_189_1
  · norm_num [gridPoint]

theorem exp_4_190_0 : expNegUpper (60520774772424471722521 / 757221502613301504000 : ℝ) ≤ (19477617595650461896032843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466787 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_190_1 : expNegUpper (121150765374420670244281 / 1514443005226603008000 : ℝ) ≤ (18122419541573966374342523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (9341 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_190 : rowCell 4 190 ≤ (1370914244664885392274023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19477617595650461896032843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18122419541573966374342523 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_190_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_190_1
  · norm_num [gridPoint]

theorem exp_4_191_0 : expNegUpper (121817023889510734205489 / 1522771552778404352000 : ℝ) ≤ (566325454123941654942939 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (9341 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_191_1 : expNegUpper (381023294904446170609 / 4758661102432513600 : ℝ) ≤ (8427355006066460642804679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1869259 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_191 : rowCell 4 191 ≤ (1275281673258017812225367 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (566325454123941654942939 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8427355006066460642804679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_191_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_191_1
  · norm_num [gridPoint]

theorem sum_4_160_2 : blockSum (rowCell 4) 160 2 ≤ (9500444049142535575934609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_160) (by simpa only [blockSum_one] using cell_4_161) (by norm_num)

theorem sum_4_162_2 : blockSum (rowCell 4) 162 2 ≤ (16884361398851389370557499 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_162) (by simpa only [blockSum_one] using cell_4_163) (by norm_num)

theorem sum_4_160_4 : blockSum (rowCell 4) 160 4 ≤ (35885249497136460522426717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_160_2 sum_4_162_2 (by norm_num)

theorem sum_4_164_2 : blockSum (rowCell 4) 164 2 ≤ (29945745947650245668303731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_164) (by simpa only [blockSum_one] using cell_4_165) (by norm_num)

theorem sum_4_166_2 : blockSum (rowCell 4) 166 2 ≤ (5300429550465188374181957 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_166) (by simpa only [blockSum_one] using cell_4_167) (by norm_num)

theorem sum_4_164_4 : blockSum (rowCell 4) 164 4 ≤ (14111973424994046884803379 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_164_2 sum_4_166_2 (by norm_num)

theorem sum_4_160_8 : blockSum (rowCell 4) 160 8 ≤ (2564367853884982171681339 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_160_4 sum_4_164_4 (by norm_num)

theorem sum_4_168_2 : blockSum (rowCell 4) 168 2 ≤ (11704092664601783335472267 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_168) (by simpa only [blockSum_one] using cell_4_169) (by norm_num)

theorem sum_4_170_2 : blockSum (rowCell 4) 170 2 ≤ (20635268149413612607972741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_170) (by simpa only [blockSum_one] using cell_4_171) (by norm_num)

theorem sum_4_168_4 : blockSum (rowCell 4) 168 4 ≤ (1761738139144687171156691 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_168_2 sum_4_170_2 (by norm_num)

theorem sum_4_172_2 : blockSum (rowCell 4) 172 2 ≤ (3631221844641713184070833 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_172) (by simpa only [blockSum_one] using cell_4_173) (by norm_num)

theorem sum_4_174_2 : blockSum (rowCell 4) 174 2 ≤ (3188966998190315903899651 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_174) (by simpa only [blockSum_one] using cell_4_175) (by norm_num)

theorem sum_4_172_4 : blockSum (rowCell 4) 172 4 ≤ (1705047210708007271992621 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_172_2 sum_4_174_2 (by norm_num)

theorem sum_4_168_8 : blockSum (rowCell 4) 168 8 ≤ (15628879538555464943753939 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_168_4 sum_4_172_4 (by norm_num)

theorem sum_4_160_16 : blockSum (rowCell 4) 160 16 ≤ (41272558077405286660567329 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_160_8 sum_4_168_8 (by norm_num)

theorem sum_4_176_2 : blockSum (rowCell 4) 176 2 ≤ (13977058765111668879230667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_176) (by simpa only [blockSum_one] using cell_4_177) (by norm_num)

theorem sum_4_178_2 : blockSum (rowCell 4) 178 2 ≤ (1222992244859419284287979 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_178) (by simpa only [blockSum_one] using cell_4_179) (by norm_num)

theorem sum_4_176_4 : blockSum (rowCell 4) 176 4 ≤ (26206981213705861722110457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_176_2 sum_4_178_2 (by norm_num)

theorem sum_4_180_2 : blockSum (rowCell 4) 180 2 ≤ (1335263881619105544082083 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_180) (by simpa only [blockSum_one] using cell_4_181) (by norm_num)

theorem sum_4_182_2 : blockSum (rowCell 4) 182 2 ≤ (2328461069133144712033403 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_182) (by simpa only [blockSum_one] using cell_4_183) (by norm_num)

theorem sum_4_180_4 : blockSum (rowCell 4) 180 4 ≤ (4998988832371355800197569 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_180_2 sum_4_182_2 (by norm_num)

theorem sum_4_176_8 : blockSum (rowCell 4) 176 8 ≤ (46202936543191284922900733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_176_4 sum_4_180_4 (by norm_num)

theorem sum_4_184_2 : blockSum (rowCell 4) 184 2 ≤ (8106849095148145202360153 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_184) (by simpa only [blockSum_one] using cell_4_185) (by norm_num)

theorem sum_4_186_2 : blockSum (rowCell 4) 186 2 ≤ (704431698203279678558257 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_186) (by simpa only [blockSum_one] using cell_4_187) (by norm_num)

theorem sum_4_184_4 : blockSum (rowCell 4) 184 4 ≤ (15151166077180941987942723 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_184_2 sum_4_186_2 (by norm_num)

theorem sum_4_188_2 : blockSum (rowCell 4) 188 2 ≤ (6110849022770537575601559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_188) (by simpa only [blockSum_one] using cell_4_189) (by norm_num)

theorem sum_4_190_2 : blockSum (rowCell 4) 190 2 ≤ (264619591792290320449939 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_190) (by simpa only [blockSum_one] using cell_4_191) (by norm_num)

theorem sum_4_188_4 : blockSum (rowCell 4) 188 4 ≤ (11403240858616343984600339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_188_2 sum_4_190_2 (by norm_num)

theorem sum_4_184_8 : blockSum (rowCell 4) 184 8 ≤ (13277203467898642986271531 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_184_4 sum_4_188_4 (by norm_num)

theorem sum_4_176_16 : blockSum (rowCell 4) 176 16 ≤ (14551468695797714179088759 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_176_8 sum_4_184_8 (by norm_num)

theorem sum_4_160_32 : blockSum (rowCell 4) 160 32 ≤ (6978003346650375104957011 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_160_16 sum_4_176_16 (by norm_num)

#print axioms sum_4_160_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
