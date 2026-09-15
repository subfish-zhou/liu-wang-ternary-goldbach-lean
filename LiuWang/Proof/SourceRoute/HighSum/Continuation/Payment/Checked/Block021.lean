import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_160_0 : expNegUpper (976431092294999768137 / 13283399904673968000 : ℝ) ≤ (2385124150815895015284150279 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (221981 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_160_1 : expNegUpper (31276233568528723946917 / 425068796949566976000 : ℝ) ≤ (11101501962923212722278029659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (888421 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_160 : rowCell 1 160 ≤ (839579238477201025691717129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2385124150815895015284150279 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11101501962923212722278029659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_160_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_160_1
  · norm_num [gridPoint]

theorem exp_1_161_0 : expNegUpper (7260853575001859624003 / 98680753017526784000 : ℝ) ≤ (1387687286888493350919706733 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (888421 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_161_1 : expNegUpper (145359272380375716171 / 1973615060350535680 : ℝ) ≤ (10329760627712360116174860869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (888921 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_161 : rowCell 1 161 ≤ (781393327649372626116746293 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1387687286888493350919706733 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10329760627712360116174860869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_161_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_161_1
  · norm_num [gridPoint]

theorem exp_1_162_0 : expNegUpper (1900963112027389205823 / 25810320518255011840 : ℝ) ≤ (516487862767959158573285749 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (888921 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_162_1 : expNegUpper (95141704231322895899461 / 1290516025912750592000 : ℝ) ≤ (9607455995756348216695997657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1778849 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_162 : rowCell 1 162 ≤ (726919751305687423967491819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (516487862767959158573285749 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9607455995756348216695997657 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_162_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_162_1
  · norm_num [gridPoint]

theorem exp_1_163_0 : expNegUpper (31902857410564826669183 / 432735033634469376000 : ℝ) ≤ (9607452896313063398847540009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1778849 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_163_1 : expNegUpper (7983603520846738311229 / 108183758408617344000 : ℝ) ≤ (8931776973323990758709555201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1779863 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_163 : rowCell 1 163 ≤ (1351897298433269991209908063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9607452896313063398847540009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8931776973323990758709555201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_163_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_163_1
  · norm_num [gridPoint]

theorem exp_1_164_0 : expNegUpper (963723563583378809903 / 13059170141998208000 : ℝ) ≤ (4465887062921010534636512523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1779863 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_164_1 : expNegUpper (3858726043843870149843 / 52236680567992832000 : ℝ) ≤ (2075010679940657566530839953 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1780883 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_164 : rowCell 1 164 ≤ (125655956609193839830603853 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4465887062921010534636512523 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2075010679940657566530839953 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_164_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_164_1
  · norm_num [gridPoint]

theorem exp_1_165_0 : expNegUpper (97039517973638309968467 / 1313651765801988608000 : ℝ) ≤ (518752506549619341201866629 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1780883 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_165_1 : expNegUpper (48568220380734612331253 / 656825882900994304000 : ℝ) ≤ (1927424773399109890531371907 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (178191 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_165 : rowCell 1 165 ≤ (583722283048342652233215633 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (518752506549619341201866629 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1927424773399109890531371907 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_165_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_165_1
  · norm_num [gridPoint]

theorem exp_1_166_0 : expNegUpper (16285011178322402278519 / 220234892618318592000 : ℝ) ≤ (7709696693095930688286202613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (178191 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_166_1 : expNegUpper (6520541415907794614207 / 88093957047327436800 : ℝ) ≤ (1431662993664051640586721859 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1782943 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_166 : rowCell 1 166 ≤ (27104719208242388688873891 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7709696693095930688286202613 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1431662993664051640586721859 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_166_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_166_1
  · norm_num [gridPoint]

theorem exp_1_167_0 : expNegUpper (19676802727912967765461 / 265837956784717926400 : ℝ) ≤ (7158312765553885368428616501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1782943 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_167_1 : expNegUpper (12310400314984810515867 / 166148722990448704000 : ℝ) ≤ (1328715689153950671219962027 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1783983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_167 : rowCell 1 167 ≤ (1006446307266354909374279439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7158312765553885368428616501 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1328715689153950671219962027 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_167_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_167_1
  · norm_num [gridPoint]

theorem exp_1_168_0 : expNegUpper (12382670959358529020763 / 167124131305377856000 : ℝ) ≤ (6643576425227531278642822941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1783983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_168_1 : expNegUpper (99161694597592566133063 / 1336993050443022848000 : ℝ) ≤ (385205812045607914705371427 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1785029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_168 : rowCell 1 168 ≤ (466944212064592971528796323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6643576425227531278642822941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (385205812045607914705371427 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_168_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_168_1
  · norm_num [gridPoint]

theorem exp_1_169_0 : expNegUpper (1329895188909109872221 / 17930922070242816000 : ℝ) ≤ (6163291140043872773140905789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1785029 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_169_1 : expNegUpper (665624049760652079737 / 8965461035121408000 : ℝ) ≤ (357210845269012884930252183 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (893041 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_169 : rowCell 1 169 ≤ (866202899562046290950424169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6163291140043872773140905789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (357210845269012884930252183 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_169_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_169_1
  · norm_num [gridPoint]

theorem exp_1_170_0 : expNegUpper (50213169055924255153891 / 676334049199577344000 : ℝ) ≤ (5715371826172021446718933097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (893041 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_170_1 : expNegUpper (100528951111732868338461 / 1352668098399154688000 : ℝ) ≤ (5297842455519593381963835353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1787141 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_170 : rowCell 1 170 ≤ (803093480105658760617745121 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5715371826172021446718933097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5297842455519593381963835353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_170_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_170_1
  · norm_num [gridPoint]

theorem exp_1_171_0 : expNegUpper (101113974498202688568789 / 1360539879835853312000 : ℝ) ≤ (5297840899630899795751705491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1787141 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_171_1 : expNegUpper (5060886776641819099793 / 68026993991792665600 : ℝ) ≤ (196353029626777984979435631 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (894103 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_171 : rowCell 1 171 ≤ (148855860292552224913781553 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5297840899630899795751705491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (196353029626777984979435631 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_171_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_171_1
  · norm_num [gridPoint]

theorem exp_1_172_0 : expNegUpper (1696750971993073698811 / 22807241659638451200 : ℝ) ≤ (1227206078909593950443358177 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (894103 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_172_1 : expNegUpper (33969990239915666553937 / 456144833192769024000 : ℝ) ≤ (909309783607865402038475253 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1789277 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_172 : rowCell 1 172 ≤ (172373577815416930339916729 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1227206078909593950443358177 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (909309783607865402038475253 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_172_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_172_1
  · norm_num [gridPoint]

theorem exp_1_173_0 : expNegUpper (102499599568332357116459 / 1376351957626515968000 : ℝ) ≤ (568318451667529607710414299 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1789277 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_173_1 : expNegUpper (51302833332401684032689 / 688175978813257984000 : ℝ) ≤ (2104666587937118406818541833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358071 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_173 : rowCell 1 173 ≤ (319243346880582990141528049 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (568318451667529607710414299 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2104666587937118406818541833 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_173_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_173_1
  · norm_num [gridPoint]

theorem exp_1_174_0 : expNegUpper (204858775656149163 / 2747974697728000 : ℝ) ≤ (4209331981781600376215673137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (358071 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_174_1 : expNegUpper (410143258998884899 / 5495949395456000 : ℝ) ≤ (3895591453770908286751705209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1791439 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_174 : rowCell 1 174 ≤ (295509149343819030455291557 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4209331981781600376215673137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3895591453770908286751705209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_174_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_174_1
  · norm_num [gridPoint]

theorem exp_1_175_0 : expNegUpper (34633031439093806630699 / 464085129546733056000 : ℝ) ≤ (1947795180651459446876242069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1791439 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_175_1 : expNegUpper (2166822516639748833367 / 29005320596670816000 : ℝ) ≤ (900956148023038992021429479 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112033 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_175 : rowCell 1 175 ≤ (546864076157191049812812877 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1947795180651459446876242069 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (900956148023038992021429479 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_175_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_175_1
  · norm_num [gridPoint]

theorem exp_1_176_0 : expNegUpper (6537754237634990058629 / 87515085100354592000 : ℝ) ≤ (3603823592957903064450533579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112033 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_176_1 : expNegUpper (20942723794446688998483 / 280048272321134694400 : ℝ) ≤ (833154385127748092017142609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224203 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_176 : rowCell 1 176 ≤ (505811519411382705900033219 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3603823592957903064450533579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (833154385127748092017142609 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_176_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_176_1
  · norm_num [gridPoint]

theorem exp_1_177_0 : expNegUpper (21062507736751810145643 / 281650034575380582400 : ℝ) ≤ (3332616627061004898038292381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (224203 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_177_1 : expNegUpper (52711628936629641818543 / 704125086438451456000 : ℝ) ≤ (3080635635396542642372699687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897363 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_177 : rowCell 1 177 ≤ (11691502922118347958740947 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3332616627061004898038292381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3080635635396542642372699687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_177_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_177_1
  · norm_num [gridPoint]

theorem exp_1_178_0 : expNegUpper (17670752825736282665269 / 236046970408981248000 : ℝ) ≤ (3080634800576523814571453453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (897363 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_178_1 : expNegUpper (35378802498041368888231 / 472093940817962496000 : ℝ) ≤ (569324190890152015634951353 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (359167 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_178 : rowCell 1 178 ≤ (432220814925431948784426039 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3080634800576523814571453453 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (569324190890152015634951353 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_178_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_178_1
  · norm_num [gridPoint]

theorem exp_1_179_0 : expNegUpper (4269600504258976938293 / 56973452413465088000 : ℝ) ≤ (569324038351668080609351957 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (359167 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_179_1 : expNegUpper (1068530778271665608043 / 14243363103366272000 : ℝ) ≤ (1314694377896187295441593679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1796949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_179 : rowCell 1 179 ≤ (79863098461437390490574821 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (569324038351668080609351957 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1314694377896187295441593679 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_179_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_179_1
  · norm_num [gridPoint]

theorem exp_1_180_0 : expNegUpper (26864758908066969963603 / 358103409131280512000 : ℝ) ≤ (2629388059236716330413540201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1796949 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_180_1 : expNegUpper (107573278864725292784971 / 1432413636525122048000 : ℝ) ≤ (2427824007560013961557273461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_180 : rowCell 1 180 ≤ (14751057899991353423115337 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2629388059236716330413540201 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2427824007560013961557273461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_180_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_180_1
  · norm_num [gridPoint]

theorem exp_1_181_0 : expNegUpper (36060532008045570637313 / 480171267006457344000 : ℝ) ≤ (2427823371624106478947245967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1798069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_181_1 : expNegUpper (3609900686637964977859 / 48017126700645734400 : ℝ) ≤ (224087801306727903436735673 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (359839 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_181 : rowCell 1 181 ≤ (85111474877024035074393237 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2427823371624106478947245967 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (224087801306727903436735673 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_181_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_181_1
  · norm_num [gridPoint]

theorem exp_1_182_0 : expNegUpper (10890770377441956635897 / 144863680381937715200 : ℝ) ≤ (1120438716336385467648037733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (359839 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_182_1 : expNegUpper (109024313022746177185761 / 1448636803819377152000 : ℝ) ≤ (413513027117144754590162089 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (900163 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_182 : rowCell 1 182 ≤ (157087751471889676933351181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1120438716336385467648037733 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (413513027117144754590162089 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_182_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_182_1
  · norm_num [gridPoint]

theorem exp_1_183_0 : expNegUpper (109637368875455089924569 / 1456782644925137408000 : ℝ) ≤ (2067564606060144148886359027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (900163 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_183_1 : expNegUpper (13719395765985702883001 / 182097830615642176000 : ℝ) ≤ (1906959625953970521215391279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225183 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_183 : rowCell 1 183 ≤ (36228234732510492740621069 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2067564606060144148886359027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1906959625953970521215391279 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_183_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_183_1
  · norm_num [gridPoint]

theorem exp_1_184_0 : expNegUpper (183951002199303215563 / 2441585540561088000 : ℝ) ≤ (1906959143000198002424607561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (225183 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_184_1 : expNegUpper (1473194532091945782661 / 19532684324488704000 : ℝ) ≤ (175819255540919723920948149 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112663 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_184 : rowCell 1 184 ≤ (13363307737887107035549759 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1906959143000198002424607561 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (175819255540919723920948149 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_184_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_184_1
  · norm_num [gridPoint]

theorem exp_1_185_0 : expNegUpper (111107411099138731327727 / 1473142842053923328000 : ℝ) ≤ (21977401438463023857922059 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112663 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_185_1 : expNegUpper (55613797176057877910763 / 736571421026961664000 : ℝ) ≤ (1620448855307463559899439777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1803757 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_185 : rowCell 1 185 ≤ (123186767529092484297286579 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21977401438463023857922059 / 12500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1620448855307463559899439777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_185_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_185_1
  · norm_num [gridPoint]

theorem exp_1_186_0 : expNegUpper (55923904103232071311707 / 740678599038474496000 : ℝ) ≤ (810224226983616520522552599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1803757 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_186_1 : expNegUpper (4478767578235349446357 / 59254287923077959680 : ℝ) ≤ (186620558092276487893835517 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112807 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_186 : rowCell 1 186 ≤ (22703286723892019475394901 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (810224226983616520522552599 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (186620558092276487893835517 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_186_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_186_1
  · norm_num [gridPoint]

theorem exp_1_187_0 : expNegUpper (115478771932201856363 / 1527789120416133120 : ℝ) ≤ (29859281981122781830971589 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (112807 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_187_1 : expNegUpper (722528110323964881031 / 9548682002600832000 : ℝ) ≤ (137502358644215867626264097 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806073 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_187 : rowCell 1 187 ≤ (209136238734222063105694961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29859281981122781830971589 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (137502358644215867626264097 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_187_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_187_1
  · norm_num [gridPoint]

theorem exp_1_188_0 : expNegUpper (28334851093443845012081 / 374463606260066432000 : ℝ) ≤ (1375023253357574614363278637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1806073 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_188_1 : expNegUpper (113463191608418758396323 / 1497854425040265728000 : ℝ) ≤ (1265956050907034824648481759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_188 : rowCell 1 188 ≤ (192582583621818995527780431 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1375023253357574614363278637 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1265956050907034824648481759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_188_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_188_1
  · norm_num [gridPoint]

theorem exp_1_189_0 : expNegUpper (4563624936737539985427 / 60245491839222272000 : ℝ) ≤ (632977873805588053468469663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1807239 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_189_1 : expNegUpper (2284312372837261875089 / 30122745919611136000 : ℝ) ≤ (1165134788038614504153528719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1808411 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_189 : rowCell 1 189 ≤ (88638653021242927109734541 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (632977873805588053468469663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1165134788038614504153528719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_189_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_189_1
  · norm_num [gridPoint]

theorem exp_1_190_0 : expNegUpper (19140911626704135907507 / 252407167537767168000 : ℝ) ≤ (291283627988740082107734083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1808411 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_190_1 : expNegUpper (38323892101070058081427 / 504814335075534336000 : ℝ) ≤ (1071973405381593431143659123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809589 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_190 : rowCell 1 190 ≤ (163131919233825982208197869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (291283627988740082107734083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1071973405381593431143659123 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_190_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_190_1
  · norm_num [gridPoint]

theorem exp_1_191_0 : expNegUpper (115603953391472974205489 / 1522771552778404352000 : ℝ) ≤ (1071973154147632971635374487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1809589 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_191_1 : expNegUpper (361660545577495770609 / 4758661102432513600 : ℝ) ≤ (492961935746305918121244071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (452693 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_191 : rowCell 1 191 ≤ (150063700001545625047898321 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1071973154147632971635374487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (492961935746305918121244071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_191_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_191_1
  · norm_num [gridPoint]

theorem sum_1_160_2 : blockSum (rowCell 1) 160 2 ≤ (810486283063286825904231711 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_160) (by simpa only [blockSum_one] using cell_1_161) (by norm_num)

theorem sum_1_162_2 : blockSum (rowCell 1) 162 2 ≤ (2805736801044644839144891701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_162) (by simpa only [blockSum_one] using cell_1_163) (by norm_num)

theorem sum_1_160_4 : blockSum (rowCell 1) 160 4 ≤ (1209536386659558428552363709 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_160_2 sum_1_162_2 (by norm_num)

theorem sum_1_164_2 : blockSum (rowCell 1) 164 2 ≤ (606001033047155925693117449 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_164) (by simpa only [blockSum_one] using cell_1_165) (by norm_num)

theorem sum_1_166_2 : blockSum (rowCell 1) 166 2 ≤ (2090635075596050456929235079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_166) (by simpa only [blockSum_one] using cell_1_167) (by norm_num)

theorem sum_1_164_4 : blockSum (rowCell 1) 164 4 ≤ (36117113662277393277613639 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_164_2 sum_1_166_2 (by norm_num)

theorem sum_1_160_8 : blockSum (rowCell 1) 160 8 ≤ (528116057054123315123176171 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_160_4 sum_1_164_4 (by norm_num)

theorem sum_1_168_2 : blockSum (rowCell 1) 168 2 ≤ (360018264738246446801603363 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_168) (by simpa only [blockSum_one] using cell_1_169) (by norm_num)

theorem sum_1_170_2 : blockSum (rowCell 1) 170 2 ≤ (773686390784209942593326443 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_170) (by simpa only [blockSum_one] using cell_1_171) (by norm_num)

theorem sum_1_168_4 : blockSum (rowCell 1) 168 4 ≤ (3347464105259652119194669701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_168_2 sum_1_170_2 (by norm_num)

theorem sum_1_172_2 : blockSum (rowCell 1) 172 2 ≤ (663990502511416850821361507 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_172) (by simpa only [blockSum_one] using cell_1_173) (by norm_num)

theorem sum_1_174_2 : blockSum (rowCell 1) 174 2 ≤ (1137882374844829110723395991 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_174) (by simpa only [blockSum_one] using cell_1_175) (by norm_num)

theorem sum_1_172_4 : blockSum (rowCell 1) 172 4 ≤ (493172675973532562473223801 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_172_2 sum_1_174_2 (by norm_num)

theorem sum_1_168_8 : blockSum (rowCell 1) 168 8 ≤ (2906663742563657465780394353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_168_4 sum_1_172_4 (by norm_num)

theorem sum_1_160_16 : blockSum (rowCell 1) 160 16 ≤ (8187824313104890617012156063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_160_8 sum_1_168_8 (by norm_num)

theorem sum_1_176_2 : blockSum (rowCell 1) 176 2 ≤ (973471636296116624249671099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_176) (by simpa only [blockSum_one] using cell_1_177) (by norm_num)

theorem sum_1_178_2 : blockSum (rowCell 1) 178 2 ≤ (51971019202038681327331259 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_178) (by simpa only [blockSum_one] using cell_1_179) (by norm_num)

theorem sum_1_176_4 : blockSum (rowCell 1) 176 4 ≤ (1805007943528735525486971243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_176_2 sum_1_178_2 (by norm_num)

theorem sum_1_180_2 : blockSum (rowCell 1) 180 2 ≤ (709222347007879975875456373 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_180) (by simpa only [blockSum_one] using cell_1_181) (by norm_num)

theorem sum_1_182_2 : blockSum (rowCell 1) 182 2 ≤ (302000690401931647895835457 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_182) (by simpa only [blockSum_one] using cell_1_183) (by norm_num)

theorem sum_1_180_4 : blockSum (rowCell 1) 180 4 ≤ (1313223727811743271667127287 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_180_2 sum_1_182_2 (by norm_num)

theorem sum_1_176_8 : blockSum (rowCell 1) 176 8 ≤ (311823167134047879715409853 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_176_4 sum_1_180_4 (by norm_num)

theorem sum_1_184_2 : blockSum (rowCell 1) 184 2 ≤ (256819844907963554652784169 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_184) (by simpa only [blockSum_one] using cell_1_185) (by norm_num)

theorem sum_1_186_2 : blockSum (rowCell 1) 186 2 ≤ (436169105973142257859643971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_186) (by simpa only [blockSum_one] using cell_1_187) (by norm_num)

theorem sum_1_184_4 : blockSum (rowCell 1) 184 4 ≤ (949808795789069367165212309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_184_2 sum_1_186_2 (by norm_num)

theorem sum_1_188_2 : blockSum (rowCell 1) 188 2 ≤ (369859889664304849747249513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_188) (by simpa only [blockSum_one] using cell_1_189) (by norm_num)

theorem sum_1_190_2 : blockSum (rowCell 1) 190 2 ≤ (31319561923537160725609619 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_190) (by simpa only [blockSum_one] using cell_1_191) (by norm_num)

theorem sum_1_188_4 : blockSum (rowCell 1) 188 4 ≤ (683055508899676457003345703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_188_2 sum_1_190_2 (by norm_num)

theorem sum_1_184_8 : blockSum (rowCell 1) 184 8 ≤ (408216076172186456042139503 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_184_4 sum_1_188_4 (by norm_num)

theorem sum_1_176_16 : blockSum (rowCell 1) 176 16 ≤ (2375547988014612310661328271 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_176_8 sum_1_184_8 (by norm_num)

theorem sum_1_160_32 : blockSum (rowCell 1) 160 32 ≤ (5281686150559751463836742167 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_160_16 sum_1_176_16 (by norm_num)

#print axioms sum_1_160_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
