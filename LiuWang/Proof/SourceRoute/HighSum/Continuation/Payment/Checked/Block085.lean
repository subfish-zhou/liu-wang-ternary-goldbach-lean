import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_160_0 : expNegUpper (3132377504821255304411 / 39850199714021904000 : ℝ) ≤ (36492480244590155209256143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (923989 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_160_1 : expNegUpper (100307978041359355840751 / 1275206390848700928000 : ℝ) ≤ (3449191144713657154412507 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (231099 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_160 : rowCell 5 160 ≤ (2588122808600061725293813 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36492480244590155209256143 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3449191144713657154412507 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_160_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_160_1
  · norm_num [gridPoint]

theorem exp_5_161_0 : expNegUpper (100909209727171375112039 / 1282849789227848192000 : ℝ) ≤ (68983795427590599968130281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (231099 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_161_1 : expNegUpper (2019644446824088150223 / 25656995784556963840 : ℝ) ≤ (2036476960385393422510783 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924807 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_161 : rowCell 5 161 ≤ (4891207843681457266745089 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68983795427590599968130281 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2036476960385393422510783 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_161_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_161_1
  · norm_num [gridPoint]

theorem exp_5_162_0 : expNegUpper (2031713736234073365823 / 25810320518255011840 : ℝ) ≤ (16291809273267816850207809 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (924807 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_162_1 : expNegUpper (101659817483470095899461 / 1290516025912750592000 : ℝ) ≤ (15382335785030453529472809 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370089 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_162 : rowCell 5 162 ≤ (461941422978162138187721 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16291809273267816850207809 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15382335785030453529472809 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_162_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_162_1
  · norm_num [gridPoint]

theorem exp_5_163_0 : expNegUpper (102265521400215696007549 / 1298205100903408128000 : ℝ) ≤ (7691164902311226349369803 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (370089 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_163_1 : expNegUpper (25585193365123766933687 / 324551275225852032000 : ℝ) ≤ (58064099422607787982196867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1851283 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_163 : rowCell 5 163 ≤ (4360429767260448631977033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7691164902311226349369803 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (58064099422607787982196867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_163_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_163_1
  · norm_num [gridPoint]

theorem exp_5_164_0 : expNegUpper (1029487234850461049903 / 13059170141998208000 : ℝ) ≤ (29032038557216366075494637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1851283 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_164_1 : expNegUpper (4121004010584718789843 / 52236680567992832000 : ℝ) ≤ (54765586209305152970492273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852129 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_164 : rowCell 5 164 ≤ (8227640419967609003814599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29032038557216366075494637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (54765586209305152970492273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_164_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_164_1
  · norm_num [gridPoint]

theorem exp_5_165_0 : expNegUpper (103635303058533541968467 / 1313651765801988608000 : ℝ) ≤ (1711423919244581978163999 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852129 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_165_1 : expNegUpper (51856403944088724331253 / 656825882900994304000 : ℝ) ≤ (1613371680600787694491933 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_165 : rowCell 5 165 ≤ (7758306632376674963340347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1711423919244581978163999 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1613371680600787694491933 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_165_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_165_1
  · norm_num [gridPoint]

theorem exp_5_166_0 : expNegUpper (52162635056508326835557 / 660704677854955776000 : ℝ) ≤ (51627874406888035958360669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1852983 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_166_1 : expNegUpper (20880781264702430242621 / 264281871141982310400 : ℝ) ≤ (3040322687820752076287637 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (463461 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_166 : rowCell 5 166 ≤ (58495999817132426450487 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (51627874406888035958360669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3040322687820752076287637 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_166_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_166_1
  · norm_num [gridPoint]

theorem exp_5_167_0 : expNegUpper (21003726928166817365461 / 265837956784717926400 : ℝ) ≤ (24322572482690602636427423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (463461 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_167_1 : expNegUpper (13137300695370090515867 / 166148722990448704000 : ℝ) ≤ (9162319792364596224110187 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (927357 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_167 : rowCell 5 167 ≤ (6887870630652601369318363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24322572482690602636427423 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9162319792364596224110187 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_167_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_167_1
  · norm_num [gridPoint]

theorem exp_5_168_0 : expNegUpper (13214425829290561020763 / 167124131305377856000 : ℝ) ≤ (45811582170900746858873633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (927357 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_168_1 : expNegUpper (105796315598861814133063 / 1336993050443022848000 : ℝ) ≤ (43121483246292248745897371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1855591 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_168 : rowCell 5 168 ≤ (6485079031022673998831891 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45811582170900746858873633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43121483246292248745897371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_168_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_168_1
  · norm_num [gridPoint]

theorem exp_5_169_0 : expNegUpper (4256623843433060176663 / 53792766210728448000 : ℝ) ≤ (5390183453129754420244371 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1855591 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_169_1 : expNegUpper (2129952928471081359211 / 26896383105364224000 : ℝ) ≤ (10142296265053929571703159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464119 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_169 : rowCell 5 169 ≤ (1525699396157368905934357 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5390183453129754420244371 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10142296265053929571703159 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_169_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_169_1
  · norm_num [gridPoint]

theorem exp_5_170_0 : expNegUpper (53559606493839391153891 / 676334049199577344000 : ℝ) ≤ (324553364270954599719441 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464119 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_170_1 : expNegUpper (107202408029376132338461 / 1352668098399154688000 : ℝ) ≤ (38149171107247349816214403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (232171 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_170 : rowCell 5 170 ≤ (2870106097990148057901779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (324553364270954599719441 / 8000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (38149171107247349816214403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_170_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_170_1
  · norm_num [gridPoint]

theorem exp_5_171_0 : expNegUpper (107826267332219968568789 / 1360539879835853312000 : ℝ) ≤ (1192161175164245995228403 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (232171 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_171_1 : expNegUpper (5395530520433332699793 / 68026993991792665600 : ℝ) ≤ (17928007179589035533801053 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464567 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_171 : rowCell 5 171 ≤ (2698261814334104956737949 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1192161175164245995228403 / 31250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17928007179589035533801053 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_171_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_171_1
  · norm_num [gridPoint]

theorem exp_5_172_0 : expNegUpper (5426838455589435496433 / 68421724978915353600 : ℝ) ≤ (35856001815006933597953013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464567 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_172_1 : expNegUpper (108622263553764279661811 / 1368434499578307072000 : ℝ) ≤ (33684401746112837874907951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74367 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_172 : rowCell 5 172 ≤ (1014189741076635635869141 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35856001815006933597953013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33684401746112837874907951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_172_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_172_1
  · norm_num [gridPoint]

theorem exp_5_173_0 : expNegUpper (109250728318723653116459 / 1376351957626515968000 : ℝ) ≤ (33684390097061267122107087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (74367 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_173_1 : expNegUpper (54668688728503828032689 / 688175978813257984000 : ℝ) ≤ (15814570413252988364480751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (186009 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_173 : rowCell 5 173 ≤ (4762721355071962564065569 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33684390097061267122107087 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15814570413252988364480751 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_173_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_173_1
  · norm_num [gridPoint]

theorem exp_5_174_0 : expNegUpper (2837887869557766319 / 35723671070464000 : ℝ) ≤ (15814565006763593095099649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (186009 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_174_1 : expNegUpper (5680307721844409287 / 71447342140928000 : ℝ) ≤ (29685165493194187331951883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (465253 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_174 : rowCell 5 174 ≤ (558886689426561484652411 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15814565006763593095099649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29685165493194187331951883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_174_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_174_1
  · norm_num [gridPoint]

theorem exp_5_175_0 : expNegUpper (110689058984046731892097 / 1392255388640199168000 : ℝ) ≤ (29685155460720509689998631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (465253 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_175_1 : expNegUpper (6923626719205390500101 / 87015961790012448000 : ℝ) ≤ (13923770385757577698427697 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1861941 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_175 : rowCell 5 175 ≤ (4195335898786395847363747 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (29685155460720509689998631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13923770385757577698427697 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_175_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_175_1
  · norm_num [gridPoint]

theorem exp_5_176_0 : expNegUpper (6963340651694510058629 / 87515085100354592000 : ℝ) ≤ (1392376573364415370843091 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1861941 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_176_1 : expNegUpper (22300716727799751398483 / 280048272321134694400 : ℝ) ≤ (26111466765231211569944521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1862877 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_176 : rowCell 5 176 ≤ (3934738629902797853773259 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1392376573364415370843091 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26111466765231211569944521 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_176_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_176_1
  · norm_num [gridPoint]

theorem exp_5_177_0 : expNegUpper (22428267853379675745643 / 281650034575380582400 : ℝ) ≤ (3263932267517229897707883 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1862877 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_177_1 : expNegUpper (56116320249105801818543 / 704125086438451456000 : ℝ) ≤ (24472281805324433224388203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1863821 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_177 : rowCell 5 177 ≤ (461076470393995769388703 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3263932267517229897707883 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24472281805324433224388203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_177_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_177_1
  · norm_num [gridPoint]

theorem exp_5_178_0 : expNegUpper (56436367747872015995807 / 708140911226943744000 : ℝ) ≤ (23898704895739303802687 / 976562500000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1863821 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_178_1 : expNegUpper (112965208077263434664693 / 1416281822453887488000 : ℝ) ≤ (4585092971164677868641411 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466193 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_178 : rowCell 5 178 ≤ (3456285687653722508983463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23898704895739303802687 / 976562500000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4585092971164677868641411 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_178_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_178_1
  · norm_num [gridPoint]

theorem exp_5_179_0 : expNegUpper (4544305964239510698293 / 56973452413465088000 : ℝ) ≤ (89552568177526435315629 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466193 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_179_1 : expNegUpper (1137012963684928968043 / 14243363103366272000 : ℝ) ≤ (335416206713944131994863 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (186573 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_179 : rowCell 5 179 ≤ (323711142781707675537511 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (89552568177526435315629 / 3906250000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (335416206713944131994863 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_179_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_179_1
  · norm_num [gridPoint]

theorem exp_5_180_0 : expNegUpper (28586522522492057963603 / 358103409131280512000 : ℝ) ≤ (5366657594103881822271281 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (186573 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_180_1 : expNegUpper (114440915364238636784971 / 1432413636525122048000 : ℝ) ≤ (10045781833245299423658427 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (373339 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_180 : rowCell 5 180 ≤ (3030460847048675141339133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5366657594103881822271281 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10045781833245299423658427 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_180_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_180_1
  · norm_num [gridPoint]

theorem exp_5_181_0 : expNegUpper (115088068440024071911939 / 1440513801019372032000 : ℝ) ≤ (2009155732424401509914133 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (233337 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_181_1 : expNegUpper (11518407505683930133577 / 144051380101937203200 : ℝ) ≤ (18796152822016290324865593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466917 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_181 : rowCell 5 181 ≤ (141786338102119300113087 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2009155732424401509914133 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18796152822016290324865593 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_181_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_181_1
  · norm_num [gridPoint]

theorem exp_5_182_0 : expNegUpper (11583359414849393435897 / 144863680381937715200 : ℝ) ≤ (18796146955135205181268119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466917 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_182_1 : expNegUpper (115930785438633537185761 / 1448636803819377152000 : ℝ) ≤ (17576457218520610068216443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1868647 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_182 : rowCell 5 182 ≤ (82885092964204509902779 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18796146955135205181268119 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17576457218520610068216443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_182_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_182_1
  · norm_num [gridPoint]

theorem exp_5_183_0 : expNegUpper (116582677207716465924569 / 1456782644925137408000 : ℝ) ≤ (8788225896806633047475297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1868647 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_183_1 : expNegUpper (14585132062744998883001 / 182097830615642176000 : ℝ) ≤ (16428672702322202773327329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1869633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_183 : rowCell 5 183 ≤ (1239842114861326853448819 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8788225896806633047475297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16428672702322202773327329 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_183_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_183_1
  · norm_num [gridPoint]

theorem exp_5_184_0 : expNegUpper (586676638050151566689 / 7324756621683264000 : ℝ) ≤ (65714670752575210533673 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1869633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_184_1 : expNegUpper (4697395929566292387983 / 58598052973466112000 : ℝ) ≤ (3837284363452523534021967 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (935313 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_184 : rowCell 5 184 ≤ (463453220264617075327303 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (65714670752575210533673 / 4000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3837284363452523534021967 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_184_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_184_1
  · norm_num [gridPoint]

theorem exp_5_185_0 : expNegUpper (118091555347774123327727 / 1473142842053923328000 : ℝ) ≤ (7674566410571038311213827 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (935313 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_185_1 : expNegUpper (59096160321282069910763 / 736571421026961664000 : ℝ) ≤ (14334330592900818893663493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (935813 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_185 : rowCell 5 185 ≤ (2164544820888668995197307 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7674566410571038311213827 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14334330592900818893663493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_185_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_185_1
  · norm_num [gridPoint]

theorem exp_5_186_0 : expNegUpper (59425685206643271311707 / 740678599038474496000 : ℝ) ≤ (2866865262887084771599637 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (935813 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_186_1 : expNegUpper (4758133348180765126357 / 59254287923077959680 : ℝ) ≤ (13380870421040313567181203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1872633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_186 : rowCell 5 186 ≤ (505254261580739450506731 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2866865262887084771599637 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13380870421040313567181203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_186_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_186_1
  · norm_num [gridPoint]

theorem exp_5_187_0 : expNegUpper (4784591311956248718157 / 59583775696229191680 : ℝ) ≤ (3345216617817584378886457 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1872633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_187_1 : expNegUpper (29929486854340230360209 / 372398598101432448000 : ℝ) ≤ (12485512338827620799614581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (936823 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_187 : rowCell 5 187 ≤ (1886199582157055317725921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3345216617817584378886457 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12485512338827620799614581 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_187_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_187_1
  · norm_num [gridPoint]

theorem exp_5_188_0 : expNegUpper (30095450624242949012081 / 374463606260066432000 : ℝ) ≤ (6242754346970626493132881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (936823 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_188_1 : expNegUpper (120486171773428166396323 / 1497854425040265728000 : ℝ) ≤ (11645146476302416602915631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (937333 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_188 : rowCell 5 188 ≤ (439907263724918225560001 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6242754346970626493132881 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11645146476302416602915631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_188_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_188_1
  · norm_num [gridPoint]

theorem exp_5_189_0 : expNegUpper (4846097579992876945427 / 60245491839222272000 : ℝ) ≤ (11645143114083035266226369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1874667 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_189_1 : expNegUpper (2425160335301190195089 / 30122745919611136000 : ℝ) ≤ (2714198767724082270212363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1875693 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_189 : rowCell 5 189 ≤ (65634461961351332623457 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11645143114083035266226369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2714198767724082270212363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_189_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_189_1
  · norm_num [gridPoint]

theorem exp_5_190_0 : expNegUpper (60963351899897623722521 / 757221502613301504000 : ℝ) ≤ (2171358394125425779394383 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1875693 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_190_1 : expNegUpper (122033492384593598244281 / 1514443005226603008000 : ℝ) ≤ (2023521925202421867043243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1876727 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_190 : rowCell 5 190 ≤ (764736104307933866228379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2171358394125425779394383 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2023521925202421867043243 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_190_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_190_1
  · norm_num [gridPoint]

theorem exp_5_191_0 : expNegUpper (122704605389230414205489 / 1522771552778404352000 : ℝ) ≤ (5058803384192712047041921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1876727 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_191_1 : expNegUpper (383789401951153370609 / 4758661102432513600 : ℝ) ≤ (9424867881176691294980221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1877767 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_191 : rowCell 5 191 ≤ (1425054809138137420133597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5058803384192712047041921 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9424867881176691294980221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_191_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_191_1
  · norm_num [gridPoint]

theorem sum_5_160_2 : blockSum (rowCell 5) 160 2 ≤ (2013490692176316143466543 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_160) (by simpa only [blockSum_one] using cell_5_161) (by norm_num)

theorem sum_5_162_2 : blockSum (rowCell 5) 162 2 ≤ (8979843997042070013854243 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_162) (by simpa only [blockSum_one] using cell_5_163) (by norm_num)

theorem sum_5_160_4 : blockSum (rowCell 5) 160 4 ≤ (9523648728961825365593479 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_160_2 sum_5_162_2 (by norm_num)

theorem sum_5_164_2 : blockSum (rowCell 5) 164 2 ≤ (7992973526172141983577473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_164) (by simpa only [blockSum_one] using cell_5_165) (by norm_num)

theorem sum_5_166_2 : blockSum (rowCell 5) 166 2 ≤ (7099935303897077337814619 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_166) (by simpa only [blockSum_one] using cell_5_167) (by norm_num)

theorem sum_5_164_4 : blockSum (rowCell 5) 164 4 ≤ (3773227207517304830348023 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_164_2 sum_5_166_2 (by norm_num)

theorem sum_5_160_8 : blockSum (rowCell 5) 160 8 ≤ (682804125759857401051581 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_160_4 sum_5_164_4 (by norm_num)

theorem sum_5_168_2 : blockSum (rowCell 5) 168 2 ≤ (12587876615652149622569319 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_168) (by simpa only [blockSum_one] using cell_5_169) (by norm_num)

theorem sum_5_170_2 : blockSum (rowCell 5) 170 2 ≤ (348022994520265813414983 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_170) (by simpa only [blockSum_one] using cell_5_171) (by norm_num)

theorem sum_5_168_4 : blockSum (rowCell 5) 168 4 ≤ (948984497612026226073951 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_168_2 sum_5_170_2 (by norm_num)

theorem sum_5_172_2 : blockSum (rowCell 5) 172 2 ≤ (4916835030227570371705637 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_172) (by simpa only [blockSum_one] using cell_5_173) (by norm_num)

theorem sum_5_174_2 : blockSum (rowCell 5) 174 2 ≤ (1733285882839777544916607 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_174) (by simpa only [blockSum_one] using cell_5_175) (by norm_num)

theorem sum_5_172_4 : blockSum (rowCell 5) 172 4 ≤ (18500099474654028467994309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_172_2 sum_5_174_2 (by norm_num)

theorem sum_5_168_8 : blockSum (rowCell 5) 168 8 ≤ (10556177978738671029960771 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_168_4 sum_5_172_4 (by norm_num)

theorem sum_5_160_16 : blockSum (rowCell 5) 160 16 ≤ (3453285140341888257031287 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_160_8 sum_5_168_8 (by norm_num)

theorem sum_5_176_2 : blockSum (rowCell 5) 176 2 ≤ (7623350393054764008882883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_176) (by simpa only [blockSum_one] using cell_5_177) (by norm_num)

theorem sum_5_178_2 : blockSum (rowCell 5) 178 2 ≤ (6693397115470799264358573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_178) (by simpa only [blockSum_one] using cell_5_179) (by norm_num)

theorem sum_5_176_4 : blockSum (rowCell 5) 176 4 ≤ (894796719282847704577591 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_176_2 sum_5_178_2 (by norm_num)

theorem sum_5_180_2 : blockSum (rowCell 5) 180 2 ≤ (5866187609091061143600873 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_180) (by simpa only [blockSum_one] using cell_5_181) (by norm_num)

theorem sum_5_182_2 : blockSum (rowCell 5) 182 2 ≤ (2566003602288599011893283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_182) (by simpa only [blockSum_one] using cell_5_183) (by norm_num)

theorem sum_5_180_4 : blockSum (rowCell 5) 180 4 ≤ (10998194813668259167387439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_180_2 sum_5_182_2 (by norm_num)

theorem sum_5_176_8 : blockSum (rowCell 5) 176 8 ≤ (5062988464438764488125779 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_176_4 sum_5_180_4 (by norm_num)

theorem sum_5_184_2 : blockSum (rowCell 5) 184 2 ≤ (2240905461105877185916911 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_184) (by simpa only [blockSum_one] using cell_5_185) (by norm_num)

theorem sum_5_186_2 : blockSum (rowCell 5) 186 2 ≤ (781443325696002623950569 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_186) (by simpa only [blockSum_one] using cell_5_187) (by norm_num)

theorem sum_5_184_4 : blockSum (rowCell 5) 184 4 ≤ (8389027550691767491586667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_184_2 sum_5_186_2 (by norm_num)

theorem sum_5_188_2 : blockSum (rowCell 5) 188 2 ≤ (3400490603933456217826429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_188) (by simpa only [blockSum_one] using cell_5_189) (by norm_num)

theorem sum_5_190_2 : blockSum (rowCell 5) 190 2 ≤ (590905403550801030518071 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_190) (by simpa only [blockSum_one] using cell_5_191) (by norm_num)

theorem sum_5_188_4 : blockSum (rowCell 5) 188 4 ≤ (397188601355466335651049 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_188_2 sum_5_190_2 (by norm_num)

theorem sum_5_184_8 : blockSum (rowCell 5) 184 8 ≤ (14744045172379228862003451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_184_4 sum_5_188_4 (by norm_num)

theorem sum_5_176_16 : blockSum (rowCell 5) 176 16 ≤ (20029493747286525651316173 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_176_8 sum_5_184_8 (by norm_num)

theorem sum_5_160_32 : blockSum (rowCell 5) 160 32 ≤ (15056411198551347552763353 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_160_16 sum_5_176_16 (by norm_num)

#print axioms sum_5_160_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
