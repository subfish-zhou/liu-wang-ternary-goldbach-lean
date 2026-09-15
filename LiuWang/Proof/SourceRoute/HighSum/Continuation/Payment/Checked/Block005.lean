import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_160_0 : expNegUpper (317015187934322589379 / 4427799968224656000 : ℝ) ≤ (80621124361694844007910684461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1749531 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_160_1 : expNegUpper (10155441300519025315639 / 141689598983188992000 : ℝ) ≤ (9327809839315562999823472537 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (437647 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_160 : rowCell 0 160 ≤ (11320503012992553647454342639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (80621124361694844007910684461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9327809839315562999823472537 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_160_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_160_1
  · norm_num [gridPoint]

theorem exp_0_161_0 : expNegUpper (91946804005468975112039 / 1282849789227848192000 : ℝ) ≤ (74622455956566914671263592839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (437647 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_161_1 : expNegUpper (1840930326240182870223 / 25656995784556963840 : ℝ) ≤ (34520975047752628489404749373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1751651 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_161 : rowCell 0 161 ≤ (10476137562806915165315046701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (74622455956566914671263592839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34520975047752628489404749373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_161_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_161_1
  · norm_num [gridPoint]

theorem exp_0_162_0 : expNegUpper (1851931627949882645823 / 25810320518255011840 : ℝ) ≤ (34520964644629321644253330563 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1751651 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_162_1 : expNegUpper (92697411761767695899461 / 1290516025912750592000 : ℝ) ≤ (31926455482340197154015631081 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1752721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_162 : rowCell 0 162 ≤ (4845405574512637634946818003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (34520964644629321644253330563 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31926455482340197154015631081 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_162_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_162_1
  · norm_num [gridPoint]

theorem exp_0_163_0 : expNegUpper (10361079588166558223061 / 144245011211489792000 : ℝ) ≤ (12770578389957443897253075539 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1752721 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_163_1 : expNegUpper (2593101890174598103743 / 36061252802872448000 : ℝ) ≤ (59030190678801924648973853487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1753797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_163 : rowCell 0 163 ≤ (4480372394023134756700414371 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12770578389957443897253075539 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (59030190678801924648973853487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_163_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_163_1
  · norm_num [gridPoint]

theorem exp_0_164_0 : expNegUpper (939062186858222969903 / 13059170141998208000 : ℝ) ≤ (11806034661477367961341608539 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1753797 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_164_1 : expNegUpper (3760371806316051909843 / 52236680567992832000 : ℝ) ≤ (13637509195997485094888313819 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1754879 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_164 : rowCell 0 164 ≤ (8282370964583198782508122443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11806034661477367961341608539 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13637509195997485094888313819 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_164_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_164_1
  · norm_num [gridPoint]

theorem exp_0_165_0 : expNegUpper (94566098566802597968467 / 1313651765801988608000 : ℝ) ≤ (54550020919755562826444811457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1754879 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_165_1 : expNegUpper (47335151544476820331253 / 656825882900994304000 : ℝ) ≤ (10078010494949846958207003647 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (877983 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_165 : rowCell 0 165 ≤ (1913081108506120054417684659 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (54550020919755562826444811457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10078010494949846958207003647 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_165_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_165_1
  · norm_num [gridPoint]

theorem exp_0_166_0 : expNegUpper (5290520329376587426173 / 73411630872772864000 : ℝ) ≤ (201560151968523845676275669 / 4000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (877983 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_166_1 : expNegUpper (2118548929595137938069 / 29364652349109145600 : ℝ) ≤ (5816141907673947491283907119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (87853 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_166 : rowCell 0 166 ≤ (7067433189466583676852129051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (201560151968523845676275669 / 4000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5816141907673947491283907119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_166_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_166_1
  · norm_num [gridPoint]

theorem exp_0_167_0 : expNegUpper (19179206152817774165461 / 265837956784717926400 : ℝ) ≤ (23264561022384099671039276693 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (87853 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_167_1 : expNegUpper (12000312672340330515867 / 166148722990448704000 : ℝ) ≤ (21473708491158502159040295063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (21977 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_167 : rowCell 0 167 ≤ (652470961493308519776146817 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23264561022384099671039276693 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21473708491158502159040295063 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_167_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_167_1
  · norm_num [gridPoint]

theorem exp_0_168_0 : expNegUpper (12070762883134017020763 / 167124131305377856000 : ℝ) ≤ (21473702462636994312305915181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (21977 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_168_1 : expNegUpper (96673711722116598133063 / 1336993050443022848000 : ℝ) ≤ (39626205277077725185893649229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879633 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_168 : rowCell 0 168 ≤ (3010670921591701573214968099 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (21473702462636994312305915181 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (39626205277077725185893649229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_168_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_168_1
  · norm_num [gridPoint]

theorem exp_0_169_0 : expNegUpper (432175968106964517407 / 5976974023414272000 : ℝ) ≤ (19813097140860100895790396939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (879633 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_169_1 : expNegUpper (216329650787337146579 / 2988487011707136000 : ℝ) ≤ (7309585323432475336251109127 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (880189 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_169 : rowCell 0 169 ≤ (5554685333633262712055822567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19813097140860100895790396939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7309585323432475336251109127 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_169_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_169_1
  · norm_num [gridPoint]

theorem exp_0_170_0 : expNegUpper (48958255016706079153891 / 676334049199577344000 : ℝ) ≤ (1827395829673745049537022227 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (880189 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_170_1 : expNegUpper (98026404767616644338461 / 1352668098399154688000 : ℝ) ≤ (1684803548697182494031540393 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (220187 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_170 : rowCell 0 170 ≤ (5122254683248740832144690223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1827395829673745049537022227 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1684803548697182494031540393 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_170_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_170_1
  · norm_num [gridPoint]

theorem exp_0_171_0 : expNegUpper (98596864685446208568789 / 1360539879835853312000 : ℝ) ≤ (33696061839194020877401514079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (220187 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_171_1 : expNegUpper (4935395372720001499793 / 68026993991792665600 : ℝ) ≤ (6211027637434580386060628987 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762619 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_171 : rowCell 0 171 ≤ (4721715680828949700170033783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33696061839194020877401514079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6211027637434580386060628987 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_171_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_171_1
  · norm_num [gridPoint]

theorem exp_0_172_0 : expNegUpper (551559259847265632937 / 7602413886546150400 : ℝ) ≤ (31055129865357383269189504623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1762619 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_172_1 : expNegUpper (11043651211887835517979 / 152048277730923008000 : ℝ) ≤ (28610586082720783130986496927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (440937 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_172 : rowCell 0 172 ≤ (543859701606316499422307399 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31055129865357383269189504623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (28610586082720783130986496927 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_172_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_172_1
  · norm_num [gridPoint]

theorem exp_0_173_0 : expNegUpper (99967926286935621116459 / 1376351957626515968000 : ℝ) ≤ (3576322313006026514820975089 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (440937 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_173_1 : expNegUpper (50040637558863380032689 / 688175978813257984000 : ℝ) ≤ (26348780374891012246972153361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441221 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_173 : rowCell 0 173 ≤ (2003842913500620518847282183 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3576322313006026514820975089 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (26348780374891012246972153361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_173_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_173_1
  · norm_num [gridPoint]

theorem exp_0_174_0 : expNegUpper (2597642663769503919 / 35723671070464000 : ℝ) ≤ (13174386737651698652472805681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (441221 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_174_1 : expNegUpper (5201195358913414087 / 71447342140928000 : ℝ) ≤ (24256946376510869187123343591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (70641 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_174 : rowCell 0 174 ≤ (230638409854420354811357479 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13174386737651698652472805681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (24256946376510869187123343591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_174_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_174_1
  · norm_num [gridPoint]

theorem exp_0_175_0 : expNegUpper (11261428618582714210233 / 154695043182244352000 : ℝ) ≤ (24256940097238192628624733583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (70641 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_175_1 : expNegUpper (704642540159660277789 / 9668440198890272000 : ℝ) ≤ (4464624505812291243025668219 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1767171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_175 : rowCell 0 175 ≤ (679332003196957241955446453 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24256940097238192628624733583 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4464624505812291243025668219 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_175_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_175_1
  · norm_num [gridPoint]

theorem exp_0_176_0 : expNegUpper (6378159332362670058629 / 87515085100354592000 : ℝ) ≤ (22323116816208513008244186621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1767171 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_176_1 : expNegUpper (20433476444439290598483 / 280048272321134694400 : ℝ) ≤ (10268057877643761600461652849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (442081 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_176 : rowCell 0 176 ≤ (1562666872727627206921262607 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22323116816208513008244186621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10268057877643761600461652849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_176_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_176_1
  · norm_num [gridPoint]

theorem exp_0_177_0 : expNegUpper (20550347693016360545643 / 281650034575380582400 : ℝ) ≤ (20536110559450737506797143943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (442081 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_177_1 : expNegUpper (51434869694451081818543 / 704125086438451456000 : ℝ) ≤ (4721364656988738839207286351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1769481 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_177 : rowCell 0 177 ≤ (179666015185105620838613199 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20536110559450737506797143943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4721364656988738839207286351 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_177_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_177_1
  · norm_num [gridPoint]

theorem exp_0_178_0 : expNegUpper (5747579722301128888423 / 78682323469660416000 : ℝ) ≤ (188854539038672247299457041 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1769481 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_178_1 : expNegUpper (11508400808382984296077 / 157364646939320832000 : ℝ) ≤ (3472273668127746587492602971 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (354129 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_178 : rowCell 0 178 ≤ (2643150843573734731428785599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (188854539038672247299457041 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3472273668127746587492602971 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_178_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_178_1
  · norm_num [gridPoint]

theorem exp_0_179_0 : expNegUpper (4166585956766276778293 / 56973452413465088000 : ℝ) ≤ (2170170505855056866754657589 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (354129 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_179_1 : expNegUpper (1042849958741691848043 / 14243363103366272000 : ℝ) ≤ (7977353729780553818560960317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (885907 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_179 : rowCell 0 179 ≤ (242943786665479597534280003 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2170170505855056866754657589 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7977353729780553818560960317 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_179_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_179_1
  · norm_num [gridPoint]

theorem exp_0_180_0 : expNegUpper (26219097552657561963603 / 358103409131280512000 : ℝ) ≤ (3988675889523911253266849909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (885907 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_180_1 : expNegUpper (104997915177407788784971 / 1432413636525122048000 : ℝ) ≤ (1465694642949603729342326143 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1772989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_180 : rowCell 0 180 ≤ (2232229019749471200691371243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3988675889523911253266849909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1465694642949603729342326143 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_180_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_180_1
  · norm_num [gridPoint]

theorem exp_0_181_0 : expNegUpper (11732407652019883545771 / 160057089002152448000 : ℝ) ≤ (14656942885627975848235043547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1772989 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_181_1 : expNegUpper (1174604168638903525953 / 16005708900215244800 : ℝ) ≤ (13460127801550338139803488469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1774169 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_181 : rowCell 0 181 ≤ (2050322055939738167774243383 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14656942885627975848235043547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13460127801550338139803488469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_181_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_181_1
  · norm_num [gridPoint]

theorem exp_0_182_0 : expNegUpper (10631049488414167835897 / 144863680381937715200 : ℝ) ≤ (6730062291752492738758774777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1774169 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_182_1 : expNegUpper (106434385866788417185761 / 1448636803819377152000 : ℝ) ≤ (2471366429233036722006979739 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (355071 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_182 : rowCell 0 182 ≤ (15060765437196884343254913 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6730062291752492738758774777 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2471366429233036722006979739 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_182_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_182_1
  · norm_num [gridPoint]

theorem exp_0_183_0 : expNegUpper (107032878250857073924569 / 1456782644925137408000 : ℝ) ≤ (12356829224887847578193305037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (355071 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_183_1 : expNegUpper (13394744654700966883001 / 182097830615642176000 : ℝ) ≤ (2835036402724052227599634713 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (888273 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_183 : rowCell 0 183 ≤ (864002347638101211943184363 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12356829224887847578193305037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2835036402724052227599634713 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_183_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_183_1
  · norm_num [gridPoint]

theorem exp_0_184_0 : expNegUpper (59866016089257658521 / 813861846853696000 : ℝ) ≤ (5670071479914940604017081277 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (888273 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_184_1 : expNegUpper (479489330143546300887 / 6510894774829568000 : ℝ) ≤ (10403629079371519551933474881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1777743 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_184 : rowCell 0 184 ≤ (792787696259378806712667703 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5670071479914940604017081277 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10403629079371519551933474881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_184_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_184_1
  · norm_num [gridPoint]

theorem exp_0_185_0 : expNegUpper (108488357005900459327727 / 1473142842053923328000 : ℝ) ≤ (1040362667425167296013148793 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1777743 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_185_1 : expNegUpper (54307910996598805910763 / 736571421026961664000 : ℝ) ≤ (298165277663801979008755803 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (355789 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_185 : rowCell 0 185 ≤ (1454401161858327064445300861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1040362667425167296013148793 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (298165277663801979008755803 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_185_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_185_1
  · norm_num [gridPoint]

theorem exp_0_186_0 : expNegUpper (54610736189452871311707 / 740678599038474496000 : ℝ) ≤ (4770643351953475113715170131 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (355789 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_186_1 : expNegUpper (4374005414505818566357 / 59254287923077959680 : ℝ) ≤ (1093443629109234856665325453 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1780153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_186 : rowCell 0 186 ≤ (333409583325478830148657977 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4770643351953475113715170131 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1093443629109234856665325453 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_186_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_186_1
  · norm_num [gridPoint]

theorem exp_0_187_0 : expNegUpper (488703044764525697573 / 6620419521803243520 : ℝ) ≤ (4373773527545797092812905999 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1780153 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_187_1 : expNegUpper (3058001371749447817801 / 41377622011270272000 : ℝ) ≤ (8017224874956966998088136567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (890683 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_187 : rowCell 0 187 ≤ (1222502231238921984520609623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4373773527545797092812905999 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8017224874956966998088136567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_187_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_187_1
  · norm_num [gridPoint]

theorem exp_0_188_0 : expNegUpper (27674626269394181012081 / 374463606260066432000 : ℝ) ≤ (501076442641388166599909353 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (890683 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_188_1 : expNegUpper (110829574046540230396323 / 1497854425040265728000 : ℝ) ≤ (183637454900694564798904383 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (222823 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_188 : rowCell 0 188 ≤ (1120263438057804772006707879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (501076442641388166599909353 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (183637454900694564798904383 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_188_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_188_1
  · norm_num [gridPoint]

theorem exp_0_189_0 : expNegUpper (4457697695516788625427 / 60245491839222272000 : ℝ) ≤ (293819862863012980708493391 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (222823 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_189_1 : expNegUpper (2231494386913288755089 / 30122745919611136000 : ℝ) ≤ (1681973412540752883623589239 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1783807 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_189 : rowCell 0 189 ≤ (513122129515343403981604433 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (293819862863012980708493391 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1681973412540752883623589239 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_189_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_189_1
  · norm_num [gridPoint]

theorem exp_0_190_0 : expNegUpper (6232778166410327969169 / 84135722512589056000 : ℝ) ≤ (6727892178590927337964847639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1783807 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_190_1 : expNegUpper (12480388363632376693809 / 168271445025178112000 : ℝ) ≤ (1540064125165132900712977853 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (446259 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_190 : rowCell 0 190 ≤ (939815380887095400947000211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6727892178590927337964847639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1540064125165132900712977853 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_190_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_190_1
  · norm_num [gridPoint]

theorem exp_0_191_0 : expNegUpper (112941208892313934205489 / 1522771552778404352000 : ℝ) ≤ (3080127583982369071130866033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (446259 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_191_1 : expNegUpper (353362224437374170609 / 4758661102432513600 : ℝ) ≤ (1409682902356430684603476037 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (178627 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_191 : rowCell 0 191 ≤ (6883141731675961753288519 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3080127583982369071130866033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1409682902356430684603476037 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_191_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_191_1
  · norm_num [gridPoint]

theorem sum_0_160_2 : blockSum (rowCell 0) 160 2 ≤ (1089832028789973440638469467 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_160) (by simpa only [blockSum_one] using cell_0_161) (by norm_num)

theorem sum_0_162_2 : blockSum (rowCell 0) 162 2 ≤ (4662888984267886195823616187 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_162) (by simpa only [blockSum_one] using cell_0_163) (by norm_num)

theorem sum_0_160_4 : blockSum (rowCell 0) 160 4 ≤ (5056024564108876699507981761 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_160_2 sum_0_162_2 (by norm_num)

theorem sum_0_164_2 : blockSum (rowCell 0) 164 2 ≤ (15934695398607679000178861079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_164) (by simpa only [blockSum_one] using cell_0_165) (by norm_num)

theorem sum_0_166_2 : blockSum (rowCell 0) 166 2 ≤ (13592142804399668874613597221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_166) (by simpa only [blockSum_one] using cell_0_167) (by norm_num)

theorem sum_0_164_4 : blockSum (rowCell 0) 164 4 ≤ (295268382030073478747924583 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_164_2 sum_0_166_2 (by norm_num)

theorem sum_0_160_8 : blockSum (rowCell 0) 160 8 ≤ (17493758678969590367714078097 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_160_4 sum_0_164_4 (by norm_num)

theorem sum_0_168_2 : blockSum (rowCell 0) 168 2 ≤ (2315205435363333171697151753 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_168) (by simpa only [blockSum_one] using cell_0_169) (by norm_num)

theorem sum_0_170_2 : blockSum (rowCell 0) 170 2 ≤ (4921985182038845266157362003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_170) (by simpa only [blockSum_one] using cell_0_171) (by norm_num)

theorem sum_0_168_4 : blockSum (rowCell 0) 168 4 ≤ (21419997540894356390800482771 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_168_2 sum_0_170_2 (by norm_num)

theorem sum_0_172_2 : blockSum (rowCell 0) 172 2 ≤ (4179281719925886516536511779 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_172) (by simpa only [blockSum_one] using cell_0_173) (by norm_num)

theorem sum_0_174_2 : blockSum (rowCell 0) 174 2 ≤ (7086874573655511886758951929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_174) (by simpa only [blockSum_one] using cell_0_175) (by norm_num)

theorem sum_0_172_4 : blockSum (rowCell 0) 172 4 ≤ (15445438013507284919831975487 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_172_2 sum_0_174_2 (by norm_num)

theorem sum_0_168_8 : blockSum (rowCell 0) 168 8 ≤ (18432717777200820655316229129 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_168_4 sum_0_172_4 (by norm_num)

theorem sum_0_160_16 : blockSum (rowCell 0) 160 16 ≤ (53420235135140001390744385323 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_160_8 sum_0_168_8 (by norm_num)

theorem sum_0_176_2 : blockSum (rowCell 0) 176 2 ≤ (2999994994208472173630168199 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_176) (by simpa only [blockSum_one] using cell_0_177) (by norm_num)

theorem sum_0_178_2 : blockSum (rowCell 0) 178 2 ≤ (5072588710228530706771585629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_178) (by simpa only [blockSum_one] using cell_0_179) (by norm_num)

theorem sum_0_176_4 : blockSum (rowCell 0) 176 4 ≤ (11072578698645475054031922027 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_176_2 sum_0_178_2 (by norm_num)

theorem sum_0_180_2 : blockSum (rowCell 0) 180 2 ≤ (2141275537844604684232807313 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_180) (by simpa only [blockSum_one] using cell_0_181) (by norm_num)

theorem sum_0_182_2 : blockSum (rowCell 0) 182 2 ≤ (3610600374925812966793232851 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_182) (by simpa only [blockSum_one] using cell_0_183) (by norm_num)

theorem sum_0_180_4 : blockSum (rowCell 0) 180 4 ≤ (7893151450615022335258847477 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_180_2 sum_0_182_2 (by norm_num)

theorem sum_0_176_8 : blockSum (rowCell 0) 176 8 ≤ (592679067164390543415336547 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_176_4 sum_0_180_4 (by norm_num)

theorem sum_0_184_2 : blockSum (rowCell 0) 184 2 ≤ (3039976554377084677870636267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_184) (by simpa only [blockSum_one] using cell_0_185) (by norm_num)

theorem sum_0_186_2 : blockSum (rowCell 0) 186 2 ≤ (2556140564540837305115241531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_186) (by simpa only [blockSum_one] using cell_0_187) (by norm_num)

theorem sum_0_184_4 : blockSum (rowCell 0) 184 4 ≤ (2798058559458960991492938899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_184_2 sum_0_186_2 (by norm_num)

theorem sum_0_188_2 : blockSum (rowCell 0) 188 2 ≤ (429301539417698315993983349 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_188) (by simpa only [blockSum_one] using cell_0_189) (by norm_num)

theorem sum_0_190_2 : blockSum (rowCell 0) 190 2 ≤ (900104048673295310054032543 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_190) (by simpa only [blockSum_one] using cell_0_191) (by norm_num)

theorem sum_0_188_4 : blockSum (rowCell 0) 188 4 ≤ (3946715794435082200077981831 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_188_2 sum_0_190_2 (by norm_num)

theorem sum_0_184_8 : blockSum (rowCell 0) 184 8 ≤ (9542832913353004183063859629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_184_4 sum_0_188_4 (by norm_num)

theorem sum_0_176_16 : blockSum (rowCell 0) 176 16 ≤ (28508563062613501572354629133 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_176_8 sum_0_184_8 (by norm_num)

theorem sum_0_160_32 : blockSum (rowCell 0) 160 32 ≤ (135349033332893504353843399779 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_160_16 sum_0_176_16 (by norm_num)

#print axioms sum_0_160_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
