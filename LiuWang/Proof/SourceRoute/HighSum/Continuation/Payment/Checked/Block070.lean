import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_4_192_0 : expNegUpper (383112954737415670769 / 4784759183237377600 : ℝ) ≤ (16854705403716608368623211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1869259 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_192_1 : expNegUpper (122707793977004917535311 / 1531122938635960832000 : ℝ) ≤ (3917353027781016098078307 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467581 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_192 : rowCell 4 192 ≤ (2371687870069011597394419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16854705403716608368623211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3917353027781016098078307 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_192_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_192_1
  · norm_num [gridPoint]

theorem exp_4_193_0 : expNegUpper (123378924416574431495879 / 1539497162799272448000 : ℝ) ≤ (3917351968334603381019393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467581 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_193_1 : expNegUpper (61745897094752872897319 / 769748581399636224000 : ℝ) ≤ (7280846176583905028361349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467849 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_193 : rowCell 4 193 ≤ (440895797854188715039441 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3917351968334603381019393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7280846176583905028361349 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_193_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_193_1
  · norm_num [gridPoint]

theorem exp_4_194_0 : expNegUpper (107969887464046636073 / 1345994978494208000 : ℝ) ≤ (2912337691526907146736969 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (467849 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_194_1 : expNegUpper (216138199998719836699 / 2691989956988416000 : ℝ) ≤ (6763478857501344572027023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (936237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_194 : rowCell 4 194 ≤ (2048249314801752166841447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2912337691526907146736969 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6763478857501344572027023 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_194_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_194_1
  · norm_num [gridPoint]

theorem exp_4_195_0 : expNegUpper (124955494009549261339357 / 1556314126043161088000 : ℝ) ≤ (13526954135383451433606379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (936237 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_195_1 : expNegUpper (31267704099654511296559 / 389078531510790272000 : ℝ) ≤ (12560847198228131316178363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (936779 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_195 : rowCell 4 195 ≤ (1902345911505967280770681 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13526954135383451433606379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12560847198228131316178363 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_195_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_195_1
  · norm_num [gridPoint]

theorem exp_4_196_0 : expNegUpper (31437326171649991947791 / 391189216280934528000 : ℝ) ≤ (12560843910090038148733429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (936779 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_196_1 : expNegUpper (25173171675981361955327 / 312951373024747622400 : ℝ) ≤ (11659223384345948748218147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1874649 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_196 : rowCell 4 196 ≤ (1766149067326982009357687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12560843910090038148733429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (11659223384345948748218147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_196_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_196_1
  · norm_num [gridPoint]

theorem exp_4_197_0 : expNegUpper (25309362521428879513687 / 314644488502014054400 : ℝ) ≤ (11659220365034831565402959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1874649 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_197_1 : expNegUpper (63332300467734423301093 / 786611221255035136000 : ℝ) ≤ (10818164015739027884487539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (937873 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_197 : rowCell 4 197 ≤ (327814212714211886520073 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11659220365034831565402959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10818164015739027884487539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_197_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_197_1
  · norm_num [gridPoint]

theorem exp_4_198_0 : expNegUpper (63674013881760598700117 / 790855429101078784000 : ℝ) ≤ (10818161244260139925720689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (937873 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_198_1 : expNegUpper (127467054057642802391953 / 1581710858202157568000 : ℝ) ≤ (2508488408220492295304059 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1876849 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_198 : rowCell 4 198 ≤ (380138737790790632110373 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10818161244260139925720689 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2508488408220492295304059 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_198_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_198_1
  · norm_num [gridPoint]

theorem exp_4_199_0 : expNegUpper (8201789449476416897 / 101774215180800000 : ℝ) ≤ (2508487772446940578426133 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1876849 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_199_1 : expNegUpper (1026185821910138591 / 12721776897600000 : ℝ) ≤ (9303075294910451824784479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938979 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_199 : rowCell 4 199 ≤ (11016197945951845916253 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2508487772446940578426133 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (9303075294910451824784479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_199_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_199_1
  · norm_num [gridPoint]

theorem exp_4_200_0 : expNegUpper (16120202469140811767959 / 199844525562949696000 : ℝ) ≤ (9303072962195095325821497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938979 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_200_1 : expNegUpper (129083131971181057780391 / 1598756204503597568000 : ℝ) ≤ (8622202407684249785339241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879073 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_200 : rowCell 4 200 ≤ (261425436942238394295993 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9303072962195095325821497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8622202407684249785339241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_200_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_200_1
  · norm_num [gridPoint]

theorem exp_4_201_0 : expNegUpper (129774016571032284513439 / 1607313135112950272000 : ℝ) ≤ (8622200268684562734622101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879073 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_201_1 : expNegUpper (12989677674722265083719 / 160731313511295027200 : ℝ) ≤ (3994095340331112859475709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376039 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_201 : rowCell 4 201 ≤ (1211244631424486367789833 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8622200268684562734622101 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3994095340331112859475709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_201_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_201_1
  · norm_num [gridPoint]

theorem exp_4_202_0 : expNegUpper (13059016059412503185399 / 161589290402805811200 : ℝ) ≤ (3994094359982351763695379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (376039 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_202_1 : expNegUpper (130714172059230749774461 / 1615892904028058112000 : ℝ) ≤ (3699035115632191808175237 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1881323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_202 : rowCell 4 202 ≤ (70123739144728220587787 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3994094359982351763695379 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3699035115632191808175237 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_202_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_202_1
  · norm_num [gridPoint]

theorem exp_4_203_0 : expNegUpper (131410061814743382894389 / 1624495511248921088000 : ℝ) ≤ (7398068434618008592019867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1881323 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_203_1 : expNegUpper (32883831974886000330317 / 406123877812230272000 : ℝ) ≤ (3424518926461682966585297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (235307 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_203 : rowCell 4 203 ≤ (259727947655518060832641 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7398068434618008592019867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3424518926461682966585297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_203_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_203_1
  · norm_num [gridPoint]

theorem exp_4_204_0 : expNegUpper (1322337302252259843637 / 16331209567755392000 : ℝ) ≤ (6849036207157901560176977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (235307 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_204_1 : expNegUpper (5294410170420042088267 / 65324838271021568000 : ℝ) ≤ (6338449460722045399866981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470899 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_204 : rowCell 4 204 ≤ (961643303033460468216253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6849036207157901560176977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6338449460722045399866981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_204_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_204_1
  · norm_num [gridPoint]

theorem exp_4_205_0 : expNegUpper (4292295994126176870677 / 52960298084126208000 : ℝ) ≤ (6338447953671524087136339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (470899 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_205_1 : expNegUpper (2148209050555492728383 / 26480149042063104000 : ℝ) ≤ (1172762545274164082226589 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (942371 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_205 : rowCell 4 205 ≤ (444899905878633743178841 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6338447953671524087136339 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1172762545274164082226589 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_205_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_205_1
  · norm_num [gridPoint]

theorem exp_4_206_0 : expNegUpper (66946204292569262752657 / 825220181373020416000 : ℝ) ≤ (5863811346801944769561591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (942371 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_206_1 : expNegUpper (26804291702740227781909 / 330088072549208166400 : ℝ) ≤ (5422779912293040643731599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (942947 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_206 : rowCell 4 206 ≤ (823028374910040679488297 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5863811346801944769561591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5422779912293040643731599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_206_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_206_1
  · norm_num [gridPoint]

theorem exp_4_207_0 : expNegUpper (26945487703849151727149 / 331826864637984870400 : ℝ) ≤ (542277864983822879455987 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (942947 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_207_1 : expNegUpper (8428609774413841761571 / 103695895199370272000 : ℝ) ≤ (2506570456377179217056479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1887051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_207 : rowCell 4 207 ≤ (760996630525733477492411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (542277864983822879455987 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2506570456377179217056479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_207_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_207_1
  · norm_num [gridPoint]

theorem exp_4_208_0 : expNegUpper (8472892225785739319459 / 104240695121222688000 : ℝ) ≤ (39165154358196674761503 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1887051 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_208_1 : expNegUpper (135697864757540183715583 / 1667851121939563008000 : ℝ) ≤ (4632816508286030335903839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (377643 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_208 : rowCell 4 208 ≤ (175847949303852995741003 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39165154358196674761503 / 7812500000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4632816508286030335903839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_208_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_208_1
  · norm_num [gridPoint]

theorem exp_4_209_0 : expNegUpper (5456357194298215346447 / 67063630359798272000 : ℝ) ≤ (2316407726055375441266931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (377643 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_209_1 : expNegUpper (2730835872135918644599 / 33531815179899136000 : ℝ) ≤ (4279851838107289934232503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (236173 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_209 : rowCell 4 209 ≤ (12998394125544361832593 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2316407726055375441266931 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4279851838107289934232503 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_209_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_209_1
  · norm_num [gridPoint]

theorem exp_4_210_0 : expNegUpper (68627705623117534507151 / 842676617178052864000 : ℝ) ≤ (427985087253237035865027 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (236173 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_210_1 : expNegUpper (137389552930727360457301 / 1685353234356105728000 : ℝ) ≤ (3952410093841658971931277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1890559 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_210 : rowCell 4 210 ≤ (75037983229994524431623 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (427985087253237035865027 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3952410093841658971931277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_210_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_210_1
  · norm_num [gridPoint]

theorem exp_4_211_0 : expNegUpper (138105729771249531899789 / 1694138548023009792000 : ℝ) ≤ (1976204605688434830851717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1890559 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_211_1 : expNegUpper (1382411527216731151267 / 16941385480230097920 : ℝ) ≤ (228047902283755152128939 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94587 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_211 : rowCell 4 211 ≤ (554284557427350322209939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1976204605688434830851717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (228047902283755152128939 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_211_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_211_1
  · norm_num [gridPoint]

theorem exp_4_212_0 : expNegUpper (1389598954248374190467 / 17029466999956689920 : ℝ) ≤ (3648765630287099353178961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94587 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_212_1 : expNegUpper (139096602971971842967211 / 1702946699995668992000 : ℝ) ≤ (3367302137863590743322013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1892927 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_212 : rowCell 4 212 ≤ (102323593030386753944497 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3648765630287099353178961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3367302137863590743322013 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_212_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_212_1
  · norm_num [gridPoint]

theorem exp_4_213_0 : expNegUpper (139817918199337377184099 / 1711777690274083328000 : ℝ) ≤ (1683650700735916226763237 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1892927 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_213_1 : expNegUpper (69977956836981095353949 / 855888845137041664000 : ℝ) ≤ (3106498945233292843646947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (47353 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_213 : rowCell 4 213 ≤ (59009417198342091194487 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1683650700735916226763237 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3106498945233292843646947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_213_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_213_1
  · norm_num [gridPoint]

theorem exp_4_214_0 : expNegUpper (2813596161741761060821 / 34412630377165056000 : ℝ) ≤ (3106498272858806776655063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (47353 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_214_1 : expNegUpper (5632763792799312203113 / 68825260754330112000 : ℝ) ≤ (2864933669819378635219811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (947659 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_214 : rowCell 4 214 ≤ (217721091109239640083061 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3106498272858806776655063 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2864933669819378635219811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_214_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_214_1
  · norm_num [gridPoint]

theorem exp_4_215_0 : expNegUpper (141545575080428093346617 / 1729508185748177408000 : ℝ) ≤ (572986611217317793292661 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (947659 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_215_1 : expNegUpper (17710769550296541600757 / 216188523218522176000 : ℝ) ≤ (2641272995406998762403961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (948261 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_215 : rowCell 4 215 ≤ (401517492256911805959227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (572986611217317793292661 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2641272995406998762403961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_215_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_215_1
  · norm_num [gridPoint]

theorem exp_4_216_0 : expNegUpper (17801903646462018103733 / 217300961367982144000 : ℝ) ≤ (2641272435373137653149603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (948261 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_216_1 : expNegUpper (28511421682693884124331 / 347681538188771430400 : ℝ) ≤ (1217134252719511257188347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (474433 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_216 : rowCell 4 216 ≤ (370113005460336730341169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2641272435373137653149603 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1217134252719511257188347 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_216_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_216_1
  · norm_num [gridPoint]

theorem exp_4_217_0 : expNegUpper (1245989394375920471477 / 15194174212567756800 : ℝ) ≤ (486853598912215127498663 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (474433 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_217_1 : expNegUpper (3118086105339406853341 / 37985435531419392000 : ℝ) ≤ (112137596244374960352977 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1898947 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_217 : rowCell 4 217 ≤ (341052494536273957243757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (486853598912215127498663 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (112137596244374960352977 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_217_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_217_1
  · norm_num [gridPoint]

theorem exp_4_218_0 : expNegUpper (72083119308685434122827 / 878137608126241024000 : ℝ) ≤ (112137572949575266888573 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1898947 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_218_1 : expNegUpper (144310723691140863431213 / 1756275216252482048000 : ℝ) ≤ (2065630573041061763422067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (237521 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_218 : rowCell 4 218 ≤ (314171088587796697278537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (112137572949575266888573 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2065630573041061763422067 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_218_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_218_1
  · norm_num [gridPoint]

theorem exp_4_219_0 : expNegUpper (5801904558258193345453 / 70609729454617088000 : ℝ) ≤ (2065630148293614788722799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (237521 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_219_1 : expNegUpper (1451934069423925118833 / 17652432363654272000 : ℝ) ≤ (19018830228085820889673 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950697 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_219 : rowCell 4 219 ≤ (28931462499938685845117 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2065630148293614788722799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19018830228085820889673 / 10000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_219_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_219_1
  · norm_num [gridPoint]

theorem exp_4_220_0 : expNegUpper (36483229090705349280233 / 443558523696031872000 : ℝ) ≤ (1901882635690392059568447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (950697 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_220_1 : expNegUpper (146080020591706307339011 / 1774234094784127488000 : ℝ) ≤ (1750554961724376576466537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (951313 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_220 : rowCell 4 220 ≤ (66584757772597214067717 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1901882635690392059568447 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1750554961724376576466537 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_220_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_220_1
  · norm_num [gridPoint]

theorem exp_4_221_0 : expNegUpper (146822155828809205428539 / 1783247791508582912000 : ℝ) ≤ (218819326125719298431687 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (951313 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_221_1 : expNegUpper (14697057463142089652741 / 178324779150858291200 : ℝ) ≤ (1610755249491634478883551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (237983 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_221 : rowCell 4 221 ≤ (61277433702113897470277 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (218819326125719298431687 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1610755249491634478883551 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_221_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_221_1
  · norm_num [gridPoint]

theorem exp_4_222_0 : expNegUpper (14771534234675690528821 / 179228432653879347200 : ℝ) ≤ (1610754928209772416229821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (237983 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_222_1 : expNegUpper (147865079053874926177561 / 1792284326538793472000 : ℝ) ≤ (1481652166613189842124669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1905107 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_222 : rowCell 4 222 ≤ (56375275922247415721091 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1610754928209772416229821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1481652166613189842124669 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_222_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_222_1
  · norm_num [gridPoint]

theorem exp_4_223_0 : expNegUpper (148612485909003143429009 / 1801343699874759168000 : ℝ) ≤ (1481651874051117570561789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1905107 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_4_223_1 : expNegUpper (4648860745356470094329 / 56291990621086224000 : ℝ) ≤ (1362469848427196672000571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (381271 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_4_223 : rowCell 4 223 ≤ (2073959112687287136781 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1481651874051117570561789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1362469848427196672000571 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_223_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_4_223_1
  · norm_num [gridPoint]

theorem sum_4_192_2 : blockSum (rowCell 4) 192 2 ≤ (572020857417494396573953 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_192) (by simpa only [blockSum_one] using cell_4_193) (by norm_num)

theorem sum_4_194_2 : blockSum (rowCell 4) 194 2 ≤ (123456100822116232737879 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_194) (by simpa only [blockSum_one] using cell_4_195) (by norm_num)

theorem sum_4_192_4 : blockSum (rowCell 4) 192 4 ≤ (1065845260705959327525469 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_192_2 sum_4_194_2 (by norm_num)

theorem sum_4_196_2 : blockSum (rowCell 4) 196 2 ≤ (851305032724510360489513 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_196) (by simpa only [blockSum_one] using cell_4_197) (by norm_num)

theorem sum_4_198_2 : blockSum (rowCell 4) 198 2 ≤ (732657072061249701430469 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_198) (by simpa only [blockSum_one] using cell_4_199) (by norm_num)

theorem sum_4_196_4 : blockSum (rowCell 4) 196 4 ≤ (791981052392880030959991 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_196_2 sum_4_198_2 (by norm_num)

theorem sum_4_192_8 : blockSum (rowCell 4) 192 8 ≤ (92891315654941967924273 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_192_4 sum_4_196_4 (by norm_num)

theorem sum_4_200_2 : blockSum (rowCell 4) 200 2 ≤ (1259185908067839169634899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_200) (by simpa only [blockSum_one] using cell_4_201) (by norm_num)

theorem sum_4_202_2 : blockSum (rowCell 4) 202 2 ≤ (540222904234430943183789 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_202) (by simpa only [blockSum_one] using cell_4_203) (by norm_num)

theorem sum_4_200_4 : blockSum (rowCell 4) 200 4 ≤ (2339631716536701056002477 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_200_2 sum_4_202_2 (by norm_num)

theorem sum_4_204_2 : blockSum (rowCell 4) 204 2 ≤ (370288622958145590914787 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_204) (by simpa only [blockSum_one] using cell_4_205) (by norm_num)

theorem sum_4_206_2 : blockSum (rowCell 4) 206 2 ≤ (396006251358943539245177 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_206) (by simpa only [blockSum_one] using cell_4_207) (by norm_num)

theorem sum_4_204_4 : blockSum (rowCell 4) 204 4 ≤ (3435468120226502111554643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_204_2 sum_4_206_2 (by norm_num)

theorem sum_4_200_8 : blockSum (rowCell 4) 200 8 ≤ (8114731553299904223559597 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_200_4 sum_4_204_4 (by norm_num)

theorem sum_4_192_16 : blockSum (rowCell 4) 192 16 ≤ (22977342058090619091443277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_192_8 sum_4_200_8 (by norm_num)

theorem sum_4_208_2 : blockSum (rowCell 4) 208 2 ≤ (676655751746315037296831 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_208) (by simpa only [blockSum_one] using cell_4_209) (by norm_num)

theorem sum_4_210_2 : blockSum (rowCell 4) 210 2 ≤ (1154588423267306517662923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_210) (by simpa only [blockSum_one] using cell_4_211) (by norm_num)

theorem sum_4_208_4 : blockSum (rowCell 4) 208 4 ≤ (501579985351987318451317 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_208_2 sum_4_210_2 (by norm_num)

theorem sum_4_212_2 : blockSum (rowCell 4) 212 2 ≤ (983693302738670499278381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_212) (by simpa only [blockSum_one] using cell_4_213) (by norm_num)

theorem sum_4_214_2 : blockSum (rowCell 4) 214 2 ≤ (836959674475391086125349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_214) (by simpa only [blockSum_one] using cell_4_215) (by norm_num)

theorem sum_4_212_4 : blockSum (rowCell 4) 212 4 ≤ (182065297721406158540373 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_212_2 sum_4_214_2 (by norm_num)

theorem sum_4_208_8 : blockSum (rowCell 4) 208 8 ≤ (865710580794799635532063 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_208_4 sum_4_212_4 (by norm_num)

theorem sum_4_216_2 : blockSum (rowCell 4) 216 2 ≤ (355582749998305343792463 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_216) (by simpa only [blockSum_one] using cell_4_217) (by norm_num)

theorem sum_4_218_2 : blockSum (rowCell 4) 218 2 ≤ (603485713587183555729707 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_218) (by simpa only [blockSum_one] using cell_4_219) (by norm_num)

theorem sum_4_216_4 : blockSum (rowCell 4) 216 4 ≤ (1314651213583794243314633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_216_2 sum_4_218_2 (by norm_num)

theorem sum_4_220_2 : blockSum (rowCell 4) 220 2 ≤ (63931095737355555768997 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_220) (by simpa only [blockSum_one] using cell_4_221) (by norm_num)

theorem sum_4_222_2 : blockSum (rowCell 4) 222 2 ≤ (13528031717428699267577 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_4_222) (by simpa only [blockSum_one] using cell_4_223) (by norm_num)

theorem sum_4_220_4 : blockSum (rowCell 4) 220 4 ≤ (23608644521414070567861 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_4_220_2 sum_4_222_2 (by norm_num)

theorem sum_4_216_8 : blockSum (rowCell 4) 216 8 ≤ (2258996994440357066029073 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_4_216_4 sum_4_220_4 (by norm_num)

theorem sum_4_208_16 : blockSum (rowCell 4) 208 16 ≤ (1646887474603588810922347 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_4_208_8 sum_4_216_8 (by norm_num)

theorem sum_4_192_32 : blockSum (rowCell 4) 192 32 ≤ (5912978391300994867026533 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_4_192_16 sum_4_208_16 (by norm_num)

#print axioms sum_4_192_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
