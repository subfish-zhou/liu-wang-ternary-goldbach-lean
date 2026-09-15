import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_5_64_0 : expNegUpper (31051162886760240943 / 404859561279048000 : ℝ) ≤ (491729874685550128251191159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11379 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_64_1 : expNegUpper (1986490113116242014503 / 25911011921859072000 : ℝ) ≤ (506841820310016495504166573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182021 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_64 : rowCell 5 64 ≤ (72816745153333940783629217 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (491729874685550128251191159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (506841820310016495504166573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_64_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_64_1
  · norm_num [gridPoint]

theorem exp_5_65_0 : expNegUpper (50080153402902331812167 / 653226219073131008000 : ℝ) ≤ (506841040121702446060635093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (182021 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_65_1 : expNegUpper (25030670292054573817703 / 326613109536565504000 : ℝ) ≤ (65206276847866290470945851 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (9099 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_65 : rowCell 5 65 ≤ (37499253171378824978438313 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (506841040121702446060635093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (65206276847866290470945851 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_65_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_65_1
  · norm_num [gridPoint]

theorem exp_5_66_0 : expNegUpper (25240417217059639966807 / 329349989202770176000 : ℝ) ≤ (104329885023499043223756339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (9099 / 5000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_66_1 : expNegUpper (10092563983644559127201 / 131739995681108070400 : ℝ) ≤ (268056337425377279852292527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454853 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_66 : rowCell 5 66 ≤ (7713296266282146387744787 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (104329885023499043223756339 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (268056337425377279852292527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_66_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_66_1
  · norm_num [gridPoint]

theorem exp_5_67_0 : expNegUpper (10176782740961175320441 / 132839315208740966400 : ℝ) ≤ (536111876696571377984123271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454853 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_67_1 : expNegUpper (12716675205646410273359 / 166049144010926208000 : ℝ) ≤ (275093496487326712308159281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819043 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_67 : rowCell 5 67 ≤ (15842777909613286569331561 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (536111876696571377984123271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (275093496487326712308159281 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_67_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_67_1
  · norm_num [gridPoint]

theorem exp_5_68_0 : expNegUpper (12822350301825192136751 / 167429002996906112000 : ℝ) ≤ (343866367087648869005379 / 625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1819043 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_68_1 : expNegUpper (51272993289536330736763 / 669716011987624448000 : ℝ) ≤ (563832125536805712417976303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (363739 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_68 : rowCell 5 68 ≤ (81235216250822016863245857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (343866367087648869005379 / 625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (563832125536805712417976303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_68_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_68_1
  · norm_num [gridPoint]

theorem exp_5_69_0 : expNegUpper (2067892277357704099883 / 27010331449491968000 : ℝ) ≤ (563831313446691406285312137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (363739 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_69_1 : expNegUpper (1033634146228270225901 / 13505165724745984000 : ℝ) ≤ (577008402756979633823702683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1818367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_69 : rowCell 5 69 ≤ (83191057078754218980449459 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (563831313446691406285312137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (577008402756979633823702683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_69_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_69_1
  · norm_num [gridPoint]

theorem exp_5_70_0 : expNegUpper (26053820438535012590741 / 340411699396364544000 : ℝ) ≤ (115401517049514587188261723 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1818367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_70_1 : expNegUpper (52092852880555829497361 / 680823398792729088000 : ℝ) ≤ (294838864281567747059935473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (909029 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_70 : rowCell 5 70 ≤ (85075741276913485528416347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (115401517049514587188261723 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (294838864281567747059935473 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_70_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_70_1
  · norm_num [gridPoint]

theorem exp_5_71_0 : expNegUpper (52520413029021683329289 / 686411349653914112000 : ℝ) ≤ (58967690667858357052934879 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (909029 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_71_1 : expNegUpper (1312660999732548301819 / 17160283741347852800 : ℝ) ≤ (601803769030454427010946869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817769 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_71 : rowCell 5 71 ≤ (3475353653744905324778571 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58967690667858357052934879 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (601803769030454427010946869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_71_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_71_1
  · norm_num [gridPoint]

theorem exp_5_72_0 : expNegUpper (1323390834553405591739 / 17300553470521356800 : ℝ) ≤ (300901471909274051316001767 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817769 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_72_1 : expNegUpper (52922478629990465750311 / 692022138820854272000 : ℝ) ≤ (613352128131894539870023909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817499 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_72 : rowCell 5 72 ≤ (17722039917502246593411893 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (300901471909274051316001767 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (613352128131894539870023909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_72_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_72_1
  · norm_num [gridPoint]

theorem exp_5_73_0 : expNegUpper (53353311928752292931359 / 697655766293549568000 : ℝ) ≤ (613351300640033108835206971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1817499 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_73_1 : expNegUpper (26670489397480038629539 / 348827883146774784000 : ℝ) ≤ (124858101936257265934222891 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (56789 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_73 : rowCell 5 73 ≤ (11281244094055571752039249 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (613351300640033108835206971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (124858101936257265934222891 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_73_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_73_1
  · norm_num [gridPoint]

theorem exp_5_74_0 : expNegUpper (1720750677158673211 / 22505991426304000 : ℝ) ≤ (39018105059532998612545991 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (56789 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_74_1 : expNegUpper (3440764830499162453 / 45011982852608000 : ℝ) ≤ (634588864495232377303006023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (227127 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_74 : rowCell 5 74 ≤ (91798554557743860816358897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (39018105059532998612545991 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (634588864495232377303006023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_74_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_74_1
  · norm_num [gridPoint]

theorem exp_5_75_0 : expNegUpper (54196083571843605135797 / 708991536156205568000 : ℝ) ≤ (634588035564452751789027423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (227127 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_75_1 : expNegUpper (13546350916774280171629 / 177247884039051392000 : ℝ) ≤ (644219521950790245071051961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908401 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_75 : rowCell 5 75 ≤ (93251796022676474432166981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (634588035564452751789027423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (644219521950790245071051961 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_75_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_75_1
  · norm_num [gridPoint]

theorem exp_5_76_0 : expNegUpper (13655299163249035384141 / 178673419636541568000 : ℝ) ≤ (322109346920485062333114417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (908401 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_76_1 : expNegUpper (10922269671788369212663 / 142938735709233254400 : ℝ) ≤ (163289326317554943994635637 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816607 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_76 : rowCell 5 76 ≤ (9460582346643716901469309 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (322109346920485062333114417 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (163289326317554943994635637 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_76_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_76_1
  · norm_num [gridPoint]

theorem exp_5_77_0 : expNegUpper (11009761579400958755023 / 144083731848376422400 : ℝ) ≤ (653156478988881093647919347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816607 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_77_1 : expNegUpper (27519897272211118093793 / 360209329620941056000 : ℝ) ≤ (165344907505032183663854181 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816429 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_77 : rowCell 5 77 ≤ (95857154097472434462146883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (653156478988881093647919347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (165344907505032183663854181 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_77_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_77_1
  · norm_num [gridPoint]

theorem exp_5_78_0 : expNegUpper (27739463648104104290257 / 363083239121676544000 : ℝ) ≤ (661378806555936406368581353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816429 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_78_1 : expNegUpper (55470752215876937788393 / 726166478243353088000 : ℝ) ≤ (334433292734186882911694043 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181627 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_78 : rowCell 5 78 ≤ (97002689128757094597408741 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (661378806555936406368581353 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (334433292734186882911694043 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_78_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_78_1
  · norm_num [gridPoint]

theorem exp_5_79_0 : expNegUpper (2236462593717801307273 / 29277485422023168000 : ℝ) ≤ (83608220723489863306484161 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (181627 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_79_1 : expNegUpper (139760578414111493987 / 1829842838876448000 : ℝ) ≤ (84450124824545698776356831 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816127 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_79 : rowCell 5 79 ≤ (6127482773641290750140537 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (83608220723489863306484161 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (84450124824545698776356831 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_79_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_79_1
  · norm_num [gridPoint]

theorem exp_5_80_0 : expNegUpper (3521670658097119550507 / 46108164447722528000 : ℝ) ≤ (675600183641143772454555409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816127 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_80_1 : expNegUpper (56340241986063862335871 / 737730631163560448000 : ℝ) ≤ (681568480715384349738345243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816003 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_80 : rowCell 5 80 ≤ (98965958336099913488541099 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (675600183641143772454555409 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (681568480715384349738345243 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_80_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_80_1
  · norm_num [gridPoint]

theorem exp_5_81_0 : expNegUpper (1831755946721725667369 / 23985385970396672000 : ℝ) ≤ (681567671398980606102527671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1816003 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_81_1 : expNegUpper (183157400224107673357 / 2398538597039667200 : ℝ) ≤ (686757456781642980507216071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (363179 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_81 : rowCell 5 81 ≤ (99779497701538421714586109 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (681567671398980606102527671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (686757456781642980507216071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_81_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_81_1
  · norm_num [gridPoint]

theorem exp_5_82_0 : expNegUpper (5722468629174242805187 / 74938613730678835200 : ℝ) ≤ (68675665398713328218480511 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (363179 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_82_1 : expNegUpper (57219897608211793538261 / 749386137306788352000 : ℝ) ≤ (86394897205597603623753081 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (453951 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_82 : rowCell 5 82 ≤ (20095772082770831756940569 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68675665398713328218480511 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (86394897205597603623753081 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_82_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_82_1
  · norm_num [gridPoint]

theorem exp_5_83_0 : expNegUpper (57667496351999356627469 / 755248147837035008000 : ℝ) ≤ (691158382222357818605404137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (453951 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_83_1 : expNegUpper (14415890648654438364427 / 188812036959258752000 : ℝ) ≤ (347383857798501175722022843 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815731 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_83 : rowCell 5 83 ≤ (5053148811048312659070433 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (691158382222357818605404137 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (347383857798501175722022843 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_83_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_83_1
  · norm_num [gridPoint]

theorem exp_5_84_0 : expNegUpper (581128745214829281443 / 7611329966730368000 : ℝ) ≤ (694766928361831177284563429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815731 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_84_1 : expNegUpper (2324391960841196209123 / 30445319866921472000 : ℝ) ≤ (348789971857059756968147929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815673 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_84 : rowCell 5 84 ≤ (101531184848421205140774203 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (694766928361831177284563429 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (348789971857059756968147929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_84_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_84_1
  · norm_num [gridPoint]

theorem exp_5_85_0 : expNegUpper (58560830792531789331427 / 767040683814793728000 : ℝ) ≤ (348789582722213864231081139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815673 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_85_1 : expNegUpper (29279308439893447789213 / 383520341907396864000 : ℝ) ≤ (699595499594387091940845921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113477 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_85 : rowCell 5 85 ≤ (25470807962185874378494391 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (348789582722213864231081139 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (699595499594387091940845921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_85_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_85_1
  · norm_num [gridPoint]

theorem exp_5_86_0 : expNegUpper (29505687578742293458957 / 386485604631152896000 : ℝ) ≤ (349797365514895376231308243 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113477 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_86_1 : expNegUpper (2360401046529094849513 / 30918848370492231680 : ℝ) ≤ (140163346841093845514923999 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226951 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_86 : rowCell 5 86 ≤ (102119262227130955048203599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (349797365514895376231308243 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (140163346841093845514923999 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_86_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_86_1
  · norm_num [gridPoint]

theorem exp_5_87_0 : expNegUpper (2378580704347198705313 / 31156982920622919680 : ℝ) ≤ (43800998502845974117966229 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (226951 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_87_1 : expNegUpper (7433004607961247366917 / 97365571626946624000 : ℝ) ≤ (701248646643532183532663811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815599 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_87 : rowCell 5 87 ≤ (102239811953921268955439493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43800998502845974117966229 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (701248646643532183532663811 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_87_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_87_1
  · norm_num [gridPoint]

theorem exp_5_88_0 : expNegUpper (7490033517307072275653 / 98112596884324416000 : ℝ) ≤ (701247899546577686234908997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815599 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_88_1 : expNegUpper (59920658973513365400023 / 784900775074595328000 : ℝ) ≤ (350449402845433430892451771 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (907803 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_88 : rowCell 5 88 ≤ (51122898743547471604095421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (701247899546577686234908997 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (350449402845433430892451771 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_88_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_88_1
  · norm_num [gridPoint]

theorem exp_5_89_0 : expNegUpper (2415145469566122614567 / 31635992617574912000 : ℝ) ≤ (175224517568246903639446551 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (907803 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_89_1 : expNegUpper (1207598049700723547219 / 15817996308787456000 : ℝ) ≤ (349888629564651192712681611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815629 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_89 : rowCell 5 89 ≤ (102138503439256246668693117 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (175224517568246903639446551 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (349888629564651192712681611 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_89_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_89_1
  · norm_num [gridPoint]

theorem exp_5_90_0 : expNegUpper (30419816701554037919371 / 398460847054952704000 : ℝ) ≤ (699776535963632771610229493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815629 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_90_1 : expNegUpper (60841777390597061547181 / 796921694109905408000 : ℝ) ≤ (348948215912911563936729709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815667 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_90 : rowCell 5 90 ≤ (12739946066626765316204411 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (699776535963632771610229493 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (348948215912911563936729709 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_90_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_90_1
  · norm_num [gridPoint]

theorem exp_5_91_0 : expNegUpper (61303268122660256357989 / 802966411086193152000 : ℝ) ≤ (43618482590126057593148001 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815667 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_91_1 : expNegUpper (3065314684126733234389 / 40148320554309657600 : ℝ) ≤ (695271013654230580530994567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45393 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_91 : rowCell 5 91 ≤ (101590969996456930882262857 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (43618482590126057593148001 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (695271013654230580530994567 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_91_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_91_1
  · norm_num [gridPoint]

theorem exp_5_92_0 : expNegUpper (3088477544507412682549 / 40451698318411801600 : ℝ) ≤ (347635158269078831023856269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (45393 / 25000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_92_1 : expNegUpper (61773461353187633511811 / 809033966368236032000 : ℝ) ≤ (345958919176257461043167627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815789 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_92 : rowCell 5 92 ≤ (101155006556485754423704573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (347635158269078831023856269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (345958919176257461043167627 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_92_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_92_1
  · norm_num [gridPoint]

theorem exp_5_93_0 : expNegUpper (62238491697910714446779 / 815124359956034048000 : ℝ) ≤ (691917154946165595801187897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815789 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_93_1 : expNegUpper (31121645197447307374169 / 407562179978017024000 : ℝ) ≤ (2686936540781476801526579 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28373 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_93 : rowCell 5 93 ≤ (20122856038433341150634579 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (691917154946165595801187897 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2686936540781476801526579 / 3906250000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_93_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_93_1
  · norm_num [gridPoint]

theorem exp_5_94_0 : expNegUpper (1254202010765725709489 / 16424751836991744000 : ℝ) ≤ (687855085141645988557142129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28373 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_94_1 : expNegUpper (2508631631999770205057 / 32849503673983488000 : ℝ) ≤ (341552744666115562504080871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_94 : rowCell 5 94 ≤ (49985838406513123997575589 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (687855085141645988557142129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (341552744666115562504080871 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_94_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_94_1
  · norm_num [gridPoint]

theorem exp_5_95_0 : expNegUpper (63184387403613613463057 / 827373662048895488000 : ℝ) ≤ (341552417248242514846025893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1815971 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_5_95_1 : expNegUpper (1974717892525787542973 / 25855426939027984000 : ℝ) ≤ (677689507792826290187621987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (454021 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_5_95 : rowCell 5 95 ≤ (49615173014201740999382383 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (341552417248242514846025893 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (677689507792826290187621987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_95_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_5_95_1
  · norm_num [gridPoint]

theorem sum_5_64_2 : blockSum (rowCell 5) 64 2 ≤ (147815251496091590740505843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_64) (by simpa only [blockSum_one] using cell_5_65) (by norm_num)

theorem sum_5_66_2 : blockSum (rowCell 5) 66 2 ≤ (6253874088435515868964227 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_66) (by simpa only [blockSum_one] using cell_5_67) (by norm_num)

theorem sum_5_64_4 : blockSum (rowCell 5) 64 4 ≤ (152081051853489743732305759 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_64_2 sum_5_66_2 (by norm_num)

theorem sum_5_68_2 : blockSum (rowCell 5) 68 2 ≤ (41106568332394058960923829 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_68) (by simpa only [blockSum_one] using cell_5_69) (by norm_num)

theorem sum_5_70_2 : blockSum (rowCell 5) 70 2 ≤ (85979791310268059323940311 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_70) (by simpa only [blockSum_one] using cell_5_71) (by norm_num)

theorem sum_5_68_4 : blockSum (rowCell 5) 68 4 ≤ (168192927975056177245787969 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_68_2 sum_5_70_2 (by norm_num)

theorem sum_5_64_8 : blockSum (rowCell 5) 64 8 ≤ (10008561869642060030565429 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_64_4 sum_5_68_4 (by norm_num)

theorem sum_5_72_2 : blockSum (rowCell 5) 72 2 ≤ (178860152339955806983373457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_72) (by simpa only [blockSum_one] using cell_5_73) (by norm_num)

theorem sum_5_74_2 : blockSum (rowCell 5) 74 2 ≤ (92525175290210167624262939 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_74) (by simpa only [blockSum_one] using cell_5_75) (by norm_num)

theorem sum_5_72_4 : blockSum (rowCell 5) 72 4 ≤ (72782100584075228446379867 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_72_2 sum_5_74_2 (by norm_num)

theorem sum_5_76_2 : blockSum (rowCell 5) 76 2 ≤ (190462977563909603476839973 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_76) (by simpa only [blockSum_one] using cell_5_77) (by norm_num)

theorem sum_5_78_2 : blockSum (rowCell 5) 78 2 ≤ (195042413507017746599657333 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_78) (by simpa only [blockSum_one] using cell_5_79) (by norm_num)

theorem sum_5_76_4 : blockSum (rowCell 5) 76 4 ≤ (192752695535463675038248653 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_76_2 sum_5_78_2 (by norm_num)

theorem sum_5_72_8 : blockSum (rowCell 5) 72 8 ≤ (749415893991303492308396641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_72_4 sum_5_76_4 (by norm_num)

theorem sum_5_64_16 : blockSum (rowCell 5) 64 16 ≤ (1389963853648395334264584097 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_64_8 sum_5_72_8 (by norm_num)

theorem sum_5_80_2 : blockSum (rowCell 5) 80 2 ≤ (24843182004704791900390901 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_80) (by simpa only [blockSum_one] using cell_5_81) (by norm_num)

theorem sum_5_82_2 : blockSum (rowCell 5) 82 2 ≤ (40308367326964082393222301 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_82) (by simpa only [blockSum_one] using cell_5_83) (by norm_num)

theorem sum_5_80_4 : blockSum (rowCell 5) 80 4 ≤ (400287292672458747169238713 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_80_2 sum_5_82_2 (by norm_num)

theorem sum_5_84_2 : blockSum (rowCell 5) 84 2 ≤ (203414416697164702654751767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_84) (by simpa only [blockSum_one] using cell_5_85) (by norm_num)

theorem sum_5_86_2 : blockSum (rowCell 5) 86 2 ≤ (51089768545263056000910773 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_86) (by simpa only [blockSum_one] using cell_5_87) (by norm_num)

theorem sum_5_84_4 : blockSum (rowCell 5) 84 4 ≤ (407773490878216926658394859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_84_2 sum_5_86_2 (by norm_num)

theorem sum_5_80_8 : blockSum (rowCell 5) 80 8 ≤ (202015195887668918456908393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_80_4 sum_5_84_4 (by norm_num)

theorem sum_5_88_2 : blockSum (rowCell 5) 88 2 ≤ (204384300926351189876883959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_88) (by simpa only [blockSum_one] using cell_5_89) (by norm_num)

theorem sum_5_90_2 : blockSum (rowCell 5) 90 2 ≤ (40702107705894210682379629 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_90) (by simpa only [blockSum_one] using cell_5_91) (by norm_num)

theorem sum_5_88_4 : blockSum (rowCell 5) 88 4 ≤ (50986854931977780411097763 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_88_2 sum_5_90_2 (by norm_num)

theorem sum_5_92_2 : blockSum (rowCell 5) 92 2 ≤ (50442321687163115044219367 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_92) (by simpa only [blockSum_one] using cell_5_93) (by norm_num)

theorem sum_5_94_2 : blockSum (rowCell 5) 94 2 ≤ (24900252855178716249239493 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_5_94) (by simpa only [blockSum_one] using cell_5_95) (by norm_num)

theorem sum_5_92_4 : blockSum (rowCell 5) 92 4 ≤ (100242827397520547542698353 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_5_92_2 sum_5_94_2 (by norm_num)

theorem sum_5_88_8 : blockSum (rowCell 5) 88 8 ≤ (202216537261476108364893879 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_5_88_4 sum_5_92_4 (by norm_num)

theorem sum_5_80_16 : blockSum (rowCell 5) 80 16 ≤ (12632241660910782088181321 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_5_80_8 sum_5_88_8 (by norm_num)

theorem sum_5_64_32 : blockSum (rowCell 5) 64 32 ≤ (601378157248995088310358637 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_5_64_16 sum_5_80_16 (by norm_num)

#print axioms sum_5_64_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
