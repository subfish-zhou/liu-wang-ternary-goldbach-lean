import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_7_64_0 : (30492288177257995261406977 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (78335068426424512299 / 1012144442591027200 : ℝ) := by
  apply lower_of_taylor (t := (1830611 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_64 : (3557640078881299631507063 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 64 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (30492288177257995261406977 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_64_0
  · norm_num [gridPoint]

theorem exp_7_65_0 : (126000858763371757483471597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (407540930988124732627 / 5267930357136384000 : ℝ) := by
  apply lower_of_taylor (t := (915073 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_65 : (36752383299686455090032451 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 65 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (126000858763371757483471597 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_65_0
  · norm_num [gridPoint]

theorem exp_7_66_0 : (129972642556743643081104837 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (82158220975264551763 / 1062414715511808000 : ℝ) := by
  apply lower_of_taylor (t := (914851 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_66 : (37910887470135174111363981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 66 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (129972642556743643081104837 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_66_0
  · norm_num [gridPoint]

theorem exp_7_67_0 : (66936556535360956710797847 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1283587961791500008559 / 16604843031387136000 : ℝ) := by
  apply lower_of_taylor (t := (11433 / 6250 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_67 : (3904859072696826561368739 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 67 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (66936556535360956710797847 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_67_0
  · norm_num [gridPoint]

theorem exp_7_68_0 : (275382052827831804698155599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6468918729481756040339 / 83714144649925632000 : ℝ) := by
  apply lower_of_taylor (t := (914439 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_68 : (40162213411537165407453079 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 68 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (275382052827831804698155599 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_68_0
  · norm_num [gridPoint]

theorem exp_7_69_0 : (282830688562134253681264977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2608080054479240638159 / 33762771572453990400 : ℝ) := by
  apply lower_of_taylor (t := (1828497 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_69 : (41248535831295169641862767 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 69 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (282830688562134253681264977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_69_0
  · norm_num [gridPoint]

theorem exp_7_70_0 : (290070581861431055210526661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (13143570556297735098207 / 170205136001127424000 : ℝ) := by
  apply lower_of_taylor (t := (228517 / 125000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_70 : (42304414879247887350830539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 70 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (290070581861431055210526661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_70_0
  · norm_num [gridPoint]

theorem exp_7_71_0 : (74270204129530901244282959 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (662367540437638474259 / 8580106185821184000 : ℝ) := by
  apply lower_of_taylor (t := (365559 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_71 : (27079250061309579720761 / 625000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 71 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (74270204129530901244282959 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_71_0
  · norm_num [gridPoint]

theorem exp_7_72_0 : (75960304285826257842827873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (667587176392298401699 / 8650241050407936000 : ℝ) := by
  apply lower_of_taylor (t := (1827473 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_72 : (44312749072866660151420313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 72 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (75960304285826257842827873 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_72_0
  · norm_num [gridPoint]

theorem exp_7_73_0 : (62066489872799471491594163 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (13456751211661992426873 / 174413227876332544000 : ℝ) := by
  apply lower_of_taylor (t := (456793 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_73 : (9051888408773065108884429 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 73 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (62066489872799471491594163 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_73_0
  · norm_num [gridPoint]

theorem exp_7_74_0 : (316536113993577010179472761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (108499010866284034769 / 1406618754567561216 : ℝ) := by
  apply lower_of_taylor (t := (1826889 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_74 : (46164195640653103373264473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 74 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (316536113993577010179472761 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_74_0
  · norm_num [gridPoint]

theorem exp_7_75_0 : (8060870864026472212569111 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (6834310732900582737001 / 88623585170998272000 : ℝ) := by
  apply lower_of_taylor (t := (913313 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_75 : (11756118911869545050483361 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 75 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (8060870864026472212569111 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_75_0
  · norm_num [gridPoint]

theorem exp_7_76_0 : (5125192775868614154438993 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1377548903229363749277 / 17867270593948672000 : ℝ) := by
  apply lower_of_taylor (t := (1826381 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_76 : (9567581744172132188152851 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 76 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (5125192775868614154438993 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_76_0
  · norm_num [gridPoint]

theorem exp_7_77_0 : (333253525616595733884836069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2776596311169516416939 / 36020790222683136000 : ℝ) := by
  apply lower_of_taylor (t := (365231 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_77 : (6075286623856645518777977 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 77 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (333253525616595733884836069 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_77_0
  · norm_num [gridPoint]

theorem exp_7_78_0 : (67628908235305580138565307 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (13991101534547660932043 / 181540905863783424000 : ℝ) := by
  apply lower_of_taylor (t := (1825947 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_78 : (49315607488657255610613379 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 78 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (67628908235305580138565307 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_78_0
  · norm_num [gridPoint]

theorem exp_7_79_0 : (342672823741310190887643423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (352496286661963392927 / 4574589254764748800 : ℝ) := by
  apply lower_of_taylor (t := (1825757 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_79 : (1561750636083213700181349 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 79 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (342672823741310190887643423 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_79_0
  · norm_num [gridPoint]

theorem exp_7_80_0 : (173413578536089792323696963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1776154231215608515259 / 23053993011729408000 : ℝ) := by
  apply lower_of_taylor (t := (365117 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_80 : (50581895792454534697667093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 80 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (173413578536089792323696963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_80_0
  · norm_num [gridPoint]

theorem exp_7_81_0 : (350597708211132271644037359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2863850236474263965857 / 37177205514703872000 : ℝ) := by
  apply lower_of_taylor (t := (1825431 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_81 : (25565899872884236187433509 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 81 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (350597708211132271644037359 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_81_0
  · norm_num [gridPoint]

theorem exp_7_82_0 : (353976057569488972341929229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (2885981192500510504197 / 37469164125928448000 : ℝ) := by
  apply lower_of_taylor (t := (912647 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_82 : (10324900857332543380368827 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 82 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (353976057569488972341929229 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_82_0
  · norm_num [gridPoint]

theorem exp_7_83_0 : (89238805043641983311360077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (7270600344101613939719 / 94405661631101952000 : ℝ) := by
  apply lower_of_taylor (t := (73007 / 40000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_83 : (3253686919635639910079379 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 83 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (89238805043641983311360077 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_83_0
  · norm_num [gridPoint]

theorem exp_7_84_0 : (89882414535576981889534053 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1465313785755800758691 / 19028253547120435200 : ℝ) := by
  apply lower_of_taylor (t := (114067 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_84 : (13108612843332165653658979 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 84 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (89882414535576981889534053 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_84_0
  · norm_num [gridPoint]

theorem exp_7_85_0 : (72339056902653716900060151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (14765719968651553325667 / 191759457256643584000 : ℝ) := by
  apply lower_of_taylor (t := (1824987 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_85 : (13187572553657362535752909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 85 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (72339056902653716900060151 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_85_0
  · norm_num [gridPoint]

theorem exp_7_86_0 : (363449458655157134287865619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (595157980782741071119 / 7729683544740864000 : ℝ) := by
  apply lower_of_taylor (t := (912459 / 500000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_86 : (10601224424702827490003599 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 86 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (363449458655157134287865619 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_86_0
  · norm_num [gridPoint]

theorem exp_7_87_0 : (182395486748185072313410721 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (149928290083935896261 / 1947304295568384000 : ℝ) := by
  apply lower_of_taylor (t := (364973 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_87 : (10640354211698224636495853 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 87 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (182395486748185072313410721 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_87_0
  · norm_num [gridPoint]

theorem exp_7_88_0 : (365720034911553394153351883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3776840233302850888077 / 49056120017898496000 : ℝ) := by
  apply lower_of_taylor (t := (1824829 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_88 : (53337267044688678700829957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 88 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (365720034911553394153351883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_88_0
  · norm_num [gridPoint]

theorem exp_7_89_0 : (366238233631507811188790647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3044509558421326047773 / 39544848032557670400 : ℝ) := by
  apply lower_of_taylor (t := (1824809 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_89 : (53412842077145155799371457 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 89 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (366238233631507811188790647 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_89_0
  · norm_num [gridPoint]

theorem exp_7_90_0 : (36634851009561752748185837 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (15338392083163931368037 / 199229709830421504000 : ℝ) := by
  apply lower_of_taylor (t := (456201 / 250000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_90 : (26714462497411969135349459 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 90 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (36634851009561752748185837 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_90_0
  · norm_num [gridPoint]

theorem exp_7_91_0 : (183027556352568902492370929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1545489630446796862209 / 20074088907449344000 : ℝ) := by
  apply lower_of_taylor (t := (114051 / 62500 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_91 : (13346533848049484880867021 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 91 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (183027556352568902492370929 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_91_0
  · norm_num [gridPoint]

theorem exp_7_92_0 : (365363549970021395872673943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (1557206295410340368329 / 20225777789500416000 : ℝ) := by
  apply lower_of_taylor (t := (1824843 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_92 : (13321319160064193189066619 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 92 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (365363549970021395872673943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_92_0
  · norm_num [gridPoint]

theorem exp_7_93_0 : (182140268535209895192628071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (15689894530154898233903 / 203780376291953664000 : ℝ) := by
  apply lower_of_taylor (t := (364977 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_93 : (13281832023235017660086651 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 93 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (182140268535209895192628071 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_93_0
  · norm_num [gridPoint]

theorem exp_7_94_0 : (362813937376577720263258947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (3161678706141422791239 / 41061736853068390400 : ℝ) := by
  apply lower_of_taylor (t := (1824943 / 1000000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_94 : (26456718279146909130642391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 94 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (362813937376577720263258947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_94_0
  · norm_num [gridPoint]

theorem exp_7_95_0 : (45121587435952102485523989 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ expNegLower (995472653365294533277 / 12927668863448064000 : ℝ) := by
  apply lower_of_taylor (t := (365003 / 200000 : ℝ)) (by norm_num) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num
  · norm_num

theorem cell_7_95 : (52644907116093428823383777 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ rowCell 7 95 := by
  simp only [rowCell]
  apply lower_cell_of_exp (e := (45121587435952102485523989 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, phase, Nat.cast_add, Nat.cast_one]
    exact exp_7_95_0
  · norm_num [gridPoint]

theorem sum_7_64_2 : (72328784088499451405103081 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 64 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_64) (by simpa only [blockSum_one] using cell_7_65) (by norm_num)

theorem sum_7_66_2 : (76959478197103439725051371 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 66 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_66) (by simpa only [blockSum_one] using cell_7_67) (by norm_num)

theorem sum_7_64_4 : (37322065571400722782538613 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 64 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_64_2 sum_7_66_2 (by norm_num)

theorem sum_7_68_2 : (40705374621416167524657923 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 68 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_68) (by simpa only [blockSum_one] using cell_7_69) (by norm_num)

theorem sum_7_70_2 : (85631214977343214904048139 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 70 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_70) (by simpa only [blockSum_one] using cell_7_71) (by norm_num)

theorem sum_7_68_4 : (33408392844035109990672797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 68 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_68_2 sum_7_70_2 (by norm_num)

theorem sum_7_64_8 : (316330226505778441083518437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 64 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_64_4 sum_7_68_4 (by norm_num)

theorem sum_7_72_2 : (44786095558365992847921229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 72 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_72) (by simpa only [blockSum_one] using cell_7_73) (by norm_num)

theorem sum_7_74_2 : (93188671288131283575197917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 74 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_74) (by simpa only [blockSum_one] using cell_7_75) (by norm_num)

theorem sum_7_72_4 : (1462086899238906154168323 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 72 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_72_2 sum_7_74_2 (by norm_num)

theorem sum_7_76_2 : (96440201711713825090988071 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 76 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_76) (by simpa only [blockSum_one] using cell_7_77) (by norm_num)

theorem sum_7_78_2 : (99291627843320094016416547 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 78 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_78) (by simpa only [blockSum_one] using cell_7_79) (by norm_num)

theorem sum_7_76_4 : (97865914777516959553702309 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 76 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_76_2 sum_7_78_2 (by norm_num)

theorem sum_7_72_8 : (378492691959897188378444993 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 72 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_72_4 sum_7_76_4 (by norm_num)

theorem sum_7_64_16 : (69482291846567562946196343 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 64 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_64_8 sum_7_72_8 (by norm_num)

theorem sum_7_80_2 : (101713695538223007072534111 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 80 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_80) (by simpa only [blockSum_one] using cell_7_81) (by norm_num)

theorem sum_7_82_2 : (103683495000832955463114199 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 82 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_82) (by simpa only [blockSum_one] using cell_7_83) (by norm_num)

theorem sum_7_80_4 : (20539719053905596253564831 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 80 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_80_2 sum_7_82_2 (by norm_num)

theorem sum_7_84_2 : (1643511587311845511838243 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 84 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_84) (by simpa only [blockSum_one] using cell_7_85) (by norm_num)

theorem sum_7_86_2 : (5310394659100263031624863 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 86 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_86) (by simpa only [blockSum_one] using cell_7_87) (by norm_num)

theorem sum_7_84_4 : (52848158692490843347536203 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 84 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_84_2 sum_7_86_2 (by norm_num)

theorem sum_7_80_8 : (208394912654509667962896561 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 80 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_80_4 sum_7_84_4 (by norm_num)

theorem sum_7_88_2 : (53375054560916917250100707 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 88 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_88) (by simpa only [blockSum_one] using cell_7_89) (by norm_num)

theorem sum_7_90_2 : (53407530193510938897083501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 90 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_90) (by simpa only [blockSum_one] using cell_7_91) (by norm_num)

theorem sum_7_88_4 : (6673911547151741009199013 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 88 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_88_2 sum_7_90_2 (by norm_num)

theorem sum_7_92_2 : (2660315118329921084915327 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 92 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_92) (by simpa only [blockSum_one] using cell_7_93) (by norm_num)

theorem sum_7_94_2 : (105558343674387247084668559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 94 2 := by
  exact block_lower (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_7_94) (by simpa only [blockSum_one] using cell_7_95) (by norm_num)

theorem sum_7_92_4 : (211970948407584090481281639 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 92 4 := by
  exact block_lower (m := 2) (n := 2) sum_7_92_2 sum_7_94_2 (by norm_num)

theorem sum_7_88_8 : (85107223583287960555130011 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 88 8 := by
  exact block_lower (m := 4) (n := 4) sum_7_88_4 sum_7_92_4 (by norm_num)

theorem sum_7_80_16 : (842325943225459138701443177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 80 16 := by
  exact block_lower (m := 8) (n := 8) sum_7_80_8 sum_7_88_8 (by norm_num)

theorem sum_7_64_32 : (1537148861691134768163406607 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤ blockSum (rowCell 7) 64 32 := by
  exact block_lower (m := 16) (n := 16) sum_7_64_16 sum_7_80_16 (by norm_num)

#print axioms sum_7_64_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
