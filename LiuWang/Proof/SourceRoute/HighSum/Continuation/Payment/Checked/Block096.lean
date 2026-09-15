import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_6_0_0 : expNegUpper (56471515483061940881 / 676601617795489000 : ℝ) ≤ (282931803478014647923551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1919487 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_0_1 : expNegUpper (28848644319994760690191 / 346420028311290368000 : ℝ) ≤ (682203002459331799623059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (383337 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_0 : rowCell 6 0 ≤ (91010138468412527695169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (282931803478014647923551 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (682203002459331799623059 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_0_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_0_1
  · norm_num [gridPoint]

theorem exp_6_1_0 : expNegUpper (29180858581801428130439 / 350409297769615872000 : ℝ) ≤ (136439860588665222756177 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (383337 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_1_1 : expNegUpper (2911666877669449583899 / 35040929776961587200 : ℝ) ≤ (40967324967197020834469 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (239243 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_1 : rowCell 6 1 ≤ (27373517236961054466979 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (136439860588665222756177 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (40967324967197020834469 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_1_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_1_1
  · norm_num [gridPoint]

theorem exp_6_2_0 : expNegUpper (2945004997373275368779 / 35442140553369651200 : ℝ) ≤ (819342156422608519465159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (239243 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_2_1 : expNegUpper (29386445301631391055461 / 354421405533696512000 : ℝ) ≤ (15318776064402883596627 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1911263 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_2 : rowCell 6 2 ≤ (5249557465724780269679 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (819342156422608519465159 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15318776064402883596627 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_2_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_2_1
  · norm_num [gridPoint]

theorem exp_6_3_0 : expNegUpper (29721000095460337132189 / 358456351603532288000 : ℝ) ≤ (61274786761956871102251 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1911263 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_3_1 : expNegUpper (7414495971786023267167 / 89614087900883072000 : ℝ) ≤ (584413525661064135243769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11929 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_3 : rowCell 6 3 ≤ (15672331873643353949101 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (61274786761956871102251 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (584413525661064135243769 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_3_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_3_1
  · norm_num [gridPoint]

theorem exp_6_4_0 : expNegUpper (299937189393228251927 / 3625141359791232000 : ℝ) ≤ (58441056513418804983469 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (11929 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_4_1 : expNegUpper (1197251781022849944307 / 14500565439164928000 : ℝ) ≤ (277691723669156932094851 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (953037 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_4 : rowCell 6 4 ≤ (46619784206242187041183 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58441056513418804983469 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (277691723669156932094851 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_4_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_4_1
  · norm_num [gridPoint]

theorem exp_6_5_0 : expNegUpper (30268216497658864598387 / 366594758660469248000 : ℝ) ≤ (1388451740827667541485743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (953037 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_5_1 : expNegUpper (15103193604625752200773 / 183297379330234624000 : ℝ) ≤ (821766077520189627028937 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (475891 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_5 : rowCell 6 5 ≤ (110547494867364708139667 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1388451740827667541485743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (821766077520189627028937 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_5_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_5_1
  · norm_num [gridPoint]

theorem exp_6_6_0 : expNegUpper (15272251381403551039157 / 185349109823785216000 : ℝ) ≤ (410881048446606339921403 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (475891 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_6_1 : expNegUpper (6096654386104701435869 / 74139643929514086400 : ℝ) ≤ (969352155009762338442973 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1901109 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_6 : rowCell 6 6 ≤ (130609660452975632412517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (410881048446606339921403 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (969352155009762338442973 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_6_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_6_1
  · norm_num [gridPoint]

theorem exp_6_7_0 : expNegUpper (6164517545421236872309 / 74964903788085350400 : ℝ) ≤ (1938695125147060783212819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1901109 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_7_1 : expNegUpper (3845244835215737958767 / 46853064867553344000 : ℝ) ≤ (2279071851737216880566161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (474677 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_7 : rowCell 6 7 ≤ (307563357354419821710977 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1938695125147060783212819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2279071851737216880566161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_7_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_7_1
  · norm_num [gridPoint]

theorem exp_6_8_0 : expNegUpper (3887810172861844772143 / 47371707067379776000 : ℝ) ≤ (113953064505210747717001 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1898709 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_8_1 : expNegUpper (31042457455197340602983 / 378973656539038208000 : ℝ) ≤ (41721697923961586046657 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1896361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_8 : rowCell 6 8 ≤ (180451876736767828478359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (113953064505210747717001 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (41721697923961586046657 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_8_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_8_1
  · norm_num [gridPoint]

theorem exp_6_9_0 : expNegUpper (1255367748900458810167 / 15325825297736192000 : ℝ) ≤ (2670176561733712566200397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1896361 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_9_1 : expNegUpper (626495564865529294139 / 7662912648868096000 : ℝ) ≤ (1559040007638492802336681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (378813 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_9 : rowCell 6 9 ≤ (422084869982388518669253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2670176561733712566200397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1559040007638492802336681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_9_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_9_1
  · norm_num [gridPoint]

theorem exp_6_10_0 : expNegUpper (15833867369147483660851 / 193670223326763264000 : ℝ) ≤ (3118066184689121537138049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (378813 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_10_1 : expNegUpper (31608931038301922711101 / 387340446653526528000 : ℝ) ≤ (3629253538704341262853937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94591 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_10 : rowCell 6 10 ≤ (9840412325498305873793 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3118066184689121537138049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3629253538704341262853937 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_10_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_10_1
  · norm_num [gridPoint]

theorem exp_6_11_0 : expNegUpper (1681742864346520847831 / 20608321008915968000 : ℝ) ≤ (1814618893303594025350803 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (94591 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_11_1 : expNegUpper (3357360613959195931 / 41216642017831936 : ℝ) ≤ (4210706531887910095746349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (236203 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_11 : rowCell 6 11 ≤ (285847891702318102389363 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1814618893303594025350803 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4210706531887910095746349 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_11_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_11_1
  · norm_num [gridPoint]

theorem exp_6_12_0 : expNegUpper (64480685535433806689 / 791597179982070784 : ℝ) ≤ (2105344323325995027909681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (15117 / 8000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_12_1 : expNegUpper (32182772618546427336211 / 395798589991035392000 : ℝ) ≤ (4869928971128872623718151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (943739 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_12 : rowCell 6 12 ≤ (66216679505597148158569 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2105344323325995027909681 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4869928971128872623718151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_12_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_12_1
  · norm_num [gridPoint]

theorem exp_6_13_0 : expNegUpper (32529429766032635757899 / 400061919118422528000 : ℝ) ≤ (1217477181374161615831851 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1887479 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_13_1 : expNegUpper (16236240694221383707649 / 200030959559211264000 : ℝ) ≤ (2807450911875545765301971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1885381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_13 : rowCell 6 13 ≤ (382280902599061447141039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1217477181374161615831851 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2807450911875545765301971 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_13_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_13_1
  · norm_num [gridPoint]

theorem exp_6_14_0 : expNegUpper (656407708197394801561 / 8086961731031296000 : ℝ) ≤ (5614878974616653264391783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1885381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_14_1 : expNegUpper (1310562485385601132433 / 16173923462062592000 : ℝ) ≤ (1613522544293733247497249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (188333 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_14 : rowCell 6 14 ≤ (440040036881557391211361 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5614878974616653264391783 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1613522544293733247497249 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_14_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_14_1
  · norm_num [gridPoint]

theorem exp_6_15_0 : expNegUpper (33113219691566863034017 / 408657092290462208000 : ℝ) ≤ (6454064465474054819196171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (188333 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_15_1 : expNegUpper (2066095303092303546991 / 25541068268153888000 : ℝ) ≤ (3698215380274678704958877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (940663 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_15 : rowCell 6 15 ≤ (1009990555685931850156413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6454064465474054819196171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3698215380274678704958877 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_15_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_15_1
  · norm_num [gridPoint]

theorem exp_6_16_0 : expNegUpper (2087996412716415709679 / 25811808520944672000 : ℝ) ≤ (3698200955635071638668517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (940663 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_16_1 : expNegUpper (6670575905058379893491 / 82597787267022950400 : ℝ) ≤ (8451313473200809738588621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_16 : rowCell 6 16 ≤ (23112592880348252590863 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3698200955635071638668517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8451313473200809738588621 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_16_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_16_1
  · norm_num [gridPoint]

theorem exp_6_17_0 : expNegUpper (6740912827579150353931 / 83468723737104486400 : ℝ) ≤ (8451281195524474393139419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1879367 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_17_1 : expNegUpper (16825068077211901593343 / 208671809342761216000 : ℝ) ≤ (1203569573140132593488533 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938727 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_17 : rowCell 6 17 ≤ (82399875910558029450511 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8451281195524474393139419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1203569573140132593488533 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_17_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_17_1
  · norm_num [gridPoint]

theorem exp_6_18_0 : expNegUpper (17001547143602405503727 / 210860569670842624000 : ℝ) ≤ (9628520572701428083315151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (938727 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_18_1 : expNegUpper (33949304729211214638613 / 421721139341685248000 : ℝ) ≤ (2734593833692753442235893 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (29306 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_18 : rowCell 6 18 ≤ (1499756527643432329638683 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9628520572701428083315151 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2734593833692753442235893 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_18_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_18_1
  · norm_num [gridPoint]

theorem exp_6_19_0 : expNegUpper (44262636185456097803 / 549834191359488000 : ℝ) ≤ (5469167633080114831819043 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (29306 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_19_1 : expNegUpper (11048514594191219533 / 137458547839872000 : ℝ) ≤ (2478268743626945868266561 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1873757 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_19 : rowCell 6 19 ≤ (1701221151793250863144709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5469167633080114831819043 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2478268743626945868266561 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_19_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_19_1
  · norm_num [gridPoint]

theorem exp_6_20_0 : expNegUpper (8651480099951348217083 / 107636173892819072000 : ℝ) ≤ (12391299257361419361702461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1873757 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_20_1 : expNegUpper (34553417685107147656811 / 430544695571276288000 : ℝ) ≤ (1399834933953354217213867 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1871973 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_20 : rowCell 6 20 ≤ (1924356885135491867864699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12391299257361419361702461 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1399834933953354217213867 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_20_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_20_1
  · norm_num [gridPoint]

theorem exp_6_21_0 : expNegUpper (34910236347774208949539 / 434990731144704512000 : ℝ) ≤ (13998300136838225788169829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1871973 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_21_1 : expNegUpper (3485838205089296268121 / 43499073114470451200 : ℝ) ≤ (15770541278331339696402413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (187023 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_21 : rowCell 6 21 ≤ (1085385330718811828270749 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (13998300136838225788169829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15770541278331339696402413 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_21_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_21_1
  · norm_num [gridPoint]

theorem exp_6_22_0 : expNegUpper (3521650087997357077001 / 43945960502388787200 : ℝ) ≤ (1577048697106235576256763 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (187023 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_22_1 : expNegUpper (35165298331688872354561 / 439459605023887872000 : ℝ) ≤ (3543854203055626655416773 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1868529 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_22 : rowCell 6 22 ≤ (2442103240818389313554509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1577048697106235576256763 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3543854203055626655416773 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_22_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_22_1
  · norm_num [gridPoint]

theorem exp_6_23_0 : expNegUpper (35524723988742125058809 / 443951317208826368000 : ℝ) ≤ (17719211228949655076349053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1868529 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_23_1 : expNegUpper (4434272064979190425741 / 55493914651103296000 : ℝ) ≤ (19856026556636757933830421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1866867 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_23 : rowCell 6 23 ≤ (2740020098327659224495227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17719211228949655076349053 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19856026556636757933830421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_23_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_23_1
  · norm_num [gridPoint]

theorem exp_6_24_0 : expNegUpper (7166983133283703709 / 89693173539904000 : ℝ) ≤ (2481995113268587669890807 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (466717 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_24_1 : expNegUpper (57256042572264900103 / 717545388319232000 : ℝ) ≤ (22192359992060682574539331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (932623 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_24 : rowCell 6 24 ≤ (23954697950669806729971 / 7812500000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2481995113268587669890807 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22192359992060682574539331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_24_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_24_1
  · norm_num [gridPoint]

theorem exp_6_25_0 : expNegUpper (36147085905341397957647 / 453003256495968768000 : ℝ) ≤ (22192288083078461631555687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (932623 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_25_1 : expNegUpper (18048929293761818279483 / 226501628247984384000 : ℝ) ≤ (154623805137272601220717 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1863663 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_25 : rowCell 6 25 ≤ (855582667967870359719297 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (22192288083078461631555687 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (154623805137272601220717 / 6250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_25_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_25_1
  · norm_num [gridPoint]

theorem exp_6_26_0 : expNegUpper (18230622348924705012907 / 228781741799086336000 : ℝ) ≤ (4947946050490760291687357 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1863663 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_26_1 : expNegUpper (7282536490349278423753 / 91512696719634534400 : ℝ) ≤ (3438726436284354362616379 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (931059 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_26 : rowCell 6 26 ≤ (3810083526827431646084331 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4947946050490760291687357 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3438726436284354362616379 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_26_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_26_1
  · norm_num [gridPoint]

theorem exp_6_27_0 : expNegUpper (7355480407256240295713 / 92429309801226342400 : ℝ) ≤ (27509725852190849798399943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (931059 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_27_1 : expNegUpper (9182377048168118993209 / 115536637251532928000 : ℝ) ≤ (6102723531474993112744337 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1860611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_27 : rowCell 6 27 ≤ (4231114339065223631743149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27509725852190849798399943 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6102723531474993112744337 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_27_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_27_1
  · norm_num [gridPoint]

theorem exp_6_28_0 : expNegUpper (9273891978243854761241 / 116688113179961472000 : ℝ) ≤ (3051352453848504033400737 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1860611 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_28_1 : expNegUpper (37048345802640534850243 / 466752452719845888000 : ℝ) ≤ (8440548460997403368183477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1859141 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_28 : rowCell 6 28 ≤ (2343521566082893005079677 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3051352453848504033400737 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8440548460997403368183477 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_28_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_28_1
  · norm_num [gridPoint]

theorem exp_6_29_0 : expNegUpper (1496630092810828378163 / 18855247789572608000 : ℝ) ≤ (4220261603729666963388389 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1859141 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_29_1 : expNegUpper (747384105479784309601 / 9427623894786304000 : ℝ) ≤ (18633062584108325313359583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464427 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_29 : rowCell 6 29 ≤ (5179441470832704310090959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4220261603729666963388389 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (18633062584108325313359583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_29_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_29_1
  · norm_num [gridPoint]

theorem exp_6_30_0 : expNegUpper (993104348697518932499 / 12527178291172096000 : ℝ) ≤ (37266015844202632820016743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464427 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_30_1 : expNegUpper (1983794557845113925859 / 25054356582344192000 : ℝ) ≤ (20517756991521866126995303 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (185631 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_30 : rowCell 6 30 ≤ (2854908952016754553926369 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (37266015844202632820016743 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20517756991521866126995303 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_30_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_30_1
  · norm_num [gridPoint]

theorem exp_6_31_0 : expNegUpper (38062216696019095716689 / 480707193695519232000 : ℝ) ≤ (20517697968307594238447933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (185631 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_6_31_1 : expNegUpper (237606436063643930707 / 3004419960596995200 : ℝ) ≤ (22539938149553753489094249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1854947 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_6_31 : rowCell 6 31 ≤ (125592060412375964693879 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20517697968307594238447933 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (22539938149553753489094249 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_31_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_6_31_1
  · norm_num [gridPoint]

theorem sum_6_0_2 : blockSum (rowCell 6) 0 2 ≤ (40100841483251349112617 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_0) (by simpa only [blockSum_one] using cell_6_1) (by norm_num)

theorem sum_6_2_2 : blockSum (rowCell 6) 2 2 ≤ (57592451075910609246597 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_2) (by simpa only [blockSum_one] using cell_6_3) (by norm_num)

theorem sum_6_0_4 : blockSum (rowCell 6) 0 4 ≤ (48846646279580979179607 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_0_2 sum_6_2_2 (by norm_num)

theorem sum_6_4_2 : blockSum (rowCell 6) 4 2 ≤ (203787063279849082222033 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_4) (by simpa only [blockSum_one] using cell_6_5) (by norm_num)

theorem sum_6_6_2 : blockSum (rowCell 6) 6 2 ≤ (568782678260371086536011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_6) (by simpa only [blockSum_one] using cell_6_7) (by norm_num)

theorem sum_6_4_4 : blockSum (rowCell 6) 4 4 ≤ (976356804820069250980077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_4_2 sum_6_6_2 (by norm_num)

theorem sum_6_0_8 : blockSum (rowCell 6) 0 8 ≤ (1464823267615879042776147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_0_4 sum_6_4_4 (by norm_num)

theorem sum_6_8_2 : blockSum (rowCell 6) 8 2 ≤ (782988623455924175625971 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_8) (by simpa only [blockSum_one] using cell_6_9) (by norm_num)

theorem sum_6_10_2 : blockSum (rowCell 6) 10 2 ≤ (132964549959943937308547 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_10) (by simpa only [blockSum_one] using cell_6_11) (by norm_num)

theorem sum_6_8_4 : blockSum (rowCell 6) 8 4 ≤ (1846705023135475674094347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_8_2 sum_6_10_2 (by norm_num)

theorem sum_6_12_2 : blockSum (rowCell 6) 12 2 ≤ (178341075031761796983471 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_12) (by simpa only [blockSum_one] using cell_6_13) (by norm_num)

theorem sum_6_14_2 : blockSum (rowCell 6) 14 2 ≤ (378014125889809326515827 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_14) (by simpa only [blockSum_one] using cell_6_15) (by norm_num)

theorem sum_6_12_4 : blockSum (rowCell 6) 12 4 ≤ (3316799229703141008446903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_12_2 sum_6_14_2 (by norm_num)

theorem sum_6_8_8 : blockSum (rowCell 6) 8 8 ≤ (4130803402270893346033 / 800000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_8_4 sum_6_12_4 (by norm_num)

theorem sum_6_0_16 : blockSum (rowCell 6) 0 16 ≤ (6628327520454495725317397 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_0_8 sum_6_8_8 (by norm_num)

theorem sum_6_16_2 : blockSum (rowCell 6) 16 2 ≤ (1237013829293170550375663 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_16) (by simpa only [blockSum_one] using cell_6_17) (by norm_num)

theorem sum_6_18_2 : blockSum (rowCell 6) 18 2 ≤ (100030552482396349774481 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_18) (by simpa only [blockSum_one] using cell_6_19) (by norm_num)

theorem sum_6_16_4 : blockSum (rowCell 6) 16 4 ≤ (2837502669011512146767359 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_16_2 sum_6_18_2 (by norm_num)

theorem sum_6_20_2 : blockSum (rowCell 6) 20 2 ≤ (4095127546573115524406197 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_20) (by simpa only [blockSum_one] using cell_6_21) (by norm_num)

theorem sum_6_22_2 : blockSum (rowCell 6) 22 2 ≤ (647765417393256067256217 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_22) (by simpa only [blockSum_one] using cell_6_23) (by norm_num)

theorem sum_6_20_4 : blockSum (rowCell 6) 20 4 ≤ (9277250885719164062455933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_20_2 sum_6_22_2 (by norm_num)

theorem sum_6_16_8 : blockSum (rowCell 6) 16 8 ≤ (14952256223742188355990651 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_16_4 sum_6_20_4 (by norm_num)

theorem sum_6_24_2 : blockSum (rowCell 6) 24 2 ≤ (1622133002389304175078369 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_24) (by simpa only [blockSum_one] using cell_6_25) (by norm_num)

theorem sum_6_26_2 : blockSum (rowCell 6) 26 2 ≤ (201029946647316381945687 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_26) (by simpa only [blockSum_one] using cell_6_27) (by norm_num)

theorem sum_6_24_4 : blockSum (rowCell 6) 24 4 ≤ (3632432468862467994535239 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_24_2 sum_6_26_2 (by norm_num)

theorem sum_6_28_2 : blockSum (rowCell 6) 28 2 ≤ (9866484602998490320250313 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_28) (by simpa only [blockSum_one] using cell_6_29) (by norm_num)

theorem sum_6_30_2 : blockSum (rowCell 6) 30 2 ≤ (46833675486923075556823 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_6_30) (by simpa only [blockSum_one] using cell_6_31) (by norm_num)

theorem sum_6_28_4 : blockSum (rowCell 6) 28 4 ≤ (21855905527650797662797001 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_6_28_2 sum_6_30_2 (by norm_num)

theorem sum_6_24_8 : blockSum (rowCell 6) 24 8 ≤ (36385635403100669640937957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_6_24_4 sum_6_28_4 (by norm_num)

theorem sum_6_16_16 : blockSum (rowCell 6) 16 16 ≤ (1604309113338839312404019 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_6_16_8 sum_6_24_8 (by norm_num)

theorem sum_6_0_32 : blockSum (rowCell 6) 0 32 ≤ (11593243829459470744449201 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_6_0_16 sum_6_16_16 (by norm_num)

#print axioms sum_6_0_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
