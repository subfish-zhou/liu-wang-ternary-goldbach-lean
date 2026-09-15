import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_1_448_0 : expNegUpper (2394382634148150418427 / 23022742834850904000 : ℝ) ≤ (68152237849601 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (563387 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_448_1 : expNegUpper (153423825807205382760901 / 1473455541430457856000 : ℝ) ≤ (601786288733981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2255739 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_448 : rowCell 1 448 ≤ (46790010493521 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (68152237849601 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (601786288733981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_448_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_448_1
  · norm_num [gridPoint]

theorem exp_1_449_0 : expNegUpper (5910428468420792131 / 56762719420518400 : ℝ) ≤ (601786272141443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2255739 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_449_1 : expNegUpper (2958747582412861347 / 28381359710259200 : ℝ) ≤ (10626851577581 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1128967 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_449 : rowCell 1 449 ≤ (82628773861867 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (601786272141443 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10626851577581 / 20000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_449_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_449_1
  · norm_num [gridPoint]

theorem exp_1_450_0 : expNegUpper (231894603869737617954711 / 2224415561735190784000 : ℝ) ≤ (531342564322531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1128967 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_450_1 : expNegUpper (464343370718353917343141 / 4448831123470381568000 : ℝ) ≤ (93822556906323 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2260133 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_450 : rowCell 1 450 ≤ (72954102885047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (531342564322531 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93822556906323 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_450_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_450_1
  · norm_num [gridPoint]

theorem exp_1_451_0 : expNegUpper (155277475560362026364063 / 1487699210172839424000 : ℝ) ≤ (469112771762023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2260133 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_451_1 : expNegUpper (7773144505216463177249 / 74384960508641971200 : ℝ) ≤ (51767881437913 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1131167 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_451 : rowCell 1 451 ≤ (32203904091331 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (469112771762023 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (51767881437913 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_451_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_451_1
  · norm_num [gridPoint]

theorem exp_1_452_0 : expNegUpper (23394094545627278075587 / 223869348793620505600 : ℝ) ≤ (207071520150963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1131167 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_452_1 : expNegUpper (468440218528249852073211 / 4477386975872410112000 : ℝ) ≤ (73117963627859 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113227 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_452 : rowCell 1 452 ≤ (28429410289387 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (207071520150963 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73117963627859 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_452_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_452_1
  · norm_num [gridPoint]

theorem exp_1_453_0 : expNegUpper (15159277755683623545069 / 144893521275227648000 : ℝ) ≤ (91397452078527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (113227 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_453_1 : expNegUpper (7588677828330302393339 / 72446760637613824000 : ℝ) ≤ (80676780002381 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (566687 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_453 : rowCell 1 453 ≤ (50191230405131 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (91397452078527 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (80676780002381 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_453_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_453_1
  · norm_num [gridPoint]

theorem exp_1_454_0 : expNegUpper (3146663968095766873183 / 30040227876649728000 : ℝ) ≤ (322707111391941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (566687 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_454_1 : expNegUpper (6300828010533508350739 / 60080455753299456000 : ℝ) ≤ (284835348937187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14181 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_454 : rowCell 1 454 ≤ (4430254204613 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (322707111391941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (284835348937187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_454_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_454_1
  · norm_num [gridPoint]

theorem exp_1_455_0 : expNegUpper (474067855269402311481737 / 4520392041768616448000 : ℝ) ≤ (284835341379213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (14181 / 6250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_455_1 : expNegUpper (59329056852648954069687 / 565049005221077056000 : ℝ) ≤ (10055652023977 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (90847 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_455 : rowCell 1 455 ≤ (19551064249603 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (284835341379213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10055652023977 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_455_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_455_1
  · norm_num [gridPoint]

theorem exp_1_456_0 : expNegUpper (59517800072955352267383 / 566846592543191104000 : ℝ) ≤ (62847823492787 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (90847 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_456_1 : expNegUpper (95341819488470582774459 / 906954548069105766400 : ℝ) ≤ (221859363728077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2273393 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_456 : rowCell 1 456 ≤ (17254931572783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (62847823492787 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (221859363728077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_456_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_456_1
  · norm_num [gridPoint]

theorem exp_1_457_0 : expNegUpper (31881549409961679845233 / 303278418481879756800 : ℝ) ≤ (110929678957731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2273393 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_457_1 : expNegUpper (79798673107639269496481 / 758196046204699392000 : ℝ) ≤ (195783720612923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455123 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_457 : rowCell 1 457 ≤ (15227454256247 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (110929678957731 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (195783720612923 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_457_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_457_1
  · norm_num [gridPoint]

theorem exp_1_458_0 : expNegUpper (240155193479544048414547 / 2281801326208309504000 : ℝ) ≤ (195783715515883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (455123 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_458_1 : expNegUpper (480881288423978388606333 / 4563602652416619008000 : ℝ) ≤ (172761443403267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28473 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_458 : rowCell 1 458 ≤ (3359330512897 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (195783715515883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (172761443403267 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_458_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_458_1
  · norm_num [gridPoint]

theorem exp_1_459_0 : expNegUpper (19296153920198806492797 / 183122074636431872000 : ℝ) ≤ (86380719466979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (28473 / 12500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_459_1 : expNegUpper (4829768567691198754837 / 45780518659107968000 : ℝ) ≤ (152436383826799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2280069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_459 : rowCell 1 459 ≤ (11856858702817 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (86380719466979 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (152436383826799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_459_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_459_1
  · norm_num [gridPoint]

theorem exp_1_460_0 : expNegUpper (3105792527432115646667 / 29439255882761088000 : ℝ) ≤ (15243637990813 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2280069 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_460_1 : expNegUpper (12437916760861505752309 / 117757023531044352000 : ℝ) ≤ (134493765585213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (22823 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_460 : rowCell 1 460 ≤ (10461601999089 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15243637990813 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (134493765585213 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_460_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_460_1
  · norm_num [gridPoint]

theorem exp_1_461_0 : expNegUpper (486609755774746379238539 / 4607018807816417792000 : ℝ) ≤ (33623440537383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (22823 / 10000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_461_1 : expNegUpper (9743739782595071638089 / 92140376156328355840 : ℝ) ≤ (118655399010239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (285567 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_461 : rowCell 1 461 ≤ (1845986427047 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33623440537383 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (118655399010239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_461_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_461_1
  · norm_num [gridPoint]

theorem exp_1_462_0 : expNegUpper (9774444449666356482489 / 92430730724557219840 : ℝ) ≤ (59327697999091 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (285567 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_462_1 : expNegUpper (489301573129923094905961 / 4621536536227860992000 : ℝ) ≤ (104675446719733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1143387 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_462 : rowCell 1 462 ≤ (3257097139959 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (59327697999091 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (104675446719733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_462_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_462_1
  · norm_num [gridPoint]

theorem exp_1_463_0 : expNegUpper (163613681465821007422283 / 1545359034315019776000 : ℝ) ≤ (104675444079211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1143387 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_463_1 : expNegUpper (10237969076384289793201 / 96584939644688736000 : ℝ) ≤ (92336677132671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (286127 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_463 : rowCell 1 463 ≤ (14366300881849 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (104675444079211 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (92336677132671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_463_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_463_1
  · norm_num [gridPoint]

theorem exp_1_464_0 : expNegUpper (1232415578773801550987 / 11626601269920032000 : ℝ) ≤ (92336674817981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (286127 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_464_1 : expNegUpper (19741993069266426965463 / 186025620318720512000 : ℝ) ≤ (81447149900929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2291261 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_464 : rowCell 1 464 ≤ (1584059079051 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (92336674817981 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (81447149900929 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_464_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_464_1
  · norm_num [gridPoint]

theorem exp_1_465_0 : expNegUpper (495097793811829265237367 / 4665226751296721408000 : ℝ) ≤ (40723573935987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2291261 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_465_1 : expNegUpper (247841758158953016911903 / 2332613375648360704000 : ℝ) ≤ (71837283698411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (229351 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_465 : rowCell 1 465 ≤ (5588819233297 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (40723573935987 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (71837283698411 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_465_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_465_1
  · norm_num [gridPoint]

theorem exp_1_466_0 : expNegUpper (82872623549454600587269 / 779972638821864192000 : ℝ) ≤ (35918640960007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (229351 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_466_1 : expNegUpper (33188239627834709057627 / 311989055528745676800 : ℝ) ≤ (12671452493279 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2295761 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_466 : rowCell 1 466 ≤ (4929253820253 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (35918640960007 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12671452493279 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_466_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_466_1
  · norm_num [gridPoint]

theorem exp_1_467_0 : expNegUpper (99876016791310856396521 / 938893550574280806400 : ℝ) ≤ (31678630453849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2295761 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_467_1 : expNegUpper (124992517755710781746859 / 1173616938217851008000 : ℝ) ≤ (55874741229631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2298017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_467 : rowCell 1 467 ≤ (2173626179589 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31678630453849 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (55874741229631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_467_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_467_1
  · norm_num [gridPoint]

theorem exp_1_468_0 : expNegUpper (125382707945911986835851 / 1177280627779344512000 : ℝ) ≤ (27937369931783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2298017 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_468_1 : expNegUpper (502122956126212153921963 / 4709122511117378048000 : ℝ) ≤ (49272817043381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (92011 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_468 : rowCell 1 468 ≤ (7667454318163 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27937369931783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (49272817043381 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_468_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_468_1
  · norm_num [gridPoint]

theorem exp_1_469_0 : expNegUpper (6715839930271296617801 / 62984001435588096000 : ℝ) ≤ (9854563169241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (92011 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_469_1 : expNegUpper (3361881731466442422647 / 31492000717794048000 : ℝ) ≤ (43448234571631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2302537 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_469 : rowCell 1 469 ≤ (3380651150269 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9854563169241 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (43448234571631 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_469_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_469_1
  · norm_num [gridPoint]

theorem exp_1_470_0 : expNegUpper (252925791454495412843341 / 2369250271263295744000 : ℝ) ≤ (1086205838063 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2302537 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_470_1 : expNegUpper (506447991796444402141761 / 4738500542526591488000 : ℝ) ≤ (4788724911037 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1152401 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_470 : rowCell 1 470 ≤ (745233650881 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1086205838063 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4788724911037 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_470_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_470_1
  · norm_num [gridPoint]

theorem exp_1_471_0 : expNegUpper (508021606191917332127289 / 4753223815689830912000 : ℝ) ≤ (7661959673797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1152401 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_471_1 : expNegUpper (12715504058699622922129 / 118830595392245772800 : ℝ) ≤ (33776974387169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2307071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_471 : rowCell 1 471 ≤ (5256632234839 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7661959673797 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33776974387169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_471_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_471_1
  · norm_num [gridPoint]

theorem exp_1_472_0 : expNegUpper (4251650621762211769883 / 39733082726323545600 : ℝ) ≤ (844424339541 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2307071 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_472_1 : expNegUpper (170266260455642184785437 / 1589323309052941824000 : ℝ) ≤ (14889320113851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2309343 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_472 : rowCell 1 472 ≤ (185381298389 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (844424339541 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14889320113851 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_472_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_472_1
  · norm_num [gridPoint]

theorem exp_1_473_0 : expNegUpper (39413922935382593322443 / 367902990533351936000 : ℝ) ≤ (2977863952191 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2309343 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_473_1 : expNegUpper (19730148417138767741703 / 183951495266675968000 : ℝ) ≤ (6562999393083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1155809 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_473 : rowCell 1 473 ≤ (2042902198469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2977863952191 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6562999393083 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_473_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_473_1
  · norm_num [gridPoint]

theorem exp_1_474_0 : expNegUpper (411656309463824705019 / 3838024532011264000 : ℝ) ≤ (26251996953959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1155809 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_474_1 : expNegUpper (824280647642188455037 / 7676049064022528000 : ℝ) ≤ (5785399505639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2313897 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_474 : rowCell 1 474 ≤ (1800912661373 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (26251996953959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5785399505639 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_474_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_474_1
  · norm_num [gridPoint]

theorem exp_1_475_0 : expNegUpper (172255416871075187786999 / 1604115097133446656000 : ℝ) ≤ (23141597480803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2313897 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_475_1 : expNegUpper (43114452429295389202243 / 401028774283361664000 : ℝ) ≤ (20398486966731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2316179 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_475 : rowCell 1 475 ≤ (3174982075959 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23141597480803 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20398486966731 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_475_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_475_1
  · norm_num [gridPoint]

theorem exp_1_476_0 : expNegUpper (129742149875661601545641 / 1206795689023088768000 : ℝ) ≤ (20398486492129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2316179 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_476_1 : expNegUpper (103915588392695453219943 / 965436551218471014400 : ℝ) ≤ (17979446040513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (36226 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_476 : rowCell 1 476 ≤ (559710664091 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (20398486492129 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17979446040513 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_476_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_476_1
  · norm_num [gridPoint]

theorem exp_1_477_0 : expNegUpper (104235488698076411293503 / 968408611818025062400 : ℝ) ≤ (17979445624759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (36226 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_477_1 : expNegUpper (260894476602252109072793 / 2421021529545062656000 : ℝ) ≤ (15846323595757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2320753 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_477 : rowCell 1 477 ≤ (24666054819 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17979445624759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15846323595757 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_477_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_477_1
  · norm_num [gridPoint]

theorem exp_1_478_0 : expNegUpper (87232132094795193490819 / 809487700065608448000 : ℝ) ≤ (15846323231573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2320753 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_478_1 : expNegUpper (174668824288988057764531 / 1618975400131216896000 : ℝ) ≤ (1745680374697 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464609 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_478 : rowCell 1 478 ≤ (2173900777439 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (15846323231573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1745680374697 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_478_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_478_1
  · norm_num [gridPoint]

theorem exp_1_479_0 : expNegUpper (21024586269206094653753 / 194873287200117248000 : ℝ) ≤ (6982721339291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (464609 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_1_479_1 : expNegUpper (657788138678994722841 / 6089790225003664000 : ℝ) ≤ (12307079741449 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (116267 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_1_479 : rowCell 1 479 ≤ (1915815939089 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6982721339291 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12307079741449 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_479_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_1_479_1
  · norm_num [gridPoint]

theorem sum_1_448_2 : blockSum (rowCell 1) 448 2 ≤ (176208794848909 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_448) (by simpa only [blockSum_one] using cell_1_449) (by norm_num)

theorem sum_1_450_2 : blockSum (rowCell 1) 450 2 ≤ (137361911067709 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_450) (by simpa only [blockSum_one] using cell_1_451) (by norm_num)

theorem sum_1_448_4 : blockSum (rowCell 1) 448 4 ≤ (156785352958309 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_448_2 sum_1_450_2 (by norm_num)

theorem sum_1_452_2 : blockSum (rowCell 1) 452 2 ≤ (21410010196781 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_452) (by simpa only [blockSum_one] using cell_1_453) (by norm_num)

theorem sum_1_454_2 : blockSum (rowCell 1) 454 2 ≤ (10425583818167 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_454) (by simpa only [blockSum_one] using cell_1_455) (by norm_num)

theorem sum_1_452_4 : blockSum (rowCell 1) 452 4 ≤ (190454721529241 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_452_2 sum_1_454_2 (by norm_num)

theorem sum_1_448_8 : blockSum (rowCell 1) 448 8 ≤ (504025427445859 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_448_4 sum_1_452_4 (by norm_num)

theorem sum_1_456_2 : blockSum (rowCell 1) 456 2 ≤ (3248238582903 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_456) (by simpa only [blockSum_one] using cell_1_457) (by norm_num)

theorem sum_1_458_2 : blockSum (rowCell 1) 458 2 ≤ (5058836150881 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_458) (by simpa only [blockSum_one] using cell_1_459) (by norm_num)

theorem sum_1_456_4 : blockSum (rowCell 1) 456 4 ≤ (11555313316687 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_456_2 sum_1_458_2 (by norm_num)

theorem sum_1_460_2 : blockSum (rowCell 1) 460 2 ≤ (4922883533581 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_460) (by simpa only [blockSum_one] using cell_1_461) (by norm_num)

theorem sum_1_462_2 : blockSum (rowCell 1) 462 2 ≤ (7662946645411 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_462) (by simpa only [blockSum_one] using cell_1_463) (by norm_num)

theorem sum_1_460_4 : blockSum (rowCell 1) 460 4 ≤ (17508713712573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_460_2 sum_1_462_2 (by norm_num)

theorem sum_1_456_8 : blockSum (rowCell 1) 456 8 ≤ (92793994008581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_456_4 sum_1_460_4 (by norm_num)

theorem sum_1_448_16 : blockSum (rowCell 1) 448 16 ≤ (689613415463021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_448_8 sum_1_456_8 (by norm_num)

theorem sum_1_464_2 : blockSum (rowCell 1) 464 2 ≤ (11925055549501 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_464) (by simpa only [blockSum_one] using cell_1_465) (by norm_num)

theorem sum_1_466_2 : blockSum (rowCell 1) 466 2 ≤ (9276506179431 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_466) (by simpa only [blockSum_one] using cell_1_467) (by norm_num)

theorem sum_1_464_4 : blockSum (rowCell 1) 464 4 ≤ (5300390432233 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_464_2 sum_1_466_2 (by norm_num)

theorem sum_1_468_2 : blockSum (rowCell 1) 468 2 ≤ (14428756618701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_468) (by simpa only [blockSum_one] using cell_1_469) (by norm_num)

theorem sum_1_470_2 : blockSum (rowCell 1) 470 2 ≤ (11218501441887 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_470) (by simpa only [blockSum_one] using cell_1_471) (by norm_num)

theorem sum_1_468_4 : blockSum (rowCell 1) 468 4 ≤ (6411814515147 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_468_2 sum_1_470_2 (by norm_num)

theorem sum_1_464_8 : blockSum (rowCell 1) 464 8 ≤ (17012595379613 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_464_4 sum_1_468_4 (by norm_num)

theorem sum_1_472_2 : blockSum (rowCell 1) 472 2 ≤ (8720336856663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_472) (by simpa only [blockSum_one] using cell_1_473) (by norm_num)

theorem sum_1_474_2 : blockSum (rowCell 1) 474 2 ≤ (1355361479741 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_474) (by simpa only [blockSum_one] using cell_1_475) (by norm_num)

theorem sum_1_472_4 : blockSum (rowCell 1) 472 4 ≤ (1937143031921 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_472_2 sum_1_474_2 (by norm_num)

theorem sum_1_476_2 : blockSum (rowCell 1) 476 2 ≤ (1053031760471 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_476) (by simpa only [blockSum_one] using cell_1_477) (by norm_num)

theorem sum_1_478_2 : blockSum (rowCell 1) 478 2 ≤ (255607294783 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_1_478) (by simpa only [blockSum_one] using cell_1_479) (by norm_num)

theorem sum_1_476_4 : blockSum (rowCell 1) 476 4 ≤ (9354875518883 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_1_476_2 sum_1_478_2 (by norm_num)

theorem sum_1_472_8 : blockSum (rowCell 1) 472 8 ≤ (24852019774251 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_1_472_4 sum_1_476_4 (by norm_num)

theorem sum_1_464_16 : blockSum (rowCell 1) 464 16 ≤ (92902401292703 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_1_464_8 sum_1_472_8 (by norm_num)

theorem sum_1_448_32 : blockSum (rowCell 1) 448 32 ≤ (195628954188931 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_1_448_16 sum_1_464_16 (by norm_num)

#print axioms sum_1_448_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
