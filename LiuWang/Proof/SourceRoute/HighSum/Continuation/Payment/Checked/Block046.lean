import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_2_448_0 : expNegUpper (2417997999874358418427 / 23022742834850904000 : ℝ) ≤ (24434675121281 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2271679 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_448_1 : expNegUpper (154932781968909318760901 / 1473455541430457856000 : ℝ) ≤ (27014328038553 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2273859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_448 : rowCell 2 448 ≤ (4197157149847 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24434675121281 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27014328038553 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_448_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_448_1
  · norm_num [gridPoint]

theorem exp_2_449_0 : expNegUpper (29842793987144092751 / 283813597102592000 : ℝ) ≤ (216114617891317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2273859 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_449_1 : expNegUpper (14938830719086128687 / 141906798551296000 : ℝ) ≤ (23891291357419 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2276043 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_449 : rowCell 2 449 ≤ (29696667547033 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (216114617891317 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23891291357419 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_449_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_449_1
  · norm_num [gridPoint]

theorem exp_2_450_0 : expNegUpper (234168960713773713954711 / 2224415561735190784000 : ℝ) ≤ (2986411331569 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2276043 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_450_1 : expNegUpper (468884802672105981343141 / 4448831123470381568000 : ℝ) ≤ (169021947875769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (227823 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_450 : rowCell 2 450 ≤ (13131313664241 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2986411331569 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (169021947875769 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_450_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_450_1
  · norm_num [gridPoint]

theorem exp_2_451_0 : expNegUpper (156796140701159466364063 / 1487699210172839424000 : ℝ) ≤ (169021942920953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (227823 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_451_1 : expNegUpper (7848956400017666377249 / 74384960508641971200 : ℝ) ≤ (149459932528717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114021 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_451 : rowCell 2 451 ≤ (464479689877 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (169021942920953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (149459932528717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_451_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_451_1
  · norm_num [gridPoint]

theorem exp_2_452_0 : expNegUpper (23622258403462900475587 / 223869348793620505600 : ℝ) ≤ (74729964087649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (114021 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_452_1 : expNegUpper (472996213950642172073211 / 4477386975872410112000 : ℝ) ≤ (16519040401119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1141307 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_452 : rowCell 2 452 ≤ (20535418381947 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (74729964087649 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (16519040401119 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_452_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_452_1
  · norm_num [gridPoint]

theorem exp_2_453_0 : expNegUpper (2186673591323617077867 / 20699074467889664000 : ℝ) ≤ (66076159692087 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1141307 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_453_1 : expNegUpper (1094611296113343770477 / 10349537233944832000 : ℝ) ≤ (116840475332821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2284811 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_453 : rowCell 2 453 ≤ (4539194573807 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (66076159692087 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (116840475332821 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_453_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_453_1
  · norm_num [gridPoint]

theorem exp_2_454_0 : expNegUpper (3177182905598118233183 / 30040227876649728000 : ℝ) ≤ (116840471972699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2284811 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_454_1 : expNegUpper (6361768795747276030739 / 60080455753299456000 : ℝ) ≤ (103295278412509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2287011 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_454 : rowCell 2 454 ≤ (16052496696303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (116840471972699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (103295278412509 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_454_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_454_1
  · norm_num [gridPoint]

theorem exp_2_455_0 : expNegUpper (478652977629075143481737 / 4520392041768616448000 : ℝ) ≤ (51647637730389 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2287011 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_455_1 : expNegUpper (59901286930818042069687 / 565049005221077056000 : ℝ) ≤ (45656900190447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457843 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_455 : rowCell 2 455 ≤ (14191068654467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (51647637730389 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45656900190447 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_455_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_455_1
  · norm_num [gridPoint]

theorem exp_2_456_0 : expNegUpper (60091850584704472267383 / 566846592543191104000 : ℝ) ≤ (45656898894039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (457843 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_456_1 : expNegUpper (96258843960405149174459 / 906954548069105766400 : ℝ) ≤ (20179077796549 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1145711 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_456 : rowCell 2 456 ≤ (6272295052353 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (45656898894039 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (20179077796549 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_456_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_456_1
  · norm_num [gridPoint]

theorem exp_2_457_0 : expNegUpper (32188195131849219045233 / 303278418481879756800 : ℝ) ≤ (40358154454397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1145711 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_457_1 : expNegUpper (80564073789971429496481 / 758196046204699392000 : ℝ) ≤ (35671821514319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2293633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_457 : rowCell 2 457 ≤ (11088348311641 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (40358154454397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (35671821514319 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_457_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_457_1
  · norm_num [gridPoint]

theorem exp_2_458_0 : expNegUpper (242458677260860656414547 / 2281801326208309504000 : ℝ) ≤ (71343641028401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2293633 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_458_1 : expNegUpper (485480974252291476606333 / 4563602652416619008000 : ℝ) ≤ (7881856171771 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2295847 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_458 : rowCell 2 458 ≤ (1531321667 / 156250000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (71343641028401 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7881856171771 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_458_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_458_1
  · norm_num [gridPoint]

theorem exp_2_459_0 : expNegUpper (19480723892076940252797 / 183122074636431872000 : ℝ) ≤ (63054847617471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2295847 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_459_1 : expNegUpper (4875838243317530914837 / 45780518659107968000 : ℝ) ≤ (55725129114273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459613 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_459 : rowCell 2 459 ≤ (1732308523933 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (63054847617471 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (55725129114273 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_459_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_459_1
  · norm_num [gridPoint]

theorem exp_2_460_0 : expNegUpper (5822918634650994200953 / 54672903782270592000 : ℝ) ≤ (55725127571559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (459613 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_460_1 : expNegUpper (23318714427169146111431 / 218691615129082368000 : ℝ) ≤ (3077749125279 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1150143 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_460 : rowCell 2 460 ≤ (956805258769 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (55725127571559 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3077749125279 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_460_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_460_1
  · norm_num [gridPoint]

theorem exp_2_461_0 : expNegUpper (491238568540339979238539 / 4607018807816417792000 : ℝ) ≤ (24621992324873 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1150143 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_461_1 : expNegUpper (9836170403220541078089 / 92140376156328355840 : ℝ) ≤ (21756798429461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (230251 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_461 : rowCell 2 461 ≤ (3381983090251 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (24621992324873 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (21756798429461 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_461_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_461_1
  · norm_num [gridPoint]

theorem exp_2_462_0 : expNegUpper (9867166339664631042489 / 92430730724557219840 : ℝ) ≤ (10878398917341 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (230251 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_462_1 : expNegUpper (493930385895516694905961 / 4621536536227860992000 : ℝ) ≤ (2402960309471 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1152369 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_462 : rowCell 2 462 ≤ (5976666885277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10878398917341 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2402960309471 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_462_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_462_1
  · norm_num [gridPoint]

theorem exp_2_463_0 : expNegUpper (165161473543898959422283 / 1545359034315019776000 : ℝ) ≤ (19223681953533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1152369 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_463_1 : expNegUpper (10334554378465825793201 / 96584939644688736000 : ℝ) ≤ (33968637714989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2306969 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_463 : rowCell 2 463 ≤ (1320159974883 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19223681953533 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (33968637714989 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_463_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_463_1
  · norm_num [gridPoint]

theorem exp_2_464_0 : expNegUpper (1244042223695186510987 / 11626601269920032000 : ℝ) ≤ (33968636797963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2306969 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_464_1 : expNegUpper (19927728118635781205463 / 186025620318720512000 : ℝ) ≤ (30009570176623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2309203 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_464 : rowCell 2 464 ≤ (291584270813 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33968636797963 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (30009570176623 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_464_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_464_1
  · norm_num [gridPoint]

theorem exp_2_465_0 : expNegUpper (499755733514703377237367 / 4665226751296721408000 : ℝ) ≤ (30009569371539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2309203 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_465_1 : expNegUpper (250167087143230008911903 / 2332613375648360704000 : ℝ) ≤ (5302023530989 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2311441 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_465 : rowCell 2 465 ≤ (2060733178689 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30009569371539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5302023530989 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_465_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_465_1
  · norm_num [gridPoint]

theorem exp_2_466_0 : expNegUpper (83650160455653640587269 / 779972638821864192000 : ℝ) ≤ (1325505847409 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2311441 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_466_1 : expNegUpper (33498768941359649857627 / 311989055528745676800 : ℝ) ≤ (5854285773233 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2313683 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_466 : rowCell 2 466 ≤ (3640740658721 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1325505847409 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5854285773233 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_466_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_466_1
  · norm_num [gridPoint]

theorem exp_2_467_0 : expNegUpper (14401502489373389999503 / 134127650082040115200 : ℝ) ≤ (4683428494503 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2313683 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_467_1 : expNegUpper (18022689016429905963837 / 167659562602550144000 : ℝ) ≤ (5170906512393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (289491 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_467 : rowCell 2 467 ≤ (643173532483 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4683428494503 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5170906512393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_467_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_467_1
  · norm_num [gridPoint]

theorem exp_2_468_0 : expNegUpper (126552654172370610835851 / 1177280627779344512000 : ℝ) ≤ (10341812752493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (289491 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_468_1 : expNegUpper (506795459297726521921963 / 4709122511117378048000 : ℝ) ≤ (4566990458099 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72443 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_468 : rowCell 2 468 ≤ (2840384744209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10341812752493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4566990458099 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_468_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_468_1
  · norm_num [gridPoint]

theorem exp_2_469_0 : expNegUpper (6778334152140024937801 / 62984001435588096000 : ℝ) ≤ (9133980677199 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (72443 / 31250 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_469_1 : expNegUpper (3393080297505339062647 / 31492000717794048000 : ℝ) ≤ (4033335137853 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2320427 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_469 : rowCell 2 469 ≤ (313571730299 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9133980677199 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4033335137853 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_469_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_469_1
  · norm_num [gridPoint]

theorem exp_2_470_0 : expNegUpper (255272965641732788843341 / 2369250271263295744000 : ℝ) ≤ (8066670065943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2320427 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_470_1 : expNegUpper (511135058436599026141761 / 4738500542526591488000 : ℝ) ≤ (356179925681 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1161341 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_470 : rowCell 2 470 ≤ (1107688032329 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8066670065943 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (356179925681 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_470_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_470_1
  · norm_num [gridPoint]

theorem exp_2_471_0 : expNegUpper (512723236300712212127289 / 4753223815689830912000 : ℝ) ≤ (7123598329527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1161341 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_471_1 : expNegUpper (12832862768061491722129 / 118830595392245772800 : ℝ) ≤ (12580723509347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2324941 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_471 : rowCell 2 471 ≤ (195631604189 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7123598329527 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12580723509347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_471_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_471_1
  · norm_num [gridPoint]

theorem exp_2_472_0 : expNegUpper (4290891553788170169883 / 39733082726323545600 : ℝ) ≤ (12580723186237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2324941 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_472_1 : expNegUpper (171833470491907144785437 / 1589323309052941824000 : ℝ) ≤ (1110843806869 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1163601 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_472 : rowCell 2 472 ≤ (1727434921941 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12580723186237 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1110843806869 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_472_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_472_1
  · norm_num [gridPoint]

theorem exp_2_473_0 : expNegUpper (517097191737408849191759 / 4782738876933575168000 : ℝ) ≤ (5554218892577 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1163601 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_473_1 : expNegUpper (258846385344361484642139 / 2391369438466787584000 : ℝ) ≤ (4903901167699 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2329467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_473 : rowCell 2 473 ≤ (762615510763 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (5554218892577 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4903901167699 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_473_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_473_1
  · norm_num [gridPoint]

theorem exp_2_474_0 : expNegUpper (59347869959032702317 / 548289218858752000 : ℝ) ≤ (9807802086601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2329467 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_474_1 : expNegUpper (118832365338012096091 / 1096578437717504000 : ℝ) ≤ (4329441483947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (291467 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_474 : rowCell 2 474 ≤ (1346607265337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9807802086601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4329441483947 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_474_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_474_1
  · norm_num [gridPoint]

theorem exp_2_475_0 : expNegUpper (173832335886433651786999 / 1604115097133446656000 : ℝ) ≤ (4329441374797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (291467 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_475_1 : expNegUpper (43508075371941661202243 / 401028774283361664000 : ℝ) ≤ (1911012968791 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (291751 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_475 : rowCell 2 475 ≤ (594412320003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4329441374797 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1911012968791 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_475_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_475_1
  · norm_num [gridPoint]

theorem exp_2_476_0 : expNegUpper (130926659570760481545641 / 1206795689023088768000 : ℝ) ≤ (7644051683633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (291751 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_476_1 : expNegUpper (104861739801910531619943 / 965436551218471014400 : ℝ) ≤ (3373860388783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2336283 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_476 : rowCell 2 476 ≤ (1049460977979 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7644051683633 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3373860388783 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_476_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_476_1
  · norm_num [gridPoint]

theorem exp_2_477_0 : expNegUpper (105184552801019540893503 / 968408611818025062400 : ℝ) ≤ (674772060953 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (2336283 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_477_1 : expNegUpper (263263495992449869072793 / 2421021529545062656000 : ℝ) ≤ (1489026547991 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1169281 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_477 : rowCell 2 477 ≤ (23159361599 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (674772060953 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1489026547991 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_477_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_477_1
  · norm_num [gridPoint]

theorem exp_2_478_0 : expNegUpper (88024232469634489490819 / 809487700065608448000 : ℝ) ≤ (119122120891 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1169281 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_478_1 : expNegUpper (176250597793893273764531 / 1618975400131216896000 : ℝ) ≤ (2628510685391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (585211 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_478 : rowCell 2 478 ≤ (817671325421 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (119122120891 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2628510685391 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_478_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_478_1
  · norm_num [gridPoint]

theorem exp_2_479_0 : expNegUpper (21214981628540330813753 / 194873287200117248000 : ℝ) ≤ (1051404248293 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (585211 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_2_479_1 : expNegUpper (663728891490289442841 / 6089790225003664000 : ℝ) ≤ (579961514807 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (234313 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_2_479 : rowCell 2 479 ≤ (90209653723 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1051404248293 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (579961514807 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_479_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_2_479_1
  · norm_num [gridPoint]

theorem sum_2_448_2 : blockSum (rowCell 2) 448 2 ≤ (63273924745809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_448) (by simpa only [blockSum_one] using cell_2_449) (by norm_num)

theorem sum_2_450_2 : blockSum (rowCell 2) 450 2 ≤ (12371652955583 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_450) (by simpa only [blockSum_one] using cell_2_451) (by norm_num)

theorem sum_2_448_4 : blockSum (rowCell 2) 448 4 ≤ (112760536568141 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_448_2 sum_2_450_2 (by norm_num)

theorem sum_2_452_2 : blockSum (rowCell 2) 452 2 ≤ (1547687867087 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_452) (by simpa only [blockSum_one] using cell_2_453) (by norm_num)

theorem sum_2_454_2 : blockSum (rowCell 2) 454 2 ≤ (3024356535077 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_454) (by simpa only [blockSum_one] using cell_2_455) (by norm_num)

theorem sum_2_452_4 : blockSum (rowCell 2) 452 4 ≤ (13787152405589 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_452_2 sum_2_454_2 (by norm_num)

theorem sum_2_448_8 : blockSum (rowCell 2) 448 8 ≤ (90848149298043 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_448_4 sum_2_452_4 (by norm_num)

theorem sum_2_456_2 : blockSum (rowCell 2) 456 2 ≤ (23632938416347 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_456) (by simpa only [blockSum_one] using cell_2_457) (by norm_num)

theorem sum_2_458_2 : blockSum (rowCell 2) 458 2 ≤ (3692400257693 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_458) (by simpa only [blockSum_one] using cell_2_459) (by norm_num)

theorem sum_2_456_4 : blockSum (rowCell 2) 456 4 ≤ (10523734926203 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_456_2 sum_2_458_2 (by norm_num)

theorem sum_2_460_2 : blockSum (rowCell 2) 460 2 ≤ (7209204125327 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_460) (by simpa only [blockSum_one] using cell_2_461) (by norm_num)

theorem sum_2_462_2 : blockSum (rowCell 2) 462 2 ≤ (11257306784809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_462) (by simpa only [blockSum_one] using cell_2_463) (by norm_num)

theorem sum_2_460_4 : blockSum (rowCell 2) 460 4 ≤ (25675715035463 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_460_2 sum_2_462_2 (by norm_num)

theorem sum_2_456_8 : blockSum (rowCell 2) 456 8 ≤ (2710826189611 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_456_4 sum_2_460_4 (by norm_num)

theorem sum_2_448_16 : blockSum (rowCell 2) 448 16 ≤ (249466953336361 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_448_8 sum_2_456_8 (by norm_num)

theorem sum_2_464_2 : blockSum (rowCell 2) 464 2 ≤ (4393407345193 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_464) (by simpa only [blockSum_one] using cell_2_465) (by norm_num)

theorem sum_2_466_2 : blockSum (rowCell 2) 466 2 ≤ (428538020071 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_466) (by simpa only [blockSum_one] using cell_2_467) (by norm_num)

theorem sum_2_464_4 : blockSum (rowCell 2) 464 4 ≤ (7821711505761 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_464_2 sum_2_466_2 (by norm_num)

theorem sum_2_468_2 : blockSum (rowCell 2) 468 2 ≤ (5348958586601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_468) (by simpa only [blockSum_one] using cell_2_469) (by norm_num)

theorem sum_2_470_2 : blockSum (rowCell 2) 470 2 ≤ (1042923026637 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_470) (by simpa only [blockSum_one] using cell_2_471) (by norm_num)

theorem sum_2_468_4 : blockSum (rowCell 2) 468 4 ≤ (9520650693149 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_468_2 sum_2_470_2 (by norm_num)

theorem sum_2_464_8 : blockSum (rowCell 2) 464 8 ≤ (25164073704671 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_464_4 sum_2_468_4 (by norm_num)

theorem sum_2_472_2 : blockSum (rowCell 2) 472 2 ≤ (3252665943467 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_472) (by simpa only [blockSum_one] using cell_2_473) (by norm_num)

theorem sum_2_474_2 : blockSum (rowCell 2) 474 2 ≤ (2535431905343 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_474) (by simpa only [blockSum_one] using cell_2_475) (by norm_num)

theorem sum_2_472_4 : blockSum (rowCell 2) 472 4 ≤ (578809784881 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_472_2 sum_2_474_2 (by norm_num)

theorem sum_2_476_2 : blockSum (rowCell 2) 476 2 ≤ (1975835441939 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_476) (by simpa only [blockSum_one] using cell_2_477) (by norm_num)

theorem sum_2_478_2 : blockSum (rowCell 2) 478 2 ≤ (307869711041 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_2_478) (by simpa only [blockSum_one] using cell_2_479) (by norm_num)

theorem sum_2_476_4 : blockSum (rowCell 2) 476 4 ≤ (439397999643 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_2_476_2 sum_2_478_2 (by norm_num)

theorem sum_2_472_8 : blockSum (rowCell 2) 472 8 ≤ (4651640922977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_2_472_4 sum_2_476_4 (by norm_num)

theorem sum_2_464_16 : blockSum (rowCell 2) 464 16 ≤ (55147768881 / 1600000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_2_464_8 sum_2_472_8 (by norm_num)

theorem sum_2_448_32 : blockSum (rowCell 2) 448 32 ≤ (141967154443493 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_2_448_16 sum_2_464_16 (by norm_num)

#print axioms sum_2_448_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
