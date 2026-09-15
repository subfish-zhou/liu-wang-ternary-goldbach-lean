import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_0_128_0 : expNegUpper (565018046443961108563 / 8145908344958596000 : ℝ) ≤ (753039035190028880906481268223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (214907 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_128_1 : expNegUpper (72386994913492086726543 / 1042676268154700288000 : ℝ) ≤ (707742002383657958101898080271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (172009 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_128 : rowCell 0 128 ≤ (26630366420084172352440110921 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (753039035190028880906481268223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (707742002383657958101898080271 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_128_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_128_1
  · norm_num [gridPoint]

theorem exp_0_129_0 : expNegUpper (2914675816300070173983 / 41983553629987328000 : ℝ) ≤ (707741679737762284679243725921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (172009 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_129_1 : expNegUpper (1458651770363502007391 / 20991776814993664000 : ℝ) ≤ (332401179482603858942091756109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1720931 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_129 : rowCell 0 129 ≤ (20017428889451068957307358457 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (707741679737762284679243725921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (332401179482603858942091756109 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_129_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_129_1
  · norm_num [gridPoint]

theorem exp_0_130_0 : expNegUpper (4078583812610048848959 / 58695791758356736000 : ℝ) ≤ (332401029933522233000307136517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1720931 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_130_1 : expNegUpper (8164579245604672822269 / 117391583516713472000 : ℝ) ≤ (312063373101384602023362910587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (86089 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_130 : rowCell 0 130 ≤ (93989846560585016168071222827 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (332401029933522233000307136517 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (312063373101384602023362910587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_130_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_130_1
  · norm_num [gridPoint]

theorem exp_0_131_0 : expNegUpper (73965159595603043420189 / 1063482500856914432000 : ℝ) ≤ (624126469073213104389887501489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (86089 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_131_1 : expNegUpper (3701643949131579927411 / 53174125042845721600 : ℝ) ≤ (146405716865827307981323207567 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1722637 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_131 : rowCell 0 131 ≤ (44108004252206376647944741481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (624126469073213104389887501489 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (146405716865827307981323207567 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_131_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_131_1
  · norm_num [gridPoint]

theorem exp_0_132_0 : expNegUpper (3725942915285344674771 / 53523179418458137600 : ℝ) ≤ (585622610816629015518212109799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1722637 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_132_1 : expNegUpper (74587595827082376542011 / 1070463588369162752000 : ℝ) ≤ (13730000632449998449144723647 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1723501 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_132 : rowCell 0 132 ≤ (82752286192690877525003752763 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (585622610816629015518212109799 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13730000632449998449144723647 / 25000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_132_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_132_1
  · norm_num [gridPoint]

theorem exp_0_133_0 : expNegUpper (8341734972181230692891 / 119718612687462912000 : ℝ) ≤ (274599893868720843692525108433 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1723501 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_133_1 : expNegUpper (4174742985340724228381 / 59859306343731456000 : ℝ) ≤ (514769288419424408926235041337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724373 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_133 : rowCell 0 133 ≤ (77585580943075535427402325699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (274599893868720843692525108433 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (514769288419424408926235041337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_133_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_133_1
  · norm_num [gridPoint]

theorem exp_0_134_0 : expNegUpper (1512708778394284767421 / 21689885566218496000 : ℝ) ≤ (514769068632904330159874536957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1724373 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_134_1 : expNegUpper (3028248908084888959353 / 43379771132436992000 : ℝ) ≤ (120560909395418376611505827293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1725253 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_134 : rowCell 0 134 ≤ (9087882786346281938134643319 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (514769068632904330159874536957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (120560909395418376611505827293 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_134_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_134_1
  · norm_num [gridPoint]

theorem exp_0_135_0 : expNegUpper (76198340808295026629577 / 1091543880740438528000 : ℝ) ≤ (482243434337587382096323227881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1725253 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_135_1 : expNegUpper (9533769089673573361247 / 136442985092554816000 : ℝ) ≤ (45153809151782562608406637449 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (86307 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_135 : rowCell 0 135 ≤ (34046093904858176139569273437 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (482243434337587382096323227881 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45153809151782562608406637449 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_135_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_135_1
  · norm_num [gridPoint]

theorem exp_0_136_0 : expNegUpper (1066171255662667885287 / 15258560020495936000 : ℝ) ≤ (451537903660980907095268652309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (86307 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_136_1 : expNegUpper (68299710021574019163 / 976547841311739904 : ℝ) ≤ (422569814094625741336598451539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (863517 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_136 : rowCell 0 136 ≤ (63740720109891507856499949719 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (451537903660980907095268652309 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (422569814094625741336598451539 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_136_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_136_1
  · norm_num [gridPoint]

theorem exp_0_137_0 : expNegUpper (618667341682432547467 / 8845692804133851136 : ℝ) ≤ (422569640542301033136479291953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (863517 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_137_1 : expNegUpper (38703647932553712359043 / 552855800258365696000 : ℝ) ≤ (98814550960385280194886326393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (26999 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_137 : rowCell 0 137 ≤ (2981837058983685423587083629 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (422569640542301033136479291953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (98814550960385280194886326393 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_137_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_137_1
  · norm_num [gridPoint]

theorem exp_0_138_0 : expNegUpper (38952806354204807718387 / 556414858931755264000 : ℝ) ≤ (395258043579676717387491693869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (26999 / 15625 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_138_1 : expNegUpper (77980528982237193098173 / 1112829717863510528000 : ℝ) ≤ (73904993400319141004709555791 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (345769 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_138 : rowCell 0 138 ≤ (55768664241322454154155008277 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (395258043579676717387491693869 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (73904993400319141004709555791 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_138_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_138_1
  · norm_num [gridPoint]

theorem exp_0_139_0 : expNegUpper (348804112863855002133 / 4977647437849088000 : ℝ) ≤ (36952481908111781766067173887 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (345769 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_139_1 : expNegUpper (87285425686665248253 / 1244411859462272000 : ℝ) ≤ (34529417523526992457304903697 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1729761 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_139 : rowCell 0 139 ≤ (52125243285741200293295082083 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (36952481908111781766067173887 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (34529417523526992457304903697 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_139_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_139_1
  · norm_num [gridPoint]

theorem exp_0_140_0 : expNegUpper (19764841440128998822973 / 281783616868583552000 : ℝ) ≤ (172647019384275167845881190357 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1729761 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_140_1 : expNegUpper (79136368264730662435731 / 1127134467474334208000 : ℝ) ≤ (322492309087060233019949968491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (346137 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_140 : rowCell 0 140 ≤ (24347790224964012097789195717 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (172647019384275167845881190357 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (322492309087060233019949968491 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_140_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_140_1
  · norm_num [gridPoint]

theorem exp_0_141_0 : expNegUpper (79640943799194121601739 / 1134321099738378752000 : ℝ) ≤ (322492183244512278311941813903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (346137 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_141_1 : expNegUpper (7971899441477165685133 / 113432109973837875200 : ℝ) ≤ (301048288297748303645106765231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (346323 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_141 : rowCell 0 141 ≤ (45469131397004042886049584427 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (322492183244512278311941813903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (301048288297748303645106765231 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_141_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_141_1
  · norm_num [gridPoint]

theorem exp_0_142_0 : expNegUpper (891396327808226679317 / 12683673003424204800 : ℝ) ≤ (18815510769034958699293987551 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (346323 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_142_1 : expNegUpper (8922752395606705933729 / 126836730034242048000 : ℝ) ≤ (280893490014719945248615641699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1732553 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_142 : rowCell 0 142 ≤ (42435708854534085398651445403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (18815510769034958699293987551 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (280893490014719945248615641699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_142_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_142_1
  · norm_num [gridPoint]

theorem exp_0_143_0 : expNegUpper (2606888802048176794559 / 37056867070443008000 : ℝ) ≤ (140446691573859895056864756647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1732553 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_143_1 : expNegUpper (163092156641402013753 / 2316054191902688000 : ℝ) ≤ (261961755918443780473709194889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (866749 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_143 : rowCell 0 143 ≤ (39585484462118652323568980253 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (140446691573859895056864756647 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (261961755918443780473709194889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_143_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_143_1
  · norm_num [gridPoint]

theorem exp_0_144_0 : expNegUpper (203511509684480017023 / 2890045065912608000 : ℝ) ≤ (261961657503108032351335410679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (866749 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_144_1 : expNegUpper (3259432752325417593367 / 46240721054601728000 : ℝ) ≤ (12209469462303661027874299899 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1734449 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_144 : rowCell 0 144 ≤ (36908989074031360679643167389 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (261961657503108032351335410679 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (12209469462303661027874299899 / 50000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_144_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_144_1
  · norm_num [gridPoint]

theorem exp_0_145_0 : expNegUpper (9110981391774958489023 / 129255112428012032000 : ℝ) ≤ (30523662331707477355194705481 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1734449 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_145_1 : expNegUpper (4560061605266617953927 / 64627556214006016000 : ℝ) ≤ (227515142653633561292161087221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108463 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_145 : rowCell 0 145 ≤ (17198555828543410150373491879 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (30523662331707477355194705481 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (227515142653633561292161087221 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_145_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_145_1
  · norm_num [gridPoint]

theorem exp_0_146_0 : expNegUpper (41298124406189993068207 / 585298417822464256000 : ℝ) ≤ (227515059298450514056624413549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108463 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_146_1 : expNegUpper (16535917989293019112017 / 234119367128985702400 : ℝ) ≤ (3310628090889344301942623489 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (868187 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_146 : rowCell 0 146 ≤ (16020548459014494604895063697 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (227515059298450514056624413549 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3310628090889344301942623489 / 15625000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_146_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_146_1
  · norm_num [gridPoint]

theorem exp_0_147_0 : expNegUpper (16639372545069346548777 / 235584099548700774400 : ℝ) ≤ (3310626893026872334436592867 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (868187 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_147_1 : expNegUpper (20820317988868000932859 / 294480124435875968000 : ℝ) ≤ (49307034407129818964079678027 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (868673 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_147 : rowCell 0 147 ≤ (3729067723575265652940542409 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3310626893026872334436592867 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (49307034407129818964079678027 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_147_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_147_1
  · norm_num [gridPoint]

theorem exp_0_148_0 : expNegUpper (2327796784922597582019 / 32924083281884288000 : ℝ) ≤ (197228067150029148434526770809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (868673 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_148_1 : expNegUpper (9320684990462054934867 / 131696333127537152000 : ℝ) ≤ (183504911804801433617466273957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (69533 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_148 : rowCell 0 148 ≤ (13881695445086012886916197581 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (197228067150029148434526770809 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (183504911804801433617466273957 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_148_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_148_1
  · norm_num [gridPoint]

theorem exp_0_149_0 : expNegUpper (135052357440510357587 / 1908218138972672000 : ℝ) ≤ (2867263234989943673962089823 / 15625000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (69533 / 40000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_149_1 : expNegUpper (67595423051890571469 / 954109069486336000 : ℝ) ≤ (170658796672468362533432685903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1739311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_149 : rowCell 0 149 ≤ (25825931093364908671633825661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2867263234989943673962089823 / 15625000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (170658796672468362533432685903 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_149_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_149_1
  · norm_num [gridPoint]

theorem exp_0_150_0 : expNegUpper (42508995073500880545261 / 600014256936880384000 : ℝ) ≤ (170658737181783620255292105579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1739311 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_150_1 : expNegUpper (85105623649924810227841 / 1200028513873760768000 : ℝ) ≤ (15864034986006098082104156557 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108769 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_150 : rowCell 0 150 ≤ (24012785281739822467745030819 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (170658737181783620255292105579 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15864034986006098082104156557 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_150_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_150_1
  · norm_num [gridPoint]

theorem exp_0_151_0 : expNegUpper (9514610498844502497521 / 134160392132817408000 : ℝ) ≤ (79320147618555108071093357451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (108769 / 62500 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_151_1 : expNegUpper (238111692810227580049 / 3354009803320435200 : ℝ) ≤ (29480472115108124777483453849 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1741303 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_151 : rowCell 0 151 ≤ (11158452711028540466723905811 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (79320147618555108071093357451 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29480472115108124777483453849 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_151_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_151_1
  · norm_num [gridPoint]

theorem exp_0_152_0 : expNegUpper (2156206160511347609561 / 30372034570567692800 : ℝ) ≤ (73701155221274210254319006531 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1741303 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_152_1 : expNegUpper (86338046092473216834711 / 1214881382822707712000 : ℝ) ≤ (13689979610736743242173883653 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1742309 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_152 : rowCell 0 152 ≤ (1295722814830857339731699813 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (73701155221274210254319006531 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13689979610736743242173883653 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_152_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_152_1
  · norm_num [gridPoint]

theorem exp_0_153_0 : expNegUpper (86868255931900553533839 / 1222342074755813888000 : ℝ) ≤ (136899750113910033442038156643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1742309 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_153_1 : expNegUpper (43479571842318660504059 / 611171037377906944000 : ℝ) ≤ (127089745143411823170836323591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1743321 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_153 : rowCell 0 153 ≤ (19250351172226055034316357729 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (136899750113910033442038156643 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (127089745143411823170836323591 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_153_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_153_1
  · norm_num [gridPoint]

theorem exp_0_154_0 : expNegUpper (194425628925064703691 / 2732945788877056000 : ℝ) ≤ (63544851482311154645375043283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1743321 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_154_1 : expNegUpper (389260054135612835853 / 5465891577754112000 : ℝ) ≤ (29482839614964688500771886897 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (87217 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_154 : rowCell 0 154 ≤ (893357796759151634629597167 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (63544851482311154645375043283 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29482839614964688500771886897 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_154_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_154_1
  · norm_num [gridPoint]

theorem exp_0_155_0 : expNegUpper (88118087665928240492837 / 1237331973539291648000 : ℝ) ≤ (58965659897366339631200887583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (87217 / 50000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_155_1 : expNegUpper (22052790393109641185049 / 309332993384822912000 : ℝ) ≤ (170915292954944152112306639 / 1562500000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (349073 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_155 : rowCell 0 155 ≤ (1657616769350118179094214291 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (58965659897366339631200887583 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (170915292954944152112306639 / 1562500000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_155_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_155_1
  · norm_num [gridPoint]

theorem exp_0_156_0 : expNegUpper (22186982468296642939641 / 311215295097415808000 : ℝ) ≤ (27346438015240437498377999749 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (349073 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_156_1 : expNegUpper (17768420370550599551399 / 248972236077932646400 : ℝ) ≤ (10141612125225854565929878159 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1746397 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_156 : rowCell 0 156 ≤ (15371861994308078805362337693 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (27346438015240437498377999749 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (10141612125225854565929878159 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_156_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_156_1
  · norm_num [gridPoint]

theorem exp_0_157_0 : expNegUpper (1986245991786505715271 / 27831405012128665600 : ℝ) ≤ (101416088798998876924071687357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1746397 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_157_1 : expNegUpper (4970907945210824102577 / 69578512530321664000 : ℝ) ≤ (93987322045690381213294590717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (436859 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_157 : rowCell 0 157 ≤ (3562248069136667869720526697 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (101416088798998876924071687357 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (93987322045690381213294590717 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_157_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_157_1
  · norm_num [gridPoint]

theorem exp_0_158_0 : expNegUpper (45008758464942721753897 / 629994054503835904000 : ℝ) ≤ (23496823082683755350308033657 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (436859 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_158_1 : expNegUpper (90113895047902719737433 / 1259988109007671808000 : ℝ) ≤ (87066160349379356751954670043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (5464 / 3125 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_158 : rowCell 0 158 ≤ (13202580434645332745192003801 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23496823082683755350308033657 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (87066160349379356751954670043 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_158_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_158_1
  · norm_num [gridPoint]

theorem exp_0_159_0 : expNegUpper (3626291270560131097977 / 50703433231012352000 : ℝ) ≤ (17413226630419914638010597371 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (5464 / 3125 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_0_159_1 : expNegUpper (113443459934269127699 / 1584482288469136000 : ℝ) ≤ (403105746225848703709286847 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1749531 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_0_159 : rowCell 0 159 ≤ (12227907288951657168564138879 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (17413226630419914638010597371 / 200000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (403105746225848703709286847 / 5000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_159_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_0_159_1
  · norm_num [gridPoint]

theorem sum_0_128_2 : blockSum (rowCell 0) 128 2 ≤ (206608610127592034196297235969 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_128) (by simpa only [blockSum_one] using cell_0_129) (by norm_num)

theorem sum_0_130_2 : blockSum (rowCell 0) 130 2 ≤ (182205855064997769463960705789 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_130) (by simpa only [blockSum_one] using cell_0_131) (by norm_num)

theorem sum_0_128_4 : blockSum (rowCell 0) 128 4 ≤ (194407232596294901830128970879 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_128_2 sum_0_130_2 (by norm_num)

theorem sum_0_132_2 : blockSum (rowCell 0) 132 2 ≤ (80168933567883206476203039231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_132) (by simpa only [blockSum_one] using cell_0_133) (by norm_num)

theorem sum_0_134_2 : blockSum (rowCell 0) 134 2 ≤ (70397625050243303892107846713 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_134) (by simpa only [blockSum_one] using cell_0_135) (by norm_num)

theorem sum_0_132_4 : blockSum (rowCell 0) 132 4 ≤ (18820819827265813796038860743 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_132_2 sum_0_134_2 (by norm_num)

theorem sum_0_128_8 : blockSum (rowCell 0) 128 8 ≤ (344973791214421412198439856823 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_128_4 sum_0_132_4 (by norm_num)

theorem sum_0_136_2 : blockSum (rowCell 0) 136 2 ≤ (123377461289565216328241622299 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_136) (by simpa only [blockSum_one] using cell_0_137) (by norm_num)

theorem sum_0_138_2 : blockSum (rowCell 0) 138 2 ≤ (2697347688176591361186252259 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_138) (by simpa only [blockSum_one] using cell_0_139) (by norm_num)

theorem sum_0_136_4 : blockSum (rowCell 0) 136 4 ≤ (231271368816628870775691712659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_136_2 sum_0_138_2 (by norm_num)

theorem sum_0_140_2 : blockSum (rowCell 0) 140 2 ≤ (94164711846932067081627975861 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_140) (by simpa only [blockSum_one] using cell_0_141) (by norm_num)

theorem sum_0_142_2 : blockSum (rowCell 0) 142 2 ≤ (10252649164581592215277553207 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_142) (by simpa only [blockSum_one] using cell_0_143) (by norm_num)

theorem sum_0_140_4 : blockSum (rowCell 0) 140 4 ≤ (176185905163584804803848401517 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_140_2 sum_0_142_2 (by norm_num)

theorem sum_0_136_8 : blockSum (rowCell 0) 136 8 ≤ (1591629976485209670232578571 / 3906250000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_136_4 sum_0_140_4 (by norm_num)

theorem sum_0_128_16 : blockSum (rowCell 0) 128 16 ≤ (548702428204528249988209913911 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_128_8 sum_0_136_8 (by norm_num)

theorem sum_0_144_2 : blockSum (rowCell 0) 144 2 ≤ (71306100731118180980390151147 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_144) (by simpa only [blockSum_one] using cell_0_145) (by norm_num)

theorem sum_0_146_2 : blockSum (rowCell 0) 146 2 ≤ (30936819353315557216657233333 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_146) (by simpa only [blockSum_one] using cell_0_147) (by norm_num)

theorem sum_0_144_4 : blockSum (rowCell 0) 144 4 ≤ (133179739437749295413704617813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_144_2 sum_0_146_2 (by norm_num)

theorem sum_0_148_2 : blockSum (rowCell 0) 148 2 ≤ (53589321983536934445466220823 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_148) (by simpa only [blockSum_one] using cell_0_149) (by norm_num)

theorem sum_0_150_2 : blockSum (rowCell 0) 150 2 ≤ (46329690703796903401192842441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_150) (by simpa only [blockSum_one] using cell_0_151) (by norm_num)

theorem sum_0_148_4 : blockSum (rowCell 0) 148 4 ≤ (3122469146479182432708095727 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_148_2 sum_0_150_2 (by norm_num)

theorem sum_0_144_8 : blockSum (rowCell 0) 144 8 ≤ (233098752125083133260363681077 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_144_4 sum_0_148_4 (by norm_num)

theorem sum_0_152_2 : blockSum (rowCell 0) 152 2 ≤ (39981916209519772470023554737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_152) (by simpa only [blockSum_one] using cell_0_153) (by norm_num)

theorem sum_0_154_2 : blockSum (rowCell 0) 154 2 ≤ (27554658902947371586827269 / 800000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_154) (by simpa only [blockSum_one] using cell_0_155) (by norm_num)

theorem sum_0_152_4 : blockSum (rowCell 0) 152 4 ≤ (74425239838203986953557640987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_152_2 sum_0_154_2 (by norm_num)

theorem sum_0_156_2 : blockSum (rowCell 0) 156 2 ≤ (29620854270854750284244444481 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_156) (by simpa only [blockSum_one] using cell_0_157) (by norm_num)

theorem sum_0_158_2 : blockSum (rowCell 0) 158 2 ≤ (635762193089924747843903567 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_0_158) (by simpa only [blockSum_one] using cell_0_159) (by norm_num)

theorem sum_0_156_4 : blockSum (rowCell 0) 156 4 ≤ (55051341994451740198000587161 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_0_156_2 sum_0_158_2 (by norm_num)

theorem sum_0_152_8 : blockSum (rowCell 0) 152 8 ≤ (32369145458163931787889557037 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_0_152_4 sum_0_156_4 (by norm_num)

theorem sum_0_144_16 : blockSum (rowCell 0) 144 16 ≤ (14503013358309554416476876369 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_0_144_8 sum_0_152_8 (by norm_num)

theorem sum_0_128_32 : blockSum (rowCell 0) 128 32 ≤ (1459980190366795360388341737047 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_0_128_16 sum_0_144_16 (by norm_num)

#print axioms sum_0_128_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
