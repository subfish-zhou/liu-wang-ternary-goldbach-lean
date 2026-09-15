import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Sums
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Pilot

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem exp_3_256_0 : expNegUpper (77889831927544574441 / 917150741966258000 : ℝ) ≤ (131097356652042751963187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1941543 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_256_1 : expNegUpper (3992380606222242456491 / 46958117988672409600 : ℝ) ≤ (29829374708287450739257 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (485743 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_256 : rowCell 3 256 ≤ (18260476244076966082469 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (131097356652042751963187 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (29829374708287450739257 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_256_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_256_1
  · norm_num [gridPoint]

theorem exp_3_257_0 : expNegUpper (36098674805236133400859 / 424590237044379750400 : ℝ) ≤ (119317482246033641998667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (485743 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_257_1 : expNegUpper (90346881513454709831943 / 1061475592610949376000 : ℝ) ≤ (13571263822404613912873 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (388881 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_257 : rowCell 3 257 ≤ (1661776801157790770077 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (119317482246033641998667 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (13571263822404613912873 / 125000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_257_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_257_1
  · norm_num [gridPoint]

theorem exp_3_258_0 : expNegUpper (90766441033724904147447 / 1066404949629647104000 : ℝ) ≤ (10857009562555720621361 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (388881 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_258_1 : expNegUpper (181734708880748651493733 / 2132809899259294208000 : ℝ) ≤ (49383644651515523323397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1945843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_258 : rowCell 3 258 ≤ (1511922838867442717709 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10857009562555720621361 / 100000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (49383644651515523323397 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_258_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_258_1
  · norm_num [gridPoint]

theorem exp_3_259_0 : expNegUpper (811452030565372311613 / 9523073118233088000 : ℝ) ≤ (49383637912424777218587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1945843 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_259_1 : expNegUpper (203088860926508058623 / 2380768279558272000 : ℝ) ≤ (44914174616716693549409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (973643 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_259 : rowCell 3 259 ≤ (2750512484126376079577 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (49383637912424777218587 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (44914174616716693549409 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_259_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_259_1
  · norm_num [gridPoint]

theorem exp_3_260_0 : expNegUpper (45906214611949049796863 / 538148960562837632000 : ℝ) ≤ (898283370877701494049 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (973643 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_260_1 : expNegUpper (183829570878573870193851 / 2152595842251350528000 : ℝ) ≤ (8167926867505248531611 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1948733 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_260 : rowCell 3 260 ≤ (12506488701089579059817 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (898283370877701494049 / 10000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (8167926867505248531611 / 100000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_260_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_260_1
  · norm_num [gridPoint]

theorem exp_3_261_0 : expNegUpper (184677346771550742247539 / 2162523071206011392000 : ℝ) ≤ (3267170309300094240683 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1948733 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_261_1 : expNegUpper (739534028028948602089 / 8650092284824045568 : ℝ) ≤ (37126080823962127075021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (390037 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_261 : rowCell 3 261 ≤ (11370659195855308015419 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (3267170309300094240683 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (37126080823962127075021 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_261_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_261_1
  · norm_num [gridPoint]

theorem exp_3_262_0 : expNegUpper (82548525262582687121 / 965543617096189952 : ℝ) ≤ (74252151791397892830049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (390037 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_262_1 : expNegUpper (20660199245798415608329 / 241385904274047488000 : ℝ) ≤ (67484789315986202470951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (975821 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_262 : rowCell 3 262 ≤ (2583896271833368598687 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (74252151791397892830049 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (67484789315986202470951 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_262_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_262_1
  · norm_num [gridPoint]

theorem exp_3_263_0 : expNegUpper (186795373647915757240649 / 2182446044032598528000 : ℝ) ≤ (33742390219782349271003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (975821 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_263_1 : expNegUpper (23375554935719785847631 / 272805755504074816000 : ℝ) ≤ (15330027101528581168261 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1953103 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_263 : rowCell 3 263 ≤ (9392568217769236662589 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (33742390219782349271003 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (15330027101528581168261 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_263_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_263_1
  · norm_num [gridPoint]

theorem exp_3_264_0 : expNegUpper (939304660926017613159 / 10962208939522624000 : ℝ) ≤ (2452804016560300918441 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1953103 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_264_1 : expNegUpper (7522858232811737446783 / 87697671516180992000 : ℝ) ≤ (27852926998890670850127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1954569 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_264 : rowCell 3 264 ≤ (8533637736213560852659 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2452804016560300918441 / 40000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (27852926998890670850127 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_264_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_264_1
  · norm_num [gridPoint]

theorem exp_3_265_0 : expNegUpper (20992318605001443213863 / 244717818898022912000 : ℝ) ≤ (55705846803380774316837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1954569 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_265_1 : expNegUpper (10507936233784990853867 / 122358909449011456000 : ℝ) ≤ (50594154232028917314387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1956039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_265 : rowCell 3 265 ≤ (1937872894852313741161 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (55705846803380774316837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (50594154232028917314387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_265_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_265_1
  · norm_num [gridPoint]

theorem exp_3_266_0 : expNegUpper (95002594709841401424307 / 1106250895282821376000 : ℝ) ≤ (16190127282255044489 / 320000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1956039 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_266_1 : expNegUpper (38043727728321226222041 / 442500358113128550400 : ℝ) ≤ (45941174647815155378021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (978757 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_266 : rowCell 3 266 ≤ (1759860610179068127863 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (16190127282255044489 / 320000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (45941174647815155378021 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_266_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_266_1
  · norm_num [gridPoint]

theorem exp_3_267_0 : expNegUpper (1232799407106784587951 / 14339135802289254400 : ℝ) ≤ (2297058441075155521743 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (978757 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_267_1 : expNegUpper (1542732460589201371939 / 17923919752861568000 : ℝ) ≤ (1668271600170329352349 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1958993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_267 : rowCell 3 267 ≤ (31956839518937623711 / 5000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (2297058441075155521743 / 50000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1668271600170329352349 / 40000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_267_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_267_1
  · norm_num [gridPoint]

theorem exp_3_268_0 : expNegUpper (5337973152304390569589 / 62018142956938368000 : ℝ) ≤ (41706784762695555875853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1958993 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_268_1 : expNegUpper (21375935734981444347707 / 248072571827753472000 : ℝ) ≤ (1182946299662686147347 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1960477 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_268 : rowCell 3 268 ≤ (725208054878276104331 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (41706784762695555875853 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (1182946299662686147347 / 31250000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_268_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_268_1
  · norm_num [gridPoint]

theorem exp_3_269_0 : expNegUpper (7730183022249631907843 / 89710523274019328000 : ℝ) ≤ (757085537493106493093 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1960477 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_269_1 : expNegUpper (3869448762785217297321 / 44855261637009664000 : ℝ) ≤ (17175029074138965842157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (392393 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_269 : rowCell 3 269 ≤ (1053040996190908043767 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (757085537493106493093 / 20000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (17175029074138965842157 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_269_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_269_1
  · norm_num [gridPoint]

theorem exp_3_270_0 : expNegUpper (97173272156869234717041 / 1126447927778470144000 : ℝ) ≤ (4293756738574940778557 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (392393 / 200000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_270_1 : expNegUpper (194565884678683214059561 / 2252895855556940288000 : ℝ) ≤ (31163398694408747344369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (981729 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_270 : rowCell 3 270 ≤ (4777299823553936324177 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4293756738574940778557 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (31163398694408747344369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_270_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_270_1
  · norm_num [gridPoint]

theorem exp_3_271_0 : expNegUpper (21715883305309969160921 / 251450163063239168000 : ℝ) ≤ (31163394882528731182907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (981729 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_271_1 : expNegUpper (271755237813109296443 / 3143127038290489600 : ℝ) ≤ (7066553894080016290909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491239 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_271 : rowCell 3 271 ≤ (1083415147112475212889 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (31163394882528731182907 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7066553894080016290909 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_271_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_271_1
  · norm_num [gridPoint]

theorem exp_3_272_0 : expNegUpper (2456797523134165043347 / 28415373973588998400 : ℝ) ≤ (1766638259359271559187 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491239 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_272_1 : expNegUpper (196766107771865949733311 / 2273229917887119872000 : ℝ) ≤ (25632836295614966597393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1966457 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_272 : rowCell 3 272 ≤ (3930367037562230308917 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1766638259359271559187 / 62500000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (25632836295614966597393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_272_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_272_1
  · norm_num [gridPoint]

theorem exp_3_273_0 : expNegUpper (197649110614907559221559 / 2283431206510842368000 : ℝ) ≤ (12816416608003896566037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1966457 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_273_1 : expNegUpper (98936452155151814835839 / 1141715603255421184000 : ℝ) ≤ (23239802666660842435093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_273 : rowCell 3 273 ≤ (3563836517572997740661 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (12816416608003896566037 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (23239802666660842435093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_273_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_273_1
  · norm_num [gridPoint]

theorem exp_3_274_0 : expNegUpper (17667456536235683239 / 203880474083584000 : ℝ) ≤ (23239799899424192902367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (491991 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_274_1 : expNegUpper (35374963703660511997 / 407760948167168000 : ℝ) ≤ (5266421502860435019803 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (984737 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_274 : rowCell 3 274 ≤ (3230795838330341876629 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (23239799899424192902367 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5266421502860435019803 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_274_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_274_1
  · norm_num [gridPoint]

theorem exp_3_275_0 : expNegUpper (199873138096303481848397 / 2303902298675552768000 : ℝ) ≤ (526642088134294530519 / 25000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (984737 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_275_1 : expNegUpper (50024979333141211849179 / 575975574668888192000 : ℝ) ≤ (19090917173443196870289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (197099 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_275 : rowCell 3 275 ≤ (1464127700576764271991 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (526642088134294530519 / 25000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (19090917173443196870289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_275_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_275_1
  · norm_num [gridPoint]

theorem exp_3_276_0 : expNegUpper (50247969199550585544891 / 578543025554135168000 : ℝ) ≤ (19090914940400453333003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (197099 / 100000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_276_1 : expNegUpper (40244030760213135728303 / 462834420443308134400 : ℝ) ≤ (4324407555174720975637 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1972509 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_276 : rowCell 3 276 ≤ (2653485405980906846403 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (19090914940400453333003 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4324407555174720975637 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_276_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_276_1
  · norm_num [gridPoint]

theorem exp_3_277_0 : expNegUpper (4491446936237481425807 / 51654772090295193600 : ℝ) ≤ (4324407053828258426017 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1972509 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_277_1 : expNegUpper (11241382790607306691477 / 129136930225737984000 : ℝ) ≤ (7834759394342938111087 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1974033 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_277 : rowCell 3 277 ≤ (2403993978452736917093 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (4324407053828258426017 / 250000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7834759394342938111087 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_277_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_277_1
  · norm_num [gridPoint]

theorem exp_3_278_0 : expNegUpper (101621427043047547261357 / 1167390112107890944000 : ℝ) ≤ (7834758494044183898651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1974033 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_278_1 : expNegUpper (203474136614501019540993 / 2334780224215781888000 : ℝ) ≤ (14191704089100915786369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1975561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_278 : rowCell 3 278 ≤ (2177507069389454096169 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7834758494044183898651 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (14191704089100915786369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_278_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_278_1
  · norm_num [gridPoint]

theorem exp_3_279_0 : expNegUpper (8175004506270651199713 / 93804741706961408000 : ℝ) ≤ (14191702472682850344223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1975561 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_279_1 : expNegUpper (1023039514720564113269 / 11725592713370176000 : ℝ) ≤ (3212653420242504778641 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (988547 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_279 : rowCell 3 279 ≤ (394389997951057307687 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (14191702472682850344223 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3212653420242504778641 / 250000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_279_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_279_1
  · norm_num [gridPoint]

theorem exp_3_280_0 : expNegUpper (2854331914375539823621 / 32714995825528384000 : ℝ) ≤ (6425306115081484982499 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (988547 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_280_1 : expNegUpper (22860688801345064057119 / 261719966604227072000 : ℝ) ≤ (2326774033262770811721 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1978631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_280 : rowCell 3 280 ≤ (55794701691507596639 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6425306115081484982499 / 500000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2326774033262770811721 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_280_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_280_1
  · norm_num [gridPoint]

theorem exp_3_281_0 : expNegUpper (206653219613251503175439 / 2365863694507807232000 : ℝ) ≤ (11633868864391502897663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1978631 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_281_1 : expNegUpper (20688903541081792785087 / 236586369450780723200 : ℝ) ≤ (2106037806795250684021 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (495043 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_281 : rowCell 3 281 ≤ (1616223014969744855473 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (11633868864391502897663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (2106037806795250684021 / 200000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_281_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_281_1
  · norm_num [gridPoint]

theorem exp_3_282_0 : expNegUpper (20779908798374283434607 / 237627052788332595200 : ℝ) ≤ (10530187865874913907987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (495043 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_282_1 : expNegUpper (208036421532588523393261 / 2376270527883325952000 : ℝ) ≤ (595580308279806289223 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (990859 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_282 : rowCell 3 282 ≤ (731377389319203292571 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (10530187865874913907987 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (595580308279806289223 / 62500000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_282_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_282_1
  · norm_num [gridPoint]

theorem exp_3_283_0 : expNegUpper (23216612548761278615741 / 265188911062733312000 : ℝ) ≤ (9529283884633173434011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (990859 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_283_1 : expNegUpper (5810787988048778051953 / 66297227765683328000 : ℝ) ≤ (4310892853057273013229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (495817 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_283 : rowCell 3 283 ≤ (661796151079454570231 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (9529283884633173434011 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (4310892853057273013229 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_283_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_283_1
  · norm_num [gridPoint]

theorem exp_3_284_0 : expNegUpper (2101045044709161694913 / 23971527095516288000 : ℝ) ≤ (1077723095789813528411 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (495817 / 250000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_284_1 : expNegUpper (8413795340586361360443 / 95886108382065152000 : ℝ) ≤ (3899576789128086136899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (992411 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_284 : rowCell 3 284 ≤ (598714788636589827977 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (1077723095789813528411 / 125000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (3899576789128086136899 / 500000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_284_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_284_1
  · norm_num [gridPoint]

theorem exp_3_285_0 : expNegUpper (211264072572275466924027 / 2407628057844412928000 : ℝ) ≤ (7799152735518648820889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (992411 / 500000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_285_1 : expNegUpper (105752989679818121272313 / 1203814028922206464000 : ℝ) ≤ (7053612912021677972759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1986381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_285 : rowCell 3 285 ≤ (541538507650138545903 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (7799152735518648820889 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (7053612912021677972759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_285_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_285_1
  · norm_num [gridPoint]

theorem exp_3_286_0 : expNegUpper (11801568179737113698273 / 134340346913497344000 : ℝ) ≤ (8817015195567843863 / 1250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1986381 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_286_1 : expNegUpper (945207400431227920889 / 10747227753079787520 : ℝ) ≤ (6378084021623687623393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (248493 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_286 : rowCell 3 286 ≤ (97945135284498003301 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (8817015195567843863 / 1250000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (6378084021623687623393 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_286_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_286_1
  · norm_num [gridPoint]

theorem exp_3_287_0 : expNegUpper (8543879138089302206201 / 97145890773889863680 : ℝ) ≤ (6378083344330388477507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (248493 / 125000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem exp_3_287_1 : expNegUpper (6682560959973993740823 / 75895227167101456000 : ℝ) ≤ (5766122547648473221247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  apply upper_of_taylor (t := (1989511 / 1000000 : ℝ)) (by norm_num)
  · norm_num [expTaylor, Finset.sum_range_succ]
  · norm_num

theorem cell_3_287 : rowCell 3 287 ≤ (110695800556634958729 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simp only [rowCell]
  apply upper_cell_of_exp (b₁ := (6378083344330388477507 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ)) (b₂ := (5766122547648473221247 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ))
  · norm_num [gridPoint]
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_287_0
  · norm_num only [gridPoint, tangent, phase, Nat.cast_add, Nat.cast_one]
    exact exp_3_287_1
  · norm_num [gridPoint]

theorem sum_3_256_2 : blockSum (rowCell 3) 256 2 ≤ (34878244255654873783239 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_256) (by simpa only [blockSum_one] using cell_3_257) (by norm_num)

theorem sum_3_258_2 : blockSum (rowCell 3) 258 2 ≤ (1154871632372252302999 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_258) (by simpa only [blockSum_one] using cell_3_259) (by norm_num)

theorem sum_3_256_4 : blockSum (rowCell 3) 256 4 ≤ (31875017532480590679107 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_256_2 sum_3_258_2 (by norm_num)

theorem sum_3_260_2 : blockSum (rowCell 3) 260 2 ≤ (5969286974236221768809 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_260) (by simpa only [blockSum_one] using cell_3_261) (by norm_num)

theorem sum_3_262_2 : blockSum (rowCell 3) 262 2 ≤ (19728153305102711057337 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_262) (by simpa only [blockSum_one] using cell_3_263) (by norm_num)

theorem sum_3_260_4 : blockSum (rowCell 3) 260 4 ≤ (43605301202047598132573 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_260_2 sum_3_262_2 (by norm_num)

theorem sum_3_256_8 : blockSum (rowCell 3) 256 8 ≤ (107355336267008779490787 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_256_4 sum_3_260_4 (by norm_num)

theorem sum_3_264_2 : blockSum (rowCell 3) 264 2 ≤ (16285129315622815817303 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_264) (by simpa only [blockSum_one] using cell_3_265) (by norm_num)

theorem sum_3_266_2 : blockSum (rowCell 3) 266 2 ≤ (3357702586125949313413 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_266) (by simpa only [blockSum_one] using cell_3_267) (by norm_num)

theorem sum_3_264_4 : blockSum (rowCell 3) 264 4 ≤ (5943187932025322614191 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_264_2 sum_3_266_2 (by norm_num)

theorem sum_3_268_2 : blockSum (rowCell 3) 268 2 ≤ (11066869419980749053483 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_268) (by simpa only [blockSum_one] using cell_3_269) (by norm_num)

theorem sum_3_270_2 : blockSum (rowCell 3) 270 2 ≤ (9110960412003837175733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_270) (by simpa only [blockSum_one] using cell_3_271) (by norm_num)

theorem sum_3_268_4 : blockSum (rowCell 3) 268 4 ≤ (630557182249518319663 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_268_2 sum_3_270_2 (by norm_num)

theorem sum_3_264_8 : blockSum (rowCell 3) 264 8 ≤ (49893769492111199300171 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_264_4 sum_3_268_4 (by norm_num)

theorem sum_3_256_16 : blockSum (rowCell 3) 256 16 ≤ (78624552879559989395479 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_256_8 sum_3_264_8 (by norm_num)

theorem sum_3_272_2 : blockSum (rowCell 3) 272 2 ≤ (3747101777567614024789 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_272) (by simpa only [blockSum_one] using cell_3_273) (by norm_num)

theorem sum_3_274_2 : blockSum (rowCell 3) 274 2 ≤ (6159051239483870420611 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_274) (by simpa only [blockSum_one] using cell_3_275) (by norm_num)

theorem sum_3_272_4 : blockSum (rowCell 3) 272 4 ≤ (13653254794619098470189 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_272_2 sum_3_274_2 (by norm_num)

theorem sum_3_276_2 : blockSum (rowCell 3) 276 2 ≤ (632184923054205470437 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_276) (by simpa only [blockSum_one] using cell_3_277) (by norm_num)

theorem sum_3_278_2 : blockSum (rowCell 3) 278 2 ≤ (1037364264786185158651 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_278) (by simpa only [blockSum_one] using cell_3_279) (by norm_num)

theorem sum_3_276_4 : blockSum (rowCell 3) 276 4 ≤ (92069364435783843981 / 10000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_276_2 sum_3_278_2 (by norm_num)

theorem sum_3_272_8 : blockSum (rowCell 3) 272 8 ≤ (22860191238197482868289 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_272_4 sum_3_276_4 (by norm_num)

theorem sum_3_280_2 : blockSum (rowCell 3) 280 2 ≤ (3401653469097987947921 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_280) (by simpa only [blockSum_one] using cell_3_281) (by norm_num)

theorem sum_3_282_2 : blockSum (rowCell 3) 282 2 ≤ (696586770199328931401 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_282) (by simpa only [blockSum_one] using cell_3_283) (by norm_num)

theorem sum_3_280_4 : blockSum (rowCell 3) 280 4 ≤ (247520021995812146941 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_280_2 sum_3_282_2 (by norm_num)

theorem sum_3_284_2 : blockSum (rowCell 3) 284 2 ≤ (28506332407168209347 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_284) (by simpa only [blockSum_one] using cell_3_285) (by norm_num)

theorem sum_3_286_2 : blockSum (rowCell 3) 286 2 ≤ (932508878649029851421 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 1) (n := 1) (by simpa only [blockSum_one] using cell_3_286) (by simpa only [blockSum_one] using cell_3_287) (by norm_num)

theorem sum_3_284_4 : blockSum (rowCell 3) 284 4 ≤ (2072762174935758225301 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 2) (n := 2) sum_3_284_2 sum_3_286_2 (by norm_num)

theorem sum_3_280_8 : blockSum (rowCell 3) 280 8 ≤ (10333524899766820124127 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 4) (n := 4) sum_3_280_4 sum_3_284_4 (by norm_num)

theorem sum_3_272_16 : blockSum (rowCell 3) 272 16 ≤ (1037303629311384468513 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 8) (n := 8) sum_3_272_8 sum_3_280_8 (by norm_num)

theorem sum_3_256_32 : blockSum (rowCell 3) 256 32 ≤ (95221410948542140891687 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 16) (n := 16) sum_3_256_16 sum_3_272_16 (by norm_num)

#print axioms sum_3_256_32

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
