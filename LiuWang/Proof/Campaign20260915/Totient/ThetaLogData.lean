import LiuWang.Proof.Campaign20260915.Totient.PrefixTable

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.Totient

def thetaLogRows : List (ℕ × ℤ) :=
  [(2, 6931471803), (3, 10986122884), (5, 16094379119), (7, 19459101485),
   (11, 23978952720), (13, 25649493566), (17, 28332133430), (19, 29444389781),
   (23, 31354942148), (29, 33672958289), (31, 34339872034), (37, 36109179113),
   (41, 37135720654), (43, 37612001143), (47, 38501476004), (53, 39702919122),
   (59, 40775374426), (61, 41108738628), (67, 42046926178), (71, 42626798754),
   (73, 42904594395), (79, 43694478509), (83, 44188406062), (89, 44886363681),
   (97, 45747109769), (101, 46151205152), (103, 46347289866), (107, 46728288329),
   (109, 46913478806), (113, 47273878171), (127, 48441870848), (131, 48751973213),
   (137, 49199809240), (139, 49344739313), (149, 50039463041), (151, 50172798349),
   (157, 50562458035), (163, 50937501989), (167, 51179938105), (173, 51532915926),
   (179, 51873858040), (181, 51984970294), (191, 52522734262), (193, 52626901870),
   (197, 52832037269), (199, 52933048229), (211, 53518581316), (223, 54071717696),
   (227, 54249500156), (229, 54337220017), (233, 54510384517), (239, 54764635501),
   (241, 54847969316), (251, 55254529373), (257, 55490760828), (263, 55721540300),
   (269, 55947113775), (271, 56021188188), (277, 56240175041), (281, 56383546672),
   (283, 56454468955), (293, 56801726069), (307, 57268477455), (311, 57397929100),
   (313, 57462031884), (317, 57589017717), (331, 58021183732), (337, 58200829282),
   (347, 58493247778), (349, 58550719201), (353, 58664680548), (359, 58833223864),
   (367, 59053618459), (373, 59215784175), (379, 59375362030), (383, 59480349871),
   (389, 59635793415), (397, 59839362786), (401, 59939614252), (409, 60137151539),
   (419, 60378709178), (421, 60426328316), (431, 60661080880), (433, 60707377259),
   (439, 60844994109), (443, 60935697679), (449, 61070228856), (457, 61246833888),
   (461, 61333980409), (463, 61377270520), (467, 61463292555), (479, 61717005953),
   (487, 61882641210), (491, 61964441257), (499, 62126060936), (503, 62205901680),
   (509, 62324480144), (521, 62557500394), (523, 62595814617), (541, 62934192765),
   (547, 63044488000), (557, 63225652375), (563, 63332796258), (569, 63438804317),
   (571, 63473892073), (577, 63578422641), (587, 63750248174), (593, 63851943966),
   (599, 63952615957), (601, 63985949321), (607, 64085287887), (613, 64183649335),
   (617, 64248690215), (619, 64281052703), (631, 64473058602), (641, 64630294545),
   (643, 64661447218), (647, 64723462921), (653, 64815771269), (659, 64907235321),
   (661, 64937538375), (673, 65117453273), (677, 65176712705), (683, 65264948572),
   (691, 65381398214), (701, 65525078846), (709, 65638555241), (719, 65778613553),
   (727, 65889264751), (733, 65971456995), (739, 66052979186), (743, 66106960423),
   (751, 66214056494), (757, 66293632510), (761, 66346333555), (769, 66450909671),
   (773, 66502790462), (787, 66682282460), (797, 66808546764), (809, 66957989147),
   (811, 66982680517), (821, 67105231071), (823, 67129561983), (827, 67178046926),
   (829, 67202201527), (839, 67322107041), (853, 67487595451), (857, 67534379162),
   (859, 67557689196), (863, 67604146887), (877, 67765069900), (881, 67810576235),
   (883, 67833251982), (887, 67878449799), (907, 68101424477), (911, 68145428949),
   (919, 68232861200), (929, 68341087364), (937, 68426832798), (941, 68469431372),
   (947, 68532990908), (953, 68596149013), (967, 68741984931), (971, 68783264659),
   (977, 68844866497), (983, 68906091178), (991, 68987145319), (997, 69047507676),
   (1009, 69167150180), (1013, 69206715019), (1019, 69265770308), (1021, 69285378158),
   (1031, 69382844814), (1033, 69402224665), (1039, 69460139884), (1049, 69555926057),
   (1051, 69574973682), (1061, 69669671360), (1063, 69688503757), (1069, 69744789084),
   (1087, 69911768845), (1091, 69948499832), (1093, 69966814855), (1097, 70003344576),
   (1103, 70057890166), (1109, 70112139847), (1117, 70184017964), (1123, 70237589521),
   (1129, 70290875615), (1151, 70483864061), (1153, 70501225176), (1163, 70587581499),
   (1171, 70656133609), (1181, 70741168135), (1187, 70791843920), (1193, 70842264194),
   (1201, 70909098194), (1213, 71008519063), (1217, 71041440903), (1223, 71090621330),
   (1229, 71139561069), (1231, 71155821235), (1237, 71204443697), (1249, 71300985075),
   (1259, 71380730314), (1277, 71522688534), (1279, 71538337989), (1283, 71569563620),
   (1289, 71616220003), (1291, 71631723882), (1297, 71678091817), (1301, 71708884759),
   (1303, 71724245745), (1307, 71754897110), (1319, 71846291501), (1321, 71861443019),
   (1327, 71906760317), (1361, 72159750000), (1367, 72203738341), (1373, 72247534031),
   (1381, 72305631508), (1399, 72435129720), (1409, 72506355092)]

private theorem theta_log_row_0 :
    Nat.Prime 2 ∧ (6931471803 : ℤ) = ⌊logCenter (2 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (2 : ℚ) = 1 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_1 :
    Nat.Prime 3 ∧ (10986122884 : ℤ) = ⌊logCenter (3 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (3 : ℚ) = 1 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_2 :
    Nat.Prime 5 ∧ (16094379119 : ℤ) = ⌊logCenter (5 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (5 : ℚ) = 2 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_3 :
    Nat.Prime 7 ∧ (19459101485 : ℤ) = ⌊logCenter (7 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (7 : ℚ) = 2 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_4 :
    Nat.Prime 11 ∧ (23978952720 : ℤ) = ⌊logCenter (11 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (11 : ℚ) = 3 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_5 :
    Nat.Prime 13 ∧ (25649493566 : ℤ) = ⌊logCenter (13 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (13 : ℚ) = 3 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_6 :
    Nat.Prime 17 ∧ (28332133430 : ℤ) = ⌊logCenter (17 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (17 : ℚ) = 4 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_7 :
    Nat.Prime 19 ∧ (29444389781 : ℤ) = ⌊logCenter (19 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (19 : ℚ) = 4 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_8 :
    Nat.Prime 23 ∧ (31354942148 : ℤ) = ⌊logCenter (23 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (23 : ℚ) = 4 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_9 :
    Nat.Prime 29 ∧ (33672958289 : ℤ) = ⌊logCenter (29 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (29 : ℚ) = 4 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_10 :
    Nat.Prime 31 ∧ (34339872034 : ℤ) = ⌊logCenter (31 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (31 : ℚ) = 4 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_11 :
    Nat.Prime 37 ∧ (36109179113 : ℤ) = ⌊logCenter (37 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (37 : ℚ) = 5 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_12 :
    Nat.Prime 41 ∧ (37135720654 : ℤ) = ⌊logCenter (41 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (41 : ℚ) = 5 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_13 :
    Nat.Prime 43 ∧ (37612001143 : ℤ) = ⌊logCenter (43 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (43 : ℚ) = 5 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_14 :
    Nat.Prime 47 ∧ (38501476004 : ℤ) = ⌊logCenter (47 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (47 : ℚ) = 5 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_15 :
    Nat.Prime 53 ∧ (39702919122 : ℤ) = ⌊logCenter (53 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (53 : ℚ) = 5 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_16 :
    Nat.Prime 59 ∧ (40775374426 : ℤ) = ⌊logCenter (59 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (59 : ℚ) = 5 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_17 :
    Nat.Prime 61 ∧ (41108738628 : ℤ) = ⌊logCenter (61 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (61 : ℚ) = 5 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_18 :
    Nat.Prime 67 ∧ (42046926178 : ℤ) = ⌊logCenter (67 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (67 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_19 :
    Nat.Prime 71 ∧ (42626798754 : ℤ) = ⌊logCenter (71 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (71 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_20 :
    Nat.Prime 73 ∧ (42904594395 : ℤ) = ⌊logCenter (73 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (73 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_21 :
    Nat.Prime 79 ∧ (43694478509 : ℤ) = ⌊logCenter (79 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (79 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_22 :
    Nat.Prime 83 ∧ (44188406062 : ℤ) = ⌊logCenter (83 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (83 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_23 :
    Nat.Prime 89 ∧ (44886363681 : ℤ) = ⌊logCenter (89 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (89 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_24 :
    Nat.Prime 97 ∧ (45747109769 : ℤ) = ⌊logCenter (97 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (97 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_25 :
    Nat.Prime 101 ∧ (46151205152 : ℤ) = ⌊logCenter (101 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (101 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_26 :
    Nat.Prime 103 ∧ (46347289866 : ℤ) = ⌊logCenter (103 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (103 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_27 :
    Nat.Prime 107 ∧ (46728288329 : ℤ) = ⌊logCenter (107 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (107 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_28 :
    Nat.Prime 109 ∧ (46913478806 : ℤ) = ⌊logCenter (109 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (109 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_29 :
    Nat.Prime 113 ∧ (47273878171 : ℤ) = ⌊logCenter (113 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (113 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_30 :
    Nat.Prime 127 ∧ (48441870848 : ℤ) = ⌊logCenter (127 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (127 : ℚ) = 6 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_31 :
    Nat.Prime 131 ∧ (48751973213 : ℤ) = ⌊logCenter (131 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (131 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_32 :
    Nat.Prime 137 ∧ (49199809240 : ℤ) = ⌊logCenter (137 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (137 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_33 :
    Nat.Prime 139 ∧ (49344739313 : ℤ) = ⌊logCenter (139 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (139 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_34 :
    Nat.Prime 149 ∧ (50039463041 : ℤ) = ⌊logCenter (149 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (149 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_35 :
    Nat.Prime 151 ∧ (50172798349 : ℤ) = ⌊logCenter (151 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (151 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_36 :
    Nat.Prime 157 ∧ (50562458035 : ℤ) = ⌊logCenter (157 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (157 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_37 :
    Nat.Prime 163 ∧ (50937501989 : ℤ) = ⌊logCenter (163 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (163 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_38 :
    Nat.Prime 167 ∧ (51179938105 : ℤ) = ⌊logCenter (167 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (167 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_39 :
    Nat.Prime 173 ∧ (51532915926 : ℤ) = ⌊logCenter (173 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (173 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_40 :
    Nat.Prime 179 ∧ (51873858040 : ℤ) = ⌊logCenter (179 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (179 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_41 :
    Nat.Prime 181 ∧ (51984970294 : ℤ) = ⌊logCenter (181 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (181 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_42 :
    Nat.Prime 191 ∧ (52522734262 : ℤ) = ⌊logCenter (191 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (191 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_43 :
    Nat.Prime 193 ∧ (52626901870 : ℤ) = ⌊logCenter (193 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (193 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_44 :
    Nat.Prime 197 ∧ (52832037269 : ℤ) = ⌊logCenter (197 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (197 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_45 :
    Nat.Prime 199 ∧ (52933048229 : ℤ) = ⌊logCenter (199 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (199 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_46 :
    Nat.Prime 211 ∧ (53518581316 : ℤ) = ⌊logCenter (211 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (211 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_47 :
    Nat.Prime 223 ∧ (54071717696 : ℤ) = ⌊logCenter (223 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (223 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_48 :
    Nat.Prime 227 ∧ (54249500156 : ℤ) = ⌊logCenter (227 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (227 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_49 :
    Nat.Prime 229 ∧ (54337220017 : ℤ) = ⌊logCenter (229 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (229 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_50 :
    Nat.Prime 233 ∧ (54510384517 : ℤ) = ⌊logCenter (233 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (233 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_51 :
    Nat.Prime 239 ∧ (54764635501 : ℤ) = ⌊logCenter (239 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (239 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_52 :
    Nat.Prime 241 ∧ (54847969316 : ℤ) = ⌊logCenter (241 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (241 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_53 :
    Nat.Prime 251 ∧ (55254529373 : ℤ) = ⌊logCenter (251 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (251 : ℚ) = 7 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_54 :
    Nat.Prime 257 ∧ (55490760828 : ℤ) = ⌊logCenter (257 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (257 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_55 :
    Nat.Prime 263 ∧ (55721540300 : ℤ) = ⌊logCenter (263 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (263 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_56 :
    Nat.Prime 269 ∧ (55947113775 : ℤ) = ⌊logCenter (269 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (269 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_57 :
    Nat.Prime 271 ∧ (56021188188 : ℤ) = ⌊logCenter (271 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (271 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_58 :
    Nat.Prime 277 ∧ (56240175041 : ℤ) = ⌊logCenter (277 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (277 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_59 :
    Nat.Prime 281 ∧ (56383546672 : ℤ) = ⌊logCenter (281 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (281 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_60 :
    Nat.Prime 283 ∧ (56454468955 : ℤ) = ⌊logCenter (283 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (283 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_61 :
    Nat.Prime 293 ∧ (56801726069 : ℤ) = ⌊logCenter (293 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (293 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_62 :
    Nat.Prime 307 ∧ (57268477455 : ℤ) = ⌊logCenter (307 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (307 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_63 :
    Nat.Prime 311 ∧ (57397929100 : ℤ) = ⌊logCenter (311 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (311 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_64 :
    Nat.Prime 313 ∧ (57462031884 : ℤ) = ⌊logCenter (313 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (313 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_65 :
    Nat.Prime 317 ∧ (57589017717 : ℤ) = ⌊logCenter (317 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (317 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_66 :
    Nat.Prime 331 ∧ (58021183732 : ℤ) = ⌊logCenter (331 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (331 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_67 :
    Nat.Prime 337 ∧ (58200829282 : ℤ) = ⌊logCenter (337 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (337 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_68 :
    Nat.Prime 347 ∧ (58493247778 : ℤ) = ⌊logCenter (347 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (347 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_69 :
    Nat.Prime 349 ∧ (58550719201 : ℤ) = ⌊logCenter (349 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (349 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_70 :
    Nat.Prime 353 ∧ (58664680548 : ℤ) = ⌊logCenter (353 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (353 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_71 :
    Nat.Prime 359 ∧ (58833223864 : ℤ) = ⌊logCenter (359 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (359 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_72 :
    Nat.Prime 367 ∧ (59053618459 : ℤ) = ⌊logCenter (367 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (367 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_73 :
    Nat.Prime 373 ∧ (59215784175 : ℤ) = ⌊logCenter (373 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (373 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_74 :
    Nat.Prime 379 ∧ (59375362030 : ℤ) = ⌊logCenter (379 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (379 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_75 :
    Nat.Prime 383 ∧ (59480349871 : ℤ) = ⌊logCenter (383 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (383 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_76 :
    Nat.Prime 389 ∧ (59635793415 : ℤ) = ⌊logCenter (389 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (389 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_77 :
    Nat.Prime 397 ∧ (59839362786 : ℤ) = ⌊logCenter (397 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (397 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_78 :
    Nat.Prime 401 ∧ (59939614252 : ℤ) = ⌊logCenter (401 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (401 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_79 :
    Nat.Prime 409 ∧ (60137151539 : ℤ) = ⌊logCenter (409 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (409 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_80 :
    Nat.Prime 419 ∧ (60378709178 : ℤ) = ⌊logCenter (419 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (419 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_81 :
    Nat.Prime 421 ∧ (60426328316 : ℤ) = ⌊logCenter (421 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (421 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_82 :
    Nat.Prime 431 ∧ (60661080880 : ℤ) = ⌊logCenter (431 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (431 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_83 :
    Nat.Prime 433 ∧ (60707377259 : ℤ) = ⌊logCenter (433 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (433 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_84 :
    Nat.Prime 439 ∧ (60844994109 : ℤ) = ⌊logCenter (439 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (439 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_85 :
    Nat.Prime 443 ∧ (60935697679 : ℤ) = ⌊logCenter (443 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (443 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_86 :
    Nat.Prime 449 ∧ (61070228856 : ℤ) = ⌊logCenter (449 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (449 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_87 :
    Nat.Prime 457 ∧ (61246833888 : ℤ) = ⌊logCenter (457 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (457 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_88 :
    Nat.Prime 461 ∧ (61333980409 : ℤ) = ⌊logCenter (461 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (461 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_89 :
    Nat.Prime 463 ∧ (61377270520 : ℤ) = ⌊logCenter (463 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (463 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_90 :
    Nat.Prime 467 ∧ (61463292555 : ℤ) = ⌊logCenter (467 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (467 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_91 :
    Nat.Prime 479 ∧ (61717005953 : ℤ) = ⌊logCenter (479 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (479 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_92 :
    Nat.Prime 487 ∧ (61882641210 : ℤ) = ⌊logCenter (487 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (487 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_93 :
    Nat.Prime 491 ∧ (61964441257 : ℤ) = ⌊logCenter (491 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (491 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_94 :
    Nat.Prime 499 ∧ (62126060936 : ℤ) = ⌊logCenter (499 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (499 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_95 :
    Nat.Prime 503 ∧ (62205901680 : ℤ) = ⌊logCenter (503 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (503 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_96 :
    Nat.Prime 509 ∧ (62324480144 : ℤ) = ⌊logCenter (509 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (509 : ℚ) = 8 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_97 :
    Nat.Prime 521 ∧ (62557500394 : ℤ) = ⌊logCenter (521 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (521 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_98 :
    Nat.Prime 523 ∧ (62595814617 : ℤ) = ⌊logCenter (523 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (523 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_99 :
    Nat.Prime 541 ∧ (62934192765 : ℤ) = ⌊logCenter (541 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (541 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_100 :
    Nat.Prime 547 ∧ (63044488000 : ℤ) = ⌊logCenter (547 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (547 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_101 :
    Nat.Prime 557 ∧ (63225652375 : ℤ) = ⌊logCenter (557 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (557 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_102 :
    Nat.Prime 563 ∧ (63332796258 : ℤ) = ⌊logCenter (563 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (563 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_103 :
    Nat.Prime 569 ∧ (63438804317 : ℤ) = ⌊logCenter (569 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (569 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_104 :
    Nat.Prime 571 ∧ (63473892073 : ℤ) = ⌊logCenter (571 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (571 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_105 :
    Nat.Prime 577 ∧ (63578422641 : ℤ) = ⌊logCenter (577 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (577 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_106 :
    Nat.Prime 587 ∧ (63750248174 : ℤ) = ⌊logCenter (587 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (587 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_107 :
    Nat.Prime 593 ∧ (63851943966 : ℤ) = ⌊logCenter (593 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (593 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_108 :
    Nat.Prime 599 ∧ (63952615957 : ℤ) = ⌊logCenter (599 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (599 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_109 :
    Nat.Prime 601 ∧ (63985949321 : ℤ) = ⌊logCenter (601 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (601 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_110 :
    Nat.Prime 607 ∧ (64085287887 : ℤ) = ⌊logCenter (607 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (607 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_111 :
    Nat.Prime 613 ∧ (64183649335 : ℤ) = ⌊logCenter (613 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (613 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_112 :
    Nat.Prime 617 ∧ (64248690215 : ℤ) = ⌊logCenter (617 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (617 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_113 :
    Nat.Prime 619 ∧ (64281052703 : ℤ) = ⌊logCenter (619 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (619 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_114 :
    Nat.Prime 631 ∧ (64473058602 : ℤ) = ⌊logCenter (631 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (631 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_115 :
    Nat.Prime 641 ∧ (64630294545 : ℤ) = ⌊logCenter (641 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (641 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_116 :
    Nat.Prime 643 ∧ (64661447218 : ℤ) = ⌊logCenter (643 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (643 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_117 :
    Nat.Prime 647 ∧ (64723462921 : ℤ) = ⌊logCenter (647 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (647 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_118 :
    Nat.Prime 653 ∧ (64815771269 : ℤ) = ⌊logCenter (653 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (653 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_119 :
    Nat.Prime 659 ∧ (64907235321 : ℤ) = ⌊logCenter (659 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (659 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_120 :
    Nat.Prime 661 ∧ (64937538375 : ℤ) = ⌊logCenter (661 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (661 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_121 :
    Nat.Prime 673 ∧ (65117453273 : ℤ) = ⌊logCenter (673 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (673 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_122 :
    Nat.Prime 677 ∧ (65176712705 : ℤ) = ⌊logCenter (677 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (677 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_123 :
    Nat.Prime 683 ∧ (65264948572 : ℤ) = ⌊logCenter (683 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (683 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_124 :
    Nat.Prime 691 ∧ (65381398214 : ℤ) = ⌊logCenter (691 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (691 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_125 :
    Nat.Prime 701 ∧ (65525078846 : ℤ) = ⌊logCenter (701 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (701 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_126 :
    Nat.Prime 709 ∧ (65638555241 : ℤ) = ⌊logCenter (709 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (709 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_127 :
    Nat.Prime 719 ∧ (65778613553 : ℤ) = ⌊logCenter (719 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (719 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_128 :
    Nat.Prime 727 ∧ (65889264751 : ℤ) = ⌊logCenter (727 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (727 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_129 :
    Nat.Prime 733 ∧ (65971456995 : ℤ) = ⌊logCenter (733 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (733 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_130 :
    Nat.Prime 739 ∧ (66052979186 : ℤ) = ⌊logCenter (739 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (739 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_131 :
    Nat.Prime 743 ∧ (66106960423 : ℤ) = ⌊logCenter (743 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (743 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_132 :
    Nat.Prime 751 ∧ (66214056494 : ℤ) = ⌊logCenter (751 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (751 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_133 :
    Nat.Prime 757 ∧ (66293632510 : ℤ) = ⌊logCenter (757 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (757 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_134 :
    Nat.Prime 761 ∧ (66346333555 : ℤ) = ⌊logCenter (761 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (761 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_135 :
    Nat.Prime 769 ∧ (66450909671 : ℤ) = ⌊logCenter (769 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (769 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_136 :
    Nat.Prime 773 ∧ (66502790462 : ℤ) = ⌊logCenter (773 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (773 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_137 :
    Nat.Prime 787 ∧ (66682282460 : ℤ) = ⌊logCenter (787 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (787 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_138 :
    Nat.Prime 797 ∧ (66808546764 : ℤ) = ⌊logCenter (797 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (797 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_139 :
    Nat.Prime 809 ∧ (66957989147 : ℤ) = ⌊logCenter (809 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (809 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_140 :
    Nat.Prime 811 ∧ (66982680517 : ℤ) = ⌊logCenter (811 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (811 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_141 :
    Nat.Prime 821 ∧ (67105231071 : ℤ) = ⌊logCenter (821 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (821 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_142 :
    Nat.Prime 823 ∧ (67129561983 : ℤ) = ⌊logCenter (823 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (823 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_143 :
    Nat.Prime 827 ∧ (67178046926 : ℤ) = ⌊logCenter (827 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (827 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_144 :
    Nat.Prime 829 ∧ (67202201527 : ℤ) = ⌊logCenter (829 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (829 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_145 :
    Nat.Prime 839 ∧ (67322107041 : ℤ) = ⌊logCenter (839 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (839 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_146 :
    Nat.Prime 853 ∧ (67487595451 : ℤ) = ⌊logCenter (853 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (853 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_147 :
    Nat.Prime 857 ∧ (67534379162 : ℤ) = ⌊logCenter (857 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (857 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_148 :
    Nat.Prime 859 ∧ (67557689196 : ℤ) = ⌊logCenter (859 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (859 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_149 :
    Nat.Prime 863 ∧ (67604146887 : ℤ) = ⌊logCenter (863 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (863 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_150 :
    Nat.Prime 877 ∧ (67765069900 : ℤ) = ⌊logCenter (877 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (877 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_151 :
    Nat.Prime 881 ∧ (67810576235 : ℤ) = ⌊logCenter (881 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (881 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_152 :
    Nat.Prime 883 ∧ (67833251982 : ℤ) = ⌊logCenter (883 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (883 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_153 :
    Nat.Prime 887 ∧ (67878449799 : ℤ) = ⌊logCenter (887 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (887 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_154 :
    Nat.Prime 907 ∧ (68101424477 : ℤ) = ⌊logCenter (907 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (907 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_155 :
    Nat.Prime 911 ∧ (68145428949 : ℤ) = ⌊logCenter (911 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (911 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_156 :
    Nat.Prime 919 ∧ (68232861200 : ℤ) = ⌊logCenter (919 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (919 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_157 :
    Nat.Prime 929 ∧ (68341087364 : ℤ) = ⌊logCenter (929 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (929 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_158 :
    Nat.Prime 937 ∧ (68426832798 : ℤ) = ⌊logCenter (937 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (937 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_159 :
    Nat.Prime 941 ∧ (68469431372 : ℤ) = ⌊logCenter (941 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (941 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_160 :
    Nat.Prime 947 ∧ (68532990908 : ℤ) = ⌊logCenter (947 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (947 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_161 :
    Nat.Prime 953 ∧ (68596149013 : ℤ) = ⌊logCenter (953 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (953 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_162 :
    Nat.Prime 967 ∧ (68741984931 : ℤ) = ⌊logCenter (967 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (967 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_163 :
    Nat.Prime 971 ∧ (68783264659 : ℤ) = ⌊logCenter (971 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (971 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_164 :
    Nat.Prime 977 ∧ (68844866497 : ℤ) = ⌊logCenter (977 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (977 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_165 :
    Nat.Prime 983 ∧ (68906091178 : ℤ) = ⌊logCenter (983 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (983 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_166 :
    Nat.Prime 991 ∧ (68987145319 : ℤ) = ⌊logCenter (991 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (991 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_167 :
    Nat.Prime 997 ∧ (69047507676 : ℤ) = ⌊logCenter (997 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (997 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_168 :
    Nat.Prime 1009 ∧ (69167150180 : ℤ) = ⌊logCenter (1009 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1009 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_169 :
    Nat.Prime 1013 ∧ (69206715019 : ℤ) = ⌊logCenter (1013 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1013 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_170 :
    Nat.Prime 1019 ∧ (69265770308 : ℤ) = ⌊logCenter (1019 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1019 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_171 :
    Nat.Prime 1021 ∧ (69285378158 : ℤ) = ⌊logCenter (1021 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1021 : ℚ) = 9 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_172 :
    Nat.Prime 1031 ∧ (69382844814 : ℤ) = ⌊logCenter (1031 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1031 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_173 :
    Nat.Prime 1033 ∧ (69402224665 : ℤ) = ⌊logCenter (1033 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1033 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_174 :
    Nat.Prime 1039 ∧ (69460139884 : ℤ) = ⌊logCenter (1039 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1039 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_175 :
    Nat.Prime 1049 ∧ (69555926057 : ℤ) = ⌊logCenter (1049 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1049 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_176 :
    Nat.Prime 1051 ∧ (69574973682 : ℤ) = ⌊logCenter (1051 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1051 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_177 :
    Nat.Prime 1061 ∧ (69669671360 : ℤ) = ⌊logCenter (1061 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1061 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_178 :
    Nat.Prime 1063 ∧ (69688503757 : ℤ) = ⌊logCenter (1063 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1063 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_179 :
    Nat.Prime 1069 ∧ (69744789084 : ℤ) = ⌊logCenter (1069 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1069 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_180 :
    Nat.Prime 1087 ∧ (69911768845 : ℤ) = ⌊logCenter (1087 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1087 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_181 :
    Nat.Prime 1091 ∧ (69948499832 : ℤ) = ⌊logCenter (1091 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1091 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_182 :
    Nat.Prime 1093 ∧ (69966814855 : ℤ) = ⌊logCenter (1093 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1093 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_183 :
    Nat.Prime 1097 ∧ (70003344576 : ℤ) = ⌊logCenter (1097 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1097 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_184 :
    Nat.Prime 1103 ∧ (70057890166 : ℤ) = ⌊logCenter (1103 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1103 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_185 :
    Nat.Prime 1109 ∧ (70112139847 : ℤ) = ⌊logCenter (1109 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1109 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_186 :
    Nat.Prime 1117 ∧ (70184017964 : ℤ) = ⌊logCenter (1117 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1117 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_187 :
    Nat.Prime 1123 ∧ (70237589521 : ℤ) = ⌊logCenter (1123 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1123 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_188 :
    Nat.Prime 1129 ∧ (70290875615 : ℤ) = ⌊logCenter (1129 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1129 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_189 :
    Nat.Prime 1151 ∧ (70483864061 : ℤ) = ⌊logCenter (1151 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1151 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_190 :
    Nat.Prime 1153 ∧ (70501225176 : ℤ) = ⌊logCenter (1153 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1153 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_191 :
    Nat.Prime 1163 ∧ (70587581499 : ℤ) = ⌊logCenter (1163 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1163 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_192 :
    Nat.Prime 1171 ∧ (70656133609 : ℤ) = ⌊logCenter (1171 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1171 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_193 :
    Nat.Prime 1181 ∧ (70741168135 : ℤ) = ⌊logCenter (1181 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1181 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_194 :
    Nat.Prime 1187 ∧ (70791843920 : ℤ) = ⌊logCenter (1187 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1187 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_195 :
    Nat.Prime 1193 ∧ (70842264194 : ℤ) = ⌊logCenter (1193 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1193 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_196 :
    Nat.Prime 1201 ∧ (70909098194 : ℤ) = ⌊logCenter (1201 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1201 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_197 :
    Nat.Prime 1213 ∧ (71008519063 : ℤ) = ⌊logCenter (1213 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1213 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_198 :
    Nat.Prime 1217 ∧ (71041440903 : ℤ) = ⌊logCenter (1217 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1217 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_199 :
    Nat.Prime 1223 ∧ (71090621330 : ℤ) = ⌊logCenter (1223 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1223 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_200 :
    Nat.Prime 1229 ∧ (71139561069 : ℤ) = ⌊logCenter (1229 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1229 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_201 :
    Nat.Prime 1231 ∧ (71155821235 : ℤ) = ⌊logCenter (1231 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1231 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_202 :
    Nat.Prime 1237 ∧ (71204443697 : ℤ) = ⌊logCenter (1237 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1237 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_203 :
    Nat.Prime 1249 ∧ (71300985075 : ℤ) = ⌊logCenter (1249 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1249 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_204 :
    Nat.Prime 1259 ∧ (71380730314 : ℤ) = ⌊logCenter (1259 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1259 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_205 :
    Nat.Prime 1277 ∧ (71522688534 : ℤ) = ⌊logCenter (1277 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1277 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_206 :
    Nat.Prime 1279 ∧ (71538337989 : ℤ) = ⌊logCenter (1279 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1279 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_207 :
    Nat.Prime 1283 ∧ (71569563620 : ℤ) = ⌊logCenter (1283 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1283 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_208 :
    Nat.Prime 1289 ∧ (71616220003 : ℤ) = ⌊logCenter (1289 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1289 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_209 :
    Nat.Prime 1291 ∧ (71631723882 : ℤ) = ⌊logCenter (1291 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1291 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_210 :
    Nat.Prime 1297 ∧ (71678091817 : ℤ) = ⌊logCenter (1297 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1297 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_211 :
    Nat.Prime 1301 ∧ (71708884759 : ℤ) = ⌊logCenter (1301 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1301 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_212 :
    Nat.Prime 1303 ∧ (71724245745 : ℤ) = ⌊logCenter (1303 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1303 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_213 :
    Nat.Prime 1307 ∧ (71754897110 : ℤ) = ⌊logCenter (1307 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1307 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_214 :
    Nat.Prime 1319 ∧ (71846291501 : ℤ) = ⌊logCenter (1319 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1319 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_215 :
    Nat.Prime 1321 ∧ (71861443019 : ℤ) = ⌊logCenter (1321 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1321 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_216 :
    Nat.Prime 1327 ∧ (71906760317 : ℤ) = ⌊logCenter (1327 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1327 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_217 :
    Nat.Prime 1361 ∧ (72159750000 : ℤ) = ⌊logCenter (1361 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1361 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_218 :
    Nat.Prime 1367 ∧ (72203738341 : ℤ) = ⌊logCenter (1367 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1367 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_219 :
    Nat.Prime 1373 ∧ (72247534031 : ℤ) = ⌊logCenter (1373 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1373 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_220 :
    Nat.Prime 1381 ∧ (72305631508 : ℤ) = ⌊logCenter (1381 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1381 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_221 :
    Nat.Prime 1399 ∧ (72435129720 : ℤ) = ⌊logCenter (1399 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1399 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

private theorem theta_log_row_222 :
    Nat.Prime 1409 ∧ (72506355092 : ℤ) = ⌊logCenter (1409 : ℚ) * 10000000000⌋ := by
  constructor
  · norm_num
  · have hs : logScale (1409 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem theta_log_rows_checked :
    ∀ r ∈ thetaLogRows, r.1.Prime ∧ r.2 = ⌊logCenter (r.1 : ℚ) * 10000000000⌋ := by
  simp only [thetaLogRows, List.forall_mem_cons]
  exact ⟨theta_log_row_0, theta_log_row_1, theta_log_row_2, theta_log_row_3, theta_log_row_4, theta_log_row_5, theta_log_row_6, theta_log_row_7, theta_log_row_8, theta_log_row_9, theta_log_row_10, theta_log_row_11, theta_log_row_12, theta_log_row_13, theta_log_row_14, theta_log_row_15, theta_log_row_16, theta_log_row_17, theta_log_row_18, theta_log_row_19, theta_log_row_20, theta_log_row_21, theta_log_row_22, theta_log_row_23, theta_log_row_24, theta_log_row_25, theta_log_row_26, theta_log_row_27, theta_log_row_28, theta_log_row_29, theta_log_row_30, theta_log_row_31, theta_log_row_32, theta_log_row_33, theta_log_row_34, theta_log_row_35, theta_log_row_36, theta_log_row_37, theta_log_row_38, theta_log_row_39, theta_log_row_40, theta_log_row_41, theta_log_row_42, theta_log_row_43, theta_log_row_44, theta_log_row_45, theta_log_row_46, theta_log_row_47, theta_log_row_48, theta_log_row_49, theta_log_row_50, theta_log_row_51, theta_log_row_52, theta_log_row_53, theta_log_row_54, theta_log_row_55, theta_log_row_56, theta_log_row_57, theta_log_row_58, theta_log_row_59, theta_log_row_60, theta_log_row_61, theta_log_row_62, theta_log_row_63, theta_log_row_64, theta_log_row_65, theta_log_row_66, theta_log_row_67, theta_log_row_68, theta_log_row_69, theta_log_row_70, theta_log_row_71, theta_log_row_72, theta_log_row_73, theta_log_row_74, theta_log_row_75, theta_log_row_76, theta_log_row_77, theta_log_row_78, theta_log_row_79, theta_log_row_80, theta_log_row_81, theta_log_row_82, theta_log_row_83, theta_log_row_84, theta_log_row_85, theta_log_row_86, theta_log_row_87, theta_log_row_88, theta_log_row_89, theta_log_row_90, theta_log_row_91, theta_log_row_92, theta_log_row_93, theta_log_row_94, theta_log_row_95, theta_log_row_96, theta_log_row_97, theta_log_row_98, theta_log_row_99, theta_log_row_100, theta_log_row_101, theta_log_row_102, theta_log_row_103, theta_log_row_104, theta_log_row_105, theta_log_row_106, theta_log_row_107, theta_log_row_108, theta_log_row_109, theta_log_row_110, theta_log_row_111, theta_log_row_112, theta_log_row_113, theta_log_row_114, theta_log_row_115, theta_log_row_116, theta_log_row_117, theta_log_row_118, theta_log_row_119, theta_log_row_120, theta_log_row_121, theta_log_row_122, theta_log_row_123, theta_log_row_124, theta_log_row_125, theta_log_row_126, theta_log_row_127, theta_log_row_128, theta_log_row_129, theta_log_row_130, theta_log_row_131, theta_log_row_132, theta_log_row_133, theta_log_row_134, theta_log_row_135, theta_log_row_136, theta_log_row_137, theta_log_row_138, theta_log_row_139, theta_log_row_140, theta_log_row_141, theta_log_row_142, theta_log_row_143, theta_log_row_144, theta_log_row_145, theta_log_row_146, theta_log_row_147, theta_log_row_148, theta_log_row_149, theta_log_row_150, theta_log_row_151, theta_log_row_152, theta_log_row_153, theta_log_row_154, theta_log_row_155, theta_log_row_156, theta_log_row_157, theta_log_row_158, theta_log_row_159, theta_log_row_160, theta_log_row_161, theta_log_row_162, theta_log_row_163, theta_log_row_164, theta_log_row_165, theta_log_row_166, theta_log_row_167, theta_log_row_168, theta_log_row_169, theta_log_row_170, theta_log_row_171, theta_log_row_172, theta_log_row_173, theta_log_row_174, theta_log_row_175, theta_log_row_176, theta_log_row_177, theta_log_row_178, theta_log_row_179, theta_log_row_180, theta_log_row_181, theta_log_row_182, theta_log_row_183, theta_log_row_184, theta_log_row_185, theta_log_row_186, theta_log_row_187, theta_log_row_188, theta_log_row_189, theta_log_row_190, theta_log_row_191, theta_log_row_192, theta_log_row_193, theta_log_row_194, theta_log_row_195, theta_log_row_196, theta_log_row_197, theta_log_row_198, theta_log_row_199, theta_log_row_200, theta_log_row_201, theta_log_row_202, theta_log_row_203, theta_log_row_204, theta_log_row_205, theta_log_row_206, theta_log_row_207, theta_log_row_208, theta_log_row_209, theta_log_row_210, theta_log_row_211, theta_log_row_212, theta_log_row_213, theta_log_row_214, theta_log_row_215, theta_log_row_216, theta_log_row_217, theta_log_row_218, theta_log_row_219, theta_log_row_220, theta_log_row_221, theta_log_row_222, (by simp)⟩

def unitsFrom : List (ℕ × ℤ) → ℕ → ℤ
  | [], _ => 0
  | (q, u) :: rs, p => if p = q then u else unitsFrom rs p

def thetaInteger (n : ℕ) : ℤ :=
  ∑ p ∈ Finset.range (n + 1), unitsFrom thetaLogRows p

#eval thetaInteger 1340

noncomputable section

private theorem unitsFrom_le (rs : List (ℕ × ℤ))
    (h : ∀ r ∈ rs, r.1.Prime ∧ (r.2 : ℝ) / 10000000000 ≤ Real.log r.1) (p : ℕ) :
    (unitsFrom rs p : ℝ) / 10000000000 ≤ if p.Prime then Real.log p else 0 := by
  induction rs with
  | nil =>
    simp only [unitsFrom, Int.cast_zero, zero_div]
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    · rfl
  | cons r rs ih =>
    rcases r with ⟨q, u⟩
    have hr := h (q, u) (by simp)
    by_cases he : p = q
    · subst p
      simpa only [unitsFrom, if_pos rfl, ite_true, if_pos hr.1] using hr.2
    · simpa only [unitsFrom, if_neg he] using
        ih (fun r hr => h r (by simp [hr]))

theorem thetaInteger_le_theta (n : ℕ) :
    (thetaInteger n : ℝ) / 10000000000 ≤ Chebyshev.theta n := by
  have hr : ∀ r ∈ thetaLogRows,
      r.1.Prime ∧ (r.2 : ℝ) / 10000000000 ≤ Real.log r.1 := by
    intro r hr
    obtain ⟨hp, hu⟩ := theta_log_rows_checked r hr
    refine ⟨hp, ?_⟩
    have h := (rational_log_bounds (x := (r.1 : ℚ))
      (by exact_mod_cast hp.one_lt.le)).1
    unfold logLo at h
    rw [← hu] at h
    exact_mod_cast h
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  change _ ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p
  rw [Finset.sum_filter]
  unfold thetaInteger
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun p _ => unitsFrom_le thetaLogRows hr p)

#print axioms theta_log_rows_checked
#print axioms thetaInteger_le_theta

end

end LiuWang.Proof.Campaign20260915.Totient
