import LiuWang.Proof.Campaign20260915.Totient.ThetaLogData

set_option autoImplicit false
set_option maxRecDepth 10000

namespace LiuWang.Proof.Campaign20260915.Totient

def eulerStep (p U : ℕ) : ℕ := if p.Prime then U * p / (p - 1) + 1 else U

def eulerUnits : ℕ → ℕ
  | 0 => 10000000000
  | n + 1 => eulerStep (n + 1) (eulerUnits n)

def productLower (u : ℤ) : ℚ :=
  (178107239 / 100000000) * ((u : ℚ) / 10000000000 +
    10000000000 / (2 * (u + 61)))

private theorem euler_units_cert_0 : eulerUnits 0 = 10000000000 := rfl

private theorem euler_units_cert_1 : eulerUnits 1 = 10000000000 := by
  change eulerStep 1 (eulerUnits 0) = 10000000000
  rw [euler_units_cert_0]
  norm_num [eulerStep]

private theorem euler_units_cert_2 : eulerUnits 2 = 20000000001 := by
  change eulerStep 2 (eulerUnits 1) = 20000000001
  rw [euler_units_cert_1]
  norm_num [eulerStep]

private theorem euler_units_cert_3 : eulerUnits 3 = 30000000002 := by
  change eulerStep 3 (eulerUnits 2) = 30000000002
  rw [euler_units_cert_2]
  norm_num [eulerStep]

private theorem euler_units_cert_4 : eulerUnits 4 = 30000000002 := by
  change eulerStep 4 (eulerUnits 3) = 30000000002
  rw [euler_units_cert_3]
  norm_num [eulerStep]

private theorem euler_units_cert_5 : eulerUnits 5 = 37500000003 := by
  change eulerStep 5 (eulerUnits 4) = 37500000003
  rw [euler_units_cert_4]
  norm_num [eulerStep]

private theorem euler_units_cert_6 : eulerUnits 6 = 37500000003 := by
  change eulerStep 6 (eulerUnits 5) = 37500000003
  rw [euler_units_cert_5]
  norm_num [eulerStep]

private theorem euler_units_cert_7 : eulerUnits 7 = 43750000004 := by
  change eulerStep 7 (eulerUnits 6) = 43750000004
  rw [euler_units_cert_6]
  norm_num [eulerStep]

private theorem euler_units_cert_8 : eulerUnits 8 = 43750000004 := by
  change eulerStep 8 (eulerUnits 7) = 43750000004
  rw [euler_units_cert_7]
  norm_num [eulerStep]

private theorem euler_units_cert_9 : eulerUnits 9 = 43750000004 := by
  change eulerStep 9 (eulerUnits 8) = 43750000004
  rw [euler_units_cert_8]
  norm_num [eulerStep]

private theorem euler_units_cert_10 : eulerUnits 10 = 43750000004 := by
  change eulerStep 10 (eulerUnits 9) = 43750000004
  rw [euler_units_cert_9]
  norm_num [eulerStep]

private theorem euler_units_cert_11 : eulerUnits 11 = 48125000005 := by
  change eulerStep 11 (eulerUnits 10) = 48125000005
  rw [euler_units_cert_10]
  norm_num [eulerStep]

private theorem euler_units_cert_12 : eulerUnits 12 = 48125000005 := by
  change eulerStep 12 (eulerUnits 11) = 48125000005
  rw [euler_units_cert_11]
  norm_num [eulerStep]

private theorem euler_units_cert_13 : eulerUnits 13 = 52135416673 := by
  change eulerStep 13 (eulerUnits 12) = 52135416673
  rw [euler_units_cert_12]
  norm_num [eulerStep]

private theorem euler_units_cert_14 : eulerUnits 14 = 52135416673 := by
  change eulerStep 14 (eulerUnits 13) = 52135416673
  rw [euler_units_cert_13]
  norm_num [eulerStep]

private theorem euler_units_cert_15 : eulerUnits 15 = 52135416673 := by
  change eulerStep 15 (eulerUnits 14) = 52135416673
  rw [euler_units_cert_14]
  norm_num [eulerStep]

private theorem euler_units_cert_16 : eulerUnits 16 = 52135416673 := by
  change eulerStep 16 (eulerUnits 15) = 52135416673
  rw [euler_units_cert_15]
  norm_num [eulerStep]

private theorem euler_units_cert_17 : eulerUnits 17 = 55393880216 := by
  change eulerStep 17 (eulerUnits 16) = 55393880216
  rw [euler_units_cert_16]
  norm_num [eulerStep]

private theorem euler_units_cert_18 : eulerUnits 18 = 55393880216 := by
  change eulerStep 18 (eulerUnits 17) = 55393880216
  rw [euler_units_cert_17]
  norm_num [eulerStep]

private theorem euler_units_cert_19 : eulerUnits 19 = 58471318006 := by
  change eulerStep 19 (eulerUnits 18) = 58471318006
  rw [euler_units_cert_18]
  norm_num [eulerStep]

private theorem euler_units_cert_20 : eulerUnits 20 = 58471318006 := by
  change eulerStep 20 (eulerUnits 19) = 58471318006
  rw [euler_units_cert_19]
  norm_num [eulerStep]

private theorem euler_units_cert_21 : eulerUnits 21 = 58471318006 := by
  change eulerStep 21 (eulerUnits 20) = 58471318006
  rw [euler_units_cert_20]
  norm_num [eulerStep]

private theorem euler_units_cert_22 : eulerUnits 22 = 58471318006 := by
  change eulerStep 22 (eulerUnits 21) = 58471318006
  rw [euler_units_cert_21]
  norm_num [eulerStep]

private theorem euler_units_cert_23 : eulerUnits 23 = 61129105189 := by
  change eulerStep 23 (eulerUnits 22) = 61129105189
  rw [euler_units_cert_22]
  norm_num [eulerStep]

private theorem euler_units_cert_24 : eulerUnits 24 = 61129105189 := by
  change eulerStep 24 (eulerUnits 23) = 61129105189
  rw [euler_units_cert_23]
  norm_num [eulerStep]

private theorem euler_units_cert_25 : eulerUnits 25 = 61129105189 := by
  change eulerStep 25 (eulerUnits 24) = 61129105189
  rw [euler_units_cert_24]
  norm_num [eulerStep]

private theorem euler_units_cert_26 : eulerUnits 26 = 61129105189 := by
  change eulerStep 26 (eulerUnits 25) = 61129105189
  rw [euler_units_cert_25]
  norm_num [eulerStep]

private theorem euler_units_cert_27 : eulerUnits 27 = 61129105189 := by
  change eulerStep 27 (eulerUnits 26) = 61129105189
  rw [euler_units_cert_26]
  norm_num [eulerStep]

private theorem euler_units_cert_28 : eulerUnits 28 = 61129105189 := by
  change eulerStep 28 (eulerUnits 27) = 61129105189
  rw [euler_units_cert_27]
  norm_num [eulerStep]

private theorem euler_units_cert_29 : eulerUnits 29 = 63312287518 := by
  change eulerStep 29 (eulerUnits 28) = 63312287518
  rw [euler_units_cert_28]
  norm_num [eulerStep]

private theorem euler_units_cert_30 : eulerUnits 30 = 63312287518 := by
  change eulerStep 30 (eulerUnits 29) = 63312287518
  rw [euler_units_cert_29]
  norm_num [eulerStep]

private theorem euler_units_cert_31 : eulerUnits 31 = 65422697102 := by
  change eulerStep 31 (eulerUnits 30) = 65422697102
  rw [euler_units_cert_30]
  norm_num [eulerStep]

private theorem euler_units_cert_32 : eulerUnits 32 = 65422697102 := by
  change eulerStep 32 (eulerUnits 31) = 65422697102
  rw [euler_units_cert_31]
  norm_num [eulerStep]

private theorem euler_units_cert_33 : eulerUnits 33 = 65422697102 := by
  change eulerStep 33 (eulerUnits 32) = 65422697102
  rw [euler_units_cert_32]
  norm_num [eulerStep]

private theorem euler_units_cert_34 : eulerUnits 34 = 65422697102 := by
  change eulerStep 34 (eulerUnits 33) = 65422697102
  rw [euler_units_cert_33]
  norm_num [eulerStep]

private theorem euler_units_cert_35 : eulerUnits 35 = 65422697102 := by
  change eulerStep 35 (eulerUnits 34) = 65422697102
  rw [euler_units_cert_34]
  norm_num [eulerStep]

private theorem euler_units_cert_36 : eulerUnits 36 = 65422697102 := by
  change eulerStep 36 (eulerUnits 35) = 65422697102
  rw [euler_units_cert_35]
  norm_num [eulerStep]

private theorem euler_units_cert_37 : eulerUnits 37 = 67239994244 := by
  change eulerStep 37 (eulerUnits 36) = 67239994244
  rw [euler_units_cert_36]
  norm_num [eulerStep]

private theorem euler_units_cert_38 : eulerUnits 38 = 67239994244 := by
  change eulerStep 38 (eulerUnits 37) = 67239994244
  rw [euler_units_cert_37]
  norm_num [eulerStep]

private theorem euler_units_cert_39 : eulerUnits 39 = 67239994244 := by
  change eulerStep 39 (eulerUnits 38) = 67239994244
  rw [euler_units_cert_38]
  norm_num [eulerStep]

private theorem euler_units_cert_40 : eulerUnits 40 = 67239994244 := by
  change eulerStep 40 (eulerUnits 39) = 67239994244
  rw [euler_units_cert_39]
  norm_num [eulerStep]

private theorem euler_units_cert_41 : eulerUnits 41 = 68920994101 := by
  change eulerStep 41 (eulerUnits 40) = 68920994101
  rw [euler_units_cert_40]
  norm_num [eulerStep]

private theorem euler_units_cert_42 : eulerUnits 42 = 68920994101 := by
  change eulerStep 42 (eulerUnits 41) = 68920994101
  rw [euler_units_cert_41]
  norm_num [eulerStep]

private theorem euler_units_cert_43 : eulerUnits 43 = 70561970152 := by
  change eulerStep 43 (eulerUnits 42) = 70561970152
  rw [euler_units_cert_42]
  norm_num [eulerStep]

private theorem euler_units_cert_44 : eulerUnits 44 = 70561970152 := by
  change eulerStep 44 (eulerUnits 43) = 70561970152
  rw [euler_units_cert_43]
  norm_num [eulerStep]

private theorem euler_units_cert_45 : eulerUnits 45 = 70561970152 := by
  change eulerStep 45 (eulerUnits 44) = 70561970152
  rw [euler_units_cert_44]
  norm_num [eulerStep]

private theorem euler_units_cert_46 : eulerUnits 46 = 70561970152 := by
  change eulerStep 46 (eulerUnits 45) = 70561970152
  rw [euler_units_cert_45]
  norm_num [eulerStep]

private theorem euler_units_cert_47 : eulerUnits 47 = 72095926025 := by
  change eulerStep 47 (eulerUnits 46) = 72095926025
  rw [euler_units_cert_46]
  norm_num [eulerStep]

private theorem euler_units_cert_48 : eulerUnits 48 = 72095926025 := by
  change eulerStep 48 (eulerUnits 47) = 72095926025
  rw [euler_units_cert_47]
  norm_num [eulerStep]

private theorem euler_units_cert_49 : eulerUnits 49 = 72095926025 := by
  change eulerStep 49 (eulerUnits 48) = 72095926025
  rw [euler_units_cert_48]
  norm_num [eulerStep]

private theorem euler_units_cert_50 : eulerUnits 50 = 72095926025 := by
  change eulerStep 50 (eulerUnits 49) = 72095926025
  rw [euler_units_cert_49]
  norm_num [eulerStep]

private theorem euler_units_cert_51 : eulerUnits 51 = 72095926025 := by
  change eulerStep 51 (eulerUnits 50) = 72095926025
  rw [euler_units_cert_50]
  norm_num [eulerStep]

private theorem euler_units_cert_52 : eulerUnits 52 = 72095926025 := by
  change eulerStep 52 (eulerUnits 51) = 72095926025
  rw [euler_units_cert_51]
  norm_num [eulerStep]

private theorem euler_units_cert_53 : eulerUnits 53 = 73482386141 := by
  change eulerStep 53 (eulerUnits 52) = 73482386141
  rw [euler_units_cert_52]
  norm_num [eulerStep]

private theorem euler_units_cert_54 : eulerUnits 54 = 73482386141 := by
  change eulerStep 54 (eulerUnits 53) = 73482386141
  rw [euler_units_cert_53]
  norm_num [eulerStep]

private theorem euler_units_cert_55 : eulerUnits 55 = 73482386141 := by
  change eulerStep 55 (eulerUnits 54) = 73482386141
  rw [euler_units_cert_54]
  norm_num [eulerStep]

private theorem euler_units_cert_56 : eulerUnits 56 = 73482386141 := by
  change eulerStep 56 (eulerUnits 55) = 73482386141
  rw [euler_units_cert_55]
  norm_num [eulerStep]

private theorem euler_units_cert_57 : eulerUnits 57 = 73482386141 := by
  change eulerStep 57 (eulerUnits 56) = 73482386141
  rw [euler_units_cert_56]
  norm_num [eulerStep]

private theorem euler_units_cert_58 : eulerUnits 58 = 73482386141 := by
  change eulerStep 58 (eulerUnits 57) = 73482386141
  rw [euler_units_cert_57]
  norm_num [eulerStep]

private theorem euler_units_cert_59 : eulerUnits 59 = 74749323834 := by
  change eulerStep 59 (eulerUnits 58) = 74749323834
  rw [euler_units_cert_58]
  norm_num [eulerStep]

private theorem euler_units_cert_60 : eulerUnits 60 = 74749323834 := by
  change eulerStep 60 (eulerUnits 59) = 74749323834
  rw [euler_units_cert_59]
  norm_num [eulerStep]

private theorem euler_units_cert_61 : eulerUnits 61 = 75995145898 := by
  change eulerStep 61 (eulerUnits 60) = 75995145898
  rw [euler_units_cert_60]
  norm_num [eulerStep]

private theorem euler_units_cert_62 : eulerUnits 62 = 75995145898 := by
  change eulerStep 62 (eulerUnits 61) = 75995145898
  rw [euler_units_cert_61]
  norm_num [eulerStep]

private theorem euler_units_cert_63 : eulerUnits 63 = 75995145898 := by
  change eulerStep 63 (eulerUnits 62) = 75995145898
  rw [euler_units_cert_62]
  norm_num [eulerStep]

private theorem euler_units_cert_64 : eulerUnits 64 = 75995145898 := by
  change eulerStep 64 (eulerUnits 63) = 75995145898
  rw [euler_units_cert_63]
  norm_num [eulerStep]

private theorem euler_units_cert_65 : eulerUnits 65 = 75995145898 := by
  change eulerStep 65 (eulerUnits 64) = 75995145898
  rw [euler_units_cert_64]
  norm_num [eulerStep]

private theorem euler_units_cert_66 : eulerUnits 66 = 75995145898 := by
  change eulerStep 66 (eulerUnits 65) = 75995145898
  rw [euler_units_cert_65]
  norm_num [eulerStep]

private theorem euler_units_cert_67 : eulerUnits 67 = 77146587503 := by
  change eulerStep 67 (eulerUnits 66) = 77146587503
  rw [euler_units_cert_66]
  norm_num [eulerStep]

private theorem euler_units_cert_68 : eulerUnits 68 = 77146587503 := by
  change eulerStep 68 (eulerUnits 67) = 77146587503
  rw [euler_units_cert_67]
  norm_num [eulerStep]

private theorem euler_units_cert_69 : eulerUnits 69 = 77146587503 := by
  change eulerStep 69 (eulerUnits 68) = 77146587503
  rw [euler_units_cert_68]
  norm_num [eulerStep]

private theorem euler_units_cert_70 : eulerUnits 70 = 77146587503 := by
  change eulerStep 70 (eulerUnits 69) = 77146587503
  rw [euler_units_cert_69]
  norm_num [eulerStep]

private theorem euler_units_cert_71 : eulerUnits 71 = 78248681611 := by
  change eulerStep 71 (eulerUnits 70) = 78248681611
  rw [euler_units_cert_70]
  norm_num [eulerStep]

private theorem euler_units_cert_72 : eulerUnits 72 = 78248681611 := by
  change eulerStep 72 (eulerUnits 71) = 78248681611
  rw [euler_units_cert_71]
  norm_num [eulerStep]

private theorem euler_units_cert_73 : eulerUnits 73 = 79335468856 := by
  change eulerStep 73 (eulerUnits 72) = 79335468856
  rw [euler_units_cert_72]
  norm_num [eulerStep]

private theorem euler_units_cert_74 : eulerUnits 74 = 79335468856 := by
  change eulerStep 74 (eulerUnits 73) = 79335468856
  rw [euler_units_cert_73]
  norm_num [eulerStep]

private theorem euler_units_cert_75 : eulerUnits 75 = 79335468856 := by
  change eulerStep 75 (eulerUnits 74) = 79335468856
  rw [euler_units_cert_74]
  norm_num [eulerStep]

private theorem euler_units_cert_76 : eulerUnits 76 = 79335468856 := by
  change eulerStep 76 (eulerUnits 75) = 79335468856
  rw [euler_units_cert_75]
  norm_num [eulerStep]

private theorem euler_units_cert_77 : eulerUnits 77 = 79335468856 := by
  change eulerStep 77 (eulerUnits 76) = 79335468856
  rw [euler_units_cert_76]
  norm_num [eulerStep]

private theorem euler_units_cert_78 : eulerUnits 78 = 79335468856 := by
  change eulerStep 78 (eulerUnits 77) = 79335468856
  rw [euler_units_cert_77]
  norm_num [eulerStep]

private theorem euler_units_cert_79 : eulerUnits 79 = 80352590252 := by
  change eulerStep 79 (eulerUnits 78) = 80352590252
  rw [euler_units_cert_78]
  norm_num [eulerStep]

private theorem euler_units_cert_80 : eulerUnits 80 = 80352590252 := by
  change eulerStep 80 (eulerUnits 79) = 80352590252
  rw [euler_units_cert_79]
  norm_num [eulerStep]

private theorem euler_units_cert_81 : eulerUnits 81 = 80352590252 := by
  change eulerStep 81 (eulerUnits 80) = 80352590252
  rw [euler_units_cert_80]
  norm_num [eulerStep]

private theorem euler_units_cert_82 : eulerUnits 82 = 80352590252 := by
  change eulerStep 82 (eulerUnits 81) = 80352590252
  rw [euler_units_cert_81]
  norm_num [eulerStep]

private theorem euler_units_cert_83 : eulerUnits 83 = 81332499890 := by
  change eulerStep 83 (eulerUnits 82) = 81332499890
  rw [euler_units_cert_82]
  norm_num [eulerStep]

private theorem euler_units_cert_84 : eulerUnits 84 = 81332499890 := by
  change eulerStep 84 (eulerUnits 83) = 81332499890
  rw [euler_units_cert_83]
  norm_num [eulerStep]

private theorem euler_units_cert_85 : eulerUnits 85 = 81332499890 := by
  change eulerStep 85 (eulerUnits 84) = 81332499890
  rw [euler_units_cert_84]
  norm_num [eulerStep]

private theorem euler_units_cert_86 : eulerUnits 86 = 81332499890 := by
  change eulerStep 86 (eulerUnits 85) = 81332499890
  rw [euler_units_cert_85]
  norm_num [eulerStep]

private theorem euler_units_cert_87 : eulerUnits 87 = 81332499890 := by
  change eulerStep 87 (eulerUnits 86) = 81332499890
  rw [euler_units_cert_86]
  norm_num [eulerStep]

private theorem euler_units_cert_88 : eulerUnits 88 = 81332499890 := by
  change eulerStep 88 (eulerUnits 87) = 81332499890
  rw [euler_units_cert_87]
  norm_num [eulerStep]

private theorem euler_units_cert_89 : eulerUnits 89 = 82256732844 := by
  change eulerStep 89 (eulerUnits 88) = 82256732844
  rw [euler_units_cert_88]
  norm_num [eulerStep]

private theorem euler_units_cert_90 : eulerUnits 90 = 82256732844 := by
  change eulerStep 90 (eulerUnits 89) = 82256732844
  rw [euler_units_cert_89]
  norm_num [eulerStep]

private theorem euler_units_cert_91 : eulerUnits 91 = 82256732844 := by
  change eulerStep 91 (eulerUnits 90) = 82256732844
  rw [euler_units_cert_90]
  norm_num [eulerStep]

private theorem euler_units_cert_92 : eulerUnits 92 = 82256732844 := by
  change eulerStep 92 (eulerUnits 91) = 82256732844
  rw [euler_units_cert_91]
  norm_num [eulerStep]

private theorem euler_units_cert_93 : eulerUnits 93 = 82256732844 := by
  change eulerStep 93 (eulerUnits 92) = 82256732844
  rw [euler_units_cert_92]
  norm_num [eulerStep]

private theorem euler_units_cert_94 : eulerUnits 94 = 82256732844 := by
  change eulerStep 94 (eulerUnits 93) = 82256732844
  rw [euler_units_cert_93]
  norm_num [eulerStep]

private theorem euler_units_cert_95 : eulerUnits 95 = 82256732844 := by
  change eulerStep 95 (eulerUnits 94) = 82256732844
  rw [euler_units_cert_94]
  norm_num [eulerStep]

private theorem euler_units_cert_96 : eulerUnits 96 = 82256732844 := by
  change eulerStep 96 (eulerUnits 95) = 82256732844
  rw [euler_units_cert_95]
  norm_num [eulerStep]

private theorem euler_units_cert_97 : eulerUnits 97 = 83113573812 := by
  change eulerStep 97 (eulerUnits 96) = 83113573812
  rw [euler_units_cert_96]
  norm_num [eulerStep]

private theorem euler_units_cert_98 : eulerUnits 98 = 83113573812 := by
  change eulerStep 98 (eulerUnits 97) = 83113573812
  rw [euler_units_cert_97]
  norm_num [eulerStep]

private theorem euler_units_cert_99 : eulerUnits 99 = 83113573812 := by
  change eulerStep 99 (eulerUnits 98) = 83113573812
  rw [euler_units_cert_98]
  norm_num [eulerStep]

private theorem euler_units_cert_100 : eulerUnits 100 = 83113573812 := by
  change eulerStep 100 (eulerUnits 99) = 83113573812
  rw [euler_units_cert_99]
  norm_num [eulerStep]

private theorem euler_units_cert_101 : eulerUnits 101 = 83944709551 := by
  change eulerStep 101 (eulerUnits 100) = 83944709551
  rw [euler_units_cert_100]
  norm_num [eulerStep]

private theorem euler_units_cert_102 : eulerUnits 102 = 83944709551 := by
  change eulerStep 102 (eulerUnits 101) = 83944709551
  rw [euler_units_cert_101]
  norm_num [eulerStep]

private theorem euler_units_cert_103 : eulerUnits 103 = 84767696900 := by
  change eulerStep 103 (eulerUnits 102) = 84767696900
  rw [euler_units_cert_102]
  norm_num [eulerStep]

private theorem euler_units_cert_104 : eulerUnits 104 = 84767696900 := by
  change eulerStep 104 (eulerUnits 103) = 84767696900
  rw [euler_units_cert_103]
  norm_num [eulerStep]

private theorem euler_units_cert_105 : eulerUnits 105 = 84767696900 := by
  change eulerStep 105 (eulerUnits 104) = 84767696900
  rw [euler_units_cert_104]
  norm_num [eulerStep]

private theorem euler_units_cert_106 : eulerUnits 106 = 84767696900 := by
  change eulerStep 106 (eulerUnits 105) = 84767696900
  rw [euler_units_cert_105]
  norm_num [eulerStep]

private theorem euler_units_cert_107 : eulerUnits 107 = 85567392154 := by
  change eulerStep 107 (eulerUnits 106) = 85567392154
  rw [euler_units_cert_106]
  norm_num [eulerStep]

private theorem euler_units_cert_108 : eulerUnits 108 = 85567392154 := by
  change eulerStep 108 (eulerUnits 107) = 85567392154
  rw [euler_units_cert_107]
  norm_num [eulerStep]

private theorem euler_units_cert_109 : eulerUnits 109 = 86359682823 := by
  change eulerStep 109 (eulerUnits 108) = 86359682823
  rw [euler_units_cert_108]
  norm_num [eulerStep]

private theorem euler_units_cert_110 : eulerUnits 110 = 86359682823 := by
  change eulerStep 110 (eulerUnits 109) = 86359682823
  rw [euler_units_cert_109]
  norm_num [eulerStep]

private theorem euler_units_cert_111 : eulerUnits 111 = 86359682823 := by
  change eulerStep 111 (eulerUnits 110) = 86359682823
  rw [euler_units_cert_110]
  norm_num [eulerStep]

private theorem euler_units_cert_112 : eulerUnits 112 = 86359682823 := by
  change eulerStep 112 (eulerUnits 111) = 86359682823
  rw [euler_units_cert_111]
  norm_num [eulerStep]

private theorem euler_units_cert_113 : eulerUnits 113 = 87130751420 := by
  change eulerStep 113 (eulerUnits 112) = 87130751420
  rw [euler_units_cert_112]
  norm_num [eulerStep]

private theorem euler_units_cert_114 : eulerUnits 114 = 87130751420 := by
  change eulerStep 114 (eulerUnits 113) = 87130751420
  rw [euler_units_cert_113]
  norm_num [eulerStep]

private theorem euler_units_cert_115 : eulerUnits 115 = 87130751420 := by
  change eulerStep 115 (eulerUnits 114) = 87130751420
  rw [euler_units_cert_114]
  norm_num [eulerStep]

private theorem euler_units_cert_116 : eulerUnits 116 = 87130751420 := by
  change eulerStep 116 (eulerUnits 115) = 87130751420
  rw [euler_units_cert_115]
  norm_num [eulerStep]

private theorem euler_units_cert_117 : eulerUnits 117 = 87130751420 := by
  change eulerStep 117 (eulerUnits 116) = 87130751420
  rw [euler_units_cert_116]
  norm_num [eulerStep]

private theorem euler_units_cert_118 : eulerUnits 118 = 87130751420 := by
  change eulerStep 118 (eulerUnits 117) = 87130751420
  rw [euler_units_cert_117]
  norm_num [eulerStep]

private theorem euler_units_cert_119 : eulerUnits 119 = 87130751420 := by
  change eulerStep 119 (eulerUnits 118) = 87130751420
  rw [euler_units_cert_118]
  norm_num [eulerStep]

private theorem euler_units_cert_120 : eulerUnits 120 = 87130751420 := by
  change eulerStep 120 (eulerUnits 119) = 87130751420
  rw [euler_units_cert_119]
  norm_num [eulerStep]

private theorem euler_units_cert_121 : eulerUnits 121 = 87130751420 := by
  change eulerStep 121 (eulerUnits 120) = 87130751420
  rw [euler_units_cert_120]
  norm_num [eulerStep]

private theorem euler_units_cert_122 : eulerUnits 122 = 87130751420 := by
  change eulerStep 122 (eulerUnits 121) = 87130751420
  rw [euler_units_cert_121]
  norm_num [eulerStep]

private theorem euler_units_cert_123 : eulerUnits 123 = 87130751420 := by
  change eulerStep 123 (eulerUnits 122) = 87130751420
  rw [euler_units_cert_122]
  norm_num [eulerStep]

private theorem euler_units_cert_124 : eulerUnits 124 = 87130751420 := by
  change eulerStep 124 (eulerUnits 123) = 87130751420
  rw [euler_units_cert_123]
  norm_num [eulerStep]

private theorem euler_units_cert_125 : eulerUnits 125 = 87130751420 := by
  change eulerStep 125 (eulerUnits 124) = 87130751420
  rw [euler_units_cert_124]
  norm_num [eulerStep]

private theorem euler_units_cert_126 : eulerUnits 126 = 87130751420 := by
  change eulerStep 126 (eulerUnits 125) = 87130751420
  rw [euler_units_cert_125]
  norm_num [eulerStep]

private theorem euler_units_cert_127 : eulerUnits 127 = 87822265321 := by
  change eulerStep 127 (eulerUnits 126) = 87822265321
  rw [euler_units_cert_126]
  norm_num [eulerStep]

private theorem euler_units_cert_128 : eulerUnits 128 = 87822265321 := by
  change eulerStep 128 (eulerUnits 127) = 87822265321
  rw [euler_units_cert_127]
  norm_num [eulerStep]

private theorem euler_units_cert_129 : eulerUnits 129 = 87822265321 := by
  change eulerStep 129 (eulerUnits 128) = 87822265321
  rw [euler_units_cert_128]
  norm_num [eulerStep]

private theorem euler_units_cert_130 : eulerUnits 130 = 87822265321 := by
  change eulerStep 130 (eulerUnits 129) = 87822265321
  rw [euler_units_cert_129]
  norm_num [eulerStep]

private theorem euler_units_cert_131 : eulerUnits 131 = 88497821209 := by
  change eulerStep 131 (eulerUnits 130) = 88497821209
  rw [euler_units_cert_130]
  norm_num [eulerStep]

private theorem euler_units_cert_132 : eulerUnits 132 = 88497821209 := by
  change eulerStep 132 (eulerUnits 131) = 88497821209
  rw [euler_units_cert_131]
  norm_num [eulerStep]

private theorem euler_units_cert_133 : eulerUnits 133 = 88497821209 := by
  change eulerStep 133 (eulerUnits 132) = 88497821209
  rw [euler_units_cert_132]
  norm_num [eulerStep]

private theorem euler_units_cert_134 : eulerUnits 134 = 88497821209 := by
  change eulerStep 134 (eulerUnits 133) = 88497821209
  rw [euler_units_cert_133]
  norm_num [eulerStep]

private theorem euler_units_cert_135 : eulerUnits 135 = 88497821209 := by
  change eulerStep 135 (eulerUnits 134) = 88497821209
  rw [euler_units_cert_134]
  norm_num [eulerStep]

private theorem euler_units_cert_136 : eulerUnits 136 = 88497821209 := by
  change eulerStep 136 (eulerUnits 135) = 88497821209
  rw [euler_units_cert_135]
  norm_num [eulerStep]

private theorem euler_units_cert_137 : eulerUnits 137 = 89148540483 := by
  change eulerStep 137 (eulerUnits 136) = 89148540483
  rw [euler_units_cert_136]
  norm_num [eulerStep]

private theorem euler_units_cert_138 : eulerUnits 138 = 89148540483 := by
  change eulerStep 138 (eulerUnits 137) = 89148540483
  rw [euler_units_cert_137]
  norm_num [eulerStep]

private theorem euler_units_cert_139 : eulerUnits 139 = 89794544400 := by
  change eulerStep 139 (eulerUnits 138) = 89794544400
  rw [euler_units_cert_138]
  norm_num [eulerStep]

private theorem euler_units_cert_140 : eulerUnits 140 = 89794544400 := by
  change eulerStep 140 (eulerUnits 139) = 89794544400
  rw [euler_units_cert_139]
  norm_num [eulerStep]

private theorem euler_units_cert_141 : eulerUnits 141 = 89794544400 := by
  change eulerStep 141 (eulerUnits 140) = 89794544400
  rw [euler_units_cert_140]
  norm_num [eulerStep]

private theorem euler_units_cert_142 : eulerUnits 142 = 89794544400 := by
  change eulerStep 142 (eulerUnits 141) = 89794544400
  rw [euler_units_cert_141]
  norm_num [eulerStep]

private theorem euler_units_cert_143 : eulerUnits 143 = 89794544400 := by
  change eulerStep 143 (eulerUnits 142) = 89794544400
  rw [euler_units_cert_142]
  norm_num [eulerStep]

private theorem euler_units_cert_144 : eulerUnits 144 = 89794544400 := by
  change eulerStep 144 (eulerUnits 143) = 89794544400
  rw [euler_units_cert_143]
  norm_num [eulerStep]

private theorem euler_units_cert_145 : eulerUnits 145 = 89794544400 := by
  change eulerStep 145 (eulerUnits 144) = 89794544400
  rw [euler_units_cert_144]
  norm_num [eulerStep]

private theorem euler_units_cert_146 : eulerUnits 146 = 89794544400 := by
  change eulerStep 146 (eulerUnits 145) = 89794544400
  rw [euler_units_cert_145]
  norm_num [eulerStep]

private theorem euler_units_cert_147 : eulerUnits 147 = 89794544400 := by
  change eulerStep 147 (eulerUnits 146) = 89794544400
  rw [euler_units_cert_146]
  norm_num [eulerStep]

private theorem euler_units_cert_148 : eulerUnits 148 = 89794544400 := by
  change eulerStep 148 (eulerUnits 147) = 89794544400
  rw [euler_units_cert_147]
  norm_num [eulerStep]

private theorem euler_units_cert_149 : eulerUnits 149 = 90401264295 := by
  change eulerStep 149 (eulerUnits 148) = 90401264295
  rw [euler_units_cert_148]
  norm_num [eulerStep]

private theorem euler_units_cert_150 : eulerUnits 150 = 90401264295 := by
  change eulerStep 150 (eulerUnits 149) = 90401264295
  rw [euler_units_cert_149]
  norm_num [eulerStep]

private theorem euler_units_cert_151 : eulerUnits 151 = 91003939391 := by
  change eulerStep 151 (eulerUnits 150) = 91003939391
  rw [euler_units_cert_150]
  norm_num [eulerStep]

private theorem euler_units_cert_152 : eulerUnits 152 = 91003939391 := by
  change eulerStep 152 (eulerUnits 151) = 91003939391
  rw [euler_units_cert_151]
  norm_num [eulerStep]

private theorem euler_units_cert_153 : eulerUnits 153 = 91003939391 := by
  change eulerStep 153 (eulerUnits 152) = 91003939391
  rw [euler_units_cert_152]
  norm_num [eulerStep]

private theorem euler_units_cert_154 : eulerUnits 154 = 91003939391 := by
  change eulerStep 154 (eulerUnits 153) = 91003939391
  rw [euler_units_cert_153]
  norm_num [eulerStep]

private theorem euler_units_cert_155 : eulerUnits 155 = 91003939391 := by
  change eulerStep 155 (eulerUnits 154) = 91003939391
  rw [euler_units_cert_154]
  norm_num [eulerStep]

private theorem euler_units_cert_156 : eulerUnits 156 = 91003939391 := by
  change eulerStep 156 (eulerUnits 155) = 91003939391
  rw [euler_units_cert_155]
  norm_num [eulerStep]

private theorem euler_units_cert_157 : eulerUnits 157 = 91587297977 := by
  change eulerStep 157 (eulerUnits 156) = 91587297977
  rw [euler_units_cert_156]
  norm_num [eulerStep]

private theorem euler_units_cert_158 : eulerUnits 158 = 91587297977 := by
  change eulerStep 158 (eulerUnits 157) = 91587297977
  rw [euler_units_cert_157]
  norm_num [eulerStep]

private theorem euler_units_cert_159 : eulerUnits 159 = 91587297977 := by
  change eulerStep 159 (eulerUnits 158) = 91587297977
  rw [euler_units_cert_158]
  norm_num [eulerStep]

private theorem euler_units_cert_160 : eulerUnits 160 = 91587297977 := by
  change eulerStep 160 (eulerUnits 159) = 91587297977
  rw [euler_units_cert_159]
  norm_num [eulerStep]

private theorem euler_units_cert_161 : eulerUnits 161 = 91587297977 := by
  change eulerStep 161 (eulerUnits 160) = 91587297977
  rw [euler_units_cert_160]
  norm_num [eulerStep]

private theorem euler_units_cert_162 : eulerUnits 162 = 91587297977 := by
  change eulerStep 162 (eulerUnits 161) = 91587297977
  rw [euler_units_cert_161]
  norm_num [eulerStep]

private theorem euler_units_cert_163 : eulerUnits 163 = 92152651669 := by
  change eulerStep 163 (eulerUnits 162) = 92152651669
  rw [euler_units_cert_162]
  norm_num [eulerStep]

private theorem euler_units_cert_164 : eulerUnits 164 = 92152651669 := by
  change eulerStep 164 (eulerUnits 163) = 92152651669
  rw [euler_units_cert_163]
  norm_num [eulerStep]

private theorem euler_units_cert_165 : eulerUnits 165 = 92152651669 := by
  change eulerStep 165 (eulerUnits 164) = 92152651669
  rw [euler_units_cert_164]
  norm_num [eulerStep]

private theorem euler_units_cert_166 : eulerUnits 166 = 92152651669 := by
  change eulerStep 166 (eulerUnits 165) = 92152651669
  rw [euler_units_cert_165]
  norm_num [eulerStep]

private theorem euler_units_cert_167 : eulerUnits 167 = 92707788125 := by
  change eulerStep 167 (eulerUnits 166) = 92707788125
  rw [euler_units_cert_166]
  norm_num [eulerStep]

private theorem euler_units_cert_168 : eulerUnits 168 = 92707788125 := by
  change eulerStep 168 (eulerUnits 167) = 92707788125
  rw [euler_units_cert_167]
  norm_num [eulerStep]

private theorem euler_units_cert_169 : eulerUnits 169 = 92707788125 := by
  change eulerStep 169 (eulerUnits 168) = 92707788125
  rw [euler_units_cert_168]
  norm_num [eulerStep]

private theorem euler_units_cert_170 : eulerUnits 170 = 92707788125 := by
  change eulerStep 170 (eulerUnits 169) = 92707788125
  rw [euler_units_cert_169]
  norm_num [eulerStep]

private theorem euler_units_cert_171 : eulerUnits 171 = 92707788125 := by
  change eulerStep 171 (eulerUnits 170) = 92707788125
  rw [euler_units_cert_170]
  norm_num [eulerStep]

private theorem euler_units_cert_172 : eulerUnits 172 = 92707788125 := by
  change eulerStep 172 (eulerUnits 171) = 92707788125
  rw [euler_units_cert_171]
  norm_num [eulerStep]

private theorem euler_units_cert_173 : eulerUnits 173 = 93246786894 := by
  change eulerStep 173 (eulerUnits 172) = 93246786894
  rw [euler_units_cert_172]
  norm_num [eulerStep]

private theorem euler_units_cert_174 : eulerUnits 174 = 93246786894 := by
  change eulerStep 174 (eulerUnits 173) = 93246786894
  rw [euler_units_cert_173]
  norm_num [eulerStep]

private theorem euler_units_cert_175 : eulerUnits 175 = 93246786894 := by
  change eulerStep 175 (eulerUnits 174) = 93246786894
  rw [euler_units_cert_174]
  norm_num [eulerStep]

private theorem euler_units_cert_176 : eulerUnits 176 = 93246786894 := by
  change eulerStep 176 (eulerUnits 175) = 93246786894
  rw [euler_units_cert_175]
  norm_num [eulerStep]

private theorem euler_units_cert_177 : eulerUnits 177 = 93246786894 := by
  change eulerStep 177 (eulerUnits 176) = 93246786894
  rw [euler_units_cert_176]
  norm_num [eulerStep]

private theorem euler_units_cert_178 : eulerUnits 178 = 93246786894 := by
  change eulerStep 178 (eulerUnits 177) = 93246786894
  rw [euler_units_cert_177]
  norm_num [eulerStep]

private theorem euler_units_cert_179 : eulerUnits 179 = 93770645248 := by
  change eulerStep 179 (eulerUnits 178) = 93770645248
  rw [euler_units_cert_178]
  norm_num [eulerStep]

private theorem euler_units_cert_180 : eulerUnits 180 = 93770645248 := by
  change eulerStep 180 (eulerUnits 179) = 93770645248
  rw [euler_units_cert_179]
  norm_num [eulerStep]

private theorem euler_units_cert_181 : eulerUnits 181 = 94291593278 := by
  change eulerStep 181 (eulerUnits 180) = 94291593278
  rw [euler_units_cert_180]
  norm_num [eulerStep]

private theorem euler_units_cert_182 : eulerUnits 182 = 94291593278 := by
  change eulerStep 182 (eulerUnits 181) = 94291593278
  rw [euler_units_cert_181]
  norm_num [eulerStep]

private theorem euler_units_cert_183 : eulerUnits 183 = 94291593278 := by
  change eulerStep 183 (eulerUnits 182) = 94291593278
  rw [euler_units_cert_182]
  norm_num [eulerStep]

private theorem euler_units_cert_184 : eulerUnits 184 = 94291593278 := by
  change eulerStep 184 (eulerUnits 183) = 94291593278
  rw [euler_units_cert_183]
  norm_num [eulerStep]

private theorem euler_units_cert_185 : eulerUnits 185 = 94291593278 := by
  change eulerStep 185 (eulerUnits 184) = 94291593278
  rw [euler_units_cert_184]
  norm_num [eulerStep]

private theorem euler_units_cert_186 : eulerUnits 186 = 94291593278 := by
  change eulerStep 186 (eulerUnits 185) = 94291593278
  rw [euler_units_cert_185]
  norm_num [eulerStep]

private theorem euler_units_cert_187 : eulerUnits 187 = 94291593278 := by
  change eulerStep 187 (eulerUnits 186) = 94291593278
  rw [euler_units_cert_186]
  norm_num [eulerStep]

private theorem euler_units_cert_188 : eulerUnits 188 = 94291593278 := by
  change eulerStep 188 (eulerUnits 187) = 94291593278
  rw [euler_units_cert_187]
  norm_num [eulerStep]

private theorem euler_units_cert_189 : eulerUnits 189 = 94291593278 := by
  change eulerStep 189 (eulerUnits 188) = 94291593278
  rw [euler_units_cert_188]
  norm_num [eulerStep]

private theorem euler_units_cert_190 : eulerUnits 190 = 94291593278 := by
  change eulerStep 190 (eulerUnits 189) = 94291593278
  rw [euler_units_cert_189]
  norm_num [eulerStep]

private theorem euler_units_cert_191 : eulerUnits 191 = 94787864822 := by
  change eulerStep 191 (eulerUnits 190) = 94787864822
  rw [euler_units_cert_190]
  norm_num [eulerStep]

private theorem euler_units_cert_192 : eulerUnits 192 = 94787864822 := by
  change eulerStep 192 (eulerUnits 191) = 94787864822
  rw [euler_units_cert_191]
  norm_num [eulerStep]

private theorem euler_units_cert_193 : eulerUnits 193 = 95281551618 := by
  change eulerStep 193 (eulerUnits 192) = 95281551618
  rw [euler_units_cert_192]
  norm_num [eulerStep]

private theorem euler_units_cert_194 : eulerUnits 194 = 95281551618 := by
  change eulerStep 194 (eulerUnits 193) = 95281551618
  rw [euler_units_cert_193]
  norm_num [eulerStep]

private theorem euler_units_cert_195 : eulerUnits 195 = 95281551618 := by
  change eulerStep 195 (eulerUnits 194) = 95281551618
  rw [euler_units_cert_194]
  norm_num [eulerStep]

private theorem euler_units_cert_196 : eulerUnits 196 = 95281551618 := by
  change eulerStep 196 (eulerUnits 195) = 95281551618
  rw [euler_units_cert_195]
  norm_num [eulerStep]

private theorem euler_units_cert_197 : eulerUnits 197 = 95767681984 := by
  change eulerStep 197 (eulerUnits 196) = 95767681984
  rw [euler_units_cert_196]
  norm_num [eulerStep]

private theorem euler_units_cert_198 : eulerUnits 198 = 95767681984 := by
  change eulerStep 198 (eulerUnits 197) = 95767681984
  rw [euler_units_cert_197]
  norm_num [eulerStep]

private theorem euler_units_cert_199 : eulerUnits 199 = 96251357146 := by
  change eulerStep 199 (eulerUnits 198) = 96251357146
  rw [euler_units_cert_198]
  norm_num [eulerStep]

private theorem euler_units_cert_200 : eulerUnits 200 = 96251357146 := by
  change eulerStep 200 (eulerUnits 199) = 96251357146
  rw [euler_units_cert_199]
  norm_num [eulerStep]

private theorem euler_units_cert_201 : eulerUnits 201 = 96251357146 := by
  change eulerStep 201 (eulerUnits 200) = 96251357146
  rw [euler_units_cert_200]
  norm_num [eulerStep]

private theorem euler_units_cert_202 : eulerUnits 202 = 96251357146 := by
  change eulerStep 202 (eulerUnits 201) = 96251357146
  rw [euler_units_cert_201]
  norm_num [eulerStep]

private theorem euler_units_cert_203 : eulerUnits 203 = 96251357146 := by
  change eulerStep 203 (eulerUnits 202) = 96251357146
  rw [euler_units_cert_202]
  norm_num [eulerStep]

private theorem euler_units_cert_204 : eulerUnits 204 = 96251357146 := by
  change eulerStep 204 (eulerUnits 203) = 96251357146
  rw [euler_units_cert_203]
  norm_num [eulerStep]

private theorem euler_units_cert_205 : eulerUnits 205 = 96251357146 := by
  change eulerStep 205 (eulerUnits 204) = 96251357146
  rw [euler_units_cert_204]
  norm_num [eulerStep]

private theorem euler_units_cert_206 : eulerUnits 206 = 96251357146 := by
  change eulerStep 206 (eulerUnits 205) = 96251357146
  rw [euler_units_cert_205]
  norm_num [eulerStep]

private theorem euler_units_cert_207 : eulerUnits 207 = 96251357146 := by
  change eulerStep 207 (eulerUnits 206) = 96251357146
  rw [euler_units_cert_206]
  norm_num [eulerStep]

private theorem euler_units_cert_208 : eulerUnits 208 = 96251357146 := by
  change eulerStep 208 (eulerUnits 207) = 96251357146
  rw [euler_units_cert_207]
  norm_num [eulerStep]

private theorem euler_units_cert_209 : eulerUnits 209 = 96251357146 := by
  change eulerStep 209 (eulerUnits 208) = 96251357146
  rw [euler_units_cert_208]
  norm_num [eulerStep]

private theorem euler_units_cert_210 : eulerUnits 210 = 96251357146 := by
  change eulerStep 210 (eulerUnits 209) = 96251357146
  rw [euler_units_cert_209]
  norm_num [eulerStep]

private theorem euler_units_cert_211 : eulerUnits 211 = 96709696942 := by
  change eulerStep 211 (eulerUnits 210) = 96709696942
  rw [euler_units_cert_210]
  norm_num [eulerStep]

private theorem euler_units_cert_212 : eulerUnits 212 = 96709696942 := by
  change eulerStep 212 (eulerUnits 211) = 96709696942
  rw [euler_units_cert_211]
  norm_num [eulerStep]

private theorem euler_units_cert_213 : eulerUnits 213 = 96709696942 := by
  change eulerStep 213 (eulerUnits 212) = 96709696942
  rw [euler_units_cert_212]
  norm_num [eulerStep]

private theorem euler_units_cert_214 : eulerUnits 214 = 96709696942 := by
  change eulerStep 214 (eulerUnits 213) = 96709696942
  rw [euler_units_cert_213]
  norm_num [eulerStep]

private theorem euler_units_cert_215 : eulerUnits 215 = 96709696942 := by
  change eulerStep 215 (eulerUnits 214) = 96709696942
  rw [euler_units_cert_214]
  norm_num [eulerStep]

private theorem euler_units_cert_216 : eulerUnits 216 = 96709696942 := by
  change eulerStep 216 (eulerUnits 215) = 96709696942
  rw [euler_units_cert_215]
  norm_num [eulerStep]

private theorem euler_units_cert_217 : eulerUnits 217 = 96709696942 := by
  change eulerStep 217 (eulerUnits 216) = 96709696942
  rw [euler_units_cert_216]
  norm_num [eulerStep]

private theorem euler_units_cert_218 : eulerUnits 218 = 96709696942 := by
  change eulerStep 218 (eulerUnits 217) = 96709696942
  rw [euler_units_cert_217]
  norm_num [eulerStep]

private theorem euler_units_cert_219 : eulerUnits 219 = 96709696942 := by
  change eulerStep 219 (eulerUnits 218) = 96709696942
  rw [euler_units_cert_218]
  norm_num [eulerStep]

private theorem euler_units_cert_220 : eulerUnits 220 = 96709696942 := by
  change eulerStep 220 (eulerUnits 219) = 96709696942
  rw [euler_units_cert_219]
  norm_num [eulerStep]

private theorem euler_units_cert_221 : eulerUnits 221 = 96709696942 := by
  change eulerStep 221 (eulerUnits 220) = 96709696942
  rw [euler_units_cert_220]
  norm_num [eulerStep]

private theorem euler_units_cert_222 : eulerUnits 222 = 96709696942 := by
  change eulerStep 222 (eulerUnits 221) = 96709696942
  rw [euler_units_cert_221]
  norm_num [eulerStep]

private theorem euler_units_cert_223 : eulerUnits 223 = 97145326208 := by
  change eulerStep 223 (eulerUnits 222) = 97145326208
  rw [euler_units_cert_222]
  norm_num [eulerStep]

private theorem euler_units_cert_224 : eulerUnits 224 = 97145326208 := by
  change eulerStep 224 (eulerUnits 223) = 97145326208
  rw [euler_units_cert_223]
  norm_num [eulerStep]

private theorem euler_units_cert_225 : eulerUnits 225 = 97145326208 := by
  change eulerStep 225 (eulerUnits 224) = 97145326208
  rw [euler_units_cert_224]
  norm_num [eulerStep]

private theorem euler_units_cert_226 : eulerUnits 226 = 97145326208 := by
  change eulerStep 226 (eulerUnits 225) = 97145326208
  rw [euler_units_cert_225]
  norm_num [eulerStep]

private theorem euler_units_cert_227 : eulerUnits 227 = 97575172785 := by
  change eulerStep 227 (eulerUnits 226) = 97575172785
  rw [euler_units_cert_226]
  norm_num [eulerStep]

private theorem euler_units_cert_228 : eulerUnits 228 = 97575172785 := by
  change eulerStep 228 (eulerUnits 227) = 97575172785
  rw [euler_units_cert_227]
  norm_num [eulerStep]

private theorem euler_units_cert_229 : eulerUnits 229 = 98003134070 := by
  change eulerStep 229 (eulerUnits 228) = 98003134070
  rw [euler_units_cert_228]
  norm_num [eulerStep]

private theorem euler_units_cert_230 : eulerUnits 230 = 98003134070 := by
  change eulerStep 230 (eulerUnits 229) = 98003134070
  rw [euler_units_cert_229]
  norm_num [eulerStep]

private theorem euler_units_cert_231 : eulerUnits 231 = 98003134070 := by
  change eulerStep 231 (eulerUnits 230) = 98003134070
  rw [euler_units_cert_230]
  norm_num [eulerStep]

private theorem euler_units_cert_232 : eulerUnits 232 = 98003134070 := by
  change eulerStep 232 (eulerUnits 231) = 98003134070
  rw [euler_units_cert_231]
  norm_num [eulerStep]

private theorem euler_units_cert_233 : eulerUnits 233 = 98425561373 := by
  change eulerStep 233 (eulerUnits 232) = 98425561373
  rw [euler_units_cert_232]
  norm_num [eulerStep]

private theorem euler_units_cert_234 : eulerUnits 234 = 98425561373 := by
  change eulerStep 234 (eulerUnits 233) = 98425561373
  rw [euler_units_cert_233]
  norm_num [eulerStep]

private theorem euler_units_cert_235 : eulerUnits 235 = 98425561373 := by
  change eulerStep 235 (eulerUnits 234) = 98425561373
  rw [euler_units_cert_234]
  norm_num [eulerStep]

private theorem euler_units_cert_236 : eulerUnits 236 = 98425561373 := by
  change eulerStep 236 (eulerUnits 235) = 98425561373
  rw [euler_units_cert_235]
  norm_num [eulerStep]

private theorem euler_units_cert_237 : eulerUnits 237 = 98425561373 := by
  change eulerStep 237 (eulerUnits 236) = 98425561373
  rw [euler_units_cert_236]
  norm_num [eulerStep]

private theorem euler_units_cert_238 : eulerUnits 238 = 98425561373 := by
  change eulerStep 238 (eulerUnits 237) = 98425561373
  rw [euler_units_cert_237]
  norm_num [eulerStep]

private theorem euler_units_cert_239 : eulerUnits 239 = 98839114152 := by
  change eulerStep 239 (eulerUnits 238) = 98839114152
  rw [euler_units_cert_238]
  norm_num [eulerStep]

private theorem euler_units_cert_240 : eulerUnits 240 = 98839114152 := by
  change eulerStep 240 (eulerUnits 239) = 98839114152
  rw [euler_units_cert_239]
  norm_num [eulerStep]

private theorem euler_units_cert_241 : eulerUnits 241 = 99250943795 := by
  change eulerStep 241 (eulerUnits 240) = 99250943795
  rw [euler_units_cert_240]
  norm_num [eulerStep]

private theorem euler_units_cert_242 : eulerUnits 242 = 99250943795 := by
  change eulerStep 242 (eulerUnits 241) = 99250943795
  rw [euler_units_cert_241]
  norm_num [eulerStep]

private theorem euler_units_cert_243 : eulerUnits 243 = 99250943795 := by
  change eulerStep 243 (eulerUnits 242) = 99250943795
  rw [euler_units_cert_242]
  norm_num [eulerStep]

private theorem euler_units_cert_244 : eulerUnits 244 = 99250943795 := by
  change eulerStep 244 (eulerUnits 243) = 99250943795
  rw [euler_units_cert_243]
  norm_num [eulerStep]

private theorem euler_units_cert_245 : eulerUnits 245 = 99250943795 := by
  change eulerStep 245 (eulerUnits 244) = 99250943795
  rw [euler_units_cert_244]
  norm_num [eulerStep]

private theorem euler_units_cert_246 : eulerUnits 246 = 99250943795 := by
  change eulerStep 246 (eulerUnits 245) = 99250943795
  rw [euler_units_cert_245]
  norm_num [eulerStep]

private theorem euler_units_cert_247 : eulerUnits 247 = 99250943795 := by
  change eulerStep 247 (eulerUnits 246) = 99250943795
  rw [euler_units_cert_246]
  norm_num [eulerStep]

private theorem euler_units_cert_248 : eulerUnits 248 = 99250943795 := by
  change eulerStep 248 (eulerUnits 247) = 99250943795
  rw [euler_units_cert_247]
  norm_num [eulerStep]

private theorem euler_units_cert_249 : eulerUnits 249 = 99250943795 := by
  change eulerStep 249 (eulerUnits 248) = 99250943795
  rw [euler_units_cert_248]
  norm_num [eulerStep]

private theorem euler_units_cert_250 : eulerUnits 250 = 99250943795 := by
  change eulerStep 250 (eulerUnits 249) = 99250943795
  rw [euler_units_cert_249]
  norm_num [eulerStep]

private theorem euler_units_cert_251 : eulerUnits 251 = 99647947571 := by
  change eulerStep 251 (eulerUnits 250) = 99647947571
  rw [euler_units_cert_250]
  norm_num [eulerStep]

private theorem euler_units_cert_252 : eulerUnits 252 = 99647947571 := by
  change eulerStep 252 (eulerUnits 251) = 99647947571
  rw [euler_units_cert_251]
  norm_num [eulerStep]

private theorem euler_units_cert_253 : eulerUnits 253 = 99647947571 := by
  change eulerStep 253 (eulerUnits 252) = 99647947571
  rw [euler_units_cert_252]
  norm_num [eulerStep]

private theorem euler_units_cert_254 : eulerUnits 254 = 99647947571 := by
  change eulerStep 254 (eulerUnits 253) = 99647947571
  rw [euler_units_cert_253]
  norm_num [eulerStep]

private theorem euler_units_cert_255 : eulerUnits 255 = 99647947571 := by
  change eulerStep 255 (eulerUnits 254) = 99647947571
  rw [euler_units_cert_254]
  norm_num [eulerStep]

private theorem euler_units_cert_256 : eulerUnits 256 = 99647947571 := by
  change eulerStep 256 (eulerUnits 255) = 99647947571
  rw [euler_units_cert_255]
  norm_num [eulerStep]

private theorem euler_units_cert_257 : eulerUnits 257 = 100037197367 := by
  change eulerStep 257 (eulerUnits 256) = 100037197367
  rw [euler_units_cert_256]
  norm_num [eulerStep]

private theorem euler_units_cert_258 : eulerUnits 258 = 100037197367 := by
  change eulerStep 258 (eulerUnits 257) = 100037197367
  rw [euler_units_cert_257]
  norm_num [eulerStep]

private theorem euler_units_cert_259 : eulerUnits 259 = 100037197367 := by
  change eulerStep 259 (eulerUnits 258) = 100037197367
  rw [euler_units_cert_258]
  norm_num [eulerStep]

private theorem euler_units_cert_260 : eulerUnits 260 = 100037197367 := by
  change eulerStep 260 (eulerUnits 259) = 100037197367
  rw [euler_units_cert_259]
  norm_num [eulerStep]

private theorem euler_units_cert_261 : eulerUnits 261 = 100037197367 := by
  change eulerStep 261 (eulerUnits 260) = 100037197367
  rw [euler_units_cert_260]
  norm_num [eulerStep]

private theorem euler_units_cert_262 : eulerUnits 262 = 100037197367 := by
  change eulerStep 262 (eulerUnits 261) = 100037197367
  rw [euler_units_cert_261]
  norm_num [eulerStep]

private theorem euler_units_cert_263 : eulerUnits 263 = 100419018731 := by
  change eulerStep 263 (eulerUnits 262) = 100419018731
  rw [euler_units_cert_262]
  norm_num [eulerStep]

private theorem euler_units_cert_264 : eulerUnits 264 = 100419018731 := by
  change eulerStep 264 (eulerUnits 263) = 100419018731
  rw [euler_units_cert_263]
  norm_num [eulerStep]

private theorem euler_units_cert_265 : eulerUnits 265 = 100419018731 := by
  change eulerStep 265 (eulerUnits 264) = 100419018731
  rw [euler_units_cert_264]
  norm_num [eulerStep]

private theorem euler_units_cert_266 : eulerUnits 266 = 100419018731 := by
  change eulerStep 266 (eulerUnits 265) = 100419018731
  rw [euler_units_cert_265]
  norm_num [eulerStep]

private theorem euler_units_cert_267 : eulerUnits 267 = 100419018731 := by
  change eulerStep 267 (eulerUnits 266) = 100419018731
  rw [euler_units_cert_266]
  norm_num [eulerStep]

private theorem euler_units_cert_268 : eulerUnits 268 = 100419018731 := by
  change eulerStep 268 (eulerUnits 267) = 100419018731
  rw [euler_units_cert_267]
  norm_num [eulerStep]

private theorem euler_units_cert_269 : eulerUnits 269 = 100793716563 := by
  change eulerStep 269 (eulerUnits 268) = 100793716563
  rw [euler_units_cert_268]
  norm_num [eulerStep]

private theorem euler_units_cert_270 : eulerUnits 270 = 100793716563 := by
  change eulerStep 270 (eulerUnits 269) = 100793716563
  rw [euler_units_cert_269]
  norm_num [eulerStep]

private theorem euler_units_cert_271 : eulerUnits 271 = 101167026625 := by
  change eulerStep 271 (eulerUnits 270) = 101167026625
  rw [euler_units_cert_270]
  norm_num [eulerStep]

private theorem euler_units_cert_272 : eulerUnits 272 = 101167026625 := by
  change eulerStep 272 (eulerUnits 271) = 101167026625
  rw [euler_units_cert_271]
  norm_num [eulerStep]

private theorem euler_units_cert_273 : eulerUnits 273 = 101167026625 := by
  change eulerStep 273 (eulerUnits 272) = 101167026625
  rw [euler_units_cert_272]
  norm_num [eulerStep]

private theorem euler_units_cert_274 : eulerUnits 274 = 101167026625 := by
  change eulerStep 274 (eulerUnits 273) = 101167026625
  rw [euler_units_cert_273]
  norm_num [eulerStep]

private theorem euler_units_cert_275 : eulerUnits 275 = 101167026625 := by
  change eulerStep 275 (eulerUnits 274) = 101167026625
  rw [euler_units_cert_274]
  norm_num [eulerStep]

private theorem euler_units_cert_276 : eulerUnits 276 = 101167026625 := by
  change eulerStep 276 (eulerUnits 275) = 101167026625
  rw [euler_units_cert_275]
  norm_num [eulerStep]

private theorem euler_units_cert_277 : eulerUnits 277 = 101533573823 := by
  change eulerStep 277 (eulerUnits 276) = 101533573823
  rw [euler_units_cert_276]
  norm_num [eulerStep]

private theorem euler_units_cert_278 : eulerUnits 278 = 101533573823 := by
  change eulerStep 278 (eulerUnits 277) = 101533573823
  rw [euler_units_cert_277]
  norm_num [eulerStep]

private theorem euler_units_cert_279 : eulerUnits 279 = 101533573823 := by
  change eulerStep 279 (eulerUnits 278) = 101533573823
  rw [euler_units_cert_278]
  norm_num [eulerStep]

private theorem euler_units_cert_280 : eulerUnits 280 = 101533573823 := by
  change eulerStep 280 (eulerUnits 279) = 101533573823
  rw [euler_units_cert_279]
  norm_num [eulerStep]

private theorem euler_units_cert_281 : eulerUnits 281 = 101896193730 := by
  change eulerStep 281 (eulerUnits 280) = 101896193730
  rw [euler_units_cert_280]
  norm_num [eulerStep]

private theorem euler_units_cert_282 : eulerUnits 282 = 101896193730 := by
  change eulerStep 282 (eulerUnits 281) = 101896193730
  rw [euler_units_cert_281]
  norm_num [eulerStep]

private theorem euler_units_cert_283 : eulerUnits 283 = 102257527751 := by
  change eulerStep 283 (eulerUnits 282) = 102257527751
  rw [euler_units_cert_282]
  norm_num [eulerStep]

private theorem euler_units_cert_284 : eulerUnits 284 = 102257527751 := by
  change eulerStep 284 (eulerUnits 283) = 102257527751
  rw [euler_units_cert_283]
  norm_num [eulerStep]

private theorem euler_units_cert_285 : eulerUnits 285 = 102257527751 := by
  change eulerStep 285 (eulerUnits 284) = 102257527751
  rw [euler_units_cert_284]
  norm_num [eulerStep]

theorem eulerUnits_286 : eulerUnits 286 = 102257527751 := by
  change eulerStep 286 (eulerUnits 285) = 102257527751
  rw [euler_units_cert_285]
  norm_num [eulerStep]

#print axioms eulerUnits_286
end LiuWang.Proof.Campaign20260915.Totient
