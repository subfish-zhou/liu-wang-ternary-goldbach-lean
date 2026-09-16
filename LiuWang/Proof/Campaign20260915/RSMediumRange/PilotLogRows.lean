import LiuWang.Proof.Campaign20260915.RSMediumRange.LogLeaf

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

theorem prime_99614741 : Nat.Prime 99614741 := by norm_num

theorem log_99614741 :
    FixedBracket.log 99614741 26 = ⟨1841682070685298, 1841682072085322⟩ := by
  have hr : FixedBracket.ratio (99614741 - 2 ^ 26) (99614741 + 2 ^ 26) =
      ⟨19496865485844, 19496865485845⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99614743 : Nat.Prime 99614743 := by norm_num

theorem log_99614743 :
    FixedBracket.log 99614743 26 = ⟨1841682072693032, 1841682074093054⟩ := by
  have hr : FixedBracket.ratio (99614743 - 2 ^ 26) (99614743 + 2 ^ 26) =
      ⟨19496866451551, 19496866451552⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99614783 : Nat.Prime 99614783 := by norm_num

theorem log_99614783 :
    FixedBracket.log 99614783 26 = ⟨1841682112847720, 1841682114247742⟩ := by
  have hr : FixedBracket.ratio (99614783 - 2 ^ 26) (99614783 + 2 ^ 26) =
      ⟨19496885765700, 19496885765701⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99614791 : Nat.Prime 99614791 := by norm_num

theorem log_99614791 :
    FixedBracket.log 99614791 26 = ⟨1841682120878656, 1841682122278678⟩ := by
  have hr : FixedBracket.ratio (99614791 - 2 ^ 26) (99614791 + 2 ^ 26) =
      ⟨19496889628529, 19496889628530⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99614803 : Nat.Prime 99614803 := by norm_num

theorem log_99614803 :
    FixedBracket.log 99614803 26 = ⟨1841682132925060, 1841682134325082⟩ := by
  have hr : FixedBracket.ratio (99614803 - 2 ^ 26) (99614803 + 2 ^ 26) =
      ⟨19496895422771, 19496895422772⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99614821 : Nat.Prime 99614821 := by norm_num

theorem log_99614821 :
    FixedBracket.log 99614821 26 = ⟨1841682150994664, 1841682152394686⟩ := by
  have hr : FixedBracket.ratio (99614821 - 2 ^ 26) (99614821 + 2 ^ 26) =
      ⟨19496904114133, 19496904114134⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99614839 : Nat.Prime 99614839 := by norm_num

theorem log_99614839 :
    FixedBracket.log 99614839 26 = ⟨1841682169064262, 1841682170464284⟩ := by
  have hr : FixedBracket.ratio (99614839 - 2 ^ 26) (99614839 + 2 ^ 26) =
      ⟨19496912805493, 19496912805494⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99614881 : Nat.Prime 99614881 := by norm_num

theorem log_99614881 :
    FixedBracket.log 99614881 26 = ⟨1841682211226648, 1841682212626672⟩ := by
  have hr : FixedBracket.ratio (99614881 - 2 ^ 26) (99614881 + 2 ^ 26) =
      ⟨19496933085326, 19496933085327⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99614899 : Nat.Prime 99614899 := by norm_num

theorem log_99614899 :
    FixedBracket.log 99614899 26 = ⟨1841682229296238, 1841682230696260⟩ := by
  have hr : FixedBracket.ratio (99614899 - 2 ^ 26) (99614899 + 2 ^ 26) =
      ⟨19496941776680, 19496941776681⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99614959 : Nat.Prime 99614959 := by norm_num

theorem log_99614959 :
    FixedBracket.log 99614959 26 = ⟨1841682289528170, 1841682290928192⟩ := by
  have hr : FixedBracket.ratio (99614959 - 2 ^ 26) (99614959 + 2 ^ 26) =
      ⟨19496970747845, 19496970747846⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99614969 : Nat.Prime 99614969 := by norm_num

theorem log_99614969 :
    FixedBracket.log 99614969 26 = ⟨1841682299566824, 1841682300966846⟩ := by
  have hr : FixedBracket.ratio (99614969 - 2 ^ 26) (99614969 + 2 ^ 26) =
      ⟨19496975576371, 19496975576372⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99615007 : Nat.Prime 99615007 := by norm_num

theorem log_99615007 :
    FixedBracket.log 99615007 26 = ⟨1841682337713694, 1841682339113716⟩ := by
  have hr : FixedBracket.ratio (99615007 - 2 ^ 26) (99615007 + 2 ^ 26) =
      ⟨19496993924763, 19496993924764⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99615041 : Nat.Prime 99615041 := by norm_num

theorem log_99615041 :
    FixedBracket.log 99615041 26 = ⟨1841682371845090, 1841682373245112⟩ := by
  have hr : FixedBracket.ratio (99615041 - 2 ^ 26) (99615041 + 2 ^ 26) =
      ⟨19497010341738, 19497010341739⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99615049 : Nat.Prime 99615049 := by norm_num

theorem log_99615049 :
    FixedBracket.log 99615049 26 = ⟨1841682379876004, 1841682381276026⟩ := by
  have hr : FixedBracket.ratio (99615049 - 2 ^ 26) (99615049 + 2 ^ 26) =
      ⟨19497014204555, 19497014204556⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]

theorem prime_99615071 : Nat.Prime 99615071 := by norm_num

theorem log_99615071 :
    FixedBracket.log 99615071 26 = ⟨1841682401961020, 1841682403361042⟩ := by
  have hr : FixedBracket.ratio (99615071 - 2 ^ 26) (99615071 + 2 ^ 26) =
      ⟨19497024827299, 19497024827300⟩ := by
    norm_num [FixedBracket.ratio, fixedScale, divUp]
  unfold FixedBracket.log
  rw [hr]
  norm_num [FixedBracket.series, FixedBracket.oddPower, FixedBracket.mul,
    FixedBracket.divNat, divUp, fixedScale, Finset.sum_range_succ]


end LiuWang.Proof.Campaign20260915.RSMediumRange
