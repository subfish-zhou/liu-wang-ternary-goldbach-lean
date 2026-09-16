import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Upper001
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Factors
import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

theorem upper_reach_1607 : UpperReach 1607 15650952934077 := by
  have hr := row_1607
  have hl := log_bounds hr.1
    (by change logScale (1607 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1601) (H := 15577131690370) (u := 73821243631)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1601

theorem upper_reach_1609 : UpperReach 1609 15724786615596 := by
  have hr := row_1609
  have hl := log_bounds hr.1
    (by change logScale (1609 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1607) (H := 15650952934077) (u := 73833681443)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1607

theorem upper_reach_1613 : UpperReach 1613 15798645126427 := by
  have hr := row_1613
  have hl := log_bounds hr.1
    (by change logScale (1613 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1609) (H := 15724786615596) (u := 73858510755)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1609

theorem upper_reach_1619 : UpperReach 1619 15872540766013 := by
  have hr := row_1619
  have hl := log_bounds hr.1
    (by change logScale (1619 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1613) (H := 15798645126427) (u := 73895639510)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1613

theorem upper_reach_1621 : UpperReach 1621 15946448751280 := by
  have hr := row_1621
  have hl := log_bounds hr.1
    (by change logScale (1621 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1619) (H := 15872540766013) (u := 73907985191)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1619

theorem upper_reach_1627 : UpperReach 1627 16020393682402 := by
  have hr := row_1627
  have hl := log_bounds hr.1
    (by change logScale (1627 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1621) (H := 15946448751280) (u := 73944931046)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1621

theorem upper_reach_1637 : UpperReach 1637 16094399888225 := by
  have hr := row_1637
  have hl := log_bounds hr.1
    (by change logScale (1637 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1627) (H := 16020393682402) (u := 74006205747)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 23, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1627

theorem upper_reach_1657 : UpperReach 1657 16168527528449 := by
  have hr := row_1657
  have hl := log_bounds hr.1
    (by change logScale (1657 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1637) (H := 16094399888225) (u := 74127640148)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 11, 2, 3, 2, 31, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1637

theorem upper_reach_1663 : UpperReach 1663 16242691313290 := by
  have hr := row_1663
  have hl := log_bounds hr.1
    (by change logScale (1663 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1657) (H := 16168527528449) (u := 74163784765)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1657

theorem upper_reach_1667 : UpperReach 1667 16316879122167 := by
  have hr := row_1667
  have hl := log_bounds hr.1
    (by change logScale (1667 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1663) (H := 16242691313290) (u := 74187808801)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1663

theorem upper_reach_1669 : UpperReach 1669 16391078921453 := by
  have hr := row_1669
  have hl := log_bounds hr.1
    (by change logScale (1669 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1667) (H := 16316879122167) (u := 74199799210)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1667

theorem upper_reach_1693 : UpperReach 1693 16465421495324 := by
  have hr := row_1693
  have hl := log_bounds hr.1
    (by change logScale (1693 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1669) (H := 16391078921453) (u := 74342573795)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1669

theorem upper_reach_1697 : UpperReach 1697 16539787668026 := by
  have hr := row_1697
  have hl := log_bounds hr.1
    (by change logScale (1697 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1693) (H := 16465421495324) (u := 74366172626)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1693

theorem upper_reach_1699 : UpperReach 1699 16614165619292 := by
  have hr := row_1699
  have hl := log_bounds hr.1
    (by change logScale (1699 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1697) (H := 16539787668026) (u := 74377951190)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1697

theorem upper_reach_1709 : UpperReach 1709 16688602256173 := by
  have hr := row_1709
  have hl := log_bounds hr.1
    (by change logScale (1709 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1699) (H := 16614165619292) (u := 74436636805)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2, 5, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1699

theorem upper_reach_1721 : UpperReach 1721 16763108864185 := by
  have hr := row_1721
  have hl := log_bounds hr.1
    (by change logScale (1721 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1709) (H := 16688602256173) (u := 74506607936)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 29, 2, 3, 2, 5, 2, 17, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1709

theorem upper_reach_1723 : UpperReach 1723 16837627086600 := by
  have hr := row_1723
  have hl := log_bounds hr.1
    (by change logScale (1723 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1721) (H := 16763108864185) (u := 74518222339)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1721

theorem upper_reach_1733 : UpperReach 1733 16912203179547 := by
  have hr := row_1733
  have hl := log_bounds hr.1
    (by change logScale (1733 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1723) (H := 16837627086600) (u := 74576092871)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 11, 2, 7, 2, 3, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1723

theorem upper_reach_1741 : UpperReach 1741 16986825328994 := by
  have hr := row_1741
  have hl := log_bounds hr.1
    (by change logScale (1741 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1733) (H := 16912203179547) (u := 74622149371)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 5, 2, 3, 2, 37, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1733

theorem upper_reach_1747 : UpperReach 1747 17061481882145 := by
  have hr := row_1747
  have hl := log_bounds hr.1
    (by change logScale (1747 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1741) (H := 16986825328994) (u := 74656553075)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1741

theorem upper_reach_1753 : UpperReach 1753 17136172721044 := by
  have hr := row_1753
  have hl := log_bounds hr.1
    (by change logScale (1753 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1747) (H := 17061481882145) (u := 74690838823)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 17, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1747

theorem upper_reach_1759 : UpperReach 1759 17210897728541 := by
  have hr := row_1759
  have hl := log_bounds hr.1
    (by change logScale (1759 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1753) (H := 17136172721044) (u := 74725007421)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 7, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1753

theorem upper_reach_1777 : UpperReach 1777 17285724546872 := by
  have hr := row_1777
  have hl := log_bounds hr.1
    (by change logScale (1777 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1759) (H := 17210897728541) (u := 74826818255)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 41, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1759

theorem upper_reach_1783 : UpperReach 1783 17360585073100 := by
  have hr := row_1783
  have hl := log_bounds hr.1
    (by change logScale (1783 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact upper_reach_next (a := 1777) (H := 17285724546872) (u := 74860526152)
    (by norm_num) (by norm_num) hr.1 (primeGap_of_factors (ds := [2, 3, 2, 13, 2]) (by decide +kernel) (by decide +kernel)) hl.2
    (by norm_num) upper_reach_1777

#print axioms upper_reach_1783

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
