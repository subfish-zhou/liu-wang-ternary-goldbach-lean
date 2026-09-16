import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block002 : List ℕ := [1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783]

theorem complete_Block002 :
    ∀ p ∈ Finset.Ioc 1601 1783, p.Prime ↔ p ∈ primes_Block002 := by
  decide +kernel

theorem row_1607 :
    (1607 : ℕ).Prime ∧ logScale (1607 : ℚ) = 10 ∧
      (73821243631 : ℤ) = ⌊logCenter (1607 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1607 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1607 : Reach 1607 15650952845116 132007431826 := by
  have hr := row_1607
  have hl := log_bounds hr.1
    (by change logScale (1607 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1601) (T := 15577131601485) (U := 131925286566)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1601

theorem row_1609 :
    (1609 : ℕ).Prime ∧ logScale (1609 : ℚ) = 10 ∧
      (73833681443 : ℤ) = ⌊logCenter (1609 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1609 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1609 : Reach 1609 15724786526559 132089526001 := by
  have hr := row_1609
  have hl := log_bounds hr.1
    (by change logScale (1609 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1607) (T := 15650952845116) (U := 132007431826)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1607

theorem row_1613 :
    (1613 : ℕ).Prime ∧ logScale (1613 : ℚ) = 10 ∧
      (73858510755 : ℤ) = ⌊logCenter (1613 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1613 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1613 : Reach 1613 15798645037314 132171467395 := by
  have hr := row_1613
  have hl := log_bounds hr.1
    (by change logScale (1613 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1609) (T := 15724786526559) (U := 132089526001)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1609

theorem row_1619 :
    (1619 : ℕ).Prime ∧ logScale (1619 : ℚ) = 10 ∧
      (73895639510 : ℤ) = ⌊logCenter (1619 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1619 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1619 : Reach 1619 15872540676824 132253155571 := by
  have hr := row_1619
  have hl := log_bounds hr.1
    (by change logScale (1619 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1613) (T := 15798645037314) (U := 132171467395)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1613

theorem row_1621 :
    (1621 : ℕ).Prime ∧ logScale (1621 : ℚ) = 10 ∧
      (73907985191 : ℤ) = ⌊logCenter (1621 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1621 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1621 : Reach 1621 15946448662015 132334793322 := by
  have hr := row_1621
  have hl := log_bounds hr.1
    (by change logScale (1621 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1619) (T := 15872540676824) (U := 132253155571)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1619

theorem row_1627 :
    (1627 : ℕ).Prime ∧ logScale (1627 : ℚ) = 10 ∧
      (73944931046 : ℤ) = ⌊logCenter (1627 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1627 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1627 : Reach 1627 16020393593061 132416180034 := by
  have hr := row_1627
  have hl := log_bounds hr.1
    (by change logScale (1627 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1621) (T := 15946448662015) (U := 132334793322)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1621

theorem row_1637 :
    (1637 : ℕ).Prime ∧ logScale (1637 : ℚ) = 10 ∧
      (74006205747 : ℤ) = ⌊logCenter (1637 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1637 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1637 : Reach 1637 16094399798808 132497119020 := by
  have hr := row_1637
  have hl := log_bounds hr.1
    (by change logScale (1637 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1627) (T := 16020393593061) (U := 132416180034)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1627

theorem row_1657 :
    (1657 : ℕ).Prime ∧ logScale (1657 : ℚ) = 10 ∧
      (74127640148 : ℤ) = ⌊logCenter (1657 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1657 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1657 : Reach 1657 16168527438956 132577129358 := by
  have hr := row_1657
  have hl := log_bounds hr.1
    (by change logScale (1657 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1637) (T := 16094399798808) (U := 132497119020)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1637

theorem row_1663 :
    (1663 : ℕ).Prime ∧ logScale (1663 : ℚ) = 10 ∧
      (74163784765 : ℤ) = ⌊logCenter (1663 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1663 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1663 : Reach 1663 16242691223721 132656898991 := by
  have hr := row_1663
  have hl := log_bounds hr.1
    (by change logScale (1663 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1657) (T := 16168527438956) (U := 132577129358)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1657

theorem row_1667 :
    (1667 : ℕ).Prime ∧ logScale (1667 : ℚ) = 10 ∧
      (74187808801 : ℤ) = ⌊logCenter (1667 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1667 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1667 : Reach 1667 16316879032522 132736524981 := by
  have hr := row_1667
  have hl := log_bounds hr.1
    (by change logScale (1667 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1663) (T := 16242691223721) (U := 132656898991)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1663

theorem row_1669 :
    (1669 : ℕ).Prime ∧ logScale (1669 : ℚ) = 10 ∧
      (74199799210 : ℤ) = ⌊logCenter (1669 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1669 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1669 : Reach 1669 16391078831732 132816103234 := by
  have hr := row_1669
  have hl := log_bounds hr.1
    (by change logScale (1669 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1667) (T := 16316879032522) (U := 132736524981)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1667

theorem row_1693 :
    (1693 : ℕ).Prime ∧ logScale (1693 : ℚ) = 10 ∧
      (74342573795 : ℤ) = ⌊logCenter (1693 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1693 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1693 : Reach 1693 16465421405527 132894599749 := by
  have hr := row_1693
  have hl := log_bounds hr.1
    (by change logScale (1693 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1669) (T := 16391078831732) (U := 132816103234)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1669

theorem row_1697 :
    (1697 : ℕ).Prime ∧ logScale (1697 : ℚ) = 10 ∧
      (74366172626 : ℤ) = ⌊logCenter (1697 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1697 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1697 : Reach 1697 16539787578153 132972957414 := by
  have hr := row_1697
  have hl := log_bounds hr.1
    (by change logScale (1697 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1693) (T := 16465421405527) (U := 132894599749)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1693

theorem row_1699 :
    (1699 : ℕ).Prime ∧ logScale (1699 : ℚ) = 10 ∧
      (74377951190 : ℤ) = ⌊logCenter (1699 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1699 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1699 : Reach 1699 16614165529343 133051268932 := by
  have hr := row_1699
  have hl := log_bounds hr.1
    (by change logScale (1699 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1697) (T := 16539787578153) (U := 132972957414)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1697

theorem row_1709 :
    (1709 : ℕ).Prime ∧ logScale (1709 : ℚ) = 10 ∧
      (74436636805 : ℤ) = ⌊logCenter (1709 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1709 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1709 : Reach 1709 16688602166148 133129167802 := by
  have hr := row_1709
  have hl := log_bounds hr.1
    (by change logScale (1709 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1699) (T := 16614165529343) (U := 133051268932)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1699

theorem row_1721 :
    (1721 : ℕ).Prime ∧ logScale (1721 : ℚ) = 10 ∧
      (74506607936 : ℤ) = ⌊logCenter (1721 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1721 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1721 : Reach 1721 16763108774084 133206568481 := by
  have hr := row_1721
  have hl := log_bounds hr.1
    (by change logScale (1721 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1709) (T := 16688602166148) (U := 133129167802)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1709

theorem row_1723 :
    (1723 : ℕ).Prime ∧ logScale (1723 : ℚ) = 10 ∧
      (74518222339 : ℤ) = ⌊logCenter (1723 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1723 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1723 : Reach 1723 16837626996423 133283924212 := by
  have hr := row_1723
  have hl := log_bounds hr.1
    (by change logScale (1723 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1721) (T := 16763108774084) (U := 133206568481)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1721

theorem row_1733 :
    (1733 : ℕ).Prime ∧ logScale (1733 : ℚ) = 10 ∧
      (74576092871 : ℤ) = ⌊logCenter (1733 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1733 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1733 : Reach 1733 16912203089294 133360877979 := by
  have hr := row_1733
  have hl := log_bounds hr.1
    (by change logScale (1733 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1723) (T := 16837626996423) (U := 133283924212)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1723

theorem row_1741 :
    (1741 : ℕ).Prime ∧ logScale (1741 : ℚ) = 10 ∧
      (74622149371 : ℤ) = ⌊logCenter (1741 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1741 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1741 : Reach 1741 16986825238665 133437522162 := by
  have hr := row_1741
  have hl := log_bounds hr.1
    (by change logScale (1741 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1733) (T := 16912203089294) (U := 133360877979)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1733

theorem row_1747 :
    (1747 : ℕ).Prime ∧ logScale (1747 : ℚ) = 10 ∧
      (74656553075 : ℤ) = ⌊logCenter (1747 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1747 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1747 : Reach 1747 17061481791740 133513946860 := by
  have hr := row_1747
  have hl := log_bounds hr.1
    (by change logScale (1747 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1741) (T := 16986825238665) (U := 133437522162)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1741

theorem row_1753 :
    (1753 : ℕ).Prime ∧ logScale (1753 : ℚ) = 10 ∧
      (74690838823 : ℤ) = ⌊logCenter (1753 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1753 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1753 : Reach 1753 17136172630563 133590153451 := by
  have hr := row_1753
  have hl := log_bounds hr.1
    (by change logScale (1753 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1747) (T := 17061481791740) (U := 133513946860)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1747

theorem row_1759 :
    (1759 : ℕ).Prime ∧ logScale (1759 : ℚ) = 10 ∧
      (74725007421 : ℤ) = ⌊logCenter (1759 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1759 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1759 : Reach 1759 17210897637984 133666143300 := by
  have hr := row_1759
  have hl := log_bounds hr.1
    (by change logScale (1759 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1753) (T := 17136172630563) (U := 133590153451)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1753

theorem row_1777 :
    (1777 : ℕ).Prime ∧ logScale (1777 : ℚ) = 10 ∧
      (74826818255 : ℤ) = ⌊logCenter (1777 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1777 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1777 : Reach 1777 17285724456239 133741405769 := by
  have hr := row_1777
  have hl := log_bounds hr.1
    (by change logScale (1777 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1759) (T := 17210897637984) (U := 133666143300)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1759

theorem row_1783 :
    (1783 : ℕ).Prime ∧ logScale (1783 : ℚ) = 10 ∧
      (74860526152 : ℤ) = ⌊logCenter (1783 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1783 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1783 : Reach 1783 17360584982391 133816457063 := by
  have hr := row_1783
  have hl := log_bounds hr.1
    (by change logScale (1783 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1777) (T := 17285724456239) (U := 133741405769)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1777

#print axioms reach_1783

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
