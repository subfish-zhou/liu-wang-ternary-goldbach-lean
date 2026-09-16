import LiuWang.Proof.Campaign20260915.RSFiniteExtension.Block003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension
open Totient
noncomputable section

def primes_Block004 : List ℕ := [1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143]

theorem complete_Block004 :
    ∀ p ∈ Finset.Ioc 1987 2143, p.Prime ↔ p ∈ primes_Block004 := by
  decide +kernel

theorem row_1993 :
    (1993 : ℕ).Prime ∧ logScale (1993 : ℚ) = 10 ∧
      (75973963176 : ℤ) = ⌊logCenter (1993 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1993 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1993 : Reach 1993 19246393959402 135601660973 := by
  have hr := row_1993
  have hl := log_bounds hr.1
    (by change logScale (1993 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1987) (T := 19170419996226) (U := 135533622006)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1987

theorem row_1997 :
    (1997 : ℕ).Prime ∧ logScale (1997 : ℚ) = 10 ∧
      (75994013308 : ℤ) = ⌊logCenter (1997 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1997 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1997 : Reach 1997 19322387972710 135669597677 := by
  have hr := row_1997
  have hl := log_bounds hr.1
    (by change logScale (1997 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1993) (T := 19246393959402) (U := 135601660973)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1993

theorem row_1999 :
    (1999 : ℕ).Prime ∧ logScale (1999 : ℚ) = 10 ∧
      (76004023318 : ℤ) = ⌊logCenter (1999 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (1999 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_1999 : Reach 1999 19398391996028 135737500379 := by
  have hr := row_1999
  have hl := log_bounds hr.1
    (by change logScale (1999 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1997) (T := 19322387972710) (U := 135669597677)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1997

theorem row_2003 :
    (2003 : ℕ).Prime ∧ logScale (2003 : ℚ) = 10 ∧
      (76024013330 : ℤ) = ⌊logCenter (2003 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2003 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2003 : Reach 2003 19474416009358 135805301329 := by
  have hr := row_2003
  have hl := log_bounds hr.1
    (by change logScale (2003 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 1999) (T := 19398391996028) (U := 135737500379)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_1999

theorem row_2011 :
    (2011 : ℕ).Prime ∧ logScale (2011 : ℚ) = 10 ∧
      (76063873871 : ℤ) = ⌊logCenter (2011 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2011 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2011 : Reach 2011 19550479883229 135872866156 := by
  have hr := row_2011
  have hl := log_bounds hr.1
    (by change logScale (2011 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2003) (T := 19474416009358) (U := 135805301329)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2003

theorem row_2017 :
    (2017 : ℕ).Prime ∧ logScale (2017 : ℚ) = 10 ∧
      (76093665353 : ℤ) = ⌊logCenter (2017 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2017 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2017 : Reach 2017 19626573548582 135940263412 := by
  have hr := row_2017
  have hl := log_bounds hr.1
    (by change logScale (2017 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2011) (T := 19550479883229) (U := 135872866156)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2011

theorem row_2027 :
    (2027 : ℕ).Prime ∧ logScale (2027 : ℚ) = 10 ∧
      (76143121438 : ℤ) = ⌊logCenter (2027 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2027 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2027 : Reach 2027 19702716670020 136007361272 := by
  have hr := row_2027
  have hl := log_bounds hr.1
    (by change logScale (2027 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2017) (T := 19626573548582) (U := 135940263412)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2017

theorem row_2029 :
    (2029 : ℕ).Prime ∧ logScale (2029 : ℚ) = 10 ∧
      (76152983372 : ℤ) = ⌊logCenter (2029 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2029 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2029 : Reach 2029 19778869653392 136074426046 := by
  have hr := row_2029
  have hl := log_bounds hr.1
    (by change logScale (2029 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2027) (T := 19702716670020) (U := 136007361272)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2027

theorem row_2039 :
    (2039 : ℕ).Prime ∧ logScale (2039 : ℚ) = 10 ∧
      (76202147679 : ℤ) = ⌊logCenter (2039 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2039 : ℚ) = 10 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2039 : Reach 2039 19855071801071 136141194656 := by
  have hr := row_2039
  have hl := log_bounds hr.1
    (by change logScale (2039 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2029) (T := 19778869653392) (U := 136074426046)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2029

theorem row_2053 :
    (2053 : ℕ).Prime ∧ logScale (2053 : ℚ) = 11 ∧
      (76270574141 : ℤ) = ⌊logCenter (2053 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2053 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2053 : Reach 2053 19931342375212 136207540268 := by
  have hr := row_2053
  have hl := log_bounds hr.1
    (by change logScale (2053 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2039) (T := 19855071801071) (U := 136141194656)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2039

theorem row_2063 :
    (2063 : ℕ).Prime ∧ logScale (2063 : ℚ) = 11 ∧
      (76319165102 : ℤ) = ⌊logCenter (2063 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2063 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2063 : Reach 2063 20007661540314 136273596302 := by
  have hr := row_2063
  have hl := log_bounds hr.1
    (by change logScale (2063 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2053) (T := 19931342375212) (U := 136207540268)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2053

theorem row_2069 :
    (2069 : ℕ).Prime ∧ logScale (2069 : ℚ) = 11 ∧
      (76348206748 : ℤ) = ⌊logCenter (2069 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2069 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2069 : Reach 2069 20084009747062 136339492626 := by
  have hr := row_2069
  have hl := log_bounds hr.1
    (by change logScale (2069 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2063) (T := 20007661540314) (U := 136273596302)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2063

theorem row_2081 :
    (2081 : ℕ).Prime ∧ logScale (2081 : ℚ) = 11 ∧
      (76406038235 : ℤ) = ⌊logCenter (2081 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2081 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2081 : Reach 2081 20160415785297 136405040459 := by
  have hr := row_2081
  have hl := log_bounds hr.1
    (by change logScale (2081 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2069) (T := 20084009747062) (U := 136339492626)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2069

theorem row_2083 :
    (2083 : ℕ).Prime ∧ logScale (2083 : ℚ) = 11 ∧
      (76415644384 : ℤ) = ⌊logCenter (2083 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2083 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2083 : Reach 2083 20236831429681 136470556809 := by
  have hr := row_2083
  have hl := log_bounds hr.1
    (by change logScale (2083 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2081) (T := 20160415785297) (U := 136405040459)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2081

theorem row_2087 :
    (2087 : ℕ).Prime ∧ logScale (2087 : ℚ) = 11 ∧
      (76434829042 : ℤ) = ⌊logCenter (2087 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2087 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2087 : Reach 2087 20313266258723 136535978936 := by
  have hr := row_2087
  have hl := log_bounds hr.1
    (by change logScale (2087 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2083) (T := 20236831429681) (U := 136470556809)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2083

theorem row_2089 :
    (2089 : ℕ).Prime ∧ logScale (2089 : ℚ) = 11 ∧
      (76444407586 : ℤ) = ⌊logCenter (2089 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2089 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2089 : Reach 2089 20389710666309 136601369731 := by
  have hr := row_2089
  have hl := log_bounds hr.1
    (by change logScale (2089 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2087) (T := 20313266258723) (U := 136535978936)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2087

theorem row_2099 :
    (2099 : ℕ).Prime ∧ logScale (2099 : ℚ) = 11 ∧
      (76492163169 : ℤ) = ⌊logCenter (2099 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2099 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2099 : Reach 2099 20466202829478 136666480013 := by
  have hr := row_2099
  have hl := log_bounds hr.1
    (by change logScale (2099 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2089) (T := 20389710666309) (U := 136601369731)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2089

theorem row_2111 :
    (2111 : ℕ).Prime ∧ logScale (2111 : ℚ) = 11 ∧
      (76549170449 : ℤ) = ⌊logCenter (2111 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2111 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2111 : Reach 2111 20542751999927 136731250857 := by
  have hr := row_2111
  have hl := log_bounds hr.1
    (by change logScale (2111 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2099) (T := 20466202829478) (U := 136666480013)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2099

theorem row_2113 :
    (2113 : ℕ).Prime ∧ logScale (2113 : ℚ) = 11 ∧
      (76558640147 : ℤ) = ⌊logCenter (2113 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2113 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2113 : Reach 2113 20619310640074 136795991033 := by
  have hr := row_2113
  have hl := log_bounds hr.1
    (by change logScale (2113 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2111) (T := 20542751999927) (U := 136731250857)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2111

theorem row_2129 :
    (2129 : ℕ).Prime ∧ logScale (2129 : ℚ) = 11 ∧
      (76634076620 : ℤ) = ⌊logCenter (2129 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2129 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2129 : Reach 2129 20695944716694 136860274864 := by
  have hr := row_2129
  have hl := log_bounds hr.1
    (by change logScale (2129 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2113) (T := 20619310640074) (U := 136795991033)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2113

theorem row_2131 :
    (2131 : ℕ).Prime ∧ logScale (2131 : ℚ) = 11 ∧
      (76643466292 : ℤ) = ⌊logCenter (2131 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2131 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2131 : Reach 2131 20772588182986 136924528515 := by
  have hr := row_2131
  have hl := log_bounds hr.1
    (by change logScale (2131 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2129) (T := 20695944716694) (U := 136860274864)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2129

theorem row_2137 :
    (2137 : ℕ).Prime ∧ logScale (2137 : ℚ) = 11 ∧
      (76671582524 : ℤ) = ⌊logCenter (2137 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2137 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2137 : Reach 2137 20849259765510 136988631759 := by
  have hr := row_2137
  have hl := log_bounds hr.1
    (by change logScale (2137 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2131) (T := 20772588182986) (U := 136924528515)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2131

theorem row_2141 :
    (2141 : ℕ).Prime ∧ logScale (2141 : ℚ) = 11 ∧
      (76690282857 : ℤ) = ⌊logCenter (2141 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2141 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2141 : Reach 2141 20925950048367 137052645139 := by
  have hr := row_2141
  have hl := log_bounds hr.1
    (by change logScale (2141 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2137) (T := 20849259765510) (U := 136988631759)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2137

theorem row_2143 :
    (2143 : ℕ).Prime ∧ logScale (2143 : ℚ) = 11 ∧
      (76699619926 : ℤ) = ⌊logCenter (2143 : ℚ) * 10000000000⌋ := by
  refine ⟨by norm_num, ?_, ?_⟩
  · decide +kernel
  · have hs : logScale (2143 : ℚ) = 11 := by decide +kernel
    norm_num [logCenter, hs, logSeries, Finset.sum_range_succ]

theorem reach_2143 : Reach 2143 21002649668293 137116628634 := by
  have hr := row_2143
  have hl := log_bounds hr.1
    (by change logScale (2143 : ℚ) ≤ 13; rw [hr.2.1]; norm_num) hr.2.2
  exact reach_next (a := 2141) (T := 20925950048367) (U := 137052645139)
    (by norm_num) (by norm_num) hr.1 (by decide +kernel)
    (by norm_num) hl.1 hl.2 (by norm_num) (by norm_num [lowerEnvelope])
    (by norm_num) reach_2141

#print axioms reach_2143

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
