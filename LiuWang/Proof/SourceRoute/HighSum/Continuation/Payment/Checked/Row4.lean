import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block064
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block065
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block066
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block067
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block068
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block069
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block070
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block071
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block072
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block073
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block074
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block075
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block076
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block077
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block078
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block079

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem row_4_0_64 : blockSum (rowCell 4) 0 64 ≤ (135220494657610564676969781 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_4_0_32 sum_4_32_32 (by norm_num)

theorem row_4_64_64 : blockSum (rowCell 4) 64 64 ≤ (3010320986027677722122866371 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_4_64_32 sum_4_96_32 (by norm_num)

theorem row_4_0_128 : blockSum (rowCell 4) 0 128 ≤ (15421796310550975005415710009 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_4_0_64 row_4_64_64 (by norm_num)

theorem row_4_128_64 : blockSum (rowCell 4) 128 64 ≤ (1910793242258670233517977499 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_4_128_32 sum_4_160_32 (by norm_num)

theorem row_4_192_64 : blockSum (rowCell 4) 192 64 ≤ (15861087632769542217897727 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_4_192_32 sum_4_224_32 (by norm_num)

theorem row_4_128_128 : blockSum (rowCell 4) 128 128 ≤ (1942515417524209317953772953 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_4_128_64 row_4_192_64 (by norm_num)

theorem row_4_0_256 : blockSum (rowCell 4) 0 256 ≤ (8682155864037592161684741481 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_4_0_128 row_4_128_128 (by norm_num)

theorem row_4_256_64 : blockSum (rowCell 4) 256 64 ≤ (122303547454271225105437 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_4_256_32 sum_4_288_32 (by norm_num)

theorem row_4_320_64 : blockSum (rowCell 4) 320 64 ≤ (183775700963064177933 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_4_320_32 sum_4_352_32 (by norm_num)

theorem row_4_256_128 : blockSum (rowCell 4) 256 128 ≤ (12248732315523428928337 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_4_256_64 row_4_320_64 (by norm_num)

theorem row_4_384_64 : blockSum (rowCell 4) 384 64 ≤ (146551896825629829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_4_384_32 sum_4_416_32 (by norm_num)

theorem row_4_448_64 : blockSum (rowCell 4) 448 64 ≤ (9370231055901 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_4_448_32 sum_4_480_32 (by norm_num)

theorem row_4_384_128 : blockSum (rowCell 4) 384 128 ≤ (146626858674077037 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_4_384_64 row_4_448_64 (by norm_num)

theorem row_4_256_256 : blockSum (rowCell 4) 256 256 ≤ (122487469782092963360407 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_4_256_128 row_4_384_128 (by norm_num)

theorem row_4_0_512 : blockSum (rowCell 4) 0 512 ≤ (17364434215544966416332843369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 256) (n := 256) row_4_0_256 row_4_256_256 (by norm_num)

theorem checked_row_4 : quadUpper (1426 / 1 : ℝ) ≤ (17364434215544966416332843369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simpa only [blockSum, rowCell, Nat.zero_add, quadUpper, quadLower, div_one]
    using row_4_0_512

#print axioms checked_row_4

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
