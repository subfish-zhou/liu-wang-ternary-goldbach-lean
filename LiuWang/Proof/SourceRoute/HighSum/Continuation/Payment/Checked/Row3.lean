import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block048
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block049
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block050
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block051
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block052
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block053
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block054
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block055
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block056
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block057
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block058
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block059
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block060
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block061
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block062
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block063

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem row_3_0_64 : blockSum (rowCell 3) 0 64 ≤ (4394382708484104288889824389 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_3_0_32 sum_3_32_32 (by norm_num)

theorem row_3_64_64 : blockSum (rowCell 3) 64 64 ≤ (26845318106282698137253978701 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_3_64_32 sum_3_96_32 (by norm_num)

theorem row_3_0_128 : blockSum (rowCell 3) 0 128 ≤ (35634083523250906715033627479 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_3_0_64 row_3_64_64 (by norm_num)

theorem row_3_128_64 : blockSum (rowCell 3) 128 64 ≤ (3732408005454438133952517663 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_3_128_32 sum_3_160_32 (by norm_num)

theorem row_3_192_64 : blockSum (rowCell 3) 192 64 ≤ (27858896643640518599607469 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_3_192_32 sum_3_224_32 (by norm_num)

theorem row_3_128_128 : blockSum (rowCell 3) 128 128 ≤ (3788125798741719171151732601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_3_128_64 row_3_192_64 (by norm_num)

theorem row_3_0_256 : blockSum (rowCell 3) 0 256 ≤ (492777616524907823577317001 / 12500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_3_0_128 row_3_128_128 (by norm_num)

theorem row_3_256_64 : blockSum (rowCell 3) 256 64 ≤ (9917785352396976187093 / 50000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_3_256_32 sum_3_288_32 (by norm_num)

theorem row_3_320_64 : blockSum (rowCell 3) 320 64 ≤ (56101529029917062923 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_3_320_32 sum_3_352_32 (by norm_num)

theorem row_3_256_128 : blockSum (rowCell 3) 256 128 ≤ (7945448587723564362259 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_3_256_64 row_3_320_64 (by norm_num)

theorem row_3_384_64 : blockSum (rowCell 3) 384 64 ≤ (42667266989694357 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_3_384_32 sum_3_416_32 (by norm_num)

theorem row_3_448_64 : blockSum (rowCell 3) 448 64 ≤ (3283096610811 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_3_448_32 sum_3_480_32 (by norm_num)

theorem row_3_384_128 : blockSum (rowCell 3) 384 128 ≤ (213441394040017737 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_3_384_64 row_3_448_64 (by norm_num)

theorem row_3_256_256 : blockSum (rowCell 3) 256 256 ≤ (49659107033620787268553 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_3_256_128 row_3_384_128 (by norm_num)

theorem row_3_0_512 : blockSum (rowCell 3) 0 512 ≤ (9855601989605190092333608573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 256) (n := 256) row_3_0_256 row_3_256_256 (by norm_num)

theorem checked_row_3 : quadUpper (1395 / 1 : ℝ) ≤ (9855601989605190092333608573 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simpa only [blockSum, rowCell, Nat.zero_add, quadUpper, quadLower, div_one]
    using row_3_0_512

#print axioms checked_row_3

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
