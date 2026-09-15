import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block016
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block017
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block018
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block019
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block020
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block021
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block022
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block023
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block024
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block025
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block026
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block027
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block028
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block029
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block030
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block031

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem row_1_0_64 : blockSum (rowCell 1) 0 64 ≤ (9084965559051441840677122283 / 3125000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_1_0_32 sum_1_32_32 (by norm_num)

theorem row_1_64_64 : blockSum (rowCell 1) 64 64 ≤ (3478251923456949637547345608269 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_1_64_32 sum_1_96_32 (by norm_num)

theorem row_1_0_128 : blockSum (rowCell 1) 0 128 ≤ (6385440902353411026564024738829 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_1_0_64 row_1_64_64 (by norm_num)

theorem row_1_128_64 : blockSum (rowCell 1) 128 64 ≤ (52629671486871175088864600427 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_1_128_32 sum_1_160_32 (by norm_num)

theorem row_1_192_64 : blockSum (rowCell 1) 192 64 ≤ (822190195920615084760578081 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_1_192_32 sum_1_224_32 (by norm_num)

theorem row_1_128_128 : blockSum (rowCell 1) 128 128 ≤ (21216306633932593052497955787 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_1_128_64 row_1_192_64 (by norm_num)

theorem row_1_0_256 : blockSum (rowCell 1) 0 256 ≤ (6597603968692736957089004296699 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_1_0_128 row_1_128_128 (by norm_num)

theorem row_1_256_64 : blockSum (rowCell 1) 256 64 ≤ (3617604090263193020250227 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_1_256_32 sum_1_288_32 (by norm_num)

theorem row_1_320_64 : blockSum (rowCell 1) 320 64 ≤ (142041736796015189089 / 40000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_1_320_32 sum_1_352_32 (by norm_num)

theorem row_1_256_128 : blockSum (rowCell 1) 256 128 ≤ (905288783420773349994363 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_1_256_64 row_1_320_64 (by norm_num)

theorem row_1_384_64 : blockSum (rowCell 1) 384 64 ≤ (203127824165735521 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_1_384_32 sum_1_416_32 (by norm_num)

theorem row_1_448_64 : blockSum (rowCell 1) 448 64 ≤ (99555291699001 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_1_448_32 sum_1_480_32 (by norm_num)

theorem row_1_384_128 : blockSum (rowCell 1) 384 128 ≤ (1016037341995473609 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_1_384_64 row_1_448_64 (by norm_num)

theorem row_1_256_256 : blockSum (rowCell 1) 256 256 ≤ (362115716575777739092467 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_1_256_128 row_1_384_128 (by norm_num)

theorem row_1_0_512 : blockSum (rowCell 1) 0 512 ≤ (6597607589849902714866395221369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 256) (n := 256) row_1_0_256 row_1_256_256 (by norm_num)

theorem checked_row_1 : quadUpper (1209 / 1 : ℝ) ≤ (6597607589849902714866395221369 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simpa only [blockSum, rowCell, Nat.zero_add, quadUpper, quadLower, div_one]
    using row_1_0_512

#print axioms checked_row_1

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
