import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block000
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block001
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block002
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block003
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block004
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block005
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block006
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block007
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block008
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block009
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block010
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block011
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block012
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block013
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block014
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block015

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem row_0_0_64 : blockSum (rowCell 0) 0 64 ≤ (55916751465977237469000060607733 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_0_0_32 sum_0_32_32 (by norm_num)

theorem row_0_64_64 : blockSum (rowCell 0) 64 64 ≤ (40925299830085231018689257732837 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_0_64_32 sum_0_96_32 (by norm_num)

theorem row_0_0_128 : blockSum (rowCell 0) 0 128 ≤ (9684205129606246848768931834057 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_0_0_64 row_0_64_64 (by norm_num)

theorem row_0_128_64 : blockSum (rowCell 0) 128 64 ≤ (797664611849844432371092568413 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_0_128_32 sum_0_160_32 (by norm_num)

theorem row_0_192_64 : blockSum (rowCell 0) 192 64 ≤ (896063303135134265152506989 / 100000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_0_192_32 sum_0_224_32 (by norm_num)

theorem row_0_128_128 : blockSum (rowCell 0) 128 128 ≤ (401072464182760051848427551679 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_0_128_64 row_0_192_64 (by norm_num)

theorem row_0_0_256 : blockSum (rowCell 0) 0 256 ≤ (49223170576396754347541514273643 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_0_0_128 row_0_128_128 (by norm_num)

theorem row_0_256_64 : blockSum (rowCell 0) 256 64 ≤ (15469794096135921513561759 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_0_256_32 sum_0_288_32 (by norm_num)

theorem row_0_320_64 : blockSum (rowCell 0) 320 64 ≤ (6321544349858480857027 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_0_320_32 sum_0_352_32 (by norm_num)

theorem row_0_256_128 : blockSum (rowCell 0) 256 128 ≤ (15482437184835638475275813 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_0_256_64 row_0_320_64 (by norm_num)

theorem row_0_384_64 : blockSum (rowCell 0) 384 64 ≤ (195946061862156569 / 31250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_0_384_32 sum_0_416_32 (by norm_num)

theorem row_0_448_64 : blockSum (rowCell 0) 448 64 ≤ (2193387847292843 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_0_448_32 sum_0_480_32 (by norm_num)

theorem row_0_384_128 : blockSum (rowCell 0) 384 128 ≤ (6272467367436303051 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_0_384_64 row_0_448_64 (by norm_num)

theorem row_0_256_256 : blockSum (rowCell 0) 256 256 ≤ (967652716081437869473679 / 62500000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_0_256_128 row_0_384_128 (by norm_num)

theorem row_0_0_512 : blockSum (rowCell 0) 0 512 ≤ (1968927132704739319961778802523 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 256) (n := 256) row_0_0_256 row_0_256_256 (by norm_num)

theorem checked_row_0 : quadUpper (1116 / 1 : ℝ) ≤ (1968927132704739319961778802523 / 20000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simpa only [blockSum, rowCell, Nat.zero_add, quadUpper, quadLower, div_one]
    using row_0_0_512

#print axioms checked_row_0

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
