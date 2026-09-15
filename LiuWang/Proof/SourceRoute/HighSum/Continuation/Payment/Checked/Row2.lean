import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block032
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block033
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block034
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block035
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block036
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block037
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block038
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block039
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block040
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block041
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block042
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block043
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block044
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block045
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block046
import LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked.Block047

set_option autoImplicit false
noncomputable section
namespace LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked

theorem row_2_0_64 : blockSum (rowCell 2) 0 64 ≤ (157282233127351428945967120387 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_2_0_32 sum_2_32_32 (by norm_num)

theorem row_2_64_64 : blockSum (rowCell 2) 64 64 ≤ (302117057387001155020239521601 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_2_64_32 sum_2_96_32 (by norm_num)

theorem row_2_0_128 : blockSum (rowCell 2) 0 128 ≤ (114849822628588145991551660497 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_2_0_64 row_2_64_64 (by norm_num)

theorem row_2_128_64 : blockSum (rowCell 2) 128 64 ≤ (13971233497766918195140727401 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_2_128_32 sum_2_160_32 (by norm_num)

theorem row_2_192_64 : blockSum (rowCell 2) 192 64 ≤ (151183746565058843286370919 / 500000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_2_192_32 sum_2_224_32 (by norm_num)

theorem row_2_128_128 : blockSum (rowCell 2) 128 128 ≤ (176530215554149712980338729 / 6250000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_2_128_64 row_2_192_64 (by norm_num)

theorem row_2_0_256 : blockSum (rowCell 2) 0 256 ≤ (121911031250754134510765209657 / 250000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_2_0_128 row_2_128_128 (by norm_num)

theorem row_2_256_64 : blockSum (rowCell 2) 256 64 ≤ (169342157924631185868189 / 200000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_2_256_32 sum_2_288_32 (by norm_num)

theorem row_2_320_64 : blockSum (rowCell 2) 320 64 ≤ (487215296913564177 / 488281250000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_2_320_32 sum_2_352_32 (by norm_num)

theorem row_2_256_128 : blockSum (rowCell 2) 256 128 ≤ (847708606551234908775441 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_2_256_64 row_2_320_64 (by norm_num)

theorem row_2_384_64 : blockSum (rowCell 2) 384 64 ≤ (658205008770066209 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_2_384_32 sum_2_416_32 (by norm_num)

theorem row_2_448_64 : blockSum (rowCell 2) 448 64 ≤ (289241040591847 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 32) (n := 32) sum_2_448_32 sum_2_480_32 (by norm_num)

theorem row_2_384_128 : blockSum (rowCell 2) 384 128 ≤ (82311781226332257 / 125000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 64) (n := 64) row_2_384_64 row_2_448_64 (by norm_num)

theorem row_2_256_256 : blockSum (rowCell 2) 256 256 ≤ (847709265045484719433497 / 1000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 128) (n := 128) row_2_256_128 row_2_384_128 (by norm_num)

theorem row_2_0_512 : blockSum (rowCell 2) 0 512 ≤ (3901159781698252668222242177 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  exact block_upper (m := 256) (n := 256) row_2_0_256 row_2_256_256 (by norm_num)

theorem checked_row_2 : quadUpper (1302 / 1 : ℝ) ≤ (3901159781698252668222242177 / 8000000000000000000000000000000000000000000000000000000000 : ℝ) := by
  simpa only [blockSum, rowCell, Nat.zero_add, quadUpper, quadLower, div_one]
    using row_2_0_512

#print axioms checked_row_2

end LiuWang.Proof.SourceRoute.HighSum.Continuation.Payment.Checked
