import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
Integer certificates for the finite sum following Liu--Wang (4.5).
The computation uses Euler's product formula, not an external totient table.
-/

set_option autoImplicit false

namespace LiuWang.Proof.ArithmeticBounds

open scoped BigOperators

def certificateTotient (q : Nat) : Nat :=
  (q / ∏ p ∈ q.primeFactors, p) * ∏ p ∈ q.primeFactors, (p - 1)

theorem certificateTotient_eq (q : Nat) :
    certificateTotient q = q.totient :=
  (Nat.totient_eq_div_primeFactors_mul q).symm

def roundedSquareWeight (q : Nat) : Nat :=
  if Squarefree q then 10000 * q ^ 2 / certificateTotient q ^ 2 + 1 else 0

private theorem finiteSum_block_01 :
    ∑ q ∈ Finset.Ico 1 51, roundedSquareWeight q ≤ 1061900 := by
  decide +kernel

private theorem finiteSum_block_02 :
    ∑ q ∈ Finset.Ico 51 101, roundedSquareWeight q ≤ 884100 := by
  decide +kernel

private theorem finiteSum_block_03 :
    ∑ q ∈ Finset.Ico 101 151, roundedSquareWeight q ≤ 1019700 := by
  decide +kernel

private theorem finiteSum_block_04 :
    ∑ q ∈ Finset.Ico 151 201, roundedSquareWeight q ≤ 953100 := by
  decide +kernel

private theorem finiteSum_block_05 :
    ∑ q ∈ Finset.Ico 201 251, roundedSquareWeight q ≤ 1056000 := by
  decide +kernel

private theorem finiteSum_block_06 :
    ∑ q ∈ Finset.Ico 251 301, roundedSquareWeight q ≤ 914400 := by
  decide +kernel

private theorem finiteSum_block_07 :
    ∑ q ∈ Finset.Ico 301 351, roundedSquareWeight q ≤ 925200 := by
  decide +kernel

private theorem finiteSum_block_08 :
    ∑ q ∈ Finset.Ico 351 401, roundedSquareWeight q ≤ 1022300 := by
  decide +kernel

private theorem finiteSum_block_09 :
    ∑ q ∈ Finset.Ico 401 451, roundedSquareWeight q ≤ 1039500 := by
  decide +kernel

private theorem finiteSum_block_10 :
    ∑ q ∈ Finset.Ico 451 501, roundedSquareWeight q ≤ 990700 := by
  decide +kernel

private theorem finiteSum_block_11 :
    ∑ q ∈ Finset.Ico 501 551, roundedSquareWeight q ≤ 1037500 := by
  decide +kernel

private theorem finiteSum_block_12 :
    ∑ q ∈ Finset.Ico 551 601, roundedSquareWeight q ≤ 938600 := by
  decide +kernel

private theorem finiteSum_block_13 :
    ∑ q ∈ Finset.Ico 601 651, roundedSquareWeight q ≤ 976800 := by
  decide +kernel

private theorem finiteSum_block_14 :
    ∑ q ∈ Finset.Ico 651 701, roundedSquareWeight q ≤ 1027900 := by
  decide +kernel

private theorem finiteSum_block_15 :
    ∑ q ∈ Finset.Ico 701 751, roundedSquareWeight q ≤ 793400 := by
  decide +kernel

private theorem finiteSum_block_16 :
    ∑ q ∈ Finset.Ico 751 801, roundedSquareWeight q ≤ 1103400 := by
  decide +kernel

private theorem finiteSum_block_17 :
    ∑ q ∈ Finset.Ico 801 851, roundedSquareWeight q ≤ 827600 := by
  decide +kernel

private theorem finiteSum_block_18 :
    ∑ q ∈ Finset.Ico 851 901, roundedSquareWeight q ≤ 1044600 := by
  decide +kernel

private theorem finiteSum_block_19 :
    ∑ q ∈ Finset.Ico 901 951, roundedSquareWeight q ≤ 1068000 := by
  decide +kernel

private theorem finiteSum_block_20 :
    ∑ q ∈ Finset.Ico 951 1001, roundedSquareWeight q ≤ 923100 := by
  decide +kernel

theorem roundedSquareWeight_sum_le :
    ∑ q ∈ Finset.Icc 1 1000, roundedSquareWeight q ≤ 19607800 := by
  have hset : Finset.Icc 1 1000 = Finset.Ico 1 1001 := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 1 ≤ 51)
    (by decide : 51 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 51 ≤ 101)
    (by decide : 101 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 101 ≤ 151)
    (by decide : 151 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 151 ≤ 201)
    (by decide : 201 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 201 ≤ 251)
    (by decide : 251 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 251 ≤ 301)
    (by decide : 301 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 301 ≤ 351)
    (by decide : 351 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 351 ≤ 401)
    (by decide : 401 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 401 ≤ 451)
    (by decide : 451 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 451 ≤ 501)
    (by decide : 501 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 501 ≤ 551)
    (by decide : 551 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 551 ≤ 601)
    (by decide : 601 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 601 ≤ 651)
    (by decide : 651 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 651 ≤ 701)
    (by decide : 701 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 701 ≤ 751)
    (by decide : 751 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 751 ≤ 801)
    (by decide : 801 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 801 ≤ 851)
    (by decide : 851 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 851 ≤ 901)
    (by decide : 901 ≤ 1001)]
  rw [← Finset.sum_Ico_consecutive roundedSquareWeight (by decide : 901 ≤ 951)
    (by decide : 951 ≤ 1001)]
  exact add_le_add finiteSum_block_01 <|
    add_le_add finiteSum_block_02 <| add_le_add finiteSum_block_03 <|
    add_le_add finiteSum_block_04 <| add_le_add finiteSum_block_05 <|
    add_le_add finiteSum_block_06 <| add_le_add finiteSum_block_07 <|
    add_le_add finiteSum_block_08 <| add_le_add finiteSum_block_09 <|
    add_le_add finiteSum_block_10 <| add_le_add finiteSum_block_11 <|
    add_le_add finiteSum_block_12 <| add_le_add finiteSum_block_13 <|
    add_le_add finiteSum_block_14 <| add_le_add finiteSum_block_15 <|
    add_le_add finiteSum_block_16 <| add_le_add finiteSum_block_17 <|
    add_le_add finiteSum_block_18 <| add_le_add finiteSum_block_19 finiteSum_block_20

end LiuWang.Proof.ArithmeticBounds
