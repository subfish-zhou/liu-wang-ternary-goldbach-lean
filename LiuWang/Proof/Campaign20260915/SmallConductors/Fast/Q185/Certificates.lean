import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q185.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q185

def values0 : List ℤ := [0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1]

theorem values0_eq : squareValues words ![false, false] = values0 := by rfl

theorem certificate0 : KernelEntries 185 37 0 (squareValues words ![false, false]) := by
  rw [values0_eq]
  decide +kernel

def values1 : List ℤ := [0, 1, -1, 1, 1, 0, -1, 1, -1, 1, 0, 1, 1, -1, -1, 0, 1, -1, -1, -1, 0, 1, -1, -1, -1, 0, 1, 1, 1, -1, 0, -1, -1, 1, 1, 0, 1, 0, 1, -1, 0, 1, -1, -1, 1, 0, 1, 1, 1, 1, 0, -1, -1, 1, -1, 0, -1, -1, 1, -1, 0, -1, 1, 1, 1, 0, -1, 1, -1, -1, 0, 1, -1, 1, 0, 0, -1, 1, 1, -1, 0, 1, -1, 1, 1, 0, 1, -1, -1, -1, 0, -1, -1, -1, -1, 0, -1, -1, -1, 1, 0, 1, 1, -1, 1, 0, -1, 1, 1, -1, 0, 0, 1, -1, 1, 0, -1, -1, 1, -1, 0, 1, 1, 1, -1, 0, -1, 1, -1, -1, 0, -1, 1, -1, -1, 0, 1, 1, 1, 1, 0, 1, -1, -1, 1, 0, -1, 1, 0, 1, 0, 1, 1, -1, -1, 0, -1, 1, 1, 1, 0, -1, -1, -1, 1, 0, -1, -1, -1, 1, 0, -1, -1, 1, 1, 0, 1, -1, 1, -1, 0, 1, 1, -1, 1]

theorem values1_eq : squareValues words ![true, false] = values1 := by rfl

theorem certificate1 : KernelEntries 185 37 0 (squareValues words ![true, false]) := by
  rw [values1_eq]
  decide +kernel

def values2 : List ℤ := [0, 1, 1, -1, 1, 0, -1, -1, 1, 1, 0, 1, -1, 1, -1, 0, 1, 1, 1, -1, 0, 1, 1, 1, -1, 0, 1, -1, -1, -1, 0, -1, 1, -1, 1, 0, 1, 0, -1, -1, 0, 1, 1, 1, 1, 0, 1, -1, -1, 1, 0, -1, 1, -1, -1, 0, -1, 1, -1, -1, 0, -1, -1, -1, 1, 0, -1, -1, 1, -1, 0, 1, 1, -1, 0, 0, -1, -1, -1, -1, 0, 1, 1, -1, 1, 0, 1, 1, 1, -1, 0, -1, 1, 1, -1, 0, -1, 1, 1, 1, 0, 1, -1, 1, 1, 0, -1, -1, -1, -1, 0, 0, -1, 1, 1, 0, -1, 1, -1, -1, 0, 1, -1, -1, -1, 0, -1, -1, 1, -1, 0, -1, -1, 1, -1, 0, 1, -1, -1, 1, 0, 1, 1, 1, 1, 0, -1, -1, 0, 1, 0, 1, -1, 1, -1, 0, -1, -1, -1, 1, 0, -1, 1, 1, 1, 0, -1, 1, 1, 1, 0, -1, 1, -1, 1, 0, 1, 1, -1, -1, 0, 1, -1, 1, 1]

theorem values2_eq : squareValues words ![false, true] = values2 := by rfl

theorem certificate2 : VerifiedScan.Weighted 185 (squareValues words ![false, true]) 185 8 (1269 / 1250) := by
  rw [values2_eq]
  apply weighted_of_list (t := 1) (B := 1000000000000)
  · decide +kernel
  · decide +kernel
  · norm_num
  · decide +kernel

def values3 : List ℤ := [0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, 0, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 0, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 0, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, 0, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1, 0, 1, -1, -1, 1]

theorem values3_eq : squareValues words ![true, true] = values3 := by rfl

theorem certificate3 : KernelEntries 185 5 0 (squareValues words ![true, true]) := by
  rw [values3_eq]
  decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q185
