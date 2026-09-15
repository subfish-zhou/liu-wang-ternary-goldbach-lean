import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q152.Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q152

def values0 : List ℤ := [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

theorem values0_eq : squareValues words ![false, false, false] = values0 := by rfl

theorem certificate0 : KernelEntries 152 76 0 (squareValues words ![false, false, false]) := by
  rw [values0_eq]
  decide +kernel

def values1 : List ℤ := [0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1]

theorem values1_eq : squareValues words ![true, false, false] = values1 := by rfl

theorem certificate1 : KernelEntries 152 76 0 (squareValues words ![true, false, false]) := by
  rw [values1_eq]
  decide +kernel

def values2 : List ℤ := [0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1]

theorem values2_eq : squareValues words ![false, true, false] = values2 := by rfl

theorem certificate2 : VerifiedScan.Weighted 152 (squareValues words ![false, true, false]) 152 12 (1269 / 1250) := by
  rw [values2_eq]
  apply weighted_of_list (t := 1) (B := 1000000000000)
  · decide +kernel
  · decide +kernel
  · norm_num
  · decide +kernel

def values3 : List ℤ := [0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 0, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1]

theorem values3_eq : squareValues words ![true, true, false] = values3 := by rfl

theorem certificate3 : KernelEntries 152 8 0 (squareValues words ![true, true, false]) := by
  rw [values3_eq]
  decide +kernel

def values4 : List ℤ := [0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, 1]

theorem values4_eq : squareValues words ![false, false, true] = values4 := by rfl

theorem certificate4 : KernelEntries 152 76 0 (squareValues words ![false, false, true]) := by
  rw [values4_eq]
  decide +kernel

def values5 : List ℤ := [0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 0, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 0, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1]

theorem values5_eq : squareValues words ![true, false, true] = values5 := by rfl

theorem certificate5 : KernelEntries 152 76 0 (squareValues words ![true, false, true]) := by
  rw [values5_eq]
  decide +kernel

def values6 : List ℤ := [0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 0, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1]

theorem values6_eq : squareValues words ![false, true, true] = values6 := by rfl

theorem certificate6 : KernelEntries 152 8 0 (squareValues words ![false, true, true]) := by
  rw [values6_eq]
  decide +kernel

def values7 : List ℤ := [0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, -1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1]

theorem values7_eq : squareValues words ![true, true, true] = values7 := by rfl

theorem certificate7 : VerifiedScan.Weighted 152 (squareValues words ![true, true, true]) 152 6 (1269 / 1250) := by
  rw [values7_eq]
  apply weighted_of_list (t := 1) (B := 1000000000000)
  · decide +kernel
  · decide +kernel
  · norm_num
  · decide +kernel

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q152
