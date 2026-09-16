import LiuWang.Proof.Campaign20260915.ThirdBudgets.M5PlatformPayment
import LiuWang.Proof.Campaign20260915.ThirdBudgets.EndpointActualPayment
import LiuWang.Proof.Campaign20260915.ThirdBudgets.MiddleDensityPayment
import LiuWang.Proof.Campaign20260915.ThirdBudgets.MiddleRealCreditPayment
import LiuWang.Proof.Campaign20260915.ThirdBudgets.Sigma6Payment

set_option autoImplicit false

namespace LiuWang.Proof.Campaign20260915.ThirdBudgets

#check @sourceM5_original_paid
#check @sourceM5_platform_and_bulk_paid
#check @middle_endpoint_original_paid
#check @middle_density_original_paid
#check @middle_near_original_paid
#check @sigma5_original_paid
#check @sigma6_original_paid

#print axioms m5_count_bound_all_heights
#print axioms m5_below_gate_count_bound
#print axioms sourceM5_original_scalar_transfer
#print axioms sourceM5_original_paid
#print axioms sourceM5_platform_and_bulk_paid
#print axioms endpoint_density_scalar_paid
#print axioms endpoint_density_count_bound
#print axioms middle_endpoint_original_paid
#print axioms middle_density_scalar_paid
#print axioms middle_density_original_paid
#print axioms middle_theorem_two_count
#print axioms middle_near_original_paid
#print axioms middle_count_after_real_credit
#print axioms sigma5_original_paid
#print axioms sigma6_original_paid

end LiuWang.Proof.Campaign20260915.ThirdBudgets
