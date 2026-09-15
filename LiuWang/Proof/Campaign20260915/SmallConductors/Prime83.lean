import LiuWang.Proof.SmallConductorExpansion.Continuation.VerifiedScan.Prefix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion
open LiuWang.Proof.SmallConductorExpansion.Continuation

namespace LiuWang.Proof.Campaign20260915.SmallConductors

instance prime83 : Fact (Nat.Prime 83) := ⟨by decide +kernel⟩

def values83 : List ℤ :=
  List.ofFn fun a : Fin 83 => quadraticCharFun (ZMod 83) (a.val : ZMod 83)

theorem table83 :
    ∀ a : ZMod 83, primeCharacter 83 a = (values83.getD a.val 0 : ℂ) :=
  primeCharacter_table 83 values83 (by decide +kernel)

theorem certificate83 : RationalWeightedCertificate 83 values83 83 20 (509 / 500) := by
  apply (VerifiedScan.weighted_iff _ _ _ _ _).mp
  unfold VerifiedScan.Weighted
  constructor <;> decide +kernel

theorem quadratic_83_original_region (chi : DirichletCharacter ℂ 83)
    (hc : chi ≠ 1) (hsq : chi ^ 2 = 1) {x beta : ℝ} (hx : 83 ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  rw [quadratic_prime_eq 83 (by decide) chi hc hsq]
  exact rationalWeighted_original_region (primeCharacter 83)
    (primeCharacter_ne_one 83 (by decide)) values83 table83
    (by decide) (dvd_refl 83) (n := 40) (by decide) certificate83
    (by norm_num) (by norm_num) (log_scale_forty (by linarith)) hb

#print axioms quadratic_83_original_region

end LiuWang.Proof.Campaign20260915.SmallConductors
