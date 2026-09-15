import LiuWang.Proof.Campaign20260915.Totient.ProductKeys

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace LiuWang.Proof.Campaign20260915.Totient

private theorem keys318 {p : ℕ} (hl : 318 ≤ p) (hu : p < 382) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys382 {p : ℕ} (hl : 382 ≤ p) (hu : p < 446) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys446 {p : ℕ} (hl : 446 ≤ p) (hu : p < 510) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys510 {p : ℕ} (hl : 510 ≤ p) (hu : p < 574) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys574 {p : ℕ} (hl : 574 ≤ p) (hu : p < 638) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys638 {p : ℕ} (hl : 638 ≤ p) (hu : p < 702) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys702 {p : ℕ} (hl : 702 ≤ p) (hu : p < 766) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys766 {p : ℕ} (hl : 766 ≤ p) (hu : p < 830) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys830 {p : ℕ} (hl : 830 ≤ p) (hu : p < 894) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys894 {p : ℕ} (hl : 894 ≤ p) (hu : p < 958) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys958 {p : ℕ} (hl : 958 ≤ p) (hu : p < 1022) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys1022 {p : ℕ} (hl : 1022 ≤ p) (hu : p < 1086) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys1086 {p : ℕ} (hl : 1086 ≤ p) (hu : p < 1150) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys1150 {p : ℕ} (hl : 1150 ≤ p) (hu : p < 1214) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys1214 {p : ℕ} (hl : 1214 ≤ p) (hu : p < 1278) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys1278 {p : ℕ} (hl : 1278 ≤ p) (hu : p < 1342) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys1342 {p : ℕ} (hl : 1342 ≤ p) (hu : p < 1406) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel
private theorem keys1406 {p : ℕ} (hl : 1406 ≤ p) (hu : p ≤ 1420) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  interval_cases p <;> norm_num at hp
  all_goals decide +kernel

theorem product_keys_complete {p : ℕ} (hl : 286 ≤ p) (hu : p ≤ 1420) (hp : p.Prime) :
    p ∈ thetaLogRows.map Prod.fst := by
  by_cases h0 : p < 318
  · exact product_keys_286 hl h0 hp
  by_cases h1 : p < 382
  · exact keys318 (by omega) h1 hp
  by_cases h2 : p < 446
  · exact keys382 (by omega) h2 hp
  by_cases h3 : p < 510
  · exact keys446 (by omega) h3 hp
  by_cases h4 : p < 574
  · exact keys510 (by omega) h4 hp
  by_cases h5 : p < 638
  · exact keys574 (by omega) h5 hp
  by_cases h6 : p < 702
  · exact keys638 (by omega) h6 hp
  by_cases h7 : p < 766
  · exact keys702 (by omega) h7 hp
  by_cases h8 : p < 830
  · exact keys766 (by omega) h8 hp
  by_cases h9 : p < 894
  · exact keys830 (by omega) h9 hp
  by_cases h10 : p < 958
  · exact keys894 (by omega) h10 hp
  by_cases h11 : p < 1022
  · exact keys958 (by omega) h11 hp
  by_cases h12 : p < 1086
  · exact keys1022 (by omega) h12 hp
  by_cases h13 : p < 1150
  · exact keys1086 (by omega) h13 hp
  by_cases h14 : p < 1214
  · exact keys1150 (by omega) h14 hp
  by_cases h15 : p < 1278
  · exact keys1214 (by omega) h15 hp
  by_cases h16 : p < 1342
  · exact keys1278 (by omega) h16 hp
  by_cases h17 : p < 1406
  · exact keys1342 (by omega) h17 hp
  exact keys1406 (by omega) hu hp

end LiuWang.Proof.Campaign20260915.Totient
