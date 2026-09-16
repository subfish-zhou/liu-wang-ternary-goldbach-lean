import LiuWang.Proof.Campaign20260915.RSMediumRange.PilotLogRows

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

def kernelPilotRows : List (ℕ × ℕ × ℕ × ℕ) :=
  [(99614737, 26, 1841682066669824, 1841682068069846),
   (99614741, 26, 1841682070685298, 1841682072085322),
   (99614743, 26, 1841682072693032, 1841682074093054),
   (99614783, 26, 1841682112847720, 1841682114247742),
   (99614791, 26, 1841682120878656, 1841682122278678),
   (99614803, 26, 1841682132925060, 1841682134325082),
   (99614821, 26, 1841682150994664, 1841682152394686),
   (99614839, 26, 1841682169064262, 1841682170464284),
   (99614881, 26, 1841682211226648, 1841682212626672),
   (99614899, 26, 1841682229296238, 1841682230696260),
   (99614959, 26, 1841682289528170, 1841682290928192),
   (99614969, 26, 1841682299566824, 1841682300966846),
   (99615007, 26, 1841682337713694, 1841682339113716),
   (99615041, 26, 1841682371845090, 1841682373245112),
   (99615049, 26, 1841682379876004, 1841682381276026),
   (99615071, 26, 1841682401961020, 1841682403361042)]

theorem kernelPilot_checked :
    ∀ r ∈ kernelPilotRows, r.1.Prime ∧
      2 ^ r.2.1 ≤ r.1 ∧ r.1 < 2 ^ (r.2.1 + 1) ∧
      (FixedBracket.log r.1 r.2.1).lo = r.2.2.1 ∧
      (FixedBracket.log r.1 r.2.1).hi = r.2.2.2 := by
  intro r hr
  simp only [kernelPilotRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [log_99614737, log_99614741, log_99614743, log_99614783,
      log_99614791, log_99614803, log_99614821, log_99614839,
      log_99614881, log_99614899, log_99614959, log_99614969,
      log_99615007, log_99615041, log_99615049, log_99615071,
      prime_99614737, prime_99614741, prime_99614743, prime_99614783,
      prime_99614791, prime_99614803, prime_99614821, prime_99614839,
      prime_99614881, prime_99614899, prime_99614959, prime_99614969,
      prime_99615007, prime_99615041, prime_99615049, prime_99615071]

theorem kernelPilot_complete :
    ∀ n ∈ Finset.Icc 99614737 99615071,
      n.Prime ↔ n ∈ kernelPilotRows.map Prod.fst := by
  intro n hn
  simp only [Finset.mem_Icc] at hn
  obtain ⟨hnlo, hnhi⟩ := hn
  interval_cases n <;> norm_num [kernelPilotRows]

theorem kernelPilot_log_bounds {r : ℕ × ℕ × ℕ × ℕ} (hr : r ∈ kernelPilotRows) :
    (FixedBracket.mk r.2.2.1 r.2.2.2).Contains (Real.log r.1) := by
  obtain ⟨_, hl, hu, hlo, hhi⟩ := kernelPilot_checked r hr
  have h := FixedBracket.log_contains hl hu
  simpa only [FixedBracket.Contains, hlo, hhi] using h

#print axioms kernelPilot_checked
#print axioms kernelPilot_complete
#print axioms kernelPilot_log_bounds

end LiuWang.Proof.Campaign20260915.RSMediumRange
