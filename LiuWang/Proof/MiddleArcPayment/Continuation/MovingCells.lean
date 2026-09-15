import LiuWang.Proof.MiddleArcPayment.Continuation.Payment

/-!
# Paying the remaining high-real packet with height-dependent R24 cutoffs

Every non-exceptional cell now has a proved real-part cutoff below one.
The final mother contains only finite elementary scalar terms, no zero packet
or assumed cost. Its size is not asserted to satisfy the target 0.5033.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical
open LiuWang.Proof.Interfaces LiuWang.Proof.Parameters
open LiuWang.Proof.CharacterExpansion LiuWang.Proof.CompleteExpansion

namespace LiuWang.Proof.MiddleArcPayment.Continuation

def heightScale (q : ℕ) (v : ℝ) : ℝ := (q : ℝ) * max 10 v

def movingCutoff (q : ℕ) (v : ℝ) : ℝ := 1 - 1 / (24 * Real.log (heightScale q v))

theorem heightScale_parameters (q : ℕ) [NeZero q] (v : ℝ) :
    10 ≤ heightScale q v ∧ (q : ℝ) ≤ heightScale q v ∧
      v ≤ heightScale q v / (q : ℝ) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hv : (10 : ℝ) ≤ max 10 v := le_max_left _ _
  unfold heightScale
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rw [mul_div_cancel_left₀ _ (by positivity : (q : ℝ) ≠ 0)]
  exact le_max_right _ _

theorem movingCutoff_mono {q : ℕ} [NeZero q] {u v : ℝ} (huv : u ≤ v) :
    movingCutoff q u ≤ movingCutoff q v := by
  have hxu := (heightScale_parameters q u).1
  have hxy : heightScale q u ≤ heightScale q v :=
    mul_le_mul_of_nonneg_left (max_le_max_left 10 huv) (Nat.cast_nonneg _)
  have hlog := Real.log_le_log (by linarith : 0 < heightScale q u) hxy
  have hpos : 0 < Real.log (heightScale q u) := Real.log_pos (by linarith)
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 24 * Real.log (heightScale q u))
    (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 24))
  unfold movingCutoff
  linarith

theorem movingCutoff_lt_one (q : ℕ) [NeZero q] (v : ℝ) :
    movingCutoff q v < 1 := by
  have hx := (heightScale_parameters q v).1
  have hl : 0 < Real.log (heightScale q v) := Real.log_pos (by linarith)
  unfold movingCutoff
  exact sub_lt_self _ (by positivity)

theorem remaining_zero_re_le {q : ℕ} [NeZero q] (chi : Character q)
    {T v : ℝ} {rho : ℂ} (hz : rho ∈ zeroValues chi T)
    (hv : |rho.im| ≤ v)
    (hout : ¬ ZeroRegionFamily.RealClosure.region (heightScale q 0) q rho) :
    rho.re ≤ movingCutoff q v := by
  by_contra h
  have hr := mem_zeroValues.mp hz
  obtain ⟨hx, hqx, hheight⟩ := heightScale_parameters q v
  have hreg : ZeroRegionFamily.RealClosure.region (heightScale q v) q rho :=
    ⟨lt_of_not_ge h, hv.trans hheight⟩
  have hp : rho ≠ 1 := by intro he; simp [he] at hr
  have hreal := (ZeroRegionFamily.RealClosure.zero_real_quadratic_simple
    hx hqx chi hreg (Or.inr hp) hr.1).2.2.1
  apply hout
  refine ⟨lt_of_le_of_lt (movingCutoff_mono ((abs_nonneg rho.im).trans hv)) (lt_of_not_ge h), ?_⟩
  rw [hreal, abs_zero]
  have hb := (heightScale_parameters q 0).2.2
  exact hb

theorem sum_le_finite_cover {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset A) (t : Finset B) (cells : B → Finset A) (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hc : ∀ a ∈ s, ∃ j ∈ t, a ∈ cells j) :
    (∑ a ∈ s, f a) ≤ ∑ j ∈ t, ∑ a ∈ cells j, f a := by
  calc
    _ ≤ ∑ a ∈ s, ∑ j ∈ t, if a ∈ cells j then f a else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨j, hj, hcell⟩ := hc a ha
      have h := Finset.single_le_sum (s := t) (f := fun j => if a ∈ cells j then f a else 0)
        (fun j _ => by split_ifs; exact hf a; exact le_rfl) hj
      simpa only [if_pos hcell] using h
    _ = ∑ j ∈ t, ∑ a ∈ s.filter (fun a => a ∈ cells j), f a := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun a ha => (Finset.mem_filter.mp ha).2) (fun a _ _ => hf a)

def remainingValues {q : ℕ} [NeZero q] (chi : Character q) (N : ℕ) : Finset ℂ :=
  (zeroValues chi (sourceT N)).filter
    (fun rho => ¬ ZeroRegionFamily.RealClosure.region (heightScale q 0) q rho)

def movingScalar (q N : ℕ) (eta : ℝ) : ℝ :=
  Real.sqrt q * ∑ j ∈ Finset.range (sourceDyadicHeight N + 1),
    (N : ℝ) ^ movingCutoff q (cellUpper 1 j) *
      heightCost N eta (cellLower 1 j) * modulusCount q (cellUpper 1 j)

theorem remaining_character_le {q N : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (chi : Character q) (eta : ℝ) :
    (∑ rho ∈ remainingValues chi N,
      (analyticOrderNatAt chi.LFunction rho : ℝ) * ‖Jrho N rho eta‖) ≤
      ∑ j ∈ Finset.range (sourceDyadicHeight N + 1),
        (N : ℝ) ^ movingCutoff q (cellUpper 1 j) *
          heightCost N eta (cellLower 1 j) * modulusCount q (cellUpper 1 j) := by
  let cells := fun j => cellValues chi (movingCutoff q (cellUpper 1 j))
    (cellLower 1 j) (cellUpper 1 j)
  have hc (rho : ℂ) (hrho : rho ∈ remainingValues chi N) :
      ∃ j ∈ Finset.range (sourceDyadicHeight N + 1), rho ∈ cells j := by
    obtain ⟨hz, hout⟩ := Finset.mem_filter.mp hrho
    have hr := mem_zeroValues.mp hz
    obtain ⟨j, hj, hlow, hhigh⟩ := dyadic_cover 1 (sourceDyadicHeight N) (abs_nonneg rho.im)
      (by simpa using hr.2.2.2.1.trans (sourceDyadicHeight_covers hN))
    exact ⟨j, hj, Finset.mem_filter.mpr ⟨DirichletZeroCount.mem_zeroValues.mpr
      ⟨hr.1, ⟨hr.2.1, hr.2.2.1, hhigh⟩, hr.2.2.2.2⟩,
      remaining_zero_re_le chi hz hhigh hout, hlow⟩⟩
  apply (sum_le_finite_cover (remainingValues chi N)
    (Finset.range (sourceDyadicHeight N + 1)) cells
    (fun rho => (analyticOrderNatAt chi.LFunction rho : ℝ) * ‖Jrho N rho eta‖)
    (fun _ => by positivity) hc).trans
  apply Finset.sum_le_sum
  intro j _
  apply (cellMass_le (nat_pos_of_exp_le hN) chi eta (movingCutoff q (cellUpper 1 j))
    (cellLower 1 j) (by unfold cellUpper; positivity) (by norm_num : (0 : ℝ) < 2)).trans
  exact mul_le_mul_of_nonneg_left
    (sharpenedBound_le_modulus chi (by unfold cellUpper; positivity))
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (heightCost_nonneg N eta _))

theorem zeroPacket_sub_base_identity {q N : ℕ} [NeZero q] (a : ℕ)
    (ha : Nat.Coprime a q) (eta : ℝ) :
    zeroPacket q N a eta - rightmostPacket q N a eta (heightScale q 0) =
      (q.totient : ℂ)⁻¹ * ∑ chi : Character q, G a chi *
        ∑ rho ∈ remainingValues chi N,
          (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta := by
  rw [zeroPacket_eq_all_values N a eta ha]
  unfold rightmostPacket rightmostPairs
  rw [Finset.sum_sigma, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  dsimp only
  rw [← Finset.mul_sum, ← mul_sub]
  congr 1
  have he := Finset.sum_filter_add_sum_filter_not (zeroValues chi (sourceT N))
    (fun rho => ZeroRegionFamily.RealClosure.region (heightScale q 0) q rho)
    (fun rho => (analyticOrderNatAt chi.LFunction rho : ℂ) * Jrho N rho eta)
  unfold zeroValueSum remainingValues
  linear_combination -he

theorem zeroPacket_sub_base_le {q N : ℕ} [NeZero q]
    (hN : Real.exp 2000 ≤ (N : ℝ)) (a : ℕ) (ha : Nat.Coprime a q) (eta : ℝ) :
    ‖zeroPacket q N a eta - rightmostPacket q N a eta (heightScale q 0)‖ ≤
      movingScalar q N eta := by
  let B := ∑ j ∈ Finset.range (sourceDyadicHeight N + 1),
    (N : ℝ) ^ movingCutoff q (cellUpper 1 j) *
      heightCost N eta (cellLower 1 j) * modulusCount q (cellUpper 1 j)
  have hB : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (heightCost_nonneg N eta _)) (modulusCount_nonneg (by unfold cellUpper; positivity))
  have hp : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  rw [zeroPacket_sub_base_identity a ha eta, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖ * B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro chi _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (norm_sum_le _ _).trans
      simpa only [norm_mul, Complex.norm_natCast] using remaining_character_le hN chi eta
    _ = ((q.totient : ℝ)⁻¹ * ∑ chi : Character q, ‖G a chi‖) * B := by
      rw [← Finset.sum_mul, mul_assoc]
    _ ≤ Real.sqrt q * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      calc
        _ ≤ (q.totient : ℝ)⁻¹ * (Real.sqrt (q.totient : ℝ) * q.totient) :=
          mul_le_mul_of_nonneg_left (NonprincipalPacket.sum_norm_G_le a) (by positivity)
        _ = Real.sqrt (q.totient : ℝ) := by field_simp
        _ ≤ _ := Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.totient_le q))

theorem S_moving_paid {q N a : ℕ} [NeZero q]
    (hN : Real.exp 3100 ≤ (N : ℝ)) (hi : sourceIndex a q)
    (hq0 : sourceP N < (q : ℝ)) (hq1 : (q : ℝ) ≤ sourceP1 N)
    {eta : ℝ} (heta : |eta| ≤ sourceL N ^ 7 / ((q : ℝ) * N)) :
    ‖S N (rationalCenter a q + eta)‖ ≤
      movingScalar q N eta + 0.239860000001 * (N : ℝ) / sourceL N := by
  have hn := exp_2000_le_of_exp_3100_le hN
  have hx := heightScale_parameters q 0
  have hp := principal_main_middle_paid hN hq0 eta
  have he := middle_error_regression (a := a) hn hq0 hq1 heta
  have hz := rightmostPacket_middle_paid hN hq0 hx.1 hx.2.1 a hi.2.2 eta
  have hr := zeroPacket_sub_base_le hn a hi.2.2 eta
  have hexp := complete_error_function hn hi hq1 eta
  have hzero : ‖zeroPacket q N a eta‖ ≤
      movingScalar q N eta + 0.23976 * (N : ℝ) / sourceL N := by
    calc
      _ = ‖(zeroPacket q N a eta - rightmostPacket q N a eta (heightScale q 0)) +
          rightmostPacket q N a eta (heightScale q 0)‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hr hz)
  calc
    _ = ‖(principalCoefficient q * J N eta - zeroPacket q N a eta) +
        (S N (rationalCenter a q + eta) - principalCoefficient q * J N eta +
          zeroPacket q N a eta)‖ := by congr 1; ring
    _ ≤ (0.0001 * (N : ℝ) / sourceL N +
        (movingScalar q N eta + 0.23976 * (N : ℝ) / sourceL N)) +
        0.000000000001 * (N : ℝ) / sourceL N :=
      (norm_add_le _ _).trans
        (add_le_add ((norm_sub_le _ _).trans (add_le_add hp hzero)) (hexp.trans he))
    _ = _ := by ring

end LiuWang.Proof.MiddleArcPayment.Continuation
