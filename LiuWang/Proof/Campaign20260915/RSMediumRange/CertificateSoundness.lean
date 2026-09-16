import LiuWang.Proof.Campaign20260915.RSMediumRange.FixedPointLog

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

theorem prime_of_no_small_prime_divisor {n : ℕ}
    (hn : 2 ≤ n) (hbound : n ≤ 100000000)
    (h : ∀ p ∈ Nat.primesLE 10000, ¬p ∣ n) : n.Prime := by
  by_contra hnp
  have hp := Nat.minFac_prime (n := n) (by omega)
  have hs := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
  have hsmall : n.minFac ≤ 10000 := by nlinarith
  exact h n.minFac (Nat.mem_primesLE.mpr ⟨hsmall, hp⟩) (Nat.minFac_dvd n)

theorem primesLE_eq_of_divisor_witnesses {n : ℕ} {ps : Finset ℕ}
    (hprime : ∀ p ∈ ps, p ≤ n ∧ p.Prime)
    (hcomposite : ∀ m, 2 ≤ m → m ≤ n → m ∉ ps →
      ∃ d, 1 < d ∧ d < m ∧ d ∣ m) :
    Nat.primesLE n = ps := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpn, hpp⟩ := Nat.mem_primesLE.mp hp
    by_contra hnot
    obtain ⟨d, hd1, hdp, hd⟩ := hcomposite p hpp.two_le hpn hnot
    rcases hpp.eq_one_or_self_of_dvd d hd with h | h <;> omega
  · intro hp
    exact Nat.mem_primesLE.mpr (hprime p hp)

def productStep (u p : ℕ) : ℕ := divUp (u * p) (p - 1)

def productUnits (ps : List ℕ) : ℕ := ps.foldl productStep fixedScale

noncomputable section

theorem theta_enclosure_from_complete_set {n : ℕ} {ps : Finset ℕ}
    {lo hi : ℕ → ℕ}
    (hps : Nat.primesLE n = ps)
    (hlog : ∀ p ∈ ps, (FixedBracket.mk (lo p) (hi p)).Contains (Real.log p)) :
    (FixedBracket.mk (∑ p ∈ ps, lo p) (∑ p ∈ ps, hi p)).Contains
      (Chebyshev.theta n) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, hps]
  constructor
  · have h := Finset.sum_le_sum (fun p hp => (hlog p hp).1)
    simpa [FixedBracket.Contains, Nat.cast_sum, Finset.sum_div] using h
  · have h := Finset.sum_le_sum (fun p hp => (hlog p hp).2)
    simpa [FixedBracket.Contains, Nat.cast_sum, Finset.sum_div] using h

theorem productStep_bound {u p : ℕ} {v : ℝ}
    (hp : 2 ≤ p) (hv : v ≤ (u : ℝ) / fixedScale) :
    v * ((p : ℝ) / (p - 1)) ≤ (productStep u p : ℝ) / fixedScale := by
  have hd : 0 < p - 1 := by omega
  have hround : u * p ≤ productStep u p * (p - 1) := by
    have hm := Nat.mod_add_div (u * p) (p - 1)
    have hr := Nat.mod_lt (u * p) hd
    unfold productStep divUp
    split_ifs with h <;> simp only [Nat.add_mul, Nat.zero_mul, Nat.one_mul] <;> nlinarith
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hcast : ((p - 1 : ℕ) : ℝ) = p - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ p by omega))
  have hroundR : (u : ℝ) * p ≤ (productStep u p : ℝ) * (p - 1) := by
    have h : (u : ℝ) * p ≤ (productStep u p : ℝ) * ((p - 1 : ℕ) : ℝ) :=
      by exact_mod_cast hround
    rwa [hcast] at h
  apply (mul_le_mul_of_nonneg_right hv (by positivity : 0 ≤ (p : ℝ) / (p - 1))).trans
  calc
    (u : ℝ) / fixedScale * ((p : ℝ) / (p - 1)) =
        ((u : ℝ) * p / (p - 1)) / fixedScale := by ring
    _ ≤ (productStep u p : ℝ) / fixedScale :=
      div_le_div_of_nonneg_right
        ((div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr hroundR) (by positivity)

private theorem product_fold_bound (ps : List ℕ)
    (hp : ∀ p ∈ ps, 2 ≤ p) {u : ℕ} {v : ℝ}
    (hv : v ≤ (u : ℝ) / fixedScale) :
    v * (ps.map (fun p : ℕ => (p : ℝ) / (p - 1))).prod ≤
      ((ps.foldl productStep u : ℕ) : ℝ) / fixedScale := by
  induction ps generalizing u v with
  | nil => simpa using hv
  | cons p ps ih =>
    have hnext := productStep_bound (hp p (by simp)) hv
    have htail := ih (fun q hq => hp q (by simp [hq])) hnext
    simpa only [List.map_cons, List.prod_cons, List.foldl_cons, mul_assoc] using htail

theorem euler_enclosure_from_complete_list {n : ℕ} {ps : List ℕ}
    (hnd : ps.Nodup) (hps : ps.toFinset = Nat.primesLE n) :
    (Totient.prefixEuler n : ℝ) ≤ (productUnits ps : ℝ) / fixedScale := by
  have hp : ∀ p ∈ ps, 2 ≤ p := by
    intro p h
    have hmem : p ∈ Nat.primesLE n := by rw [← hps]; exact List.mem_toFinset.mpr h
    exact (Nat.mem_primesLE.mp hmem).2.two_le
  have h := product_fold_bound ps hp (u := fixedScale) (v := 1) (by norm_num [fixedScale])
  rw [one_mul, ← List.prod_toFinset (fun p : ℕ => (p : ℝ) / (p - 1)) hnd, hps] at h
  simpa [Totient.prefixEuler, productUnits, Rat.cast_prod] using h

theorem actual_bounds_on_cell {a b x tlo thi pu l r : ℝ}
    (ha : 16000 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (ht : tlo ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ thi)
    (hp : (Totient.prefixEuler ⌊x⌋₊ : ℝ) ≤ pu)
    (hlower : (b - tlo) ^ 2 < 4 * b) (hupper : thi < a)
    (hl0 : 0 ≤ l) (hl : l ≤ Real.log a) (hr : Real.sqrt b ≤ r)
    (hproduct : pu < (178107239 / 100000000 : ℝ) * (l + 2 / r)) :
    (x - 2 * Real.sqrt x < Chebyshev.theta x ∧ Chebyshev.theta x < x) ∧
      (Totient.prefixEuler ⌊x⌋₊ : ℝ) <
        Real.exp Real.eulerMascheroniConstant * (Real.log x + 2 / Real.sqrt x) ∧
      (Totient.prefixEuler ⌊x⌋₊ : ℝ) < Totient.productEnvelope x := by
  have htheta := (theta_lower_on_cell (by linarith : 1 ≤ a) hax hxb hlower).trans_le ht.1
  have hprod := (hp.trans_lt hproduct).trans_le
    (theorem23_lower_envelope_on_cell (by linarith) hax hxb hl0 hl hr)
  exact ⟨⟨htheta, (ht.2.trans_lt hupper).trans_le hax⟩, hprod,
    hprod.trans_le (theorem23_envelope_le_3_29 (ha.trans hax))⟩

#print axioms prime_of_no_small_prime_divisor
#print axioms primesLE_eq_of_divisor_witnesses
#print axioms theta_enclosure_from_complete_set
#print axioms euler_enclosure_from_complete_list
#print axioms actual_bounds_on_cell

end
end LiuWang.Proof.Campaign20260915.RSMediumRange
