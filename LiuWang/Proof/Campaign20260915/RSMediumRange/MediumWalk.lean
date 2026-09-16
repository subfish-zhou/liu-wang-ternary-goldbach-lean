import LiuWang.Proof.Campaign20260915.RSMediumRange.PackedGap

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

structure MediumState where
  p : ℕ
  logLo : ℕ
  thetaLo : ℕ
  thetaHi : ℕ
  eulerHi : ℕ

structure MediumRow where
  p : ℕ
  k : ℕ
  logLo : ℕ
  logHi : ℕ
  root : ℕ
  gap : ℕ

def nextState (s : MediumState) (r : MediumRow) : MediumState :=
  ⟨r.p, r.logLo, s.thetaLo + r.logLo, s.thetaHi + r.logHi,
    productStep s.eulerHi r.p⟩

def CellCheck (s : MediumState) (b root : ℕ) : Prop :=
  s.thetaLo ≤ s.thetaHi ∧
  s.thetaHi < s.p * fixedScale ∧
  (b * fixedScale - s.thetaLo) ^ 2 < 4 * b * fixedScale ^ 2 ∧
  b * 1000000 ^ 2 ≤ root ^ 2 ∧
  s.eulerHi * 100000000 * root <
    178107239 * (s.logLo * root + 2 * 1000000 * fixedScale)

instance (s : MediumState) (b root : ℕ) : Decidable (CellCheck s b root) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def StepCheck (s : MediumState) (r : MediumRow) : Prop :=
  s.p < r.p ∧ r.p ≤ 100000000 ∧
  2 ^ r.k ≤ r.p ∧ r.p < 2 ^ (r.k + 1) ∧
  (FixedBracket.log r.p r.k).lo = r.logLo ∧
  (FixedBracket.log r.p r.k).hi = r.logHi ∧
  packedCompositeRun (s.p + 1) (r.p - s.p - 1) r.gap ∧ CellCheck s r.p r.root

instance (s : MediumState) (r : MediumRow) : Decidable (StepCheck s r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def MediumWalk : MediumState → List MediumRow → Prop
  | _, [] => True
  | s, r :: rs => StepCheck s r ∧ MediumWalk (nextState s r) rs

instance (s : MediumState) (rs : List MediumRow) : Decidable (MediumWalk s rs) := by
  induction rs generalizing s with
  | nil => exact instDecidableTrue
  | cons r rs ih =>
    unfold MediumWalk
    exact instDecidableAnd

noncomputable section

def MediumState.Actual (s : MediumState) : Prop :=
  (s.thetaLo : ℝ) / fixedScale ≤ Chebyshev.theta s.p ∧
    Chebyshev.theta s.p ≤ (s.thetaHi : ℝ) / fixedScale ∧
    (Totient.prefixEuler s.p : ℝ) ≤ (s.eulerHi : ℝ) / fixedScale ∧
    (s.logLo : ℝ) / fixedScale ≤ Real.log s.p

def MediumBounds (x : ℝ) : Prop :=
  (x - 2 * Real.sqrt x < Chebyshev.theta x ∧ Chebyshev.theta x < x) ∧
    (Totient.prefixEuler ⌊x⌋₊ : ℝ) <
      Real.exp Real.eulerMascheroniConstant * (Real.log x + 2 / Real.sqrt x) ∧
    (Totient.prefixEuler ⌊x⌋₊ : ℝ) < Totient.productEnvelope x

theorem actual_next {s : MediumState} {r : MediumRow}
    (hs : s.Actual) (hc : StepCheck s r) (hp : r.p.Prime) :
    (nextState s r).Actual := by
  obtain ⟨hsp, _, hscaleL, hscaleH, hlogL, hlogH, hgap, _⟩ := hc
  have hg := gap_of_packed hsp hgap
  have he := primesLE_insert_of_gap hsp hp hg
  have hnot : r.p ∉ Nat.primesLE s.p := by simp [Nat.mem_primesLE, hsp.not_ge]
  have ht : Chebyshev.theta r.p = Chebyshev.theta s.p + Real.log r.p := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, he, Finset.sum_insert hnot,
      Chebyshev.theta_eq_sum_primesLE_log]
    ring
  have hprod : Totient.prefixEuler r.p =
      Totient.prefixEuler s.p * (r.p : ℚ) / (r.p - 1) := by
    unfold Totient.prefixEuler
    rw [he, Finset.prod_insert hnot]
    ring
  have hl := FixedBracket.log_contains hscaleL hscaleH
  simp only [FixedBracket.Contains, hlogL, hlogH] at hl
  refine ⟨?_, ?_, ?_, hl.1⟩
  · change ((s.thetaLo + r.logLo : ℕ) : ℝ) / fixedScale ≤ Chebyshev.theta r.p
    rw [ht, Nat.cast_add, add_div]
    exact add_le_add hs.1 hl.1
  · change Chebyshev.theta r.p ≤ ((s.thetaHi + r.logHi : ℕ) : ℝ) / fixedScale
    rw [ht, Nat.cast_add, add_div]
    exact add_le_add hs.2.1 hl.2
  · change (Totient.prefixEuler r.p : ℝ) ≤ (productStep s.eulerHi r.p : ℝ) / fixedScale
    rw [hprod]
    push_cast
    have h := productStep_bound hp.two_le hs.2.2.1
    simpa only [mul_div_assoc] using h

theorem cellCheck_sound {s : MediumState} {b root : ℕ}
    (hs : 16000 ≤ s.p) (hb : s.p ≤ b) (hc : CellCheck s b root) :
    ((b : ℝ) - (s.thetaLo : ℝ) / fixedScale) ^ 2 < 4 * b ∧
    (s.thetaHi : ℝ) / fixedScale < s.p ∧
    Real.sqrt b ≤ (root : ℝ) / 1000000 ∧
    (s.eulerHi : ℝ) / fixedScale <
      (178107239 / 100000000 : ℝ) *
        ((s.logLo : ℝ) / fixedScale + 2 / ((root : ℝ) / 1000000)) := by
  obtain ⟨hlo, hhi, htheta, hroot, hprod⟩ := hc
  have hdiff : s.thetaLo ≤ b * fixedScale :=
    hlo.trans (hhi.le.trans (Nat.mul_le_mul_right fixedScale hb))
  have ht : ((b : ℝ) * fixedScale - s.thetaLo) ^ 2 <
      4 * b * (fixedScale : ℝ) ^ 2 := by
    have h := (Nat.cast_lt (α := ℝ)).mpr htheta
    simpa only [Nat.cast_sub hdiff, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using h
  have hu : (s.thetaHi : ℝ) < s.p * (fixedScale : ℝ) := by exact_mod_cast hhi
  have hr : (b : ℝ) * (1000000 : ℝ) ^ 2 ≤ (root : ℝ) ^ 2 := by exact_mod_cast hroot
  have hp : (s.eulerHi : ℝ) * 100000000 * root <
      178107239 * (s.logLo * (root : ℝ) + 2 * 1000000 * fixedScale) := by
    exact_mod_cast hprod
  have hbR : (16000 : ℝ) ≤ b := by exact_mod_cast hs.trans hb
  have hrootR : (0 : ℝ) < root := by
    have hnonneg : (0 : ℝ) ≤ root := Nat.cast_nonneg root
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [fixedScale] at ht ⊢
    nlinarith
  · exact (div_lt_iff₀ (by norm_num [fixedScale] : (0 : ℝ) < fixedScale)).mpr hu
  · nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ b by positivity), Real.sqrt_nonneg b]
  · apply (mul_lt_mul_iff_right₀ hrootR).mp
    field_simp
    norm_num [fixedScale] at hp ⊢
    nlinarith

theorem actual_cell {s : MediumState} {b root : ℕ} {x : ℝ}
    (hs : 16000 ≤ s.p) (hb : s.p ≤ b) (ha : s.Actual)
    (hc : CellCheck s b root)
    (hx : (s.p : ℝ) ≤ x) (hxb : x ≤ b)
    (hset : Nat.primesLE ⌊x⌋₊ = Nat.primesLE s.p) :
    MediumBounds x := by
  have ht : Chebyshev.theta x = Chebyshev.theta s.p := by
    rw [Chebyshev.theta_eq_sum_primesLE, hset, Chebyshev.theta_eq_sum_primesLE_log]
  have hp : Totient.prefixEuler ⌊x⌋₊ = Totient.prefixEuler s.p := by
    unfold Totient.prefixEuler
    rw [hset]
  obtain ⟨hl, hu, hr, hprod⟩ := cellCheck_sound hs hb hc
  exact actual_bounds_on_cell (by exact_mod_cast hs) hx hxb
    (by simpa only [ht] using (show (s.thetaLo : ℝ) / fixedScale ≤ Chebyshev.theta s.p ∧
      Chebyshev.theta s.p ≤ (s.thetaHi : ℝ) / fixedScale from ⟨ha.1, ha.2.1⟩))
    (by simpa only [hp] using ha.2.2.1) hl hu (by positivity) ha.2.2.2 hr hprod

theorem actual_step_cell {s : MediumState} {r : MediumRow} {x : ℝ}
    (hs : 16000 ≤ s.p) (ha : s.Actual) (hc : StepCheck s r)
    (hx : (s.p : ℝ) ≤ x) (hxr : x < r.p) : MediumBounds x := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg s.p).trans hx
  have hlo : s.p ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr hx
  have hhi : ⌊x⌋₊ < r.p := by exact_mod_cast (Nat.floor_le hx0).trans_lt hxr
  have hg := gap_of_packed hc.1 hc.2.2.2.2.2.2.1
  exact actual_cell hs hc.1.le ha hc.2.2.2.2.2.2.2 hx hxr.le
    (primesLE_of_gap hg hlo hhi)

theorem mediumWalk_sound {s : MediumState} {rs : List MediumRow}
    (hs : 16000 ≤ s.p) (ha : s.Actual) (hc : MediumWalk s rs)
    (hp : ∀ r ∈ rs, r.p.Prime) :
    (rs.foldl nextState s).Actual ∧
      s.p ≤ (rs.foldl nextState s).p ∧
      ∀ x : ℝ, (s.p : ℝ) ≤ x → x < (rs.foldl nextState s).p → MediumBounds x := by
  induction rs generalizing s with
  | nil => exact ⟨ha, le_rfl, fun x hx hhi => (not_lt_of_ge hx hhi).elim⟩
  | cons r rs ih =>
    obtain ⟨hstep, htail⟩ := hc
    have hnext := actual_next ha hstep (hp r (by simp))
    have hsp : s.p < r.p := hstep.1
    have ht := ih (s := nextState s r) (by change 16000 ≤ r.p; omega)
      hnext htail (fun r hr => hp r (by simp [hr]))
    refine ⟨ht.1, hsp.le.trans ht.2.1, ?_⟩
    intro x hx hhi
    by_cases hxr : x < r.p
    · exact actual_step_cell hs ha hstep hx hxr
    · exact ht.2.2 x (le_of_not_gt hxr) hhi

#print axioms mediumWalk_sound

end
end LiuWang.Proof.Campaign20260915.RSMediumRange
