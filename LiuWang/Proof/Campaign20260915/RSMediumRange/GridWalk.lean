import LiuWang.Proof.Campaign20260915.RSMediumRange.GridLogTable

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace LiuWang.Proof.Campaign20260915.RSMediumRange

def GridStepCheck (s : MediumState) (r : MediumRow) : Prop :=
  s.p < r.p ∧ r.p ≤ 100000000 ∧
  1024 ≤ r.p / 2 ^ r.k ∧ r.p / 2 ^ r.k < 2048 ∧
  gridRowLo r.p r.k = r.logLo ∧ gridRowHi r.p r.k = r.logHi ∧
  packedCompositeRun (s.p + 1) (r.p - s.p - 1) r.gap ∧ CellCheck s r.p r.root

instance (s : MediumState) (r : MediumRow) : Decidable (GridStepCheck s r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def GridWalk : MediumState → List MediumRow → Prop
  | _, [] => True
  | s, r :: rs => GridStepCheck s r ∧ GridWalk (nextState s r) rs

instance (s : MediumState) (rs : List MediumRow) : Decidable (GridWalk s rs) := by
  induction rs generalizing s with
  | nil => exact instDecidableTrue
  | cons r rs ih =>
    unfold GridWalk
    exact instDecidableAnd

noncomputable section

theorem actual_next_from_bounds {s : MediumState} {r : MediumRow}
    (hs : s.Actual) (hsp : s.p < r.p) (hp : r.p.Prime)
    (hg : NoPrimeGap s.p r.p)
    (hl : (FixedBracket.mk r.logLo r.logHi).Contains (Real.log r.p)) :
    (nextState s r).Actual := by
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

theorem actual_grid_next {s : MediumState} {r : MediumRow}
    (ha : s.Actual) (hc : GridStepCheck s r) (hp : r.p.Prime) :
    (nextState s r).Actual := by
  obtain ⟨hsp, _, hm, hh, hlo, hhi, hgap, _⟩ := hc
  have hl := gridRow_bounds hm hh
  rw [hlo, hhi] at hl
  exact actual_next_from_bounds ha hsp hp (gap_of_packed hsp hgap) hl

theorem actual_grid_cell {s : MediumState} {r : MediumRow} {x : ℝ}
    (hs : 16000 ≤ s.p) (ha : s.Actual) (hc : GridStepCheck s r)
    (hx : (s.p : ℝ) ≤ x) (hxr : x < r.p) : MediumBounds x := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg s.p).trans hx
  have hlo : s.p ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr hx
  have hhi : ⌊x⌋₊ < r.p := by exact_mod_cast (Nat.floor_le hx0).trans_lt hxr
  have hg := gap_of_packed hc.1 hc.2.2.2.2.2.2.1
  exact actual_cell hs hc.1.le ha hc.2.2.2.2.2.2.2 hx hxr.le
    (primesLE_of_gap hg hlo hhi)

theorem gridWalk_mono {s : MediumState} {rs : List MediumRow}
    (hc : GridWalk s rs) : s.p ≤ (rs.foldl nextState s).p := by
  induction rs generalizing s with
  | nil => exact le_rfl
  | cons r rs ih =>
    exact hc.1.1.le.trans (ih hc.2)

theorem gridWalk_sound {s : MediumState} {rs : List MediumRow}
    (hs : 16000 ≤ s.p) (ha : s.Actual) (hc : GridWalk s rs)
    (hp : ∀ r ∈ rs, r.p.Prime) :
    (rs.foldl nextState s).Actual ∧
      ∀ x : ℝ, (s.p : ℝ) ≤ x → x < (rs.foldl nextState s).p → MediumBounds x := by
  induction rs generalizing s with
  | nil => exact ⟨ha, fun x hx hhi => (not_lt_of_ge hx hhi).elim⟩
  | cons r rs ih =>
    obtain ⟨hstep, htail⟩ := hc
    have hnext := actual_grid_next ha hstep (hp r (by simp))
    have hsp : s.p < r.p := hstep.1
    have ht := ih (s := nextState s r) (by change 16000 ≤ r.p; omega)
      hnext htail (fun r hr => hp r (by simp [hr]))
    refine ⟨ht.1, ?_⟩
    intro x hx hhi
    by_cases hxr : x < r.p
    · exact actual_grid_cell hs ha hstep hx hxr
    · exact ht.2 x (le_of_not_gt hxr) hhi

theorem certifiedChunk_of_gridWalk {s t : MediumState} {rs : List MediumRow}
    (hs : 16000 ≤ s.p) (he : rs.foldl nextState s = t)
    (hc : GridWalk s rs)
    (hpr : ∀ r ∈ rs, 2 ≤ r.p ∧ r.p ≤ 100000000)
    (hprime : Nat.Coprime (rs.map MediumRow.p).prod factorialBase) :
    CertifiedChunk s t := by
  have hp : ∀ r ∈ rs, r.p.Prime := by
    have h := batch_prime_of_coprime_factorial
      (ps := rs.map MediumRow.p) (by
        intro p hp
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
        exact hpr r hr) (by rwa [factorialBase_eq])
    intro r hr
    exact h r.p (List.mem_map.mpr ⟨r, hr, rfl⟩)
  refine ⟨by simpa only [he] using gridWalk_mono hc, ?_⟩
  intro ha
  simpa only [he] using gridWalk_sound hs ha hc hp

theorem certified_terminal {s : MediumState} {b root code : ℕ}
    (hs : 16000 ≤ s.p) (hb : s.p ≤ b)
    (hc : CellCheck s b root)
    (hgap : packedCompositeRun (s.p + 1) (b - s.p) code)
    (ha : s.Actual) :
    ∀ x : ℝ, (s.p : ℝ) ≤ x → x ≤ b → MediumBounds x := by
  intro x hx hxb
  have hx0 : 0 ≤ x := (Nat.cast_nonneg s.p).trans hx
  have hnlo : s.p ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr hx
  have hnhi : ⌊x⌋₊ < b + 1 := by
    have h : (⌊x⌋₊ : ℝ) < (b + 1 : ℕ) := by
      have := (Nat.floor_le hx0).trans hxb
      push_cast
      linarith
    exact_mod_cast h
  have hg : NoPrimeGap s.p (b + 1) := by
    apply gap_of_packed (by omega)
    convert hgap using 1
    omega
  exact actual_cell hs hb ha hc hx hxb (primesLE_of_gap hg hnlo hnhi)

#print axioms certifiedChunk_of_gridWalk
#print axioms certified_terminal

end
end LiuWang.Proof.Campaign20260915.RSMediumRange
