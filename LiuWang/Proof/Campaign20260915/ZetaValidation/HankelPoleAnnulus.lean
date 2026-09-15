import LiuWang.Proof.Campaign20260915.ZetaValidation.HankelLiftPoles

set_option autoImplicit false
noncomputable section
open Complex Set

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

def rsLiftPoleIndices (M : ℕ) : Finset ℤ := (Finset.Icc (-(M : ℤ)) M).erase 0

def rsLiftPoleSet (M : ℕ) : Finset ℂ :=
  (rsLiftPoleIndices M).image (fun n : ℤ => rsHankelLog (n : ℂ))

theorem rsHankelLog_int_re (n : ℤ) :
    (rsHankelLog (n : ℂ)).re = Real.log |(n : ℝ)| := by
  simp [rsHankelLog, log_re, norm_intCast]

theorem rsHankelLog_int_im (n : ℤ) (hn : n ≠ 0) :
    (rsHankelLog (n : ℂ)).im = 0 ∨ (rsHankelLog (n : ℂ)).im = Real.pi := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · left
    have hk : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero (by exact_mod_cast hn))
    simpa only [Int.cast_natCast, ofReal_natCast, ofReal_im] using
      congrArg Complex.im (rsHankelLog_pos hk)
  · right
    have hk : (0 : ℝ) < k := by
      have hk0 : (k : ℤ) ≠ 0 := neg_ne_zero.mp hn
      exact_mod_cast (Nat.pos_of_ne_zero (by exact_mod_cast hk0))
    simpa only [Int.cast_neg, Int.cast_natCast, ofReal_natCast, add_im, ofReal_im,
      mul_im, I_re, I_im, mul_zero, mul_one, zero_add, ofReal_re, add_zero] using
      congrArg Complex.im (rsHankelLog_neg hk)

theorem rsHankelLog_int_injective : Function.Injective (fun n : ℤ => rsHankelLog (n : ℂ)) := by
  intro n k h
  change rsHankelLog (n : ℂ) = rsHankelLog (k : ℂ) at h
  have hz : (rsHankelLog 0).im = Real.pi / 2 := by simp [rsHankelLog]
  by_cases hn : n = 0
  · subst n
    have hi := congrArg Complex.im h
    by_contra hk
    have hh := rsHankelLog_int_im k (Ne.symm hk)
    rw [Int.cast_zero, hz] at hi
    rcases hh with hh | hh <;> linarith [Real.pi_pos]
  · have hk : k ≠ 0 := by
      intro hk
      subst k
      have hi := congrArg Complex.im h
      have hh := rsHankelLog_int_im n hn
      rw [Int.cast_zero, hz] at hi
      rcases hh with hh | hh <;> linarith [Real.pi_pos]
    have he := congrArg exp h
    rw [exp_rsHankelLog (by exact_mod_cast hn), exp_rsHankelLog (by exact_mod_cast hk)] at he
    exact_mod_cast he

theorem rsLiftPole_mem_rectangle {M : ℕ} {u R : ℝ}
    (hu : u < 0) (hR : (M : ℝ) < R) (hR' : R < M + 1) (hM : 0 < M) (n : ℤ) :
    n ∈ rsLiftPoleIndices M ↔ n ≠ 0 ∧ rsHankelLog (n : ℂ) ∈
      Rectangle (u - Real.pi / 4 * I) ((Real.log R : ℂ) + 5 * Real.pi / 4 * I) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR0 : 0 < R := by linarith
  have hv : 0 < Real.log R := Real.log_pos (by linarith)
  have hmem (w : ℂ) : w ∈ Rectangle (u - Real.pi / 4 * I)
      ((Real.log R : ℂ) + 5 * Real.pi / 4 * I) ↔
      u ≤ w.re ∧ w.re ≤ Real.log R ∧ -(Real.pi / 4) ≤ w.im ∧ w.im ≤ 5 * Real.pi / 4 := by
    simpa using mem_Rect
      (show (u - Real.pi / 4 * I : ℂ).re ≤ ((Real.log R : ℂ) + 5 * Real.pi / 4 * I).re by
        simp; linarith)
      (show (u - Real.pi / 4 * I : ℂ).im ≤ ((Real.log R : ℂ) + 5 * Real.pi / 4 * I).im by
        simp; linarith [Real.pi_pos]) w
  simp only [rsLiftPoleIndices, Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨hn, hnlo, hnhi⟩
    have habs : |(n : ℝ)| ≤ M := by exact_mod_cast abs_le.mpr ⟨hnlo, hnhi⟩
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    refine ⟨hn, (hmem _).mpr ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [rsHankelLog_int_re]
      exact hu.le.trans (Real.log_nonneg hn1)
    · rw [rsHankelLog_int_re]
      exact Real.log_le_log (by linarith) (habs.trans hR.le)
    · rcases rsHankelLog_int_im n hn with hh | hh <;> rw [hh] <;> linarith [Real.pi_pos]
    · rcases rsHankelLog_int_im n hn with hh | hh <;> rw [hh] <;> linarith [Real.pi_pos]
  · rintro ⟨hn, hrect⟩
    have hlog := ((hmem _).mp hrect).2.1
    rw [rsHankelLog_int_re] at hlog
    have hn0 : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have hbound : |(n : ℝ)| < M + 1 := ((Real.log_le_log_iff hn0 hR0).mp hlog).trans_lt hR'
    have hZ : |n| < (M : ℤ) + 1 := by exact_mod_cast hbound
    have hZ' : |n| ≤ M := by omega
    exact ⟨hn, (abs_le.mp hZ').1, (abs_le.mp hZ').2⟩

theorem rsLiftPole_strict_interior {M : ℕ} {u R : ℝ}
    (hu : u < 0) (hR : (M : ℝ) < R) {n : ℤ} (hn : n ∈ rsLiftPoleIndices M) :
    u < (rsHankelLog (n : ℂ)).re ∧ (rsHankelLog (n : ℂ)).re < Real.log R ∧
      -(Real.pi / 4) < (rsHankelLog (n : ℂ)).im ∧
        (rsHankelLog (n : ℂ)).im < 5 * Real.pi / 4 := by
  have hi := Finset.mem_erase.mp hn
  have hni := Finset.mem_Icc.mp hi.2
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hi.1
  have hnM : |(n : ℝ)| ≤ M := by exact_mod_cast abs_le.mpr hni
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rsHankelLog_int_re]
    exact hu.trans_le (Real.log_nonneg hn1)
  · rw [rsHankelLog_int_re]
    exact Real.log_lt_log (by linarith) (hnM.trans_lt hR)
  · rcases rsHankelLog_int_im n hi.1 with hh | hh <;> rw [hh] <;> linarith [Real.pi_pos]
  · rcases rsHankelLog_int_im n hi.1 with hh | hh <;> rw [hh] <;> linarith [Real.pi_pos]

end LiuWang.Proof.Campaign20260915.ZetaValidation
