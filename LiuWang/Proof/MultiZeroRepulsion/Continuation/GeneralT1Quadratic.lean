import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Mass

/-! Three repeated quadratic labels: all six principal pair-product poles paid simultaneously. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1_primitive_three_selected {q : ℕ} [NeZero q] {alpha y sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) (ha : 1 / 2 ≤ alpha)
    (p r s : ZeroSlots q alpha y) (hpr : p ≠ r) (hps : p ≠ s) (hrs : r ≠ s)
    (hcr : r.character = p.character) (hcs : s.character = p.character)
    (hc : p.character ≠ 1) (hp : p.character.IsPrimitive) (t : ℝ) :
    dampedLogDeriv p.character sigma (stechkinSigma sigma) stechkinK t +
      reflectedKernel sigma t p.value + reflectedKernel sigma t r.value +
      reflectedKernel sigma t s.value ≤
      stechkinConductorCoeff * (Real.log q + Real.log (max 1 |t|) - Real.log Real.pi) + 4 / 15 := by
  have hm := primitive_ordinary_mass_le hc hp hs t (strictZeroValues p.character alpha y)
    (fun z hz => ha.trans_lt (mem_strictZeroValues.mp hz).2.2.1)
  change ordinaryMass p.character sigma t _ ≤ _ at hm
  have hf := primitive_full_zero_sum_bound hc hp hs hs1 t
  linarith [t1_three_slots_mass_le hs p r s t hpr hps hrs hcr hcs]

theorem t1_conjugate_ne {q : ℕ} [NeZero q] {alpha y : ℝ}
    {p r : ZeroSlots q alpha y} (h : p ≠ conjugateSlot r) : r ≠ conjugateSlot p := by
  intro he
  have hh := congrArg conjugateSlot he
  rw [conjugateSlot_involutive] at hh
  exact h hh.symm

theorem t1_pair_height {q : ℕ} {x a b : ℝ}
    (hya : |a| ≤ x / q) (hyb : |b| ≤ x / q) :
    |a + b| ≤ 2 * x / q ∧ |a - b| ≤ 2 * x / q := by
  have hh := abs_add_le a b
  have hh' := abs_sub a b
  rw [mul_div_assoc]
  constructor <;> linarith

theorem t1_principal_pair_cost {q : ℕ} [NeZero q] {x sigma t : ℝ}
    (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20)
    (ht : |t| ≤ 2 * x / q) :
    dampedLogDeriv (1 : DirichletCharacter ℂ q) sigma (stechkinSigma sigma) stechkinK t ≤
    poleDifference sigma t + stechkinConductorCoeff *
      (Real.log x + Real.log 2 - Real.log q - Real.log Real.pi) +
      23 / 40 - 11 * stechkinK / 30 + principalPrimeCost q sigma := by
  have hh := principal_all_height (q := q) hs hs1 t
  have hl := t1_height_log (dvd_refl q) hq (by norm_num : (1 : ℝ) ≤ 2) ht
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  linarith

theorem t1_primitive_triple_cost {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) {x sigma a b c : ℝ}
    (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20)
    (hab : |a + b| ≤ 2 * x / q) (hac : |c| ≤ x / q) :
    dampedLogDeriv chi sigma (stechkinSigma sigma) stechkinK (a + b + c) ≤
      stechkinConductorCoeff * (Real.log x + Real.log 3 - Real.log Real.pi) + 4 / 15 := by
  have ht : |a + b + c| ≤ 3 * x / q := by
    have hh := abs_add_le (a + b) c
    rw [mul_div_assoc] at hab ⊢
    linarith
  have hl := t1_height_log (dvd_refl q) hq (by norm_num : (1 : ℝ) ≤ 3) ht
  have hm := mul_le_mul_of_nonneg_left hl conductorCoeff_bounds.1
  linarith [primitive_damped_bound hc hp hs hs1 (a + b + c)]

theorem t1_principal_prime_cost {q : ℕ} [NeZero q] {sigma : ℝ}
    (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20) :
    principalPrimeCost q sigma ≤ stechkinConductorCoeff * Real.log q + 941 / 1600 := by
  have hh := general_finite_prime_cost q.primeFactors
    (fun _ h => Nat.prime_of_mem_primeFactors h) hs hs1
  have hlog := disjoint_prime_support_log (NeZero.pos q) (by norm_num : 0 < 1)
    (one_dvd q) q.primeFactors (fun _ h => h) (fun _ _ => Nat.coprime_one_right _)
  simp only [Nat.cast_one, Real.log_one, zero_add] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog conductorCoeff_bounds.1
  change principalPrimeCost q sigma ≤ _ at hh
  linarith

theorem t1_quadratic_three_mother {q : ℕ} [NeZero q] {x alpha sigma : ℝ}
    (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 51 / 50) (ha : 9 / 10 ≤ alpha)
    (p r s : ZeroSlots q alpha (x / q))
    (hpr : p ≠ r) (hps : p ≠ s) (hrs : r ≠ s)
    (hcpr : p ≠ conjugateSlot r) (hcps : p ≠ conjugateSlot s) (hcrs : r ≠ conjugateSlot s)
    (hcr : r.character = p.character) (hcs : s.character = p.character)
    (hc : p.character ≠ 1) (hp : p.character.IsPrimitive) (hsq : p.character ^ 2 = 1)
    (hgp : 1 - p.value.re ≤ sigma - 1) (hgr : 1 - r.value.re ≤ sigma - 1)
    (hgs : 1 - s.value.re ≤ sigma - 1) :
    1 / (sigma - p.value.re) + 1 / (sigma - r.value.re) + 1 / (sigma - s.value.re) ≤
      1 / (sigma - 1) + 7 * stechkinConductorCoeff * Real.log x + 9 / 4 := by
  have hs15 : sigma ≤ 23 / 20 := by linarith
  have ha5 : 1 / 2 ≤ alpha := by linarith
  have hprod : p.character * p.character = 1 := by simpa only [pow_two] using hsq
  have hinv : p.character⁻¹ = p.character := (mul_eq_one_iff_eq_inv.mp hprod).symm
  have hcp : (conjugateSlot p).character = p.character := by rw [conjugateSlot_character, hinv]
  have hcr' : (conjugateSlot r).character = p.character := by rw [conjugateSlot_character, hcr, hinv]
  have hcs' : (conjugateSlot s).character = p.character := by rw [conjugateSlot_character, hcs, hinv]
  have hconj {a b : ZeroSlots q alpha (x / q)} (h : a ≠ b) : conjugateSlot a ≠ conjugateSlot b :=
    fun he => h (conjugateSlot_involutive.injective he)
  have h1 := t1_primitive_three_selected hs hs15 ha5 p r s hpr hps hrs hcr hcs hc hp p.value.im
  have h1' := t1_primitive_three_selected hs hs15 ha5 p (conjugateSlot r) (conjugateSlot s)
    hcpr hcps (hconj hrs) hcr' hcs' hc hp p.value.im
  have h2 := t1_primitive_three_selected hs hs15 ha5 r p s (Ne.symm hpr) hrs hps
    hcr.symm (hcs.trans hcr.symm) (hcr ▸ hc) (hcr ▸ hp) r.value.im
  have h2' := t1_primitive_three_selected hs hs15 ha5 r (conjugateSlot p) (conjugateSlot s)
    (t1_conjugate_ne hcpr) hcrs (hconj hps) (hcp.trans hcr.symm) (hcs'.trans hcr.symm)
    (hcr ▸ hc) (hcr ▸ hp) r.value.im
  have h3 := t1_primitive_three_selected hs hs15 ha5 s p r (Ne.symm hps) (Ne.symm hrs) hpr
    hcs.symm (hcr.trans hcs.symm) (hcs ▸ hc) (hcs ▸ hp) s.value.im
  have h3' := t1_primitive_three_selected hs hs15 ha5 s (conjugateSlot p) (conjugateSlot r)
    (t1_conjugate_ne hcps) (t1_conjugate_ne hcrs) (hconj hpr)
    (hcp.trans hcs.symm) (hcr'.trans hcs.symm) (hcs ▸ hc) (hcs ▸ hp) s.value.im
  rw [hcr] at h2 h2'
  rw [hcs] at h3 h3'
  rw [conjugateSlot_value, conjugateSlot_value] at h1' h2' h3'
  have zp := mem_strictZeroValues.mp p.zero_mem
  have zr := mem_strictZeroValues.mp r.zero_mem
  have zs := mem_strictZeroValues.mp s.zero_mem
  have bp : 9 / 10 ≤ p.value.re := ha.trans zp.2.2.1.le
  have br : 9 / 10 ≤ r.value.re := ha.trans zr.2.2.1.le
  have bs : 9 / 10 ≤ s.value.re := ha.trans zs.2.2.1.le
  have k1 : 1 / (sigma - p.value.re) ≤ reflectedKernel sigma p.value.im p.value :=
    selected_pair_dominates hs ⟨zp.2.1, zp.2.2.2.1⟩
  have k2 : 1 / (sigma - r.value.re) ≤ reflectedKernel sigma r.value.im r.value :=
    selected_pair_dominates hs ⟨zr.2.1, zr.2.2.2.1⟩
  have k3 : 1 / (sigma - s.value.re) ≤ reflectedKernel sigma s.value.im s.value :=
    selected_pair_dominates hs ⟨zs.2.1, zs.2.2.2.1⟩
  have pairPay (a b : ℂ) (ba : 9 / 10 ≤ a.re) (ba1 : a.re < 1)
      (bb : 9 / 10 ≤ b.re) (bb1 : b.re < 1)
      (ga : 1 - a.re ≤ sigma - 1) (gb : 1 - b.re ≤ sigma - 1) :
      poleDifference sigma (a.im + b.im) + poleDifference sigma (a.im - b.im) ≤
        reflectedKernel sigma a.im b + reflectedKernel sigma a.im (conj b) +
        reflectedKernel sigma b.im a + reflectedKernel sigma b.im (conj a) := by
    have hm := t1_two_kernels_pay_pole hs hs1 bb bb1 ba ba1 gb ga
      (t := a.im) (u := b.im) (v := a.im - b.im) rfl (by ring)
    have hh := t1_two_kernels_pay_pole hs hs1
      (rho := conj b) (tau := conj a) bb bb1 ba ba1 gb ga
      (t := a.im) (u := b.im) (v := a.im + b.im) (by simp) (by simp [add_comm])
    linarith
  have pay12 := pairPay p.value r.value bp zp.2.2.2.1 br zr.2.2.2.1 hgp hgr
  have pay13 := pairPay p.value s.value bp zp.2.2.2.1 bs zs.2.2.2.1 hgp hgs
  have pay23 := pairPay r.value s.value br zr.2.2.2.1 bs zs.2.2.2.1 hgr hgs
  have hpos := triple_euler_nonneg p.character p.character p.character hs p.value.im r.value.im s.value.im
  simp only [Fin.sum_univ_succ, tripleCoefficients, tripleCharacters, tripleHeights,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, one_mul,
    hinv, hprod] at hpos
  have h0 := principal_real_strong (q := q) hs hs15
  have p12 := t1_pair_height zp.2.2.2.2 zr.2.2.2.2
  have p13 := t1_pair_height zp.2.2.2.2 zs.2.2.2.2
  have p23 := t1_pair_height zr.2.2.2.2 zs.2.2.2.2
  have h4 := t1_principal_pair_cost hq hs hs15 p12.1
  have h5 := t1_principal_pair_cost hq hs hs15 p12.2
  have h6 := t1_principal_pair_cost hq hs hs15 p13.1
  have h7 := t1_principal_pair_cost hq hs hs15 p13.2
  have h8 := t1_principal_pair_cost hq hs hs15 p23.1
  have h9 := t1_principal_pair_cost hq hs hs15 p23.2
  have h10 := t1_primitive_triple_cost p.character hc hp hq hs hs15 p12.1 zs.2.2.2.2
  have h11 := t1_primitive_triple_cost p.character hc hp hq hs hs15
    (a := p.value.im) (b := -r.value.im) (c := s.value.im)
    (by simpa only [← sub_eq_add_neg] using p12.2) zs.2.2.2.2
  have h12 := t1_primitive_triple_cost p.character hc hp hq hs hs15 (c := -s.value.im) p12.1
    (by simpa only [abs_neg] using zs.2.2.2.2)
  have h13 := t1_primitive_triple_cost p.character hc hp hq hs hs15
    (a := p.value.im) (b := -r.value.im) (c := -s.value.im)
    (by simpa only [← sub_eq_add_neg] using p12.2) (by simpa only [abs_neg] using zs.2.2.2.2)
  simp only [← sub_eq_add_neg] at h11 h12 h13
  have l1 := conductor_height_log_max_le hq zp.2.2.2.2
  have l2 := conductor_height_log_max_le hq zr.2.2.2.2
  have l3 := conductor_height_log_max_le hq zs.2.2.2.2
  have lm1 := mul_le_mul_of_nonneg_left l1 conductorCoeff_bounds.1
  have lm2 := mul_le_mul_of_nonneg_left l2 conductorCoeff_bounds.1
  have lm3 := mul_le_mul_of_nonneg_left l3 conductorCoeff_bounds.1
  have hP := t1_principal_prime_cost (q := q) hs hs15
  have hq0 := mul_nonneg conductorCoeff_bounds.1 (Real.log_natCast_nonneg q)
  have hk : 11 / 40 ≤ stechkinConductorCoeff := by
    unfold stechkinConductorCoeff
    linarith [stechkinK_le]
  have hconst : stechkinConductorCoeff * (3 * Real.log 2 + Real.log 3 - 7 * Real.log Real.pi) +
      4 * (4 / 15 : ℝ) + 3 * (23 / 40 - 11 * stechkinK / 30) - 3 / 4 +
      2 * (941 / 1600) ≤ 9 / 4 := by
    nlinarith only [hk, stechkinK_ge, Real.log_two_lt_d9, Real.log_three_lt_d9,
      LiuWang.Proof.NearOneDensity.log_pi_ge_eleven_tenths]
  linear_combination
    (1 / 2) * h1 + (1 / 2) * h1' + (1 / 2) * h2 + (1 / 2) * h2' +
    (1 / 2) * h3 + (1 / 2) * h3' + k1 + k2 + k3 +
    (1 / 2) * pay12 + (1 / 2) * pay13 + (1 / 2) * pay23 +
    (1 / 4) * hpos + h0 +
    (1 / 2) * h4 + (1 / 2) * h5 + (1 / 2) * h6 +
    (1 / 2) * h7 + (1 / 2) * h8 + (1 / 2) * h9 +
    (1 / 4) * h10 + (1 / 4) * h11 + (1 / 4) * h12 + (1 / 4) * h13 +
    lm1 + lm2 + lm3 + 2 * hP + hq0 + hconst

end LiuWang.Proof.MultiZeroRepulsion.Continuation
