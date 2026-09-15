import LiuWang.Proof.MultiZeroRepulsion.Continuation.GeneralT1Costs

/-! The original-width three-point contradiction for actual ordinary slots in the nondegenerate case. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical ComplexConjugate
open LiuWang.Proof.ZeroRegionFamily LiuWang.Proof.ZeroRegionFamily.Sharp
open LiuWang.Proof.NearOneDensity.Continuation
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.MultiZeroRepulsion.Continuation

theorem t1_primitive_triple_bound {d e f q : ℕ} [NeZero d] [NeZero e] [NeZero f] [NeZero q]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (eta : DirichletCharacter ℂ f)
    (hc : chi ≠ 1) (hp : chi.IsPrimitive) (hc' : psi ≠ 1) (hp' : psi.IsPrimitive)
    (hc'' : eta ≠ 1) (hp'' : eta.IsPrimitive)
    (hproducts : ∀ b c : Bool,
      t1Product chi (t1Orient psi b) ≠ 1 ∧
      t1Product chi (t1Orient eta c) ≠ 1 ∧
      t1Product (t1Orient psi b) (t1Orient eta c) ≠ 1 ∧
      t1Product (t1Product chi (t1Orient psi b)) (t1Orient eta c) ≠ 1)
    (hdq : d ∣ q) (heq : e ∣ q) (hfq : f ∣ q) {x sigma : ℝ}
    (hq : (q : ℝ) ≤ x) (hs : 1 < sigma) (hs1 : sigma ≤ 23 / 20)
    {rho tau ups : ℂ} (hr : 1 / 2 < rho.re) (hr1 : rho.re < 1)
    (ht : 1 / 2 < tau.re) (ht1 : tau.re < 1) (hu : 1 / 2 < ups.re) (hu1 : ups.re < 1)
    (hry : |rho.im| ≤ x / q) (hty : |tau.im| ≤ x / q) (huy : |ups.im| ≤ x / q) :
    (analyticOrderNatAt chi.LFunction rho : ℝ) / (sigma - rho.re) +
      (analyticOrderNatAt psi.LFunction tau : ℝ) / (sigma - tau.re) +
      (analyticOrderNatAt eta.LFunction ups : ℝ) / (sigma - ups.re) ≤
      1 / (sigma - 1) + 7 * stechkinConductorCoeff * Real.log x + 9 / 4 := by
  have hb (b c : Bool) :=
    t1G_primitive_bound chi (t1Orient psi b) (t1Orient eta c)
      hc hp (t1Orient_ne_one hc' b) (t1Orient_primitive hp' b)
      (t1Orient_ne_one hc'' c) (t1Orient_primitive hp'' c)
      (hproducts b c).1 (hproducts b c).2.1 (hproducts b c).2.2.1 (hproducts b c).2.2.2
      hdq heq hfq hq hs hs1 hr hr1
      (rho := rho) (tau := t1OrientValue tau b) (ups := t1OrientValue ups c)
      (by rwa [t1OrientValue_re]) (by rwa [t1OrientValue_re])
      (by rwa [t1OrientValue_re]) (by rwa [t1OrientValue_re]) hry
      (by rwa [t1OrientValue_abs_im]) (by rwa [t1OrientValue_abs_im])
  have h00 := hb false false
  have h10 := hb true false
  have h01 := hb false true
  have h11 := hb true true
  simp only [t1Orient, t1OrientValue, Bool.false_eq_true, if_false, if_true,
    conj_im, conj_re, ordinary_order_conjugate psi (by linarith : 0 < tau.re) ht1,
    ordinary_order_conjugate eta (by linarith : 0 < ups.re) hu1] at h00 h10 h01 h11
  have he := t1_euler_nonneg chi psi eta hs rho.im tau.im ups.im
  linarith only [h00, h10, h01, h11, he]

def t1Sigma (x : ℝ) : ℝ := 1 + (9 / 25) / Real.log x

theorem t1Sigma_parameters {x : ℝ} (hx : 8000000000 ≤ x) :
    1 < t1Sigma x ∧ t1Sigma x ≤ 23 / 20 ∧
    1 / 2 ≤ 1 - (26213 / 100000) / Real.log x ∧
    1 - (26213 / 100000) / Real.log x ≥ 2 - t1Sigma x := by
  have hL := source_log_twenty_two hx
  have hL0 : 0 < Real.log x := by linarith
  have hs : 0 < (9 / 25 : ℝ) / Real.log x := div_pos (by norm_num) hL0
  have hs1 : (9 / 25 : ℝ) / Real.log x ≤ 3 / 20 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  have ha : (26213 / 100000 : ℝ) / Real.log x ≤ 1 / 2 := by
    apply (div_le_iff₀ hL0).mpr
    linarith
  have hg := div_le_div_of_nonneg_right
    (show (26213 / 100000 : ℝ) ≤ 9 / 25 by norm_num) hL0.le
  dsimp [t1Sigma]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem t1_scalar_strict {x beta gamma delta : ℝ} (hx : 8000000000 ≤ x)
    (hb : 1 - (26213 / 100000) / Real.log x < beta) (hb1 : beta < 1)
    (hg : 1 - (26213 / 100000) / Real.log x < gamma) (hg1 : gamma < 1)
    (hd : 1 - (26213 / 100000) / Real.log x < delta) (hd1 : delta < 1) :
    1 / (t1Sigma x - 1) + 7 * stechkinConductorCoeff * Real.log x + 9 / 4 <
      1 / (t1Sigma x - beta) + 1 / (t1Sigma x - gamma) + 1 / (t1Sigma x - delta) := by
  have hL := source_log_twenty_two hx
  have hL0 : 0 < Real.log x := by linarith
  have hs := (t1Sigma_parameters hx).1
  have he : (t1Sigma x - 1) * Real.log x = 9 / 25 := by
    dsimp [t1Sigma]
    field_simp
    ring
  have hl {b : ℝ} (h : 1 - (26213 / 100000) / Real.log x < b) (h1 : b < 1) :
      Real.log x / (62213 / 100000) < 1 / (t1Sigma x - b) := by
    have hh : (1 - b) * Real.log x < 26213 / 100000 := by
      apply (lt_div_iff₀ hL0).mp
      linarith
    apply (div_lt_div_iff₀ (by norm_num) (by linarith)).mpr
    nlinarith
  have hl1 := hl hb hb1
  have hl2 := hl hg hg1
  have hl3 := hl hd hd1
  have hi : 1 / (t1Sigma x - 1) = Real.log x / (9 / 25) := by
    dsimp [t1Sigma]
    field_simp
    ring
  have hk := mul_le_mul_of_nonneg_right conductorCoeff_le_691_2500 hL0.le
  rw [hi]
  norm_num [div_eq_mul_inv] at hl1 hl2 hl3 hk ⊢
  nlinarith only [hl1, hl2, hl3, hk, hL]

theorem t1Orient_changeLevel {d q : ℕ} (chi : DirichletCharacter ℂ d) (hd : d ∣ q) (b : Bool) :
    (t1Orient chi b).changeLevel hd = t1Orient (chi.changeLevel hd) b := by
  cases b <;> simp [t1Orient]

theorem t1_ordinary_nondegenerate_impossible {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 8000000000 ≤ x) (hq : (q : ℝ) ≤ x)
    (p r s : ZeroSlots q (1 - (26213 / 100000) / Real.log x) (x / q))
    (hp : p.character ≠ 1) (hr : r.character ≠ 1) (hs : s.character ≠ 1)
    (hproducts : ∀ b c : Bool,
      p.character * t1Orient r.character b ≠ 1 ∧
      p.character * t1Orient s.character c ≠ 1 ∧
      t1Orient r.character b * t1Orient s.character c ≠ 1 ∧
      p.character * t1Orient r.character b * t1Orient s.character c ≠ 1) : False := by
  let chi := p.character.primitiveCharacter
  let psi := r.character.primitiveCharacter
  let eta := s.character.primitiveCharacter
  let : NeZero p.character.conductor := ⟨p.character.conductor_ne_zero⟩
  let : NeZero r.character.conductor := ⟨r.character.conductor_ne_zero⟩
  let : NeZero s.character.conductor := ⟨s.character.conductor_ne_zero⟩
  have hd := p.character.conductor_dvd_level
  have he := r.character.conductor_dvd_level
  have hf := s.character.conductor_dvd_level
  have hprods (b c : Bool) :
      t1Product chi (t1Orient psi b) ≠ 1 ∧ t1Product chi (t1Orient eta c) ≠ 1 ∧
      t1Product (t1Orient psi b) (t1Orient eta c) ≠ 1 ∧
      t1Product (t1Product chi (t1Orient psi b)) (t1Orient eta c) ≠ 1 := by
    have hh := hproducts b c
    have hde := t1Product_changeLevel chi (t1Orient psi b) hd he
    have hdf := t1Product_changeLevel chi (t1Orient eta c) hd hf
    have hef := t1Product_changeLevel (t1Orient psi b) (t1Orient eta c) he hf
    have hdef := t1Product_changeLevel (t1Product chi (t1Orient psi b)) (t1Orient eta c)
      (Nat.lcm_dvd hd he) hf
    rw [hde] at hdef
    simp only [t1Orient_changeLevel, chi, psi, eta,
      DirichletCharacter.changeLevel_primitiveCharacter] at hde hdf hef hdef
    have lift {d : ℕ} (a : DirichletCharacter ℂ d) (h : d ∣ q) (hn : a.changeLevel h ≠ 1) : a ≠ 1 := by
      intro ha
      exact hn (by rw [ha, map_one])
    refine ⟨lift _ (Nat.lcm_dvd hd he) ?_, lift _ (Nat.lcm_dvd hd hf) ?_,
      lift _ (Nat.lcm_dvd he hf) ?_, lift _ (Nat.lcm_dvd (Nat.lcm_dvd hd he) hf) ?_⟩
    · rw [hde]; exact hh.1
    · rw [hdf]; exact hh.2.1
    · rw [hef]; exact hh.2.2.1
    · rw [hdef]; exact hh.2.2.2
  obtain ⟨hsg, hsg1, ha, _⟩ := t1Sigma_parameters hx
  have hz1 := mem_strictZeroValues.mp p.zero_mem
  have hz2 := mem_strictZeroValues.mp r.zero_mem
  have hz3 := mem_strictZeroValues.mp s.zero_mem
  have hm := t1_primitive_triple_bound chi psi eta
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one _ hp)
    p.character.primitiveCharacter_isPrimitive
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one _ hr)
    r.character.primitiveCharacter_isPrimitive
    (BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one _ hs)
    s.character.primitiveCharacter_isPrimitive hprods hd he hf hq hsg hsg1
    (ha.trans_lt hz1.2.2.1) hz1.2.2.2.1 (ha.trans_lt hz2.2.2.1) hz2.2.2.2.1
    (ha.trans_lt hz3.2.2.1) hz3.2.2.2.1 hz1.2.2.2.2 hz2.2.2.2.2 hz3.2.2.2.2
  have h1 : (1 : ℝ) ≤ analyticOrderNatAt chi.LFunction p.value := by
    rw [← analyticOrderNatAt_LFunction_eq_primitive p.character hp hz1.2.1]
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) p.index_lt)
  have h2 : (1 : ℝ) ≤ analyticOrderNatAt psi.LFunction r.value := by
    rw [← analyticOrderNatAt_LFunction_eq_primitive r.character hr hz2.2.1]
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) r.index_lt)
  have h3 : (1 : ℝ) ≤ analyticOrderNatAt eta.LFunction s.value := by
    rw [← analyticOrderNatAt_LFunction_eq_primitive s.character hs hz3.2.1]
    exact_mod_cast Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) s.index_lt)
  have h1' := div_le_div_of_nonneg_right h1 (show 0 ≤ t1Sigma x - p.value.re by linarith [hz1.2.2.2.1])
  have h2' := div_le_div_of_nonneg_right h2 (show 0 ≤ t1Sigma x - r.value.re by linarith [hz2.2.2.2.1])
  have h3' := div_le_div_of_nonneg_right h3 (show 0 ≤ t1Sigma x - s.value.re by linarith [hz3.2.2.2.1])
  have hstrict := t1_scalar_strict hx hz1.2.2.1 hz1.2.2.2.1 hz2.2.2.1 hz2.2.2.2.1 hz3.2.2.1 hz3.2.2.2.1
  linarith only [hm, h1', h2', h3', hstrict]

end LiuWang.Proof.MultiZeroRepulsion.Continuation
