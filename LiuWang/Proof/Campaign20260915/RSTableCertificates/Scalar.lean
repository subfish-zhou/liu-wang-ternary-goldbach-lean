import LiuWang.Proof.Campaign20260915.Totient.RSEpsilonTerminal

set_option autoImplicit false
set_option Elab.async false

namespace LiuWang.Proof.Campaign20260915.RSTableCertificates

open LiuWang.Proof.Campaign20260915.Totient

def taylor (s : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 12, s ^ j / (j.factorial : ℚ)

def ExpCertificate (s q u : ℚ) : Prop :=
  0 ≤ s ∧ 0 < q ∧ 0 ≤ u ∧ q ≤ taylor (s / 128) ∧ 1 ≤ u * q ^ 128

instance (s q u : ℚ) : Decidable (ExpCertificate s q u) := by
  unfold ExpCertificate
  infer_instance

noncomputable section

theorem exp_certificate_sound {s q u : ℚ} (h : ExpCertificate s q u) :
    Real.exp (-(s : ℝ)) ≤ (u : ℝ) := by
  obtain ⟨hs, hq, hu, ht, hp⟩ := h
  have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) ≤ u := by exact_mod_cast hu
  have htR : (q : ℝ) ≤ ∑ j ∈ Finset.range 12,
      ((s : ℝ) / 128) ^ j / (j.factorial : ℝ) := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr ht
    simpa only [taylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_natCast] using hh
  have he := htR.trans (Real.sum_le_exp_of_nonneg (by positivity) 12)
  have he' := pow_le_pow_left₀ hqR.le he 128
  rw [← Real.exp_nat_mul] at he'
  have hid : (128 : ℝ) * ((s : ℝ) / 128) = s := by ring
  norm_num only [Nat.cast_ofNat] at he'
  rw [hid] at he'
  have hpR : (1 : ℝ) ≤ (u : ℝ) * (q : ℝ) ^ 128 := by exact_mod_cast hp
  rw [Real.exp_neg, ← one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr
    (hpR.trans (mul_le_mul_of_nonneg_left he' huR))

end

def coefficient (m : ℕ) (b : ℚ) : ℚ :=
  (0.0003647 * (m : ℚ) ^ 2 + 1.298 * m + 0.1592) /
    ((1 - ((m : ℚ) + 0.123) * b / (1748 * (m : ℚ) ^ 2)) * (m : ℚ) ^ 2)

def epsilon (m : ℕ) (d : ℚ) : ℚ :=
  d / 2 * ((((1 + d) ^ (m + 1) + 1) / 2) ^ m + m)

structure Row where
  b : ℚ
  m : ℕ
  d : ℚ
  e : ℚ
  k : ℚ
  lowS : ℚ
  lowQ : ℚ
  lowU : ℚ
  highQ : ℚ
  highU : ℚ

def Row.Valid (r : Row) : Prop :=
  2 ≤ r.b ∧ 1 ≤ r.m ∧ 0 < r.d ∧ 0 ≤ r.k ∧
  r.b < 1748 * (r.m : ℚ) ^ 2 / ((r.m : ℚ) + 0.123) ∧
  r.lowS ≤ r.b / 2 ∧
  ExpCertificate r.lowS r.lowQ r.lowU ∧
  ExpCertificate (9.99 * r.m + r.b / 175) r.highQ r.highU ∧
  (r.m : ℚ) * r.d + r.lowU ^ 2 < 1 ∧
  r.k * r.lowU + coefficient r.m r.b * r.highU ≤ (r.d / 2) ^ (r.m + 1) ∧
  epsilon r.m r.d + 2 * r.lowU ^ 2 ≤ r.e

instance (r : Row) : Decidable r.Valid := by
  unfold Row.Valid
  infer_instance

noncomputable section

def budget (m : ℕ) (b k : ℝ) : ℝ :=
  k * Real.exp (-b / 2) +
    (0.0003647 * (m : ℝ) ^ 2 + 1.298 * m + 0.1592) /
      ((1 - ((m : ℝ) + 0.123) * b / (1748 * (m : ℝ) ^ 2)) * (m : ℝ) ^ 2) *
      Real.exp (-(9.99 * m + b / 175))

theorem coefficient_nonneg {m : ℕ} {b : ℚ} (hm : 1 ≤ m)
    (hb : b < 1748 * (m : ℚ) ^ 2 / ((m : ℚ) + 0.123)) :
    0 ≤ coefficient m b := by
  have hmR : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  have hden : 0 < 1 - ((m : ℚ) + 0.123) * b / (1748 * (m : ℚ) ^ 2) := by
    have hb' := (lt_div_iff₀ (by positivity : (0 : ℚ) < m + 0.123)).mp hb
    have hh : ((m : ℚ) + 0.123) * b / (1748 * (m : ℚ) ^ 2) < 1 :=
      (div_lt_one (by positivity)).mpr (by nlinarith)
    linarith
  unfold coefficient
  positivity

theorem epsilon_cast (m : ℕ) (d : ℚ) :
    (epsilon m d : ℝ) = rsEpsilon m (d : ℝ) := by
  unfold epsilon rsEpsilon
  push_cast
  rfl

theorem row_exp_bounds {r : Row} (h : r.Valid) :
    Real.exp (-(r.b : ℝ) / 2) ≤ (r.lowU : ℝ) ∧
      Real.exp (-(r.b : ℝ)) ≤ (r.lowU : ℝ) ^ 2 := by
  have hs : (r.lowS : ℝ) ≤ (r.b : ℝ) / 2 := by exact_mod_cast h.2.2.2.2.2.1
  have he := exp_certificate_sound h.2.2.2.2.2.2.1
  have hl : Real.exp (-(r.b : ℝ) / 2) ≤ (r.lowU : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans he
  refine ⟨hl, ?_⟩
  have hh := pow_le_pow_left₀ (Real.exp_pos _).le hl 2
  rw [← Real.exp_nat_mul] at hh
  convert hh using 1
  congr 1
  push_cast
  ring

theorem row_budget {r : Row} (h : r.Valid) :
    budget r.m r.b r.k ≤ ((r.d : ℝ) / 2) ^ (r.m + 1) := by
  have hlow := (row_exp_bounds h).1
  obtain ⟨_, hm, _, hk, hb, _, _, hh, _, hpay, _⟩ := h
  have hhigh := exp_certificate_sound hh
  have hkR : (0 : ℝ) ≤ r.k := by exact_mod_cast hk
  have hcR : (0 : ℝ) ≤ coefficient r.m r.b := by
    exact_mod_cast coefficient_nonneg hm hb
  have hpayR : (r.k : ℝ) * r.lowU + (coefficient r.m r.b : ℝ) * r.highU ≤
      ((r.d : ℝ) / 2) ^ (r.m + 1) := by exact_mod_cast hpay
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hlow hkR)
    (mul_le_mul_of_nonneg_left hhigh hcR)
  have hco : (coefficient r.m r.b : ℝ) =
      (0.0003647 * (r.m : ℝ) ^ 2 + 1.298 * r.m + 0.1592) /
        ((1 - ((r.m : ℝ) + 0.123) * r.b / (1748 * (r.m : ℝ) ^ 2)) *
          (r.m : ℝ) ^ 2) := by
    unfold coefficient
    push_cast
    rfl
  push_cast at hsum
  simpa only [budget, hco] using hsum.trans hpayR

theorem row_cut {r : Row} (h : r.Valid) :
    1 < Real.exp (r.b : ℝ) ∧
      1 + (r.m : ℝ) * r.d * Real.exp (r.b : ℝ) < Real.exp (r.b : ℝ) := by
  have hb : (2 : ℝ) ≤ r.b := by exact_mod_cast h.1
  have hcut : (r.m : ℝ) * r.d + (r.lowU : ℝ) ^ 2 < 1 := by
    exact_mod_cast h.2.2.2.2.2.2.2.2.1
  have he := (row_exp_bounds h).2
  have hexp := Real.exp_pos (r.b : ℝ)
  refine ⟨(Real.one_lt_exp_iff).mpr (by linarith), ?_⟩
  have hh : Real.exp (-(r.b : ℝ)) + (r.m : ℝ) * r.d < 1 := by linarith
  have ht := mul_lt_mul_of_pos_right hh hexp
  rw [add_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at ht
  simpa only [one_mul] using ht

theorem row_epsilon_gap {r : Row} (h : r.Valid) :
    rsEpsilon r.m (r.d : ℝ) + 2 * Real.exp (-(r.b : ℝ)) ≤ (r.e : ℝ) := by
  have hg : (epsilon r.m r.d : ℝ) + 2 * (r.lowU : ℝ) ^ 2 ≤ (r.e : ℝ) := by
    exact_mod_cast h.2.2.2.2.2.2.2.2.2.2
  rw [epsilon_cast] at hg
  linarith [(row_exp_bounds h).2]

theorem row_root {r : Row} (h : r.Valid) :
    2 * (budget r.m r.b r.k) ^ (1 / ((r.m : ℝ) + 1)) ≤ (r.d : ℝ) := by
  have hd : (0 : ℝ) ≤ r.d := Rat.cast_nonneg.mpr h.2.2.1.le
  have hc : (0 : ℝ) ≤ coefficient r.m r.b :=
    Rat.cast_nonneg.mpr (coefficient_nonneg h.2.1 h.2.2.2.2.1)
  have hk : (0 : ℝ) ≤ r.k := Rat.cast_nonneg.mpr h.2.2.2.1
  have hc' : 0 ≤
      (0.0003647 * (r.m : ℝ) ^ 2 + 1.298 * r.m + 0.1592) /
        ((1 - ((r.m : ℝ) + 0.123) * r.b / (1748 * (r.m : ℝ) ^ 2)) *
          (r.m : ℝ) ^ 2) := by
    unfold coefficient at hc
    push_cast at hc
    exact hc
  have hb : 0 ≤ budget r.m r.b r.k := by unfold budget; positivity
  have hp := Real.rpow_le_rpow hb (row_budget h)
    (show (0 : ℝ) ≤ ((r.m + 1 : ℕ) : ℝ)⁻¹ by positivity)
  rw [Real.pow_rpow_inv_natCast (by positivity) (Nat.succ_ne_zero _)] at hp
  norm_num only [Nat.cast_add, Nat.cast_one, ← one_div] at hp
  linarith

theorem trivial_kernel_le_one {x : ℝ} (hx : 2 ≤ x) :
    rsTrivialKernel x ≤ 1 := by
  have hmono := rsTrivialKernel_antitone (by norm_num : (1 : ℝ) < 2)
    (by linarith : 1 < x) hx
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (3 / 4 : ℝ)⁻¹)
  rw [Real.log_inv] at hl
  norm_num at hl
  have hk : rsTrivialKernel 2 ≤ 1 := by
    unfold rsTrivialKernel
    norm_num
    linarith
  exact hmono.trans hk

theorem absorb_remainders {b e E x y : ℝ} (hb : 2 ≤ b)
    (hx : Real.exp b ≤ x) (hgap : e + 2 * Real.exp (-b) ≤ E)
    (hl : x * (1 - e) - 1.84 < y)
    (hu : y < x * (1 + e) + rsTrivialKernel x) :
    x * (1 - E) < y ∧ y < x * (1 + E) := by
  have ha2 : 2 ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  have hx2 := ha2.trans hx
  have hpos : 0 < E - e := by linarith [Real.exp_pos (-b)]
  have hg := mul_le_mul_of_nonneg_right hgap (Real.exp_pos b).le
  have hid : Real.exp (-b) * Real.exp b = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscale : 2 ≤ x * (E - e) := by
    have hmul := mul_le_mul_of_nonneg_right hx hpos.le
    nlinarith
  have hk := trivial_kernel_le_one hx2
  constructor <;> nlinarith

theorem row_psi_of_actual_moment {r : Row} (h : r.Valid) {x : ℝ}
    (hx : Real.exp (r.b : ℝ) ≤ x)
    (hmoment : (∑' p, rsZeroMoment r.m (r.b : ℝ) p) ≤
      ((r.d : ℝ) / 2) ^ (r.m + 1)) :
    x * (1 - (r.e : ℝ)) < Chebyshev.psi x ∧
      Chebyshev.psi x < x * (1 + (r.e : ℝ)) := by
  have hcut := row_cut h
  have hmom : (∑' p, rsZeroMoment r.m (Real.log (Real.exp (r.b : ℝ))) p) ≤
      ((r.d : ℝ) / 2) ^ (r.m + 1) := by simpa only [Real.log_exp] using hmoment
  have hh := rsPsi_delta_epsilon_of_actual_moment h.2.1
    (Rat.cast_pos.mpr h.2.2.1) hcut.1 hcut.2 hx hmom
  apply absorb_remainders (by exact_mod_cast h.1) hx (row_epsilon_gap h) hh.1
  simpa only [rsTrivialKernel, sub_eq_add_neg, neg_mul] using hh.2

theorem constant_error_on_log_interval {b c E C x : ℝ}
    (hb : 0 < b) (hE : 0 ≤ E) (hpay : E * c ≤ C)
    (hx : Real.exp b ≤ x) (hxc : x ≤ Real.exp c) :
    E ≤ C / Real.log x := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hl : b ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hu : Real.log x ≤ c := (Real.log_le_iff_le_exp hx0).mpr hxc
  apply (le_div_iff₀ (hb.trans_le hl)).mpr
  exact (mul_le_mul_of_nonneg_left hu hE).trans hpay

#print axioms exp_certificate_sound
#print axioms row_budget
#print axioms row_cut
#print axioms row_epsilon_gap
#print axioms row_root
#print axioms row_psi_of_actual_moment
#print axioms constant_error_on_log_interval

end
end LiuWang.Proof.Campaign20260915.RSTableCertificates
