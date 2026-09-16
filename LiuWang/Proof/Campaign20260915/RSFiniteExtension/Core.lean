import LiuWang.Proof.Campaign20260915.Totient.ProductFinite
import LiuWang.Proof.Campaign20260915.Totient.ThetaTable

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LiuWang.Proof.Campaign20260915.RSFiniteExtension

open Totient

def PrimeGap (a b : ℕ) : Prop :=
  ∀ p ∈ Finset.Ioo a b, ¬ p.Prime

instance (a b : ℕ) : Decidable (PrimeGap a b) :=
  inferInstanceAs (Decidable (∀ p ∈ Finset.Ioo a b, ¬ p.Prime))

def lowerEnvelope (u : ℤ) : ℚ :=
  (178107239 / 100000000) *
    ((u : ℚ) / 10000000000 + 10000000000 / (2 * (u + 76)))

noncomputable section

def State (a : ℕ) (T : ℤ) (U : ℕ) : Prop :=
  (T : ℝ) / 10000000000 ≤ Chebyshev.theta a ∧
    (prefixEuler a : ℝ) ≤ (U : ℝ) / 10000000000

def Reach (a : ℕ) (T : ℤ) (U : ℕ) : Prop :=
  State a T U ∧
    (∀ x : ℝ, 1420 ≤ x → x ≤ a →
      (prefixEuler ⌊x⌋₊ : ℝ) < productEnvelope x) ∧
    (∀ x : ℝ, 1423 ≤ x → x ≤ a →
      x - 2 * Real.sqrt x < Chebyshev.theta x)

theorem log_bounds {p : ℕ} {u : ℤ} (hp : p.Prime)
    (hs : logScale (p : ℚ) ≤ 13)
    (hu : u = ⌊logCenter (p : ℚ) * 10000000000⌋) :
    (u : ℝ) / 10000000000 ≤ Real.log p ∧
      Real.log p ≤ (u + 76 : ℝ) / 10000000000 := by
  have h := rational_log_bounds (x := (p : ℚ)) (by exact_mod_cast hp.one_lt.le)
  unfold logHi logLo at h
  rw [← hu] at h
  push_cast at h
  have hsR : (logScale (p : ℚ) : ℝ) ≤ 13 := by exact_mod_cast hs
  exact ⟨h.1, by linarith [h.2]⟩

theorem lowerEnvelope_le {x : ℝ} {u : ℤ} (hu : 0 < u)
    (hl : (u : ℝ) / 10000000000 ≤ Real.log x)
    (hh : Real.log x ≤ (u + 76 : ℝ) / 10000000000) :
    (lowerEnvelope u : ℝ) ≤ productEnvelope x := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hlog : 0 < Real.log x := lt_of_lt_of_le (by positivity) hl
  have hrec := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
    (show 0 < 2 * Real.log x by positivity)
    (show 2 * Real.log x ≤ 2 * ((u + 76 : ℝ) / 10000000000) by linarith)
  have hg :=
    LiuWang.Proof.SourceRoute.MajorException.Continuation.CriticalCertificate.gammaFactor_interval.1
  change (1.78107239 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant at hg
  unfold lowerEnvelope productEnvelope
  push_cast
  have hm := mul_le_mul hg (add_le_add hl hrec) (by positivity)
    (Real.exp_pos Real.eulerMascheroniConstant).le
  calc
    _ = (1.78107239 : ℝ) *
        ((u : ℝ) / 10000000000 + 1 / (2 * ((u + 76 : ℝ) / 10000000000))) := by
      field_simp
      ring
    _ ≤ _ := hm

theorem primesLE_gap {a b n : ℕ} (hg : PrimeGap a b)
    (ha : a ≤ n) (hb : n < b) : Nat.primesLE n = Nat.primesLE a := by
  ext p
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨hpn, hp⟩
    refine ⟨?_, hp⟩
    by_contra! hpa
    exact hg p (Finset.mem_Ioo.mpr ⟨hpa, hpn.trans_lt hb⟩) hp
  · rintro ⟨hpa, hp⟩
    exact ⟨hpa.trans ha, hp⟩

theorem primesLE_next {a p : ℕ} (ha : a < p) (hp : p.Prime)
    (hg : PrimeGap a p) : Nat.primesLE p = insert p (Nat.primesLE a) := by
  have h := primesLE_gap hg (n := p - 1) (by omega) (by omega)
  have he : p = (p - 1) + 1 := by omega
  conv_lhs => rw [he, Nat.primesLE_succ]
  rw [← he, if_pos hp, h]

theorem state_next {a p U V : ℕ} {T u : ℤ} (ha : a < p)
    (hp : p.Prime) (hg : PrimeGap a p)
    (hl : (u : ℝ) / 10000000000 ≤ Real.log p)
    (hV : U * p / (p - 1) + 1 = V) (h : State a T U) :
    State p (T + u) V := by
  have he := primesLE_next ha hp hg
  have hnot : p ∉ Nat.primesLE a := by simp [Nat.mem_primesLE, ha.not_ge]
  have ht : Chebyshev.theta p = Chebyshev.theta a + Real.log p := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, he, Finset.sum_insert hnot,
      Chebyshev.theta_eq_sum_primesLE_log]
    ring
  have hprod : prefixEuler p = prefixEuler a * (p : ℚ) / (p - 1) := by
    unfold prefixEuler
    rw [he, Finset.prod_insert hnot]
    ring
  refine ⟨?_, ?_⟩
  · rw [ht, Int.cast_add, add_div]
    exact add_le_add h.1 hl
  · have hd : 0 < p - 1 := by have := hp.two_le; omega
    have hround : U * p < V * (p - 1) := by
      rw [← hV]
      exact (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
    have hroundR : (U : ℝ) * p < (V : ℝ) * (p - 1 : ℕ) := by
      exact_mod_cast hround
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hdR : (0 : ℝ) < p - 1 := by linarith
    have hcast : ((p - 1 : ℕ) : ℝ) = p - 1 :=
      by simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ p from hp.one_lt.le))
    rw [hcast] at hroundR
    rw [hprod]
    push_cast
    calc
      (prefixEuler a : ℝ) * p / (p - 1) =
          (prefixEuler a : ℝ) * ((p : ℝ) / (p - 1)) := by ring
      _ ≤ ((U : ℝ) / 10000000000) * ((p : ℝ) / (p - 1)) :=
        mul_le_mul_of_nonneg_right h.2 (by positivity)
      _ ≤ (V : ℝ) / 10000000000 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hdR).mpr
        nlinarith

theorem theta_endpoint {b x : ℝ} {T : ℤ} (hx : 1 ≤ x) (hb : x ≤ b)
    (hnum : (b * 10000000000 - T) ^ 2 < 4 * b * 10000000000 ^ 2)
    (ht : (T : ℝ) / 10000000000 ≤ Chebyshev.theta x) :
    x - 2 * Real.sqrt x < Chebyshev.theta x := by
  let t : ℝ := (T : ℝ) / 10000000000
  have htr : (b - t) ^ 2 < 4 * b := by dsimp [t]; nlinarith
  have hsx := Real.sq_sqrt (show 0 ≤ x by linarith)
  have hsb := Real.sq_sqrt (show 0 ≤ b by linarith)
  have hsm := Real.sqrt_le_sqrt hb
  have hsl : 1 ≤ Real.sqrt x := by
    simpa using Real.sqrt_le_sqrt hx
  have hmain : b - 2 * Real.sqrt b < t := by
    nlinarith [sq_nonneg (b - t + 2 * Real.sqrt b)]
  have hmono : x - 2 * Real.sqrt x ≤ b - 2 * Real.sqrt b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsm)
      (show 0 ≤ Real.sqrt x + Real.sqrt b - 2 by linarith)]
  exact (hmono.trans_lt hmain).trans_le ht

theorem product_between {a b : ℕ} {x : ℝ} (ha : 3 ≤ a)
    (hg : PrimeGap a b) (hx : (a : ℝ) ≤ x) (hb : x < b)
    (hprod : (prefixEuler a : ℝ) < productEnvelope a) :
    (prefixEuler ⌊x⌋₊ : ℝ) < productEnvelope x := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg a).trans hx
  have haR : (3 : ℝ) ≤ a := by exact_mod_cast ha
  have hn : a ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr hx
  have hi : ⌊x⌋₊ < b := by
    have := (Nat.floor_le hx0).trans_lt hb
    exact_mod_cast this
  have he : prefixEuler ⌊x⌋₊ = prefixEuler a := by
    unfold prefixEuler
    rw [primesLE_gap hg hn hi]
  rw [he]
  exact hprod.trans_le (productEnvelope_monotone
    haR (haR.trans hx) hx)

theorem reach_next {a p U V : ℕ} {T u : ℤ} (ha : 1420 ≤ a) (hap : a < p)
    (hp : p.Prime) (hg : PrimeGap a p)
    (hu : 0 < u) (hl : (u : ℝ) / 10000000000 ≤ Real.log p)
    (hh : Real.log p ≤ (u + 76 : ℝ) / 10000000000)
    (hV : U * p / (p - 1) + 1 = V)
    (hprod : (V : ℚ) / 10000000000 < lowerEnvelope u)
    (htheta : ((p : ℤ) * 10000000000 - T) ^ 2 <
      4 * p * 10000000000 ^ 2) (h : Reach a T U) :
    Reach p (T + u) V := by
  have hs := state_next hap hp hg hl hV h.1
  have hpr : (prefixEuler p : ℝ) < productEnvelope p := by
    have hnum := Rat.cast_lt (K := ℝ) |>.mpr hprod
    push_cast at hnum
    exact hs.2.trans_lt (hnum.trans_le (lowerEnvelope_le hu hl hh))
  refine ⟨hs, ?_, ?_⟩
  · intro x hx hxp
    by_cases hxa : x ≤ a
    · exact h.2.1 x hx hxa
    by_cases he : x = p
    · subst x
      simpa using hpr
    exact product_between (by omega) hg (le_of_not_ge hxa) (lt_of_le_of_ne hxp he)
      (by simpa using h.2.1 a (by exact_mod_cast ha) le_rfl)
  · intro x hx hxp
    by_cases hxa : x ≤ a
    · exact h.2.2 x hx hxa
    apply theta_endpoint (b := (p : ℝ)) (by linarith) hxp
    · exact_mod_cast htheta
    · exact h.1.1.trans (Chebyshev.theta_mono (by linarith))

end
end LiuWang.Proof.Campaign20260915.RSFiniteExtension
