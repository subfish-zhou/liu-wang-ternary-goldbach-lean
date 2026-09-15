import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.Consumers
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads

inductive FactorCertificate where
  | one
  | step (p k : ℕ) (tail : FactorCertificate)

namespace FactorCertificate

def number : FactorCertificate → ℕ
  | .one => 1
  | .step p k tail => p ^ k * tail.number

def phi : FactorCertificate → ℕ
  | .one => 1
  | .step p k tail => p ^ (k - 1) * (p - 1) * tail.phi

def mu : FactorCertificate → ℤ
  | .one => 1
  | .step _ k tail => (if k = 1 then -1 else 0) * tail.mu

def valid : FactorCertificate → Bool
  | .one => true
  | .step p k tail =>
      decide (2 ≤ p) && (Nat.minFac p == p) && decide (0 < k) &&
        (Nat.gcd p tail.number == 1) && tail.valid

theorem sound {f : FactorCertificate} (hf : f.valid = true) :
    0 < f.number ∧ f.number.totient = f.phi ∧ ArithmeticFunction.moebius f.number = f.mu := by
  induction f with
  | one => simp [number, phi, mu]
  | step p k tail ih =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
    obtain ⟨⟨⟨⟨hp2, hpmin⟩, hk⟩, hcop⟩, htail⟩ := hf
    have hp : p.Prime := Nat.prime_def_minFac.mpr ⟨hp2, hpmin⟩
    have hc : Nat.Coprime (p ^ k) tail.number :=
      (show Nat.Coprime p tail.number from hcop).pow_left k
    obtain ⟨hn, hphi, hmu⟩ := ih htail
    refine ⟨mul_pos (pow_pos hp.pos k) hn, ?_, ?_⟩
    · simp only [number, phi, Nat.totient_mul hc, Nat.totient_prime_pow hp hk, hphi]
    · simp only [number, mu, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
        ArithmeticFunction.moebius_apply_prime_pow hp hk.ne', hmu]

end FactorCertificate

def denominator : ℕ := 1000000000000

structure Row where
  q : ℕ
  phi : ℕ
  mu : ℤ
  factors : FactorCertificate
  root : ℕ
  upper1 : ℕ
  upper7 : ℕ

def Row.valid (r : Row) : Bool :=
  r.factors.valid && (r.factors.number == r.q) && (r.factors.phi == r.phi) &&
    (r.factors.mu == r.mu) &&
    (if r.mu = 0 then (r.upper1 == 0) && (r.upper7 == 0) else
      decide (r.mu = 1 ∨ r.mu = -1) && decide (r.q * denominator ^ 6 ≤ r.root ^ 6) &&
        decide (r.root ≤ r.upper1 * r.phi ^ 2) &&
        decide (r.q * r.root ≤ r.upper7 * r.phi ^ 2))

theorem sixth_root_bound {q D R : ℕ} (hD : 0 < D) (hR : q * D ^ 6 ≤ R ^ 6) :
    (q : ℝ) ^ (1 / 6 : ℝ) ≤ (R : ℝ) / D := by
  have hd : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have he : ((q : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
    norm_num
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg q) _) (by positivity)
    (by decide : 6 ≠ 0)).mp
  rw [he, div_pow, le_div_iff₀ (pow_pos hd 6)]
  exact_mod_cast hR

theorem weight_bounds {q ph R A B : ℕ} {m : ℤ} (hq : 0 < q)
    (hphi : q.totient = ph) (hmu : ArithmeticFunction.moebius q = m)
    (hm : m = 1 ∨ m = -1) (hR : q * denominator ^ 6 ≤ R ^ 6)
    (hA : R ≤ A * ph ^ 2) (hB : q * R ≤ B * ph ^ 2) :
    totientWeight q (1 / 6) ≤ (A : ℝ) / denominator ∧
      totientWeight q (7 / 6) ≤ (B : ℝ) / denominator := by
  have hph : (0 : ℝ) < ph := Nat.cast_pos.mpr (hphi ▸ Nat.totient_pos.mpr hq)
  have hd : (0 : ℝ) < denominator := by norm_num [denominator]
  have hroot := sixth_root_bound (by norm_num [denominator] : 0 < denominator) hR
  have hmabs : |(ArithmeticFunction.moebius q : ℝ)| = 1 := by
    rcases hm with hm | hm <;> rw [hmu, hm] <;> norm_num
  have h1 : totientWeight q (1 / 6) ≤ (R : ℝ) / denominator / ph ^ 2 := by
    unfold totientWeight
    rw [hmabs, one_mul, hphi]
    exact div_le_div_of_nonneg_right hroot (sq_nonneg _)
  have hA' : (R : ℝ) ≤ A * (ph : ℝ) ^ 2 := by exact_mod_cast hA
  have hB' : (q : ℝ) * R ≤ B * (ph : ℝ) ^ 2 := by exact_mod_cast hB
  constructor
  · apply h1.trans
    apply (div_le_iff₀ (sq_pos_of_pos hph)).mpr
    apply (div_le_iff₀ hd).mpr
    convert! hA' using 1
    field_simp
  · rw [totientWeight_seven_sixths hq]
    apply (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg q)).trans
    apply (le_div_iff₀ hd).mpr
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hph)).mp
    convert! hB' using 1
    field_simp
    ring

theorem Row.sound {r : Row} (hr : r.valid = true) :
    0 < r.q ∧ r.q.totient = r.phi ∧ ArithmeticFunction.moebius r.q = r.mu ∧
      totientWeight r.q (1 / 6) ≤ (r.upper1 : ℝ) / denominator ∧
      totientWeight r.q (7 / 6) ≤ (r.upper7 : ℝ) / denominator := by
  simp only [Row.valid, Bool.and_eq_true, beq_iff_eq] at hr
  obtain ⟨⟨⟨⟨hf, hn⟩, hphi⟩, hmu⟩, hc⟩ := hr
  obtain ⟨hq, hp, hm⟩ := FactorCertificate.sound hf
  rw [hn] at hq hp hm
  rw [hphi] at hp
  rw [hmu] at hm
  refine ⟨hq, hp, hm, ?_⟩
  split_ifs at hc with hz
  · simp only [Bool.and_eq_true, beq_iff_eq] at hc
    simp only [totientWeight, hm, hz, Int.cast_zero, abs_zero, zero_mul, zero_div,
      hc.1, hc.2, Nat.cast_zero, le_refl, and_self]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact weight_bounds hq hp hm hc.1.1.1 hc.1.1.2 hc.1.2 hc.2

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads
