import LiuWang.Target
import Mathlib.Tactic.NormNum

/-!
# Kernel-checkable certificates for three odd primes

Certificates contain data, not assumed proofs. The interval checker consumes one
certificate for each successive odd integer, rejecting gaps, duplicates, excess
rows and premature termination. The lower endpoint must be odd; the upper
endpoint is inclusive and may be even. Repetition of primes is permitted.
-/

set_option autoImplicit false

namespace LiuWang.Proof.FiniteTernaryClosure

structure Certificate where
  n : ℕ
  p : ℕ
  q : ℕ
  r : ℕ
  deriving DecidableEq, Repr

def checkCertificate (c : Certificate) : Bool :=
  decide (c.p.Prime ∧ c.q.Prime ∧ c.r.Prime ∧
    c.p % 2 = 1 ∧ c.q % 2 = 1 ∧ c.r % 2 = 1 ∧ c.n = c.p + c.q + c.r)

theorem checkCertificate_sound {c : Certificate} (h : checkCertificate c = true) :
    LiuWang.IsThreeOddPrimeSum c.n := by
  exact ⟨c.p, c.q, c.r, by simpa only [Nat.odd_iff] using of_decide_eq_true h⟩

def checkOddRun (lo hi : ℕ) : List Certificate → Bool
  | [] => decide (hi < lo)
  | c :: cs =>
      decide (lo ≤ hi ∧ c.n = lo) && checkCertificate c && checkOddRun (lo + 2) hi cs

def checkInterval (lo hi : ℕ) (cs : List Certificate) : Bool :=
  decide (lo % 2 = 1) && checkOddRun lo hi cs

theorem checkInterval_of_checkOddRun {lo hi : ℕ} {cs : List Certificate}
    (hlo : lo % 2 = 1) (h : checkOddRun lo hi cs = true) :
    checkInterval lo hi cs = true := by
  simp only [checkInterval, hlo, decide_true, Bool.true_and, h]

/-- Join adjacent, fully checked runs without recomputing primality proofs. -/
theorem checkOddRun_append {lo mid hi : ℕ} {left right : List Certificate}
    (hmid : mid ≤ hi + 1) (hlen : lo + 2 * left.length = mid)
    (hl : checkOddRun lo (mid - 1) left = true)
    (hr : checkOddRun mid hi right = true) :
    checkOddRun lo hi (left ++ right) = true := by
  induction left generalizing lo with
  | nil =>
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hlen
      simpa only [List.nil_append, hlen] using hr
  | cons c cs ih =>
      simp only [checkOddRun, Bool.and_eq_true, decide_eq_true_eq] at hl
      simp only [List.length_cons] at hlen
      simp only [List.cons_append, checkOddRun, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨by omega, hl.1.1.2⟩, hl.1.2⟩, ih (by omega) hl.2⟩

theorem checkOddRun_sound {cs : List Certificate} {lo hi : ℕ}
    (h : checkOddRun lo hi cs = true) (hlo : Odd lo) :
    ∀ n : ℕ, lo ≤ n → n ≤ hi → Odd n → LiuWang.IsThreeOddPrimeSum n := by
  induction cs generalizing lo with
  | nil =>
      have hend : hi < lo := of_decide_eq_true h
      intro n hn hn' _
      omega
  | cons c cs ih =>
      simp only [checkOddRun, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨_, hindex⟩, hc⟩, htail⟩ := h
      intro n hn hn' hodd
      by_cases heq : n = lo
      · simpa only [hindex, heq] using checkCertificate_sound hc
      · have hnext : Odd (lo + 2) := by
          obtain ⟨a, ha⟩ := hlo
          exact ⟨a + 1, by omega⟩
        apply ih htail hnext n _ hn' hodd
        obtain ⟨a, ha⟩ := hlo
        obtain ⟨b, hb⟩ := hodd
        omega

theorem checkInterval_sound {lo hi : ℕ} {cs : List Certificate}
    (h : checkInterval lo hi cs = true) :
    ∀ n : ℕ, lo ≤ n → n ≤ hi → Odd n → LiuWang.IsThreeOddPrimeSum n := by
  simp only [checkInterval, Bool.and_eq_true, decide_eq_true_eq] at h
  exact checkOddRun_sound h.2 (Nat.odd_iff.mpr h.1)

/-- An accepted nonempty run has exactly the advertised consecutive indices. -/
theorem checkOddRun_indices {cs : List Certificate} {lo hi : ℕ}
    (h : checkOddRun lo hi cs = true) :
    cs.map Certificate.n = (List.range cs.length).map (fun k => lo + 2 * k) := by
  induction cs generalizing lo with
  | nil => rfl
  | cons c cs ih =>
      simp only [checkOddRun, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨_, hindex⟩, _⟩, htail⟩ := h
      simp only [List.map_cons, List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.map_map, Function.comp_def, Nat.mul_zero, Nat.add_zero, hindex, ih htail]
      congr 1
      apply List.map_congr_left
      intro k _
      omega

theorem nine_le_of_isThreeOddPrimeSum {n : ℕ} (h : LiuWang.IsThreeOddPrimeSum n) :
    9 ≤ n := by
  obtain ⟨p, q, r, hp, hq, hr, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, heq⟩ := h
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  omega

theorem not_isThreeOddPrimeSum_of_lt_nine {n : ℕ} (hn : n < 9) :
    ¬LiuWang.IsThreeOddPrimeSum n := by
  intro h
  have := nine_le_of_isThreeOddPrimeSum h
  omega

end LiuWang.Proof.FiniteTernaryClosure
