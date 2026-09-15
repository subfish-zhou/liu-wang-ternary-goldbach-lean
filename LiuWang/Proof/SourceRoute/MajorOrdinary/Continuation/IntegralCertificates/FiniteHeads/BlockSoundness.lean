import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads.ArithmeticSoundness

set_option autoImplicit false
noncomputable section

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads

def HeadBound (a b A B : ℕ) : Prop :=
  a ≤ b ∧
    (∑ q ∈ Finset.Ico a b, totientWeight q (1 / 6)) ≤ (A : ℝ) / denominator ∧
    (∑ q ∈ Finset.Ico a b, totientWeight q (7 / 6)) ≤ (B : ℝ) / denominator

theorem HeadBound.join {a b c A B C D : ℕ}
    (hl : HeadBound a b A B) (hr : HeadBound b c C D) :
    HeadBound a c (A + C) (B + D) := by
  refine ⟨hl.1.trans hr.1, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive _ hl.1 hr.1, Nat.cast_add, add_div]
    exact add_le_add hl.2.1 hr.2.1
  · rw [← Finset.sum_Ico_consecutive _ hl.1 hr.1, Nat.cast_add, add_div]
    exact add_le_add hl.2.2 hr.2.2

theorem Row.headBound {r : Row} (hr : r.valid = true) :
    HeadBound r.q (r.q + 1) r.upper1 r.upper7 := by
  obtain ⟨_, _, _, h1, h7⟩ := r.sound hr
  exact ⟨by omega, by simpa using h1, by simpa using h7⟩

inductive Block where
  | leaf (r : Row)
  | branch (left right : Block)

namespace Block

def first : Block → ℕ
  | .leaf r => r.q
  | .branch l _ => l.first

def stop : Block → ℕ
  | .leaf r => r.q + 1
  | .branch _ r => r.stop

def upper1 : Block → ℕ
  | .leaf r => r.upper1
  | .branch l r => l.upper1 + r.upper1

def upper7 : Block → ℕ
  | .leaf r => r.upper7
  | .branch l r => l.upper7 + r.upper7

def valid : Block → Bool
  | .leaf r => r.valid
  | .branch l r => l.valid && r.valid && (l.stop == r.first)

theorem sound {b : Block} (hb : b.valid = true) :
    HeadBound b.first b.stop b.upper1 b.upper7 := by
  induction b with
  | leaf r => exact r.headBound hb
  | branch l r hl hr =>
    simp only [valid, Bool.and_eq_true, beq_iff_eq] at hb
    have hleft := hl hb.1.1
    have hright := hr hb.1.2
    rw [← hb.2] at hright
    exact hleft.join hright

def verifies (b : Block) (a z A B : ℕ) : Bool :=
  b.valid && (b.first == a) && (b.stop == z) && (b.upper1 == A) && (b.upper7 == B)

theorem verifies_sound {b : Block} {a z A B : ℕ} (hb : b.verifies a z A B = true) :
    HeadBound a z A B := by
  simp only [verifies, Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨⟨⟨⟨hv, ha⟩, hz⟩, hA⟩, hB⟩ := hb
  simpa only [ha, hz, hA, hB] using sound hv

end Block

theorem heads_of_whole_bound {A B : ℕ} (h : HeadBound 1 100001 A B)
    (hA : A * 5000 ≤ 16421 * denominator) (hB : B * 5000 ≤ 349901 * denominator) :
    totientMoment 100000 (1 / 6) ≤ 3.2842 ∧ totientMoment 100000 (7 / 6) ≤ 69.9802 := by
  have he : LiuWang.Proof.SingularSeries.denominators 100000 = Finset.Ico 1 100001 := by
    unfold LiuWang.Proof.SingularSeries.denominators
    norm_num only [Nat.floor_natCast]
    rfl
  have hd : (0 : ℝ) < denominator := by norm_num [denominator]
  unfold totientMoment
  rw [he]
  constructor
  · apply h.2.1.trans
    apply (div_le_iff₀ hd).mpr
    have hA' : (A : ℝ) * 5000 ≤ 16421 * denominator := by exact_mod_cast hA
    linarith only [hA']
  · apply h.2.2.trans
    apply (div_le_iff₀ hd).mpr
    have hB' : (B : ℝ) * 5000 ≤ 349901 * denominator := by exact_mod_cast hB
    linarith only [hB']

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.FiniteHeads
