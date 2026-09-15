import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.GramPoints
import LiuWang.Proof.Campaign20260915.ZetaGramBlocks.SignAreas

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory

namespace LiuWang.Proof.Campaign20260915.ZetaGramBlocks

open LiuWang.Proof.Campaign20260915.ZetaValidation
open LiuWang.Proof.Campaign20260915.ZetaWinding

structure IsGramBlock (g : ℤ → ℝ) (n p : ℤ) : Prop where
  indices : n < p
  positive : 0 < g n
  ordered : StrictMonoOn g (Set.Icc n p)
  phase : ∀ j ∈ Set.Icc n p, IsGramPoint j (g j)
  good_left : IsGoodGramPoint n (g n)
  good_right : IsGoodGramPoint p (g p)
  bad_inside : ∀ j ∈ Set.Ioo n p, ¬ IsGoodGramPoint j (g j)

def RosserRule (g : ℤ → ℝ) (n p : ℤ) : Prop :=
  (p - n).toNat ≤ criticalBlockCount (g n) (g p)

structure GramSignCertificate (g : ℤ → ℝ) (n p : ℤ) where
  left : Fin (p - n).toNat → ℝ
  right : Fin (p - n).toNat → ℝ
  lower : ∀ i, g n ≤ left i
  upper : ∀ i, right i ≤ g p
  width : ∀ i, left i < right i
  separated : ∀ i j, i < j → right i ≤ left j
  signs : ∀ i, criticalCompletedZeta (left i) * criticalCompletedZeta (right i) < 0

theorem IsGramBlock.height_lt {g : ℤ → ℝ} {n p : ℤ} (B : IsGramBlock g n p) :
    g n < g p :=
  B.ordered ⟨le_rfl, B.indices.le⟩ ⟨B.indices.le, le_rfl⟩ B.indices

theorem rosserRule_of_signs {g : ℤ → ℝ} {n p : ℤ} (B : IsGramBlock g n p)
    (C : GramSignCertificate g n p) : RosserRule g n p :=
  (sign_windows_count_and_areas B.positive.le B.height_lt C.left C.right
    C.lower C.upper C.width C.separated C.signs).1

theorem rosser_count_increment {g : ℤ → ℝ} {n p : ℤ} (B : IsGramBlock g n p)
    (hR : RosserRule g n p) :
    (positiveCount (g n) : ℤ) + (p - n) ≤ positiveCountLeft (g p) := by
  have h := criticalBlockCount_add_le_strictCount B.height_lt
    (goodGram_critical_ne_zero B.good_left)
  have hc : positiveCount (g n) + (p - n).toNat ≤ positiveCountLeft (g p) :=
    (Nat.add_le_add_left hR _).trans h
  have hn : 0 ≤ p - n := sub_nonneg.mpr B.indices.le
  have hci : (positiveCount (g n) : ℤ) + ((p - n).toNat : ℤ) ≤
      (positiveCountLeft (g p) : ℤ) := by exact_mod_cast hc
  simpa only [Int.toNat_of_nonneg hn] using hci

theorem rosser_turing_increment {g : ℤ → ℝ} {n p : ℤ} (B : IsGramBlock g n p)
    (hR : RosserRule g n p) : turingS (g n) ≤ turingSLeft (g p) := by
  have hc := rosser_count_increment B hR
  have hr : (positiveCount (g n) : ℝ) + ((p : ℝ) - n) ≤ positiveCountLeft (g p) := by
    exact_mod_cast hc
  rw [turingS_at_gram B.good_left.1, turingSLeft_at_gram B.good_right.1]
  linarith

theorem turingSLeft_le_turingS (t : ℝ) : turingSLeft t ≤ turingS t := by
  have h := turingS_jump t
  linarith [Nat.cast_nonneg (α := ℝ) (boundaryMultiplicity t)]

theorem consecutive_rosser_turing_closed {g : ℤ → ℝ} (v : ℕ → ℤ) (K : ℕ)
    (hB : ∀ j < K, IsGramBlock g (v j) (v (j + 1)))
    (hR : ∀ j < K, RosserRule g (v j) (v (j + 1))) :
    turingS (g (v 0)) ≤ turingS (g (v K)) := by
  induction K with
  | zero => exact le_rfl
  | succ K ih =>
    have hp := ih (fun j hj => hB j (by omega)) (fun j hj => hR j (by omega))
    exact hp.trans ((rosser_turing_increment (hB K (by omega)) (hR K (by omega))).trans
      (turingSLeft_le_turingS _))

theorem consecutive_rosser_turing_strict {g : ℤ → ℝ} (v : ℕ → ℤ) {K : ℕ}
    (hK : 0 < K) (hB : ∀ j < K, IsGramBlock g (v j) (v (j + 1)))
    (hR : ∀ j < K, RosserRule g (v j) (v (j + 1))) :
    turingS (g (v 0)) ≤ turingSLeft (g (v K)) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hK)
  exact (consecutive_rosser_turing_closed v L
    (fun j hj => hB j (by omega)) (fun j hj => hR j (by omega))).trans
      (rosser_turing_increment (hB L (by omega)) (hR L (by omega)))

theorem consecutive_signed_blocks_turing {g : ℤ → ℝ} (v : ℕ → ℤ) {K : ℕ}
    (hK : 0 < K) (hB : ∀ j < K, IsGramBlock g (v j) (v (j + 1)))
    (C : ∀ j < K, GramSignCertificate g (v j) (v (j + 1))) :
    turingS (g (v 0)) ≤ turingSLeft (g (v K)) :=
  consecutive_rosser_turing_strict v hK hB (fun j hj => rosserRule_of_signs (hB j hj) (C j hj))

theorem consecutive_block_span {g : ℤ → ℝ} (v : ℕ → ℤ) (K : ℕ)
    (hB : ∀ j < K, IsGramBlock g (v j) (v (j + 1))) :
    (K : ℤ) ≤ v K - v 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hp := ih (fun j hj => hB j (by omega))
    have hs := (hB K (by omega)).indices
    omega

theorem signed_block_turing_areas {g : ℤ → ℝ} {n p : ℤ} (B : IsGramBlock g n p)
    (C : GramSignCertificate g n p) :
    ((positiveCount (g n) : ℝ) - 1) * (g p - g n) + (∑ i, (g p - C.right i)) -
      (∫ t in g n..g p, criticalGammaArgument t) / Real.pi ≤
        (∫ t in g n..g p, turingS t) ∧
    (∫ t in g n..g p, turingS t) ≤
      ((positiveCountLeft (g p) : ℝ) - 1) * (g p - g n) -
        (∑ i, (C.left i - g n)) -
          (∫ t in g n..g p, criticalGammaArgument t) / Real.pi :=
  sign_windows_turing_areas B.positive.le B.height_lt C.left C.right
    C.lower C.upper C.width C.separated C.signs

#print axioms rosserRule_of_signs
#print axioms rosser_count_increment
#print axioms consecutive_signed_blocks_turing
#print axioms consecutive_block_span
#print axioms signed_block_turing_areas

end LiuWang.Proof.Campaign20260915.ZetaGramBlocks
