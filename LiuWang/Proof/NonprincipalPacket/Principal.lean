import LiuWang.Proof.NonprincipalPacket.Energy
import LiuWang.Proof.SingularSeries.Ramanujan

/-!
# 实际主字符 Gauss 系数

原正相位系数是负相位 Ramanujan 和的共轭。
整数式与互素性识别为 Moebius，不使用主字符 psi 公式。
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical ArithmeticFunction
open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.Interfaces LiuWang.Proof.CharacterExpansion
open LiuWang.Proof.SingularSeries

namespace LiuWang.Proof.NonprincipalPacket

theorem G_one_eq_conj_ramanujan {q : ℕ} [NeZero q] (a : ℕ) :
    G a (1 : Character q) = star (ramanujan a q) := by
  rw [ramanujan_eq_zmod, star_sum]
  simp only [G, gaussSum, inv_one, AddChar.mulShift_apply]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : IsUnit x
  · rw [MulChar.one_apply hx, one_mul, if_pos hx]
    change _ = (starRingEnd ℂ) _
    rw [← AddChar.map_neg_eq_conj]
    congr 1
    ring
  · rw [MulChar.map_nonunit _ hx, zero_mul, if_neg hx, star_zero]

theorem ramanujan_eq_moebius_of_coprime {a q : ℕ} [NeZero q]
    (haq : Nat.Coprime a q) : ramanujan a q = (moebius q : ℂ) := by
  rw [ramanujan_integer_formula]
  rw [Finset.sum_eq_single q]
  · simp [Nat.div_self (NeZero.pos q)]
  · intro d hd hdq
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hn : ¬ q / d ∣ a := by
      intro h
      have he : q / d = 1 :=
        Nat.eq_one_of_dvd_coprimes haq h (Nat.div_dvd_of_dvd hdvd)
      have hm := Nat.mul_div_cancel' hdvd
      rw [he, mul_one] at hm
      exact hdq hm
    simp [hn]
  · intro h
    exact (h (Nat.mem_divisors.mpr ⟨dvd_refl q, NeZero.ne q⟩)).elim

theorem G_one_eq_moebius {a q : ℕ} [NeZero q] (haq : Nat.Coprime a q) :
    G a (1 : Character q) = (moebius q : ℂ) := by
  rw [G_one_eq_conj_ramanujan, ramanujan_eq_moebius_of_coprime haq]
  simp

theorem G_one_source {a q : ℕ} [NeZero q] (hi : sourceIndex a q) :
    G a (1 : Character q) = (moebius q : ℂ) :=
  G_one_eq_moebius hi.2.2

theorem S_sub_principal_mode {q : ℕ} [NeZero q] (N a : ℕ) (η : ℝ)
    (haq : Nat.Coprime a q) :
    S N (rationalCenter a q + η) -
        ((moebius q : ℂ) / (q.totient : ℂ)) * twistedS N η (1 : Character q) =
      (q.totient : ℂ)⁻¹ *
        (∑ chi ∈ (Finset.univ : Finset (Character q)).erase 1,
          G a chi * twistedS N η chi) +
        nonCoprimeError N q (rationalCenter a q + η) := by
  rw [S_character_expansion]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Character q)),
    G_one_eq_moebius haq]
  ring

@[simp] theorem G_one_modulus_one (a : ℕ) :
    G a (1 : Character 1) = 1 := by
  simpa using G_one_eq_moebius (Nat.coprime_one_right a)

theorem S_modulus_one (N a : ℕ) (η : ℝ) :
    S N (rationalCenter a 1 + η) = twistedS N η (1 : Character 1) := by
  rw [S_character_expansion]
  simp [Subsingleton.elim (default : Character 1) 1]

end LiuWang.Proof.NonprincipalPacket
