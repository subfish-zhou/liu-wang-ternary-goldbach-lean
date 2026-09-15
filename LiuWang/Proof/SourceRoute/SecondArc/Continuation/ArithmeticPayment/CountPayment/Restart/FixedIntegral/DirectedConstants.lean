import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral.Partition

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral

theorem sourceNu_upper_of_intervals {x E ellLo ellHi : ℝ}
    (hE : Real.exp Real.eulerMascheroniConstant ≤ E)
    (hlo : 0 < ellLo) (hlo' : ellLo ≤ Real.log (Real.log x))
    (hhi : Real.log (Real.log x) ≤ ellHi) :
    sourceNu x ≤ E * ellHi + 2.50637 / ellLo := by
  have hell : 0 ≤ Real.log (Real.log x) := (hlo.trans_le hlo').le
  have hEp : 0 ≤ E := (Real.exp_pos _).le.trans hE
  unfold sourceNu
  exact add_le_add (mul_le_mul hE hhi hell hEp)
    (div_le_div_of_nonneg_left (by norm_num) hlo hlo')

theorem densityKernel_antitone_H {Hlo H y : ℝ} (hy : 0 < y)
    (hHlo : 4 * y < Hlo) (hH : Hlo ≤ H) :
    densityKernel H y ≤ densityKernel Hlo y := by
  have hlo0 : 0 < Hlo := by linarith
  have hH0 : 0 < H := hlo0.trans_le hH
  have hdlo : 0 < Hlo - 4 * y := by linarith
  have hd : 0 < H - 4 * y := by linarith
  have hr : H / (H - 4 * y) ≤ Hlo / (Hlo - 4 * y) := by
    apply (div_le_div_iff₀ hd hdlo).mpr
    nlinarith [mul_le_mul_of_nonneg_right hH hy.le]
  have he : Real.exp (-y / 2 - 0.478 * H / y) ≤
      Real.exp (-y / 2 - 0.478 * Hlo / y) := by
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH
      (by norm_num : (0 : ℝ) ≤ 0.478)) hy.le
    linarith only [hh]
  unfold densityKernel
  exact mul_le_mul (mul_le_mul_of_nonneg_left hr (by positivity)) he
    (Real.exp_pos _).le (by positivity)

theorem original_fixed_directed_bound (n : ℕ) (p m : ℕ → ℝ)
    {Hlo Ephase Egamma ellLo ellHi : ℝ}
    (hp : MonotoneOn p (Set.Icc 0 n)) (hp0 : 0 < p 0)
    (ha : p 0 ≤ lowerLog 3100) (hb : upperLog 3100 ≤ p n)
    (hHlo : 4 * p n < Hlo) (hH : Hlo ≤ (3100 : ℝ) + Real.log 0.001)
    (hm : ∀ i < n, m i ∈ Set.Icc (p i) (p (i + 1)))
    (hphase : Real.exp (4 * 0.478) ≤ Ephase)
    (hgamma : Real.exp Real.eulerMascheroniConstant ≤ Egamma)
    (hell : 0 < ellLo)
    (hellLo : ellLo ≤ Real.log (Real.log ((3100 : ℝ) ^ (3 : ℕ))))
    (hellHi : Real.log (Real.log ((3100 : ℝ) ^ (3 : ℕ))) ≤ ellHi) :
    originalDensityScalar 3100 ≤
      (8 * Ephase * (Egamma * ellHi + 2.50637 / ellLo) * 3100) *
        ∑ i ∈ Finset.range n, cellValue Hlo (p i) (p (i + 1)) (m i) := by
  have hd := base_domain
  have hi := intervalIntegral.integral_mono_on hd.2.1
    ((densityKernel_continuousOn hd.1 hd.2.2).intervalIntegrable_of_Icc (μ := volume) hd.2.1)
    ((densityKernel_continuousOn hd.1 (by linarith :
      4 * upperLog 3100 < Hlo)).intervalIntegrable_of_Icc (μ := volume) hd.2.1)
    (fun y hy => densityKernel_antitone_H (hd.1.trans_le hy.1)
      (by linarith [hy.2]) hH)
  have he := density_integral_enclosure hp0 ha hd.2.1 hb hHlo
  have hs := partition_integral_le_sum n p m hp hp0 hHlo hm
  have hsum : 0 ≤ ∑ i ∈ Finset.range n, cellValue Hlo (p i) (p (i + 1)) (m i) := by
    apply Finset.sum_nonneg
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hlo := hp ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, hi'.le⟩ (Nat.zero_le _)
    have hup := hp ⟨Nat.zero_le _, hi'⟩ ⟨Nat.zero_le _, le_rfl⟩ hi'
    have hord := hp ⟨Nat.zero_le _, hi'.le⟩ ⟨Nat.zero_le _, hi'⟩ (Nat.le_succ i)
    exact cellValue_nonnegative (hp0.trans_le hlo) hord (by linarith)
  have hnu0 := (sourceNu_linear_scaling (L := (3100 : ℝ)) le_rfl).1
  have hnu := sourceNu_upper_of_intervals hgamma hell hellLo hellHi
  have hEp : 0 ≤ Ephase := (Real.exp_pos _).le.trans hphase
  have hcoef : 8 * Real.exp (4 * 0.478) * sourceNu ((3100 : ℝ) ^ (3 : ℕ)) * 3100 ≤
      8 * Ephase * (Egamma * ellHi + 2.50637 / ellLo) * 3100 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hphase (by norm_num)) hnu hnu0
        (by positivity)) (by norm_num)
  unfold originalDensityScalar
  exact (mul_le_mul_of_nonneg_left (hi.trans (he.trans hs)) (by positivity)).trans
    (mul_le_mul_of_nonneg_right hcoef hsum)

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.FixedIntegral
