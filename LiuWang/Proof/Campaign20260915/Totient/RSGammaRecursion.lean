import LiuWang.Proof.Campaign20260915.Totient.RSIntegratedAll
import LiuWang.Proof.Campaign20260915.Totient.RSZeroIntegration

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Complex MeasureTheory Set
open LiuWang.Proof.ChebyshevBound.IntegratedFormula

namespace LiuWang.Proof.Campaign20260915.Totient

def rsGammaPrimitive : ℕ → ℝ → ℂ
  | 0 => fun _ => 0
  | 1 => gammaCorrection
  | m + 2 => fun x => ∫ t in (2 : ℝ)..x, rsGammaPrimitive (m + 1) t

theorem rsGammaCorrection_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn gammaCorrection (Icc a b) := by
  have hp : Continuous (fun x => (rsPsiPrimitive 1 x : ℂ)) :=
    Complex.continuous_ofReal.comp
      (intervalIntegral.continuous_primitive (rsPsiPrimitive_integrable 0) 0)
  have hz := rsZeroSum_continuousOn_Icc (by omega : 1 ≤ 1) (b := b) ha.le
  have hc : ContinuousOn
      (fun x => (rsPsiPrimitive 1 x : ℂ) -
        (((1 - Real.log (2 * Real.pi) : ℝ) : ℂ) * ((x : ℂ) - 1) +
          ((x : ℂ) - 1) ^ 2 / 2) +
        ((∑' p, rsZeroPrimitive 1 x p) - ∑' p, rsZeroPrimitive 1 1 p)) (Icc a b) :=
    (hp.continuousOn.sub (by fun_prop)).add (hz.sub continuousOn_const)
  apply hc.congr
  intro x hx
  have he := rsPsiPrimitive_one_spectral (ha.trans_le hx.1)
  linear_combination -he

theorem rs_positive_primitive_integrable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E}
    (hf : ∀ a b, 1 < a → 1 < b → IntervalIntegrable f volume a b)
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun x => ∫ t in (2 : ℝ)..x, f t) volume a b := by
  let lo := min 2 (min a b)
  let hi := max 2 (max a b)
  have hlo : 1 < lo := lt_min (by norm_num) (lt_min ha hb)
  have hhi : 1 < hi := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _)
  have horder : lo ≤ hi := (min_le_left _ _).trans (le_max_left _ _)
  have htwo : (2 : ℝ) ∈ uIcc lo hi := by
    rw [uIcc_of_le horder]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  have hc := intervalIntegral.continuousOn_primitive_interval' (hf lo hi hlo hhi) htwo
  apply (hc.mono _).intervalIntegrable
  intro t ht
  rw [uIcc_of_le horder]
  exact ⟨(min_le_right _ _).trans ht.1, ht.2.trans (le_max_right _ _)⟩

theorem rsGammaPrimitive_integrable (m : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (rsGammaPrimitive m) volume a b := by
  induction m using Nat.twoStepInduction generalizing a b with
  | zero => exact intervalIntegrable_const
  | one =>
    apply ContinuousOn.intervalIntegrable
    rw [uIcc]
    exact rsGammaCorrection_continuousOn (lt_min ha hb)
  | more m _ ih =>
    exact rs_positive_primitive_integrable (fun a b ha hb => ih ha hb) ha hb

theorem rsGammaPrimitive_integral {m : ℕ} (hm : 1 ≤ m) {x : ℝ} :
    (∫ t in (2 : ℝ)..x, rsGammaPrimitive m t) = rsGammaPrimitive (m + 1) x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp only [Nat.add_comm 1, rsGammaPrimitive]

#print axioms rsGammaCorrection_continuousOn
#print axioms rs_positive_primitive_integrable
#print axioms rsGammaPrimitive_integrable
#print axioms rsGammaPrimitive_integral

end LiuWang.Proof.Campaign20260915.Totient
