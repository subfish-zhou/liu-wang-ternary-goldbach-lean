import LiuWang.Proof.Campaign20260915.ZetaValidation.CriticalLine

/-!
Disjoint sign-change intervals give distinct actual critical-line zeros.
This is a lower-count mechanism, not a finite-height completeness theorem.
-/

set_option autoImplicit false

noncomputable section

namespace LiuWang.Proof.Campaign20260915.ZetaValidation

theorem exists_strictMono_zero_ordinates {n : ℕ} (l r : Fin n → ℝ)
    (hwidth : ∀ i, l i < r i)
    (hsep : ∀ i j, i < j → r i ≤ l j)
    (hsign : ∀ i, criticalCompletedZeta (l i) * criticalCompletedZeta (r i) < 0) :
    ∃ t : Fin n → ℝ, StrictMono t ∧
      ∀ i, t i ∈ Set.Ioo (l i) (r i) ∧ riemannZeta (criticalPoint (t i)) = 0 := by
  have hroots (i : Fin n) := exists_critical_zero_of_sign_change (hwidth i) (hsign i)
  choose t ht hz using hroots
  have hmono : StrictMono t := by
    intro i j hij
    exact (ht i).2.trans ((hsep i j hij).trans_lt (ht j).1)
  exact ⟨t, hmono, fun i => ⟨ht i, hz i⟩⟩

theorem exists_injective_critical_zeros {n : ℕ} (l r : Fin n → ℝ)
    (hwidth : ∀ i, l i < r i)
    (hsep : ∀ i j, i < j → r i ≤ l j)
    (hsign : ∀ i, criticalCompletedZeta (l i) * criticalCompletedZeta (r i) < 0) :
    ∃ z : Fin n → ℂ, Function.Injective z ∧
      ∀ i, riemannZeta (z i) = 0 ∧ (z i).re = 1 / 2 ∧
        (z i).im ∈ Set.Ioo (l i) (r i) := by
  obtain ⟨t, hmono, ht⟩ := exists_strictMono_zero_ordinates l r hwidth hsep hsign
  refine ⟨fun i => criticalPoint (t i), ?_, ?_⟩
  · intro i j hij
    apply hmono.injective
    exact congrArg Complex.im hij
  · intro i
    exact ⟨(ht i).2, rfl, (ht i).1⟩

#print axioms exists_strictMono_zero_ordinates
#print axioms exists_injective_critical_zeros

end LiuWang.Proof.Campaign20260915.ZetaValidation
