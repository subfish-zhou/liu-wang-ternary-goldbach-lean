import LiuWang.Proof.Campaign20260915.SmallConductors.TwiceOdd
import LiuWang.Proof.EffectiveLValue.EvenHelpers.IntegralQuotient.Conductor

set_option autoImplicit false
noncomputable section

open LiuWang.Proof.EffectiveLValue

namespace LiuWang.Proof.Campaign20260915.SmallConductors

def Admissible (q : ℕ) : Prop :=
  q % 4 ≠ 2 ∧ ¬16 ∣ q ∧ ¬9 ∣ q ∧ ¬25 ∣ q ∧ ¬49 ∣ q ∧ ¬121 ∣ q ∧
    ¬169 ∣ q ∧ ¬289 ∣ q ∧ ¬361 ∣ q ∧ ¬529 ∣ q ∧ ¬841 ∣ q ∧ ¬961 ∣ q

instance (q : ℕ) : Decidable (Admissible q) := by
  unfold Admissible
  infer_instance

theorem primitive_admissible {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hsq : chi ^ 2 = 1) : Admissible q := by
  refine ⟨primitive_mod_four_ne_two chi hp,
    primitive_quadratic_not_sixteen_dvd chi hp hsq, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
        (p := 3) (by decide) (by decide)
    | exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
        (p := 5) (by decide) (by decide)
    | exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
        (p := 7) (by decide) (by decide)
    | exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
        (p := 11) (by decide) (by decide)
    | exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
        (p := 13) (by decide) (by decide)
    | exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
        (p := 17) (by decide) (by decide)
    | exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
        (p := 19) (by decide) (by decide)
    | exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
        (p := 23) (by decide) (by decide)
    | exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
        (p := 29) (by decide) (by decide)
    | exact primitive_quadratic_not_odd_prime_sq_dvd chi hp hsq
        (p := 31) (by decide) (by decide)

end LiuWang.Proof.Campaign20260915.SmallConductors
