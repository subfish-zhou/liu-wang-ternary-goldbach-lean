import LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates.WeightedMoments

set_option autoImplicit false
noncomputable section
open Set

namespace LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates

theorem scalar_interval {x l u : ℝ} (hx : l ≤ x ∧ x ≤ u) (a : ℝ) :
    min (a * l) (a * u) ≤ a * x ∧ a * x ≤ max (a * l) (a * u) := by
  by_cases ha : 0 ≤ a
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hx.1 ha),
      (mul_le_mul_of_nonneg_left hx.2 ha).trans (le_max_right _ _)⟩
  · have ha' : a ≤ 0 := le_of_not_ge ha
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hx.2 ha'),
      (mul_le_mul_of_nonpos_left hx.1 ha').trans (le_max_left _ _)⟩

theorem product_interval {x y l u m n : ℝ}
    (hx : l ≤ x ∧ x ≤ u) (hy : m ≤ y ∧ y ≤ n) :
    min (min (l * m) (u * m)) (min (l * n) (u * n)) ≤ x * y ∧
      x * y ≤ max (max (l * m) (u * m)) (max (l * n) (u * n)) := by
  have h := scalar_interval hy x
  have hm := scalar_interval hx m
  have hn := scalar_interval hx n
  simp only [mul_comm m, mul_comm n] at hm hn
  exact ⟨(min_le_min hm.1 hn.1).trans h.1, h.2.trans (max_le_max hm.2 hn.2)⟩

structure RationalInterval where
  lo : ℚ
  hi : ℚ

def RationalInterval.Contains (b : RationalInterval) (x : ℝ) : Prop :=
  (b.lo : ℝ) ≤ x ∧ x ≤ b.hi

inductive RationalExpression where
  | constant : ℚ → RationalExpression
  | variable : Fin 4 → RationalExpression
  | add : RationalExpression → RationalExpression → RationalExpression
  | neg : RationalExpression → RationalExpression
  | mul : RationalExpression → RationalExpression → RationalExpression

namespace RationalExpression

def eval (v : Fin 4 → ℝ) : RationalExpression → ℝ
  | .constant c => c
  | .variable i => v i
  | .add a b => eval v a + eval v b
  | .neg a => -eval v a
  | .mul a b => eval v a * eval v b

def interval (v : Fin 4 → RationalInterval) : RationalExpression → RationalInterval
  | .constant c => ⟨c, c⟩
  | .variable i => v i
  | .add a b => ⟨(interval v a).lo + (interval v b).lo, (interval v a).hi + (interval v b).hi⟩
  | .neg a => ⟨-(interval v a).hi, -(interval v a).lo⟩
  | .mul a b =>
      let A := interval v a
      let B := interval v b
      ⟨min (min (A.lo * B.lo) (A.hi * B.lo)) (min (A.lo * B.hi) (A.hi * B.hi)),
       max (max (A.lo * B.lo) (A.hi * B.lo)) (max (A.lo * B.hi) (A.hi * B.hi))⟩

theorem interval_correct (e : RationalExpression) {v : Fin 4 → ℝ}
    {b : Fin 4 → RationalInterval} (hb : ∀ i, (b i).Contains (v i)) :
    (e.interval b).Contains (e.eval v) := by
  induction e with
  | constant c => exact ⟨le_rfl, le_rfl⟩
  | «variable» i => exact hb i
  | add a b ha hb =>
    simpa only [RationalInterval.Contains, interval, eval, Rat.cast_add] using
      And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)
  | neg a ha =>
    simpa only [RationalInterval.Contains, interval, eval, Rat.cast_neg] using
      And.intro (neg_le_neg ha.2) (neg_le_neg ha.1)
  | mul a b ha hb =>
    simpa only [RationalInterval.Contains, interval, eval, Rat.cast_min, Rat.cast_max,
      Rat.cast_mul] using product_interval ha hb

def pow (a : RationalExpression) : ℕ → RationalExpression
  | 0 => .constant 1
  | n + 1 => .mul (pow a n) a

theorem eval_pow (v : Fin 4 → ℝ) (a : RationalExpression) (n : ℕ) :
    (a.pow n).eval v = (a.eval v) ^ n := by
  induction n with
  | zero => simp [pow, eval]
  | succ n ih => simp [pow, eval, ih, pow_succ]

end RationalExpression

open RationalExpression

def momentExpression (r : ℚ) (z : RationalExpression) : ℕ → RationalExpression
  | 0 => .constant (1 / r)
  | n + 1 => .add (.mul (.constant (1 / r)) (z.pow (n + 1)))
      (.neg (.mul (.constant ((n + 1) / r)) (momentExpression r z n)))

theorem eval_momentExpression (v : Fin 4 → ℝ) (r : ℚ) (z : RationalExpression) (n : ℕ) :
    (momentExpression r z n).eval v = momentPrimitive r n (z.eval v) := by
  induction n with
  | zero => simp [momentExpression, eval, momentPrimitive]
  | succ n ih =>
    simp only [momentExpression, eval, eval_pow, ih, momentPrimitive,
      Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast]
    ring

def squareExpression (r : ℚ) (a b c d z : RationalExpression) : RationalExpression :=
  .add (.add (.add (.add (.add (.add
    (.mul (a.pow 2) (momentExpression r z 0))
    (.mul (.mul (.constant 2) (.mul a b)) (momentExpression r z 1)))
    (.mul (.add (b.pow 2) (.mul (.constant 2) (.mul a c))) (momentExpression r z 2)))
    (.mul (.add (.mul (.constant 2) (.mul a d)) (.mul (.constant 2) (.mul b c)))
      (momentExpression r z 3)))
    (.mul (.add (c.pow 2) (.mul (.constant 2) (.mul b d))) (momentExpression r z 4)))
    (.mul (.mul (.constant 2) (.mul c d)) (momentExpression r z 5)))
    (.mul (d.pow 2) (momentExpression r z 6))

theorem eval_squareExpression (v : Fin 4 → ℝ) (r : ℚ) (a b c d z : RationalExpression) :
    (squareExpression r a b c d z).eval v =
      squarePrimitive r (a.eval v) (b.eval v) (c.eval v) (d.eval v) (z.eval v) := by
  simp only [squareExpression, eval, eval_pow, eval_momentExpression, Rat.cast_ofNat, squarePrimitive]
  ring

def cubicEndpointExpression (t : ℚ) : RationalExpression :=
  let v := RationalExpression.variable 0
  let w := RationalExpression.variable 1
  let z := RationalExpression.variable 2
  let root := RationalExpression.variable 3
  let E := RationalExpression.constant 1.781076
  let C := RationalExpression.constant 2.50637
  let a := RationalExpression.add (.mul E v) (.mul C w)
  let b := RationalExpression.mul (.constant (1 / t)) (.add E (.neg (.mul C (w.pow 2))))
  let c := RationalExpression.mul (.constant (1 / (2 * t ^ 2)))
    (.add (.add (.neg E) (.mul C (w.pow 2))) (.mul (.constant (2 * 2.50637)) (w.pow 3)))
  let d := RationalExpression.mul (.constant (1 / (6 * t ^ 3)))
    (.add (.mul (.constant 2) E) (.neg (.mul C
      (.add (.add (.mul (.constant 2) (w.pow 2)) (.mul (.constant 6) (w.pow 3)))
        (.mul (.constant 6) (w.pow 4))))))
  .mul root (squareExpression (1 / 6) a b c d z)

theorem eval_cubicEndpointExpression (t : ℚ) (x : ℝ) :
    (cubicEndpointExpression t).eval
      ![Real.log (t : ℝ), 1 / Real.log (t : ℝ), Real.log x - t, x ^ (1 / 6 : ℝ)] =
      weightedSquarePrimitive (1 / 6) t (logNu t) (logNuD1 t) (logNuD2 t / 2) (logNuD3 t / 6) x := by
  simp only [cubicEndpointExpression, eval, eval_squareExpression, eval_pow, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Rat.cast_div, Rat.cast_pow,
    Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat]
  unfold weightedSquarePrimitive logNu logNuD1 logNuD2 logNuD3
  congr 2 <;> ring

end LiuWang.Proof.SourceRoute.MajorOrdinary.Continuation.IntegralCertificates
