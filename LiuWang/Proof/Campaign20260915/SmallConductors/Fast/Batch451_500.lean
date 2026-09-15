import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q451.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q452.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q453.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q455.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q456.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q457.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q460.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q461.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q463.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q465.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q467.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q469.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q471.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q472.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q473.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q476.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q479.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q481.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q483.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q485.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q487.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q488.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q489.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q491.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q492.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q493.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q497.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q499.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_451_500 {q : ℕ} [NeZero q]
    (hl : 451 ≤ q) (hu : q ≤ 500) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 501, 451 ≤ k.val → Admissible k.val →
    k.val = 451 ∨
    k.val = 452 ∨
    k.val = 453 ∨
    k.val = 455 ∨
    k.val = 456 ∨
    k.val = 457 ∨
    k.val = 460 ∨
    k.val = 461 ∨
    k.val = 463 ∨
    k.val = 465 ∨
    k.val = 467 ∨
    k.val = 469 ∨
    k.val = 471 ∨
    k.val = 472 ∨
    k.val = 473 ∨
    k.val = 476 ∨
    k.val = 479 ∨
    k.val = 481 ∨
    k.val = 483 ∨
    k.val = 485 ∨
    k.val = 487 ∨
    k.val = 488 ∨
    k.val = 489 ∨
    k.val = 491 ∨
    k.val = 492 ∨
    k.val = 493 ∨
    k.val = 497 ∨
    k.val = 499 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q451.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q452.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q453.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q455.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q456.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q457.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q460.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q461.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q463.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q465.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q467.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q469.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q471.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q472.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q473.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q476.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q479.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q481.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q483.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q485.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q487.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q488.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q489.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q491.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q492.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q493.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q497.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q499.original_region chi hp hc hsq hqx hb

#print axioms range_451_500

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
