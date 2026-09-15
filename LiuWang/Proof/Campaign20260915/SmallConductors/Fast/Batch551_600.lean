import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q551.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q552.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q553.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q555.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q556.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q557.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q559.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q561.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q563.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q564.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q565.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q568.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q569.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q571.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q572.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q573.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q577.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q579.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q580.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q581.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q583.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q584.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q587.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q589.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q591.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q593.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q595.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q596.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q597.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q599.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_551_600 {q : ℕ} [NeZero q]
    (hl : 551 ≤ q) (hu : q ≤ 600) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 601, 551 ≤ k.val → Admissible k.val →
    k.val = 551 ∨
    k.val = 552 ∨
    k.val = 553 ∨
    k.val = 555 ∨
    k.val = 556 ∨
    k.val = 557 ∨
    k.val = 559 ∨
    k.val = 561 ∨
    k.val = 563 ∨
    k.val = 564 ∨
    k.val = 565 ∨
    k.val = 568 ∨
    k.val = 569 ∨
    k.val = 571 ∨
    k.val = 572 ∨
    k.val = 573 ∨
    k.val = 577 ∨
    k.val = 579 ∨
    k.val = 580 ∨
    k.val = 581 ∨
    k.val = 583 ∨
    k.val = 584 ∨
    k.val = 587 ∨
    k.val = 589 ∨
    k.val = 591 ∨
    k.val = 593 ∨
    k.val = 595 ∨
    k.val = 596 ∨
    k.val = 597 ∨
    k.val = 599 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q551.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q552.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q553.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q555.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q556.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q557.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q559.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q561.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q563.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q564.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q565.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q568.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q569.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q571.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q572.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q573.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q577.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q579.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q580.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q581.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q583.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q584.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q587.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q589.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q591.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q593.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q595.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q596.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q597.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q599.original_region chi hp hc hsq hqx hb

#print axioms range_551_600

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
