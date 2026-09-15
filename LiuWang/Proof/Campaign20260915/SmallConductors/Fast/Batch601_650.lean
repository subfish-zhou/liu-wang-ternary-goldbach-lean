import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q601.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q604.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q607.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q609.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q611.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q613.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q615.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q616.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q617.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q619.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q620.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q623.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q627.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q628.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q629.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q631.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q632.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q633.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q635.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q636.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q641.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q643.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q644.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q645.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q647.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q649.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_601_650 {q : ℕ} [NeZero q]
    (hl : 601 ≤ q) (hu : q ≤ 650) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 651, 601 ≤ k.val → Admissible k.val →
    k.val = 601 ∨
    k.val = 604 ∨
    k.val = 607 ∨
    k.val = 609 ∨
    k.val = 611 ∨
    k.val = 613 ∨
    k.val = 615 ∨
    k.val = 616 ∨
    k.val = 617 ∨
    k.val = 619 ∨
    k.val = 620 ∨
    k.val = 623 ∨
    k.val = 627 ∨
    k.val = 628 ∨
    k.val = 629 ∨
    k.val = 631 ∨
    k.val = 632 ∨
    k.val = 633 ∨
    k.val = 635 ∨
    k.val = 636 ∨
    k.val = 641 ∨
    k.val = 643 ∨
    k.val = 644 ∨
    k.val = 645 ∨
    k.val = 647 ∨
    k.val = 649 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q601.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q604.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q607.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q609.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q611.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q613.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q615.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q616.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q617.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q619.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q620.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q623.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q627.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q628.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q629.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q631.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q632.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q633.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q635.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q636.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q641.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q643.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q644.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q645.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q647.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q649.original_region chi hp hc hsq hqx hb

#print axioms range_601_650

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
