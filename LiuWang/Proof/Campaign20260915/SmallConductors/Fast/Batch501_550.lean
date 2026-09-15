import LiuWang.Proof.Campaign20260915.SmallConductors.Classification
import LiuWang.Proof.SmallConductorExpansion.Continuation.Prime163
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q501.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q503.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q505.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q508.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q509.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q511.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q515.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q516.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q517.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q519.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q520.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q521.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q523.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q524.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q527.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q532.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q533.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q535.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q536.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q537.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q541.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q543.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q545.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q547.Consumer
import LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q548.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

open LiuWang.Proof.SmallConductorExpansion.Continuation

set_option synthInstance.maxSize 4096

namespace LiuWang.Proof.Campaign20260915.SmallConductors.Fast

theorem range_501_550 {q : ℕ} [NeZero q]
    (hl : 501 ≤ q) (hu : q ≤ 550) (chi : DirichletCharacter ℂ q)
    (hp : chi.IsPrimitive) (hc : chi ≠ 1) (hsq : chi ^ 2 = 1)
    {x beta : ℝ} (hqx : (q : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta) :
    chi.LFunction (beta : ℂ) ≠ 0 := by
  have ha := primitive_admissible chi hp hsq
  have hall : ∀ k : Fin 551, 501 ≤ k.val → Admissible k.val →
    k.val = 501 ∨
    k.val = 503 ∨
    k.val = 505 ∨
    k.val = 508 ∨
    k.val = 509 ∨
    k.val = 511 ∨
    k.val = 515 ∨
    k.val = 516 ∨
    k.val = 517 ∨
    k.val = 519 ∨
    k.val = 520 ∨
    k.val = 521 ∨
    k.val = 523 ∨
    k.val = 524 ∨
    k.val = 527 ∨
    k.val = 532 ∨
    k.val = 533 ∨
    k.val = 535 ∨
    k.val = 536 ∨
    k.val = 537 ∨
    k.val = 541 ∨
    k.val = 543 ∨
    k.val = 545 ∨
    k.val = 547 ∨
    k.val = 548 := by decide +kernel
  have he := hall ⟨q, by omega⟩ hl ha
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q501.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q503.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q505.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q508.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q509.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q511.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q515.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q516.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q517.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q519.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q520.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q521.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q523.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q524.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q527.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q532.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q533.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q535.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q536.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q537.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q541.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q543.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q545.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q547.original_region chi hp hc hsq hqx hb
  · exact LiuWang.Proof.Campaign20260915.SmallConductors.Fast.Q548.original_region chi hp hc hsq hqx hb

#print axioms range_501_550

end LiuWang.Proof.Campaign20260915.SmallConductors.Fast
