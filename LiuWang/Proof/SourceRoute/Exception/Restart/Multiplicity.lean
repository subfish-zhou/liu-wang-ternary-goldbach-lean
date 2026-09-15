import LiuWang.Proof.SourceRoute.Exception.Restart.Family

set_option autoImplicit false
noncomputable section

open AnalyticNumberTheory.LargeSieve
open LiuWang.Proof.ZeroRegionFamily

namespace LiuWang.Proof.SourceRoute.Exception.Restart

def originalZeroSlots (x : ℝ) (q : ℕ) [NeZero q] :=
  Σ z : {z : DirichletCharacter ℂ q × ℂ //
    1 - 1 / (9.645908801 * Real.log x) ≤ z.2.re ∧ |z.2.im| ≤ x / q ∧
      (z.1 ≠ 1 ∨ z.2 ≠ 1) ∧ z.1.LFunction z.2 = 0},
    Fin (analyticOrderNatAt z.val.1.LFunction z.val.2)

theorem fixed_source_slots_subsingleton (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) {q : ℕ} [NeZero q] (hq : (q : ℝ) ≤ x) :
    Subsingleton (originalZeroSlots x q) := by
  refine ⟨?_⟩
  rintro ⟨z, i⟩ ⟨w, j⟩
  have hz := fixed_source_characterization d hx hdx hb hzb hq z.val.1
    z.property.1 z.property.2.1 z.property.2.2.1 z.property.2.2.2
  have hw := fixed_source_characterization d hx hdx hb hzb hq w.val.1
    w.property.1 w.property.2.1 w.property.2.2.1 w.property.2.2.2
  have hzw : z = w := Subtype.ext (Prod.ext
    (hz.2.2.2.1.trans hw.2.2.2.1.symm) (hz.2.2.2.2.1.trans hw.2.2.2.2.1.symm))
  subst w
  have hij : i = j := by
    apply Fin.ext
    have hi : i.val < 1 := lt_of_lt_of_le i.isLt hz.2.2.2.2.2.le
    have hj : j.val < 1 := lt_of_lt_of_le j.isLt hz.2.2.2.2.2.le
    omega
  subst j
  rfl

theorem fixed_source_slots_nonempty_iff (d : PrimitiveQuadraticDatum)
    {x beta : ℝ} (hx : 10 ≤ x) (hdx : (d.modulus : ℝ) ≤ x)
    (hb : 1 - 1 / (9.645908801 * Real.log x) ≤ beta)
    (hzb : datumL d (beta : ℂ) = 0) {q : ℕ} [NeZero q] (hq : (q : ℝ) ≤ x) :
    Nonempty (originalZeroSlots x q) ↔ d.modulus ∣ q := by
  constructor
  · rintro ⟨⟨z, _⟩⟩
    exact (fixed_source_characterization d hx hdx hb hzb hq z.val.1
      z.property.1 z.property.2.1 z.property.2.2.1 z.property.2.2.2).2.2.1
  · intro hd
    let : NeZero d.modulus := ⟨d.modulus_ne⟩
    have hc : inducedAt d q ≠ 1 := by
      rw [inducedAt, dif_pos hd]
      exact fun he => d.ne_one ((DirichletCharacter.changeLevel_eq_one_iff hd).mp he)
    have ht : |(beta : ℂ).im| ≤ x / q := by
      simp only [Complex.ofReal_im, abs_zero]
      exact div_nonneg (by linarith) (Nat.cast_nonneg q)
    have hz := induced_source_zero d hd hzb
    have hh := fixed_source_characterization d hx hdx hb hzb hq (inducedAt d q)
      (by simpa using hb) ht (Or.inl hc) hz
    refine ⟨⟨⟨(inducedAt d q, (beta : ℂ)), ?_⟩, ?_⟩⟩
    · exact ⟨hb, ht, Or.inl hc, hz⟩
    · exact ⟨0, by simpa only [hh.2.2.2.2.2] using Nat.zero_lt_one⟩

end LiuWang.Proof.SourceRoute.Exception.Restart
