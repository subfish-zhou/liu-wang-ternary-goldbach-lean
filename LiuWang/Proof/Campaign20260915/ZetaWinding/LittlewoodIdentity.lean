import LiuWang.Proof.Campaign20260915.ZetaWinding.LogMassContinuity

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

namespace LiuWang.Proof.Campaign20260915.ZetaWinding

open LiuWang.Proof.Campaign20260915.ZetaValidation

theorem right_log_mass_continuousAt (T : ℝ) :
    ContinuousAt (fun t => ∫ x in Set.Ioi (3 : ℝ),
      Real.log ‖riemannZeta (horizontalAt t x)‖) T := by
  have hc : ContinuousAt (fun t => ∫ x in Set.Ioi (3 : ℝ),
      log (riemannZeta (horizontalAt t x))) T := by
    refine continuousAt_of_dominated
      (Eventually.of_forall (fun t => (log_zeta_right_integrable t (by norm_num :
        (2 : ℝ) ≤ 3)).aestronglyMeasurable)) ?_ (log_tail_envelope_integrable 3) ?_
    · exact Eventually.of_forall (fun t => by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx' : (3 : ℝ) < x := hx
        simpa [horizontalAt] using
          norm_log_zeta_decay (s := horizontalAt t x) (by simp [horizontalAt]; linarith))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : (3 : ℝ) < x := hx
      exact (log_zeta_hasDerivAt_right (s := horizontalAt T x)
        (by simp [horizontalAt]; linarith)).continuousAt.comp
          (f := fun t => horizontalAt t x) (by unfold horizontalAt; fun_prop)
  have he (t : ℝ) : (∫ x in Set.Ioi (3 : ℝ),
      Real.log ‖riemannZeta (horizontalAt t x)‖) =
      (∫ x in Set.Ioi (3 : ℝ), log (riemannZeta (horizontalAt t x))).re := by
    simpa only [RCLike.re_to_complex, log_re] using
      integral_re (log_zeta_right_integrable t (by norm_num : (2 : ℝ) ≤ 3))
  simp_rw [he]
  exact Complex.continuous_re.continuousAt.comp hc

theorem horizontalLogMass_continuousAt {T : ℝ} (hT : T ≠ 0) :
    ContinuousAt horizontalLogMass T := by
  have hc := (zeta_finite_horizontal_log_continuousAt T (1 / 2) 3).add
    (right_log_mass_continuousAt T)
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hT] with t ht
  exact horizontalLogMass_split ht 3

theorem integral_eq_sub_finite_exception (F : Finset ℝ) {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Set.Icc a b))
    (hi : IntervalIntegrable f' volume a b)
    (hd : ∀ x ∈ Set.Ioo a b, x ∉ F → HasDerivAt f (f' x) x) :
    (∫ x in a..b, f' x) = f b - f a := by
  classical
  induction F using Finset.induction_on generalizing a b with
  | empty =>
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
      (fun x hx => hd x hx (by simp)) hi
  | @insert r F hr ih =>
    by_cases hrab : r ∈ Set.Ioo a b
    · have ha : a ≤ r := hrab.1.le
      have hb : r ≤ b := hrab.2.le
      have hia : IntervalIntegrable f' volume a r := hi.mono
        (by simpa only [Set.uIcc_of_le hab, Set.uIcc_of_le ha] using
          Set.Icc_subset_Icc le_rfl hb) le_rfl
      have hib : IntervalIntegrable f' volume r b := hi.mono
        (by simpa only [Set.uIcc_of_le hab, Set.uIcc_of_le hb] using
          Set.Icc_subset_Icc ha le_rfl) le_rfl
      have hea := ih ha (hc.mono (Set.Icc_subset_Icc le_rfl hb)) hia
        (fun x hx hn => hd x ⟨hx.1, hx.2.trans_le hb⟩ (by simp [hx.2.ne, hn]))
      have heb := ih hb (hc.mono (Set.Icc_subset_Icc ha le_rfl)) hib
        (fun x hx hn => hd x ⟨ha.trans_lt hx.1, hx.2⟩ (by simp [hx.1.ne', hn]))
      rw [← intervalIntegral.integral_add_adjacent_intervals hia hib, hea, heb]
      ring
    · apply ih hab hc hi
      intro x hx hn
      have hxr : x ≠ r := by intro he; subst x; exact hrab hx
      exact hd x hx (by simp [hxr, hn])

theorem littlewood_identity {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Real.pi * (∫ t in u..v, turingS t) = horizontalLogMass v - horizontalLogMass u := by
  classical
  let F := (zetaClosedValues v).image (fun z => |z.im|)
  rw [← intervalIntegral.integral_const_mul]
  apply integral_eq_sub_finite_exception F huv
    (fun t ht => (horizontalLogMass_continuousAt (hu.trans_le ht.1).ne').continuousWithinAt)
    ((turingS_intervalIntegrable u v).const_mul _)
  intro t ht hn
  apply horizontalLogMass_hasDerivAt_turingS (hu.trans ht.1)
  intro s hs0 hs1 he hz
  apply hn
  exact Finset.mem_image.mpr ⟨s,
    mem_zetaClosedValues.mpr ⟨hz, hs0, hs1, by rw [he]; exact ht.2.le⟩, he⟩

theorem littlewood_identity_mid {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Real.pi * (∫ t in u..v, turingSMid t) =
      horizontalLogMass v - horizontalLogMass u := by
  rw [← integral_turingS_eq_mid]
  exact littlewood_identity hu huv

#print axioms horizontalLogMass_continuousAt
#print axioms integral_eq_sub_finite_exception
#print axioms littlewood_identity
#print axioms littlewood_identity_mid

end LiuWang.Proof.Campaign20260915.ZetaWinding
