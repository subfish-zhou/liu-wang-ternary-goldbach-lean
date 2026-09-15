import LiuWang.Proof.MultiZeroRepulsion.FullWindow

/-! The actual product Pi, strict real boundary, and all character-labelled multiplicity slots. -/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Classical
open BombieriVinogradov.SiegelWalfisz

namespace LiuWang.Proof.MultiZeroRepulsion

theorem ordinary_analytic {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (h1 : rho ≠ 1) : AnalyticAt ℂ chi.LFunction rho := by
  by_cases hc : chi = 1
  · subst chi
    exact PrincipalPsi.analytic_principal_of_ne_one h1
  · exact (DirichletCharacter.differentiable_LFunction hc).analyticAt rho

theorem ordinary_order_ne_top {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {rho : ℂ} (h1 : rho ≠ 1) : analyticOrderAt chi.LFunction rho ≠ ⊤ := by
  by_cases hc : chi = 1
  · subst chi
    rw [← PrincipalPsi.analyticOrderAt_regularized_eq_principal h1]
    intro htop
    have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero rho
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).analyticAt).mp htop
    exact PrincipalPsi.regularizedPrincipal_one_ne_zero q (congrFun hz 1)
  · intro htop
    have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero rho
      (DirichletCharacter.differentiable_LFunction hc).analyticAt).mp htop
    exact DirichletCharacter.LFunction_apply_one_ne_zero hc (congrFun hz 1)

def productL (q : ℕ) [NeZero q] : ℂ → ℂ :=
  ∏ chi : DirichletCharacter ℂ q, chi.LFunction

theorem productL_analytic (q : ℕ) [NeZero q] {rho : ℂ} (h1 : rho ≠ 1) :
    AnalyticAt ℂ (productL q) rho :=
  Finset.univ.analyticAt_prod (fun chi _ => ordinary_analytic chi h1)

theorem productL_order (q : ℕ) [NeZero q] {rho : ℂ} (h1 : rho ≠ 1) :
    analyticOrderNatAt (productL q) rho =
      ∑ chi : DirichletCharacter ℂ q, analyticOrderNatAt chi.LFunction rho := by
  have hh (s : Finset (DirichletCharacter ℂ q)) :
      analyticOrderAt (∏ chi ∈ s, chi.LFunction) rho =
        ∑ chi ∈ s, analyticOrderAt chi.LFunction rho := by
    induction s using Finset.induction_on with
    | empty => simp [analyticOrderAt_eq_zero]
    | @insert chi s hnot ih =>
      rw [Finset.prod_insert hnot, analyticOrderAt_mul (ordinary_analytic chi h1)
        (s.analyticAt_prod (fun psi _ => ordinary_analytic psi h1)), ih, Finset.sum_insert hnot]
  have he := hh Finset.univ
  simp_rw [← Nat.cast_analyticOrderNatAt (ordinary_order_ne_top _ h1)] at he
  rw [← Nat.cast_sum] at he
  exact congrArg ENat.toNat he

def strictFamilyCount (q : ℕ) [NeZero q] (alpha y : ℝ) : ℕ :=
  ∑ chi : DirichletCharacter ℂ q, ∑ rho ∈ strictZeroValues chi alpha y,
    analyticOrderNatAt chi.LFunction rho

def productZeroValues (q : ℕ) [NeZero q] (alpha y : ℝ) : Finset ℂ :=
  Finset.univ.biUnion (fun chi : DirichletCharacter ℂ q => strictZeroValues chi alpha y)

theorem mem_productZeroValues {q : ℕ} [NeZero q] {alpha y : ℝ} {rho : ℂ} :
    rho ∈ productZeroValues q alpha y ↔
      productL q rho = 0 ∧ 0 < rho.re ∧ alpha < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ y := by
  simp only [productZeroValues, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_strictZeroValues]
  rw [productL, Finset.prod_apply, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨chi, hz, h0, ha, h1, ht⟩
    exact ⟨⟨chi, hz⟩, h0, ha, h1, ht⟩
  · rintro ⟨⟨chi, hz⟩, h0, ha, h1, ht⟩
    exact ⟨chi, hz, h0, ha, h1, ht⟩

theorem strictFamilyCount_eq_product_count (q : ℕ) [NeZero q] (alpha y : ℝ) :
    strictFamilyCount q alpha y =
      ∑ rho ∈ productZeroValues q alpha y, analyticOrderNatAt (productL q) rho := by
  symm
  calc
    _ = ∑ rho ∈ productZeroValues q alpha y,
        ∑ chi : DirichletCharacter ℂ q, analyticOrderNatAt chi.LFunction rho := by
      apply Finset.sum_congr rfl
      intro rho hr
      exact productL_order q (by
        intro he; have := (mem_productZeroValues.mp hr).2.2.2.1; simp [he] at this)
    _ = ∑ chi : DirichletCharacter ℂ q, ∑ rho ∈ productZeroValues q alpha y,
        analyticOrderNatAt chi.LFunction rho := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro chi _
      symm
      apply Finset.sum_subset
      · intro rho hr
        exact Finset.mem_biUnion.mpr ⟨chi, Finset.mem_univ _, hr⟩
      · intro rho hr hn
        apply not_ne_iff.mp
        intro ho
        have hh := mem_productZeroValues.mp hr
        exact hn (mem_strictZeroValues.mpr
          ⟨apply_eq_zero_of_analyticOrderNatAt_ne_zero ho, hh.2⟩)

structure ZeroSlots (q : ℕ) [NeZero q] (alpha y : ℝ) where
  character : DirichletCharacter ℂ q
  value : ℂ
  index : ℕ
  zero_mem : value ∈ strictZeroValues character alpha y
  index_lt : index < analyticOrderNatAt character.LFunction value

def zeroSlotsSigmaEquiv (q : ℕ) [NeZero q] (alpha y : ℝ) :
    ZeroSlots q alpha y ≃
      Σ chi : DirichletCharacter ℂ q,
        Σ rho : {rho : ℂ // rho ∈ strictZeroValues chi alpha y},
          Fin (analyticOrderNatAt chi.LFunction rho.val) where
  toFun p := ⟨p.character, ⟨⟨p.value, p.zero_mem⟩, ⟨p.index, p.index_lt⟩⟩⟩
  invFun p := ⟨p.1, p.2.1.val, p.2.2.val, p.2.1.property, p.2.2.isLt⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨chi, ⟨⟨rho, hr⟩, ⟨k, hk⟩⟩⟩; rfl

instance zeroSlotsFintype (q : ℕ) [NeZero q] (alpha y : ℝ) : Fintype (ZeroSlots q alpha y) :=
  Fintype.ofEquiv _ (zeroSlotsSigmaEquiv q alpha y).symm

theorem card_zeroSlots (q : ℕ) [NeZero q] (alpha y : ℝ) :
    Fintype.card (ZeroSlots q alpha y) = strictFamilyCount q alpha y := by
  rw [Fintype.card_congr (zeroSlotsSigmaEquiv q alpha y)]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_coe_sort, strictFamilyCount]

theorem card_zeroSlots_eq_product_count (q : ℕ) [NeZero q] (alpha y : ℝ) :
    Fintype.card (ZeroSlots q alpha y) =
      ∑ rho ∈ productZeroValues q alpha y, analyticOrderNatAt (productL q) rho := by
  rw [card_zeroSlots, strictFamilyCount_eq_product_count]

theorem strictFamilyCount_le_familyCount (q : ℕ) [NeZero q] (alpha y : ℝ) :
    strictFamilyCount q alpha y ≤ DirichletZeroCount.familyCount q alpha y := by
  apply Finset.sum_le_sum
  intro chi _
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end LiuWang.Proof.MultiZeroRepulsion
