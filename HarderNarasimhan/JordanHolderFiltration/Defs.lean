import HarderNarasimhan.NashEquilibrium.Impl
import HarderNarasimhan.FirstMoverAdvantage.Results
import HarderNarasimhan.SlopeLike.Result
import Mathlib.Order.OrderIsoNat
open Classical

namespace HarderNarasimhan

class FiniteTotalPayoff {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) : Prop where
  fin_tot_payoff : μ ⟨(⊥,⊤),bot_lt_top⟩ ≠ ⊤


class StrongDescendingChainCondition' {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) : Prop where
  wdcc' : ∀ x : ℕ → ℒ, (sax : StrictAnti x) → ∃ N : ℕ, μ ⟨(x (N +1), x N), sax <| lt_add_one N⟩ = ⊤


@[ext]
structure JordanHolderFiltration {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S)
--[FiniteTotalPayoff μ] [SlopeLike μ] [Semistable μ] [StrongDescendingChainCondition' μ]
where
  filtration : ℕ → ℒ
  antitone : Antitone filtration
  fin_len : ∃ N : ℕ, filtration N =⊥
  strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i
  first_eq_top : filtration 0 = ⊤
  step_cond₁ : ∀ k : ℕ,  (hk : k < Nat.find (fin_len)) → μ ⟨(filtration (k + 1),filtration k),strict_anti k (k+1) (lt_add_one k) hk⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩
  step_cond₂ : ∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ < μ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩



instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [h : StrongDescendingChainCondition' μ] :
StrongDescendingChainCondition μ where
  wdcc := by
    intro f saf
    rcases h.wdcc' f saf with ⟨N, hN⟩
    use N
    exact hN ▸ le_top


instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [h : StrongDescendingChainCondition' μ] {I : {p : ℒ × ℒ // p.1 < p.2}} : StrongDescendingChainCondition' (Resμ I μ) where
  wdcc' := fun f saf ↦ h.wdcc' (fun n ↦ (f n).val) fun ⦃_ _⦄ hn ↦ lt_iff_le_not_le.mpr (saf hn)


class Affine {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) : Prop where
  affine : ∀ a b : ℒ, (h : ¬ a ≤ b) → μ ⟨(a ⊓ b, a), inf_lt_left.2 h⟩ = μ ⟨(b, a ⊔ b), right_lt_sup.2 h⟩


instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [haff : Affine μ] {I : {p : ℒ × ℒ // p.1 < p.2}} : Affine (Resμ I μ) where
  affine := fun a b h ↦ haff.affine a b h

instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type*} [CompleteLattice S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S} [haff : Affine μ] : Convex μ := by
  rw [← impl.ConvexI_TotIntvl_iff_Convex]
  refine { convex := ?_ }
  intro x y hx hy hxy
  rw [haff.affine x y hxy]

instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[hftp : FiniteTotalPayoff μ] [hsl : SlopeLike μ] [hst : Semistable μ] [hwdcc' : StrongDescendingChainCondition' μ] {x : ℒ} {hx : ⊥ < x}: FiniteTotalPayoff (Resμ ⟨(⊥, x), hx⟩ μ) := by
  refine { fin_tot_payoff := ?_ }
  simp only [Resμ]
  by_contra h
  have : Semistable μ → μmax μ TotIntvl = μ TotIntvl := by
    exact fun a ↦ (List.TFAE.out (impl.thm4d21 μ hsl inferInstance inferInstance).1 0 3).2 ((impl.thm4d21 μ hsl inferInstance inferInstance).2.1 a)
  have := this hst
  simp only [μmax, TotIntvl, ne_eq] at this
  have this_q: μ ⟨(⊥, x), hx⟩ ≤ μ ⟨(⊥, ⊤), bot_lt_top⟩ := by
    rw [← this]
    apply le_sSup
    use x, ⟨in_TotIntvl x, Ne.symm <| bot_lt_iff_ne_bot.1 hx⟩
  exact (not_le_of_lt <| h ▸ lt_top_iff_ne_top.2 hftp.fin_tot_payoff) this_q

lemma fuck {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
(μ : {p : ℒ × ℒ // p.1 < p.2} → S) [SlopeLike μ] [sdc : StrongDescendingChainCondition' μ]
(filtration : ℕ → ℒ) (fin_len : ∃ N : ℕ, filtration N =⊥)
(strict_anti : ∀ i j : ℕ, i < j → j ≤ Nat.find (fin_len) → filtration j < filtration i)
(step_cond₁ : ∀ k : ℕ,  (hk : k < Nat.find (fin_len)) → μ ⟨(filtration (k + 1),filtration k),strict_anti k (k+1) (lt_add_one k) hk⟩ = μ ⟨(⊥,⊤),bot_lt_top⟩) :
(∀ i : ℕ, (hi : i < Nat.find fin_len) →
    ∀ z : ℒ, (h' : filtration (i+1) < z) → (h'' : z < filtration i) →
    μ ⟨(filtration (i+1), z), h'⟩ < μ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩)
↔ (
∀ i : ℕ, (hi : i < Nat.find fin_len) → Stable (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩ μ)
) := by
  constructor
  · intro h
    intro i hi
    have h := h i hi
    refine { toSemistable := ?_, stable := ?_ }
    · apply (impl.thm4d21 (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).2.2 (fun _ _ ↦ inferInstance)
      apply (List.TFAE.out (impl.thm4d21 (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).1 1 3).1
      --simp only [μmin_res_intvl,μ_res_intvl]
      apply eq_of_le_of_le ?_ ?_
      · apply sInf_le
        simp only [ne_eq, Set.mem_setOf_eq]
        use ⊥
        simp only [bot_ne_top, not_false_eq_true, and_true, exists_prop,in_TotIntvl]
      · apply le_sInf
        intro b hb
        simp only [ne_eq, Set.mem_setOf_eq] at hb
        rcases hb with ⟨u,hu1,hu2⟩
        rw [← hu2]
        simp only [μ_res_intvl]
        if hu : u = ⊥ then
          simp only [hu, le_refl]
        else
        have h := h u.val (lt_of_le_of_ne u.prop.1 (by
          by_contra hc
          refine hu ?_
          apply Subtype.coe_inj.1
          exact id (Eq.symm hc)
          )) (lt_of_le_of_ne u.prop.2 (by
            by_contra hc
            refine hu1.2 ?_
            apply Subtype.coe_inj.1
            exact hc
            ))
        have := ((seesaw_useful μ inferInstance (filtration (i + 1)) u.val (filtration i) ⟨(lt_of_le_of_ne u.prop.1 (by
          by_contra hc
          refine hu ?_
          apply Subtype.coe_inj.1
          exact id (Eq.symm hc)
          )),(lt_of_le_of_ne u.prop.2 (by
            by_contra hc
            refine hu1.2 ?_
            apply Subtype.coe_inj.1
            exact hc
            ))⟩).1.1 h).2
        apply le_of_lt this
    · intro x hx hx'
      have := (proposition_4_1 (Resμ ⟨(filtration (i+1), filtration i), strict_anti i (i+1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance).1
      have this' := (proposition_4_1 (Resμ ⟨(filtration (i+1), x.val), (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          refine hx ?_
          apply Subtype.coe_inj.1
          exact id (Eq.symm hc)
          ))⟩ μ) inferInstance inferInstance).1
      unfold μAstar at this
      unfold μAstar at this'
      simp only [μA_res_intvl,μmin_res_intvl] at *
      rw [this]
      have t1: @Bot.bot (Interval ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩) OrderBot.toBot = filtration (i + 1) := by rfl
      simp only [t1] at *
      have t2 : @Top.top (Interval ⟨(filtration (i + 1), ↑x), lt_of_le_of_ne (Subtype.prop x).left fun hc ↦ hx (Subtype.coe_inj.mp (id (Eq.symm hc)))⟩) OrderTop.toTop = x.val := by rfl
      simp only [t2] at *
      have t3 : (@Bot.bot (Interval ⟨(filtration (i + 1), ↑x), lt_of_le_of_ne (Subtype.prop x).left fun hc ↦ hx (Subtype.coe_inj.mp (id (Eq.symm hc)))⟩) OrderBot.toBot).val = filtration (i + 1) := by rfl
      simp only [t3] at *
      rw [this']
      have hss : Semistable (Resμ ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩ μ) := by sorry
      have := (impl.thm4d21 (Resμ ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).2.1 hss
      have := (List.TFAE.out (impl.thm4d21 (Resμ ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩ μ) inferInstance inferInstance inferInstance).1 1 3).2 this
      simp only [μmin_res_intvl,μ_res_intvl] at this
      have t4 : @Bot.bot (Interval ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩) OrderBot.toBot = filtration (i+1) := by rfl
      simp only [t4] at *
      have t5 : @Top.top (Interval ⟨(filtration (i + 1), filtration i), strict_anti i (i + 1) (lt_add_one i) hi⟩) OrderTop.toTop = filtration i := by rfl
      simp only [t5] at *
      rw [this]
      apply ne_of_lt
      have : μmin μ ⟨(filtration (i + 1), ↑x), (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          refine hx ?_
          apply Subtype.coe_inj.1
          exact id (Eq.symm hc)
          ))⟩ ≤ μ ⟨(filtration (i + 1), ↑x), (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          refine hx ?_
          apply Subtype.coe_inj.1
          exact id (Eq.symm hc)
          ))⟩ := by
        apply sInf_le
        simp only [ne_eq, id_eq, Set.mem_setOf_eq]
        use filtration (i + 1)
        simp only [exists_prop, and_true]
        constructor
        · exact ⟨le_rfl,x.prop.1⟩
        · by_contra hc
          refine hx ?_
          apply Subtype.coe_inj.1
          rw [← hc]
          rfl
      refine lt_of_le_of_lt this ?_
      refine h x.val (lt_of_le_of_ne x.prop.1 (by
          by_contra hc
          refine hx ?_
          apply Subtype.coe_inj.1
          exact id (Eq.symm hc)
          )) ?_
      apply lt_top_iff_ne_top.2 at hx'
      exact lt_iff_le_not_le.mpr hx'
  · intro h
    intro i hi z hz1 hz2
    have h := h i hi
    have h1 := h.toSemistable.semistable ⟨z,⟨le_of_lt hz1,le_of_lt hz2⟩⟩ (by
      by_contra hc
      apply Subtype.coe_inj.2 at hc
      simp only at hc
      rw [hc] at hz1
      exact lt_irrefl _ hz1
      )
    simp only [gt_iff_lt, not_lt] at h1
    have h2 := h.stable ⟨z,⟨le_of_lt hz1,le_of_lt hz2⟩⟩ (by
      by_contra hc
      apply Subtype.coe_inj.2 at hc
      simp only at hc
      rw [hc] at hz1
      exact lt_irrefl _ hz1
      ) (by
      by_contra hc
      apply Subtype.coe_inj.2 at hc
      simp only at hc
      rw [hc] at hz2
      exact lt_irrefl _ hz2
      )
    have h' := lt_of_le_of_ne h1 h2
    simp only [μA_res_intvl] at h'

    sorry



end HarderNarasimhan
