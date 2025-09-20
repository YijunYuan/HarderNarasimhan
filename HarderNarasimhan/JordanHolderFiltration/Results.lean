import HarderNarasimhan.JordanHolderFiltration.Impl

open Classical

namespace HarderNarasimhan

--`Theorem 4.25`
instance {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[hftp : FiniteTotalPayoff μ] [hsl : SlopeLike μ] [hst : Semistable μ] [hwdcc' : StrongDescendingChainCondition' μ] :
------------
Nonempty (JordanHolderFiltration μ)
------------
:= Nonempty.intro {
  filtration := impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc',
  antitone := fun x y hxy ↦
    if hy : y ≤ Nat.find (impl.JHFil_fin_len μ FiniteTotalPayoff.fin_tot_payoff hsl hst StrongDescendingChainCondition'.wdcc') then
      (Nat.le_induction
        (fun a ↦ le_rfl)
        (fun n hn hind hn' ↦
          le_trans (le_of_lt <| impl.JHFil_anti_mono μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' n <|
            bot_lt_iff_ne_bot.2 <|
              Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hn') <|
            hind <| le_trans (le_of_lt <| lt_add_one n) hn')
        : ∀ y : ℕ, x ≤ y →
          y ≤ Nat.find (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') →
            impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' y ≤
              impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' x
      ) y hxy hy
    else
      (Nat.le_induction
        (Nat.find_spec (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc'))
        fun i hi hi' ↦ by simp only [impl.JHFil, hi']; simp only [not_lt_bot, false_and,
          exists_false, Set.setOf_false, Set.not_nonempty_empty, ↓reduceDIte]
        : ∀ n : ℕ, Nat.find (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') ≤ n →
          impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' n = ⊥)
      y (le_of_lt <| lt_of_not_ge hy) ▸ bot_le,
  fin_len := impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc',
  strict_anti := fun x y hxy hx' ↦
    (Nat.le_induction
      (fun a ↦ impl.JHFil_anti_mono μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' x <|
        bot_lt_iff_ne_bot.2 <|
          Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') <|
            lt_of_lt_of_le (lt_add_one x) a)
      (fun n hn hind hn' ↦
        lt_trans (impl.JHFil_anti_mono μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' n <|
          bot_lt_iff_ne_bot.2 <|
            Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hn') <|
              hind (le_trans (le_of_lt <| lt_add_one n) hn'))
        : ∀ y : ℕ, (x+1) ≤ y →
          y ≤ Nat.find (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') →
            impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' y <
              impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' x
    ) y hxy hx',
  first_eq_top := of_eq_true (eq_self ⊤),
  step_cond₁ := fun k hk ↦
    impl.JHFil_prop₁ μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' k <|
      bot_lt_iff_ne_bot.2 <|
        (Nat.find_min <| impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hk,
  step_cond₂ := fun i hi z h' h'' ↦
    impl.JHFil_prop₂ μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' i
      (bot_lt_iff_ne_bot.2 <| Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hi) z h' h''
}


theorem piecewise_stable_of_JordanHolderFiltration
{ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[SlopeLike μ] [sdc : StrongDescendingChainCondition' μ]
(JH : JordanHolderFiltration μ) :
∀ i : ℕ, (hi : i < Nat.find JH.fin_len) → Stable (Resμ ⟨(JH.filtration (i+1), JH.filtration i), JH.strict_anti i (i+1) (lt_add_one i) hi⟩ μ) := by
  exact impl.stable_of_step_cond₂ μ JH.filtration JH.fin_len JH.strict_anti JH.step_cond₂


theorem length_eq_of_JordanHolderFiltration {ℒ : Type*} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] [IsModularLattice ℒ]
{S : Type*} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[FiniteTotalPayoff μ] [SlopeLike μ] [Semistable μ]
[StrongDescendingChainCondition' μ] [Affine μ] :
------------
∀ JH1 JH2 : JordanHolderFiltration μ, Nat.find JH1.fin_len = Nat.find JH2.fin_len
------------
:= fun JH1 JH2 ↦ eq_of_le_of_le (impl.induction_on_length_of_JordanHolderFiltration (Nat.find JH2.fin_len) ℒ _ _ _ inferInstance inferInstance _ _ μ inferInstance inferInstance inferInstance inferInstance inferInstance ⟨JH2,rfl.le⟩ JH1) <| impl.induction_on_length_of_JordanHolderFiltration (Nat.find JH1.fin_len) ℒ _ _ _ inferInstance inferInstance _ _ _ inferInstance inferInstance inferInstance inferInstance inferInstance ⟨JH1,rfl.le⟩ JH2


end HarderNarasimhan
