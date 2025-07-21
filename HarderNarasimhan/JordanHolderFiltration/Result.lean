import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.BoundedOrder.Basic
import HarderNarasimhan.Semistability.Defs
import HarderNarasimhan.SlopeLike.Impl
import HarderNarasimhan.NashEquilibrium.Impl
import Mathlib.Data.List.TFAE
import Mathlib.Order.OrderIsoNat
import HarderNarasimhan.JordanHolderFiltration.Impl

open Classical


instance {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLinearOrder S]
{μ : {p : ℒ × ℒ // p.1 < p.2} → S}
[hftp : FiniteTotalPayoff μ] [hsl : SlopeLike μ] [hst : Semistable μ] [hwdcc' : WeakDescendingChainCondition' μ] :
Nonempty (JordanHolderFiltration μ)
:= Nonempty.intro {filtration := impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc', antitone := fun x y hxy ↦ if hy : y ≤ Nat.find (impl.JHFil_fin_len μ FiniteTotalPayoff.fin_tot_payoff hsl hst WeakDescendingChainCondition'.wdcc') then ((Nat.le_induction (fun a ↦ le_rfl) (fun n hn hind hn' ↦ le_trans (le_of_lt <| impl.JHFil_anti_mono μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' n <| bot_lt_iff_ne_bot.2 <| Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hn') <| hind <| le_trans (le_of_lt <| lt_add_one n) hn'): ∀ y : ℕ, x ≤ y → y ≤ Nat.find (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') → impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' y ≤ impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' x) y hxy hy) else (Nat.le_induction (Nat.find_spec (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc')) fun i hi hi' ↦ by simp only [impl.JHFil, hi'];simp : ∀ n : ℕ, Nat.find (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') ≤ n → impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' n = ⊥) y (le_of_lt <| lt_of_not_le hy) ▸ bot_le, fin_len := impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc', strict_anti := fun x y hxy hx' ↦ (Nat.le_induction (fun a ↦ impl.JHFil_anti_mono μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' x <| bot_lt_iff_ne_bot.2 <| Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') <| lt_of_lt_of_le (lt_add_one x) a) (fun n hn hind hn' ↦ lt_trans (impl.JHFil_anti_mono μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' n <| bot_lt_iff_ne_bot.2 <| Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hn') <| hind (le_trans (le_of_lt <| lt_add_one n) hn')) : ∀ y : ℕ, (x+1) ≤ y → y ≤ Nat.find (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') → impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' y < impl.JHFil μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' x) y hxy hx', first_eq_top := of_eq_true (eq_self ⊤), step_cond₁ := fun k hk ↦ impl.JHFil_prop₁ μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' k <| bot_lt_iff_ne_bot.2 <| (Nat.find_min <| impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hk, step_cond₂ := fun i hi z h' h'' ↦ impl.JHFil_prop₂ μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc' i (bot_lt_iff_ne_bot.2 <| Nat.find_min (impl.JHFil_fin_len μ hftp.fin_tot_payoff hsl hst hwdcc'.wdcc') hi) z h' h''}
