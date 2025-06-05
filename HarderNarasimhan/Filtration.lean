import HarderNarasimhan.Semistability


noncomputable def HNfiltration {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] [DecidableEq ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvexI ⟨(⊥ ,⊤) , bot_lt_top⟩ μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  ∃ u : S, u = μA μ I)
(k : Nat) : ℒ :=
  match k with
  | 0 => ⊥
  | n + 1 =>
    let prev_term := HNfiltration μ hμ hμcvx h n
    if htop : prev_term = ⊤ then
      ⊤
    else
      let I' := (⟨(prev_term,⊤),lt_top_iff_ne_top.2 htop⟩ : {p : ℒ × ℒ // p.1 < p.2})
      (prop3d8₁' μ hμ I' (Or.casesOn
       h (fun h ↦ Or.inl h) fun h ↦
       Or.inr fun z hzI hz ↦ h ⟨(I'.val.1, z), lt_of_le_of_ne hzI.left hz⟩)).choose


lemma HNfiltration_defprop {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] [DecidableEq ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvexI ⟨(⊥ ,⊤) , bot_lt_top⟩ μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  ∃ u : S, u = μA μ I) :
∀ n : Nat, (h' : HNfiltration μ hμ hμcvx h n ≠ ⊤) → IsGreatest (St μ ⟨(HNfiltration μ hμ hμcvx h n , ⊤), lt_top_iff_ne_top.2 h'⟩) (HNfiltration μ hμ hμcvx h (n + 1)) := by
  intro n h'
  simp only [HNfiltration]
  simp [h']
  exact (HNfiltration._proof_5 μ hμ hμcvx h n
  (Eq.mpr_not (Eq.refl (HNfiltration μ hμ hμcvx h n = ⊤)) (of_eq_false (eq_false h')))).choose_spec


lemma HNfiltration_strict_increasing {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] [DecidableEq ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvexI ⟨(⊥ ,⊤) , bot_lt_top⟩ μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  ∃ u : S, u = μA μ I) :
∀ n : Nat, HNfiltration μ hμ hμcvx h n ≠ ⊤ → HNfiltration μ hμ hμcvx h n < HNfiltration μ hμ hμcvx h (n + 1) := by
  intro n hn
  sorry



lemma finite_length {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] [DecidableEq ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvexI ⟨(⊥ ,⊤) , bot_lt_top⟩ μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  ∃ u : S, u = μA μ I)
: ∃ N : Nat, HNfiltration μ hμ hμcvx h N = ⊤ := by
  sorry


noncomputable def length {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] [DecidableEq ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvexI ⟨(⊥ ,⊤) , bot_lt_top⟩ μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  ∃ u : S, u = μA μ I) : Nat :=
Nat.find (finite_length μ hμ hμcvx h)


lemma HNfiltration_prop {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ] [DecidableEq ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μDCC μ) (hμcvx : IsConvexI ⟨(⊥ ,⊤) , bot_lt_top⟩ μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  ∃ u : S, u = μA μ I) : True := sorry
