import HarderNarasimhan.Semistability.Results

namespace Filtration
noncomputable def HNFil {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]-- [DecidableEq ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : Convex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I)
(k : Nat) : ℒ :=
  match k with
  | 0 => ⊥
  | n + 1 =>
    let prev_term := HNFil μ hμ hμcvx h n
    letI := Classical.propDecidable
    if htop : prev_term = ⊤ then
      ⊤
    else
      let I' := (⟨(prev_term , ⊤) , lt_top_iff_ne_top.2 htop⟩ : {p : ℒ × ℒ // p.1 < p.2})
      (impl.prop3d8₁' μ hμ I' (Convex_of_Convex_large TotIntvl I' ⟨bot_le,le_top⟩ μ hμcvx) (Or.casesOn
       h (fun h ↦ Or.inl h) fun h ↦
       Or.inr fun z hzI hz ↦ h ⟨(I'.val.1 , z) ,  lt_of_le_of_ne hzI.left hz⟩)).choose


lemma HNFil_prop_of_def {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : Convex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I) :
∀ n : Nat, (h' : HNFil μ hμ hμcvx h n ≠ ⊤) → IsGreatest (StI μ ⟨(HNFil μ hμ hμcvx h n , ⊤), lt_top_iff_ne_top.2 h'⟩) (HNFil μ hμ hμcvx h (n + 1)) := by
  intro n h'
  simp only [HNFil, h']
  exact (HNFil._proof_4 μ hμ hμcvx h n h').choose_spec


lemma is_strict_mono {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : Convex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I) :
∀ n : Nat, HNFil μ hμ hμcvx h n ≠ ⊤ → HNFil μ hμ hμcvx h n < HNFil μ hμ hμcvx h (n + 1) := fun
    n hn ↦ lt_of_le_of_ne (HNFil_prop_of_def μ hμ hμcvx h n hn).1.1.1 (HNFil_prop_of_def μ hμ hμcvx h n hn).1.2.1


lemma of_fin_len {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [inst_3 : WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : Convex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I)
: ∃ N : Nat, HNFil μ hμ hμcvx h N = ⊤ := by
  by_contra!
  exact (WellFounded.wellFounded_iff_no_descending_seq.1 inst_3.wf).elim ⟨fun n => HNFil μ hμ hμcvx h n, fun n => is_strict_mono μ hμ hμcvx h n (this n)⟩


noncomputable def HNlen {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : Convex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I) : Nat := by
  letI := Classical.propDecidable
  exact Nat.find (of_fin_len μ hμ hμcvx h)


lemma ne_top_iff_lt_len {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : Convex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I) :
  ∀ n : Nat, HNFil μ hμ hμcvx h n ≠ ⊤ ↔ n < HNlen μ hμ hμcvx h := by
  letI := Classical.propDecidable
  intro n
  constructor
  · intro hn
    by_contra!
    have h : ∀ n : ℕ, (hn' : HNlen μ hμ hμcvx h ≤ n) → HNFil μ hμ hμcvx h n = ⊤ := by
      apply Nat.le_induction
      · exact Nat.find_spec (of_fin_len μ hμ hμcvx h)
      · intro k hk hk'
        simp [HNFil,hk']
    exact hn (h n this)
  · exact fun hn ↦ Nat.find_min (of_fin_len μ hμ hμcvx h) hn


lemma is_strict_mono' {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ] [WellFoundedGT ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S) (hμ : μA_DescendingChainCondition μ) (hμcvx : Convex μ)
(h : (IsTotal S (· ≤ ·)) ∨
     ∀ I : {p : ℒ × ℒ // p.1 < p.2},  IsAttained μ I) :
∀ i : ℕ, ∀ j : ℕ, i < j → j ≤ HNlen μ hμ hμcvx h → HNFil μ hμ hμcvx h i < HNFil μ hμ hμcvx h j := by
  intro i
  have h' : ∀ j : ℕ, i + 1 ≤ j → j ≤ HNlen μ hμ hμcvx h → HNFil μ hμ hμcvx h i < HNFil μ hμ hμcvx h j := Nat.le_induction
    (fun hi ↦
      is_strict_mono μ hμ hμcvx h i
        ((ne_top_iff_lt_len μ hμ hμcvx h i).2 (Nat.add_one_le_iff.1 hi)))
    fun k _ hk' hk'' ↦
    lt_trans (hk' (le_trans (Nat.le_succ k) hk''))
      (is_strict_mono μ hμ hμcvx h k
        ((ne_top_iff_lt_len μ hμ hμcvx h k).2 (Nat.add_one_le_iff.1 hk'')))
  exact fun j hj hij ↦ h' j (Nat.add_one_le_iff.2 hj) hij

end Filtration
