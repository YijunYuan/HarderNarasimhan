import HarderNarasimhan.Semistability.Results

noncomputable def seq {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) → ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) → μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩)
(h₃ : {YA | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB), ¬μ ⟨(xA, xB), hAB⟩ ≤ μ ⟨(YA, ⊤), h⟩}.Nonempty)
(k : ℕ)
: {YA | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB), ¬μ ⟨(xA, xB), hAB⟩ ≤ μ ⟨(YA, ⊤), h⟩} :=
  match k with
  | 0 => ⟨h₃.choose,h₃.choose_spec⟩
  | k + 1 => by
    let seqkp1 := (seq μ h₁ h₂ h₃ k).prop.out.choose_spec (seq μ h₁ h₂ h₃ k) (seq μ h₁ h₂ h₃ k).prop.out.choose
    use seqkp1.choose
    have h''' := seqkp1.choose_spec.choose_spec
    have h' : seqkp1.choose < ⊤ := by
      by_contra! hcon
      have : seqkp1.choose = ⊤ := not_lt_top_iff.mp hcon
      simp [this] at h'''
    by_contra!
    simp at this
    rcases this h' with ⟨xA,⟨hxA,hh⟩⟩
    have hhh : ∀ (xB : ℒ) (x_1 : xA < xB), μ ⟨(xA, xB), x_1⟩ ≤ μ ⟨(seq μ h₁ h₂ h₃ k, ⊤), (seq μ h₁ h₂ h₃ k).prop.choose⟩ := fun xB hAB ↦ le_trans (hh xB hAB) <| Or.resolve_left (h₂ ⟨(seq μ h₁ h₂ h₃ k, seqkp1.choose), seqkp1.choose_spec.choose⟩ h') h'''
    rcases (seq μ h₁ h₂ h₃ k).prop.out.choose_spec xA hxA with ⟨xB,⟨hAB,con⟩⟩
    exact con (hhh xB hAB)


lemma prop4d1 {ℒ : Type} [Nontrivial ℒ] [Lattice ℒ] [BoundedOrder ℒ]
{S : Type} [CompleteLattice S]
(μ : {p :ℒ × ℒ // p.1 < p.2} → S)
(h₁ : ∀ x : ℕ → ℒ, (smf : StrictMono x) → ∃ N : ℕ, μ ⟨(x N, x (N+1)), smf <| Nat.lt_add_one N⟩ ≤ μ ⟨(x N,⊤), lt_of_lt_of_le (smf <| Nat.lt_add_one N) le_top⟩)
(h₂ : ∀ z : {p :ℒ × ℒ // p.1 < p.2}, (hz :z.val.2 < ⊤) → μ z ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩ ∨ μ ⟨(z.val.2,⊤),hz⟩ ≤ μ ⟨(z.val.1,⊤),lt_trans z.prop hz⟩) :
μAstar ℒ S μ = sInf {μ ⟨(x,⊤),hx⟩ | (x : ℒ) (hx : x < ⊤) } := by
  have : ∀ yA : ℒ, (hyA : yA < ⊤) → ∃ xA : ℒ, xA < ⊤ ∧ (∀ xB : ℒ, (hAB : xA < xB) → μ ⟨(xA,xB), hAB⟩ ≤ μ ⟨(yA,⊤), hyA⟩) := by
    by_contra!
    have : {YA : ℒ | ∃ (h : YA < ⊤), ∀ xA < ⊤, ∃ xB, ∃ (hAB : xA < xB), ¬μ ⟨(xA, xB), hAB⟩ ≤ μ ⟨(YA, ⊤), h⟩}.Nonempty := this
    have hsmf : StrictMono (fun n ↦ seq μ h₁ h₂ this n) := strictMono_nat_of_lt_succ <| fun n ↦ ((seq μ h₁ h₂ this n).prop.out.choose_spec (seq μ h₁ h₂ this n) (seq μ h₁ h₂ this n).prop.out.choose).choose_spec.choose
    have hfinal : ∀ n : ℕ, ¬ μ ⟨((seq μ h₁ h₂ this n),(seq μ h₁ h₂ this (n+1))),hsmf (Nat.lt_add_one n)⟩ ≤ μ ⟨((seq μ h₁ h₂ this n),⊤),lt_of_lt_of_le (hsmf (Nat.lt_add_one n)) le_top⟩ := fun n ↦ ((seq μ h₁ h₂ this n).prop.out.choose_spec (seq μ h₁ h₂ this n) (seq μ h₁ h₂ this n).prop.out.choose).choose_spec.choose_spec
    rcases h₁ (fun n ↦ seq μ h₁ h₂ this n) hsmf with ⟨N,hN⟩
    exact (hfinal N) hN
  refine le_antisymm ?_ ?_
  · apply le_sInf
    intro y hy
    rcases hy with ⟨yA, hyA, h⟩
    rw [← h]
    rcases this yA hyA with ⟨xA, hxA, h'⟩
    have : μmax μ ⟨(xA,⊤),hxA⟩ ∈ {μmax μ ⟨(a , ⊤),(lt_of_le_of_ne ha.1.2 ha.2)⟩ | (a : ℒ) (ha : InIntvl TotIntvl a ∧ a ≠ ⊤)} := by
      refine Set.mem_setOf.mpr ?_
      use xA, ⟨in_TotIntvl xA,ne_top_of_lt hxA⟩
    refine sInf_le_of_le this (sSup_le ?_)
    rintro _ ⟨xB,⟨hxB,hxB'⟩⟩
    rw [← hxB']
    exact h' xB (lt_of_le_of_ne hxB.1.1 hxB.2)
  · apply le_sInf
    intro t ht
    rcases ht with ⟨x, hx, h⟩
    rw [← h]
    have : μ ⟨(x,⊤),lt_top_iff_ne_top.2 hx.2⟩ ∈  {x | ∃ x_1, ∃ (hx : x_1 < ⊤), μ ⟨(x_1, ⊤), hx⟩ = x} := by
      refine Set.mem_setOf.mpr ?_
      use x, lt_top_iff_ne_top.2 hx.2
    apply sInf_le_of_le this <| Set.mem_setOf.mpr <| le_sSup ?_
    use ⊤, ⟨⟨le_top,le_top⟩,hx.2⟩
