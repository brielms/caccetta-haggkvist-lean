import LeanCH.BR.BRRelayFoldBanks

/-! The actual shared-cut graph and its complete No2/No3 proof.
The same physical K clears every selected relay target. -/
namespace LeanCH.BR.WeightedSD.RelayFold
open Finset BRq2 BRq3 BR45 BRsub

def ValidCuts (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ) (K : Finset (ℕ×ℕ)) : Prop :=
  ∀z r,(z,r)∈K→z∈X1 D V u h t ∧ r∈R D V u h t ∧ D z r=true

noncomputable def eligible (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ)
    (K : Finset (ℕ×ℕ)) (r : ℕ) : Finset ℕ :=
  (W D V u h t).filter (fun w=>¬D r w=true ∧ ¬D w r=true ∧
    ∀x∈V,D w x=true→D x r=true→x=h ∨ x∈X1 D V u h t ∧ (x,r)∈K)

def Selected (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ)
    (K : Finset (ℕ×ℕ)) (Q : ℕ→Finset ℕ) : Prop :=
  ∀r∈R D V u h t,Q r⊆eligible D V u h t K r

def Old (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ) (K : Finset (ℕ×ℕ)) (a b : ℕ) : Prop :=
  D a b=true ∧ ¬(a=u ∧ b∈C D V u h t) ∧
    ¬(a∈R D V u h t ∧ (b=u ∨ b∈X1 D V u h t)) ∧ (a,b)∉K

def New (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ) (Q : ℕ→Finset ℕ) (a b : ℕ) : Prop :=
  (a∈X0 D V u h t ∧ b=u) ∨ (a∈X1 D V u h t ∧ b=t) ∨
    (a=u ∧ b=t) ∨ (a∈R D V u h t ∧ b∈Q a)

noncomputable def graph (D : CH.Digraph) (V : Finset ℕ) (u h t : ℕ)
    (K : Finset (ℕ×ℕ)) (Q : ℕ→Finset ℕ) : CH.Digraph := by
  classical
  exact fun a b=>decide (Old D V u h t K a b ∨ New D V u h t Q a b)

theorem graph_edge {D : CH.Digraph} {V : Finset ℕ} {u h t a b : ℕ}
    {K : Finset (ℕ×ℕ)} {Q : ℕ→Finset ℕ} :
    graph D V u h t K Q a b=true ↔ Old D V u h t K a b ∨ New D V u h t Q a b := by
  classical
  simp only [graph,decide_eq_true_eq]

theorem mem_eligible {D : CH.Digraph} {V : Finset ℕ} {u h t r w : ℕ}
    {K : Finset (ℕ×ℕ)} : w∈eligible D V u h t K r ↔
      w∈W D V u h t ∧ ¬D r w=true ∧ ¬D w r=true ∧
        ∀x∈V,D w x=true→D x r=true→x=h ∨ x∈X1 D V u h t ∧ (x,r)∈K := by
  classical
  simp only [eligible,mem_filter]

namespace Base
variable {D : CH.Digraph} {V : Finset ℕ} {u h t : ℕ} (B : Base D V u h t)
include B
variable {K : Finset (ℕ×ℕ)} {Q : ℕ→Finset ℕ}

theorem new_fresh (hQ : Selected D V u h t K Q) {a b : ℕ}
    (e : New D V u h t Q a b) : ¬D a b=true := by
  rcases e with ⟨ha,rfl⟩|⟨ha,rfl⟩|⟨rfl,rfl⟩|⟨ha,hb⟩
  · exact (mem_X0.mp ha).2.2.2
  · exact (mem_X1.mp ha).2.2.1
  · exact B.miss_t
  · exact (mem_eligible.mp (hQ a ha hb)).2.1

theorem new_from_u {b : ℕ} (e : New D V u h t Q u b) : b=t := by
  rcases e with ⟨hu,_⟩|⟨hu,rfl⟩|⟨_,rfl⟩|⟨hu,_⟩
  · exact False.elim ((B.X_facts (X0_X hu)).2.1 rfl)
  · exact False.elim ((B.X_facts (X1_X hu)).2.1 rfl)
  · rfl
  · exact False.elim ((B.R_facts hu).2.1 rfl)

theorem new_from_t {b : ℕ} : ¬New D V u h t Q t b := by
  intro e
  rcases e with ⟨ht,_⟩|⟨ht,_⟩|⟨htu,_⟩|⟨ht,_⟩
  · exact (B.X_facts (X0_X ht)).2.2.2.1 rfl
  · exact (B.X_facts (X1_X ht)).2.2.2.1 rfl
  · exact B.ut htu.symm
  · exact (B.R_facts ht).2.2.2.1 rfl

omit B in
theorem new_from_W {a b : ℕ} (ha : a∈W D V u h t)
    (e : New D V u h t Q a b) : a∈X0 D V u h t ∧ b=u := by
  have hw := mem_W.mp ha
  rcases e with he|⟨ha,_⟩|⟨ha,_⟩|⟨ha,_⟩
  · exact he
  · exact False.elim (hw.2.2.2.2.1 ha)
  · exact False.elim (hw.2.2.2.1 ha)
  · exact False.elim (hw.2.2.2.2.2 ha)

theorem new_chain (hQ : Selected D V u h t K Q) {a b c : ℕ}
    (e : New D V u h t Q a b) (f : New D V u h t Q b c) :
    (a∈X0 D V u h t ∧ b=u ∧ c=t) ∨
      (a∈R D V u h t ∧ b∈X0 D V u h t ∧ c=u) := by
  rcases e with ⟨ha,rfl⟩|⟨ha,rfl⟩|⟨rfl,rfl⟩|⟨ha,hb⟩
  · exact Or.inl ⟨ha,rfl,B.new_from_u f⟩
  · exact False.elim (B.new_from_t f)
  · exact False.elim (B.new_from_t f)
  · obtain ⟨hb0,hc⟩ := new_from_W (mem_eligible.mp (hQ a ha hb)).1 f
    exact Or.inr ⟨ha,hb0,hc⟩

theorem new_irrefl (hQ : Selected D V u h t K Q) (a : ℕ) : ¬New D V u h t Q a a := by
  intro e
  rcases e with ⟨ha,hau⟩|⟨ha,hat⟩|⟨hau,hat⟩|⟨ha,haa⟩
  · exact (B.X_facts (X0_X ha)).2.1 hau
  · exact (B.X_facts (X1_X ha)).2.2.2.1 hat
  · exact B.ut (hau.symm.trans hat)
  · exact (mem_W.mp (mem_eligible.mp (hQ a ha haa)).1).2.2.2.2.2 ha

theorem new_new_no_reverse (hQ : Selected D V u h t K Q) {a b : ℕ}
    (e : New D V u h t Q a b) : ¬New D V u h t Q b a := by
  intro f
  rcases B.new_chain hQ e f with ⟨ha,_,hat⟩|⟨ha,_,hau⟩
  · exact (B.X_facts (X0_X ha)).2.2.2.1 hat
  · exact (B.R_facts ha).2.1 hau

theorem new_new_no_close (hQ : Selected D V u h t K Q) {a b c : ℕ}
    (e : New D V u h t Q a b) (f : New D V u h t Q b c) :
    ¬graph D V u h t K Q c a=true := by
  intro g
  rcases B.new_chain hQ e f with ⟨ha,rfl,rfl⟩|⟨ha,hb,rfl⟩
  · rcases graph_edge.mp g with g|g
    · exact (B.X_facts (X0_X ha)).2.2.2.2.2.2 g.1
    · exact B.new_from_t g
  · rcases graph_edge.mp g with g|g
    · exact (B.R_facts ha).2.2.2.2.2.2.2.2 g.1
    · exact (B.R_facts ha).2.2.2.1 (B.new_from_u g)

theorem new_old_no_reverse (hQ : Selected D V u h t K Q) {a b : ℕ}
    (e : New D V u h t Q a b) : ¬Old D V u h t K b a := by
  intro f
  rcases e with ⟨ha,rfl⟩|⟨ha,rfl⟩|⟨rfl,rfl⟩|⟨ha,hb⟩
  · exact f.2.1 ⟨rfl,mem_C.mpr ⟨(mem_X0.mp ha).1,f.1,Or.inl ha⟩⟩
  · exact (B.X_facts (X1_X ha)).2.2.2.2.2.2 f.1
  · exact B.back f.1
  · exact (mem_eligible.mp (hQ a ha hb)).2.2.1 f.1

theorem new_old_no_two_return (hQ : Selected D V u h t K Q) {a b x : ℕ}
    (hx : x∈V.erase h) (e : New D V u h t Q a b)
    (f : Old D V u h t K b x) (g : Old D V u h t K x a) : False := by
  have hxV := (mem_erase.mp hx).2
  rcases e with ⟨ha,rfl⟩|⟨ha,rfl⟩|⟨rfl,rfl⟩|⟨ha,hb⟩
  · exact f.2.1 ⟨rfl,mem_C.mpr ⟨hxV,f.1,Or.inr ⟨a,ha,g.1⟩⟩⟩
  · have hxR := mem_R.mpr ⟨hxV,f.1,Or.inr ⟨a,ha,g.1⟩⟩
    exact g.2.2.1 ⟨hxR,Or.inr ha⟩
  · have hxR : x∈R D V a h b := mem_R.mpr ⟨hxV,f.1,Or.inl g.1⟩
    exact g.2.2.1 ⟨hxR,Or.inl rfl⟩
  · rcases (mem_eligible.mp (hQ a ha hb)).2.2.2 x hxV f.1 g.1 with heq|heq
    · exact (mem_erase.mp hx).1 heq
    · exact g.2.2.2 heq.2

theorem graph_qfree (hQ : Selected D V u h t K Q) :
    QFree (graph D V u h t K Q) (V.erase h) 3 := by
  have no1 (a : ℕ) (ha : a∈V.erase h) : ¬graph D V u h t K Q a a=true := by
    intro e
    rcases graph_edge.mp e with e|e
    · exact loopfree B.free (by decide) (mem_erase.mp ha).2 e.1
    · exact B.new_irrefl hQ a e
  have no2 (a b : ℕ) (ha : a∈V.erase h) (hb : b∈V.erase h)
      (e : graph D V u h t K Q a b=true) (f : graph D V u h t K Q b a=true) : False := by
    rcases graph_edge.mp e with e|e <;> rcases graph_edge.mp f with f|f
    · exact digonfree B.free (by decide) (mem_erase.mp ha).2 (mem_erase.mp hb).2 e.1 f.1
    · exact B.new_old_no_reverse hQ f e
    · exact B.new_old_no_reverse hQ e f
    · exact B.new_new_no_reverse hQ e f
  have no3 (a b c : ℕ) (ha : a∈V.erase h) (hb : b∈V.erase h) (hc : c∈V.erase h)
      (e : graph D V u h t K Q a b=true) (f : graph D V u h t K Q b c=true)
      (g : graph D V u h t K Q c a=true) : False := by
    rcases graph_edge.mp e with eo|en <;> rcases graph_edge.mp f with fo|fn <;> rcases graph_edge.mp g with go|gn
    · exact donor_no_triangle B.free (mem_erase.mp ha).2 (mem_erase.mp hb).2 (mem_erase.mp hc).2 eo.1 fo.1 go.1
    · exact B.new_old_no_two_return hQ hb gn eo fo
    · exact B.new_old_no_two_return hQ ha fn go eo
    · exact B.new_new_no_close hQ fn gn e
    · exact B.new_old_no_two_return hQ hc en fo go
    · exact B.new_new_no_close hQ gn en f
    · exact B.new_new_no_close hQ en fn g
    · exact B.new_new_no_close hQ en fn g
  intro a l hl hlq w
  rcases (by omega : l=1 ∨ l=2 ∨ l=3) with rfl|rfl|rfl
  · cases w with
    | step hb hab w => cases w; exact no1 _ hb hab
  · cases w with
    | step hb hab w => cases w with
      | step ha hba w => cases w; exact no2 _ _ ha hb hab hba
  · cases w with
    | step hb hab w => cases w with
      | step hc hbc w => cases w with
        | step ha hca w => cases w; exact no3 _ _ _ ha hb hc hab hbc hca

end Base
end LeanCH.BR.WeightedSD.RelayFold

