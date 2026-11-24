import checkpoints.shen_extension.FourReturnEscape
import checkpoints.shen_extension.ThresholdReturn

namespace LeanCH.BR.Closure.PaidLayerDescent
open BRq2 BRq3 BR45 Finset DeficitLevels

/-- On a proper carrier, even the minimum *actual* row must obey the
smaller-degree order law. Use least order at the original degree. -/
theorem light {q s} (O : Origin q s) (laws : ∀ j<s, OrderLaw q j (q*j+1))
    {T : Finset ℕ} (sub : T⊆O.V) (proper : T.card<O.V.card) (live : T.Nonempty) :
    ∃ x∈T, q*(outN O.G T x).card+1≤T.card := by
  obtain ⟨x,hx,minimal⟩ := T.exists_min_image (fun x => (outN O.G T x).card) live
  have low : (outN O.G T x).card<s := by
    by_contra! ge
    exact proper.not_ge (O.least O.G T (O.free.mono_set sub) (fun v hv => ge.trans (minimal v hv)) live)
  exact ⟨x,hx,laws _ low O.G T (O.free.mono_set sub) minimal live⟩

private theorem split {D : CH.Digraph} {V B : Finset ℕ} (sub : B⊆V) (v : ℕ) :
    (outN D (V\B) v).card+(outN D B v).card=(outN D V v).card := by
  have eq : outN D (V\B) v=outN D V v\outN D B v := by
    ext z; simp only [mem_sdiff,mem_outN]; tauto
  rw [eq,card_sdiff_add_card_eq_card (show outN D B v⊆outN D V v from
    fun z hz => mem_outN.mpr ⟨sub (mem_outN.mp hz).1,(mem_outN.mp hz).2⟩)]

/-- A is previously processed, B is the current bank, and every vertex
remaining in T has at most c old heads. A particular row in T must supply
the displayed number of actual heads in B. -/
theorem bank_witness {q s} (O : Origin q s) (laws : ∀ j<s, OrderLaw q j (q*j+1))
    {A B : Finset ℕ} (av : A⊆O.V) (bv : B⊆O.V\A)
    (proper : ((O.V\A)\B).card<O.V.card) (live : ((O.V\A)\B).Nonempty)
    {c} (old : ∀x∈(O.V\A)\B, (outN O.G A x).card≤c) :
    ∃x∈(O.V\A)\B, q*s+1≤((O.V\A)\B).card+q*c+q*(outN O.G B x).card := by
  obtain ⟨x,xt,row⟩ := light O laws (sdiff_subset.trans sdiff_subset) proper live
  have deg := O.deg x (mem_sdiff.mp (mem_sdiff.mp xt).1).1
  have first := split (D:=O.G) av x
  have second := split (D:=O.G) bv x
  have bound : s≤(outN O.G ((O.V\A)\B) x).card+c+(outN O.G B x).card := by
    have := old x xt; omega
  have mul := Nat.mul_le_mul_left q bound
  simp only [Nat.mul_add] at mul
  exact ⟨x,xt,by omega⟩

/-- Promote every fresh row with at least r+1 heads into B. Subsequent
rounds use the promoted bank alone. Old and new incidence bills add. -/
def promote (D : CH.Digraph) (V A B : Finset ℕ) (r : ℕ) : Finset ℕ :=
  ((V\A)\B).filter (fun x => r+1≤(outN D B x).card)

theorem next_old {D V A B r c}
    (old : ∀x∈(V\A)\B, (outN D A x).card≤c) :
    ∀x∈(V\(A∪B))\promote D V A B r, (outN D (A∪B) x).card≤c+r := by
  intro x hx
  obtain ⟨xw,xp⟩ := mem_sdiff.mp hx
  obtain ⟨xv,xab⟩ := mem_sdiff.mp xw
  have tail : x∈(V\A)\B := mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨xv,fun ha => xab (mem_union_left _ ha)⟩,
    fun hb => xab (mem_union_right _ hb)⟩
  have small : (outN D B x).card≤r := by by_contra! ge; exact xp (mem_filter.mpr ⟨tail,ge⟩)
  have eq : outN D (A∪B) x = outN D A x ∪ outN D B x := by
    ext z; simp only [mem_outN,mem_union]; tauto
  rw [eq]
  exact (card_union_le _ _).trans (Nat.add_le_add (old x tail) small)

structure Layers (D : CH.Digraph) (V : Finset ℕ) where
  old : Finset ℕ
  bank : Finset ℕ
  cost : ℕ
  old_sub : old⊆V
  bank_sub : bank⊆V\old
  paid : ∀x∈(V\old)\bank, (outN D old x).card≤cost

def Layers.start {D V} (J : Finset ℕ) (jv : J⊆V) : Layers D V :=
  ⟨∅,J,0,empty_subset _,by simpa using jv,by simp [outN]⟩

def Layers.step {D V} (L : Layers D V) (r : ℕ) : Layers D V where
  old := L.old∪L.bank
  bank := promote D V L.old L.bank r
  cost := L.cost+r
  old_sub := union_subset L.old_sub (L.bank_sub.trans sdiff_subset)
  bank_sub := by
    intro x hx
    obtain ⟨pre,nb⟩ := mem_sdiff.mp (mem_filter.mp hx).1
    obtain ⟨xv,na⟩ := mem_sdiff.mp pre
    exact mem_sdiff.mpr ⟨xv,fun ab => (mem_union.mp ab).elim na nb⟩
  paid := next_old L.paid

/-- A quantitative constraint at every reachable node. At zero bank size
it is the order bound for the honest induced smaller host on the tail. -/
theorem price {q s} (O : Origin q s) (laws : ∀ j<s, OrderLaw q j (q*j+1))
    (L : Layers O.G O.V) (live : ((O.V\L.old)\L.bank).Nonempty)
    (used : (L.old∪L.bank).Nonempty) :
    ∃x∈(O.V\L.old)\L.bank, q*s+1+L.old.card+L.bank.card ≤
      O.V.card+q*L.cost+q*(outN O.G L.bank x).card := by
  have c1 := card_sdiff_add_card_eq_card L.old_sub
  have c2 := card_sdiff_add_card_eq_card L.bank_sub
  have pos : 0<L.old.card+L.bank.card := (card_pos.mpr used).trans_le (card_union_le _ _)
  obtain ⟨x,xt,bill⟩ := bank_witness O laws L.old_sub L.bank_sub (by omega) live L.paid
  exact ⟨x,xt,by omega⟩

/-- An actual exit from a stopped threshold process. For general input this
returns the original induced graph on the smaller carrier with its degree.
There are no arcs to add or weights to choose. -/
theorem stopped_host {D V s} {L : Layers D V} (deg : ∀x∈V,s≤(outN D V x).card)
    (stopped : L.bank=∅) :
    ∀x∈V\L.old, s-L.cost≤(outN D (V\L.old) x).card := by
  intro x hx
  have old := L.paid x (by simpa [stopped] using hx)
  have part := split (D:=D) L.old_sub x
  have := deg x (mem_sdiff.mp hx).1
  omega

#print axioms price
#print axioms Layers.step
#print axioms stopped_host
end LeanCH.BR.Closure.PaidLayerDescent
