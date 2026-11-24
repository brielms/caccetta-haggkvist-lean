import checkpoints.shen_extension.RootFourCyclePacking

namespace LeanCH.BR.Closure.DisjointRootFourCycles
open BRq2 BRq3 BR45 Finset DeficitLevels RootFourCyclePacking

/-- The other three vertices of a simple directed four-cycle through h.
The witness gives their order in the original digraph. -/
def CycleInterior (D : CH.Digraph) (V : Finset ℕ) (h : ℕ) (C : Finset ℕ) : Prop :=
  C.card=3 ∧ C⊆V.erase h ∧ ∃ a z b, C={a,z,b} ∧
    D h a=true ∧ D a z=true ∧ D z b=true ∧ D b h=true

/-- Different members of the family share only the root of their cycles. -/
def Packing (D : CH.Digraph) (V : Finset ℕ) (h : ℕ) (P : Finset (Finset ℕ)) : Prop :=
  (∀ C∈P, CycleInterior D V h C) ∧ (P : Set (Finset ℕ)).PairwiseDisjoint id

private theorem interior_of_edges {D : CH.Digraph} {V : Finset ℕ} {h a z b : ℕ}
    (safe : QFree D V 3) (hv : h∈V) (av : a∈V) (zv : z∈V) (bv : b∈V)
    (ha : D h a=true) (az : D a z=true) (zb : D z b=true) (bh : D b h=true) :
    CycleInterior D V h {a,z,b} := by
  have ah : a≠h := fun e => loopfree safe (by decide) hv (e ▸ ha)
  have zh : z≠h := fun e => digonfree safe (by decide) hv av ha (e ▸ az)
  have bne : b≠h := fun e => loopfree safe (by decide) hv (e ▸ bh)
  have anz : a≠z := fun e => loopfree safe (by decide) zv (e ▸ az)
  have anb : a≠b := fun e => digonfree safe (by decide) hv bv (e ▸ ha) bh
  have znb : z≠b := fun e => loopfree safe (by decide) bv (e ▸ zb)
  exact ⟨card_triple_eq_three_iff.mpr ⟨anz,anb,znb⟩,
    insert_subset (mem_erase.mpr ⟨ah,av⟩) (insert_subset (mem_erase.mpr ⟨zh,zv⟩)
      (singleton_subset_iff.mpr (mem_erase.mpr ⟨bne,bv⟩))),a,z,b,rfl,ha,az,zb,bh⟩

/-- A maximum family of disjoint interiors hits every remaining four-cycle
through h. Its union contains exactly three vertices per cycle. -/
theorem packing_cut {D : CH.Digraph} {V : Finset ℕ} {h : ℕ}
    (safe : QFree D V 3) (hv : h∈V) :
    ∃ P, Packing D V h P ∧ CutsFour D V h (P.biUnion id) ∧
      (P.biUnion id).card=3*P.card := by
  classical
  let families := V.powerset.powerset.filter (Packing D V h)
  have zero : ∅∈families := by simp [families,Packing]
  obtain ⟨P,ok,largest⟩ := families.exists_max_image Finset.card ⟨∅,zero⟩
  obtain ⟨carrier,valid⟩ := mem_filter.mp ok
  have rows := valid.1
  have disj := valid.2
  let M := P.biUnion id
  refine ⟨P,valid,?_,?_⟩
  · intro a ha z hz b hb az zb
    obtain ⟨ao,am⟩ := mem_sdiff.mp ha
    obtain ⟨zv,zm⟩ := mem_sdiff.mp hz
    obtain ⟨bi,bm⟩ := mem_sdiff.mp hb
    let C : Finset ℕ := {a,z,b}
    have cycle : CycleInterior D V h C := interior_of_edges safe hv (outN_subset ao) zv
      (mem_inN.mp bi).1 (mem_outN.mp ao).2 az zb (mem_inN.mp bi).2
    have free : Disjoint C M := disjoint_left.mpr (by
      intro v hc
      rcases mem_insert.mp hc with rfl|hc
      · exact am
      rcases mem_insert.mp hc with rfl|hc
      · exact zm
      · exact (mem_singleton.mp hc) ▸ bm)
    have separates {T} (ht : T∈P) : Disjoint C T :=
      free.mono_right (fun x hx => mem_biUnion.mpr ⟨T,ht,hx⟩)
    have fresh : C∉P := fun cp => am (mem_biUnion.mpr ⟨C,cp,mem_insert_self _ _⟩)
    have more : insert C P ∈ families := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset (mem_powerset.mpr (cycle.2.1.trans (erase_subset _ _)))
        (mem_powerset.mp carrier)),?_,?_⟩
      · intro T ht
        rcases mem_insert.mp ht with rfl|ht
        · exact cycle
        · exact rows T ht
      · intro U hu T ht ne
        rcases mem_insert.mp hu with rfl|hu
        · exact separates ((mem_insert.mp ht).resolve_left ne.symm)
        rcases mem_insert.mp ht with rfl|ht
        · exact (separates hu).symm
        · exact disj hu ht ne
    have contradicts := largest _ more
    simp [card_insert_of_notMem fresh] at contradicts
  · rw [card_biUnion disj]
    change ∑ C ∈ P, C.card = 3 * P.card
    rw [sum_const_nat (fun C hc => (rows C hc).1),Nat.mul_comm]

/-- A small cut exists at any original root. If its incoming row is large,
the middle vertices lie outside the root and both of its open neighborhoods. -/
private theorem small_cut {s} (S : Origin 3 s) {h : ℕ} (hv : h∈S.V) :
    ∃ M : Finset ℕ, M.card<s ∧ CutsFour S.G S.V h M := by
  let O := outN S.G S.V h
  let I := inN S.G S.V h
  by_cases low : I.card<s
  · refine ⟨I,low,?_⟩
    intro a ha z hz b hb
    exact False.elim ((mem_sdiff.mp hb).2 (mem_sdiff.mp hb).1)
  let K := S.V \ insert h (O∪I)
  have disj : Disjoint O I := disjoint_left.mpr (by
    intro v vo vi
    exact digonfree S.free (by decide) hv (outN_subset vo) (mem_outN.mp vo).2 (mem_inN.mp vi).2)
  have miss : h∉O∪I := by
    intro hit
    rcases mem_union.mp hit with g|g
    · exact loopfree S.free (by decide) hv (mem_outN.mp g).2
    · exact loopfree S.free (by decide) hv (mem_inN.mp g).2
  have size : K.card+(O.card+I.card+1)=S.V.card := by
    have ov : O⊆S.V := outN_subset
    have iv : I⊆S.V := filter_subset _ _
    have eq := card_sdiff_add_card_eq_card (insert_subset hv (union_subset ov iv))
    rwa [card_insert_of_notMem miss,card_union_of_disjoint disj] at eq
  have out : s≤O.card := S.deg h hv
  refine ⟨K,by have := S.order; omega,?_⟩
  intro a ha z hz b hb az zb
  have ⟨ao,_⟩ := mem_sdiff.mp ha
  have ⟨zv,zk⟩ := mem_sdiff.mp hz
  have ⟨bi,_⟩ := mem_sdiff.mp hb
  have notMiddle : z∈insert h (O∪I) := by
    by_contra no
    exact zk (mem_sdiff.mpr ⟨zv,no⟩)
  rcases mem_insert.mp notMiddle with rfl|oi
  · exact digonfree S.free (by decide) hv (outN_subset ao) (mem_outN.mp ao).2 az
  rcases mem_union.mp oi with zo|zi
  · exact S.free h 3 (by decide) (by decide) (.step zv (mem_outN.mp zo).2
      (.step (mem_inN.mp bi).1 zb (.step hv (mem_inN.mp bi).2 (.refl h))))
  · exact S.free h 3 (by decide) (by decide) (.step (outN_subset ao) (mem_outN.mp ao).2
      (.step zv az (.step hv (mem_inN.mp zi).2 (.refl h))))

/-- The order-law cut estimates can be read on one actual packing at each root. -/
theorem native_packing {s} (S : Origin 3 s) (laws : ∀ j<s, OrderLaw 3 j (3*j+1))
    {h : ℕ} (hv : h∈S.V) :
    ∃ P, Packing S.G S.V h P ∧
      15*s+9*(inN S.G S.V h).card+4*(outN S.G S.V h).card+14 ≤ 9*S.V.card+30*P.card ∧
      (s≤(inN S.G S.V h).card → s+14≤30*P.card) ∧
      (s≤(inN S.G S.V h).card → (∀ b∈inN S.G S.V h, s≤(inN S.G S.V b).card) →
        s+1≤3*P.card+2*((s-1)/3)) := by
  obtain ⟨P,valid,cut,cnt⟩ := packing_cut S.free hv
  obtain ⟨M,ms,mc,le⟩ : ∃ M : Finset ℕ, M.card<s ∧ CutsFour S.G S.V h M ∧ M.card≤3*P.card := by
    by_cases small : (P.biUnion id).card<s
    · exact ⟨_,small,cut,cnt.le⟩
    · obtain ⟨K,ks,kc⟩ := small_cut S hv
      exact ⟨K,ks,kc,by omega⟩
  refine ⟨P,valid,?_,?_,?_⟩
  · have := native_cut S laws hv ms mc
    omega
  · intro high
    have := high_indegree_cut S laws hv high ms mc
    omega
  · intro high parents
    have := high_parent_cut S laws hv high ms mc parents
    omega

/-- A high-indegree root supports at least ceiling((s+14)/30) genuine
internally vertex-disjoint directed four-cycles. -/
theorem high_root {s} (S : Origin 3 s) (laws : ∀ j<s, OrderLaw 3 j (3*j+1))
    {h : ℕ} (hv : h∈S.V) (high : s≤(inN S.G S.V h).card) :
    ∃ P, Packing S.G S.V h P ∧ s+14≤30*P.card := by
  obtain ⟨P,valid,_,bound,_⟩ := native_packing S laws hv
  exact ⟨P,valid,bound high⟩

#print axioms packing_cut
#print axioms native_packing
#print axioms high_root
end LeanCH.BR.Closure.DisjointRootFourCycles
