import checkpoints.shen_extension.FlatPairedExcursion

namespace LeanCH.BR.Closure.FlatReturnLayers
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor FlatExchangeChain FlatExchangeTriangle FlatPairedExcursion

private def Reach (E : CH.Digraph) (W H : Finset ℕ) (k z : ℕ) :=
  ∃h∈H, ∃l≤k,Walk E W h z l

/-- Every exterior segment from a cycle exit to a cycle entrance meets the bank.
The starting label is tested separately because Walk constrains only later vertices. -/
def Cuts (E : CH.Digraph) (V T S : Finset ℕ) : Prop :=
  ∀h∈V\T,(inN E T h).Nonempty → h∉S →
    ∀z∈V\T,(outN E T z).Nonempty → ∀l,¬ Walk E ((V\T)\S) h z l

/-- Distance from the set of all recipients of exits gives disjoint banks.
Every bank meets every exterior return, even when the walk is not shortest. -/
theorem layers {E V T m} (tv : T⊆V)
    (delay : ∀w∈V\T,(inN E T w).Nonempty → ∀v∈T,∀k,Walk E V w v k → m≤k) :
    ∃L : ℕ→Finset ℕ, (∀k<m,L k⊆V\T ∧ Cuts E V T (L k)) ∧
      (range m : Set ℕ).PairwiseDisjoint L ∧ (∑k∈range m,(L k).card)≤(V\T).card := by
  classical
  let W := V\T
  let H := W.filter (fun h => (inN E T h).Nonempty)
  let L := fun k => W.filter (fun z => Reach E W H k z ∧ ∀j<k,¬Reach E W H j z)
  have mono {z i j} (ij : i≤j) (a : Reach E W H i z) : Reach E W H j z := by
    obtain ⟨h,hh,l,le,path⟩ := a
    exact ⟨h,hh,l,le.trans ij,path⟩
  have cut (k) (km : k<m) : Cuts E V T (L k) := by
    intro h hw inh hn z zw out l walk
    have hh : h∈H := mem_filter.mpr ⟨hw,inh⟩
    have root : Reach E W H 0 h := ⟨h,hh,0,le_rfl,.refl _⟩
    cases k with
    | zero =>
      exact hn (mem_filter.mpr ⟨hw,root,by omega⟩)
    | succ k =>
      have closed (i j) (ri : Reach E W H k i) (jc : j∈W\L (k+1)) (arc : E i j=true) : Reach E W H k j := by
        obtain ⟨h',ph,t,ts,r⟩ := ri
        have hit := (mem_sdiff.mp jc).1
        have higher : Reach E W H (k+1) j := ⟨h',ph,t+1,by omega,r.snoc hit arc⟩
        by_contra low
        exact (mem_sdiff.mp jc).2 (mem_filter.mpr ⟨hit,higher,fun t lt earlier => low (mono (by omega) earlier)⟩)
      have keep {i j l} (p : Walk E (W\L (k+1)) i j l) (ri : Reach E W H k i) : Reach E W H k j := by
        induction p with
        | refl => exact ri
        | step jt e _ ih => exact ih (closed _ _ ri jt e)
      obtain ⟨s,sh,t,ts,short⟩ := keep walk (mono (Nat.zero_le _) root)
      obtain ⟨v,vh⟩ := out
      obtain ⟨vt,edge⟩ := mem_outN.mp vh
      have start := mem_filter.mp sh
      have low := delay s start.1 start.2 v vt (t+1) ((short.mono sdiff_subset).snoc (tv vt) edge)
      omega
  have dis : (range m : Set ℕ).PairwiseDisjoint L := by
    intro i _ j _ ne
    apply disjoint_left.mpr
    intro z hz hj
    have one := (mem_filter.mp hz).2
    have two := (mem_filter.mp hj).2
    rcases lt_or_gt_of_ne ne with lt|gt
    · exact two.2 i lt one.1
    · exact one.2 j gt two.1
  have total := card_le_card (biUnion_subset.mpr (fun k _ => filter_subset _ _) : (range m).biUnion L⊆W)
  rw [card_biUnion dis] at total
  exact ⟨L,fun k km => ⟨filter_subset _ _,cut k km⟩,dis,total⟩

theorem thin {q E V A B C} (free : QFree E V q)
    (ca : Cycle E V q A) (cb : Cycle E V q B) (cc : Cycle E V q C)
    (a : Packet E V A B C) (b : Packet E V B C A) (c : Packet E V C A B) :
    let T := A∪B∪C
    ∃S⊆V\T,(B\C).card*S.card≤(V\T).card ∧ Cuts E V T S := by
  classical
  intro T
  have tv : T⊆V := union_subset (union_subset ca.sub cb.sub) cc.sub
  obtain ⟨L,good,_,cap⟩ := layers tv (triple_exit free ca cb cc a b c)
  obtain ⟨i,hi,best⟩ := (range (B\C).card).exists_min_image (fun k => (L k).card)
    ⟨0,mem_range.mpr (card_pos.mpr a.live)⟩
  have lb := sum_le_sum (s:=range (B\C).card) (fun k hk => best k hk)
  simp only [sum_const,card_range,nsmul_eq_mul] at lb
  exact ⟨L i,(good i (mem_range.mp hi)).1,lb.trans cap,(good i (mem_range.mp hi)).2⟩

/-- At the smallest allowed exterior order all returns share one actual exterior label. -/
theorem single {q E V A B C} (free : QFree E V q) (hq : 1≤q)
    (ca : Cycle E V q A) (cb : Cycle E V q B) (cc : Cycle E V q C)
    (a : Packet E V A B C) (b : Packet E V B C A) (c : Packet E V C A B)
    (size : (V\(A∪B∪C)).card=q) :
    ∃z∈V\(A∪B∪C),Cuts E V (A∪B∪C) {z} := by
  classical
  obtain ⟨S,sub,cap,cut⟩ := thin free ca cb cc a b c
  obtain ⟨e⟩ := a.copy
  have cnt : (B\C).card=(A\B).card := by simpa only [Fintype.card_coe] using Fintype.card_congr e.equiv
  have m := card_sdiff_add_card_inter A B
  rw [ca.size,a.overlap,←cnt] at m
  rw [size] at cap
  have small : S.card≤1 := by
    by_contra! big
    have lo := Nat.mul_le_mul_left (B\C).card big
    omega
  rcases S.eq_empty_or_nonempty with empty|live
  · obtain ⟨z,zw⟩ := card_pos.mp (show 0<(V\(A∪B∪C)).card by omega)
    refine ⟨z,zw,?_⟩
    intro h hw hs hn v vv out k path
    apply cut h hw hs (by simp [empty]) v vv out k
    apply path.mono
    simp [empty,sdiff_subset]
  · obtain ⟨z,zs⟩ := card_eq_one.mp (show S.card=1 by have := card_pos.mpr live; omega)
    exact ⟨z,sub (zs.symm ▸ mem_singleton_self z),zs ▸ cut⟩

#print axioms layers
#print axioms thin
#print axioms single

/-- A crossing shortest cycle must contain a label of the return bank. -/
theorem hits {q E V T S N} (free : QFree E V q) (cn : Cycle E V q N)
    (cut : Cuts E V T S) (inside : (N∩T).Nonempty) (outside : (N\T).Nonempty) :
    (N∩S).Nonempty := by
  classical
  by_contra! empty
  have avoids (v) (vn : v∈N) : v∉S := fun vs => notMem_empty v (empty ▸ mem_inter.mpr ⟨vn,vs⟩)
  let L := N\T
  have sub : L⊆N := sdiff_subset
  have lv := sub.trans cn.sub
  have size := card_sdiff_add_card_inter N T
  rw [cn.size] at size
  have ip := card_pos.mpr inside
  have cap : L.card≤q := by dsimp [L]; omega
  obtain ⟨h,hl,first⟩ := exists_sink ((free.mono_set lv).reverse) outside cap
  obtain ⟨u,uh⟩ := card_pos.mp (show 0<(inN E N h).card by rw [show (inN E N h).card=1 from cn.incoming h (sub hl)]; decide)
  obtain ⟨un,edge⟩ := mem_inN.mp uh
  have ut : u∈T := by by_contra no; exact first u (mem_sdiff.mpr ⟨un,no⟩) edge
  obtain ⟨z,zl,last,k,_,walk⟩ := reach_sink_of_card (free.mono_set lv) cap hl
  obtain ⟨v,vh⟩ := card_pos.mp (show 0<(outN E N z).card by rw [cn.heads z (sub zl)]; decide)
  obtain ⟨vn,back⟩ := mem_outN.mp vh
  have vt : v∈T := by by_contra no; exact last v (mem_sdiff.mpr ⟨vn,no⟩) back
  have lift : L⊆(V\T)\S := fun i hi => mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨lv hi,(mem_sdiff.mp hi).2⟩,avoids i (sub hi)⟩
  exact cut h (mem_sdiff.mpr ⟨lv hl,(mem_sdiff.mp hl).2⟩) ⟨u,mem_inN.mpr ⟨ut,edge⟩⟩
    (avoids h (sub hl)) z (mem_sdiff.mpr ⟨lv zl,(mem_sdiff.mp zl).2⟩) ⟨v,mem_outN.mpr ⟨vt,back⟩⟩ k (walk.mono lift)

theorem puncture {q E V A B C} (free : QFree E V q) (hq : 1≤q)
    (ca : Cycle E V q A) (cb : Cycle E V q B) (cc : Cycle E V q C)
    (a : Packet E V A B C) (b : Packet E V B C A) (c : Packet E V C A B)
    (size : (V\(A∪B∪C)).card=q) :
    let T := A∪B∪C
    ∃z∈V\T,Cuts E V T {z} ∧ ∀N,Cycle E V q N → (z∉N ↔ N=A ∨ N=B ∨ N=C) := by
  intro T
  obtain ⟨z,zw,cut⟩ := single free hq ca cb cc a b c size
  refine ⟨z,zw,cut,?_⟩
  intro N cn
  constructor
  · intro avoid
    by_contra! diff
    have inside : (N∩T).Nonempty := by
      by_contra! empty
      have sub : N⊆V\T := fun i hi => mem_sdiff.mpr ⟨cn.sub hi,fun it => notMem_empty i (empty ▸ mem_inter.mpr ⟨hi,it⟩)⟩
      have lim := card_le_card sub
      rw [cn.size,show (V\T).card=q from size] at lim
      omega
    have bound := (triple_overlap free ca cb cc a b c cn diff.1 diff.2.1 diff.2.2).1
    have pos := card_pos.mpr a.live
    obtain ⟨i,ih⟩ := hits free cn cut inside (card_pos.mp (pos.trans_le bound))
    have eq := mem_singleton.mp (mem_inter.mp ih).2
    exact avoid (eq ▸ (mem_inter.mp ih).1)
  · rintro (rfl|rfl|rfl) <;> intro zn <;> apply (mem_sdiff.mp zw).2
    · exact mem_union_left _ (mem_union_left _ zn)
    · exact mem_union_left _ (mem_union_right _ zn)
    · exact mem_union_right _ zn


/-- After deleting the returned bank, every other surviving shortest cycle
is supported entirely in the smaller exterior. -/
theorem recursive_cut {q E V A B C} (free : QFree E V q)
    (ca : Cycle E V q A) (cb : Cycle E V q B) (cc : Cycle E V q C)
    (a : Packet E V A B C) (b : Packet E V B C A) (c : Packet E V C A B) :
    let T := A∪B∪C
    ∃S⊆V\T,(B\C).card*S.card≤(V\T).card ∧ Cuts E V T S ∧
      ∀N,Cycle E (V\S) q N → N=A ∨ N=B ∨ N=C ∨ Cycle E ((V\T)\S) q N := by
  intro T
  obtain ⟨S,sub,cap,cut⟩ := thin free ca cb cc a b c
  refine ⟨S,sub,cap,cut,?_⟩
  intro N cn
  by_cases na : N=A
  · exact Or.inl na
  by_cases nb : N=B
  · exact Or.inr (Or.inl nb)
  by_cases nc : N=C
  · exact Or.inr (Or.inr (Or.inl nc))
  refine Or.inr (Or.inr (Or.inr ⟨?_,cn.size,cn.heads,cn.incoming⟩))
  have full : Cycle E V q N := ⟨cn.sub.trans sdiff_subset,cn.size,cn.heads,cn.incoming⟩
  have far := (triple_overlap free ca cb cc a b c full na nb nc).1
  have out : (N\T).Nonempty := card_pos.mp ((card_pos.mpr a.live).trans_le far)
  intro i hi
  have keep := mem_sdiff.mp (cn.sub hi)
  refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨keep.1,?_⟩,keep.2⟩
  intro it
  obtain ⟨z,zh⟩ := hits free full cut ⟨i,mem_inter.mpr ⟨hi,it⟩⟩ out
  exact (mem_sdiff.mp (cn.sub (mem_inter.mp zh).1)).2 (mem_inter.mp zh).2

#print axioms recursive_cut

open PairedFamilyLoop

theorem on_schedule {F q E V} (hq : 1≤q) (free : QFree E V q)
    (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (left : ∀s : PairedFamilyLoop.State F,Cycle E V q (previous s))
    (right : ∀s : PairedFamilyLoop.State F,Cycle E V q (current s))
    (join : ∀s,previous (go s)=current s)
    (mark : ∀s,Marked E (previous s) (current s) (current (go s))) (s : PairedFamilyLoop.State F) :
    let A := previous s
    let B := current s
    let C := current (go s)
    let T := A∪B∪C
    Packet E V A B C →
    Packet E V (previous (go s)) C (current (go (go s))) →
    Packet E V (previous (go (go s))) (current (go (go s))) (current (go (go (go s)))) →
    (∃S⊆V\T,(B\C).card*S.card≤(V\T).card ∧ Cuts E V T S ∧
      ∀N,Cycle E (V\S) q N → N=A ∨ N=B ∨ N=C ∨ Cycle E ((V\T)\S) q N) ∧
    ((V\T).card=q → ∃z∈V\T,Cuts E V T {z} ∧ ∀N,Cycle E V q N → (z∉N ↔ N=A ∨ N=B ∨ N=C)) := by
  intro A B C T a b c
  have ret (z : PairedFamilyLoop.State F) := scheduled_return free (left z) (right z) (right (go z))
    (right (go (go z))) (join z) (mark z) (mark (go z))
  have d := ret s a b
  have e := ret (go s) b c
  dsimp only [A,B,C] at a b c
  rw [join s,d] at b
  rw [join (go s),d,e,join s] at c
  exact ⟨recursive_cut free (left s) (right s) (right (go s)) a b c,
    puncture free hq (left s) (right s) (right (go s)) a b c⟩

#print axioms hits
#print axioms puncture
#print axioms on_schedule

end LeanCH.BR.Closure.FlatReturnLayers

