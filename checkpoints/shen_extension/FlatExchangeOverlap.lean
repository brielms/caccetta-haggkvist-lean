import checkpoints.shen_extension.FlatExchangeChain

namespace LeanCH.BR.Closure.FlatExchangeOverlap
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor FlatExchangeIntervals FlatExchangeChain

/-- Deleting a nonempty directed interval from a shortest cycle leaves a
connected interval. Its only possible incoming arc from the deleted path
comes from the final vertex of that path. -/
theorem complement_connected {q E V B L f} (free : QFree E V q) (cy : Cycle E V q B)
    (sub : L⊆B) (live : L.Nonempty) (P : Chain E L f) : Connected E (B\L) := by
  classical
  intro label same u hu v hv
  let H := B\L
  have size := card_sdiff_add_card_eq_card sub
  rw [cy.size] at size
  have lp := card_pos.mpr live
  have cap : H.card≤q := by dsimp [H]; omega
  let last := f (L.card-1)
  have lastMem : last∈B := sub (P.mem (by omega))
  have entry (c : Bool) (y) (hy : y∈H) (yc : label y=c) :
      ∃r∈H, label r=c ∧ E last r=true := by
    let K := H.filter (fun z => label z=c)
    have kv : K⊆V := (filter_subset _ _).trans (sdiff_subset.trans cy.sub)
    have kc : K.card≤q := (card_le_card (filter_subset _ _)).trans cap
    obtain ⟨r,hr,nop⟩ := exists_sink ((free.mono_set kv).reverse) ⟨y,mem_filter.mpr ⟨hy,yc⟩⟩ kc
    obtain ⟨rh,rc⟩ := mem_filter.mp hr
    have rb := (mem_sdiff.mp rh).1
    obtain ⟨b,hb⟩ := card_pos.mp (show 0<(inN E B r).card by rw [show (inN E B r).card=1 from cy.incoming r rb]; decide)
    obtain ⟨bb,edge⟩ := mem_inN.mp hb
    have bl : b∈L := by
      by_contra out
      have bh : b∈H := mem_sdiff.mpr ⟨bb,out⟩
      exact nop b (mem_filter.mpr ⟨bh,(same b bh r rh edge).trans rc⟩) edge
    obtain ⟨i,hi,rfl⟩ := P.index bl
    have final : i=L.card-1 := by
      by_contra ne
      have hnext : i+1<L.card := by omega
      have eq := card_le_one.mp (cy.heads (f i) bb).le _ (mem_outN.mpr ⟨rb,edge⟩)
        _ (mem_outN.mpr ⟨sub (P.mem hnext),(P.edge i hi _ hnext).mpr rfl⟩)
      exact (mem_sdiff.mp rh).2 (eq ▸ P.mem hnext)
    exact ⟨r,rh,rc,by simpa only [last,final] using edge⟩
  obtain ⟨r,hr,ru,er⟩ := entry (label u) u hu rfl
  obtain ⟨s,hs,sv,es⟩ := entry (label v) v hv rfl
  have eq := card_le_one.mp (cy.heads last lastMem).le _ (mem_outN.mpr ⟨(mem_sdiff.mp hr).1,er⟩)
    _ (mem_outN.mpr ⟨(mem_sdiff.mp hs).1,es⟩)
  exact ru.symm.trans ((congrArg label eq).trans sv)

/-- A common vertex in all three cycles would propagate membership in
the preceding cycle around the entire retained interval, up to the mark. -/
theorem no_triple {q E V A B C f} (free : QFree E V q)
    (ca : Cycle E V q A) (cb : Cycle E V q B)
    (mark : ∃y∈B∩C,y∉A) (live : (B\C).Nonempty) (P : Chain E (B\C) f)
    (e : ↥(V\(A\B)) ≃ ↥(V\(B\C)))
    (fix : ∀i : ↥(V\(A\B)),(i:ℕ)∈V\(B\C) → (e i:ℕ)=i)
    (iso : ∀i j : ↥(V\(A\B)),E i j=E (e i) (e j)) : Disjoint (A∩B) (B∩C) := by
  classical
  let S := V\(A\B)
  let T := V\(B\C)
  let H := B\(B\C)
  have conn := complement_connected free cb (sdiff_subset : B\C⊆B) live P
  have shared (i) (hi : i∈H) : i∈S ∧ i∈T := by
    obtain ⟨ib,out⟩ := mem_sdiff.mp hi
    exact ⟨mem_sdiff.mpr ⟨cb.sub ib,fun d => (mem_sdiff.mp d).2 ib⟩,mem_sdiff.mpr ⟨cb.sub ib,out⟩⟩
  have copy (t) (ta : t∈A) (tb : t∉B) : ∃r : ↥S,(r:ℕ)∈B\C ∧ (e r:ℕ)=t := by
    have tv := ca.sub ta
    let b : ↥T := ⟨t,mem_sdiff.mpr ⟨tv,fun h => tb (mem_sdiff.mp h).1⟩⟩
    let a := e.symm b
    have ab : (e a:ℕ)=t := congrArg Subtype.val (e.apply_symm_apply b)
    refine ⟨a,?_,ab⟩
    by_contra no
    have atv : (a:ℕ)∈T := mem_sdiff.mpr ⟨(mem_sdiff.mp a.property).1,no⟩
    have eq : t=(a:ℕ) := ab.symm.trans (fix a atv)
    exact (mem_sdiff.mp a.property).2 (eq ▸ mem_sdiff.mpr ⟨ta,tb⟩)
  have closed (u) (hu : u∈H) (v) (hv : v∈H) (uv : E u v=true) : u∈A ↔ v∈A := by
    obtain ⟨us,ut⟩ := shared u hu
    obtain ⟨vs,vt⟩ := shared v hv
    have ub := (mem_sdiff.mp hu).1
    have vb := (mem_sdiff.mp hv).1
    constructor
    · intro ua
      obtain ⟨t,ht⟩ := card_pos.mp (show 0<(outN E A u).card by rw [ca.heads u ua]; decide)
      obtain ⟨ta,arc⟩ := mem_outN.mp ht
      by_cases tb : t∈B
      · have eq := card_le_one.mp (cb.heads u ub).le _ (mem_outN.mpr ⟨tb,arc⟩) _ (mem_outN.mpr ⟨vb,uv⟩)
        exact eq ▸ ta
      · obtain ⟨r,hr,ert⟩ := copy t ta tb
        have eq := iso ⟨u,us⟩ r
        rw [fix ⟨u,us⟩ ut,ert] at eq
        have hit := card_le_one.mp (cb.heads u ub).le _ (mem_outN.mpr ⟨(mem_sdiff.mp hr).1,eq.trans arc⟩)
          _ (mem_outN.mpr ⟨vb,uv⟩)
        exact ((mem_sdiff.mp hv).2 (hit ▸ hr)).elim
    · intro va
      obtain ⟨t,ht⟩ := card_pos.mp (show 0<(inN E A v).card by rw [show (inN E A v).card=1 from ca.incoming v va]; decide)
      obtain ⟨ta,arc⟩ := mem_inN.mp ht
      by_cases tb : t∈B
      · have eq := card_le_one.mp (cb.incoming v vb).le _ (mem_inN.mpr ⟨tb,arc⟩) _ (mem_inN.mpr ⟨ub,uv⟩)
        exact eq ▸ ta
      · obtain ⟨r,hr,ert⟩ := copy t ta tb
        have eq := iso r ⟨v,vs⟩
        rw [fix ⟨v,vs⟩ vt,ert] at eq
        have hit := card_le_one.mp (cb.incoming v vb).le _ (mem_inN.mpr ⟨(mem_sdiff.mp hr).1,eq.trans arc⟩)
          _ (mem_inN.mpr ⟨ub,uv⟩)
        exact ((mem_sdiff.mp hu).2 (hit ▸ hr)).elim
  have same : ConstantOnArcs E H (fun i => decide (i∈A)) := by
    intro u hu v hv edge
    by_cases ua : u∈A
    · simp [ua,(closed u hu v hv edge).mp ua]
    · simp [ua,mt (closed u hu v hv edge).mpr ua]
  obtain ⟨y,hy,ya⟩ := mark
  apply disjoint_left.mpr
  intro i prev next
  have asH (i) (h : i∈B∩C) : i∈H :=
    mem_sdiff.mpr ⟨(mem_inter.mp h).1,fun d => (mem_sdiff.mp d).2 (mem_inter.mp h).2⟩
  have contradiction := conn _ same i (asH i next) y (asH y hy)
  simp [(mem_inter.mp prev).1,ya] at contradiction

#print axioms complement_connected
#print axioms no_triple

/-- Every contact of a shared vertex with the moved vertices comes with
a second, different contact in the same direction. -/
private theorem paired_contacts {E : CH.Digraph} {S T : Finset ℕ} (e : ↥S ≃ ↥T)
    (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) (iso : ∀i j : ↥S,E i j=E (e i) (e j))
    {h} (hs : h∈S) (ht : h∈T) {i} (im : i∈FlatExchangeCycle.moved S T) :
    ∃j∈FlatExchangeCycle.moved S T,i≠j ∧ E h i=E h j ∧ E i h=E j h := by
  let u : ↥S := ⟨h,hs⟩
  rcases mem_union.mp im with a | a
  · obtain ⟨s,t⟩ := mem_sdiff.mp a
    let r : ↥S := ⟨i,s⟩
    have ex : (e r:ℕ)∉S := by
      intro hit
      have eq : e ⟨e r,hit⟩=e r := Subtype.ext (fix ⟨e r,hit⟩ (e r).property)
      have val : (e r:ℕ)=i := congrArg Subtype.val (e.injective eq)
      exact t (val ▸ (e r).property)
    refine ⟨e r,mem_union_right _ (mem_sdiff.mpr ⟨(e r).property,ex⟩),fun eq => t (eq ▸ (e r).property),?_,?_⟩
    · simpa only [fix u ht] using iso u r
    · simpa only [fix u ht] using iso r u
  · obtain ⟨t,s⟩ := mem_sdiff.mp a
    let v : ↥T := ⟨i,t⟩
    let r := e.symm v
    have image : (e r:ℕ)=i := congrArg Subtype.val (e.apply_symm_apply v)
    have ex : (r:ℕ)∉T := fun h => s ((image.symm.trans (fix r h)) ▸ r.property)
    refine ⟨r,mem_union_left _ (mem_sdiff.mpr ⟨r.property,ex⟩),fun eq => s (eq ▸ r.property),?_,?_⟩
    · simpa only [fix u ht,image] using (iso u r).symm
    · simpa only [fix u ht,image] using (iso r u).symm

theorem overlap {q E V A B C f} (hq : 2≤q) (free : QFree E V q)
    (ca : Cycle E V q A) (cb : Cycle E V q B) (mark : ∃y∈B∩C,y∉A)
    (eqSize : (A\B).card=(B\C).card) (large : q<2*(B\C).card) :
    let S := V\(A\B)
    let T := V\(B\C)
    ∀e : ↥S ≃ ↥T, (∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) →
      (∀i j : ↥S,E i j=E (e i) (e j)) → Chain E (S\T) f →
      Disjoint (A∩B) (B∩C) ∧
      (2*(B\C).card=q+1 → A=FlatExchangeCycle.moved S T ∧
        ∀h∈V\A,(outN E A h)=∅ ∨ (inN E A h)=∅) := by
  classical
  intro S T e fix iso path
  have left : S\T=B\C := by
    ext i; have bv := @cb.sub i; simp only [S,T,mem_sdiff]; tauto
  have right : T\S=A\B := by
    ext i; have av := @ca.sub i; simp only [S,T,mem_sdiff]; tauto
  have dis := no_triple free ca cb mark (card_pos.mp (by omega)) (left ▸ path) e fix iso
  refine ⟨dis,fun endpoint => ?_⟩
  have incl : A∩B⊆B\C := by
    intro i hi
    exact mem_sdiff.mpr ⟨(mem_inter.mp hi).2,fun h => disjoint_left.mp dis hi (mem_inter.mpr ⟨(mem_inter.mp hi).2,h⟩)⟩
  have cnt := card_sdiff_add_card_inter A B
  rw [ca.size,eqSize] at cnt
  have full := eq_of_subset_of_card_le incl (by omega)
  have old : A=FlatExchangeCycle.moved S T := by
    rw [FlatExchangeCycle.moved,left,right,←full]
    ext i; simp only [mem_union,mem_sdiff,mem_inter]; tauto
  refine ⟨old,?_⟩
  intro h hh
  have hv := (mem_sdiff.mp hh).1
  have ns := (mem_sdiff.mp hh).2
  have hs : h∈S := mem_sdiff.mpr ⟨hv,fun d => ns (mem_sdiff.mp d).1⟩
  have ht : h∈T := mem_sdiff.mpr ⟨hv,fun d => ns (mem_inter.mp (full.symm ▸ d)).1⟩
  by_contra! both
  obtain ⟨p,hp⟩ := both.2
  obtain ⟨r,hr⟩ := both.1
  obtain ⟨t,tm,pt,_,th⟩ := paired_contacts e fix iso hs ht (old ▸ (mem_inN.mp hp).1)
  obtain ⟨z,zm,rz,hz,_⟩ := paired_contacts e fix iso hs ht (old ▸ (mem_outN.mp hr).1)
  have ti : t∈inN E A h := mem_inN.mpr ⟨old.symm ▸ tm,th.symm.trans (mem_inN.mp hp).2⟩
  have zo : z∈outN E A h := mem_outN.mpr ⟨old.symm ▸ zm,hz.symm.trans (mem_outN.mp hr).2⟩
  have twoI := one_lt_card.mpr ⟨p,hp,t,ti,pt⟩
  have twoO := one_lt_card.mpr ⟨r,hr,z,zo,rz⟩
  have bound := BRsub.cycle_two_sided_contact_cap hq free ca.sub ca.size ca.heads hv ⟨p,hp⟩ ⟨r,hr⟩
  omega

theorem on_mark {F q E V} (hq : 2≤q) (free : QFree E V q) {x : ℕ→ℚ} {s t : PairedFamilyLoop.State F}
    (ca : Cycle E V q (PairedFamilyLoop.previous s)) (cb : Cycle E V q (PairedFamilyLoop.current s))
    {send : ↥(PairedFamilyLoop.previous s) ≃ ↥(PairedFamilyLoop.previous t)}
    (mark : PairedFamilyLoop.previous t=PairedFamilyLoop.current s ∧
      ∃ b,∃r : ↥(PairedFamilyLoop.previous s),E b r=false ∧ E b (send r)=true ∧
        FullFamilySchedule.Mark q E V x s t send b (send r) r)
    (size : (RawRepairAlternative.gone s).card=(RawRepairAlternative.gone t).card) :
    let S := V\RawRepairAlternative.gone s
    let T := V\RawRepairAlternative.gone t
    let A := PairedFamilyLoop.previous s
    let B := PairedFamilyLoop.current s
    let C := PairedFamilyLoop.current t
    ∀ (e : ↥S ≃ ↥T) (f : ℕ→ℕ), (∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) →
      (∀i j : ↥S,E i j=E (e i) (e j)) → q<2*(RawRepairAlternative.gone t).card →
      Chain E (S\T) f → Disjoint (A∩B) (B∩C) ∧
      (2*(RawRepairAlternative.gone t).card=q+1 → A=FlatExchangeCycle.moved S T ∧
        ∀h∈V\A,(outN E A h)=∅ ∨ (inN E A h)=∅) := by
  obtain ⟨join,b,r,_,_,_,_,_,_,hit,_⟩ := mark
  have y := mem_inter.mp hit
  have yb := mem_sdiff.mp y.2
  dsimp only [RawRepairAlternative.gone]
  rw [join]
  intro e f fix iso large path
  exact overlap hq free ca cb ⟨_,mem_inter.mpr ⟨yb.1,y.1⟩,yb.2⟩
    (by simpa only [RawRepairAlternative.gone,join] using size) large e fix iso path

#print axioms overlap
#print axioms on_mark

end LeanCH.BR.Closure.FlatExchangeOverlap
