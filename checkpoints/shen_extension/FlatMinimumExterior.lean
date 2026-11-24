import checkpoints.shen_extension.FlatReturnLayers
import LeanCH.BR.BRWeightedOutUniformContraction

namespace LeanCH.BR.Closure.FlatMinimumExterior
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor MandatoryTwoStep
open FlatExchangeTriangle FlatExchangeChain FlatExchangeIntervals FlatPairedExcursion

private def Witnessed (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) :=
  ∀u∈V,∀v∈V,E u v=true → ∃N,Cycle E V q N ∧ u∈N ∧ v∈N

private def Sep (E : CH.Digraph) (V : Finset ℕ) :=
  ∀u∈V,∀v∈V,(∀w∈V,E w u=true → E w v=true) → u=v

private theorem sep_of_strict {q E V x} (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i) : Sep E V := by
  intro u uv v vv dom
  by_contra ne
  exact strict_no_incoming_domination (small.induced free) x xp strict uv vv ne
    (fun w wh => dom w (mem_of_mem_erase wh))

/-- Adjacent comparable cycle-incidence columns coincide. The two
directions use separation of columns and rows respectively. -/
private def ForcesIn (family : Finset ℕ→Prop) (u v : ℕ) := ∀N,family N → u∈N → v∈N

private theorem compare_arc {q E V} {family : Finset ℕ→Prop} (cycles : ∀N,family N → Cycle E V q N)
    (witness : ∀u∈V,∀v∈V,E u v=true → ∃N,family N ∧ u∈N ∧ v∈N) (cols : Sep E V)
    (rows : Sep (fun i j => E j i) V) {u v} (uv : u∈V) (vv : v∈V) (arc : E u v=true) :
    ForcesIn family u v ↔ ForcesIn family v u := by
  constructor
  · intro force
    have only (j) (jv : j∈V) (uj : E u j=true) : j=v := by
      obtain ⟨M,mf,um,jm⟩ := witness u uv j jv uj
      exact card_le_one.mp ((cycles M mf).heads u um).le _ (mem_outN.mpr ⟨jm,uj⟩) _ (mem_outN.mpr ⟨force M mf um,arc⟩)
    intro N nf vn
    have cn := cycles N nf
    obtain ⟨p,hp⟩ := card_pos.mp (show 0<(inN E N v).card by rw [show (inN E N v).card=1 from cn.incoming v vn]; decide)
    obtain ⟨pn,pv⟩ := mem_inN.mp hp
    have eq := rows u uv p (cn.sub pn) (fun j jv ej => (only j jv ej).symm ▸ pv)
    exact eq.symm ▸ pn
  · intro force
    have only (i) (iv : i∈V) (iv' : E i v=true) : i=u := by
      obtain ⟨M,mf,im,vm⟩ := witness i iv v vv iv'
      exact card_le_one.mp ((cycles M mf).incoming v vm).le _ (mem_inN.mpr ⟨im,iv'⟩) _ (mem_inN.mpr ⟨force M mf vm,arc⟩)
    intro N nf un
    have cn := cycles N nf
    obtain ⟨j,hj⟩ := card_pos.mp (show 0<(outN E N u).card by rw [cn.heads u un]; decide)
    obtain ⟨jn,uj⟩ := mem_outN.mp hj
    have eq := cols v vv j (cn.sub jn) (fun i iv e => (only i iv e).symm ▸ uj)
    exact eq.symm ▸ jn

private theorem chain_connected {E W f} (p : Chain E W f) : Connected E W := by
  intro label same u uw v vw
  have all (i) (hi : i<W.card) : label (f 0)=label (f i) := by
    induction i with
    | zero => rfl
    | succ i ih => exact (ih (by omega)).trans (same _ (p.mem (by omega)) _ (p.mem hi) ((p.edge _ (by omega) _ hi).mpr rfl))
  obtain ⟨i,hi,rfl⟩ := p.index uw
  obtain ⟨j,hj,rfl⟩ := p.index vw
  exact (all i hi).symm.trans (all j hj)

/-- A shared exterior label propagates along the exterior path of each
crossing cycle. Every exterior vertex ends up on every cycle through z. -/
private theorem propagate {q E V T z} {family : Finset ℕ→Prop} (cycles : ∀N,family N → Cycle E V q N)
    (witness : ∀u∈V,∀v∈V,E u v=true → ∃N,family N ∧ u∈N ∧ v∈N) (cols : Sep E V)
    (rows : Sep (fun i j => E j i) V) (zw : z∈V\T)
    (active : ∀i∈V,∃N,family N ∧ i∈N)
    (geometry : ∀N,family N → (N\T).Nonempty → z∈N ∧ Connected E (N\T)) :
    ∀i∈V\T,ForcesIn family z i := by
  classical
  intro i iw
  have toZ (u) (uw : u∈V\T) : ForcesIn family u z := fun N cn un =>
    (geometry N cn ⟨u,mem_sdiff.mpr ⟨un,(mem_sdiff.mp uw).2⟩⟩).1
  obtain ⟨N,nf,ni⟩ := active i (mem_sdiff.mp iw).1
  have cn := cycles N nf
  have il : i∈N\T := mem_sdiff.mpr ⟨ni,(mem_sdiff.mp iw).2⟩
  obtain ⟨zn,conn⟩ := geometry N nf ⟨i,il⟩
  let L := N\T
  have sub : L⊆V\T := fun _ h => mem_sdiff.mpr ⟨cn.sub (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩
  let label := fun u => decide (ForcesIn family z u)
  have same : ConstantOnArcs E L label := by
    intro u ul v vl arc
    have cmp := compare_arc cycles witness cols rows (cn.sub (mem_sdiff.mp ul).1) (cn.sub (mem_sdiff.mp vl).1) arc
    have uz := toZ u (sub ul)
    have vz := toZ v (sub vl)
    have iff : ForcesIn family z u ↔ ForcesIn family z v := by
      constructor
      · intro zu
        have vu : ForcesIn family v u := fun K ck vk => zu K ck (vz K ck vk)
        exact fun K ck zk => cmp.mpr vu K ck (zu K ck zk)
      · intro zv
        have uv : ForcesIn family u v := fun K ck uk => zv K ck (uz K ck uk)
        exact fun K ck zk => cmp.mp uv K ck (zv K ck zk)
    simp only [label,propext iff]
  have eq := conn label same z (mem_sdiff.mpr ⟨zn,(mem_sdiff.mp zw).2⟩) i il
  have id : ForcesIn family z z := fun _ _ h => h
  simpa [label,id] using eq

/-- A bank consisting of q mandatory labels on one path forces uniform
outgoing contacts from its complement. It cannot occur in a strict host. -/
private theorem serial_false {q E V T z f x} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (small : SmallerSmallRow q V.card) (tv : T⊆V) (large : 2≤T.card)
    (size : (V\T).card=q) (path : Chain E (V\T) f) (zw : z∈V\T)
    (witness : Witnessed q E V)
    (toZ : ∀N,Cycle E V q N → (N\T).Nonempty → z∈N)
    (all : ∀i∈V\T,Forces E V q z i)
    (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i) : False := by
  let W := V\T
  have n : W.card=q := size
  have mem (i) (hi : i<q) : f i∈W := path.mem (n.symm ▸ hi)
  have follow (i) (hi : i+1<q) (v) (vv : v∈V) (edge : E (f i) v=true) : v=f (i+1) := by
    have fu := mem i (by omega)
    have fv := mem (i+1) hi
    obtain ⟨N,cn,un,vn⟩ := witness _ (mem_sdiff.mp fu).1 v vv edge
    have zn := toZ N cn ⟨_,mem_sdiff.mpr ⟨un,(mem_sdiff.mp fu).2⟩⟩
    have next := (path.edge i (by omega) (i+1) (n.symm ▸ hi)).mpr rfl
    exact card_le_one.mp (cn.heads _ un).le _ (mem_outN.mpr ⟨vn,edge⟩) _ (mem_outN.mpr ⟨all _ fv N cn zn,next⟩)
  have forcedWalk {v k} (w : Walk E V (f 0) v k) (lim : k<q) : v=f k := by
    induction k generalizing v with
    | zero => cases w; rfl
    | succ k ih =>
      obtain ⟨u,pre,vv,edge⟩ := w.unsnoc
      rw [ih pre (by omega)] at edge
      exact follow k lim v vv edge
  have first (t) (tt : t∈T) : E t (f 0)=true := by
    by_contra no
    obtain ⟨_,k,le,w⟩ := mem_ball.mp (sat _ (mem_sdiff.mp (mem 0 (by omega))).1 t (tv tt) no)
    have eq := forcedWalk w (by omega)
    exact (mem_sdiff.mp (mem k (by omega))).2 (eq ▸ tt)
  have only (t) (tt : t∈T) (j) (jw : j∈W) (edge : E t j=true) : j=f 0 := by
    obtain ⟨i,hi,rfl⟩ := path.index jw
    cases i with
    | zero => rfl
    | succ i =>
      obtain ⟨N,cn,tn,jn⟩ := witness t (tv tt) _ (mem_sdiff.mp jw).1 edge
      have zn := toZ N cn ⟨_,mem_sdiff.mpr ⟨jn,(mem_sdiff.mp jw).2⟩⟩
      have p := mem i (by change i+1<W.card at hi; omega)
      have e := (path.edge i (by omega) (i+1) hi).mpr rfl
      have eq := card_le_one.mp (cn.incoming _ jn).le _ (mem_inN.mpr ⟨tn,edge⟩) _
        (mem_inN.mpr ⟨all _ p N cn zn,e⟩)
      exact ((mem_sdiff.mp p).2 (eq ▸ tt)).elim
  have uniform : BRsub.OutUniform E V T := by
    intro a at' b bt v vv vt
    have vw : v∈W := mem_sdiff.mpr ⟨vv,vt⟩
    by_cases eq : v=f 0
    · rw [eq,first a at',first b bt]
    · have off (u) (ut : u∈T) : E u v=false := Bool.eq_false_iff.mpr (fun e => eq (only u ut v vw e))
      rw [off a at',off b bt]
  have proper : T≠V := fun eq => (mem_sdiff.mp zw).2 (eq.symm ▸ (mem_sdiff.mp zw).1)
  obtain ⟨i,iv,low⟩ := smallRow_of_smaller_outUniform small free tv large proper uniform x xp
    ⟨z,(mem_sdiff.mp zw).1⟩
  exact (strict i iv).not_ge low

open FirstPacketBarrier MarkedCyclePeeling PairedFamilyLoop

/-- The smallest positive exterior multiple is impossible. The actual
strict source and the reverse strict source rule out incidence domination. -/
theorem minimum_false {q D V F A B C} (hq : 2≤q) (free : QFree (graph D F) V q)
    (small : SmallerSmallRow q V.card) (sat : BRsub.Sat q (graph D F) V)
    (cycles : ∀I∈F,Cycle (graph D F) V q I)
    (ca : Cycle (graph D F) V q A) (cb : Cycle (graph D F) V q B) (cc : Cycle (graph D F) V q C)
    (a : Packet (graph D F) V A B C) (b : Packet (graph D F) V B C A) (c : Packet (graph D F) V C A B)
    {x p : ℕ→ℚ} (xp : ∀u∈V,0≤x u) (pp : ∀u∈V,0≤p u)
    (strict : ∀u∈V,mass V x<WeightedSD.row q (graph D F) V x u)
    (costrict : ∀u∈V,mass V p<WeightedSD.col q (graph D F) V p u)
    (size : (V\(A∪B∪C)).card=q) : False := by
  classical
  let E := graph D F
  let T := A∪B∪C
  let W := V\T
  have tv : T⊆V := union_subset (union_subset ca.sub cb.sub) cc.sub
  have av : A⊆T := subset_union_left.trans subset_union_left
  have bv : B⊆T := subset_union_right.trans subset_union_left
  have cv : C⊆T := subset_union_right
  have wc : W.card=q := size
  have big : 2≤T.card := by have l := card_le_card av; rw [ca.size] at l; omega
  have witness : Witnessed q E V := by
    intro u uv v vv arc
    obtain ⟨N,nh⟩ := active.mp arc
    obtain ⟨nf,un,vn,_⟩ := mem_col.mp nh
    exact ⟨N,cycles _ nf,un,vn⟩
  have activeLabel (u) (uv : u∈V) : ∃N,Cycle E V q N ∧ u∈N := by
    have edge : (outN E V u).Nonempty := by
      by_contra! empty
      have high := strict u uv
      have lim : x u≤mass V x := single_le_sum xp uv
      change mass V x < WeightedSD.row q E V x u at high
      rw [WeightedSD.row,outW_eq_mass,empty] at high
      simp [mass] at high
      exact lim.not_gt high
    obtain ⟨v,vh⟩ := edge
    obtain ⟨N,cn,un,_⟩ := witness u uv v (mem_outN.mp vh).1 (mem_outN.mp vh).2
    exact ⟨N,cn,un⟩
  obtain ⟨z,zw,_,three⟩ := FlatReturnLayers.puncture free (by omega) ca cb cc a b c size
  have geometry (N) (cn : Cycle E V q N) (outside : (N\T).Nonempty) :
      z∈N ∧ ∃f,Chain E (N\T) f := by
    obtain ⟨u,un⟩ := outside
    have h := mem_sdiff.mp un
    have na : N≠A := fun eq => h.2 (av (eq ▸ h.1))
    have nb : N≠B := fun eq => h.2 (bv (eq ▸ h.1))
    have nc : N≠C := fun eq => h.2 (cv (eq ▸ h.1))
    have inT : (N∩T).Nonempty := by
      by_contra! no
      have sub : N⊆W := fun i hi => mem_sdiff.mpr ⟨cn.sub hi,fun it => notMem_empty i (no ▸ mem_inter.mpr ⟨hi,it⟩)⟩
      have l := card_le_card sub
      rw [cn.size,wc] at l
      omega
    have zn : z∈N := by
      by_contra no
      exact ((three N cn).mp no).elim na (fun h => h.elim nb nc)
    exact ⟨zn,((triple_overlap free ca cb cc a b c cn na nb nc).2.2 inT).1⟩
  have sep := sep_of_strict free small xp strict
  have rev : Sep (fun i j => E j i) V := sep_of_strict free.reverse small pp costrict
  have all := propagate (family:=Cycle E V q) (fun _ h => h) witness sep rev (show z∈W from zw) activeLabel
    (fun N cn extN => by obtain ⟨zn,f,h⟩ := geometry N cn extN; exact ⟨zn,chain_connected h⟩)
  obtain ⟨N,cn,zn⟩ := activeLabel z (mem_sdiff.mp zw).1
  obtain ⟨_,f,fp⟩ := geometry N cn ⟨z,mem_sdiff.mpr ⟨zn,(mem_sdiff.mp zw).2⟩⟩
  have eq : N\T=W := Subset.antisymm (fun _ h => mem_sdiff.mpr ⟨cn.sub (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩)
    (fun i iw => mem_sdiff.mpr ⟨all i iw N cn zn,(mem_sdiff.mp iw).2⟩)
  exact serial_false hq free sat small tv big size (eq ▸ fp) zw witness
    (fun I ci io => (geometry I ci io).1) all xp strict


private theorem cycle_connected {q E V N} (hq : 1≤q) (free : QFree E V q) (cn : Cycle E V q N) :
    Connected E N := by
  intro label same u un v vn
  obtain ⟨_,_,w,_⟩ := MandatoryExcursion.segments hq free cn un vn
  have along {i j k} (path : Walk E N i j k) (im : i∈N) : label i=label j := by
    induction path with
    | refl => rfl
    | step jt arc _ ih => exact (same _ im _ jt arc).trans (ih jt)
  exact along w un

/-- Beyond the minimum, every proposed exterior pivot is avoided by
another selected cycle which uses exterior vertices. A singleton return
cut therefore produces a selected cycle wholly in the smaller exterior. -/
theorem avoid_selected {q D V F A B C} (hq : 2≤q) (free : QFree (graph D F) V q)
    (small : SmallerSmallRow q V.card) (cycles : ∀I∈F,Cycle (graph D F) V q I)
    (ca : Cycle (graph D F) V q A) (cb : Cycle (graph D F) V q B) (cc : Cycle (graph D F) V q C)
    (a : Packet (graph D F) V A B C) (b : Packet (graph D F) V B C A) (c : Packet (graph D F) V C A B)
    {x p : ℕ→ℚ} (xp : ∀u∈V,0≤x u) (pp : ∀u∈V,0≤p u)
    (strict : ∀u∈V,mass V x<WeightedSD.row q (graph D F) V x u)
    (costrict : ∀u∈V,mass V p<WeightedSD.col q (graph D F) V p u)
    (space : q<(V\(A∪B∪C)).card) {M} (mf : M∈F) (inside : (M∩(A∪B∪C)).Nonempty)
    (outside : (M\(A∪B∪C)).Nonempty) :
    let T := A∪B∪C
    ∀z∈V\T,∃N∈F,(N\T).Nonempty ∧ z∉N ∧
      (FlatReturnLayers.Cuts (graph D F) V T {z} → N⊆(V\T).erase z) := by
  classical
  intro T z zw
  let E := graph D F
  let W := V\T
  have wit (u) (_ : u∈V) (v) (_ : v∈V) (uv : E u v=true) : ∃N∈F,u∈N ∧ v∈N := by
    obtain ⟨N,nh⟩ := active.mp uv
    obtain ⟨nf,un,vn,_⟩ := mem_col.mp nh
    exact ⟨N,nf,un,vn⟩
  have act (u) (uv : u∈V) : ∃N∈F,u∈N := by
    have edge : (outN E V u).Nonempty := by
      by_contra! empty
      have hi := strict u uv
      change mass V x < WeightedSD.row q E V x u at hi
      rw [WeightedSD.row,outW_eq_mass,empty] at hi
      simp [mass] at hi
      exact (single_le_sum xp uv : x u≤mass V x).not_gt hi
    obtain ⟨v,vh⟩ := edge
    obtain ⟨N,nf,un,_⟩ := wit _ uv _ (mem_outN.mp vh).1 (mem_outN.mp vh).2
    exact ⟨N,nf,un⟩
  have find : ∃N∈F,(N\T).Nonempty ∧ z∉N := by
    by_contra! blocked
    have geom (N) (nf : N∈F) (extN : (N\T).Nonempty) : z∈N ∧ Connected E (N\T) := by
      refine ⟨blocked N nf extN,?_⟩
      by_cases inn : (N∩T).Nonempty
      · obtain ⟨v,vh⟩ := extN
        have nv := mem_sdiff.mp vh
        have av : A⊆T := subset_union_left.trans subset_union_left
        have bv : B⊆T := subset_union_right.trans subset_union_left
        have cv : C⊆T := subset_union_right
        obtain ⟨f,path⟩ := ((triple_overlap free ca cb cc a b c (cycles _ nf)
          (fun eq => nv.2 (av (eq ▸ nv.1))) (fun eq => nv.2 (bv (eq ▸ nv.1)))
          (fun eq => nv.2 (cv (eq ▸ nv.1)))).2.2 inn).1
        exact chain_connected path
      · have eq : N\T=N := by
          ext i; simp only [mem_sdiff]; exact ⟨And.left,fun h => ⟨h,fun it => inn ⟨i,mem_inter.mpr ⟨h,it⟩⟩⟩⟩
        exact eq.symm ▸ cycle_connected (by omega) free (cycles _ nf)
    have all := propagate (family:=(·∈F)) cycles wit (sep_of_strict free small xp strict)
      (sep_of_strict free.reverse small pp costrict) (show z∈W from zw) act geom
    have wm : W⊆M\T := fun v vh => mem_sdiff.mpr ⟨all v vh M mf (blocked M mf outside),(mem_sdiff.mp vh).2⟩
    have lb := card_le_card wm
    have split := card_sdiff_add_card_inter M T
    rw [(cycles _ mf).size] at split
    have pos := card_pos.mpr inside
    change 0<(M∩T).card at pos
    change q<W.card at space
    omega
  obtain ⟨N,nf,extN,no⟩ := find
  refine ⟨N,nf,extN,no,?_⟩
  intro cut i ni
  refine mem_erase.mpr ⟨fun eq => no (eq ▸ ni),mem_sdiff.mpr ⟨(cycles _ nf).sub ni,?_⟩⟩
  intro it
  obtain ⟨h,hh⟩ := FlatReturnLayers.hits free (cycles _ nf) cut ⟨i,mem_inter.mpr ⟨ni,it⟩⟩ extN
  exact no ((mem_singleton.mp (mem_inter.mp hh).2) ▸ (mem_inter.mp hh).1)

#print axioms avoid_selected

theorem on_schedule {q D V F} (hq : 2≤q) (free : QFree (graph D F) V q)
    (small : SmallerSmallRow q V.card) (cycles : ∀I∈F,Cycle (graph D F) V q I)
    (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (join : ∀s,previous (go s)=current s)
    (mark : ∀s,Marked (graph D F) (previous s) (current s) (current (go s)))
    (flat : ∀a : Function.periodicPts go,BRsub.Sat q (graph D F) (V\RawRepairAlternative.gone a.val))
    {x p : ℕ→ℚ} (xp : ∀u∈V,0<x u) (pp : ∀u∈V,0≤p u)
    (strict : ∀u∈V,mass V x<WeightedSD.row q (graph D F) V x u)
    (costrict : ∀u∈V,mass V p<WeightedSD.col q (graph D F) V p u)
    (s : Function.periodicPts go) :
    let E := graph D F
    let A := previous s.val
    let B := current s.val
    let C := current (go s.val)
    let T := A∪B∪C
    ((V\RawRepairAlternative.gone s.val).card : ZMod q)=1 →
    Packet E V A B C →
    Packet E V (previous (go s.val)) C (current (go (go s.val))) →
    Packet E V (previous (go (go s.val))) (current (go (go s.val))) (current (go (go (go s.val)))) →
    (∃k,2≤k ∧ (V\T).card=q*k) ∧
      ∀z∈V\T,∃N∈F,(N\T).Nonempty ∧ z∉N ∧
        (FlatReturnLayers.Cuts E V T {z} → N⊆(V\T).erase z) := by
  intro E A B C T modOne a b c
  have lp (z : PairedFamilyLoop.State F) := (mem_product.mp (mem_filter.mp z.property).1).1
  have rp (z : PairedFamilyLoop.State F) := (mem_product.mp (mem_filter.mp z.property).1).2
  have left (z : PairedFamilyLoop.State F) := cycles _ (lp z)
  have right (z : PairedFamilyLoop.State F) := cycles _ (rp z)
  have period := period_three free go left right join mark s.val a b c
  have odd : ¬Even (Function.minimalPeriod go s.val) := by rw [period]; decide
  have sat := FlatOrbitSaturation.odd_saturated go join flat s odd
  obtain ⟨⟨k,eq⟩,pos,M,mf,_,_,_,ins,far,_⟩ := FlatPairedExcursion.on_schedule hq free small cycles xp strict go join mark s.val modOne a b c
  have ret (t : PairedFamilyLoop.State F) := scheduled_return free (left t) (right t) (right (go t))
    (right (go (go t))) (join t) (mark t) (mark (go t))
  have d := ret s.val a b
  have e := ret (go s.val) b c
  have live := card_pos.mpr a.live
  dsimp only [A,B,C,E] at a b c
  rw [join s.val,d] at b
  rw [join (go s.val),d,e,join s.val] at c
  change (V\T).card=q*k at eq
  change q≤(V\T).card at pos
  have two : 2≤k := by
    by_contra! short
    rcases (show k=0 ∨ k=1 by omega) with zero|one
    · rw [zero,Nat.mul_zero] at eq
      omega
    · rw [one,Nat.mul_one] at eq
      exact minimum_false hq free small sat cycles (left s.val) (right s.val) (right (go s.val)) a b c
        (fun i hi => (xp i hi).le) pp strict costrict eq
  have space : q<(V\T).card := by have v := Nat.mul_le_mul_left q two; omega
  exact ⟨⟨k,two,eq⟩,avoid_selected hq free small cycles (left s.val) (right s.val) (right (go s.val))
    a b c (fun i hi => (xp i hi).le) pp strict costrict space mf ins (card_pos.mp (live.trans_le far))⟩

#print axioms minimum_false
#print axioms on_schedule

end LeanCH.BR.Closure.FlatMinimumExterior

