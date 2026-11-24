import checkpoints.shen_extension.FlatOrbitSaturation

namespace LeanCH.BR.Closure.FlatPairedExcursion
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor FlatExchangeChain FlatExchangeTriangle

private theorem forward {E L f i j} (path : Chain E L f) (ij : i≤j) (jm : j<L.card) :
    Walk E L (f i) (f j) (j-i) := by
  apply walk_between (m:=j) _ ij le_rfl
  intro k hk
  exact ⟨path.mem (by omega),(path.edge k (by omega) _ (by omega)).mpr rfl⟩

/-- The last vertex of either half has the first vertex of the other as its only cycle head. -/
private theorem bridge {q E V A P Q f g} (cy : Cycle E V q A) (cover : P∪Q=A)
    (dis : Disjoint P Q) (live : P.Nonempty) (pos : Q.Nonempty) (p : Chain E P f) (r : Chain E Q g) :
    E (f (P.card-1)) (g 0)=true := by
  have pv := card_pos.mpr live
  have qv := card_pos.mpr pos
  have endP := p.mem (show P.card-1<P.card by omega)
  have pa : P⊆A := cover ▸ subset_union_left
  have qa : Q⊆A := cover ▸ subset_union_right
  obtain ⟨y,hy⟩ := card_pos.mp (show 0<(outN E A (f (P.card-1))).card by rw [cy.heads _ (pa endP)]; decide)
  obtain ⟨ya,fy⟩ := mem_outN.mp hy
  have ynp : y∉P := by
    intro h
    obtain ⟨j,hj,rfl⟩ := p.index h
    have := (p.edge _ (by omega) j hj).mp fy
    omega
  have yq : y∈Q := (mem_union.mp (cover.symm ▸ ya)).resolve_left ynp
  obtain ⟨j,hj,rfl⟩ := r.index yq
  cases j with
  | zero => exact fy
  | succ j =>
    have gj := r.mem (show j<Q.card by omega)
    have edge := (r.edge j (by omega) (j+1) hj).mpr rfl
    have eq := card_le_one.mp (cy.incoming _ ya).le _ (mem_inN.mpr ⟨pa endP,fy⟩) _ (mem_inN.mpr ⟨qa gj,edge⟩)
    exact (disjoint_left.mp dis endP (eq.symm ▸ gj)).elim

private theorem align {E V P Q f g} (copy : Copy E V P Q) (p : Chain E P f) (r : Chain E Q g)
    (i) (hi : i<P.card) : (copy.equiv ⟨f i,p.mem hi⟩ : ℕ)=g i := by
  have count : P.card=Q.card := by simpa only [Fintype.card_coe] using Fintype.card_congr copy.equiv
  induction i with
  | zero =>
    let x : ↥P := ⟨f 0,p.mem hi⟩
    obtain ⟨j,hj,eq⟩ := r.index (copy.equiv x).property
    cases j with
    | zero => exact eq.symm
    | succ j =>
      let y : ↥Q := ⟨g j,r.mem (by omega)⟩
      have edge : E y (copy.equiv x)=true := by rw [←eq]; exact (r.edge j (by omega) _ hj).mpr rfl
      have pre := copy.arcs (copy.equiv.symm y) x
      rw [copy.equiv.apply_symm_apply,edge] at pre
      obtain ⟨k,hk,m⟩ := p.index (copy.equiv.symm y).property
      change E (copy.equiv.symm y) (f 0)=true at pre
      rw [←m] at pre
      have := (p.edge k hk 0 hi).mp pre
      omega
  | succ i ih =>
    have n := (p.edge i (by omega) (i+1) hi).mpr rfl
    have a := copy.arcs ⟨f i,p.mem (by omega)⟩ ⟨f (i+1),p.mem hi⟩
    change E (f i) (f (i+1))=_ at a
    rw [n,ih (by omega)] at a
    obtain ⟨j,hj,m⟩ := r.index (copy.equiv ⟨f (i+1),p.mem hi⟩).property
    rw [←m] at a
    have eq := (r.edge i (by omega) j hj).mp a.symm
    exact m.symm.trans (congrArg g eq)

private theorem reach_exit {E V P Q f g i j w} (pv : P⊆V) (qv : Q⊆V)
    (p : Chain E P f) (r : Chain E Q g) (count : P.card=Q.card)
    (cross : E (f (P.card-1)) (g 0)=true) (hit : E (f i) w=true) (hit' : E (g i) w=true)
    (wv : w∈V) (im : i<P.card) (jm : j<P.card) : ∃l≤P.card,Walk E V (f j) w l := by
  by_cases order : j ≤ i
  · exact ⟨_,by omega,((forward p order im).mono pv).snoc wv hit⟩
  · have one := ((forward p (show j≤P.card-1 by omega) (by omega)).mono pv).snoc (qv (r.mem (show 0<Q.card by omega))) cross
    have two := ((forward r (Nat.zero_le i) (show i<Q.card by omega)).mono qv).snoc wv hit'
    exact ⟨_,by omega,one.append two⟩

/-- If a vertex outside the paired cycle receives one arc from it, every
vertex of that cycle reaches it in at most half a turn. Any return to the
cycle therefore takes at least half a turn. -/
theorem packet_exit {q E V A B C w v k} (free : QFree E V q) (ca : Cycle E V q A)
    (pac : Packet E V A B C) (wv : w∈V\A) (hit : (inN E A w).Nonempty)
    (va : v∈A) (returnPath : Walk E V w v k) :
    (B\C).card≤k := by
  let P := B\C
  let Q := A\B
  have cover : P∪Q=A := by
    change (B\C)∪(A\B)=A
    rw [←pac.overlap]
    ext i; simp only [mem_union,mem_sdiff,mem_inter]; tauto
  have separate : Disjoint P Q := by
    apply disjoint_left.mpr
    intro i ip iq
    exact (mem_sdiff.mp iq).2 (mem_sdiff.mp ip).1
  have pv : P⊆V := (show P⊆A from cover ▸ subset_union_left).trans ca.sub
  have qv : Q⊆V := (show Q⊆A from cover ▸ subset_union_right).trans ca.sub
  obtain ⟨copy⟩ := pac.copy
  obtain ⟨f,p⟩ := pac.leftPath
  obtain ⟨g,r⟩ := pac.rightPath
  have cnt : P.card=Q.card := by simpa only [Fintype.card_coe] using Fintype.card_congr copy.equiv
  have pos := card_pos.mpr pac.live
  have liveQ : Q.Nonempty := card_pos.mp (by change 0<P.card at pos; omega)
  have pq := bridge ca cover separate pac.live liveQ p r
  have qp := bridge ca ((union_comm Q P).trans cover) separate.symm liveQ pac.live r p
  have len := card_union_of_disjoint separate
  rw [cover,ca.size,←cnt] at len
  have both (i) (hi : i<P.card) : E (f i) w=E (g i) w := by
    have z := (copy.contacts w (show w∈V\(P∪Q) from cover.symm ▸ wv) ⟨f i,p.mem hi⟩).2
    rw [align copy p r i hi] at z
    exact z
  obtain ⟨u,uh⟩ := hit
  obtain ⟨ua,e⟩ := mem_inN.mp uh
  have index : ∃i<P.card,E (f i) w=true ∧ E (g i) w=true := by
    rcases mem_union.mp (cover.symm ▸ ua) with h|h
    · obtain ⟨i,hi,rfl⟩ := p.index h
      exact ⟨i,hi,e,(both i hi).symm.trans e⟩
    · obtain ⟨i,hi,rfl⟩ := r.index h
      change i<Q.card at hi
      exact ⟨i,by omega,(both i (by omega)).trans e,e⟩
  obtain ⟨i,hi,hf,hg⟩ := index
  have back : ∃l≤P.card,Walk E V v w l := by
    rcases mem_union.mp (cover.symm ▸ va) with h|h
    · obtain ⟨j,hj,rfl⟩ := p.index h
      exact reach_exit pv qv p r cnt pq hf hg (mem_sdiff.mp wv).1 hi hj
    · obtain ⟨j,hj,rfl⟩ := r.index h
      simpa only [cnt] using reach_exit qv pv r p cnt.symm qp hg hf (mem_sdiff.mp wv).1 (by omega) hj
  obtain ⟨l,le,path⟩ := back
  have ne : v≠w := fun eq => (mem_sdiff.mp wv).2 (eq ▸ va)
  have lp : 0<l := by cases path with | refl => contradiction | step => omega
  have ban := free v (l+k) (by omega)
  have bound : q<l+k := by by_contra! no; exact ban no (path.append returnPath)
  change P.card≤k
  omega

#print axioms packet_exit

open FlatExchangeIntervals

/-- Any set with the return bound admits at most one exterior interval
on a shortest cycle of length at most twice that bound. -/
theorem outside_interval {q E V U N m} (free : QFree E V q) (cn : Cycle E V q N)
    (twice : q+1≤2*m)
    (barrier : ∀w∈V\U,(inN E U w).Nonempty → ∀v∈U,∀k,Walk E V w v k → m≤k)
    (inside : (N∩U).Nonempty) (outside : (N\U).Nonempty) :
    m≤(N\U).card ∧ (∃f,Chain E (N\U) f) ∧ ∃g,Chain E (N∩U) g := by
  classical
  let L := N\U
  have sub : L⊆N := sdiff_subset
  have lv := sub.trans cn.sub
  have size := card_sdiff_add_card_inter N U
  change L.card+(N∩U).card=N.card at size
  have pos := card_pos.mpr inside
  have cap : L.card≤q := by rw [cn.size] at size; omega
  have color (label : ℕ→Bool) (same : ConstantOnArcs E L label) (a : ℕ) (al : a∈L) :
      m≤(L.filter (fun z => label z=label a)).card := by
    let Z := L.filter (fun z => label z=label a)
    have zs : Z⊆L := filter_subset _ _
    have zv := zs.trans lv
    have zc := (card_le_card zs).trans cap
    have za : a∈Z := mem_filter.mpr ⟨al,rfl⟩
    obtain ⟨w,wz,first⟩ := exists_sink ((free.mono_set zv).reverse) ⟨a,za⟩ zc
    have wn := sub (zs wz)
    obtain ⟨p,par⟩ := card_pos.mp (show 0<(inN E N w).card by rw [show (inN E N w).card=1 from cn.incoming w wn]; decide)
    obtain ⟨pn,pw⟩ := mem_inN.mp par
    have pu : p∈U := by
      by_contra no
      have pl : p∈L := mem_sdiff.mpr ⟨pn,no⟩
      exact first p (mem_filter.mpr ⟨pl,(same p pl w (zs wz) pw).trans (mem_filter.mp wz).2⟩) pw
    obtain ⟨b,bz,last,k,hk,path⟩ := reach_sink_of_card (free.mono_set zv) zc wz
    obtain ⟨v,next⟩ := card_pos.mp (show 0<(outN E N b).card by rw [cn.heads b (sub (zs bz))]; decide)
    obtain ⟨vn,bv⟩ := mem_outN.mp next
    have vu : v∈U := by
      by_contra no
      have vl : v∈L := mem_sdiff.mpr ⟨vn,no⟩
      exact last v (mem_filter.mpr ⟨vl,(same b (zs bz) v vl bv).symm.trans (mem_filter.mp bz).2⟩) bv
    have low := barrier w (mem_sdiff.mpr ⟨zv wz,(mem_sdiff.mp (zs wz)).2⟩)
      ⟨p,mem_inN.mpr ⟨pu,pw⟩⟩ v vu (k+1) ((path.mono zv).snoc (cn.sub vn) bv)
    change m≤Z.card
    omega
  obtain ⟨a,al⟩ := outside
  have all := color (fun _ => true) (by intro i hi j hj e; rfl) a al
  simp at all
  have conn : Connected E L := by
    intro label same u hu v hv
    by_contra diff
    let X := L.filter (fun z => label z=label u)
    let Y := L.filter (fun z => label z=label v)
    have ux : m≤X.card := color label same u hu
    have vy : m≤Y.card := color label same v hv
    have dis : Disjoint X Y := disjoint_left.mpr (fun _ x y => diff ((mem_filter.mp x).2.symm.trans (mem_filter.mp y).2))
    have lim := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _) : X∪Y⊆L)
    rw [card_union_of_disjoint dis] at lim
    omega
  obtain ⟨f,fp⟩ := chain_of_connected free cn sub cap ⟨a,al⟩ conn
  have c := FlatExchangeOverlap.complement_connected free cn sub ⟨a,al⟩ fp
  have comp : N\L=N∩U := by ext i; simp only [L,mem_inter,mem_sdiff]; tauto
  rw [comp] at c
  have other := card_pos.mpr (show L.Nonempty from ⟨a,al⟩)
  rw [cn.size] at size
  exact ⟨all,⟨f,fp⟩,chain_of_connected free cn inter_subset_left (by omega) inside c⟩

theorem packet_overlap {q E V A B C N} (free : QFree E V q) (ca : Cycle E V q A)
    (pac : Packet E V A B C) (cn : Cycle E V q N) (diff : N≠A) :
    (N∩A).card≤(B\C).card ∧ ((N∩A).Nonempty →
      (∃f,Chain E (N\A) f) ∧ ∃g,Chain E (N∩A) g) := by
  classical
  obtain ⟨e⟩ := pac.copy
  have count : (B\C).card=(A\B).card := by simpa only [Fintype.card_coe] using Fintype.card_congr e.equiv
  have size := card_sdiff_add_card_inter A B
  rw [pac.overlap,ca.size,←count] at size
  by_cases inside : (N∩A).Nonempty
  · have outside : (N\A).Nonempty := by
      by_contra! empty
      exact diff (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.mp empty) (by rw [ca.size,cn.size]))
    obtain ⟨lim,extp,intp⟩ := outside_interval free cn (m:=(B\C).card) (by omega)
      (fun _ wh hit _ vh _ path => packet_exit free ca pac wh hit vh path) inside outside
    have split := card_sdiff_add_card_inter N A
    rw [cn.size] at split
    exact ⟨by omega,fun _ => ⟨extp,intp⟩⟩
  · simp_all

#print axioms outside_interval
#print axioms packet_overlap

theorem triple_exit {q E V A B C} (free : QFree E V q)
    (ca : Cycle E V q A) (cb : Cycle E V q B) (cc : Cycle E V q C)
    (a : Packet E V A B C) (b : Packet E V B C A) (c : Packet E V C A B) :
    let T := A∪B∪C
    ∀w∈V\T,(inN E T w).Nonempty → ∀v∈T,∀k,Walk E V w v k → (B\C).card≤k := by
  classical
  intro T
  have size {I J K} (cy : Cycle E V q I) (h : Packet E V I J K) : 2*(J\K).card=q+1 := by
    obtain ⟨e⟩ := h.copy
    have cnt : (J\K).card=(I\J).card := by simpa only [Fintype.card_coe] using Fintype.card_congr e.equiv
    have x := card_sdiff_add_card_inter I J
    rw [cy.size,h.overlap,←cnt] at x
    omega
  have aa := size ca a
  have bb := size cb b
  have ccc := size cc c
  have role (v) (vt : v∈T) : (v∈A ∧ v∈B) ∨ (v∈B ∧ v∈C) ∨ (v∈C ∧ v∈A) := by
    have e (I J K : Finset ℕ) (eq : I∩J=J\K) : v∈I∩J ↔ v∈J\K := eq ▸ Iff.rfl
    have p := e _ _ _ a.overlap
    have r := e _ _ _ b.overlap
    have s := e _ _ _ c.overlap
    simp only [T,mem_union,mem_inter,mem_sdiff] at p r s vt
    tauto
  have bound (w) (wv : w∈V\T) (incoming : (inN E T w).Nonempty) (v) (vt : v∈T) (k) (path : Walk E V w v k) :
      (B\C).card≤k := by
    obtain ⟨u,uh⟩ := incoming
    obtain ⟨ut,hit⟩ := mem_inN.mp uh
    have pair : (u∈A ∧ v∈A) ∨ (u∈B ∧ v∈B) ∨ (u∈C ∧ v∈C) := by
      have := role u ut
      have rv := role v vt
      tauto
    have ws := mem_sdiff.mp wv
    simp only [T,mem_union] at ws
    rcases pair with h|h|h
    · exact packet_exit free ca a (mem_sdiff.mpr ⟨ws.1,by tauto⟩) ⟨u,mem_inN.mpr ⟨h.1,hit⟩⟩ h.2 path
    · have l := packet_exit free cb b (mem_sdiff.mpr ⟨ws.1,by tauto⟩) ⟨u,mem_inN.mpr ⟨h.1,hit⟩⟩ h.2 path
      omega
    · have l := packet_exit free cc c (mem_sdiff.mpr ⟨ws.1,by tauto⟩) ⟨u,mem_inN.mpr ⟨h.1,hit⟩⟩ h.2 path
      omega
  exact bound

/-- All three paired cycles together have the same excursion bound. Every
fourth shortest cycle uses at least half of its vertices outside their union,
and its visit to the union is one interval. -/
theorem triple_overlap {q E V A B C N} (free : QFree E V q)
    (ca : Cycle E V q A) (cb : Cycle E V q B) (cc : Cycle E V q C)
    (a : Packet E V A B C) (b : Packet E V B C A) (c : Packet E V C A B)
    (cn : Cycle E V q N) (na : N≠A) (nb : N≠B) (nc : N≠C) :
    let T := A∪B∪C
    (B\C).card≤(N\T).card ∧ (N∩T).card≤(B\C).card ∧
      ((N∩T).Nonempty → (∃f,Chain E (N\T) f) ∧ ∃g,Chain E (N∩T) g) := by
  classical
  intro T
  have size {I J K} (cy : Cycle E V q I) (h : Packet E V I J K) : 2*(J\K).card=q+1 := by
    obtain ⟨e⟩ := h.copy
    have cnt : (J\K).card=(I\J).card := by simpa only [Fintype.card_coe] using Fintype.card_congr e.equiv
    have x := card_sdiff_add_card_inter I J
    rw [cy.size,h.overlap,←cnt] at x
    omega
  have aa := size ca a
  have bb := size cb b
  have ccc := size cc c
  have role (v) (vt : v∈T) : (v∈A ∧ v∈B) ∨ (v∈B ∧ v∈C) ∨ (v∈C ∧ v∈A) := by
    have e (I J K : Finset ℕ) (eq : I∩J=J\K) : v∈I∩J ↔ v∈J\K := eq ▸ Iff.rfl
    have p := e _ _ _ a.overlap
    have r := e _ _ _ b.overlap
    have s := e _ _ _ c.overlap
    simp only [T,mem_union,mem_inter,mem_sdiff] at p r s vt
    tauto
  by_cases inside : (N∩T).Nonempty
  · have extN : (N\T).Nonempty := by
      by_contra! empty
      have nt := sdiff_eq_empty_iff_subset.mp empty
      have pa := (packet_overlap free ca a cn na).1
      have pb := (packet_overlap free cb b cn nb).1
      have pc := (packet_overlap free cc c cn nc).1
      have ac := card_sdiff_add_card_inter N A
      have bc := card_sdiff_add_card_inter N B
      have kc := card_sdiff_add_card_inter N C
      rw [cn.size] at ac bc kc
      have ab : Disjoint (N\A) (N\B) := by
        intro x ha hb v hv
        have ia := mem_sdiff.mp (ha hv)
        have ib := mem_sdiff.mp (hb hv)
        have := role v (nt ia.1)
        tauto
      have abc : Disjoint ((N\A)∪(N\B)) (N\C) := by
        apply disjoint_left.mpr
        intro v h vc
        have e := mem_sdiff.mp vc
        have := role v (nt e.1)
        simp only [mem_union,mem_sdiff] at h
        tauto
      have cap := card_le_card (union_subset (union_subset sdiff_subset sdiff_subset) sdiff_subset :
        ((N\A)∪(N\B))∪(N\C) ⊆ N)
      rw [card_union_of_disjoint abc,card_union_of_disjoint ab,cn.size] at cap
      omega
    have bound := triple_exit free ca cb cc a b c
    obtain ⟨low,ex,ins⟩ := outside_interval (U:=T) free cn aa.ge bound inside extN
    have split := card_sdiff_add_card_inter N T
    rw [cn.size] at split
    exact ⟨low,by omega,fun _ => ⟨ex,ins⟩⟩
  · have split := card_sdiff_add_card_inter N T
    rw [not_nonempty_iff_eq_empty.mp inside,card_empty,cn.size] at split
    exact ⟨by omega,by simp [not_nonempty_iff_eq_empty.mp inside],fun h => (inside h).elim⟩

#print axioms triple_overlap

open WeightedSD

private theorem internal_scores {q E V A B P Q H f g h} (ca : Cycle E V q A) (cb : Cycle E V q B)
    (a : P∪Q=A) (b : P∪H=B) (all : A∪B=V) (pq : Disjoint P Q) (ph : Disjoint P H)
    (qh : Disjoint Q H) (pn : P.Nonempty) (qn : Q.Nonempty) (hn : H.Nonempty)
    (p : Chain E P f) (r : Chain E Q g) (s : Chain E H h)
    (x : ℕ→ℚ) (strict : ∀u∈V,mass V x<WeightedSD.row q E V x u) :
    (∀i,i+1<P.card → mass V x<x (f i)+q*x (f (i+1))) ∧
      mass V x<x (f (P.card-1))+q*(x (g 0)+x (h 0)) := by
  classical
  have av : A⊆V := all ▸ subset_union_left
  have bv : B⊆V := all ▸ subset_union_right
  have pa : P⊆A := a ▸ subset_union_left
  have pb : P⊆B := b ▸ subset_union_left
  have qa : Q⊆A := a ▸ subset_union_right
  have hb : H⊆B := b ▸ subset_union_right
  have unique {C u v w} (cy : Cycle E V q C) (uc : u∈C) (vc : v∈C) (wc : w∈C)
      (uv : E u v=true) (uw : E u w=true) : v=w :=
    card_le_one.mp (cy.heads u uc).le _ (mem_outN.mpr ⟨vc,uv⟩) _ (mem_outN.mpr ⟨wc,uw⟩)
  have form (u) : WeightedSD.row q E V x u=x u+q*(∑i∈outN E V u,x i) := by
    simp only [WeightedSD.row,WeightedSD.outW,outN,sum_filter]
  constructor
  · intro i hi
    have iu := p.mem (show i<P.card by omega)
    have jv := p.mem hi
    have edge := (p.edge i (by omega) (i+1) hi).mpr rfl
    have eq : outN E V (f i)={f (i+1)} := by
      ext w
      simp only [mem_outN,mem_singleton]
      constructor
      · rintro ⟨wv,uw⟩
        rcases mem_union.mp (all.symm ▸ wv) with ha|hc
        · exact unique ca (pa iu) ha (pa jv) uw edge
        · exact unique cb (pb iu) hc (pb jv) uw edge
      · rintro rfl
        exact ⟨av (pa jv),edge⟩
    simpa only [form,eq,sum_singleton] using strict (f i) (av (pa iu))
  · have n := card_pos.mpr pn
    have iu := p.mem (show P.card-1<P.card by omega)
    have gq := r.mem (card_pos.mpr qn)
    have hh := s.mem (card_pos.mpr hn)
    have fg := bridge ca a pq pn qn p r
    have fh := bridge cb b ph pn hn p s
    have neq : g 0≠h 0 := fun eq => disjoint_left.mp qh gq (eq.symm ▸ hh)
    have eq : outN E V (f (P.card-1))={g 0,h 0} := by
      ext w
      simp only [mem_outN,mem_insert,mem_singleton]
      constructor
      · rintro ⟨wv,uw⟩
        rcases mem_union.mp (all.symm ▸ wv) with ha|hc
        · exact Or.inl (unique ca (pa iu) ha (qa gq) uw fg)
        · exact Or.inr (unique cb (pb iu) hc (hb hh) uw fh)
      · rintro (rfl|rfl)
        · exact ⟨av (qa gq),fg⟩
        · exact ⟨bv (hb hh),fh⟩
    simpa [form,eq,neq] using strict (f (P.card-1)) (av (pa iu))

private theorem sum_chain {E L f} (p : Chain E L f) (x : ℕ→ℚ) :
    (∑i∈range L.card,x (f i))=mass L x := by
  change _=∑u∈L,x u
  conv_rhs => rw [←p.span,sum_image p.injective]

private theorem scores_false {q m : ℕ} (large : 2≤q) (sz : 2*m=q+1)
    {W : ℕ→ℚ} {M : ℚ} (positive : 0<M) (wn : ∀i<m,0≤W i) (tot : (∑i∈range m,W i)=M)
    (inner : ∀i,i+1<m → 3*M<W i+q*W (i+1))
    (last : 3*M<W (m-1)+2*q*W 0) : False := by
  have mp : 0<m := by omega
  let k := m-1
  have km : k+1=m := by dsimp [k]; omega
  have before := sum_le_sum (s:=range k) (f:=fun _ => 3*M) (g:=fun i => W i+q*W (i+1))
    (fun i hi => (inner i (by have := mem_range.mp hi; omega)).le)
  simp only [sum_const,card_range,nsmul_eq_mul,sum_add_distrib,←mul_sum] at before
  have atLast := sum_range_succ W k
  have atFirst := sum_range_succ' W k
  rw [km,tot] at atLast atFirst
  have ls : 3*M<W k+2*q*W 0 := last
  have nat : 2*k+1=q := by omega
  have alg : 2*(k:ℚ)+1=q := by exact_mod_cast nat
  have qv : 2≤(q:ℚ) := by exact_mod_cast large
  have nonneg := wn k (by omega)
  rw [show (q:ℚ)=2*k+1 from alg.symm] at ls before qv
  nlinarith [mul_nonneg (show (0:ℚ)≤(2*k+1)-2 by linarith) positive.le,
    congrArg (fun t : ℚ => (2*k+1)*t) atFirst]

/-- A strict parent cannot consist of the three paths alone. This is a
weighted statement with no degree or ambient-order restriction. -/
theorem exterior_exists {q E V A B C} (hq : 2≤q) (ca : Cycle E V q A)
    (cb : Cycle E V q B) (cc : Cycle E V q C) (a : Packet E V A B C)
    (b : Packet E V B C A) (c : Packet E V C A B) {x : ℕ→ℚ}
    (xp : ∀v∈V,0<x v) (strict : ∀u∈V,mass V x<WeightedSD.row q E V x u) :
    (V\(A∪B∪C)).Nonempty := by
  classical
  by_contra! empty
  let P := B\C
  let Q := A\B
  let H := C\A
  have ca' : P∪Q=A := by change (B\C)∪(A\B)=A; rw [←a.overlap]; ext; simp only [mem_union,mem_inter,mem_sdiff]; tauto
  have cb' : P∪H=B := by change (B\C)∪(C\A)=B; rw [←b.overlap]; ext; simp only [mem_union,mem_inter,mem_sdiff]; tauto
  have cc' : Q∪H=C := by change (A\B)∪(C\A)=C; rw [←c.overlap]; ext; simp only [mem_union,mem_inter,mem_sdiff]; tauto
  have pq : Disjoint P Q := disjoint_left.mpr (fun _ p r => (mem_sdiff.mp r).2 (mem_sdiff.mp p).1)
  have ph : Disjoint P H := disjoint_left.mpr (fun _ p s => (mem_sdiff.mp p).2 (mem_sdiff.mp s).1)
  have qh : Disjoint Q H := disjoint_left.mpr (fun _ r s => (mem_sdiff.mp s).2 (mem_sdiff.mp r).1)
  have all : P∪Q∪H=V := by
    have sub := sdiff_eq_empty_iff_subset.mp empty
    rw [←ca',←cb',←cc'] at sub
    have pv := (sdiff_subset : P⊆B).trans cb.sub
    have qv := (sdiff_subset : Q⊆A).trans ca.sub
    have hv := (sdiff_subset : H⊆C).trans cc.sub
    apply Subset.antisymm (union_subset (union_subset pv qv) hv)
    intro i iv
    have := sub iv
    simp only [mem_union] at this ⊢
    tauto
  have ab : A∪B=V := by rw [←ca',←cb',←all]; ext; simp only [mem_union]; tauto
  have ac : A∪C=V := by rw [←ca',←cc',←all]; ext; simp only [mem_union]; tauto
  have bc : B∪C=V := by rw [←cb',←cc',←all]; ext; simp only [mem_union]; tauto
  obtain ⟨f,p⟩ := a.leftPath
  obtain ⟨g,r⟩ := a.rightPath
  obtain ⟨h,s⟩ := b.leftPath
  obtain ⟨eq₁⟩ := a.copy
  obtain ⟨eq₂⟩ := b.copy
  have one : P.card=Q.card := by simpa only [Fintype.card_coe] using Fintype.card_congr eq₁.equiv
  have two : H.card=P.card := by simpa only [Fintype.card_coe] using Fintype.card_congr eq₂.equiv
  have p' := internal_scores ca cb ca' cb' ab pq ph qh a.live c.live b.live p r s x strict
  have r' := internal_scores ca cc ((union_comm Q P).trans ca') cc' ac pq.symm qh ph c.live a.live b.live r p s x strict
  have s' := internal_scores cb cc ((union_comm H P).trans cb') ((union_comm H Q).trans cc')
    bc ph.symm qh.symm pq b.live a.live c.live s p r x strict
  let W := fun i => x (f i)+x (g i)+x (h i)
  have total := sum_chain p x
  have total' := sum_chain r x
  have total'' := sum_chain s x
  change (∑i∈range P.card,x (f i))=mass P x at total
  change (∑i∈range Q.card,x (g i))=mass Q x at total'
  change (∑i∈range H.card,x (h i))=mass H x at total''
  have sz := card_sdiff_add_card_inter A B
  rw [a.overlap,ca.size] at sz
  change Q.card+P.card=q+1 at sz
  have plus : Disjoint (P∪Q) H := Finset.disjoint_union_left.mpr ⟨ph,qh⟩
  have pu : P⊆V := (show P⊆A from ca' ▸ subset_union_left).trans ca.sub
  have qu : Q⊆V := (show Q⊆A from ca' ▸ subset_union_right).trans ca.sub
  have hu : H⊆V := (show H⊆C from cc' ▸ subset_union_right).trans cc.sub
  have massPos : 0<mass V x := sum_pos' (fun i iv => (xp i iv).le)
    (by obtain ⟨i,ip⟩ := a.live; exact ⟨i,pu ip,xp i (pu ip)⟩)
  apply scores_false (m:=P.card) (W:=W) hq (by omega) massPos
  · intro i hi
    have y := xp _ (qu (r.mem (one ▸ hi)))
    have z := xp _ (hu (s.mem (two.symm ▸ hi)))
    dsimp [W]; linarith [xp _ (pu (p.mem hi))]
  · dsimp only [W]
    rw [sum_add_distrib,sum_add_distrib,total,one,total',←one,←two,total'']
    change (∑i∈P,x i)+(∑i∈Q,x i)+(∑i∈H,x i)=∑i∈V,x i
    rw [←sum_union pq,←sum_union plus,all]
  · intro i hi
    have u := p'.1 i hi
    have v := r'.1 i (one ▸ hi)
    have w := s'.1 i (two.symm ▸ hi)
    dsimp [W]; linarith
  · have u := p'.2
    have v := r'.2
    have w := s'.2
    change mass V x < x (g (Q.card-1))+_ at v
    change mass V x < x (h (H.card-1))+_ at w
    rw [←one] at v
    rw [two] at w
    dsimp [W]; linarith

#print axioms exterior_exists

open PairedFamilyLoop FirstPacketBarrier MarkedCyclePeeling

private theorem split_logic {a b c v : Prop} (p : b ∧ c ↔ c ∧ ¬a) (r : c ∧ a ↔ a ∧ ¬b) (s : b → v) :
    (v ∧ ¬(a ∧ ¬b)) ↔ (v ∧ ¬((a ∨ b) ∨ c)) ∨ b := by tauto


/-- A strict parent cannot be assembled from two smaller supports joined
at a single label when every arc is internal to one of them. -/
theorem one_join_false {q E V I J t} (hq : 1≤q) (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (cover : I∪J=V) (shared : I∩J={t}) (li : I≠V) (lj : J≠V)
    (internal : ∀u∈V,∀v∈V,E u v=true → (u∈I ∧ v∈I) ∨ (u∈J ∧ v∈J))
    {x : ℕ→ℚ} (xp : ∀v∈V,0≤x v) (strict : ∀v∈V,mass V x<WeightedSD.row q E V x v) : False := by
  classical
  have iv : I⊆V := cover ▸ subset_union_left
  have jv : J⊆V := cover ▸ subset_union_right
  have tin : t∈I∩J := shared.symm ▸ mem_singleton_self t
  have vI := (mem_inter.mp tin).1
  have vJ := (mem_inter.mp tin).2
  have low {S} (sub : S⊆V) (prop : S≠V) (ts : t∈S)
      (closed : ∀u∈S,u≠t → ∀v∈V,E u v=true → v∈S) : WeightedSD.row q E S x t≤mass S x := by
    obtain ⟨u,us,lo⟩ := small.induced free S sub prop x (fun i hi => xp i (sub hi)) ⟨t,ts⟩
    by_cases eq : u=t
    · exact eq ▸ lo
    · have empty : outN E (V\S) u=∅ := eq_empty_iff_forall_notMem.mpr (fun v hv =>
        (mem_sdiff.mp (mem_outN.mp hv).1).2 (closed u us eq v (mem_sdiff.mp (mem_outN.mp hv).1).1 (mem_outN.mp hv).2))
      have z : outW E (V\S) x u=0 := by rw [outW_eq_mass,empty]; exact sum_empty
      have hi := strict u (sub us)
      rw [WeightedSD.row,outW_split sub,z,add_zero] at hi
      exact ((mass_mono sub xp).trans_lt hi).not_ge lo |>.elim
  have al := low iv li vI (fun u ui ne v vv edge => (internal u (iv ui) v vv edge).elim And.right
    (fun j => (ne (mem_singleton.mp (shared ▸ mem_inter.mpr ⟨ui,j.1⟩))).elim))
  have bl := low jv lj vJ (fun u uj ne v vv edge => (internal u (jv uj) v vv edge).elim
    (fun i => (ne (mem_singleton.mp (shared ▸ mem_inter.mpr ⟨i.1,uj⟩))).elim) And.right)
  have mx := sum_union_inter (f:=x) (s₁:=I) (s₂:=J)
  have ox := sum_union_inter (f:=fun v => if E t v=true then x v else 0) (s₁:=I) (s₂:=J)
  rw [cover,shared,sum_singleton] at mx ox
  have no := loopfree free hq (iv vI)
  simp [no] at ox
  change mass V x+x t=mass I x+mass J x at mx
  change outW E V x t=outW E I x t+outW E J x t at ox
  have hi := strict t (iv vI)
  simp only [WeightedSD.row,ox,mul_add] at hi al bl
  linarith

/-- Any proposed fourth member requires a fifth. With just one further
cycle the cardinality congruence would make its attachment a single vertex. -/
theorem fifth_member {q D V F A B C N} (hq : 1≤q) (free : QFree (graph D F) V q)
    (small : SmallerSmallRow q V.card) (ca : Cycle (graph D F) V q A)
    (cb : Cycle (graph D F) V q B) (cc : Cycle (graph D F) V q C) (cn : Cycle (graph D F) V q N)
    (ex : q≤(V\(A∪B∪C)).card) (inside : (N∩(A∪B∪C)).Nonempty)
    {x : ℕ→ℚ} (xp : ∀v∈V,0<x v) (strict : ∀v∈V,mass V x<WeightedSD.row q (graph D F) V x v) :
    ∃K∈F,K≠A ∧ K≠B ∧ K≠C ∧ K≠N := by
  classical
  let T := A∪B∪C
  have av : A⊆T := subset_union_left.trans subset_union_left
  have bv : B⊆T := subset_union_right.trans subset_union_left
  have cv : C⊆T := subset_union_right
  have tv : T⊆V := union_subset (union_subset ca.sub cb.sub) cc.sub
  by_contra! blocked
  have four (K) (kf : K∈F) : K=A ∨ K=B ∨ K=C ∨ K=N := by
    by_cases h : K=A
    · exact Or.inl h
    by_cases j : K=B
    · exact Or.inr (Or.inl j)
    by_cases z : K=C
    · exact Or.inr (Or.inr (Or.inl z))
    exact Or.inr (Or.inr (Or.inr (blocked K kf h j z)))
  have intern (u v) (edge : graph D F u v=true) : (u∈T ∧ v∈T) ∨ (u∈N ∧ v∈N) := by
    obtain ⟨K,kh⟩ := active.mp edge
    obtain ⟨kf,ku,kv,_⟩ := mem_col.mp kh
    rcases four K kf with rfl|rfl|rfl|rfl
    · exact Or.inl ⟨av ku,av kv⟩
    · exact Or.inl ⟨bv ku,bv kv⟩
    · exact Or.inl ⟨cv ku,cv kv⟩
    · exact Or.inr ⟨ku,kv⟩
  have cover : T∪N=V := by
    refine Subset.antisymm (union_subset tv cn.sub) ?_
    intro u uv
    have arc : (outN (graph D F) V u).Nonempty := by
      by_contra! empty
      have high := strict u uv
      have le : x u≤mass V x := single_le_sum (fun i hi => (xp i hi).le) uv
      rw [WeightedSD.row,outW_eq_mass,empty] at high
      simp [mass] at high
      exact le.not_gt high
    obtain ⟨v,vh⟩ := arc
    exact mem_union.mpr ((intern u v (mem_outN.mp vh).2).imp And.left And.left)
  have eq : V\T=N\T := by rw [←cover]; ext; simp only [mem_sdiff,mem_union]; tauto
  change q≤(V\T).card at ex
  rw [eq] at ex
  have csize := card_sdiff_add_card_inter N T
  rw [cn.size] at csize
  have non := card_pos.mpr inside
  change 0<(N∩T).card at non
  obtain ⟨t,shared⟩ := card_eq_one.mp (show (N∩T).card=1 by omega)
  have lt : T≠V := by
    obtain ⟨w,wh⟩ := card_pos.mp (show 0<(N\T).card by omega)
    exact fun e => (mem_sdiff.mp wh).2 (e.symm ▸ cn.sub (mem_sdiff.mp wh).1)
  have ln : N≠V := by
    intro e
    have sub : A⊆N∩T := fun i hi => mem_inter.mpr ⟨e.symm ▸ ca.sub hi,av hi⟩
    have bound := card_le_card sub
    rw [ca.size,shared,card_singleton] at bound
    omega
  exact one_join_false hq free small cover ((inter_comm T N).trans shared) lt ln
    (fun u _ v _ => intern u v) (fun i hi => (xp i hi).le) strict

#print axioms fifth_member

/-- The next selected cycle crosses the union of the three recurrent
cycles. Child cardinality also makes the whole exterior a positive
multiple of the cutoff. -/
theorem fourth_member {q D V F A B C} (hq : 2≤q) (free : QFree (graph D F) V q)
    (small : SmallerSmallRow q V.card) (af : A∈F) (bf : B∈F) (cf : C∈F)
    (cycles : ∀I∈F,Cycle (graph D F) V q I)
    (a : Packet (graph D F) V A B C) (b : Packet (graph D F) V B C A)
    (c : Packet (graph D F) V C A B) {x : ℕ→ℚ} (xp : ∀v∈V,0<x v)
    (strict : ∀v∈V,mass V x<WeightedSD.row q (graph D F) V x v)
    (modOne : ((V\(A\B)).card : ZMod q)=1) :
    let T := A∪B∪C
    q∣(V\T).card ∧ q≤(V\T).card ∧
      ∃N∈F,N≠A ∧ N≠B ∧ N≠C ∧ (N∩T).Nonempty ∧ (B\C).card≤(N\T).card ∧
        (∃f,Chain (graph D F) (N\T) f) ∧ (∃g,Chain (graph D F) (N∩T) g) ∧
        ∃K∈F,K≠A ∧ K≠B ∧ K≠C ∧ K≠N := by
  classical
  intro T
  let E := graph D F
  have ca := cycles A af
  have cb := cycles B bf
  have cc := cycles C cf
  have tv : T⊆V := union_subset (union_subset ca.sub cb.sub) cc.sub
  have av : A⊆T := subset_union_left.trans subset_union_left
  have bv : B⊆T := subset_union_right.trans subset_union_left
  have cv : C⊆T := subset_union_right
  obtain ⟨w,ww⟩ := exterior_exists hq ca cb cc a b c xp strict
  have outside : (V\T).Nonempty := ⟨w,ww⟩
  have nt : T≠V := fun eq => (mem_sdiff.mp (show w∈V\T from ww)).2 (eq.symm ▸ (mem_sdiff.mp ww).1)
  have live : T.Nonempty := by
    obtain ⟨z,za⟩ := card_pos.mp (show 0<A.card by rw [ca.size]; omega)
    exact ⟨z,av za⟩
  obtain ⟨u,ut,low⟩ := small.induced free T tv nt x (fun i hi => (xp i (tv hi)).le) live
  have signed := strict u (tv ut)
  have massLe : mass T x≤mass V x := sum_le_sum_of_subset_of_nonneg tv (fun i hi _ => (xp i hi).le)
  have hit : (outN E (V\T) u).Nonempty := by
    by_contra! empty
    have eq : outW E (V\T) x u=0 := by rw [outW_eq_mass,empty]; exact sum_empty
    change mass V x < x u+q*outW E V x u at signed
    rw [outW_split tv,eq,add_zero] at signed
    exact (massLe.trans_lt signed).not_ge low
  obtain ⟨v,vh⟩ := hit
  obtain ⟨vout,uv⟩ := mem_outN.mp vh
  obtain ⟨N,nh⟩ := active.mp uv
  obtain ⟨nf,un,vn,_⟩ := mem_col.mp nh
  have vnT := (mem_sdiff.mp vout).2
  have na : N≠A := fun eq => vnT (av (eq ▸ vn))
  have nb : N≠B := fun eq => vnT (bv (eq ▸ vn))
  have nc : N≠C := fun eq => vnT (cv (eq ▸ vn))
  have it : (N∩T).Nonempty := ⟨u,mem_inter.mpr ⟨un,ut⟩⟩
  have ov := triple_overlap free ca cb cc a b c (cycles _ nf) na nb nc
  have split : V\(A\B)=(V\T)∪B := by
    ext i
    have p : i∈B∩C ↔ i∈C\A := b.overlap ▸ Iff.rfl
    have r : i∈C∩A ↔ i∈A\B := c.overlap ▸ Iff.rfl
    have sb := @cb.sub i
    simp only [T,mem_union,mem_inter,mem_sdiff] at p r ⊢
    exact split_logic p r sb
  have dis : Disjoint (V\T) B := disjoint_left.mpr (fun _ z zb => (mem_sdiff.mp z).2 (bv zb))
  rw [split,card_union_of_disjoint dis,cb.size] at modOne
  have zero : ((V\T).card : ZMod q)=0 := by
    simpa only [Nat.cast_add,Nat.cast_one, ZMod.natCast_self,zero_add,add_eq_right] using modOne
  have divisor : q∣(V\T).card := (ZMod.natCast_eq_zero_iff _ _).mp zero
  exact ⟨divisor,Nat.le_of_dvd (card_pos.mpr outside) divisor,
    N,nf,na,nb,nc,it,ov.1,(ov.2.2 it).1,(ov.2.2 it).2,
    fifth_member (by omega) free small ca cb cc (cycles _ nf) (Nat.le_of_dvd (card_pos.mpr outside) divisor) it xp strict⟩

/-- Specialize to the actual chosen repair schedule. Three consecutive
packets force the fourth member independently of any search over cycles. -/
theorem on_schedule {F q D V} (hq : 2≤q) (free : QFree (graph D F) V q)
    (small : SmallerSmallRow q V.card) (cycles : ∀I∈F,Cycle (graph D F) V q I)
    {x : ℕ→ℚ} (xp : ∀v∈V,0<x v) (strict : ∀v∈V,mass V x<WeightedSD.row q (graph D F) V x v)
    (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (join : ∀s,previous (go s)=current s)
    (mark : ∀s,Marked (graph D F) (previous s) (current s) (current (go s)))
    (s : PairedFamilyLoop.State F) :
    let E := graph D F
    let A := previous s
    let B := current s
    let C := current (go s)
    let T := A∪B∪C
    ((V\RawRepairAlternative.gone s).card : ZMod q)=1 →
    Packet E V A B C →
    Packet E V (previous (go s)) C (current (go (go s))) →
    Packet E V (previous (go (go s))) (current (go (go s))) (current (go (go (go s)))) →
    q∣(V\T).card ∧ q≤(V\T).card ∧
      ∃N∈F,N≠A ∧ N≠B ∧ N≠C ∧ (N∩T).Nonempty ∧ (B\C).card≤(N\T).card ∧
        (∃f,Chain E (N\T) f) ∧ (∃g,Chain E (N∩T) g) ∧
        ∃K∈F,K≠A ∧ K≠B ∧ K≠C ∧ K≠N := by
  intro E A B C T modOne a b c
  have lp (z : PairedFamilyLoop.State F) := (mem_product.mp (mem_filter.mp z.property).1).1
  have rp (z : PairedFamilyLoop.State F) := (mem_product.mp (mem_filter.mp z.property).1).2
  have ret (z : PairedFamilyLoop.State F) := scheduled_return free (cycles _ (lp z)) (cycles _ (rp z))
    (cycles _ (rp (go z))) (cycles _ (rp (go (go z)))) (join z) (mark z) (mark (go z))
  have d := ret s a b
  have e := ret (go s) b c
  dsimp only [A,B,C,E] at a b c
  rw [join s,d] at b
  rw [join (go s),d,e,join s] at c
  exact fourth_member hq free small (lp s) (rp s) (rp (go s)) cycles a b c xp strict modOne

#print axioms fourth_member
#print axioms on_schedule

end LeanCH.BR.Closure.FlatPairedExcursion

