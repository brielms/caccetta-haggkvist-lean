import checkpoints.shen_extension.FlatExchangeOverlap

namespace LeanCH.BR.Closure.FlatExchangeTriangle
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor FlatExchangeIntervals FlatExchangeChain

/-- An identification of the two private blocks with their contacts at
every vertex outside the blocks. -/
structure Copy (E : CH.Digraph) (V L R : Finset ℕ) where
  equiv : ↥L ≃ ↥R
  arcs : ∀i j : ↥L,E i j=E (equiv i) (equiv j)
  contacts : ∀w∈V\(L∪R),∀i : ↥L,E w i=E w (equiv i) ∧ E i w=E (equiv i) w

theorem copy_of_iso {E : CH.Digraph} {V S T : Finset ℕ} (cover : V⊆S∪T) (e : ↥S ≃ ↥T)
    (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) (iso : ∀i j : ↥S,E i j=E (e i) (e j)) :
    Nonempty (Copy E V (S\T) (T\S)) := by
  classical
  let f (i : ↥(S\T)) : ↥S := ⟨i,(mem_sdiff.mp i.property).1⟩
  let g (j : ↥(T\S)) : ↥T := ⟨j,(mem_sdiff.mp j.property).1⟩
  have dest (i : ↥(S\T)) : (e (f i):ℕ)∈T\S := by
    refine mem_sdiff.mpr ⟨(e (f i)).property,fun h => ?_⟩
    have eq : e ⟨e (f i),h⟩=e (f i) := Subtype.ext (fix ⟨e (f i),h⟩ (e (f i)).property)
    have val : (e (f i):ℕ)=(i:ℕ) := congrArg Subtype.val (e.injective eq)
    exact (mem_sdiff.mp i.property).2 (val ▸ (e (f i)).property)
  have back (j : ↥(T\S)) : (e.symm (g j):ℕ)∈S\T := by
    refine mem_sdiff.mpr ⟨(e.symm (g j)).property,fun h => ?_⟩
    have eq := fix (e.symm (g j)) h
    rw [e.apply_symm_apply] at eq
    have val : (j:ℕ)=(e.symm (g j):ℕ) := eq
    exact (mem_sdiff.mp j.property).2 (val ▸ (e.symm (g j)).property)
  let p : ↥(S\T) ≃ ↥(T\S) := {
    toFun := fun i => ⟨e (f i),dest i⟩
    invFun := fun j => ⟨e.symm (g j),back j⟩
    left_inv := fun i => Subtype.ext (congrArg (fun v : ↥S => v.val) (e.symm_apply_apply (f i)))
    right_inv := fun j => Subtype.ext (congrArg (fun v : ↥T => v.val) (e.apply_symm_apply (g j))) }
  refine ⟨⟨p,fun i j => iso (f i) (f j),?_⟩⟩
  intro w hw i
  have either := mem_union.mp (cover (mem_sdiff.mp hw).1)
  have both : w∈S ∧ w∈T := by by_cases ws : w∈S <;> by_cases wt : w∈T <;> simp_all
  let u : ↥S := ⟨w,both.1⟩
  change E u (f i)=E u (e (f i)) ∧ E (f i) u=E (e (f i)) u
  have a := iso u (f i)
  have b := iso (f i) u
  rw [fix u both.2] at a b
  exact ⟨a,b⟩

/-- Two successive identifications give matching contacts between the
first and third blocks outside all three. -/
private theorem extremal {q E V A B C P Q H} (ca : Cycle E V q A) (cb : Cycle E V q B)
    (cc : Cycle E V q C) (pa : P=A∩B) (hdef : H=B∩C) (qdef : Q=A\B)
    (pb : P=B\C) (mSize : (C\B).card=Q.card)
    (p : ↥H ≃ ↥Q) (ep : ∀u v : ↥H,E u v=E (p u) (p v))
    (eqOut : ∀w∈V,w∉P → w∉Q → w∉H → ∀u : ↥H,E w u=E w (p u) ∧ E u w=E (p u) w)
    {f : ℕ→ℕ} (path : Chain E Q f) (conn : Connected E (C\B))
    {b y r : ℕ} (bank : b∈C\B) (yh : y∈H) (hit : E b y=true) (miss : E b r=false)
    (pair : FullCycleTransfer.Pairing E B A) (paired : pair.label y=r) :
    C\B=Q := by
  classical
  have yc := mem_inter.mp (hdef ▸ yh)
  have hpB : H⊆B := hdef ▸ inter_subset_left
  have hpC : H⊆C := hdef ▸ inter_subset_right
  have ppB : P⊆B := pb ▸ sdiff_subset
  have qqA : Q⊆A := qdef ▸ sdiff_subset
  let Y : ↥H := ⟨y,yh⟩
  have noH (v : ↥H) : ¬E v y=true := by
    intro edge
    have eq := card_le_one.mp (cc.incoming y yc.2).le _ (mem_inN.mpr ⟨hpC v.property,edge⟩)
      _ (mem_inN.mpr ⟨(mem_sdiff.mp bank).1,hit⟩)
    exact (mem_sdiff.mp bank).2 (eq ▸ hpB v.property)
  obtain ⟨w,hw⟩ := card_pos.mp (show 0<(inN E B y).card by rw [show (inN E B y).card=1 from cb.incoming y yc.1]; decide)
  obtain ⟨wb,wy⟩ := mem_inN.mp hw
  have wnc : w∉C := fun wc => noH (⟨w,hdef.symm ▸ mem_inter.mpr ⟨wb,wc⟩⟩) wy
  have wp : w∈P := pb.symm ▸ mem_sdiff.mpr ⟨wb,wnc⟩
  have wa := (mem_inter.mp (pa ▸ wp)).1
  have yr : (pair.equiv ⟨y,yc.1⟩:ℕ)=r := (pair.label_apply yc.1).symm.trans paired
  have wr := pair.successor w (mem_inter.mpr ⟨wb,wa⟩) ⟨y,yc.1⟩ wy
  rw [yr] at wr
  have ra : r∈A := yr ▸ (pair.equiv ⟨y,yc.1⟩).property
  have rq : r∈Q := by
    rw [qdef]
    refine mem_sdiff.mpr ⟨ra,fun rb => ?_⟩
    have ry := card_le_one.mp (cb.heads w wb).le _ (mem_outN.mpr ⟨rb,wr⟩) _ (mem_outN.mpr ⟨yc.1,wy⟩)
    rw [ry] at miss
    simp [hit] at miss
  have noR (v : ↥Q) : ¬ E v r=true := by
    intro edge
    have eq := card_le_one.mp (ca.incoming r ra).le _ (mem_inN.mpr ⟨qqA v.property,edge⟩)
      _ (mem_inN.mpr ⟨wa,wr⟩)
    have vb : (v:ℕ)∈A\B := qdef ▸ (show (v:ℕ)∈Q from v.property)
    exact (mem_sdiff.mp vb).2 (eq ▸ wb)
  have noY (v : ↥Q) : ¬E v (p Y)=true := by
    intro arc
    apply noH (p.symm v)
    exact (ep (p.symm v) Y).trans (by simpa using arc)
  have first {z} (zq : z∈Q) (no : ∀v : ↥Q,¬E v z=true) : f 0=z := by
    obtain ⟨j,hj,eq⟩ := path.index zq
    cases j with
    | zero => exact eq
    | succ i =>
      have step := (path.edge i (by omega) (i+1) hj).mpr rfl
      exact (no ⟨f i,path.mem (by omega)⟩ (eq ▸ step)).elim
  have mapped : (p Y:ℕ)=r := (first (p Y).property noY).symm.trans (first rq noR)
  have outside (v) (vr : v∈C\B) (nq : v∉Q) := eqOut v (cc.sub (mem_sdiff.mp vr).1)
    (fun t => (mem_sdiff.mp vr).2 (ppB t)) nq (fun t => (mem_sdiff.mp vr).2 (hpB t))
  have bq : b∈Q := by
    by_contra nq
    have eq := (outside b bank nq Y).1
    rw [mapped] at eq
    exact Bool.noConfusion (miss.symm.trans (eq.symm.trans hit))
  have agree (u) (ur : u∈C\B) (v) (vr : v∈C\B) (edge : E u v=true) : u∈Q ↔ v∈Q := by
    constructor
    · intro uq
      by_contra vn
      let z := p.symm (⟨u,uq⟩ : ↥Q)
      have zc := hpC z.property
      have ez := (outside v vr vn z).2.trans (by simpa [z] using edge)
      have eq := card_le_one.mp (cc.incoming v (mem_sdiff.mp vr).1).le _ (mem_inN.mpr ⟨zc,ez⟩)
        _ (mem_inN.mpr ⟨(mem_sdiff.mp ur).1,edge⟩)
      exact (mem_sdiff.mp ur).2 (eq ▸ hpB z.property)
    · intro vq
      by_contra un
      let z := p.symm (⟨v,vq⟩ : ↥Q)
      have ez := (outside u ur un z).1.trans (by simpa [z] using edge)
      have eq := card_le_one.mp (cc.heads u (mem_sdiff.mp ur).1).le _ (mem_outN.mpr ⟨hpC z.property,ez⟩)
        _ (mem_outN.mpr ⟨(mem_sdiff.mp vr).1,edge⟩)
      exact (mem_sdiff.mp vr).2 (eq ▸ hpB z.property)
  have same : ConstantOnArcs E (C\B) (fun z => decide (z∈Q)) := by
    intro u hu v hv edge
    by_cases uq : u∈Q
    · simp [uq,(agree u hu v hv edge).mp uq]
    · simp [uq,mt (agree u hu v hv edge).mpr uq]
  apply eq_of_subset_of_card_le _ mSize.ge
  intro v vr
  have all := conn _ same b bank v vr
  simpa [bq] using all.symm

#print axioms copy_of_iso

structure Packet (E : CH.Digraph) (V A B C : Finset ℕ) : Prop where
  overlap : A∩B=B\C
  live : (B\C).Nonempty
  copy : Nonempty (Copy E V (B\C) (A\B))
  leftPath : ∃f,Chain E (B\C) f
  rightPath : ∃g,Chain E (A\B) g

def Marked (E : CH.Digraph) (A B C : Finset ℕ) : Prop :=
  ∃b∈C\B, ∃y∈B∩C, ∃r, E b y=true ∧ E b r=false ∧
    ∃p : FullCycleTransfer.Pairing E B A,p.label y=r

theorem packet {q E V A B C f g} (ca : Cycle E V q A) (cb : Cycle E V q B)
    (eqSize : (A\B).card=(B\C).card) (half : 2*(B\C).card=q+1)
    (dis : Disjoint (A∩B) (B∩C)) :
    let S := V\(A\B)
    let T := V\(B\C)
    ∀e : ↥S ≃ ↥T,(∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) →
      (∀i j : ↥S,E i j=E (e i) (e j)) → CrossOrder q E S T f g → Packet E V A B C := by
  classical
  intro S T e fix iso order
  have left : S\T=B\C := by ext i; have b := @cb.sub i; simp only [S,T,mem_sdiff]; tauto
  have right : T\S=A\B := by ext i; have a := @ca.sub i; simp only [S,T,mem_sdiff]; tauto
  have cover : V⊆S∪T := by intro i hi; simp only [S,T,mem_union,mem_sdiff]; tauto
  have sub : A∩B⊆B\C := fun i hi => mem_sdiff.mpr ⟨(mem_inter.mp hi).2,
    fun h => disjoint_left.mp dis hi (mem_inter.mpr ⟨(mem_inter.mp hi).2,h⟩)⟩
  have count := card_sdiff_add_card_inter A B
  rw [eqSize,ca.size] at count
  refine ⟨eq_of_subset_of_card_le sub (by omega),card_pos.mp (by omega),?_,
    ⟨f,left ▸ order.leftPath⟩,⟨g,right ▸ order.rightPath⟩⟩
  simpa only [left,right] using copy_of_iso cover e fix iso

theorem bank_return {q E V A B C D} (free : QFree E V q)
    (ca : Cycle E V q A) (cb : Cycle E V q B) (cc : Cycle E V q C) (cd : Cycle E V q D)
    (first : Packet E V A B C) (second : Packet E V B C D)
    (one : Marked E A B C) (two : Marked E B C D) :
    C\B=A\B ∧ D=A := by
  classical
  let P := B\C
  let Q := A\B
  let H := B∩C
  have hp : H=C\D := second.overlap
  obtain ⟨old⟩ := first.copy
  have newExists : Nonempty (Copy E V H P) := hp.symm ▸ second.copy
  obtain ⟨newC⟩ := newExists
  let p := newC.equiv.trans old.equiv
  have ep (u v : ↥H) : E u v=E (p u) (p v) := (newC.arcs u v).trans (old.arcs _ _)
  have ext (w) (wv : w∈V) (wp : w∉P) (wq : w∉Q) (wh : w∉H) (u : ↥H) :
      E w u=E w (p u) ∧ E u w=E (p u) w := by
    have x := newC.contacts w (mem_sdiff.mpr ⟨wv,fun m => (mem_union.mp m).elim wh wp⟩) u
    have y := old.contacts w (mem_sdiff.mpr ⟨wv,fun m => (mem_union.mp m).elim wp wq⟩) (newC.equiv u)
    exact ⟨x.1.trans y.1,x.2.trans y.2⟩
  have symSize {I J : Finset ℕ} (eq : I.card=J.card) : (I\J).card=(J\I).card := by
    have a := card_sdiff_add_card_inter I J
    have b := card_sdiff_add_card_inter J I
    rw [inter_comm J I] at b
    omega
  have oldCount : P.card=Q.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr old.equiv
  have ch : C\H=C\B := by ext i; simp only [H,mem_sdiff,mem_inter]; tauto
  have hh : H.Nonempty := hp.symm ▸ second.live
  obtain ⟨fH,hH⟩ := second.leftPath
  have hPath : Chain E H fH := hp.symm ▸ hH
  have conn : Connected E (C\B) := ch ▸ FlatExchangeOverlap.complement_connected free cc inter_subset_right hh hPath
  obtain ⟨g,Qpath⟩ := first.rightPath
  obtain ⟨b,bh,y,yh,r,hit,miss,pair,rel⟩ := one
  have same : C\B=Q := extremal ca cb cc first.overlap.symm rfl rfl rfl
    ((symSize (cc.size.trans cb.size.symm)).trans oldCount) p ep ext Qpath conn bh yh hit miss pair rel
  have qI : Q=C∩D := by
    ext i
    have eq₁ : i∈Q ↔ i∈C\B := same ▸ Iff.rfl
    have eq₂ : i∈B∩C ↔ i∈C\D := second.overlap ▸ Iff.rfl
    simp only [mem_sdiff,mem_inter] at eq₁ eq₂ ⊢
    tauto
  have qne : Q.Nonempty := by
    obtain ⟨v,hv⟩ := first.live
    exact ⟨_,(old.equiv ⟨v,hv⟩).property⟩
  have dq : D\Q=D\C := by ext i; rw [qI]; simp only [mem_sdiff,mem_inter]; tauto
  have dc : Connected E (D\C) := dq ▸ FlatExchangeOverlap.complement_connected free cd
    (show Q⊆D by rw [qI]; exact inter_subset_right) qne Qpath
  obtain ⟨f,Ppath⟩ := first.leftPath
  obtain ⟨b',bh',y',yh',r',hit',miss',pair',rel'⟩ := two
  have revArc (u v : ↥Q) : E u v=E (old.equiv.symm u) (old.equiv.symm v) := by
    simpa using (old.arcs (old.equiv.symm u) (old.equiv.symm v)).symm
  have revExt (w) (wv : w∈V) (_ : w∉H) (wp : w∉P) (wq : w∉Q) (u : ↥Q) :
      E w u=E w (old.equiv.symm u) ∧ E u w=E (old.equiv.symm u) w := by
    have z := old.contacts w (mem_sdiff.mpr ⟨wv,fun m => (mem_union.mp m).elim wp wq⟩) (old.equiv.symm u)
    simpa using And.intro z.1.symm z.2.symm
  have dh : D\C=P := extremal cb cc cd rfl qI rfl hp (by
    rw [symSize (cd.size.trans cc.size.symm),←hp]
    simpa only [Fintype.card_coe] using Fintype.card_congr newC.equiv)
    old.equiv.symm revArc revExt Ppath dc bh' (qI.symm ▸ yh') hit' miss' pair' rel'
  refine ⟨same,?_⟩
  ext i
  have x : i∈D\C ↔ i∈B\C := dh ▸ Iff.rfl
  have y : i∈A\B ↔ i∈C∩D := qI ▸ Iff.rfl
  have z : i∈A∩B ↔ i∈B\C := first.overlap ▸ Iff.rfl
  simp only [mem_sdiff,mem_inter] at x y z
  tauto

#print axioms bank_return

open PairedFamilyLoop

theorem marked_of_mark {F q E V} {x : ℕ→ℚ} {s t : PairedFamilyLoop.State F}
    {send : ↥(previous s) ≃ ↥(previous t)}
    (mark : previous t=current s ∧ ∃b, ∃r : ↥(previous s),
      E b r=false ∧ E b (send r)=true ∧ FullFamilySchedule.Mark q E V x s t send b (send r) r) :
    Marked E (previous s) (current s) (current t) := by
  obtain ⟨join,b,r,miss,hit,p,_,lab,bh,yh,_⟩ := mark
  refine ⟨b,bh,_,mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp yh).2).1,(mem_inter.mp yh).1⟩,
    r,hit,miss,?_⟩
  rw [←join]
  exact ⟨p,lab⟩

theorem packet_on_mark {F q E V} (hq : 2≤q) (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {x : ℕ→ℚ} (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    {s t : PairedFamilyLoop.State F} (ca : Cycle E V q (previous s)) (cb : Cycle E V q (current s))
    {send : ↥(previous s) ≃ ↥(previous t)}
    (mark : previous t=current s ∧ ∃b, ∃r : ↥(previous s),
      E b r=false ∧ E b (send r)=true ∧ FullFamilySchedule.Mark q E V x s t send b (send r) r)
    (sz : (RawRepairAlternative.gone s).card=(RawRepairAlternative.gone t).card) :
    let S := V\RawRepairAlternative.gone s
    let T := V\RawRepairAlternative.gone t
    BRsub.Sat q E S → BRsub.Sat q E T → ∀e : ↥S ≃ ↥T,
    (∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) → FlatChildExchange.ExchangePattern E e →
    (∀i j : ↥S,E i j=E (e i) (e j)) → 2*(RawRepairAlternative.gone t).card=q+1 →
    Packet E V (previous s) (current s) (current t) := by
  intro S T ss ts e fix pattern iso half
  rcases FlatExchangeChain.on_mark hq free small xp strict ca.sub cb mark sz ss ts e fix pattern with
    ⟨⟨i,j,yes,no⟩,_⟩ | ⟨_,large,f,g,order,_⟩
  · have bad := iso i j
    rw [yes,no] at bad
    contradiction
  · have dis := (FlatExchangeOverlap.on_mark hq free ca cb mark sz e f fix iso large order.leftPath).1
    have join := mark.1
    dsimp only [S,T,RawRepairAlternative.gone] at sz half e fix iso order
    rw [join] at sz half
    have aux : ∀ (U : Finset ℕ), U=current s →
        ∀ (e : ↥(V\(previous s\current s)) ≃ ↥(V\(U\current t))),
        (∀i : ↥(V\(previous s\current s)),(i:ℕ)∈V\(U\current t) → (e i:ℕ)=i) →
        (∀i j : ↥(V\(previous s\current s)), E i j=E (e i) (e j)) →
        CrossOrder q E (V\(previous s\current s)) (V\(U\current t)) f g →
        Packet E V (previous s) (current s) (current t) := by
      intro U eq
      subst U
      exact packet ca cb sz half dis
    exact aux _ join e fix iso order

theorem scheduled_return {F q E V} (free : QFree E V q)
    {s t u : PairedFamilyLoop.State F} (ca : Cycle E V q (previous s))
    (cb : Cycle E V q (current s)) (cc : Cycle E V q (current t)) (cd : Cycle E V q (current u))
    (join : previous t=current s)
    (one : Marked E (previous s) (current s) (current t))
    (two : Marked E (previous t) (current t) (current u))
    (first : Packet E V (previous s) (current s) (current t))
    (second : Packet E V (previous t) (current t) (current u)) : current u=previous s := by
  rw [join] at second two
  exact (bank_return free ca cb cc cd first second one two).2

#print axioms packet_on_mark
#print axioms scheduled_return

/-- Three consecutive packets suffice, including when only this segment of a
chosen orbit has been inspected. The ordered state then has least period three. -/
theorem period_three {F q E V} (free : QFree E V q) (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (left : ∀s : PairedFamilyLoop.State F,Cycle E V q (previous s)) (right : ∀s : PairedFamilyLoop.State F,Cycle E V q (current s))
    (join : ∀s,previous (go s)=current s)
    (mark : ∀s,Marked E (previous s) (current s) (current (go s))) (s : PairedFamilyLoop.State F)
    (a : Packet E V (previous s) (current s) (current (go s)))
    (b : Packet E V (previous (go s)) (current (go s)) (current (go (go s))))
    (c : Packet E V (previous (go (go s))) (current (go (go s))) (current (go (go (go s))))) :
    Function.minimalPeriod go s=3 := by
  have h (v : PairedFamilyLoop.State F) := scheduled_return free (left v) (right v)
    (right (go v)) (right (go (go v))) (join v) (mark v) (mark (go v))
  have p := h s a b
  have t := h (go s) b c
  have ret : Function.IsPeriodicPt go 3 s := by
    change go (go (go s))=s
    apply Subtype.ext
    exact Prod.ext ((join _).trans p) (t.trans (join _))
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp ret.minimalPeriod_dvd with one|three
  · have fixed := Function.isPeriodicPt_minimalPeriod go s
    rw [one] at fixed
    have eq : go s=s := fixed
    have diff : previous s≠current s := (mem_filter.mp s.property).2
    exact (diff ((congrArg previous eq).symm.trans (join s))).elim
  · exact three

#print axioms period_three

theorem offset_on_mark {F q E V} (hq : 2≤q) (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {x : ℕ→ℚ} (xp : ∀i∈V,0≤x i) (strict : ∀i∈V,mass V x<WeightedSD.row q E V x i)
    {s t : PairedFamilyLoop.State F} (ca : Cycle E V q (previous s)) (cb : Cycle E V q (current s))
    {send : ↥(previous s) ≃ ↥(previous t)}
    (mark : previous t=current s ∧ ∃b, ∃r : ↥(previous s),
      E b r=false ∧ E b (send r)=true ∧ FullFamilySchedule.Mark q E V x s t send b (send r) r)
    (sz : (RawRepairAlternative.gone s).card=(RawRepairAlternative.gone t).card) :
    let S := V\RawRepairAlternative.gone s
    let T := V\RawRepairAlternative.gone t
    BRsub.Sat q E S → BRsub.Sat q E T → ∀e : ↥S ≃ ↥T,
    (∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) → FlatChildExchange.ExchangePattern E e →
    (∀i j : ↥S,E i j=E (e i) (e j)) →
    let A := previous s
    let B := current s
    let C := current t
    Disjoint (A∩B) (B∩C) ∧ (B\(A∪C)).card+(q+1)=2*(B\C).card ∧
      (∃f,Chain E (A∩B) f) ∧ (∃g,Chain E (B∩C) g) := by
  intro S T ss ts e fix pattern iso A B C
  rcases FlatExchangeChain.on_mark hq free small xp strict ca.sub cb mark sz ss ts e fix pattern with
    ⟨⟨i,j,yes,no⟩,_⟩ | ⟨_,large,f,g,order,_⟩
  · have bad := iso i j
    rw [yes,no] at bad
    contradiction
  · have dis := (FlatExchangeOverlap.on_mark hq free ca cb mark sz e f fix iso large order.leftPath).1
    have join := mark.1
    have eqSize : (A\B).card=(B\C).card := by simpa only [A,B,C,RawRepairAlternative.gone,join] using sz
    have big : q<2*(B\C).card := by simpa only [B,C,RawRepairAlternative.gone,join] using large
    have left : S\T=B\C := by
      ext i
      have b := @cb.sub i
      simp only [A,B,C,S,T,RawRepairAlternative.gone,join,mem_sdiff] at *
      tauto
    have right : T\S=A\B := by
      ext i
      have a := @ca.sub i
      simp only [A,B,C,S,T,RawRepairAlternative.gone,join,mem_sdiff] at *
      tauto
    have uv : A∩B⊆B\C := by
      intro i hi
      refine mem_sdiff.mpr ⟨(mem_inter.mp hi).2,fun hc => ?_⟩
      exact disjoint_left.mp dis hi (mem_inter.mpr ⟨(mem_inter.mp hi).2,hc⟩)
    have rem : (B\C)\(A∩B)=B\(A∪C) := by ext i; simp only [mem_sdiff,mem_inter,mem_union]; tauto
    have countA := card_sdiff_add_card_inter A B
    rw [eqSize,show A.card=q+1 from ca.size] at countA
    have countB := card_sdiff_add_card_inter B C
    rw [show B.card=q+1 from cb.size] at countB
    have rest := card_sdiff_add_card_eq_card uv
    rw [rem] at rest
    have caa : A\(A\B)=A∩B := by ext i; simp only [mem_sdiff,mem_inter]; tauto
    have cbb : B\(B\C)=B∩C := by ext i; simp only [mem_sdiff,mem_inter]; tauto
    have hp : Chain E (B\C) f := left ▸ order.leftPath
    have hq' : Chain E (A\B) g := right ▸ order.rightPath
    have cnA := FlatExchangeOverlap.complement_connected free ca sdiff_subset
      (card_pos.mp (show 0<(A\B).card by omega)) hq'
    have cnB := FlatExchangeOverlap.complement_connected free cb sdiff_subset
      (card_pos.mp (show 0<(B\C).card by omega)) hp
    rw [caa] at cnA
    rw [cbb] at cnB
    obtain ⟨_,_,_,_,_,_,_,_,_,shared,_⟩ := mark
    have live : (B∩C).Nonempty := ⟨_,mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp shared).2).1,(mem_inter.mp shared).1⟩⟩
    have pos := card_pos.mpr live
    exact ⟨dis,by omega,chain_of_connected free ca inter_subset_left (by omega) (card_pos.mp (by omega)) cnA,
      chain_of_connected free cb inter_subset_left (by omega) live cnB⟩

#print axioms offset_on_mark

end LeanCH.BR.Closure.FlatExchangeTriangle
