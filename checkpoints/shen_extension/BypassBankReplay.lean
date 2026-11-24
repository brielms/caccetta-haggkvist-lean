import checkpoints.shen_extension.BypassDegreeDescent

namespace LeanCH.BR.BypassBankReplay
open Finset BRq2 BRq3 BR45 CHRuleCatalog BypassRepair FundedCascade

/-- Deleting one label loses at most one head at each surviving row. -/
theorem order_floor {q r : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (none : NoHost q (r-1)) (two : 2≤r) (free : QFree D V q) (nonempty : V.Nonempty)
    (deg : ∀x∈V,r≤(outN D V x).card) : q*(r-1)+2≤V.card := by
  obtain ⟨a,av⟩ := nonempty
  have large := (deg a av).trans (card_le_card (show outN D V a⊆V from outN_subset))
  have card := card_erase_add_one av
  by_contra! small
  apply none D (V.erase a) (card_pos.mp (by omega)) (by omega) (free.mono_set (erase_subset _ _))
  intro x hx
  have old := deg x (mem_of_mem_erase hx)
  have eq : outN D (V.erase a) x=(outN D V x).erase a := by
    ext j
    simp only [mem_outN,mem_erase]
    tauto
  rw [eq]
  by_cases hit : a∈outN D V x
  · have := card_erase_add_one hit
    omega
  · rw [erase_eq_of_notMem hit]
    omega

structure Cell where
  bank : Finset ℕ
  x : ℕ
  parent : ℕ
  target : ℕ

structure Marked {q r : ℕ} (X : ShenMinimumOrder.Source q r) (m : Cell) : Prop where
  sub : m.bank⊆X.V
  size : m.bank.card=X.V.card-q*(r-1)
  xu : m.x∈X.V\m.bank
  erased : m.parent∈m.bank
  zu : m.target∈X.V\m.bank
  xp : X.D m.x m.parent=true
  pz : X.D m.parent m.target=true
  fresh : X.D m.x m.target≠true
  deficit : (outN X.D (X.V\m.bank) m.x).card+1=r-1
  chain : ∃v : ℕ→ℕ, v 2=m.x ∧ v 1=m.parent ∧
    (∀i,X.D (v (i+1)) (v i)=true) ∧
    ∀a,r≤∑i∈range (q+1),(outN X.D X.V (v (a+i+1))\RemoteParentPacking.missed X.D X.V q (v (a+i))).card

/-- Choose an exact-size bank with a specified erased parent, keeping the
    row and target. Precisely two heads of the row are erased. -/
theorem bank_at_turn {D : CH.Digraph} {V : Finset ℕ} {b r x p z : ℕ}
    (two : 2≤r) (size : 2≤b) (room : b+r≤V.card)
    (off : D x x≠true) (fresh : D x z≠true) (pp : p∈outN D V x)
    (exactDegree : (outN D V x).card=r) :
    ∃B⊆V,B.card=b ∧ p∈B ∧ x∉B ∧ z∉B ∧ (outN D (V\B) x).card+2=r := by
  classical
  let H := outN D V x
  have one : {p}⊆H := singleton_subset_iff.mpr pp
  obtain ⟨T,pt,th,tc⟩ := exists_subsuperset_card_eq one (by simp : ({p}:Finset ℕ).card≤2)
    (show 2≤H.card by simpa only [H,exactDegree] using two)
  let A := V\(H∪{x,z})
  have pairMax : ({x,z}:Finset ℕ).card≤2 := (card_insert_le ..).trans (by simp)
  have both := card_union_le H ({x,z}:Finset ℕ)
  have cap := card_le_card_sdiff_add_card (s:=V) (t:=H∪{x,z})
  have hc : H.card=r := exactDegree
  obtain ⟨F,fa,fc⟩ := exists_subset_card_eq (show b-2≤A.card by dsimp only [A]; omega)
  have dis : Disjoint T F := disjoint_left.mpr (fun j jt jf =>
    (mem_sdiff.mp (fa jf)).2 (mem_union_left _ (th jt)))
  have hx : x∉T∪F := by
    intro hit
    rcases mem_union.mp hit with ht|hf
    · exact off (mem_outN.mp (th ht)).2
    · exact (mem_sdiff.mp (fa hf)).2 (by simp)
  have hz : z∉T∪F := by
    intro hit
    rcases mem_union.mp hit with ht|hf
    · exact fresh (mem_outN.mp (th ht)).2
    · exact (mem_sdiff.mp (fa hf)).2 (by simp)
  have rem : outN D (V\(T∪F)) x = H\T := by
    ext j
    constructor
    · intro hj
      obtain ⟨jv,edge⟩ := mem_outN.mp hj
      exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨(mem_sdiff.mp jv).1,edge⟩,
        fun jt=>(mem_sdiff.mp jv).2 (mem_union_left _ jt)⟩
    · intro hj
      obtain ⟨jh,jt⟩ := mem_sdiff.mp hj
      refine mem_outN.mpr ⟨mem_sdiff.mpr ⟨outN_subset jh,?_⟩,(mem_outN.mp jh).2⟩
      intro erased
      rcases mem_union.mp erased with hit|jf
      · exact jt hit
      · exact (mem_sdiff.mp (fa jf)).2 (mem_union_left _ jh)
  refine ⟨T∪F,union_subset (th.trans outN_subset) (fa.trans sdiff_subset),?_,
    mem_union_left _ (pt (mem_singleton_self _)),hx,hz,?_⟩
  · rw [card_union_of_disjoint dis,tc,fc]; omega
  · rw [rem,card_sdiff_of_subset th,tc,hc]; omega

/-- A physical cell exists on the native source at its own degree and cutoff. -/
theorem exists_mark {q r} (X : ShenMinimumOrder.Source q r) (hq : 2≤q) (hr : 2≤r)
    (room : X.V.card≤q*r) (none : NoHost q (r-1)) : ∃m,Marked X m := by
  obtain ⟨u,uv⟩ := X.nonempty
  obtain ⟨v,_,live,steps,supply⟩ := RemoteParentPacking.every_window X hq (by omega) room uv
  let x := v 2
  let p := v 1
  have xp : X.D x p=true := (steps 1).1
  have xr : (outN X.D X.V x).card=r := (steps 1).2.1
  have pr : (outN X.D X.V p).card=r := (steps 0).2.1
  obtain ⟨z,zu,pz,xz⟩ := candidate_exists (B:=∅) X.free (by omega) (live 1) xp
    (xr.trans_le pr.ge) (by simp)
  let b := X.V.card-q*(r-1)
  have low := order_floor none hr X.free X.nonempty X.degree
  have product := Nat.mul_le_mul_right (r-1) hq
  obtain ⟨B,sub,card,pe,xu,zkeep,deficit⟩ := bank_at_turn (b:=b) hr (by dsimp [b]; omega)
    (by dsimp [b]; omega) (loopfree X.free (by omega) (live 2)) xz
    (mem_outN.mpr ⟨live 1,xp⟩) xr
  change (outN X.D (X.V\B) x).card+2=r at deficit
  have one : (outN X.D (X.V\B) x).card+1=r-1 := by omega
  exact ⟨⟨B,x,p,z⟩,sub,card,mem_sdiff.mpr ⟨live 2,xu⟩,pe,mem_sdiff.mpr ⟨(mem_sdiff.mp zu).1,zkeep⟩,
    xp,pz,xz,one,v,rfl,rfl,fun i=>(steps i).1,supply⟩

structure BankAvailable {q r} (X : ShenMinimumOrder.Source q r) : Prop where
  exists_cell : ∃m,Marked X m

noncomputable def chosen {q r} {X : ShenMinimumOrder.Source q r} (a : BankAvailable X) : Cell :=
  Classical.choose a.exists_cell

@[aesop safe forward (immediate := [hq,hr,order,cover,none]) (rule_sets := [CHGraphFamilies])]
theorem on_source {q r n} {X : ShenMinimumOrder.Source q r} (hq : 2≤q) (hr : 2≤r)
    (order : X.V.card≤n) (cover : n≤q*r) (none : NoHost q (r-1)) : BankAvailable X :=
  ⟨exists_mark X hq hr (order.trans cover) none⟩

@[aesop safe forward (immediate := [available]) (rule_sets := [CHGraphFamilies])]
theorem mark {q r} {X : ShenMinimumOrder.Source q r} (available : BankAvailable X) :
    Marked X (chosen available) := Classical.choose_spec available.exists_cell

@[aesop safe forward (immediate := [available,order,none]) (rule_sets := [CHGraphFamilies])]
theorem terminal_order {q r n} {X : ShenMinimumOrder.Source q r} (available : BankAvailable X)
    (order : X.V.card≤n) (none : NoHost q (r-1)) : q*(r-1)+2≤n := by
  have deficit := (mark available).deficit
  exact (order_floor none (by omega) X.free X.nonempty X.degree).trans order

def JointShort {q r} (X : ShenMinimumOrder.Source q r) (m : Cell) : Prop :=
  ∃j∈X.V\m.bank,j≠m.x ∧ (outN X.D (X.V\m.bank) j).card<r-1

structure LoneBlocked {q r} (X : ShenMinimumOrder.Source q r) (m : Cell) : Prop where
  paid_elsewhere : ∀c∈X.V\m.bank,c≠m.x → r-1≤(outN X.D (X.V\m.bank) c).card
  first_entry :
    let U := X.V\m.bank
    let W := via X.D U m.x m.parent
    let A := active X.D W {m.x} (spare X.D U (r-1))
    m.target∈A (q-1) ∧ m.target∉A (q-2) ∧ spare X.D U (r-1) m.target < (outN X.D (A (q-2)) m.target).card
  unpaid : ∃y∈X.V\m.bank,y≠m.x ∧ X.D y m.x=true ∧ X.D y m.parent≠true ∧
    (outN X.D (X.V\m.bank) y).card=r-1 ∧ (∃h∈m.bank,h≠m.parent ∧ X.D y h=true) ∧
    Walk X.D (via X.D (X.V\m.bank) m.x m.parent) m.target y (q-2)

@[aesop safe forward (immediate := [hq,none,cell]) (rule_sets := [CHGraphFamilies])]
theorem split_bank {q r} {X : ShenMinimumOrder.Source q r} {m}
    (hq : 2≤q) (none : NoHost q (r-1)) (cell : Marked X m) :
    JointShort X m ∨ LoneBlocked X m := by
  classical
  by_cases several : JointShort X m
  · exact Or.inl several
  have rows (c) (cu : c∈X.V\m.bank) (cx : c≠m.x) : r-1≤(outN X.D (X.V\m.bank) c).card :=
    Nat.le_of_not_gt (fun poor=>several ⟨c,cu,cx,poor⟩)
  obtain ⟨on,early,hops,y,yu,yx,arc,yp,eq,walk⟩ := lone_row_law X.free hq none cell.sub
    cell.size.ge cell.xu cell.zu (cell.sub cell.erased) cell.xp cell.pz cell.fresh rows cell.deficit.ge
  have high : r-1<(outN X.D X.V y).card := by
    have deg := X.degree y (mem_sdiff.mp yu).1
    have debt := cell.deficit
    omega
  exact Or.inr ⟨rows,⟨on,early,hops⟩,y,yu,yx,arc,yp,eq,lost_other_label eq.le high yp,walk⟩

ch_family_split_result split_bank
ch_family_split_predicate JointShort

attribute [aesop safe forward (rule_sets := [CHGraphFamilies])]
  LoneBlocked.paid_elsewhere LoneBlocked.first_entry LoneBlocked.unpaid
ch_family_split_result LoneBlocked.unpaid

/-- The general obstruction for simultaneous repairs also acts on any marked bank. -/
structure BankDebt (D : CH.Digraph) (U : Finset ℕ) (q t : ℕ) : Prop where
  witness : ∃u∈U,(outN D U u).card<t ∧
    ((U\active D U (U.filter (fun c=>(outN D U c).card<t)) (spare D U t) (q-1)).filter
      (fun z=>D u z≠true)).card+(outN D U u).card<t

structure Eligible (V B : Finset ℕ) (q t : ℕ) : Prop where
  sub : B⊆V
  size : V.card-q*t≤B.card
  live : (V\B).Nonempty

@[aesop safe forward (immediate := [sub,size,live]) (rule_sets := [CHGraphFamilies])]
theorem eligible {V B : Finset ℕ} {q t : ℕ} (sub : B⊆V) (size : V.card-q*t≤B.card)
    (live : (V\B).Nonempty) : Eligible V B q t := ⟨sub,size,live⟩

@[aesop safe forward (immediate := [cell]) (rule_sets := [CHGraphFamilies])]
theorem marked_bank {q r} {X : ShenMinimumOrder.Source q r} {m}
    (cell : Marked X m) : Eligible X.V m.bank q (r-1) :=
  ⟨cell.sub,cell.size.ge,⟨m.x,cell.xu⟩⟩

/-- Every admissible bank on every q-free carrier is eligible for the joint
    cascade. A native source or parent chain is unnecessary here. -/
@[aesop safe forward (immediate := [free,none,bank]) (rule_sets := [CHGraphFamilies])]
theorem any_bank {D V B q t} (free : QFree D V q) (none : NoHost q t) (bank : Eligible V B q t) :
    BankDebt D (V\B) q t := ⟨forced_row free none bank.sub bank.size bank.live⟩

attribute [aesop safe forward (rule_sets := [CHGraphFamilies])] BankDebt.witness
ch_family_split_result BankDebt.witness

/-- Exact safety on any carrier, including a repaired child with new labels.
    Storing the equivalence keeps both directions available on the same marks. -/
structure Site (D : CH.Digraph) (V U : Finset ℕ) (q x p z : ℕ) : Prop where
  free : QFree D V q
  cutoff : 2≤q
  inside : U⊆V
  start : x∈U
  target : z∈U
  parent : p∈V
  feeds : D p z=true
  fresh : D x z≠true

attribute [aesop safe forward (rule_sets := [CHGraphFamilies])] Site.free

def Off (D : CH.Digraph) (U : Finset ℕ) (q t x p z : ℕ) : Prop :=
  z∉active D (via D U x p) {x} (spare D U t) (q-1)

structure Test (D : CH.Digraph) (U : Finset ℕ) (q x p z : ℕ) : Prop where
  exact_at : ∀t, (∃C : ℕ→Finset ℕ,(∀c∈U,(C c).card≤spare D U t c) ∧
    QFree (DeleteRepair.repair (cut D C) {x} (fun _=>{z})) U q) ↔ Off D U q t x p z

@[aesop safe forward (immediate := [hq,cell]) (rule_sets := [CHGraphFamilies])]
theorem marked_site {q r} {X : ShenMinimumOrder.Source q r} {m} (hq : 2≤q) (cell : Marked X m) :
    Site X.D X.V (X.V\m.bank) q m.x m.parent m.target :=
  ⟨X.free,hq,sdiff_subset,cell.xu,cell.zu,cell.sub cell.erased,cell.pz,cell.fresh⟩

@[aesop safe forward (immediate := [site]) (rule_sets := [CHGraphFamilies])]
theorem test_site {D V U q x p z} (site : Site D V U q x p z) : Test D U q x p z :=
  ⟨fun _=>shortcut_iff site.free site.cutoff site.inside site.start site.target site.parent site.feeds site.fresh⟩

@[aesop safe forward (immediate := [site,xp,clean]) (rule_sets := [CHGraphFamilies])]
theorem clean_site {D V U q t x p z} (site : Site D V U q x p z) (xp : D x p=true)
    (clean : ∀y∈U,D y x=true → D y p≠true → t<(outN D U y).card) : Off D U q t x p z := by
  unfold Off
  rw [clean_active clean,mem_singleton]
  exact target_ne site.free site.cutoff (site.inside site.start) site.parent xp site.feeds

@[aesop safe forward (immediate := [site,off,rows,row]) (rule_sets := [CHGraphFamilies])]
theorem paid_site {D V U q t x p z} (site : Site D V U q x p z) (off : Off D U q t x p z)
    (rows : ∀c∈U,c≠x → t≤(outN D U c).card) (row : t≤(outN D U x).card+1) :
    ∃E : CH.Digraph,QFree E U q ∧ ∀c∈U,t≤(outN E U c).card :=
  shortcut_host site.free site.cutoff site.inside site.target site.parent site.feeds site.fresh rows row off

@[aesop safe forward (immediate := [hq,none,cell,off,rows]) (rule_sets := [CHGraphFamilies])]
theorem paid_exit {q r} {X : ShenMinimumOrder.Source q r} {m} (hq : 2≤q)
    (none : NoHost q (r-1)) (cell : Marked X m)
    (off : Off X.D (X.V\m.bank) q (r-1) m.x m.parent m.target)
    (rows : ∀c∈X.V\m.bank,c≠m.x → r-1≤(outN X.D (X.V\m.bank) c).card) : False := by
  obtain ⟨E,free,deg⟩ := paid_site (marked_site hq cell) off rows cell.deficit.ge
  have card := card_sdiff_add_card_eq_card cell.sub
  have size := cell.size
  exact none E _ ⟨_,cell.xu⟩ (by omega) free deg

#print axioms on_source
#print axioms terminal_order
#print axioms split_bank
#print axioms any_bank
#print axioms clean_site
#print axioms test_site
#print axioms paid_exit
end LeanCH.BR.BypassBankReplay
