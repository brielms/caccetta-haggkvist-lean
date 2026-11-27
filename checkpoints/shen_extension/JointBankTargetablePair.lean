import checkpoints.shen_extension.JointBankLockedPair

/-! Synchronize the common targets with a bank carrying several locked rows. -/
namespace LeanCH.BR.JointTargetablePair
open Finset BRq2 BRq3 BR45 JointFreeTargets JointLockedPair

private theorem locked_iff {D : CH.Digraph} {V : Finset ℕ} {a b c : ℕ}
    (av : a ∈ V) (bv : b ∈ V) :
    c ∈ lockedRows D V (inN D V a ∩ inN D V b) ↔
      c ∈ V ∧ a ∈ sharedHeads D V c ∧ b ∈ sharedHeads D V c := by
  classical
  constructor
  · intro hit
    obtain ⟨cs,allHeads⟩ := mem_filter.mp hit
    obtain ⟨ca,cb⟩ := mem_inter.mp cs
    exact ⟨(mem_inN.mp ca).1,mem_filter.mpr ⟨mem_outN.mpr ⟨av,(mem_inN.mp ca).2⟩,
      fun v fv => (mem_inN.mp (mem_inter.mp (allHeads v fv)).1).2⟩,
      mem_filter.mpr ⟨mem_outN.mpr ⟨bv,(mem_inN.mp cb).2⟩,
      fun v fv => (mem_inN.mp (mem_inter.mp (allHeads v fv)).2).2⟩⟩
  · rintro ⟨cv,ca,cb⟩
    obtain ⟨edgeA,allA⟩ := mem_filter.mp ca
    obtain ⟨edgeB,allB⟩ := mem_filter.mp cb
    exact mem_filter.mpr ⟨mem_inter.mpr ⟨mem_inN.mpr ⟨cv,(mem_outN.mp edgeA).2⟩,
      mem_inN.mpr ⟨cv,(mem_outN.mp edgeB).2⟩⟩,fun v fv => mem_inter.mpr
      ⟨mem_inN.mpr ⟨fv.1,allA v fv⟩,mem_inN.mpr ⟨fv.1,allB v fv⟩⟩⟩

/-- A unique locked row and every one of its free targets see every common
successor of the deleted labels. A free target inside the bank of short rows
can itself be left as the only paid row. -/
theorem singleton_locked_target {D : CH.Digraph} {V : Finset ℕ} {s p h c z : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (zv : z ∈ V) (pz : D p z = true) (hz : D h z = true)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1))
    (single : lockedRows D V (inN D V p ∩ inN D V h) = {c}) :
    z ∈ sharedHeads D V c := by
  classical
  let U := V \ {p,h}
  let S := inN D V p ∩ inN D V h
  let L := lockedRows D V S
  have only : L = {c} := single
  have member : c ∈ L := only ▸ mem_singleton_self c
  have resolve (a : ℕ) (obstruction : (∃ d ∈ ({a} : Finset ℕ), D d z = true) ∨
      ∃ w ∈ outN D U z, ∃ v ∈ outN D U z, w ≠ v ∧
        2 ≤ (outN D U w ∩ {a}).card ∧ 2 ≤ (outN D U v ∩ {a}).card) : D a z = true := by
    rcases obstruction with ⟨d,da,dz⟩ | ⟨w,_,_,_,_,debt,_⟩
    · rwa [mem_singleton.mp da] at dz
    · have small := card_le_card (inter_subset_right : outN D U w ∩ {a} ⊆ {a})
      simp only [card_singleton] at small
      omega
  have obs := locked_obstruction free reg hs pv hv ph zv pz hz room none
  dsimp only at obs
  rw [single] at obs
  refine mem_filter.mpr ⟨mem_outN.mpr ⟨zv,resolve c obs⟩,?_⟩
  intro v fv
  have vs : v ∈ S := (mem_filter.mp member).2 v fv
  let R := S.erase v
  have choices (b) (br : b ∈ R) : ∃ t, FreeTarget D V b t ∧ t ∉ R := by
    by_cases bc : b = c
    · subst b
      exact ⟨v,fv,notMem_erase _ _⟩
    · have outside : b ∉ L := fun bl => bc (mem_singleton.mp (only ▸ bl))
      have bad : ¬ ∀ t, FreeTarget D V b t → t ∈ S :=
        fun h => outside (mem_filter.mpr ⟨(mem_erase.mp br).2,h⟩)
      push Not at bad
      obtain ⟨t,ft,ts⟩ := bad
      exact ⟨t,ft,fun tr => ts (mem_erase.mp tr).2⟩
  have one := remaining_obstruction free reg hs pv hv ph zv pz hz room none
    (show R ⊆ S from erase_subset _ _) choices
  have rest : (inN D V p ∩ inN D V h) \ R = {v} := by
    ext t
    change t ∈ S \ S.erase v ↔ _
    simp only [mem_sdiff,mem_erase,mem_singleton]
    grind
  dsimp only at one
  rw [rest] at one
  exact resolve v one

/-- Enlarge a set of common heads as far as possible while keeping two
covering rows. Its covering rows cannot supply a common parent within that
same set of rows for every pair of their labels. -/
private theorem maximal_heads {V P₀ : Finset ℕ} {K : ℕ → Finset ℕ}
    (loop : ∀ c ∈ V, c ∉ K c) (base : P₀ ⊆ V)
    (two : 2 ≤ (V.filter (fun c => P₀ ⊆ K c)).card) :
    ∃ P ⊆ V, P₀.card ≤ P.card ∧
      (∀ Q ⊆ V, ∀ x ∈ V, ∀ j ∈ V, x ≠ j → Q ⊆ K x → Q ⊆ K j → Q.card ≤ P.card) ∧ ∃ a ∈ V, ∃ b ∈ V, a ≠ b ∧ P ⊆ K a ∧ P ⊆ K b ∧
      ∀ c ∈ V, a ∈ K c → b ∈ K c → ¬ P ⊆ K c := by
  classical
  let W (P : Finset ℕ) := V.filter (fun c => P ⊆ K c)
  let options := V.powerset.filter (fun P => 2 ≤ (W P).card)
  have start : P₀ ∈ options := mem_filter.mpr ⟨mem_powerset.mpr base,two⟩
  obtain ⟨P,pm,best⟩ := options.exists_max_image Finset.card ⟨P₀,start⟩
  obtain ⟨pSub,atLeast⟩ := mem_filter.mp pm
  have sub := mem_powerset.mp pSub
  refine ⟨P,sub,best _ start,?_,?_⟩
  · intro Q qv x xv j jv xj qx qj
    exact best Q (mem_filter.mpr ⟨mem_powerset.mpr qv,one_lt_card.mpr
      ⟨x,mem_filter.mpr ⟨xv,qx⟩,j,mem_filter.mpr ⟨jv,qj⟩,xj⟩⟩)
  by_contra! complete
  have pred {a b} (aW : a ∈ W P) (bW : b ∈ W P) (ab : a ≠ b) :
      ∃ c ∈ W P, a ∈ K c ∧ b ∈ K c := by
    obtain ⟨av,pa⟩ := mem_filter.mp aW
    obtain ⟨bv,pb⟩ := mem_filter.mp bW
    obtain ⟨c,cv,ac,bc,pc⟩ := complete a av b bv ab pa pb
    exact ⟨c,mem_filter.mpr ⟨cv,pc⟩,ac,bc⟩
  obtain ⟨t,tW,u,uW,tu⟩ := one_lt_card.mp atLeast
  obtain ⟨a,aW,ta,_⟩ := pred tW uW tu
  have av := (mem_filter.mp aW).1
  have tv := (mem_filter.mp tW).1
  have at' : a ≠ t := fun eq => loop t tv (eq ▸ ta)
  obtain ⟨b,bW,ab,tb⟩ := pred aW tW at'
  have ba : a ≠ b := fun eq => loop a av (eq ▸ ab)
  have larger (c) (cw : c ∈ W P) (tc : t ∈ K c) : c ∈ W (insert t P) := by
    obtain ⟨cv,pc⟩ := mem_filter.mp cw
    exact mem_filter.mpr ⟨cv,insert_subset_iff.mpr ⟨tc,pc⟩⟩
  have eligible : insert t P ∈ options := mem_filter.mpr
    ⟨mem_powerset.mpr (insert_subset tv sub),one_lt_card.mpr ⟨a,larger a aW ta,b,larger b bW tb,ba⟩⟩
  have fresh : t ∉ P := fun tp => loop t tv ((mem_filter.mp tW).2 tp)
  have more := best _ eligible
  rw [card_insert_of_notMem fresh] at more
  omega

/-- One deleted pair has at least two locked rows and at least two common
targets. For every locked row, some target in the very same set is missed
by it or by one of its free targets. -/
theorem maximal_targetable_locked_pair {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ a ∈ V, ∃ b ∈ V, a ≠ b ∧ ∃ P ⊆ outN D V a ∩ outN D V b, 2 ≤ P.card ∧
      (∀ Q ⊆ V, ∀ x ∈ V, ∀ j ∈ V, x ≠ j → Q ⊆ sharedHeads D V x →
        Q ⊆ sharedHeads D V j → Q.card ≤ P.card) ∧
      let L := lockedRows D V (inN D V a ∩ inN D V b)
      2 ≤ L.card ∧ ∀ c ∈ L, ∃ z ∈ P, z ∉ sharedHeads D V c := by
  classical
  let K := sharedHeads D V
  have edge {c v} (hit : v ∈ K c) : v ∈ outN D V c := (mem_filter.mp hit).1
  obtain ⟨p,pv,h,hv,ph,two⟩ := exists_two_locked free reg hs room none
  let P₀ : Finset ℕ := {p,h}
  have init : 2 ≤ (V.filter (fun c => P₀ ⊆ K c)).card := by
    apply two.trans (card_le_card ?_)
    intro c cm
    obtain ⟨cv,cp,ch⟩ := (locked_iff pv hv).mp cm
    exact mem_filter.mpr ⟨cv,insert_subset_iff.mpr ⟨cp,singleton_subset_iff.mpr ch⟩⟩
  obtain ⟨P,sub,size,best,a,av,b,bv,ab,pa,pb,miss⟩ := maximal_heads
    (fun c cv cc => loopfree free (by decide) cv (mem_outN.mp (edge cc)).2)
    (show P₀ ⊆ V from insert_subset pv (singleton_subset_iff.mpr hv)) init
  have count : 2 ≤ P.card := (show P₀.card = 2 from card_pair ph) ▸ size
  let L := lockedRows D V (inN D V a ∩ inN D V b)
  have obstruction (c) (cm : c ∈ L) : ∃ z ∈ P, z ∉ K c := by
    obtain ⟨cv,ca,cb⟩ := (locked_iff av bv).mp cm
    exact not_subset.mp (miss c cv ca cb)
  refine ⟨a,av,b,bv,ab,P,fun z zp => mem_inter.mpr ⟨edge (pa zp),edge (pb zp)⟩,
    count,best,?_,obstruction⟩
  obtain ⟨c,cv,ca,cb⟩ := pair_covered free reg hs av bv ab room none
  have cm : c ∈ L := (locked_iff av bv).mpr ⟨cv,ca,cb⟩
  by_contra! few
  change L.card < 2 at few
  have only : L = {c} := eq_of_subset_of_card_le (singleton_subset_iff.mpr cm)
    (by simpa using (show L.card ≤ 1 by omega)) |>.symm
  obtain ⟨z,zp,cz⟩ := obstruction c cm
  exact cz (singleton_locked_target free reg hs av bv ab (sub zp)
    (mem_outN.mp (edge (pa zp))).2 (mem_outN.mp (edge (pb zp))).2 room none only)

theorem targetable_locked_pair {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ a ∈ V, ∃ b ∈ V, a ≠ b ∧ ∃ P ⊆ outN D V a ∩ outN D V b, 2 ≤ P.card ∧
      let L := lockedRows D V (inN D V a ∩ inN D V b)
      2 ≤ L.card ∧ ∀ c ∈ L, ∃ z ∈ P, z ∉ sharedHeads D V c := by
  obtain ⟨a,av,b,bv,ab,P,sub,pc,_,rest⟩ := maximal_targetable_locked_pair free reg hs room none
  exact ⟨a,av,b,bv,ab,P,sub,pc,rest⟩

/-- With the target set and bank held fixed, each locked row supplies a
capstone mark either at itself or at one of its own free targets. -/
theorem marked_repair_choices {s : ℕ} (X : ShenMinimumOrder.Source 3 s)
    (reg : OutEq s X.D X.V) (hs : 2 ≤ s) (room : X.V.card = 3*(s-1)+2)
    (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ p ∈ X.V, ∃ h ∈ X.V, p ≠ h ∧ ∃ P ⊆ outN X.D X.V p ∩ outN X.D X.V h,
      2 ≤ P.card ∧ let L := lockedRows X.D X.V (inN X.D X.V p ∩ inN X.D X.V h)
      2 ≤ L.card ∧ ∀ c ∈ L, ∃ z ∈ P, ∃ x, (x = c ∨ FreeTarget X.D X.V c x) ∧
        BypassBankReplay.Marked X ⟨{p,h},x,p,z⟩ ∧ BypassBankReplay.JointShort X ⟨{p,h},x,p,z⟩ := by
  classical
  obtain ⟨p,pv,h,hv,ph,P,sub,pc,two,obstruction⟩ := targetable_locked_pair X.free reg hs room none
  let B : Finset ℕ := {p,h}
  let U := X.V \ B
  let S := inN X.D X.V p ∩ inN X.D X.V h
  let L := lockedRows X.D X.V S
  have short (a) (as : a ∈ S) : a ∈ U ∧ (outN X.D U a).card < s-1 := by
    have eq := BypassBankReplay.short_rows_eq_jointParents X.free (by decide) reg pv hv ph hs
    obtain ⟨ap,ah⟩ := mem_inter.mp as
    have hit : a ∈ BypassBankReplay.jointParents X.D X.V p h :=
      mem_inN.mpr ⟨ap,(mem_inN.mp ah).2⟩
    rw [←eq] at hit
    exact mem_filter.mp hit
  refine ⟨p,pv,h,hv,ph,P,sub,pc,two,?_⟩
  intro c cl
  obtain ⟨z,zp,notShared⟩ := obstruction c cl
  obtain ⟨zpEdge,zhEdge⟩ := mem_inter.mp (sub zp)
  obtain ⟨zv,pz⟩ := mem_outN.mp zpEdge
  have hz := (mem_outN.mp zhEdge).2
  obtain ⟨cs,allShort⟩ := mem_filter.mp cl
  have witness : ∃ x ∈ S, (x = c ∨ FreeTarget X.D X.V c x) ∧ X.D x z ≠ true := by
    by_cases ed : X.D c z = true
    · have bad : ¬ ∀ v, FreeTarget X.D X.V c v → X.D v z = true :=
        fun hh => notShared (mem_filter.mpr ⟨mem_outN.mpr ⟨zv,ed⟩,hh⟩)
      push Not at bad
      obtain ⟨v,fv,miss⟩ := bad
      exact ⟨v,allShort v fv,Or.inr fv,miss⟩
    · exact ⟨c,cs,Or.inl rfl,ed⟩
  obtain ⟨x,xs,rel,xz⟩ := witness
  have large : 2 ≤ S.card := two.trans (card_le_card (filter_subset _ _))
  obtain ⟨j,jm⟩ := card_pos.mp (show 0 < (S.erase x).card by rw [card_erase_of_mem xs]; omega)
  obtain ⟨jx,js⟩ := mem_erase.mp jm
  obtain ⟨xp,xh⟩ := mem_inter.mp xs
  obtain ⟨xv,exP⟩ := mem_inN.mp xp
  have bc : B.card = 2 := card_pair ph
  have deficit : (outN X.D U x).card+1 = s-1 := by
    have both : B ⊆ outN X.D X.V x := insert_subset_iff.mpr
      ⟨mem_outN.mpr ⟨pv,exP⟩,singleton_subset_iff.mpr (mem_outN.mpr ⟨hv,(mem_inN.mp xh).2⟩)⟩
    have eq : outN X.D U x = outN X.D X.V x \ B := by
      ext w; simp only [U,mem_sdiff,mem_outN]; tauto
    have count := card_sdiff_add_card_inter (outN X.D X.V x) B
    rw [inter_eq_right.mpr both,bc,reg x xv] at count
    rw [eq]
    omega
  have znP : z ≠ p := fun eq => loopfree X.free (by decide) pv (eq ▸ pz)
  have znH : z ≠ h := fun eq => loopfree X.free (by decide) hv (eq ▸ hz)
  refine ⟨z,zp,x,rel,?_,j,(short j js).1,jx,(short j js).2⟩
  exact ⟨insert_subset pv (singleton_subset_iff.mpr hv),by change B.card = _; omega,
    (short x xs).1,by simp,mem_sdiff.mpr ⟨zv,by simp [znP,znH]⟩,exP,pz,xz,deficit,
    BypassBankReplay.chain_through_arc X (by decide) (by omega) reg (by omega) xv pv zv exP pz⟩

/-- Add one free arc to a row at most one below the floor. -/
private theorem add_one {D : CH.Digraph} {U : Finset ℕ} {c v t : ℕ}
    (safe : QFree D U 3) (fv : FreeTarget D U c v) (need : t ≤ (outN D U c).card+1) :
    let E := addTargets D {c} (fun _ => v)
    QFree E U 3 ∧ U.filter (fun u => (outN E U u).card < t) =
      (U.filter (fun u => (outN D U u).card < t)).erase c := by
  classical
  have head (a) (am : a ∈ ({c} : Finset ℕ)) : FreeTarget D U a v ∧ v ∉ ({c} : Finset ℕ) := by
    obtain rfl := mem_singleton.mp am
    exact ⟨fv,fun vc => fv.2.1 (mem_singleton.mp vc)⟩
  obtain ⟨ok,rows⟩ := free_repair (f := fun _ => v) safe head
  refine ⟨ok,?_⟩
  ext u
  by_cases uc : u = c
  · subst u; simp [rows,not_lt_of_ge need]
  · simp [rows,uc]

/-- A free row and a different row missing a common target are paid in one
graph, including when the free arc ends at the paid row. -/
theorem repair_two {D : CH.Digraph} {V : Finset ℕ} {s p h z x c v : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (pv : p ∈ V) (hv : h ∈ V)
    (ph : p ≠ h) (zv : z ∈ V) (pz : D p z = true) (hz : D h z = true)
    (xs : x ∈ inN D V p ∩ inN D V h) (cs : c ∈ inN D V p ∩ inN D V h)
    (cx : c ≠ x) (xz : D x z ≠ true) (fv : FreeTarget D V c v) :
    let U := V \ {p,h}
    let S := inN D V p ∩ inN D V h
    ∃ G : CH.Digraph, QFree G U 3 ∧
      U.filter (fun u => (outN G U u).card < s-1) = (S.erase x).erase c := by
  classical
  let U := V \ {p,h}
  let E := JointFreshRepair.edit D {x} z z
  obtain ⟨ok,short⟩ := JointFreshRepair.repair_one free reg hs pv hv ph zv pz hz xs xz
  obtain ⟨cv,cp⟩ := mem_inN.mp (mem_inter.mp cs).1
  have cz : c ≠ z := fun eq => digonfree free (by decide) pv zv pz (eq ▸ cp)
  have zc : D z c ≠ true := fun ed => free c 3 (by decide) (by decide)
    (.step pv cp (.step zv pz (.step cv ed (.refl _))))
  have off : c ∉ ({x} : Finset ℕ) := fun H => cx (mem_singleton.mp H)
  have row : outN E U c = outN D U c := by
    ext w; simp [E,JointFreshRepair.edit,mem_outN,off,cz,zc]
  have need : s-1 ≤ (outN E U c).card+1 := row ▸ retained_floor reg cv ph
  obtain ⟨safe,eq⟩ := add_one ok
    (free_after_edit (retained_target cs fv) off cz zc) need
  exact ⟨_,safe,eq.trans (congrArg (fun T : Finset ℕ => T.erase c) short)⟩

/-- On one common bank every short row admits an edit removing exactly that
row from the short set. Saturated rows use a target from the same set P. -/
theorem all_rows_repairable {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ p ∈ V, ∃ h ∈ V, p ≠ h ∧ ∃ P ⊆ outN D V p ∩ outN D V h, 2 ≤ P.card ∧
      let U := V \ {p,h}
      let S := inN D V p ∩ inN D V h
      2 ≤ (lockedRows D V S).card ∧ (∀ c ∈ lockedRows D V S, ∃ z ∈ P, z ∉ sharedHeads D V c) ∧
      ∀ c ∈ S, ∃ E : CH.Digraph, QFree E U 3 ∧
        U.filter (fun u => (outN E U u).card < s-1) = S.erase c := by
  classical
  obtain ⟨p,pv,h,hv,ph,P,sub,pc,lockedCount,miss⟩ := targetable_locked_pair free reg hs room none
  let U := V \ {p,h}
  let S := inN D V p ∩ inN D V h
  have short : U.filter (fun u => (outN D U u).card < s-1) = S := by
    rw [BypassBankReplay.short_rows_eq_jointParents free (by decide) reg pv hv ph hs]
    ext w
    simp only [S,BypassBankReplay.jointParents,mem_inN,mem_inter]
    tauto
  refine ⟨p,pv,h,hv,ph,P,sub,pc,lockedCount,miss,?_⟩
  intro c cs
  by_cases has : ∃ v, FreeTarget D V c v
  · obtain ⟨v,fv⟩ := has
    obtain ⟨ok,eq⟩ := add_one (free.mono_set (show U ⊆ V from sdiff_subset))
      (retained_target cs fv) (retained_floor reg (mem_inN.mp (mem_inter.mp cs).1).1 ph)
    exact ⟨_,ok,eq.trans (congrArg (fun T : Finset ℕ => T.erase c) short)⟩
  · have cl : c ∈ lockedRows D V S :=
      mem_filter.mpr ⟨cs,fun v fv => False.elim (has ⟨v,fv⟩)⟩
    obtain ⟨z,zp,off⟩ := miss c cl
    obtain ⟨ez,ez'⟩ := mem_inter.mp (sub zp)
    obtain ⟨zv,pz⟩ := mem_outN.mp ez
    have fresh : D c z ≠ true := fun cz => off (mem_filter.mpr
      ⟨mem_outN.mpr ⟨zv,cz⟩,fun v fv => False.elim (has ⟨v,fv⟩)⟩)
    exact ⟨_,JointFreshRepair.repair_one free reg hs pv hv ph zv pz
      (mem_outN.mp ez').2 cs fresh⟩

/-- Either all short rows on the chosen bank are saturated, or one actual
triangle-free edit removes exactly two distinct shortages. On this same bank
each individual shortage can always be removed on its own. -/
theorem simultaneous_or_saturated {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ p ∈ V, ∃ h ∈ V, p ≠ h ∧ ∃ P ⊆ outN D V p ∩ outN D V h, 2 ≤ P.card ∧
      let U := V \ {p,h}
      let S := inN D V p ∩ inN D V h
      let repaired := fun T : Finset ℕ => ∃ E : CH.Digraph, QFree E U 3 ∧
        U.filter (fun u => (outN E U u).card < s-1) = T
      2 ≤ (lockedRows D V S).card ∧ (∀ c ∈ S, repaired (S.erase c)) ∧
        ((∀ c ∈ S, ∀ v, ¬ FreeTarget D V c v) ∨
        ∃ x ∈ S, ∃ c ∈ S, c ≠ x ∧ repaired ((S.erase x).erase c)) := by
  classical
  obtain ⟨p,pv,h,hv,ph,P,sub,pc,two,miss,each⟩ := all_rows_repairable free reg hs room none
  let S := inN D V p ∩ inN D V h
  let L := lockedRows D V S
  have lx : L ⊆ S := filter_subset _ _
  refine ⟨p,pv,h,hv,ph,P,sub,pc,two,each,?_⟩
  by_cases frozen : ∀ c ∈ S, ∀ v, ¬ FreeTarget D V c v
  · exact Or.inl frozen
  right
  push Not at frozen
  obtain ⟨u,us,v,fv⟩ := frozen
  have pair : ∃ x ∈ S, ∃ z ∈ P, D x z ≠ true ∧ ∃ c ∈ S, c ≠ x ∧ ∃ y, FreeTarget D V c y := by
    have large : 2 ≤ L.card := two
    have nonempty : (L.erase u).Nonempty := by
      by_cases ul : u ∈ L
      · exact card_pos.mp (by rw [card_erase_of_mem ul]; omega)
      · rw [erase_eq_of_notMem ul]; exact card_pos.mp (by omega)
    obtain ⟨a,am⟩ := nonempty
    obtain ⟨au,al⟩ := mem_erase.mp am
    obtain ⟨z,zp,off⟩ := miss a al
    by_cases az : D a z = true
    · have bad : ¬ ∀ y, FreeTarget D V a y → D y z = true := fun allHit =>
        off (mem_filter.mpr ⟨mem_outN.mpr ⟨(mem_outN.mp (mem_inter.mp (sub zp)).1).1,az⟩,allHit⟩)
      push Not at bad
      obtain ⟨y,fy,yz⟩ := bad
      exact ⟨y,(mem_filter.mp al).2 y fy,z,zp,yz,a,lx al,fy.2.1.symm,y,fy⟩
    · exact ⟨a,lx al,z,zp,az,u,us,au.symm,v,fv⟩
  obtain ⟨x,xs,z,zp,xz,c,cs,cx,y,fy⟩ := pair
  obtain ⟨ep,eh⟩ := mem_inter.mp (sub zp)
  obtain ⟨zv,pz⟩ := mem_outN.mp ep
  exact ⟨x,xs,c,cs,cx,repair_two free reg hs pv hv ph zv pz (mem_outN.mp eh).2 xs cs cx xz fy⟩

#print axioms simultaneous_or_saturated
#print axioms repair_two
#print axioms all_rows_repairable
#print axioms marked_repair_choices
#print axioms singleton_locked_target
#print axioms maximal_targetable_locked_pair
#print axioms targetable_locked_pair
end LeanCH.BR.JointTargetablePair
