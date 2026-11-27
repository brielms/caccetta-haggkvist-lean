import checkpoints.shen_extension.JointBankTargetablePair
import checkpoints.shen_extension.TwoRowSharedBlockers

/-! The maximum in the targetable-pair selection supplies distinct targets on the
same bank. A pair of short rows with such targets forces three shared blockers. -/

namespace LeanCH.BR.MaximalBankTwoRows
open Finset BRq2 BRq3 BR45 JointFreeTargets JointTargetablePair TwoRowShared

abbrev Maximum (D : CH.Digraph) (V P : Finset ℕ) : Prop :=
  ∀ Q ⊆ V, ∀ x ∈ V, ∀ j ∈ V, x ≠ j → Q ⊆ sharedHeads D V x →
    Q ⊆ sharedHeads D V j → Q.card ≤ P.card

/-- Two locked rows certify every head seen by all short rows. The bank labels
are two such heads outside P, so the rows must collectively miss two labels in P. -/
theorem two_misses {D : CH.Digraph} {V P : Finset ℕ} {a b : ℕ}
    (free : QFree D V 3) (av : a ∈ V) (bv : b ∈ V) (ab : a ≠ b)
    (sub : P ⊆ outN D V a ∩ outN D V b) (best : Maximum D V P)
    (two : 2 ≤ (lockedRows D V (inN D V a ∩ inN D V b)).card) :
    2 ≤ (P.filter (fun y => ∃ c ∈ inN D V a ∩ inN D V b, D c y ≠ true)).card := by
  classical
  let S := inN D V a ∩ inN D V b
  let G := P.filter (fun y => ∀ c ∈ S, D c y = true)
  let Q := insert a (insert b G)
  have gv : G ⊆ V := fun y hy => (mem_outN.mp (mem_inter.mp (sub (mem_filter.mp hy).1)).1).1
  have allHead {z} (zq : z ∈ Q) (c) (cs : c ∈ S) : D c z = true := by
    rcases mem_insert.mp zq with rfl | q
    · exact (mem_inN.mp (mem_inter.mp cs).1).2
    rcases mem_insert.mp q with rfl | zg
    · exact (mem_inN.mp (mem_inter.mp cs).2).2
    · exact (mem_filter.mp zg).2 c cs
  have qv : Q ⊆ V := insert_subset av (insert_subset bv gv)
  have certified {c} (cl : c ∈ lockedRows D V S) : Q ⊆ sharedHeads D V c := by
    intro z zq
    obtain ⟨cs,lock⟩ := mem_filter.mp cl
    exact mem_filter.mpr ⟨mem_outN.mpr ⟨qv zq,allHead zq _ cs⟩,
      fun v fv => allHead zq v (lock v fv)⟩
  obtain ⟨x,xl,j,jl,xj⟩ := one_lt_card.mp two
  have cv {c} (cl : c ∈ lockedRows D V S) : c ∈ V :=
    (mem_inN.mp (mem_inter.mp (mem_filter.mp cl).1).1).1
  have bound := best Q qv x (cv xl) j (cv jl) xj (certified xl) (certified jl)
  have an : a ∉ G := fun am => loopfree free (by decide) av
    (mem_outN.mp (mem_inter.mp (sub (mem_filter.mp am).1)).1).2
  have bn : b ∉ G := fun bm => loopfree free (by decide) bv
    (mem_outN.mp (mem_inter.mp (sub (mem_filter.mp bm).1)).2).2
  have qc : Q.card = G.card + 2 := by simp [Q,ab,an,bn,Nat.add_assoc]
  have eq : P.filter (fun y => ∃ c ∈ S, D c y ≠ true) = P \ G := by
    ext y
    simp [G]
    tauto
  change 2 ≤ (P.filter (fun y => ∃ c ∈ S, D c y ≠ true)).card
  rw [eq,card_sdiff_of_subset (show G ⊆ P from filter_subset _ _)]
  omega

private theorem bank_size {V : Finset ℕ} {a b t : ℕ} (av : a ∈ V) (bv : b ∈ V)
    (ab : a ≠ b) (order : V.card = 3*t+2) : (V \ {a,b}).card ≤ 3*t := by
  rw [card_sdiff_of_subset (insert_subset av (singleton_subset_iff.mpr bv)),card_pair ab,order]
  omega

/-- Each of the two short rows must itself miss a selected target. If it saw
all of them, its selection witness would give it a free arc and a different
short row missing a target. The existing two-row edit would repair both. -/
private theorem native_miss {D : CH.Digraph} {V P : Finset ℕ} {t a b x j : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (av : a ∈ V) (bv : b ∈ V) (ab : a ≠ b) (sub : P ⊆ outN D V a ∩ outN D V b)
    (exactS : inN D V a ∩ inN D V b = {x,j}) (xj : x ≠ j)
    (lock : x ∈ lockedRows D V (inN D V a ∩ inN D V b))
    (miss : ∃ z ∈ P, z ∉ sharedHeads D V x) : ∃ z ∈ P, D x z ≠ true := by
  classical
  obtain ⟨z,zp,bad⟩ := miss
  obtain ⟨az,bz⟩ := mem_inter.mp (sub zp)
  obtain ⟨zv,az⟩ := mem_outN.mp az
  by_cases xz : D x z = true
  · have holes : ¬ ∀ v, FreeTarget D V x v → D v z = true :=
      fun h => bad (mem_filter.mpr ⟨mem_outN.mpr ⟨zv,xz⟩,h⟩)
    push Not at holes
    obtain ⟨v,fv,vz⟩ := holes
    have vs := (mem_filter.mp lock).2 v fv
    have vj : v = j := by
      rw [exactS] at vs
      simpa [fv.2.1] using vs
    subst v
    exact False.elim (vz (other_row_hits_target free reg (by omega) av bv ab zv az
      (mem_outN.mp bz).2 (by simpa using order) (by simpa using no) exactS xj ⟨j,fv⟩))
  · exact ⟨z,zp,xz⟩

/-- On this same selected bank the two rows admit distinct fresh targets. -/
theorem distinct_targets {D : CH.Digraph} {V P : Finset ℕ} {t a b x j : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (av : a ∈ V) (bv : b ∈ V) (ab : a ≠ b) (sub : P ⊆ outN D V a ∩ outN D V b)
    (best : Maximum D V P)
    (two : 2 ≤ (lockedRows D V (inN D V a ∩ inN D V b)).card)
    (miss : ∀ c ∈ lockedRows D V (inN D V a ∩ inN D V b), ∃ z ∈ P, z ∉ sharedHeads D V c)
    (xj : x ≠ j) (exactS : inN D V a ∩ inN D V b = {x,j}) :
    ∃ p ∈ P, ∃ y ∈ P, p ≠ y ∧ D x p ≠ true ∧ D j y ≠ true := by
  classical
  let L := lockedRows D V (inN D V a ∩ inN D V b)
  have ls : L ⊆ inN D V a ∩ inN D V b := filter_subset _ _
  have eq : L = inN D V a ∩ inN D V b := eq_of_subset_of_card_le ls (by
    rw [exactS,card_pair xj]; exact two)
  have xl : x ∈ L := by simp [eq,exactS]
  have jl : j ∈ L := by simp [eq,exactS]
  obtain ⟨p,pp,xp⟩ := native_miss free reg ht order no av bv ab sub exactS xj xl (miss x xl)
  obtain ⟨y,yp,jy⟩ := native_miss free reg ht order no av bv ab sub
    (exactS.trans (pair_comm x j)) xj.symm jl (miss j jl)
  by_cases py : p = y
  · subst y
    obtain ⟨c,hc,d,hd,cd⟩ := one_lt_card.mp (two_misses free av bv ab sub best two)
    have extra : ∃ z ∈ P, z ≠ p ∧ (D x z ≠ true ∨ D j z ≠ true) := by
      have pick {z} (hm : z ∈ P.filter (fun y => ∃ c ∈ inN D V a ∩ inN D V b, D c y ≠ true))
          (zp : z ≠ p) : ∃ z ∈ P, z ≠ p ∧ (D x z ≠ true ∨ D j z ≠ true) := by
        obtain ⟨zP,r,rs,rz⟩ := mem_filter.mp hm
        rw [exactS] at rs
        rcases mem_insert.mp rs with rfl | rs
        · exact ⟨z,zP,zp,Or.inl rz⟩
        · exact ⟨z,zP,zp,Or.inr (mem_singleton.mp rs ▸ rz)⟩
      by_cases cp : c = p
      · exact pick hd (fun h => cd (cp.trans h.symm))
      · exact pick hc cp
    obtain ⟨z,zp,ne,h | h⟩ := extra
    · exact ⟨z,zp,p,pp,ne,h,jy⟩
    · exact ⟨p,pp,z,zp,ne.symm,xp,h⟩
  · exact ⟨p,pp,y,yp,py,xp,jy⟩

/-- A blocker shared by the two proposed edits lies on both return paths. -/
def blockers (D : CH.Digraph) (U : Finset ℕ) (x j p y : ℕ) : Finset ℕ :=
  (outN D U p).filter (fun m => D y m = true ∧ D m x = true ∧ D m j = true)

/-- Any assignment of distinct fresh common targets to the two short rows
forces at least three of the very same return middles. -/
theorem three_blockers {D : CH.Digraph} {V : Finset ℕ} {t a b x j p y : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (av : a ∈ V) (bv : b ∈ V) (ab : a ≠ b) (xj : x ≠ j)
    (exactS : inN D V a ∩ inN D V b = {x,j})
    (pP : p ∈ outN D V a ∩ outN D V b) (yP : y ∈ outN D V a ∩ outN D V b)
    (py : p ≠ y) (xp : D x p ≠ true) (jy : D j y ≠ true) :
    3 ≤ (blockers D (V \ {a,b}) x j p y).card := by
  classical
  let B : Finset ℕ := {a,b}
  let U := V \ B
  have bank : B ⊆ V := insert_subset av (singleton_subset_iff.mpr bv)
  have parents (c) (cs : c ∈ inN D V a ∩ inN D V b) :
      c ∈ U ∧ D c a = true := by
    obtain ⟨ca,cb⟩ := mem_inter.mp cs
    obtain ⟨cv,ca⟩ := mem_inN.mp ca
    have na : c ≠ a := fun e => loopfree free (by decide) av (e ▸ ca)
    have nb : c ≠ b := fun e => loopfree free (by decide) bv (e ▸ (mem_inN.mp cb).2)
    exact ⟨mem_sdiff.mpr ⟨cv,by simp [B,na,nb]⟩,ca⟩
  obtain ⟨xu,xa⟩ := parents x (by simp [exactS])
  obtain ⟨ju,ja⟩ := parents j (by simp [exactS])
  have target (z) (zs : z ∈ outN D V a ∩ outN D V b) :
      z ∈ U ∧ (∀ k ∈ B, D k z = true) ∧
      z ≠ x ∧ z ≠ j ∧ D z x ≠ true ∧ D z j ≠ true := by
    obtain ⟨az,bz⟩ := mem_inter.mp zs
    obtain ⟨zv,az⟩ := mem_outN.mp az
    have bz := (mem_outN.mp bz).2
    have na : z ≠ a := fun e => loopfree free (by decide) av (e ▸ az)
    have nb : z ≠ b := fun e => loopfree free (by decide) bv (e ▸ bz)
    have off {c} (cu : c ∈ U) (ca : D c a = true) : z ≠ c ∧ D z c ≠ true := by
      have cv := (mem_sdiff.mp cu).1
      exact ⟨fun e => digonfree free (by decide) cv av ca (e ▸ az),
        fun zc => free c 3 (by decide) (by decide) (.step av ca (.step zv az (.step cv zc (.refl _))))⟩
    refine ⟨mem_sdiff.mpr ⟨zv,by simp [B,na,nb]⟩,?_,(off xu xa).1,(off ju ja).1,
      (off xu xa).2,(off ju ja).2⟩
    intro k km
    rcases mem_insert.mp km with rfl | km
    · exact az
    · exact mem_singleton.mp km ▸ bz
  obtain ⟨pu,cp,pnx,pnj,px,pj⟩ := target p pP
  obtain ⟨yu,cy,ynx,ynj,yx,yj⟩ := target y yP
  obtain ⟨rp,sp⟩ := bank_rich free reg bank pu cp
  obtain ⟨ry,sy⟩ := bank_rich free reg bank yu cy
  have short : U.filter (fun i => (outN D U i).card < t+1-1) = {x,j} := by
    rw [BypassBankReplay.short_rows_eq_jointParents free (by decide) reg av bv ab (by omega),← exactS]
    ext k
    simp only [BypassBankReplay.jointParents,mem_inN,mem_inter]
    tauto
  have floor (i) (iu : i ∈ U) (ix : i ≠ x) (ij : i ≠ j) : t ≤ (outN D U i).card := by
    by_contra! small
    have hit : i ∈ U.filter (fun k => (outN D U k).card < t+1-1) := mem_filter.mpr ⟨iu,by simpa using small⟩
    rw [short] at hit
    simp [ix,ij] at hit
  by_contra! few
  let K := blockers D U x j p y
  change K.card < 3 at few
  change (outN D U p).card = t+1 at rp
  have ks : K ⊆ outN D U p := filter_subset _ _
  obtain ⟨T,kT,Tp,tc⟩ := exists_subsuperset_card_eq ks (show K.card ≤ 2 by omega)
    (show 2 ≤ (outN D U p).card by omega)
  obtain ⟨u,w,_,eq⟩ := card_eq_two.mp tc
  subst T
  have pu' := (mem_outN.mp (Tp (show u ∈ {u,w} by simp))).2
  have pw := (mem_outN.mp (Tp (show w ∈ {u,w} by simp))).2
  obtain ⟨E,safe,_,_,rows⟩ := two_target_repair (free.mono_set (show U ⊆ V from sdiff_subset))
    xu ju pu yu xj py pnx pnj ynx ynj xp px pj jy yj yx pu' pw
    (fun m mu pm ym mx mj => by
      have mk : m ∈ K := mem_filter.mpr ⟨mem_outN.mpr ⟨mu,pm⟩,ym,mx,mj⟩
      simpa using kT mk)
    (by simpa using retained_floor reg (mem_sdiff.mp xu).1 ab)
    (by simpa using retained_floor reg (mem_sdiff.mp ju).1 ab)
    rp.ge ry.ge (fun m mu arc => (sp m mu arc).ge) (fun m mu arc => (sy m mu arc).ge) floor
  exact no E U ⟨x,xu⟩ (bank_size av bv ab order) safe rows


/-- The two short rows agree on every common bank target, including targets
outside the maximizer. An asymmetric arc would close a triangle with every
shared blocker in a suitable assignment. -/
theorem common_target_agreement {D : CH.Digraph} {V : Finset ℕ} {t a b x j p y : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (av : a ∈ V) (bv : b ∈ V) (ab : a ≠ b) (xj : x ≠ j)
    (exactS : inN D V a ∩ inN D V b = {x,j})
    (pP : p ∈ outN D V a ∩ outN D V b) (yP : y ∈ outN D V a ∩ outN D V b)
    (xp : D x p ≠ true) (jy : D j y ≠ true) :
    ∀ z ∈ outN D V a ∩ outN D V b, D x z = D j z := by
  classical
  let U := V \ {a,b}
  have xv : x ∈ V := (mem_inN.mp (mem_inter.mp
    (show x ∈ inN D V a ∩ inN D V b by simp [exactS])).1).1
  have jv : j ∈ V := (mem_inN.mp (mem_inter.mp
    (show j ∈ inN D V a ∩ inN D V b by simp [exactS])).1).1
  have cross {r s} (rP : r ∈ outN D V a ∩ outN D V b) (sP : s ∈ outN D V a ∩ outN D V b)
      (rs : r ≠ s) (xr : D x r ≠ true) (js : D j s ≠ true) :
      D j r ≠ true ∧ D x s ≠ true := by
    have three := three_blockers free reg ht order no av bv ab xj exactS rP sP rs xr js
    obtain ⟨m,mm⟩ := card_pos.mp (show 0 < (blockers D U x j r s).card from lt_of_lt_of_le (by decide : 0 < 3) three)
    obtain ⟨rm,sm,mx,mj⟩ := mem_filter.mp mm
    obtain ⟨mu,rm⟩ := mem_outN.mp rm
    have mv := (mem_sdiff.mp mu).1
    have rv := (mem_outN.mp (mem_inter.mp rP).1).1
    have sv := (mem_outN.mp (mem_inter.mp sP).1).1
    exact ⟨fun jr => free r 3 (by decide) (by decide)
      (.step mv rm (.step jv mj (.step rv jr (.refl _)))),
      fun xs => free s 3 (by decide) (by decide)
      (.step mv sm (.step xv mx (.step sv xs (.refl _))))⟩
  intro z zs
  by_cases xz : D x z = true
  · by_cases jz : D j z = true
    · exact xz.trans jz.symm
    · have pz : p ≠ z := fun e => xp (e ▸ xz)
      exact False.elim ((cross pP zs pz xp jz).2 xz)
  · by_cases jz : D j z = true
    · have zy : z ≠ y := fun e => jy (e ▸ jz)
      exact False.elim ((cross zs yP zy xz jy).1 jz)
    · simp_all

/-- On the selected source bank with exactly two short rows, at least two
selected common targets are jointly missed. Every pair of jointly missed common
targets, even outside P, has at least three shared return middles. -/
theorem selected_two_row_obstruction {D : CH.Digraph} {V : Finset ℕ} {t : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t) :
    ∃ a ∈ V, ∃ b ∈ V, a ≠ b ∧ ∃ P ⊆ outN D V a ∩ outN D V b, 2 ≤ P.card ∧
      2 ≤ (lockedRows D V (inN D V a ∩ inN D V b)).card ∧
      ∀ x j, x ≠ j → inN D V a ∩ inN D V b = {x,j} →
        (∀ z ∈ outN D V a ∩ outN D V b, D x z = D j z) ∧
        2 ≤ (P.filter (fun z => D x z ≠ true ∧ D j z ≠ true)).card ∧
        ∀ p ∈ outN D V a ∩ outN D V b, ∀ y ∈ outN D V a ∩ outN D V b,
          p ≠ y → D x p ≠ true → D j y ≠ true → 3 ≤ (blockers D (V \ {a,b}) x j p y).card := by
  classical
  obtain ⟨a,av,b,bv,ab,P,sub,pc,best,two,miss⟩ := maximal_targetable_locked_pair free reg
    (by omega) (by simpa using order) (by simpa using no)
  refine ⟨a,av,b,bv,ab,P,sub,pc,two,?_⟩
  intro x j xj exactS
  obtain ⟨p,pp,y,yp,py,xp,jy⟩ := distinct_targets free reg ht order no av bv ab sub
    best two miss xj exactS
  have agree := common_target_agreement free reg ht order no av bv ab xj exactS
    (sub pp) (sub yp) xp jy
  have jp : D j p ≠ true := fun h => xp ((agree p (sub pp)).trans h)
  have xy : D x y ≠ true := fun h => jy ((agree y (sub yp)).symm.trans h)
  refine ⟨agree,one_lt_card.mpr ⟨p,mem_filter.mpr ⟨pp,xp,jp⟩,y,mem_filter.mpr ⟨yp,xy,jy⟩,py⟩,?_⟩
  intro r rP s sP rs xr js
  exact three_blockers free reg ht order no av bv ab xj exactS rP sP rs xr js

#print axioms two_misses
#print axioms distinct_targets
#print axioms three_blockers
#print axioms common_target_agreement
#print axioms selected_two_row_obstruction

end LeanCH.BR.MaximalBankTwoRows
