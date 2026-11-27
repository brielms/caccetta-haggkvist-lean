import checkpoints.shen_extension.MaximalBankTwoRows

/-! Rotate the bank to two jointly missed targets. Two of their shared blockers
repair the old bank labels, even if every additional short row needs a free edit. -/

namespace LeanCH.BR.RotatedLockedRows
open Finset BRq2 BRq3 BR45 JointFreeTargets TwoRowShared MaximalBankTwoRows

theorem extra_locked_parent {D : CH.Digraph} {V : Finset ℕ} {t a b x j p y u w : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (av : a ∈ V) (bv : b ∈ V) (ab : a ≠ b)
    (exactS : inN D V a ∩ inN D V b = {x,j})
    (pP : p ∈ outN D V a ∩ outN D V b) (yP : y ∈ outN D V a ∩ outN D V b) (py : p ≠ y)
    (uk : u ∈ blockers D (V \ {a,b}) x j p y) (wk : w ∈ blockers D (V \ {a,b}) x j p y)
    (uw : u ≠ w) :
    ∃ c ∈ lockedRows D V (inN D V p ∩ inN D V y), c ≠ a ∧ c ≠ b := by
  classical
  let B : Finset ℕ := {p,y}
  let U := V \ B
  let S := inN D V p ∩ inN D V y
  let R := S \ {a,b}
  obtain ⟨ap,bp⟩ := mem_inter.mp pP
  obtain ⟨ay,by'⟩ := mem_inter.mp yP
  obtain ⟨pv,ap⟩ := mem_outN.mp ap
  obtain ⟨yv,ay⟩ := mem_outN.mp ay
  have bp := (mem_outN.mp bp).2
  have by' := (mem_outN.mp by').2
  have bank : B ⊆ V := insert_subset pv (singleton_subset_iff.mpr yv)
  have as' : a ∈ S := mem_inter.mpr ⟨mem_inN.mpr ⟨av,ap⟩,mem_inN.mpr ⟨av,ay⟩⟩
  have bs : b ∈ S := mem_inter.mpr ⟨mem_inN.mpr ⟨bv,bp⟩,mem_inN.mpr ⟨bv,by'⟩⟩
  have su : S ⊆ U := by
    intro c cs
    obtain ⟨cp,cy⟩ := mem_inter.mp cs
    obtain ⟨cv,cp⟩ := mem_inN.mp cp
    have np : c ≠ p := fun e => loopfree free (by decide) pv (e ▸ cp)
    have ny : c ≠ y := fun e => loopfree free (by decide) yv (e ▸ (mem_inN.mp cy).2)
    exact mem_sdiff.mpr ⟨cv,by simp [B,np,ny]⟩
  have tri {i k l} (iv : i ∈ V) (kv : k ∈ V) (lv : l ∈ V)
      (ik : D i k = true) (kl : D k l = true) : D l i ≠ true := fun li =>
    free i 3 (by decide) (by decide) (.step kv ik (.step lv kl (.step iv li (.refl _))))
  have xm : x ∈ inN D V a ∩ inN D V b := by simp [exactS]
  obtain ⟨xa,xb⟩ := mem_inter.mp xm
  obtain ⟨xv,xa⟩ := mem_inN.mp xa
  have xb := (mem_inN.mp xb).2
  have props {z} (zk : z ∈ blockers D (V \ {a,b}) x j p y) :
      z ∈ U ∧ z ∉ S ∧ (∀ k ∈ B, D k z=true) ∧ D z x=true ∧ D z j=true ∧
      D a z ≠ true ∧ D b z ≠ true ∧ D z a ≠ true ∧ D z b ≠ true := by
    obtain ⟨ph,yz,zx,zj⟩ := mem_filter.mp zk
    obtain ⟨zU,pz⟩ := mem_outN.mp ph
    have zv := (mem_sdiff.mp zU).1
    have np : z ≠ p := fun e => loopfree free (by decide) pv (e ▸ pz)
    have ny : z ≠ y := fun e => loopfree free (by decide) yv (e ▸ yz)
    refine ⟨mem_sdiff.mpr ⟨zv,by simp [B,np,ny]⟩,
      fun zs => digonfree free (by decide) pv zv pz (mem_inN.mp (mem_inter.mp zs).1).2,?_,
      zx,zj,tri zv xv av zx xa,tri zv xv bv zx xb,tri av pv zv ap pz,tri bv pv zv bp pz⟩
    intro k km
    rcases mem_insert.mp km with rfl | km
    · exact pz
    · exact mem_singleton.mp km ▸ yz
  obtain ⟨uU,uns,uc,ux,uj,au,_,ua,ub⟩ := props uk
  obtain ⟨wU,wns,wc,_,_,_,bw,wa,wb⟩ := props wk
  by_contra absent
  have outside (c) (cr : c ∈ R) : ∃ v, FreeTarget D V c v ∧ v ∉ S := by
    by_contra! h
    have cL : c ∈ lockedRows D V S := mem_filter.mpr ⟨(mem_sdiff.mp cr).1,h⟩
    have off := (mem_sdiff.mp cr).2
    exact absent ⟨c,cL,fun e => off (by simp [e]),fun e => off (by simp [e])⟩
  let f (c : ℕ) := if cr : c ∈ R then (outside c cr).choose else a
  have chosen {c} (cr : c ∈ R) : FreeTarget D V c (f c) ∧ f c ∉ S := by
    simpa [f,cr] using (outside c cr).choose_spec
  let E := addTargets D R f
  obtain ⟨safe,deg⟩ := free_repair (f:=f) (free.mono_set (show U ⊆ V from sdiff_subset))
    (fun c cr => ⟨retained_target (mem_sdiff.mp cr).1 (chosen cr).1,
      fun hr => (chosen cr).2 (mem_sdiff.mp hr).1⟩)
  have unchanged {c d} (cr : c ∉ R) : E c d = true ↔ D c d = true := by
    simp [E,addTargets,cr]
  have into {c d} (ds : d ∈ S) (cd : E c d = true) : D c d = true := by
    rcases of_decide_eq_true cd with old | ⟨cr,e⟩
    · exact old
    · exact False.elim ((chosen cr).2 (e ▸ ds))
  have ar : a ∉ R := fun ar => (mem_sdiff.mp ar).2 (by simp)
  have br : b ∉ R := fun br => (mem_sdiff.mp br).2 (by simp)
  have ur : u ∉ R := fun r => uns (mem_sdiff.mp r).1
  have wr : w ∉ R := fun r => wns (mem_sdiff.mp r).1
  have gain (k) : (outN D U k).card ≤ (outN E U k).card := by rw [deg]; omega
  obtain ⟨ru,ug⟩ := bank_rich free reg bank uU uc
  obtain ⟨rw',wg⟩ := bank_rich free reg bank wU wc
  have base (c) (cu : c ∈ U) : t ≤ (outN D U c).card+1 := by
    simpa [U,B] using retained_floor reg (mem_sdiff.mp cu).1 py
  have floor (k) (ku : k ∈ U) (ka : k ≠ a) (kb : k ≠ b) : t ≤ (outN E U k).card := by
    by_cases ks : k ∈ S
    · have kr : k ∈ R := mem_sdiff.mpr ⟨ks,by simp [ka,kb]⟩
      change t ≤ (outN (addTargets D R f) U k).card
      rw [deg,ite_eq_left kr]
      exact base k ku
    · apply le_trans _ (gain k)
      by_contra! low
      have sh : k ∈ U.filter (fun i => (outN D U i).card < (t+1)-1) :=
        mem_filter.mpr ⟨ku,by simpa using low⟩
      rw [BypassBankReplay.short_rows_eq_jointParents free (by decide) reg pv yv py (by omega)] at sh
      exact ks (mem_inter.mpr ⟨(mem_inN.mp sh).1,mem_inN.mpr ⟨(mem_sdiff.mp ku).1,(mem_inN.mp sh).2⟩⟩)
  obtain ⟨G,ok,_,_,paid⟩ := two_target_repair (D:=E) safe (su as') (su bs) uU wU ab uw
    (fun e => uns (e ▸ as')) (fun e => uns (e ▸ bs))
    (fun e => wns (e ▸ as')) (fun e => wns (e ▸ bs))
    (fun e => au ((unchanged ar).mp e)) (fun e => ua ((unchanged ur).mp e))
    (fun e => ub ((unchanged ur).mp e)) (fun e => bw ((unchanged br).mp e))
    (fun e => wb ((unchanged wr).mp e)) (fun e => wa ((unchanged wr).mp e))
    ((unchanged ur).mpr ux) ((unchanged ur).mpr uj)
    (fun m mu _ _ ma mb => by
      have hits : m ∈ inN D V a ∩ inN D V b := mem_inter.mpr
        ⟨mem_inN.mpr ⟨(mem_sdiff.mp mu).1,into as' ma⟩,mem_inN.mpr ⟨(mem_sdiff.mp mu).1,into bs mb⟩⟩
      simpa [exactS] using hits)
    ((base a (su as')).trans (Nat.add_le_add_right (gain a) 1))
    ((base b (su bs)).trans (Nat.add_le_add_right (gain b) 1))
    (ru.ge.trans (gain u)) (rw'.ge.trans (gain w))
    (fun m mu h => (ug m mu ((unchanged ur).mp h)).ge.trans (gain m))
    (fun m mu h => (wg m mu ((unchanged wr).mp h)).ge.trans (gain m)) floor
  have size : U.card ≤ 3*t := by
    rw [show U = V \ {p,y} from rfl,card_sdiff_of_subset bank,card_pair py,order]
    omega
  exact no G U ⟨a,su as'⟩ size ok paid


/-- If the rotated bank labels belonged to both original certified head sets,
the old bank labels and the extra locked row give three distinct locked rows. -/
theorem three_locked_after_rotation {D : CH.Digraph} {V : Finset ℕ} {t a b x j p y : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (av : a ∈ V) (bv : b ∈ V) (ab : a ≠ b)
    (exactS : inN D V a ∩ inN D V b = {x,j})
    (pK : p ∈ sharedHeads D V a ∩ sharedHeads D V b)
    (yK : y ∈ sharedHeads D V a ∩ sharedHeads D V b) (py : p ≠ y)
    (size : 2 ≤ (blockers D (V \ {a,b}) x j p y).card) :
    3 ≤ (lockedRows D V (inN D V p ∩ inN D V y)).card := by
  classical
  let S := inN D V p ∩ inN D V y
  have locked {c} (cv : c ∈ V) (pc : p ∈ sharedHeads D V c) (yc : y ∈ sharedHeads D V c) :
      c ∈ lockedRows D V S := by
    obtain ⟨cp,cp'⟩ := mem_filter.mp pc
    obtain ⟨cy,cy'⟩ := mem_filter.mp yc
    refine mem_filter.mpr ⟨mem_inter.mpr ⟨mem_inN.mpr ⟨cv,(mem_outN.mp cp).2⟩,
      mem_inN.mpr ⟨cv,(mem_outN.mp cy).2⟩⟩,?_⟩
    intro v fv
    exact mem_inter.mpr ⟨mem_inN.mpr ⟨fv.1,cp' v fv⟩,mem_inN.mpr ⟨fv.1,cy' v fv⟩⟩
  have ordinary {z} (hit : z ∈ sharedHeads D V a ∩ sharedHeads D V b) :
      z ∈ outN D V a ∩ outN D V b :=
    mem_inter.mpr ⟨(mem_filter.mp (mem_inter.mp hit).1).1,(mem_filter.mp (mem_inter.mp hit).2).1⟩
  obtain ⟨u,uk,w,wk,uw⟩ := one_lt_card.mp size
  obtain ⟨c,cl,ca,cb⟩ := extra_locked_parent free reg ht order no av bv ab exactS
    (ordinary pK) (ordinary yK) py uk wk uw
  exact two_lt_card_iff.mpr ⟨a,b,c,
    locked av (mem_inter.mp pK).1 (mem_inter.mp yK).1,
    locked bv (mem_inter.mp pK).2 (mem_inter.mp yK).2,cl,ab,ca.symm,cb.symm⟩

/-- A source admits one bank with three short rows, two locked rows and two
distinct common targets each missed by a short row, all on the same labels. -/
theorem exists_three_short_bank {D : CH.Digraph} {V : Finset ℕ} {t : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t) :
    ∃ a ∈ V, ∃ b ∈ V, a ≠ b ∧
      let S := inN D V a ∩ inN D V b
      3 ≤ S.card ∧ 2 ≤ (lockedRows D V S).card ∧
      ∃ T ⊆ outN D V a ∩ outN D V b, 2 ≤ T.card ∧ ∀ z ∈ T, ∃ c ∈ S, D c z ≠ true := by
  classical
  obtain ⟨a,av,b,bv,ab,P,K,_,best,two,miss⟩ := JointTargetablePair.certified_maximal_targetable_locked_pair
    free reg (by omega) (by simpa using order) (by simpa using no)
  let S := inN D V a ∩ inN D V b
  have sub : P ⊆ outN D V a ∩ outN D V b := fun z zp => by
    obtain ⟨za,zb⟩ := mem_inter.mp (K zp)
    exact mem_inter.mpr ⟨(mem_filter.mp za).1,(mem_filter.mp zb).1⟩
  by_cases many : 3 ≤ S.card
  · exact ⟨a,av,b,bv,ab,many,two,P.filter (fun z => ∃ c ∈ S, D c z ≠ true),
      fun z zm => sub (mem_filter.mp zm).1,two_misses free av bv ab sub best two,
      fun z zm => (mem_filter.mp zm).2⟩
  have lb : 2 ≤ S.card := two.trans (card_le_card (filter_subset _ _))
  obtain ⟨x,j,xj,exactS⟩ := card_eq_two.mp (show S.card = 2 by omega)
  obtain ⟨p,pp,y,yp,py,xp,jy⟩ := distinct_targets free reg ht order no av bv ab sub
    best two miss xj exactS
  let T := blockers D (V \ {a,b}) x j p y
  have three : 3 ≤ T.card := three_blockers free reg ht order no av bv ab xj exactS (sub pp) (sub yp) py xp jy
  let R := inN D V p ∩ inN D V y
  have locks : 3 ≤ (lockedRows D V R).card := three_locked_after_rotation free reg ht order no av bv ab
    exactS (K pp) (K yp) py (le_trans (by decide : 2 ≤ 3) three)
  have large : 3 ≤ R.card := locks.trans (card_le_card (filter_subset _ _))
  obtain ⟨pv,ap⟩ := mem_outN.mp (mem_inter.mp (sub pp)).1
  obtain ⟨yv,ay⟩ := mem_outN.mp (mem_inter.mp (sub yp)).1
  have ar : a ∈ R := mem_inter.mpr ⟨mem_inN.mpr ⟨av,ap⟩,mem_inN.mpr ⟨av,ay⟩⟩
  have xs : x ∈ S := by simp [exactS]
  obtain ⟨xv,xa⟩ := mem_inN.mp (mem_inter.mp xs).1
  refine ⟨p,pv,y,yv,py,large,le_trans (by decide : 2 ≤ 3) locks,T,?_,le_trans (by decide : 2 ≤ 3) three,?_⟩
  · intro z zt
    obtain ⟨ph,yz,_,_⟩ := mem_filter.mp zt
    obtain ⟨zu,pz⟩ := mem_outN.mp ph
    have zv := (mem_sdiff.mp zu).1
    exact mem_inter.mpr ⟨mem_outN.mpr ⟨zv,pz⟩,mem_outN.mpr ⟨zv,yz⟩⟩
  · intro z zt
    obtain ⟨ph,_,zx,_⟩ := mem_filter.mp zt
    have zv := (mem_sdiff.mp (mem_outN.mp ph).1).1
    exact ⟨a,ar,fun az => free a 3 (by decide) (by decide)
      (.step zv az (.step xv zx (.step av xa (.refl _))))⟩


/-- The synchronized bank and targets produce ordinary capstone marks. -/
theorem three_short_marked_choices {t : ℕ} (X : ShenMinimumOrder.Source 3 (t+1))
    (reg : OutEq (t+1) X.D X.V) (ht : 1 ≤ t) (order : X.V.card = 3*t+2)
    (no : BypassRepair.NoHost 3 t) :
    ∃ a ∈ X.V, ∃ b ∈ X.V, a ≠ b ∧
      let U := X.V \ {a,b}
      let S := U.filter (fun c => (outN X.D U c).card < t)
      3 ≤ S.card ∧ 2 ≤ (lockedRows X.D X.V S).card ∧
      ∃ T ⊆ outN X.D X.V a ∩ outN X.D X.V b, 2 ≤ T.card ∧
        ∀ z ∈ T, ∃ x ∈ S, BypassBankReplay.Marked X ⟨{a,b},x,a,z⟩ ∧
          BypassBankReplay.JointShort X ⟨{a,b},x,a,z⟩ := by
  classical
  obtain ⟨a,av,b,bv,ab,three,two,T,sub,tc,miss⟩ := exists_three_short_bank X.free reg ht order no
  let U := X.V \ {a,b}
  let S := U.filter (fun c => (outN X.D U c).card < t)
  have eq : S = inN X.D X.V a ∩ inN X.D X.V b := by
    have sh := BypassBankReplay.short_rows_eq_jointParents X.free (by decide) reg av bv ab (by omega)
    change U.filter (fun c => (outN X.D U c).card < t+1-1) = _ at sh
    have sEq : S = BypassBankReplay.jointParents X.D X.V a b := by simpa [S] using sh
    rw [sEq]
    ext c
    simp only [BypassBankReplay.jointParents,mem_inN,mem_inter]
    tauto
  have large : 3 ≤ S.card := eq ▸ three
  have locked : 2 ≤ (lockedRows X.D X.V S).card := by rw [eq]; exact two
  refine ⟨a,av,b,bv,ab,large,locked,T,sub,tc,?_⟩
  intro z zt
  obtain ⟨x,xs,xz⟩ := miss z zt
  have xS : x ∈ S := eq ▸ xs
  obtain ⟨xu,low⟩ := mem_filter.mp xS
  obtain ⟨xv,xa⟩ := mem_inN.mp (mem_inter.mp xs).1
  obtain ⟨zv,az⟩ := mem_outN.mp (mem_inter.mp (sub zt)).1
  have bz := (mem_outN.mp (mem_inter.mp (sub zt)).2).2
  have za : z ≠ a := fun e => loopfree X.free (by decide) av (e ▸ az)
  have zb : z ≠ b := fun e => loopfree X.free (by decide) bv (e ▸ bz)
  have floor := retained_floor reg xv ab
  change t+1-1 ≤ (outN X.D U x).card+1 at floor
  have size : 0 < (S.erase x).card := by rw [card_erase_of_mem xS]; omega
  obtain ⟨j,jm⟩ := card_pos.mp size
  obtain ⟨jx,js⟩ := mem_erase.mp jm
  obtain ⟨ju,jlow⟩ := mem_filter.mp js
  refine ⟨x,xS,?_,j,ju,jx,by simpa using jlow⟩
  exact ⟨insert_subset av (singleton_subset_iff.mpr bv),by change ({a,b} : Finset ℕ).card = _; rw [card_pair ab]; omega,
    xu,by simp,mem_sdiff.mpr ⟨zv,by simp [za,zb]⟩,xa,az,xz,
    by change (outN X.D U x).card+1=t+1-1; omega,
    BypassBankReplay.chain_through_arc X (by decide) (by omega) reg (by omega) xv av zv xa az⟩

#print axioms three_short_marked_choices

#print axioms extra_locked_parent
#print axioms three_locked_after_rotation
#print axioms exists_three_short_bank
end LeanCH.BR.RotatedLockedRows
