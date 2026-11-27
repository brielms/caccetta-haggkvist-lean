import checkpoints.shen_extension.RotatedLockedRows

/-! Three locked rows a, b, c of the rotated bank {p,y}.

Rows a and b take two original common blockers u, w. Their edits share only
the middles x, j, which are paid around the four-cycle u, x, w, j. Row c
takes a third common successor z of p and y. The only returns of c→z that
can stay unpaid are z→m→c with m also on u→m→a or on w→m→b.

* `three_target_repair`: the edit, with at most one such middle m₀ paid at z.
* `rotated_three_rows`: its use on the source, with any number of further
  short rows that have a free target outside the short set.
* `three_row_obstruction`: every admissible u, w, z has two such middles.
* `locked_row_sees_common_targets`: if c points to u and w, then c points to
  every common successor of p and y. -/

namespace LeanCH.BR.RotatedThreeRows
open Finset BRq2 BRq3 BR45 TripleBank JointFreeTargets TwoRowShared MaximalBankTwoRows

private theorem lose (S T : Finset ℕ) : S.card ≤ (S \ T).card+T.card :=
  card_le_card_sdiff_add_card

/-- Rows a, b, c take u, w, z. Payments: u→x, x→b, w→j, j→a around the
shared four-cycle, z→m₀ for the one middle shared with it, and one arc at
every other blocker. -/
theorem three_target_repair {D : CH.Digraph} {U : Finset ℕ} {t a b c u w z x j m₀ : ℕ}
    (safe : QFree D U 3) (au : a∈U) (bu : b∈U) (cu : c∈U)
    (uu : u∈U) (wu : w∈U) (zu : z∈U)
    (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (ua : u≠a) (ub : u≠b) (uc : u≠c) (wa : w≠a) (wb : w≠b) (wc : w≠c)
    (za : z≠a) (zb : z≠b) (zc : z≠c) (uw : u≠w) (zu' : z≠u) (zw : z≠w)
    (xw : x≠w) (xz : x≠z) (jw : j≠w) (jz : j≠z) (cx : c≠x) (cj : c≠j)
    (a_u : D a u≠true) (u_a : D u a≠true) (b_w : D b w≠true) (w_b : D w b≠true)
    (c_z : D c z≠true) (z_c : D z c≠true)
    (w_a : D w a≠true) (z_a : D z a≠true) (u_b : D u b≠true) (z_b : D z b≠true)
    (u_c : D u c≠true) (w_c : D w c≠true)
    (ux : D u x=true) (uj : D u j=true)
    (xa : D x a=true) (xb : D x b=true) (ja : D j a=true) (jb : D j b=true)
    (only : ∀ m∈U, D u m=true → D w m=true → D m a=true → D m b=true → m=x ∨ m=j)
    (one : ∀ m∈U, D z m=true → D m c=true →
      (D u m=true ∧ D m a=true) ∨ (D w m=true ∧ D m b=true) → m=m₀)
    (needa : t≤(outN D U a).card+1) (needb : t≤(outN D U b).card+1)
    (needc : t≤(outN D U c).card+1)
    (richU : t+1≤(outN D U u).card) (richW : t+1≤(outN D U w).card)
    (richZ : t+1≤(outN D U z).card)
    (succU : ∀ m∈U, D u m=true → t+1≤(outN D U m).card)
    (succW : ∀ m∈U, D w m=true → t+1≤(outN D U m).card)
    (succZ : ∀ m∈U, D z m=true → t+1≤(outN D U m).card)
    (floor : ∀ i∈U, i≠a → i≠b → i≠c → t≤(outN D U i).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E a u=true ∧ E b w=true ∧ E c z=true ∧
      ∀ i∈U, t≤(outN E U i).card := by
  classical
  have loop {k} (ku : k∈U) : D k k≠true := loopfree safe (by decide) ku
  have xu' : x≠u := fun e => loop uu (e ▸ ux)
  have ju' : j≠u := fun e => loop uu (e ▸ uj)
  have xna : x≠a := fun e => loop au (e ▸ xa)
  have xnb : x≠b := fun e => loop bu (e ▸ xb)
  have jna : j≠a := fun e => loop au (e ▸ ja)
  have jnb : j≠b := fun e => loop bu (e ▸ jb)
  let A (m : ℕ) : Finset ℕ :=
    if m=a then {u} else if m=b then {w} else if m=c then {z} else ∅
  let C (m : ℕ) : Finset ℕ :=
    if m=u then {x} else if m=w then {j} else if m=z then {m₀} else
    if m=x then {b} else if m=j then {a} else
      ((if D u m=true ∧ D m a=true then {a} else ∅) ∪
      (if D w m=true ∧ D m b=true then {b} else ∅)) ∪
      (if D z m=true ∧ D m c=true ∧ m≠m₀ then {c} else ∅)
  have spec {r h} (g : h∈A r) : (r=a ∧ h=u) ∨ (r=b ∧ h=w) ∨ (r=c ∧ h=z) := by
    by_cases ra : r=a
    · exact Or.inl ⟨ra,by simpa [A,ra] using g⟩
    · by_cases rb : r=b
      · exact Or.inr (Or.inl ⟨rb,by simpa [A,rb,ab.symm] using g⟩)
      · by_cases rc : r=c
        · exact Or.inr (Or.inr ⟨rc,by simpa [A,rc,ac.symm,bc.symm] using g⟩)
        · simp [A,ra,rb,rc] at g
  have Au : A u=∅ := by simp [A,ua,ub,uc]
  have Aw : A w=∅ := by simp [A,wa,wb,wc]
  have Az : A z=∅ := by simp [A,za,zb,zc]
  obtain ⟨ok,rows⟩ := patch_certificate (A:=A) (C:=C) safe
    (fun r _ h g => by
      rcases spec g with ⟨e1,e2⟩ | ⟨e1,e2⟩ | ⟨e1,e2⟩
      · rw [e1,e2]; exact ⟨uu,ua,a_u,u_a⟩
      · rw [e1,e2]; exact ⟨wu,wb,b_w,w_b⟩
      · rw [e1,e2]; exact ⟨zu,zc,c_z,z_c⟩)
    (fun r _ h g m mu hm mr => by
      rcases spec g with ⟨e1,e2⟩ | ⟨e1,e2⟩ | ⟨e1,e2⟩
      · rw [e2] at hm
        rw [e1] at mr
        rw [e1,e2]
        by_cases mx : m=x
        · exact Or.inl (by simp [C,mx])
        · refine Or.inr ?_
          have m1 : m≠u := fun q => loop uu (q ▸ hm)
          have m2 : m≠w := fun q => w_a (q ▸ mr)
          have m3 : m≠z := fun q => z_a (q ▸ mr)
          by_cases mj : m=j
          · have jx : j≠x := fun e => mx (mj.trans e)
            simp [C,mj,ju',jw,jz,jx]
          · simp [C,m1,m2,m3,mx,mj,hm,mr]
      · rw [e2] at hm
        rw [e1] at mr
        rw [e1,e2]
        by_cases mj : m=j
        · exact Or.inl (by simp [C,uw.symm,mj])
        · refine Or.inr ?_
          have m1 : m≠u := fun q => u_b (q ▸ mr)
          have m2 : m≠w := fun q => loop wu (q ▸ hm)
          have m3 : m≠z := fun q => z_b (q ▸ mr)
          by_cases mx : m=x
          · simp [C,mx,xu',xw,xz]
          · simp [C,m1,m2,m3,mx,mj,hm,mr]
      · rw [e2] at hm
        rw [e1] at mr
        rw [e1,e2]
        by_cases e : m=m₀
        · exact Or.inl (by simp [C,zu',zw,e])
        · refine Or.inr ?_
          have m1 : m≠u := fun q => u_c (q ▸ mr)
          have m2 : m≠w := fun q => w_c (q ▸ mr)
          have m3 : m≠z := fun q => loop zu (q ▸ hm)
          have m4 : m≠x := fun q => e (one m mu hm mr (Or.inl ⟨q ▸ ux,q ▸ xa⟩))
          have m5 : m≠j := fun q => e (one m mu hm mr (Or.inl ⟨q ▸ uj,q ▸ ja⟩))
          simp [C,m1,m2,m3,m4,m5,hm,mr,e])
    (fun r _ h g q k => by
      rcases spec g with ⟨_,e2⟩ | ⟨_,e2⟩ | ⟨_,e2⟩
      · rw [e2,Au] at k; exact (notMem_empty _ k).elim
      · rw [e2,Aw] at k; exact (notMem_empty _ k).elim
      · rw [e2,Az] at k; exact (notMem_empty _ k).elim)
  refine ⟨_,ok,decide_eq_true (Or.inl (by simp [A])),
    decide_eq_true (Or.inl (by simp [A,ab.symm])),
    decide_eq_true (Or.inl (by simp [A,ac.symm,bc.symm])),?_⟩
  intro i iu
  rw [rows i iu]
  by_cases ia : i=a
  · have k : C i=∅ := by
      simp [C,ia,ua.symm,wa.symm,za.symm,xna.symm,jna.symm,u_a,w_a,z_a]
    have r : A i={u} := by simp [A,ia]
    rw [k,r,sdiff_empty,card_singleton,ia]
    exact needa
  by_cases ib : i=b
  · have k : C i=∅ := by
      simp [C,ib,ub.symm,wb.symm,zb.symm,xnb.symm,jnb.symm,u_b,w_b,z_b]
    have r : A i={w} := by simp [A,ib,ab.symm]
    rw [k,r,sdiff_empty,card_singleton,ib]
    exact needb
  by_cases ic : i=c
  · have k : C i=∅ := by
      simp [C,ic,uc.symm,wc.symm,zc.symm,cx,cj,u_c,w_c,z_c]
    have r : A i={z} := by simp [A,ic,ac.symm,bc.symm]
    rw [k,r,sdiff_empty,card_singleton,ic]
    exact needc
  have a0 : A i=∅ := by simp [A,ia,ib,ic]
  rw [a0,card_empty,Nat.add_zero]
  by_cases iuu : i=u
  · have k : C i={x} := by simp [C,iuu]
    have l := lose (outN D U i) {x}
    have r : t+1≤(outN D U i).card := iuu ▸ richU
    rw [k]; simp at l; omega
  by_cases iw : i=w
  · have k : C i={j} := by simp [C,iw,uw.symm]
    have l := lose (outN D U i) {j}
    have r : t+1≤(outN D U i).card := iw ▸ richW
    rw [k]; simp at l; omega
  by_cases iz : i=z
  · have k : C i={m₀} := by simp [C,iz,zu',zw]
    have l := lose (outN D U i) {m₀}
    have r : t+1≤(outN D U i).card := iz ▸ richZ
    rw [k]; simp at l; omega
  by_cases ix : i=x
  · have k : C i={b} := by simp [C,ix,xu',xw,xz]
    have l := lose (outN D U i) {b}
    have r := succU i iu (ix ▸ ux)
    rw [k]; simp at l; omega
  by_cases ij : i=j
  · have jx : j≠x := fun e => ix (ij.trans e)
    have k : C i={a} := by simp [C,ij,ju',jw,jz,jx]
    have l := lose (outN D U i) {a}
    have r := succU i iu (ij ▸ uj)
    rw [k]; simp at l; omega
  by_cases c1 : D u i=true ∧ D i a=true
  · have n2 : ¬(D w i=true ∧ D i b=true) := fun c2 =>
      (only i iu c1.1 c2.1 c1.2 c2.2).elim ix ij
    have n3 : ¬(D z i=true ∧ D i c=true ∧ i≠m₀) := fun c3 =>
      c3.2.2 (one i iu c3.1 c3.2.1 (Or.inl c1))
    have k : C i={a} := by simp [C,iuu,iw,iz,ix,ij,c1.1,c1.2,n2,n3]
    have l := lose (outN D U i) {a}
    have r := succU i iu c1.1
    rw [k]; simp at l; omega
  by_cases c2 : D w i=true ∧ D i b=true
  · have n3 : ¬(D z i=true ∧ D i c=true ∧ i≠m₀) := fun c3 =>
      c3.2.2 (one i iu c3.1 c3.2.1 (Or.inr c2))
    have k : C i={b} := by simp [C,iuu,iw,iz,ix,ij,c1,c2.1,c2.2,n3]
    have l := lose (outN D U i) {b}
    have r := succW i iu c2.1
    rw [k]; simp at l; omega
  by_cases c3 : D z i=true ∧ D i c=true ∧ i≠m₀
  · have k : C i={c} := by simp [C,iuu,iw,iz,ix,ij,c1,c2,c3.1,c3.2.1,c3.2.2]
    have l := lose (outN D U i) {c}
    have r := succZ i iu c3.1
    rw [k]; simp at l; omega
  · have k : C i=∅ := by simp [C,iuu,iw,iz,ix,ij,c1,c2,c3]
    rw [k,sdiff_empty]
    exact floor i iu ia ib ic

/-- The three-row edit on the rotated bank {p,y} of a source. Every short
row other than a, b, c first receives a free arc leaving the short set. If
at most one middle m₀ lies on z→m→c and on u→m→a or w→m→b, the edit gives a
host. -/
theorem rotated_three_rows {D : CH.Digraph} {V : Finset ℕ} {t a b c x j p y u w z m₀ : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (av : a ∈ V) (bv : b ∈ V) (ab : a ≠ b)
    (exactS : inN D V a ∩ inN D V b = {x,j})
    (pP : p ∈ outN D V a ∩ outN D V b) (yP : y ∈ outN D V a ∩ outN D V b) (py : p ≠ y)
    (uk : u ∈ blockers D (V \ {a,b}) x j p y) (wk : w ∈ blockers D (V \ {a,b}) x j p y)
    (uw : u ≠ w)
    (cS : c ∈ inN D V p ∩ inN D V y) (ca : c ≠ a) (cb : c ≠ b)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ≠ a → r ≠ b → r ≠ c →
      ∃ v, FreeTarget D V r v ∧ v ∉ inN D V p ∩ inN D V y)
    (zP : z ∈ outN D V p ∩ outN D V y) (cz : D c z ≠ true) (zu : z ≠ u) (zw : z ≠ w)
    (one : ∀ m ∈ V, D z m = true → D m c = true →
      (D u m = true ∧ D m a = true) ∨ (D w m = true ∧ D m b = true) → m = m₀) : False := by
  classical
  let B : Finset ℕ := {p,y}
  let U := V \ B
  let S := inN D V p ∩ inN D V y
  let R := S \ {a,b,c}
  obtain ⟨ap,bp⟩ := mem_inter.mp pP
  obtain ⟨ay,by'⟩ := mem_inter.mp yP
  obtain ⟨pv,ap⟩ := mem_outN.mp ap
  obtain ⟨yv,ay⟩ := mem_outN.mp ay
  have bp := (mem_outN.mp bp).2
  have by' := (mem_outN.mp by').2
  have bank : B ⊆ V := insert_subset pv (singleton_subset_iff.mpr yv)
  have as' : a ∈ S := mem_inter.mpr ⟨mem_inN.mpr ⟨av,ap⟩,mem_inN.mpr ⟨av,ay⟩⟩
  have bs : b ∈ S := mem_inter.mpr ⟨mem_inN.mpr ⟨bv,bp⟩,mem_inN.mpr ⟨bv,by'⟩⟩
  have cs : c ∈ S := cS
  have su : S ⊆ U := by
    intro k ks
    obtain ⟨kp,ky⟩ := mem_inter.mp ks
    obtain ⟨kv,kp⟩ := mem_inN.mp kp
    have np : k ≠ p := fun e => loopfree free (by decide) pv (e ▸ kp)
    have ny : k ≠ y := fun e => loopfree free (by decide) yv (e ▸ (mem_inN.mp ky).2)
    exact mem_sdiff.mpr ⟨kv,by simp [B,np,ny]⟩
  have tri {i k l} (iv : i ∈ V) (kv : k ∈ V) (lv : l ∈ V)
      (ik : D i k = true) (kl : D k l = true) : D l i ≠ true := fun li =>
    free i 3 (by decide) (by decide) (.step kv ik (.step lv kl (.step iv li (.refl _))))
  have xm : x ∈ inN D V a ∩ inN D V b := by simp [exactS]
  have jm : j ∈ inN D V a ∩ inN D V b := by simp [exactS]
  obtain ⟨xa,xb⟩ := mem_inter.mp xm
  obtain ⟨xv,xa⟩ := mem_inN.mp xa
  have xb := (mem_inN.mp xb).2
  obtain ⟨ja,jb⟩ := mem_inter.mp jm
  obtain ⟨jv,ja⟩ := mem_inN.mp ja
  have jb := (mem_inN.mp jb).2
  have props {q} (qk : q ∈ blockers D (V \ {a,b}) x j p y) :
      q ∈ U ∧ q ∉ S ∧ (∀ k ∈ B, D k q=true) ∧ D q x=true ∧ D q j=true ∧
      D a q ≠ true ∧ D b q ≠ true ∧ D q a ≠ true ∧ D q b ≠ true := by
    obtain ⟨ph,yq,qx,qj⟩ := mem_filter.mp qk
    obtain ⟨qU,pq⟩ := mem_outN.mp ph
    have qv := (mem_sdiff.mp qU).1
    have np : q ≠ p := fun e => loopfree free (by decide) pv (e ▸ pq)
    have ny : q ≠ y := fun e => loopfree free (by decide) yv (e ▸ yq)
    refine ⟨mem_sdiff.mpr ⟨qv,by simp [B,np,ny]⟩,
      fun qs => digonfree free (by decide) pv qv pq (mem_inN.mp (mem_inter.mp qs).1).2,?_,
      qx,qj,tri qv xv av qx xa,tri qv xv bv qx xb,tri av pv qv ap pq,tri bv pv qv bp pq⟩
    intro k km
    rcases mem_insert.mp km with rfl | km
    · exact pq
    · exact mem_singleton.mp km ▸ yq
  obtain ⟨uU,uns,ucm,ux,uj,a_u,b_u,u_a,u_b⟩ := props uk
  obtain ⟨wU,wns,wcm,wx,wj,a_w,b_w,w_a,w_b⟩ := props wk
  have uv := (mem_sdiff.mp uU).1
  have wv := (mem_sdiff.mp wU).1
  have pu : D p u = true := ucm p (by simp [B])
  have pw : D p w = true := wcm p (by simp [B])
  obtain ⟨pz,yz⟩ := mem_inter.mp zP
  obtain ⟨zv,pz⟩ := mem_outN.mp pz
  have yz := (mem_outN.mp yz).2
  have zp : z ≠ p := fun e => loopfree free (by decide) pv (e ▸ pz)
  have zy : z ≠ y := fun e => loopfree free (by decide) yv (e ▸ yz)
  have zU : z ∈ U := mem_sdiff.mpr ⟨zv,by simp [B,zp,zy]⟩
  have zns : z ∉ S := fun zs =>
    digonfree free (by decide) pv zv pz (mem_inN.mp (mem_inter.mp zs).1).2
  have zcm : ∀ k ∈ B, D k z = true := by
    intro k km
    rcases mem_insert.mp km with rfl | km
    · exact pz
    · exact mem_singleton.mp km ▸ yz
  obtain ⟨cv,cp⟩ := mem_inN.mp (mem_inter.mp cS).1
  have z_a : D z a ≠ true := tri av pv zv ap pz
  have z_b : D z b ≠ true := tri bv pv zv bp pz
  have z_c : D z c ≠ true := tri cv pv zv cp pz
  have u_c : D u c ≠ true := tri cv pv uv cp pu
  have w_c : D w c ≠ true := tri cv pv wv cp pw
  have xns : x ∉ S := fun xs =>
    tri xv pv uv (mem_inN.mp (mem_inter.mp xs).1).2 pu ux
  have jns : j ∉ S := fun js =>
    tri jv pv uv (mem_inN.mp (mem_inter.mp js).1).2 pu uj
  have outside (k) (kr : k ∈ R) : ∃ v, FreeTarget D V k v ∧ v ∉ S := by
    have off := (mem_sdiff.mp kr).2
    exact others k (mem_sdiff.mp kr).1 (fun e => off (by simp [e]))
      (fun e => off (by simp [e])) (fun e => off (by simp [e]))
  let f (k : ℕ) := if kr : k ∈ R then (outside k kr).choose else a
  have chosen {k} (kr : k ∈ R) : FreeTarget D V k (f k) ∧ f k ∉ S := by
    simpa [f,kr] using (outside k kr).choose_spec
  let E := addTargets D R f
  obtain ⟨safe,deg⟩ := free_repair (f:=f) (free.mono_set (show U ⊆ V from sdiff_subset))
    (fun k kr => ⟨retained_target (mem_sdiff.mp kr).1 (chosen kr).1,
      fun hr => (chosen kr).2 (mem_sdiff.mp hr).1⟩)
  have unchanged {k d} (kr : k ∉ R) : E k d = true ↔ D k d = true := by
    simp [E,addTargets,kr]
  have into {k d} (ds : d ∈ S) (kd : E k d = true) : D k d = true := by
    rcases of_decide_eq_true kd with old | ⟨kr,e⟩
    · exact old
    · exact False.elim ((chosen kr).2 (e ▸ ds))
  have ar : a ∉ R := fun h => (mem_sdiff.mp h).2 (by simp)
  have br : b ∉ R := fun h => (mem_sdiff.mp h).2 (by simp)
  have cr : c ∉ R := fun h => (mem_sdiff.mp h).2 (by simp)
  have ur : u ∉ R := fun h => uns (mem_sdiff.mp h).1
  have wr : w ∉ R := fun h => wns (mem_sdiff.mp h).1
  have zr : z ∉ R := fun h => zns (mem_sdiff.mp h).1
  have xr : x ∉ R := fun h => xns (mem_sdiff.mp h).1
  have jr : j ∉ R := fun h => jns (mem_sdiff.mp h).1
  have gain (k) : (outN D U k).card ≤ (outN E U k).card := by rw [deg]; omega
  obtain ⟨ru,ug⟩ := bank_rich free reg bank uU ucm
  obtain ⟨rw',wg⟩ := bank_rich free reg bank wU wcm
  obtain ⟨rz,zg⟩ := bank_rich free reg bank zU zcm
  have base (k) (ku : k ∈ U) : t ≤ (outN D U k).card+1 := by
    simpa [U,B] using retained_floor reg (mem_sdiff.mp ku).1 py
  have floor (k) (ku : k ∈ U) (ka : k ≠ a) (kb : k ≠ b) (kc : k ≠ c) :
      t ≤ (outN E U k).card := by
    by_cases ks : k ∈ S
    · have kr : k ∈ R := mem_sdiff.mpr ⟨ks,by simp [ka,kb,kc]⟩
      change t ≤ (outN (addTargets D R f) U k).card
      rw [deg,ite_eq_left kr]
      exact base k ku
    · apply le_trans _ (gain k)
      by_contra! low
      have sh : k ∈ U.filter (fun i => (outN D U i).card < (t+1)-1) :=
        mem_filter.mpr ⟨ku,by simpa using low⟩
      rw [BypassBankReplay.short_rows_eq_jointParents free (by decide) reg pv yv py (by omega)] at sh
      exact ks (mem_inter.mpr ⟨(mem_inN.mp sh).1,mem_inN.mpr ⟨(mem_sdiff.mp ku).1,(mem_inN.mp sh).2⟩⟩)
  obtain ⟨G,ok,_,_,_,paid⟩ := three_target_repair (D:=E) (x:=x) (j:=j) (m₀:=m₀)
    safe (su as') (su bs) (su cs) uU wU zU
    ab ca.symm cb.symm
    (fun e => uns (e ▸ as')) (fun e => uns (e ▸ bs)) (fun e => uns (e ▸ cs))
    (fun e => wns (e ▸ as')) (fun e => wns (e ▸ bs)) (fun e => wns (e ▸ cs))
    (fun e => zns (e ▸ as')) (fun e => zns (e ▸ bs)) (fun e => zns (e ▸ cs))
    uw zu zw
    (fun e => loopfree free (by decide) wv (e ▸ wx))
    (fun e => tri xv av pv xa ap (e ▸ pz))
    (fun e => loopfree free (by decide) wv (e ▸ wj))
    (fun e => tri jv av pv ja ap (e ▸ pz))
    (fun e => xns (e ▸ cs)) (fun e => jns (e ▸ cs))
    (fun e => a_u ((unchanged ar).mp e)) (fun e => u_a ((unchanged ur).mp e))
    (fun e => b_w ((unchanged br).mp e)) (fun e => w_b ((unchanged wr).mp e))
    (fun e => cz ((unchanged cr).mp e)) (fun e => z_c ((unchanged zr).mp e))
    (fun e => w_a ((unchanged wr).mp e)) (fun e => z_a ((unchanged zr).mp e))
    (fun e => u_b ((unchanged ur).mp e)) (fun e => z_b ((unchanged zr).mp e))
    (fun e => u_c ((unchanged ur).mp e)) (fun e => w_c ((unchanged wr).mp e))
    ((unchanged ur).mpr ux) ((unchanged ur).mpr uj)
    ((unchanged xr).mpr xa) ((unchanged xr).mpr xb)
    ((unchanged jr).mpr ja) ((unchanged jr).mpr jb)
    (fun m mu _ _ ma mb => by
      have hits : m ∈ inN D V a ∩ inN D V b := mem_inter.mpr
        ⟨mem_inN.mpr ⟨(mem_sdiff.mp mu).1,into as' ma⟩,mem_inN.mpr ⟨(mem_sdiff.mp mu).1,into bs mb⟩⟩
      simpa [exactS] using hits)
    (fun m mu zm mc h => one m (mem_sdiff.mp mu).1 ((unchanged zr).mp zm) (into cs mc)
      (h.imp (fun q => ⟨(unchanged ur).mp q.1,into as' q.2⟩)
        (fun q => ⟨(unchanged wr).mp q.1,into bs q.2⟩)))
    ((base a (su as')).trans (Nat.add_le_add_right (gain a) 1))
    ((base b (su bs)).trans (Nat.add_le_add_right (gain b) 1))
    ((base c (su cs)).trans (Nat.add_le_add_right (gain c) 1))
    (ru.ge.trans (gain u)) (rw'.ge.trans (gain w)) (rz.ge.trans (gain z))
    (fun m mu h => (ug m mu ((unchanged ur).mp h)).ge.trans (gain m))
    (fun m mu h => (wg m mu ((unchanged wr).mp h)).ge.trans (gain m))
    (fun m mu h => (zg m mu ((unchanged zr).mp h)).ge.trans (gain m)) floor
  have size : U.card ≤ 3*t := by
    rw [show U = V \ {p,y} from rfl,card_sdiff_of_subset bank,card_pair py,order]
    omega
  exact no G U ⟨a,su as'⟩ size ok paid

/-- In a source, any two original blockers u, w for a, b and any third
common successor z of p, y missed by c leave at least two middles on z→m→c
that also lie on u→m→a or on w→m→b. -/
theorem three_row_obstruction {D : CH.Digraph} {V : Finset ℕ} {t a b c x j p y u w z : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (av : a ∈ V) (bv : b ∈ V) (ab : a ≠ b)
    (exactS : inN D V a ∩ inN D V b = {x,j})
    (pP : p ∈ outN D V a ∩ outN D V b) (yP : y ∈ outN D V a ∩ outN D V b) (py : p ≠ y)
    (uk : u ∈ blockers D (V \ {a,b}) x j p y) (wk : w ∈ blockers D (V \ {a,b}) x j p y)
    (uw : u ≠ w)
    (cS : c ∈ inN D V p ∩ inN D V y) (ca : c ≠ a) (cb : c ≠ b)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ≠ a → r ≠ b → r ≠ c →
      ∃ v, FreeTarget D V r v ∧ v ∉ inN D V p ∩ inN D V y)
    (zP : z ∈ outN D V p ∩ outN D V y) (cz : D c z ≠ true) (zu : z ≠ u) (zw : z ≠ w) :
    2 ≤ (V.filter (fun m => D z m = true ∧ D m c = true ∧
      ((D u m = true ∧ D m a = true) ∨ (D w m = true ∧ D m b = true)))).card := by
  classical
  let M := V.filter (fun m => D z m = true ∧ D m c = true ∧
    ((D u m = true ∧ D m a = true) ∨ (D w m = true ∧ D m b = true)))
  change 2 ≤ M.card
  by_contra! few
  have le1 : M.card ≤ 1 := by omega
  by_cases ne : M.Nonempty
  · obtain ⟨m₀,m0⟩ := ne
    exact rotated_three_rows (m₀:=m₀) free reg ht order no av bv ab exactS pP yP py uk wk uw
      cS ca cb others zP cz zu zw (fun m mv zm mc h =>
        card_le_one.mp le1 m (mem_filter.mpr ⟨mv,zm,mc,h⟩) m₀ m0)
  · exact rotated_three_rows (m₀:=0) free reg ht order no av bv ab exactS pP yP py uk wk uw
      cS ca cb others zP cz zu zw (fun m mv zm mc h =>
        (ne ⟨m,mem_filter.mpr ⟨mv,zm,mc,h⟩⟩).elim)

/-- If the third locked row points to two original blockers u, w, no
successor of u or w points to it, so the three-row edit has no unpaid
return. Hence c points to every common successor of p and y. -/
theorem locked_row_sees_common_targets {D : CH.Digraph} {V : Finset ℕ}
    {t a b c x j p y u w : ℕ}
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (av : a ∈ V) (bv : b ∈ V) (ab : a ≠ b)
    (exactS : inN D V a ∩ inN D V b = {x,j})
    (pP : p ∈ outN D V a ∩ outN D V b) (yP : y ∈ outN D V a ∩ outN D V b) (py : p ≠ y)
    (uk : u ∈ blockers D (V \ {a,b}) x j p y) (wk : w ∈ blockers D (V \ {a,b}) x j p y)
    (uw : u ≠ w)
    (cS : c ∈ inN D V p ∩ inN D V y) (ca : c ≠ a) (cb : c ≠ b)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ≠ a → r ≠ b → r ≠ c →
      ∃ v, FreeTarget D V r v ∧ v ∉ inN D V p ∩ inN D V y)
    (cu : D c u = true) (cw : D c w = true) :
    ∀ z ∈ outN D V p ∩ outN D V y, D c z = true := by
  classical
  intro z zP
  by_contra cz
  have uv : u ∈ V := (mem_sdiff.mp (mem_outN.mp (mem_filter.mp uk).1).1).1
  have wv : w ∈ V := (mem_sdiff.mp (mem_outN.mp (mem_filter.mp wk).1).1).1
  have cv : c ∈ V := (mem_inN.mp (mem_inter.mp cS).1).1
  exact rotated_three_rows (m₀:=0) free reg ht order no av bv ab exactS pP yP py uk wk uw
    cS ca cb others zP cz (fun e => cz (by rw [e]; exact cu)) (fun e => cz (by rw [e]; exact cw))
    (fun m mv _ mc h => by
      rcases h with ⟨um,_⟩ | ⟨wm,_⟩
      · exact (free c 3 (by decide) (by decide)
          (.step uv cu (.step mv um (.step cv mc (.refl _))))).elim
      · exact (free c 3 (by decide) (by decide)
          (.step wv cw (.step mv wm (.step cv mc (.refl _))))).elim)

#print axioms three_target_repair
#print axioms rotated_three_rows
#print axioms three_row_obstruction
#print axioms locked_row_sees_common_targets
end LeanCH.BR.RotatedThreeRows
