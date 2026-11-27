import checkpoints.shen_extension.ReverseTargetBudget

/-! Two short rows x, j with a common fresh target p and two shared blockers
u, w. All statements are about the original retained graph on U.

* `two_target_repair`: a second head y, fresh for j, repairs both rows.
* `blocker_head_repair`: if x and j point to y, the shortage left at w is
  repaired by w→y.
* `target_head_repair`: likewise the shortage left at p is repaired by p→y.
* `second_target_forced`: in a source every other common target of the bank
  is a common head of x, j, u, w and p. -/

namespace LeanCH.BR.TwoRowShared
open Finset BRq2 BRq3 BR45 TripleBank

private theorem lose (S T : Finset ℕ) : S.card ≤ (S \ T).card+T.card :=
  card_le_card_sdiff_add_card

/-- A label pointed to by the whole bank, and each of its successors, keeps
every original head when the bank is deleted. -/
theorem bank_rich {D : CH.Digraph} {V B : Finset ℕ} {t y : ℕ}
    (native : QFree D V 3) (reg : OutEq (t+1) D V) (bv : B⊆V)
    (yu : y∈V\B) (common : ∀ b∈B, D b y=true) :
    (outN D (V\B) y).card=t+1 ∧ ∀ m∈V\B, D y m=true → (outN D (V\B) m).card=t+1 := by
  classical
  have uv : V\B⊆V := sdiff_subset
  have split (a) (au : a∈V\B) : (outN D B a).card+(outN D (V\B) a).card=t+1 := by
    have h := card_outN_union (D:=D) (show Disjoint B (V\B) from disjoint_sdiff) a
    rw [union_sdiff_of_subset bv,reg _ (uv au)] at h
    omega
  constructor
  · have empty : outN D B y=∅ := eq_empty_iff_forall_notMem.mpr (fun b hb =>
      digonfree native (by decide) (bv (outN_subset hb)) (uv yu)
        (common b (outN_subset hb)) (mem_outN.mp hb).2)
    have h := split y yu
    rw [empty,card_empty,zero_add] at h
    exact h
  · intro m mu ym
    have empty : outN D B m=∅ := eq_empty_iff_forall_notMem.mpr (fun b hb =>
      native b 3 (by decide) (by decide) (.step (uv yu) (common b (outN_subset hb))
        (.step (uv mu) ym (.step (bv (outN_subset hb)) (mem_outN.mp hb).2 (.refl _)))))
    have h := split m mu
    rw [empty,card_empty,zero_add] at h
    exact h

/-- Row x takes p and row j takes y. Shared blockers lie among u, w.
The payments are p→u, u→j, y→w, w→x, and one arc at every other blocker. -/
theorem two_target_repair {D : CH.Digraph} {U : Finset ℕ} {t x j p y u w : ℕ}
    (safe : QFree D U 3) (xu : x∈U) (ju : j∈U) (pu : p∈U) (yu : y∈U)
    (xj : x≠j) (py : p≠y) (pnx : p≠x) (pnj : p≠j) (ynx : y≠x) (ynj : y≠j)
    (xp : D x p≠true) (px : D p x≠true) (pj : D p j≠true)
    (jy : D j y≠true) (yj : D y j≠true) (yx : D y x≠true)
    (pu' : D p u=true) (pw : D p w=true)
    (only : ∀ m∈U, D p m=true → D y m=true → D m x=true → D m j=true → m=u ∨ m=w)
    (needx : t≤(outN D U x).card+1) (needj : t≤(outN D U j).card+1)
    (richP : t+1≤(outN D U p).card) (richY : t+1≤(outN D U y).card)
    (succP : ∀ m∈U, D p m=true → t+1≤(outN D U m).card)
    (succY : ∀ m∈U, D y m=true → t+1≤(outN D U m).card)
    (floor : ∀ i∈U, i≠x → i≠j → t≤(outN D U i).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E x p=true ∧ E j y=true ∧
      ∀ i∈U, t≤(outN E U i).card := by
  classical
  have loop {a} (au : a∈U) : D a a≠true := loopfree safe (by decide) au
  have up : u≠p := fun e => loop pu (e ▸ pu')
  have wp : w≠p := fun e => loop pu (e ▸ pw)
  have ux : u≠x := fun e => px (e ▸ pu')
  have uj : u≠j := fun e => pj (e ▸ pu')
  have wx : w≠x := fun e => px (e ▸ pw)
  have wj : w≠j := fun e => pj (e ▸ pw)
  let A (m : ℕ) : Finset ℕ := if m=x then {p} else if m=j then {y} else ∅
  let C (m : ℕ) : Finset ℕ :=
    if m=p then {u} else if m=y then {w} else if m=u then {j} else if m=w then {x} else
      (if D p m=true ∧ D m x=true then {x} else ∅) ∪
      (if D y m=true ∧ D m j=true then {j} else ∅)
  have spec {a b} (h : b∈A a) : (a=x ∧ b=p) ∨ (a=j ∧ b=y) := by
    by_cases ax : a=x
    · exact Or.inl ⟨ax,by simpa [A,ax] using h⟩
    · by_cases aj : a=j
      · exact Or.inr ⟨aj,by simpa [A,aj,xj.symm] using h⟩
      · simp [A,ax,aj] at h
  have Ap : A p=∅ := by simp [A,pnx,pnj]
  have Ay : A y=∅ := by simp [A,ynx,ynj]
  obtain ⟨ok,rows⟩ := patch_certificate (A:=A) (C:=C) safe
    (fun a _ b h => by
      rcases spec h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨pu,pnx,xp,px⟩
      · exact ⟨yu,ynj,jy,yj⟩)
    (fun a _ b h m mu bm ma => by
      rcases spec h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · by_cases e : m=u
        · exact Or.inl (by simp [C,e])
        · refine Or.inr ?_
          have mp : m≠b := fun q => px (q ▸ ma)
          have my : m≠y := fun q => yx (q ▸ ma)
          by_cases q : m=w
          · subst q; simp [C,mp,my,e]
          · simp [C,mp,my,e,q,bm,ma]
      · by_cases e : m=w
        · exact Or.inl (by simp [C,py.symm,e])
        · refine Or.inr ?_
          have mp : m≠p := fun q => pj (q ▸ ma)
          have my : m≠b := fun q => loop yu (q ▸ bm)
          by_cases q : m=u
          · subst q; simp [C,mp,my]
          · simp [C,mp,my,e,q,bm,ma])
    (fun a _ b h c g => by
      rcases spec h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rw [Ap] at g; exact (notMem_empty _ g).elim
      · rw [Ay] at g; exact (notMem_empty _ g).elim)
  refine ⟨_,ok,decide_eq_true (Or.inl (by simp [A])),
    decide_eq_true (Or.inl (by simp [A,xj.symm])),?_⟩
  intro i iu
  rw [rows i iu]
  by_cases ix : i=x
  · subst ix
    have c : C i=∅ := by simp [C,pnx.symm,ynx.symm,ux.symm,wx.symm,px,yx]
    simpa [c,A] using needx
  by_cases ij : i=j
  · subst ij
    have c : C i=∅ := by simp [C,pnj.symm,ynj.symm,uj.symm,wj.symm,pj,yj]
    simpa [c,A,ix] using needj
  have a0 : A i=∅ := by simp [A,ix,ij]
  rw [a0,card_empty,Nat.add_zero]
  by_cases ip : i=p
  · subst ip
    have c : C i={u} := by simp [C]
    have l := lose (outN D U i) {u}
    rw [c]; simp at l; omega
  by_cases iy : i=y
  · subst iy
    have c : C i={w} := by simp [C,ip]
    have l := lose (outN D U i) {w}
    rw [c]; simp at l; omega
  by_cases iuu : i=u
  · subst iuu
    have c : C i={j} := by simp [C,ip,iy]
    have l := lose (outN D U i) {j}
    have r := succP i iu pu'
    rw [c]; simp at l; omega
  by_cases iw : i=w
  · subst iw
    have c : C i={x} := by simp [C,ip,iy,iuu]
    have l := lose (outN D U i) {x}
    have r := succP i iu pw
    rw [c]; simp at l; omega
  by_cases c1 : D p i=true ∧ D i x=true
  · by_cases c2 : D y i=true ∧ D i j=true
    · exact ((only i iu c1.1 c2.1 c1.2 c2.2).elim iuu iw).elim
    · have c : C i={x} := by simp [C,ip,iy,iuu,iw,c1,c2]
      have l := lose (outN D U i) {x}
      have r := succP i iu c1.1
      rw [c]; simp at l; omega
  · by_cases c2 : D y i=true ∧ D i j=true
    · have c : C i={j} := by simp [C,ip,iy,iuu,iw,c1,c2]
      have l := lose (outN D U i) {j}
      have r := succY i iu c2.1
      rw [c]; simp at l; omega
    · have c : C i=∅ := by simp [C,ip,iy,iuu,iw,c1,c2]
      rw [c,sdiff_empty]
      exact floor i iu ix ij

/-- Both rows take p and p drops u. Row w loses both arcs to x, j and takes
the head y. Because x and j point to y, no successor of y points to x or j,
so every return middle of w→y other than p still has its spare arc. -/
theorem blocker_head_repair {D : CH.Digraph} {U : Finset ℕ} {t x j p y u w : ℕ}
    (safe : QFree D U 3) (xu : x∈U) (ju : j∈U) (pu : p∈U) (yu : y∈U) (wu : w∈U)
    (xj : x≠j) (pnx : p≠x) (pnj : p≠j) (ynp : y≠p)
    (xp : D x p≠true) (px : D p x≠true) (jp : D j p≠true) (pj : D p j≠true)
    (xy : D x y=true) (jy : D j y=true)
    (pu' : D p u=true) (pw : D p w=true) (ux : D u x=true)
    (wx : D w x=true) (wy : D w y≠true)
    (only : ∀ m∈U, D p m=true → D m x=true → D m j=true → m=u ∨ m=w)
    (needx : t≤(outN D U x).card+1) (needj : t≤(outN D U j).card+1)
    (richP : t+1≤(outN D U p).card) (richY : t+1≤(outN D U y).card)
    (succP : ∀ m∈U, D p m=true → t+1≤(outN D U m).card)
    (succY : ∀ m∈U, D y m=true → t+1≤(outN D U m).card)
    (floor : ∀ i∈U, i≠x → i≠j → t≤(outN D U i).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E x p=true ∧ E j p=true ∧ E w y=true ∧
      ∀ i∈U, t≤(outN E U i).card := by
  classical
  have loop {a} (au : a∈U) : D a a≠true := loopfree safe (by decide) au
  have wnp : w≠p := fun e => loop pu (e ▸ pw)
  have unx : u≠x := fun e => px (e ▸ pu')
  have unj : u≠j := fun e => pj (e ▸ pu')
  have wnx : w≠x := fun e => px (e ▸ pw)
  have wnj : w≠j := fun e => pj (e ▸ pw)
  have ynx : y≠x := fun e => loop xu (e ▸ xy)
  have ynj : y≠j := fun e => loop ju (e ▸ jy)
  have yx : D y x≠true := digonfree safe (by decide) xu yu xy
  have yj : D y j≠true := digonfree safe (by decide) ju yu jy
  have ynw : y≠w := fun e => yx (e ▸ wx)
  have yw : D y w≠true := fun h => safe y 3 (by decide) (by decide)
    (.step wu h (.step xu wx (.step yu xy (.refl _))))
  let A (m : ℕ) : Finset ℕ :=
    if m=x then {p} else if m=j then {p} else if m=w then {y} else ∅
  let C (m : ℕ) : Finset ℕ :=
    if m=p then {u} else if m=w then {x,j} else if m=y then {p} else if m=u then ∅ else
      ((if D p m=true ∧ D m x=true then {x} else ∅) ∪
      (if D p m=true ∧ D m j=true then {j} else ∅)) ∪
      (if D y m=true ∧ D m w=true then {w} else ∅)
  have spec {a b} (h : b∈A a) : (a=x ∧ b=p) ∨ (a=j ∧ b=p) ∨ (a=w ∧ b=y) := by
    by_cases ax : a=x
    · exact Or.inl ⟨ax,by simpa [A,ax] using h⟩
    · by_cases aj : a=j
      · exact Or.inr (Or.inl ⟨aj,by simpa [A,aj,xj.symm] using h⟩)
      · by_cases aw : a=w
        · exact Or.inr (Or.inr ⟨aw,by simpa [A,aw,wnx,wnj] using h⟩)
        · simp [A,ax,aj,aw] at h
  have Ap : A p=∅ := by simp [A,pnx,pnj,wnp.symm]
  have Ay : A y=∅ := by simp [A,ynx,ynj,ynw]
  obtain ⟨ok,rows⟩ := patch_certificate (A:=A) (C:=C) safe
    (fun a _ b h => by
      rcases spec h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨pu,pnx,xp,px⟩
      · exact ⟨pu,pnj,jp,pj⟩
      · exact ⟨yu,ynw,wy,yw⟩)
    (fun a _ b h m mu bm ma => by
      rcases spec h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · by_cases e : m=u
        · exact Or.inl (by simp [C,e])
        · refine Or.inr ?_
          have mp : m≠b := fun q => px (q ▸ ma)
          have my : m≠y := fun q => yx (q ▸ ma)
          by_cases q : m=w
          · simp [C,q,wnp]
          · simp [C,mp,my,e,q,bm,ma]
      · by_cases e : m=u
        · exact Or.inl (by simp [C,e])
        · refine Or.inr ?_
          have mp : m≠b := fun q => pj (q ▸ ma)
          have my : m≠y := fun q => yj (q ▸ ma)
          by_cases q : m=w
          · simp [C,q,wnp]
          · simp [C,mp,my,e,q,bm,ma]
      · by_cases e : m=p
        · exact Or.inl (by simp [C,ynp,ynw,e])
        · refine Or.inr ?_
          have mw : m≠a := fun q => loop wu (q ▸ ma)
          have my : m≠b := fun q => loop yu (q ▸ bm)
          have mu' : m≠u := fun q => safe b 3 (by decide) (by decide)
            (.step mu bm (.step xu (q ▸ ux) (.step yu xy (.refl _))))
          simp [C,e,mw,my,mu',bm,ma])
    (fun a _ b h c g => by
      rcases spec h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rw [Ap] at g; exact (notMem_empty _ g).elim
      · rw [Ap] at g; exact (notMem_empty _ g).elim
      · rw [Ay] at g; exact (notMem_empty _ g).elim)
  refine ⟨_,ok,decide_eq_true (Or.inl (by simp [A])),
    decide_eq_true (Or.inl (by simp [A,xj.symm])),
    decide_eq_true (Or.inl (by simp [A,wnx,wnj])),?_⟩
  intro i iu
  rw [rows i iu]
  by_cases ix : i=x
  · subst ix
    have c : C i=∅ := by simp [C,pnx.symm,wnx.symm,ynx.symm,unx.symm,px,yx]
    simpa [c,A] using needx
  by_cases ij : i=j
  · subst ij
    have c : C i=∅ := by simp [C,pnj.symm,wnj.symm,ynj.symm,unj.symm,pj,yj]
    simpa [c,A,ix] using needj
  by_cases iw : i=w
  · subst iw
    have c : C i={x,j} := by simp [C,wnp]
    have a : A i={y} := by simp [A,ix,ij]
    have l := lose (outN D U i) {x,j}
    have two : ({x,j} : Finset ℕ).card=2 := card_pair xj
    have r := succP i iu pw
    rw [c,a,card_singleton]
    omega
  have a0 : A i=∅ := by simp [A,ix,ij,iw]
  rw [a0,card_empty,Nat.add_zero]
  by_cases ip : i=p
  · subst ip
    have c : C i={u} := by simp [C]
    have l := lose (outN D U i) {u}
    rw [c]; simp at l; omega
  by_cases iy : i=y
  · subst iy
    have c : C i={p} := by simp [C,ip,iw]
    have l := lose (outN D U i) {p}
    rw [c]; simp at l; omega
  by_cases iuu : i=u
  · subst iuu
    have c : C i=∅ := by simp [C,ip,iw,iy]
    rw [c,sdiff_empty]
    exact floor i iu ix ij
  by_cases c1 : D p i=true ∧ D i x=true
  · have n2 : ¬(D p i=true ∧ D i j=true) := fun c2 =>
      (only i iu c1.1 c1.2 c2.2).elim iuu iw
    have n3 : ¬(D y i=true ∧ D i w=true) := fun c3 => safe x 3 (by decide) (by decide)
      (.step yu xy (.step iu c3.1 (.step xu c1.2 (.refl _))))
    have nj : D i j≠true := fun h => n2 ⟨c1.1,h⟩
    have c : C i={x} := by simp [C,ip,iw,iy,iuu,c1.1,c1.2,nj,n3]
    have l := lose (outN D U i) {x}
    have r := succP i iu c1.1
    rw [c]; simp at l; omega
  by_cases c2 : D p i=true ∧ D i j=true
  · have n3 : ¬(D y i=true ∧ D i w=true) := fun c3 => safe j 3 (by decide) (by decide)
      (.step yu jy (.step iu c3.1 (.step ju c2.2 (.refl _))))
    have nx : D i x≠true := fun h => c1 ⟨c2.1,h⟩
    have c : C i={j} := by simp [C,ip,iw,iy,iuu,c2.1,c2.2,nx,n3]
    have l := lose (outN D U i) {j}
    have r := succP i iu c2.1
    rw [c]; simp at l; omega
  by_cases c3 : D y i=true ∧ D i w=true
  · have c : C i={w} := by simp [C,ip,iw,iy,iuu,c1,c2,c3]
    have l := lose (outN D U i) {w}
    have r := succY i iu c3.1
    rw [c]; simp at l; omega
  · have c : C i=∅ := by simp [C,ip,iw,iy,iuu,c1,c2,c3]
    rw [c,sdiff_empty]
    exact floor i iu ix ij

/-- Both rows take p and p drops both shared blockers. Row p then takes the
head y. No successor of y points to x or j, and the rows that have paid for
x or j are successors of p, so no return middle of p→y is tight. -/
theorem target_head_repair {D : CH.Digraph} {U : Finset ℕ} {t x j p y u w : ℕ}
    (safe : QFree D U 3) (xu : x∈U) (ju : j∈U) (pu : p∈U) (yu : y∈U)
    (xj : x≠j) (pnx : p≠x) (pnj : p≠j) (ynp : y≠p)
    (xp : D x p≠true) (px : D p x≠true) (jp : D j p≠true) (pj : D p j≠true)
    (xy : D x y=true) (jy : D j y=true)
    (pu' : D p u=true) (pw : D p w=true) (py : D p y≠true) (yp : D y p≠true)
    (only : ∀ m∈U, D p m=true → D m x=true → D m j=true → m=u ∨ m=w)
    (needx : t≤(outN D U x).card+1) (needj : t≤(outN D U j).card+1)
    (richP : t+1≤(outN D U p).card)
    (succP : ∀ m∈U, D p m=true → t+1≤(outN D U m).card)
    (succY : ∀ m∈U, D y m=true → t+1≤(outN D U m).card)
    (floor : ∀ i∈U, i≠x → i≠j → t≤(outN D U i).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E x p=true ∧ E j p=true ∧ E p y=true ∧
      ∀ i∈U, t≤(outN E U i).card := by
  classical
  have loop {a} (au : a∈U) : D a a≠true := loopfree safe (by decide) au
  have unx : u≠x := fun e => px (e ▸ pu')
  have unj : u≠j := fun e => pj (e ▸ pu')
  have wnx : w≠x := fun e => px (e ▸ pw)
  have wnj : w≠j := fun e => pj (e ▸ pw)
  have ynx : y≠x := fun e => loop xu (e ▸ xy)
  have ynj : y≠j := fun e => loop ju (e ▸ jy)
  have yx : D y x≠true := digonfree safe (by decide) xu yu xy
  have yj : D y j≠true := digonfree safe (by decide) ju yu jy
  let A (m : ℕ) : Finset ℕ :=
    if m=x then {p} else if m=j then {p} else if m=p then {y} else ∅
  let C (m : ℕ) : Finset ℕ :=
    if m=p then {u,w} else if m=u then ∅ else if m=w then ∅ else
      ((if D p m=true ∧ D m x=true then {x} else ∅) ∪
      (if D p m=true ∧ D m j=true then {j} else ∅)) ∪
      (if D y m=true ∧ D m p=true then {p} else ∅)
  have spec {a b} (h : b∈A a) : (a=x ∧ b=p) ∨ (a=j ∧ b=p) ∨ (a=p ∧ b=y) := by
    by_cases ax : a=x
    · exact Or.inl ⟨ax,by simpa [A,ax] using h⟩
    · by_cases aj : a=j
      · exact Or.inr (Or.inl ⟨aj,by simpa [A,aj,xj.symm] using h⟩)
      · by_cases ap : a=p
        · exact Or.inr (Or.inr ⟨ap,by simpa [A,ap,pnx,pnj] using h⟩)
        · simp [A,ax,aj,ap] at h
  have Ap {c} (g : c∈A p) : c=y := by simpa [A,pnx,pnj] using g
  have Ay : A y=∅ := by simp [A,ynx,ynj,ynp]
  have noYX : patch D A C y x≠true := fun h => by
    rcases of_decide_eq_true h with h1 | h2
    · rw [Ay] at h1; exact notMem_empty _ h1
    · exact yx h2.1
  have noYJ : patch D A C y j≠true := fun h => by
    rcases of_decide_eq_true h with h1 | h2
    · rw [Ay] at h1; exact notMem_empty _ h1
    · exact yj h2.1
  obtain ⟨ok,rows⟩ := patch_certificate (A:=A) (C:=C) safe
    (fun a _ b h => by
      rcases spec h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨pu,pnx,xp,px⟩
      · exact ⟨pu,pnj,jp,pj⟩
      · exact ⟨yu,ynp,py,yp⟩)
    (fun a _ b h m mu bm ma => by
      rcases spec h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · by_cases e : m=u ∨ m=w
        · exact Or.inl (by rcases e with e | e <;> simp [C,e])
        · refine Or.inr ?_
          have mp : m≠b := fun q => px (q ▸ ma)
          have m1 : m≠u := fun q => e (Or.inl q)
          have m2 : m≠w := fun q => e (Or.inr q)
          simp [C,mp,m1,m2,bm,ma]
      · by_cases e : m=u ∨ m=w
        · exact Or.inl (by rcases e with e | e <;> simp [C,e])
        · refine Or.inr ?_
          have mp : m≠b := fun q => pj (q ▸ ma)
          have m1 : m≠u := fun q => e (Or.inl q)
          have m2 : m≠w := fun q => e (Or.inr q)
          simp [C,mp,m1,m2,bm,ma]
      · refine Or.inr ?_
        have mp : m≠a := fun q => loop pu (q ▸ ma)
        have m1 : m≠u := fun q => digonfree safe (by decide) pu mu (q ▸ pu') ma
        have m2 : m≠w := fun q => digonfree safe (by decide) pu mu (q ▸ pw) ma
        simp [C,mp,m1,m2,bm,ma])
    (fun a _ b h c g => by
      rcases spec h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have e := Ap g; subst e; exact ⟨ynx,noYX⟩
      · have e := Ap g; subst e; exact ⟨ynj,noYJ⟩
      · rw [Ay] at g; exact (notMem_empty _ g).elim)
  refine ⟨_,ok,decide_eq_true (Or.inl (by simp [A])),
    decide_eq_true (Or.inl (by simp [A,xj.symm])),
    decide_eq_true (Or.inl (by simp [A,pnx,pnj])),?_⟩
  intro i iu
  rw [rows i iu]
  by_cases ix : i=x
  · subst ix
    have c : C i=∅ := by simp [C,pnx.symm,unx.symm,wnx.symm,px,yx]
    simpa [c,A] using needx
  by_cases ij : i=j
  · subst ij
    have c : C i=∅ := by simp [C,pnj.symm,unj.symm,wnj.symm,pj,yj]
    simpa [c,A,ix] using needj
  by_cases ip : i=p
  · subst ip
    have c : C i={u,w} := by simp [C]
    have a : A i={y} := by simp [A,ix,ij]
    have l := lose (outN D U i) {u,w}
    have two : ({u,w} : Finset ℕ).card≤2 := card_le_two
    rw [c,a,card_singleton]
    omega
  have a0 : A i=∅ := by simp [A,ix,ij,ip]
  rw [a0,card_empty,Nat.add_zero]
  by_cases iuu : i=u
  · subst iuu
    have c : C i=∅ := by simp [C,ip]
    rw [c,sdiff_empty]
    exact floor i iu ix ij
  by_cases iw : i=w
  · subst iw
    have c : C i=∅ := by simp [C,ip,iuu]
    rw [c,sdiff_empty]
    exact floor i iu ix ij
  have n3 (h : D p i=true) : ¬(D y i=true ∧ D i p=true) := fun c3 =>
    digonfree safe (by decide) pu iu h c3.2
  by_cases c1 : D p i=true ∧ D i x=true
  · have n2 : ¬(D p i=true ∧ D i j=true) := fun c2 =>
      (only i iu c1.1 c1.2 c2.2).elim iuu iw
    have nj : D i j≠true := fun h => n2 ⟨c1.1,h⟩
    have c : C i={x} := by simp [C,ip,iw,iuu,c1.1,c1.2,nj,n3 c1.1]
    have l := lose (outN D U i) {x}
    have r := succP i iu c1.1
    rw [c]; simp at l; omega
  by_cases c2 : D p i=true ∧ D i j=true
  · have nx : D i x≠true := fun h => c1 ⟨c2.1,h⟩
    have c : C i={j} := by simp [C,ip,iw,iuu,c2.1,c2.2,nx,n3 c2.1]
    have l := lose (outN D U i) {j}
    have r := succP i iu c2.1
    rw [c]; simp at l; omega
  by_cases c3 : D y i=true ∧ D i p=true
  · have c : C i={p} := by simp [C,ip,iw,iuu,c1,c2,c3]
    have l := lose (outN D U i) {p}
    have r := succY i iu c3.1
    rw [c]; simp at l; omega
  · have c : C i=∅ := by simp [C,ip,iw,iuu,c1,c2,c3]
    rw [c,sdiff_empty]
    exact floor i iu ix ij

/-- In a source with two short rows, one common fresh target p and exactly
two shared blockers u, w, every other common target y of the bank is a
common head of x, j, u, w and p. -/
theorem second_target_forced {D : CH.Digraph} {V B : Finset ℕ} {t b x j p y u w : ℕ}
    (native : QFree D V 3) (reg : OutEq (t+1) D V) (bv : B⊆V) (bb : b∈B)
    (no : BypassRepair.NoHost 3 t) (size : (V\B).card≤3*t)
    (xu : x∈V\B) (ju : j∈V\B) (pu : p∈V\B) (yu : y∈V\B) (uu : u∈V\B) (wu : w∈V\B)
    (xj : x≠j) (py : p≠y)
    (hitx : ∀ b∈B, D x b=true) (hitj : ∀ b∈B, D j b=true)
    (cp : ∀ b∈B, D b p=true) (cy : ∀ b∈B, D b y=true)
    (xp : D x p≠true) (jp : D j p≠true)
    (pu' : D p u=true) (pw : D p w=true)
    (ux : D u x=true) (wx : D w x=true)
    (only : ∀ m∈V\B, D p m=true → D m x=true → D m j=true → m=u ∨ m=w)
    (needx : t≤(outN D (V\B) x).card+1) (needj : t≤(outN D (V\B) j).card+1)
    (floor : ∀ i∈V\B, i≠x → i≠j → t≤(outN D (V\B) i).card) :
    D x y=true ∧ D j y=true ∧ D u y=true ∧ D w y=true ∧ D p y=true := by
  classical
  have uv : V\B⊆V := sdiff_subset
  have safe : QFree D (V\B) 3 := native.mono_set uv
  have bV := bv bb
  have tri {a c d} (av : a∈V) (cv : c∈V) (dv : d∈V) (ac : D a c=true) (cd : D c d=true) :
      D d a≠true := fun da => native a 3 (by decide) (by decide)
    (.step cv ac (.step dv cd (.step av da (.refl _))))
  have px : D p x≠true := tri (uv xu) bV (uv pu) (hitx b bb) (cp b bb)
  have pj : D p j≠true := tri (uv ju) bV (uv pu) (hitj b bb) (cp b bb)
  have yx : D y x≠true := tri (uv xu) bV (uv yu) (hitx b bb) (cy b bb)
  have yj : D y j≠true := tri (uv ju) bV (uv yu) (hitj b bb) (cy b bb)
  have pnx : p≠x := fun e => digonfree native (by decide) (uv xu) bV (hitx b bb) (e ▸ cp b bb)
  have pnj : p≠j := fun e => digonfree native (by decide) (uv ju) bV (hitj b bb) (e ▸ cp b bb)
  have ynx : y≠x := fun e => digonfree native (by decide) (uv xu) bV (hitx b bb) (e ▸ cy b bb)
  have ynj : y≠j := fun e => digonfree native (by decide) (uv ju) bV (hitj b bb) (e ▸ cy b bb)
  obtain ⟨rp,sp⟩ := bank_rich native reg bv pu cp
  obtain ⟨ry,sy⟩ := bank_rich native reg bv yu cy
  have succP : ∀ m∈V\B, D p m=true → t+1≤(outN D (V\B) m).card := fun m mu h => (sp m mu h).ge
  have succY : ∀ m∈V\B, D y m=true → t+1≤(outN D (V\B) m).card := fun m mu h => (sy m mu h).ge
  have host {E : CH.Digraph} (good : QFree E (V\B) 3)
      (rows : ∀ i∈V\B, t≤(outN E (V\B) i).card) : False :=
    no E (V\B) ⟨x,xu⟩ size good rows
  have jy : D j y=true := by
    by_contra h
    obtain ⟨E,good,_,_,rows⟩ := two_target_repair safe xu ju pu yu xj py pnx pnj ynx ynj
      xp px pj h yj yx pu' pw (fun m mu a _ c d => only m mu a c d)
      needx needj rp.ge ry.ge succP succY floor
    exact host good rows
  have xy : D x y=true := by
    by_contra h
    obtain ⟨E,good,_,_,rows⟩ := two_target_repair safe ju xu pu yu xj.symm py pnj pnx ynj ynx
      jp pj px h yx yj pu' pw (fun m mu a _ c d => only m mu a d c)
      needj needx rp.ge ry.ge succP succY (fun i iu a c => floor i iu c a)
    exact host good rows
  have wy : D w y=true := by
    by_contra h
    obtain ⟨E,good,_,_,_,rows⟩ := blocker_head_repair safe xu ju pu yu wu xj pnx pnj py.symm
      xp px jp pj xy jy pu' pw ux wx h only needx needj rp.ge ry.ge succP succY floor
    exact host good rows
  have uy : D u y=true := by
    by_contra h
    obtain ⟨E,good,_,_,_,rows⟩ := blocker_head_repair safe xu ju pu yu uu xj pnx pnj py.symm
      xp px jp pj xy jy pw pu' wx ux h (fun m mu a c d => (only m mu a c d).symm)
      needx needj rp.ge ry.ge succP succY floor
    exact host good rows
  refine ⟨xy,jy,uy,wy,?_⟩
  by_contra h
  have yp : D y p≠true := fun yp => safe y 3 (by decide) (by decide)
    (.step pu yp (.step uu pu' (.step yu uy (.refl _))))
  obtain ⟨E,good,_,_,_,rows⟩ := target_head_repair safe xu ju pu yu xj pnx pnj py.symm
    xp px jp pj xy jy pu' pw h yp only needx needj rp.ge succP succY floor
  exact host good rows

#print axioms bank_rich
#print axioms two_target_repair
#print axioms blocker_head_repair
#print axioms target_head_repair
#print axioms second_target_forced
/-- Delete x and j instead of the bank. The bank labels are then common
fresh targets for u and w, and p is their only shared blocker. If u and w
were the only common predecessors of x and j, the edit u→b₁, w→b₂ would
restore every row. So a third common predecessor exists. -/
theorem third_common_parent {D : CH.Digraph} {V : Finset ℕ} {t b₁ b₂ x j p u w : ℕ}
    (native : QFree D V 3) (reg : OutEq (t+1) D V) (order : V.card=3*t+2)
    (no : BypassRepair.NoHost 3 t) (b1v : b₁∈V) (b2v : b₂∈V) (bne : b₁≠b₂)
    (xu : x∈V\{b₁,b₂}) (ju : j∈V\{b₁,b₂}) (pu : p∈V\{b₁,b₂})
    (uu : u∈V\{b₁,b₂}) (wu : w∈V\{b₁,b₂}) (xj : x≠j) (uw : u≠w)
    (x1 : D x b₁=true) (x2 : D x b₂=true) (j1 : D j b₁=true) (j2 : D j b₂=true)
    (p1 : D b₁ p=true) (p2 : D b₂ p=true)
    (xp : D x p≠true) (jp : D j p≠true)
    (pu' : D p u=true) (pw : D p w=true)
    (ux : D u x=true) (uj : D u j=true) (wx : D w x=true) (wj : D w j=true)
    (only : ∀ m∈V\{b₁,b₂}, D p m=true → D m x=true → D m j=true → m=u ∨ m=w)
    (needx : t≤(outN D (V\{b₁,b₂}) x).card+1) (needj : t≤(outN D (V\{b₁,b₂}) j).card+1)
    (floor : ∀ i∈V\{b₁,b₂}, i≠x → i≠j → t≤(outN D (V\{b₁,b₂}) i).card) :
    ∃ r∈V, r≠u ∧ r≠w ∧ D r x=true ∧ D r j=true := by
  classical
  by_contra none
  let B : Finset ℕ := {b₁,b₂}
  have bv : B⊆V := insert_subset b1v (singleton_subset_iff.mpr b2v)
  have uvB : V\B⊆V := sdiff_subset
  have xv := uvB xu
  have jv := uvB ju
  have pv := uvB pu
  have uv' := uvB uu
  have wv := uvB wu
  have loop {a} (av : a∈V) : D a a≠true := loopfree native (by decide) av
  have tri {a c d} (av : a∈V) (cv : c∈V) (dv : d∈V) (ac : D a c=true) (cd : D c d=true) :
      D d a≠true := fun da => native a 3 (by decide) (by decide)
    (.step cv ac (.step dv cd (.step av da (.refl _))))
  have sizeB : (V\B).card≤3*t := by
    rw [card_sdiff_of_subset bv,show B.card=2 from card_pair bne,order]; omega
  have shared : ∀ m∈V, D b₁ m=true → D b₂ m=true → D m u=true → D m w=true → m=p := by
    intro m mv a c d _
    by_contra mp
    have mB : m∈V\B := mem_sdiff.mpr ⟨mv,fun h => by
      rcases mem_insert.mp h with e | e
      · exact loop b1v (e ▸ a)
      · exact loop b2v (mem_singleton.mp e ▸ c)⟩
    have all := second_target_forced (B:=B) (b:=b₁) (y:=m) native reg bv (by simp [B]) no sizeB
      xu ju pu mB uu wu xj (fun e => mp e.symm)
      (fun b bm => by rcases mem_insert.mp bm with e | e
                      · exact e ▸ x1
                      · exact mem_singleton.mp e ▸ x2)
      (fun b bm => by rcases mem_insert.mp bm with e | e
                      · exact e ▸ j1
                      · exact mem_singleton.mp e ▸ j2)
      (fun b bm => by rcases mem_insert.mp bm with e | e
                      · exact e ▸ p1
                      · exact mem_singleton.mp e ▸ p2)
      (fun b bm => by rcases mem_insert.mp bm with e | e
                      · exact e ▸ a
                      · exact mem_singleton.mp e ▸ c)
      xp jp pu' pw ux wx only needx needj floor
    exact digonfree native (by decide) uv' mv all.2.2.1 d
  let K : Finset ℕ := {x,j}
  have kv : K⊆V := insert_subset xv (singleton_subset_iff.mpr jv)
  have sizeK : (V\K).card≤3*t := by
    rw [card_sdiff_of_subset kv,show K.card=2 from card_pair xj,order]; omega
  have inK {a} (av : a∈V) (ax : a≠x) (aj : a≠j) : a∈V\K :=
    mem_sdiff.mpr ⟨av,by simp [K,ax,aj]⟩
  have safe : QFree D (V\K) 3 := native.mono_set sdiff_subset
  have split (a) (av : a∈V) : (outN D K a).card+(outN D (V\K) a).card=t+1 := by
    have h := card_outN_union (D:=D) (show Disjoint K (V\K) from disjoint_sdiff) a
    rw [union_sdiff_of_subset kv,reg _ av] at h
    omega
  have two (a : ℕ) : (outN D K a).card≤2 :=
    (card_le_card outN_subset).trans_eq (card_pair xj)
  have b1x : b₁≠x := fun e => loop xv (e ▸ x1)
  have b1j : b₁≠j := fun e => loop jv (e ▸ j1)
  have b2x : b₂≠x := fun e => loop xv (e ▸ x2)
  have b2j : b₂≠j := fun e => loop jv (e ▸ j2)
  have unx : u≠x := fun e => loop xv (e ▸ ux)
  have unj : u≠j := fun e => loop jv (e ▸ uj)
  have wnx : w≠x := fun e => loop xv (e ▸ wx)
  have wnj : w≠j := fun e => loop jv (e ▸ wj)
  have c1 : ∀ k∈K, D k b₁=true := fun k km => by
    rcases mem_insert.mp km with e | e
    · exact e ▸ x1
    · exact mem_singleton.mp e ▸ j1
  have c2 : ∀ k∈K, D k b₂=true := fun k km => by
    rcases mem_insert.mp km with e | e
    · exact e ▸ x2
    · exact mem_singleton.mp e ▸ j2
  obtain ⟨r1,s1⟩ := bank_rich native reg kv (inK b1v b1x b1j) c1
  obtain ⟨r2,s2⟩ := bank_rich native reg kv (inK b2v b2x b2j) c2
  have fl : ∀ i∈V\K, i≠u → i≠w → t≤(outN D (V\K) i).card := by
    intro i iu iuu iw
    have iv := (mem_sdiff.mp iu).1
    have h := split i iv
    have one : (outN D K i).card≤1 := by
      by_contra! big
      have eq : outN D K i=K := eq_of_subset_of_card_le outN_subset
        ((card_pair xj).le.trans big)
      have ix : D i x=true := (mem_outN.mp (eq ▸ (by simp [K] : x∈K))).2
      have ij : D i j=true := (mem_outN.mp (eq ▸ (by simp [K] : j∈K))).2
      exact none ⟨i,iv,iuu,iw,ix,ij⟩
    omega
  have nu : t≤(outN D (V\K) u).card+1 := by
    have h := split u uv'
    have l := two u
    omega
  have nw : t≤(outN D (V\K) w).card+1 := by
    have h := split w wv
    have l := two w
    omega
  obtain ⟨E,good,_,_,rows⟩ := two_target_repair (x:=u) (j:=w) (p:=b₁) (y:=b₂) (u:=p) (w:=p)
    safe (inK uv' unx unj) (inK wv wnx wnj) (inK b1v b1x b1j) (inK b2v b2x b2j)
    uw bne
    (fun e => digonfree native (by decide) b1v pv p1 (e ▸ pu'))
    (fun e => digonfree native (by decide) b1v pv p1 (e ▸ pw))
    (fun e => digonfree native (by decide) b2v pv p2 (e ▸ pu'))
    (fun e => digonfree native (by decide) b2v pv p2 (e ▸ pw))
    (tri b1v pv uv' p1 pu') (tri uv' xv b1v ux x1) (tri wv xv b1v wx x1)
    (tri b2v pv wv p2 pw) (tri wv xv b2v wx x2) (tri uv' xv b2v ux x2)
    p1 p1
    (fun m mu a c d e => Or.inl (shared m (mem_sdiff.mp mu).1 a c d e))
    nu nw r1.ge r2.ge (fun m mu h => (s1 m mu h).ge) (fun m mu h => (s2 m mu h).ge) fl
  exact no E (V\K) ⟨u,inK uv' unx unj⟩ sizeK good rows

#print axioms third_common_parent
end LeanCH.BR.TwoRowShared
