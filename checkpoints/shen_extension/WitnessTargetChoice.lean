import checkpoints.shen_extension.BankWalkReturnBudget

/-! Choice of the new head in the one-arc witness repair.

* `overlap_floor`: the overlap bound of `tight_return_obstruction` is a count
  that holds along every arc `w→d` and for every `z`.
* `indegree_cap`: the same count with a light head of `w` bounds every indegree.
* `deficit_shift`: with one unpaid tight middle the shortage moves to that middle.
* `common_target_budget`: a head pointed to by the whole bank only has to pay
  for middles that the partial repair has already cut. -/

namespace LeanCH.BR.WalkReturn
open Finset BRq2 BRq3 BR45 TripleBank

/-- Predecessors of w outside the row of z lie outside all three rows of
z, w, d. No arc from z to w is assumed. -/
theorem overlap_floor {D : CH.Digraph} {V : Finset ℕ} {z w d : ℕ}
    (safe : QFree D V 3) (wv : w∈V) (dv : d∈V) (wd : D w d=true) :
    (inN D V w \ outN D V z).card+(outN D V z).card+(outN D V w).card+(outN D V d).card ≤
      V.card+returnOverlap D V z w d := by
  classical
  let B := outN D V z
  let C := outN D V w
  let E := outN D V d
  let S := (B∪E)∪C
  have spare : inN D V w \ B ⊆ V \ S := by
    intro r rm
    obtain ⟨rin,off⟩ := mem_sdiff.mp rm
    obtain ⟨rv,rw⟩ := mem_inN.mp rin
    have ed : r∉E := fun h => safe r 3 (by decide) (by decide)
      (.step wv rw (.step dv wd (.step rv (mem_outN.mp h).2 (.refl _))))
    have cen : r∉C := fun h => digonfree safe (by decide) rv wv rw (mem_outN.mp h).2
    exact mem_sdiff.mpr ⟨rv,by simp [S,off,ed,cen]⟩
  have n := card_le_card spare
  have total := card_sdiff_add_card_eq_card (show S⊆V from
    union_subset (union_subset outN_subset outN_subset) outN_subset)
  have h₁ := card_union_add_card_inter B E
  have h₂ := card_union_add_card_inter (B∪E) C
  change S.card+((B∪E)∩C).card=(B∪E).card+C.card at h₂
  change (inN D V w \ B).card+B.card+C.card+E.card ≤ V.card+((B∩E).card+((B∪E)∩C).card)
  omega

/-- The marked middles outside the row of b, and the common predecessors
of a and c, are predecessors of c missed by b. -/
theorem marked_inside_floor {D : CH.Digraph} {V K : Finset ℕ} {a b c : ℕ}
    (safe : QFree D V 3) (av : a∈V)
    (sub : K ⊆ outN D V a ∩ inN D V c) (bk : b∈K) :
    K.card+(inN D V a ∩ inN D V c).card ≤ (inN D V c \ outN D V b).card+(outN D K b).card := by
  classical
  let B := outN D V b
  let P := inN D V a ∩ inN D V c
  have kv : K⊆V := sub.trans (inter_subset_left.trans outN_subset)
  have ab := (mem_outN.mp (mem_inter.mp (sub bk)).1).2
  have inc : (K\B)∪P ⊆ inN D V c \ B := by
    intro r rm
    rcases mem_union.mp rm with h | h
    · obtain ⟨rk,off⟩ := mem_sdiff.mp h
      exact mem_sdiff.mpr ⟨(mem_inter.mp (sub rk)).2,off⟩
    · obtain ⟨ra,rc⟩ := mem_inter.mp h
      obtain ⟨rv,ra'⟩ := mem_inN.mp ra
      exact mem_sdiff.mpr ⟨rc,fun br => safe r 3 (by decide) (by decide)
        (.step av ra' (.step (kv bk) ab (.step rv (mem_outN.mp br).2 (.refl _))))⟩
  have dis : Disjoint (K\B) P := disjoint_left.mpr (fun r rk rp =>
    digonfree safe (by decide) av (kv (mem_sdiff.mp rk).1)
      (mem_outN.mp (mem_inter.mp (sub (mem_sdiff.mp rk).1)).1).2 (mem_inN.mp (mem_inter.mp rp).1).2)
  have n := card_le_card inc
  rw [card_union_of_disjoint dis] at n
  have inside : K∩B=outN D K b := by
    ext r
    simp only [mem_inter,mem_outN,B]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,kv h.1,h.2⟩⟩
  have marked := card_sdiff_add_card_inter K B
  rw [inside] at marked
  change (K\B).card+P.card ≤ (inN D V c \ B).card at n
  change K.card+P.card ≤ (inN D V c \ B).card+(outN D K b).card
  omega

/-- Along an arc w→d the predecessors of w, and w, miss both rows. -/
theorem indegree_arc {D : CH.Digraph} {V : Finset ℕ} {w d : ℕ}
    (safe : QFree D V 3) (wv : w∈V) (dv : d∈V) (wd : D w d=true) :
    (inN D V w).card+1+(outN D V w).card+(outN D V d).card ≤
      V.card+(outN D V w ∩ outN D V d).card := by
  classical
  let C := outN D V w
  let E := outN D V d
  have wn : w∉inN D V w := fun h => loopfree safe (by decide) wv (mem_inN.mp h).2
  have spare : insert w (inN D V w) ⊆ V \ (C∪E) := by
    intro r rm
    rcases mem_insert.mp rm with rfl | rin
    · exact mem_sdiff.mpr ⟨wv,by
        simp only [mem_union,not_or,C,E]
        exact ⟨fun h => loopfree safe (by decide) wv (mem_outN.mp h).2,
          fun h => digonfree safe (by decide) wv dv wd (mem_outN.mp h).2⟩⟩
    · obtain ⟨rv,rw⟩ := mem_inN.mp rin
      exact mem_sdiff.mpr ⟨rv,by
        simp only [mem_union,not_or,C,E]
        exact ⟨fun h => digonfree safe (by decide) rv wv rw (mem_outN.mp h).2,
          fun h => safe r 3 (by decide) (by decide)
            (.step wv rw (.step dv wd (.step rv (mem_outN.mp h).2 (.refl _))))⟩⟩
  have n := card_le_card spare
  rw [card_insert_of_notMem wn] at n
  have total := card_sdiff_add_card_eq_card (show C∪E⊆V from union_subset outN_subset outN_subset)
  have h := card_union_add_card_inter C E
  change (inN D V w).card+1+C.card+E.card ≤ V.card+(C∩E).card
  omega

/-- At the two-label order every indegree is at most (4s-7)/3. -/
theorem indegree_cap {D : CH.Digraph} {V : Finset ℕ} {s w : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 1≤s) (order : V.card+1=3*s)
    (lower : ∀ j, j<s → BypassRepair.NoHost 3 j) (wv : w∈V) :
    3*(inN D V w).card+7 ≤ 4*s := by
  classical
  let K := outN D V w
  have size : K.card=s := reg w wv
  have live : K.Nonempty := card_pos.mp (by omega)
  obtain ⟨d,dk,small⟩ := K.exists_min_image (fun i => (outN D K i).card) live
  have kv : K⊆V := outN_subset
  have inside : outN D K d ⊆ K.erase d := fun _ h => mem_erase.mpr
    ⟨fun eq => loopfree safe (by decide) (kv dk) (eq ▸ (mem_outN.mp h).2),outN_subset h⟩
  have n := card_le_card inside
  have e := card_erase_add_one dk
  have light : 3*(outN D K d).card < K.card := by
    by_contra! fails
    exact lower _ (by omega) D K live fails (safe.mono_set kv) small
  have same : outN D V w ∩ outN D V d=outN D K d := by
    ext r
    simp only [mem_inter,mem_outN,K]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.1.1,h.2⟩⟩
  have count := indegree_arc safe wv (kv dk) (mem_outN.mp dk).2
  rw [same,reg w wv,reg d (kv dk)] at count
  omega

/-- If the new head can pay for all tight middles except one, the edit
leaves that middle as the only row below the floor, one arc short. -/
theorem deficit_shift {D : CH.Digraph} {U : Finset ℕ} {w y z t : ℕ}
    (safe : QFree D U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y)
    (off : D w y≠true) (back : D y w≠true)
    (need : t≤(outN D U w).card+1)
    (floor : ∀ v∈U, v≠w → t≤(outN D U v).card)
    (zk : z∈(outN D U y ∩ inN D U w).filter (fun z => (outN D U z).card≤t))
    (budget : t+((outN D U y ∩ inN D U w).filter
      (fun z => (outN D U z).card≤t)).card ≤ (outN D U y).card+1) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧ E z w≠true ∧
      (∀ i j, E i j=true → D i j=true ∨ (i=w ∧ j=y)) ∧
      t≤(outN E U z).card+1 ∧ ∀ i∈U, i≠z → t≤(outN E U i).card := by
  classical
  let Z := outN D U y ∩ inN D U w
  let T := Z.filter (fun z => (outN D U z).card≤t)
  let A (v : ℕ) : Finset ℕ := if v=w then {y} else ∅
  let K (v : ℕ) : Finset ℕ :=
    if v=y then T.erase z else if v∈Z ∧ (v∉T ∨ v=z) then {w} else ∅
  have nw : w∉Z := fun h => back (mem_outN.mp (mem_inter.mp h).1).2
  have ny : y∉Z := fun h => back (mem_inN.mp (mem_inter.mp h).2).2
  have zT : z∈T := zk
  have zZ : z∈Z := (mem_filter.mp zk).1
  have zu : z∈U := outN_subset (mem_inter.mp zZ).1
  have zy : z≠y := fun eq => ny (eq ▸ zZ)
  have zw : z≠w := fun eq => nw (eq ▸ zZ)
  have spec {i j} (h : j∈A i) : i=w ∧ j=y := by
    by_cases iw : i=w
    · exact ⟨iw,by simpa [A,iw] using h⟩
    · simp [A,iw] at h
  obtain ⟨ok,rows⟩ := patch_certificate (A:=A) (C:=K) safe
    (fun _ _ _ h => by obtain ⟨rfl,rfl⟩ := spec h; exact ⟨yu,wy.symm,off,back⟩)
    (fun i _ j h m mu ym mw => by
      obtain ⟨hi,hj⟩ := spec h
      subst i
      subst j
      have mm : m∈Z := mem_inter.mpr ⟨mem_outN.mpr ⟨mu,ym⟩,mem_inN.mpr ⟨mu,mw⟩⟩
      have my : m≠y := fun eq => ny (eq ▸ mm)
      by_cases pay : m∈T ∧ m≠z
      · exact Or.inl (by simp [K,pay.1,pay.2])
      · have alt : m∉T ∨ m=z := by tauto
        exact Or.inr (by simp [K,my,mm,alt]))
    (fun _ _ _ h _ g => by
      obtain ⟨rfl,rfl⟩ := spec h
      exact False.elim (wy (spec g).1.symm))
  refine ⟨_,ok,decide_eq_true (Or.inl (by simp [A] : y∈A w)),?_,?_,?_,?_⟩
  · intro h
    rcases of_decide_eq_true h with new | ⟨_,kept⟩
    · simp [A,zw] at new
    · exact kept (by simp [K,zy,zZ])
  · intro i j h
    rcases of_decide_eq_true h with new | ⟨old,_⟩
    · exact Or.inr (spec new)
    · exact Or.inl old
  · rw [rows z zu]
    have fl := floor z zu zw
    have count := card_sdiff_add_card_inter (outN D U z) ({w} : Finset ℕ)
    have one := (card_le_card (inter_subset_right :
      (outN D U z ∩ {w}) ⊆ {w})).trans_eq (card_singleton _)
    simp [K,zy,zZ,A,zw]
    omega
  · intro i iu iz
    rw [rows i iu]
    by_cases iw : i=w
    · subst i
      simpa [A,K,wy,nw] using need
    have fl := floor i iu iw
    by_cases iy : i=y
    · subst i
      have sub : T.erase z ⊆ outN D U y :=
        (erase_subset _ _).trans ((filter_subset ..).trans inter_subset_left)
      have n := card_sdiff_of_subset sub
      have e := card_erase_add_one zT
      change t+T.card≤(outN D U y).card+1 at budget
      simp [A,K,iw,n]
      omega
    by_cases im : i∈Z
    · by_cases it : i∈T
      · simpa [K,iy,im,it,iz,A,iw] using fl
      · have hi : t < (outN D U i).card := by
          by_contra! low
          exact it (mem_filter.mpr ⟨im,low⟩)
        have count := card_sdiff_add_card_inter (outN D U i) ({w} : Finset ℕ)
        have one := (card_le_card (inter_subset_right :
          (outN D U i ∩ {w}) ⊆ {w})).trans_eq (card_singleton _)
        simp [K,iy,im,it,A,iw]
        omega
    · simpa [A,K,iw,iy,im] using fl

/-- A head y pointed to by every bank label has only full rows among its
old successors. The edit w→y therefore pays only for return middles whose
row the partial repair H has already shortened. -/
theorem common_target_budget {D H : CH.Digraph} {V B : Finset ℕ} {t w y : ℕ}
    (safe : QFree D V 3) (reg : OutEq (t+1) D V) (bv : B⊆V)
    (wu : w∈V\B) (yu : y∈V\B) (target : ∀ b∈B, D b y=true)
    (ok : QFree H (V\B) 3) (wy : w≠y) (off : H w y≠true) (back : H y w≠true)
    (need : t≤(outN H (V\B) w).card+1)
    (floor : ∀ v∈V\B, v≠w → t≤(outN H (V\B) v).card)
    (oldY : outN H (V\B) y ⊆ outN D (V\B) y)
    (few : t+((outN H (V\B) y ∩ inN H (V\B) w).filter
      (fun m => (outN H (V\B) m).card<(outN D (V\B) m).card)).card ≤ (outN H (V\B) y).card) :
    ∃ E : CH.Digraph, QFree E (V\B) 3 ∧ E w y=true ∧ ∀ i∈V\B, t≤(outN E (V\B) i).card := by
  classical
  have uv : V\B⊆V := sdiff_subset
  have full (m) (mm : m∈outN D (V\B) y) : (outN D (V\B) m).card=t+1 := by
    obtain ⟨mu,ym⟩ := mem_outN.mp mm
    have h := card_outN_union (D:=D) (show Disjoint B (V\B) from disjoint_sdiff) m
    rw [union_sdiff_of_subset bv,reg _ (uv mu)] at h
    have empty : outN D B m=∅ := eq_empty_iff_forall_notMem.mpr (fun b hb =>
      safe b 3 (by decide) (by decide) (.step (uv yu) (target b (outN_subset hb))
        (.step (uv mu) ym (.step (bv (outN_subset hb)) (mem_outN.mp hb).2 (.refl _)))))
    rw [empty,card_empty,zero_add] at h
    exact h.symm
  apply one_arc_return_budget ok wu yu wy off back need floor
  refine le_trans (Nat.add_le_add_left (card_le_card ?_) t) few
  intro m mm
  obtain ⟨mem,tight⟩ := mem_filter.mp mm
  have f := full m (oldY (mem_inter.mp mem).1)
  exact mem_filter.mpr ⟨mem,by omega⟩

/-- In a source the common target fails. Every head of the whole bank that
is not adjacent to w in H has more shortened successors pointing to w
than its own surplus. -/
theorem common_target_obstruction {D H : CH.Digraph} {V B : Finset ℕ} {t w y : ℕ}
    (safe : QFree D V 3) (reg : OutEq (t+1) D V) (bv : B⊆V)
    (wu : w∈V\B) (yu : y∈V\B) (target : ∀ b∈B, D b y=true)
    (no : BypassRepair.NoHost 3 t) (size : (V\B).card≤3*t)
    (ok : QFree H (V\B) 3) (wy : w≠y) (off : H w y≠true) (back : H y w≠true)
    (need : t≤(outN H (V\B) w).card+1)
    (floor : ∀ v∈V\B, v≠w → t≤(outN H (V\B) v).card)
    (oldY : outN H (V\B) y ⊆ outN D (V\B) y) :
    (outN H (V\B) y).card < t+((outN H (V\B) y ∩ inN H (V\B) w).filter
      (fun m => (outN H (V\B) m).card<(outN D (V\B) m).card)).card := by
  by_contra! few
  obtain ⟨E,good,_,rows⟩ := common_target_budget safe reg bv wu yu target ok wy off back
    need floor oldY few
  exact no E (V\B) ⟨w,wu⟩ size good rows

/-- Two steps in one statement. The shortage first moves from x to the
unpaid middle w of x→p. In the resulting graph every head y of the whole
bank that is not adjacent to w is blocked by shortened successors only. -/
theorem shift_then_common_target {D H : CH.Digraph} {V B : Finset ℕ} {t x p w : ℕ}
    (safe : QFree D V 3) (reg : OutEq (t+1) D V) (bv : B⊆V)
    (no : BypassRepair.NoHost 3 t) (size : (V\B).card≤3*t)
    (ok : QFree H (V\B) 3) (xu : x∈V\B) (pu : p∈V\B) (xp : x≠p)
    (off : H x p≠true) (back : H p x≠true)
    (need : t≤(outN H (V\B) x).card+1)
    (floor : ∀ v∈V\B, v≠x → t≤(outN H (V\B) v).card)
    (wk : w∈(outN H (V\B) p ∩ inN H (V\B) x).filter (fun m => (outN H (V\B) m).card≤t))
    (budget : t+((outN H (V\B) p ∩ inN H (V\B) x).filter
      (fun m => (outN H (V\B) m).card≤t)).card ≤ (outN H (V\B) p).card+1) :
    ∃ E : CH.Digraph, QFree E (V\B) 3 ∧ E x p=true ∧
      (∀ i j, E i j=true → H i j=true ∨ (i=x ∧ j=p)) ∧
      ∀ y∈V\B, (∀ b∈B, D b y=true) → y≠w → y≠x → H w y≠true → H y w≠true →
        outN H (V\B) y ⊆ outN D (V\B) y →
        (outN E (V\B) y).card < t+((outN E (V\B) y ∩ inN E (V\B) w).filter
          (fun m => (outN E (V\B) m).card<(outN D (V\B) m).card)).card := by
  classical
  obtain ⟨E,good,arc,_,old,short,rows⟩ :=
    deficit_shift ok xu pu xp off back need floor wk budget
  have wu : w∈V\B := outN_subset (mem_inter.mp (mem_filter.mp wk).1).1
  refine ⟨E,good,arc,old,?_⟩
  intro y yu target yw yx wy' yw' oldY
  have wx : w≠x := fun e => loopfree ok (by decide) xu
    (e ▸ (mem_inN.mp (mem_inter.mp (mem_filter.mp wk).1).2).2)
  have ew : E w y≠true := fun h => (old w y h).elim wy' (fun e => wx e.1)
  have ey : E y w≠true := fun h => (old y w h).elim yw' (fun e => yx e.1)
  have incl : outN E (V\B) y ⊆ outN D (V\B) y := by
    intro m mm
    obtain ⟨mu,ym⟩ := mem_outN.mp mm
    rcases old y m ym with h | ⟨e,_⟩
    · exact oldY (mem_outN.mpr ⟨mu,h⟩)
    · exact absurd e yx
  exact common_target_obstruction safe reg bv wu yu target no size good yw.symm ew ey short
    (fun v vu vw => rows v vu vw) incl

#print axioms shift_then_common_target
#print axioms overlap_floor
#print axioms marked_inside_floor
#print axioms indegree_arc
#print axioms indegree_cap
#print axioms deficit_shift
#print axioms common_target_budget
#print axioms common_target_obstruction
end LeanCH.BR.WalkReturn
