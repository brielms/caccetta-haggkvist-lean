import checkpoints.shen_extension.SelectedMenuGrowth

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

private theorem clone_short {D : CH.Digraph} {J : Finset ℕ} {r c t : ℕ} (safe : QFree D J 3)
    (fresh : c ∉ J) (rj : r ∈ J) (small : J.card+1 ≤ 3*t) (no : BypassRepair.NoHost 3 t) :
    ∃ v ∈ J, (outN D J v).card + (if D v r = true then 1 else 0) < t := by
  classical
  let U := insert c J
  have diff : U \ {c} = J := by ext w; simp [U]; grind
  have dest : ∀ i ∈ ({c} : Finset ℕ), (fun _ : ℕ => r) i ∈ U \ {c} := by
    intro i hi; rw [diff]; exact rj
  have size : U.card ≤ 3*t := by simpa [U,card_insert_of_notMem fresh] using small
  obtain ⟨v,vj,low⟩ := BypassCloneCover.uncovered_row no size (show U.Nonempty from ⟨c,mem_insert_self ..⟩)
    (diff ▸ safe) (singleton_subset_iff.mpr (mem_insert_self ..)) dest
  rw [diff] at vj low
  exact ⟨v,vj,by by_cases e : D v r=true <;> simpa [e] using low⟩

/-- Two parent promotions paid by spare degrees and specified extra credits.
Cuts preserve every old arc ending in L. -/
theorem pair_payment_patch {D : CH.Digraph} {J L T : Finset ℕ} {a b p q t : ℕ}
    (safe : QFree D J 3)
    (sub : L ⊆ J) (pl : p ∈ L) (ql : q ∈ L) (pq : p ≠ q)
    (au : a ∈ J) (bu : b ∈ J) (ab : a ≠ b) (al : a ∉ L) (bl : b ∉ L)
    (neutral : ∀ l ∈ L, D l a ≠ true ∧ D l b ≠ true)
    (ap : D a p ≠ true) (bq : D b q ≠ true)
    (parents : ∀ v ∈ ({a,b} : Finset ℕ), t ≤ (outN D J v).card+1 + (if v∈T then 1 else 0))
    (floor : ∀ v ∈ J, v ≠ a → v ≠ b → t ≤ (outN D J v).card + (if v∈T then 1 else 0))
    (fullP : t+1 ≤ (outN D J p).card) (fullQ : t+1 ≤ (outN D J q).card)
    (spare : ∀ w ∈ (outN D J p \ L) ∪ (outN D J q \ L), t+1 ≤ (outN D J w).card)
    (budget : (((outN D J p \ L) ∩ (outN D J q \ L)) \ T).card ≤
      (1 + (if p∈T then 1 else 0)) + (1 + (if q∈T then 1 else 0))) :
    ∃ E : CH.Digraph, QFree E J 3 ∧
      (∀ v ∈ J, t ≤ (outN E J v).card + (if v∈T then 1 else 0)) ∧
      (∀ v w, E v w = true → D v w = true ∨ (v=a ∧ w=p) ∨ (v=b ∧ w=q)) ∧
      ∀ v w, w ∈ L → D v w = true → E v w = true := by
  classical
  let X := outN D J p \ L
  let Y := outN D J q \ L
  let W := (X ∩ Y) \ T
  let i := 1+(if p∈T then 1 else 0)
  let j := 1+(if q∈T then 1 else 0)
  have few : W.card ≤ i+j := budget
  obtain ⟨F,fw,fc⟩ := exists_subset_card_eq (min_le_right i W.card)
  let G := W \ F
  have gc := card_sdiff_of_subset fw
  change G.card = W.card-F.card at gc
  have fsmall : F.card ≤ i := by omega
  have gsmall : G.card ≤ j := by omega
  have wx : W ⊆ X := sdiff_subset.trans inter_subset_left
  have wy : W ⊆ Y := sdiff_subset.trans inter_subset_right
  have gx : G ⊆ W := sdiff_subset
  have ax : a ∉ X := fun h => (neutral p pl).1 (mem_outN.mp (mem_sdiff.mp h).1).2
  have ay : a ∉ Y := fun h => (neutral q ql).1 (mem_outN.mp (mem_sdiff.mp h).1).2
  have bx : b ∉ X := fun h => (neutral p pl).2 (mem_outN.mp (mem_sdiff.mp h).1).2
  have by' : b ∉ Y := fun h => (neutral q ql).2 (mem_outN.mp (mem_sdiff.mp h).1).2
  have pa : p ≠ a := fun e => al (e ▸ pl)
  have pb : p ≠ b := fun e => bl (e ▸ pl)
  have qa : q ≠ a := fun e => al (e ▸ ql)
  have qb : q ≠ b := fun e => bl (e ▸ ql)
  let A (v : ℕ) : Finset ℕ := if v=a then {p} else if v=b then {q} else ∅
  let K (v : ℕ) : Finset ℕ := (if v ∈ X \ F then {a} else ∅) ∪
    (if v ∈ Y \ G then {b} else ∅)
  let C (v : ℕ) := if v=p then F else if v=q then G else K v
  let E := patch D A C
  have ad {v h} (m : h ∈ A v) : (v=a ∧ h=p) ∨ (v=b ∧ h=q) := by
    by_cases va : v=a <;> by_cases vb : v=b <;> simp_all [A]
  have old {v w} (ed : D v w=true) (keep : w ∉ C v) : E v w=true := by
    apply decide_eq_true; exact Or.inr ⟨ed,keep⟩
  have inK (v w : ℕ) : w ∈ K v ↔ (v ∈ X \ F ∧ w=a) ∨ (v ∈ Y \ G ∧ w=b) := by
    by_cases x : v ∈ X \ F <;> by_cases y : v ∈ Y \ G <;> simp [-Finset.mem_sdiff,K,x,y]
  have outsider {v} (h : v ∈ X ∨ v ∈ Y) : v ≠ p ∧ v ≠ q := by
    have vl : v ∉ L := h.elim (fun m => (mem_sdiff.mp m).2) (fun m => (mem_sdiff.mp m).2)
    exact ⟨fun e => vl (e ▸ pl),fun e => vl (e ▸ ql)⟩
  obtain ⟨ok,rows⟩ := patch_certificate (A:=A) (C:=C) safe
    (fun v _ h hm => by
      rcases ad hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨sub pl,pa,ap,(neutral _ pl).1⟩
      · exact ⟨sub ql,qb,bq,(neutral _ ql).2⟩)
    (fun v _ h hm w wj hw wv => by
      rcases ad hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have x : w ∈ X := mem_sdiff.mpr ⟨mem_outN.mpr ⟨wj,hw⟩,fun wl => (neutral w wl).1 wv⟩
        by_cases wf : w ∈ F
        · exact Or.inl (by simpa [C] using wf)
        · have away := outsider (Or.inl x)
          exact Or.inr (by simp only [C,ite_eq_right away.1,ite_eq_right away.2]; exact (inK w _).mpr (Or.inl ⟨mem_sdiff.mpr ⟨x,wf⟩,rfl⟩))
      · have y : w ∈ Y := mem_sdiff.mpr ⟨mem_outN.mpr ⟨wj,hw⟩,fun wl => (neutral w wl).2 wv⟩
        by_cases wg : w ∈ G
        · exact Or.inl (by simpa [C,pq.symm] using wg)
        · have away := outsider (Or.inr y)
          exact Or.inr (by simp only [C,ite_eq_right away.1,ite_eq_right away.2]; exact (inK w _).mpr (Or.inr ⟨mem_sdiff.mpr ⟨y,wg⟩,rfl⟩)))
    (fun _ _ _ h _ h' => by
      rcases ad h with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rcases ad h' with ⟨e,_⟩ | ⟨e,_⟩ <;> contradiction)
  refine ⟨E,ok,?_,?_,?_⟩
  · intro v vj
    have bill := rows v vj
    change (outN E J v).card = _ at bill
    have removed := card_sdiff_add_card_inter (outN D J v) (C v)
    have costs := card_le_card (inter_subset_right : outN D J v ∩ C v ⊆ C v)
    by_cases vp : v=p
    · subst v
      simp [C,A,pa,pb] at costs bill
      have split := card_sdiff_add_card_inter (outN D J p) F
      dsimp [i] at fsmall
      omega
    by_cases vq : v=q
    · subst v
      simp [C,A,qa,qb,pq.symm] at costs bill
      have split := card_sdiff_add_card_inter (outN D J q) G
      dsimp [j] at gsmall
      omega
    have cost : C v = K v := by simp [C,vp,vq]
    by_cases vx : v ∈ X \ F
    · have x := (mem_sdiff.mp vx).1
      have rich := spare v (mem_union_left _ x)
      by_cases vy : v ∈ Y \ G
      · have y := (mem_sdiff.mp vy).1
        have vr : v ∈ T := by
          by_contra ne
          have m : v ∈ W := mem_sdiff.mpr ⟨mem_inter.mpr ⟨x,y⟩,ne⟩
          exact (mem_sdiff.mp vy).2 (mem_sdiff.mpr ⟨m,(mem_sdiff.mp vx).2⟩)
        have cap : (C v).card=2 := by simp [-Finset.mem_sdiff,cost,K,vx,vy,ab]
        simp [vr]
        omega
      · have cap : (C v).card=1 := by simp [-Finset.mem_sdiff,cost,K,vx,vy]
        omega
    by_cases vy : v ∈ Y \ G
    · have rich := spare v (mem_union_right _ (mem_sdiff.mp vy).1)
      have cap : (C v).card=1 := by simp [-Finset.mem_sdiff,cost,K,vx,vy]
      omega
    have clear : C v=∅ := by simp [-Finset.mem_sdiff,cost,K,vx,vy]
    rw [clear,sdiff_empty] at bill
    by_cases va : v=a
    · subst v
      have enough := parents a (mem_insert_self ..)
      simp [A] at bill
      omega
    by_cases vb : v=b
    · subst v
      have enough := parents b (mem_insert_of_mem (mem_singleton_self _))
      simp [A,ab.symm] at bill
      omega
    have enough := floor v vj va vb
    omega
  · intro v w e
    rcases (of_decide_eq_true e : w ∈ A v ∨ D v w = true ∧ w ∉ C v) with new | old
    · exact Or.inr (ad new)
    · exact Or.inl old.1
  · intro v w wl vw
    apply old vw
    by_cases vp : v=p
    · simp only [C,ite_eq_left vp]
      exact fun m => (mem_sdiff.mp (wx (fw m))).2 wl
    by_cases vq : v=q
    · simp only [C,ite_eq_right vp,ite_eq_left vq]
      exact fun m => (mem_sdiff.mp (wy (gx m))).2 wl
    simp only [C,ite_eq_right vp,ite_eq_right vq,inK]
    rintro (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · exact al wl
    · exact bl wl

/-- On the vacant core, clone r to compensate any double cut at a predecessor
of r. Both repair targets can also spend the extra arc to this clone. -/
theorem clone_payment_obstruction {D : CH.Digraph} {J L : Finset ℕ} {c a b p q r t : ℕ}
    (safe : QFree D J 3) (fresh : c ∉ J) (small : J.card+1 ≤ 3*t) (no : BypassRepair.NoHost 3 t)
    (sub : L ⊆ J) (pl : p ∈ L) (ql : q ∈ L) (rl : r ∈ L) (pq : p ≠ q)
    (au : a ∈ J) (bu : b ∈ J) (ab : a ≠ b) (al : a ∉ L) (bl : b ∉ L)
    (neutral : ∀ l ∈ L, D l a ≠ true ∧ D l b ≠ true)
    (ap : D a p ≠ true) (bq : D b q ≠ true)
    (parents : ∀ v ∈ ({a,b} : Finset ℕ), t ≤ (outN D J v).card+1)
    (floor : ∀ v ∈ J, v ≠ a → v ≠ b → t ≤ (outN D J v).card + (if D v r=true then 1 else 0))
    (fullP : t+1 ≤ (outN D J p).card) (fullQ : t+1 ≤ (outN D J q).card)
    (spare : ∀ w ∈ (outN D J p \ L) ∪ (outN D J q \ L), t+1 ≤ (outN D J w).card) :
    (1 + (if D p r=true then 1 else 0)) + (1 + (if D q r=true then 1 else 0)) <
      (((outN D J p \ L) ∩ (outN D J q \ L)).filter (fun w => D w r ≠ true)).card := by
  classical
  by_contra! few
  let T := J.filter (fun v => D v r=true)
  have credit (v) (vj : v ∈ J) : v ∈ T ↔ D v r=true := by simp [T,vj]
  have floor' (v) (vj : v ∈ J) (va : v ≠ a) (vb : v ≠ b) :
      t ≤ (outN D J v).card + (if v∈T then 1 else 0) := by
    simpa [credit v vj] using floor v vj va vb
  have pool : ((outN D J p \ L) ∩ (outN D J q \ L)) \ T =
      ((outN D J p \ L) ∩ (outN D J q \ L)).filter (fun w => D w r ≠ true) := by
    ext v
    have inJ (h : v ∈ (outN D J p \ L) ∩ (outN D J q \ L)) : v ∈ J :=
      outN_subset (mem_sdiff.mp (mem_inter.mp h).1).1
    simp only [mem_sdiff, mem_filter]
    constructor
    · exact fun ⟨m,n⟩ => ⟨m,fun e => n ((credit v (inJ m)).2 e)⟩
    · exact fun ⟨m,n⟩ => ⟨m,fun e => n ((credit v (inJ m)).1 e)⟩
  obtain ⟨E,ok,lower,_,keep⟩ := pair_payment_patch safe sub pl ql pq au bu ab al bl neutral ap bq
    (fun v vs => (parents v vs).trans (Nat.le_add_right ..)) floor' fullP fullQ spare
    (by simpa [pool,credit p (sub pl),credit q (sub ql)] using few)
  obtain ⟨v,vj,short⟩ := clone_short ok fresh (sub rl) small no
  have pay : t ≤ (outN E J v).card + (if D v r=true then 1 else 0) := by
    simpa [credit v vj] using lower v vj
  by_cases e : D v r=true
  · have er := keep v r rl e
    simp [e,er] at pay short
    omega
  · simp [e] at pay
    have nonneg : 0 ≤ (if E v r = true then 1 else 0 : ℕ) := Nat.zero_le _
    omega

#print axioms pair_payment_patch
#print axioms clone_payment_obstruction
end LeanCH.BR.TripleBank
