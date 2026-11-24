import checkpoints.shen_extension.ForwardShortcutLayers

namespace LeanCH.BR.Closure.ForwardMerge
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights ForwardShortcutLayers

/-- Retained rows which would lose their strict native budget after erasing
    the other labels, at the full original mass. -/
def targets (q : ℕ) (D : CH.Digraph) (V U : Finset ℕ) (w : ℕ→ℚ) :=
  U.filter (fun i => WeightedSD.row q D U w i < mass V w)

def demand (q : ℕ) (V : Finset ℕ) (w : ℕ→ℚ) : RowRule :=
  fun i S => mass V w ≤ w i+q*mass S w

/-- Replace the entire erased block by one label of the same total weight.
    Every head in the complement of the forced bank may be installed
    at once. Its total weight is strictly below one qth of the retained mass. -/
theorem merged_budget {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    {U : Finset ℕ} (us : U⊆V) (room : U.card+1<V.card) (live : U.Nonempty)
    (w : ℕ→ℚ) (positive : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w < WeightedSD.row q D V w i) :
    let T := targets q D V U w
    let H := U \ layer D U T (offTargets T (demand q V w)) (q-2)
    q*mass H w < mass U w := by
  classical
  intro T H
  let W := V \ U
  have total : mass W w+mass U w=mass V w := sum_sdiff us
  have card := card_sdiff_add_card_eq_card us
  have wl : W.Nonempty := card_pos.mp (by dsimp [W]; omega)
  obtain ⟨b,bw⟩ := wl
  have bu : b∉U := (mem_sdiff.mp bw).2
  have bwpos : 0<mass W w := sum_pos (fun i iw => positive i (mem_sdiff.mp iw).1) ⟨b,bw⟩
  have nn : ∀i∈U,0≤w i := fun i iu => (positive i (us iu)).le
  obtain ⟨t,tu,tlow⟩ := small D U (by omega) (free.mono_set us) w nn live
  have tt : t∈T := mem_filter.mpr ⟨tu,by linarith⟩
  have base (i) (iu : i∈U) : offTargets T (demand q V w) i (outN D U i) := by
    by_cases it : i∈T
    · exact Or.inl it
    · apply Or.inr
      have gt : mass V w ≤ WeightedSD.row q D U w i :=
        le_of_not_gt (fun lo => it (mem_filter.mpr ⟨iu,lo⟩))
      simpa only [demand,WeightedSD.row,outW_eq_mass] using gt
  obtain ⟨E,sub,paid,keep,_,detect⟩ := realize_layers base (q-2)
  let K := coreTwoSidedExtension E U T H b
  have hs : H⊆U := sdiff_subset
  have ts : T⊆U := filter_subset _ _
  have safe : QFree K (insert b U) q := coreTwoSidedExtension_qfree bu ts
    (qfree_sub sub (free.mono_set us)) (fun h hh i it k le p =>
      (mem_sdiff.mp hh).2 (detect (q-2) le_rfl h (hs hh) ⟨i,it,k,le,p⟩))
  let z (i : ℕ) := if i=b then mass W w else w i
  have zi {i} (iu : i∈U) : z i=w i := by simp [z,show i≠b from fun eq => bu (eq ▸ iu)]
  have zb : z b=mass W w := by simp [z]
  have zm : mass (insert b U) z=mass V w := by
    rw [mass,sum_insert bu,zb,sum_congr rfl (fun i iu => zi iu)]
    exact total
  have old {i j} (iu : i∈U) (ju : j∈U) : K i j=E i j := by
    have ib : i≠b := fun eq => bu (eq ▸ iu)
    have jb : j≠b := fun eq => bu (eq ▸ ju)
    simp [K,coreTwoSidedExtension,coreOutgoingExtension,iu,ju,ib,jb]
  have score (i) (iu : i∈U) : WeightedSD.row q K (insert b U) z i =
      WeightedSD.row q E U w i + q*(if i∈T then mass W w else 0) := by
    have visit : K i b=true ↔ i∈T := by simp [K,coreTwoSidedExtension,coreOutgoingExtension,bu]
    simp only [WeightedSD.row,outW,sum_insert bu,zi iu,zb,visit]
    rw [sum_congr rfl (fun j ju => by rw [old iu ju,zi ju])]
    ring
  have lifted (i) (iu : i∈U) (it : i∈T) :
      mass V w < WeightedSD.row q K (insert b U) z i := by
    have cover : outW D W w i ≤ mass W w := by
      rw [outW_eq_mass]
      exact mass_mono (fun _ m => (mem_outN.mp m).1) (fun j jw => (positive j (mem_sdiff.mp jw).1).le)
    have eq : WeightedSD.row q E U w i=WeightedSD.row q D U w i := by
      simp only [WeightedSD.row,outW,keep i it]
    rw [score i iu,eq]
    simp only [it,ite_true,WeightedSD.row]
    have high := strict i (us iu)
    rw [WeightedSD.row,outW_split us,mul_add] at high
    exact high.trans_le (by linarith [mul_le_mul_of_nonneg_left cover (Nat.cast_nonneg q)])
  have bridge : WeightedSD.row q K (insert b U) z b = mass W w+q*mass H w := by
    have bb : K b b=false := by simp [K,coreTwoSidedExtension,coreOutgoingExtension,bu,show b∉T from fun bt => bu (ts bt)]
    have arc (j) (ju : j∈U) : K b j=true ↔ j∈H := by
      have jb : j≠b := fun eq => bu (eq ▸ ju)
      simp [K,coreTwoSidedExtension,coreOutgoingExtension,bu,ju,jb]
    simp only [WeightedSD.row,zb,outW,sum_insert bu,bb,Bool.false_eq_true,ite_false,zero_add]
    congr 2
    calc
      _ = ∑j∈U, if j∈H then w j else 0 := sum_congr rfl (fun j ju => by rw [zi ju,if_congr (arc j ju) rfl rfl])
      _ = mass H w := by rw [← sum_filter]; congr 1; ext j; simp; exact fun jh => hs jh
  by_contra! high
  have weak (i) (iv : i∈insert b U) : mass (insert b U) z ≤ WeightedSD.row q K (insert b U) z i := by
    rw [zm]
    rcases mem_insert.mp iv with rfl|iu
    · rw [bridge,←total]; linarith
    · by_cases it : i∈T
      · exact (lifted i iu it).le
      · rw [score i iu]
        simp only [it,ite_false,mul_zero,add_zero,WeightedSD.row,outW_eq_mass]
        exact (paid i iu).resolve_left it
  have pos (i) (iv : i∈insert b U) : 0<z i := by
    rcases mem_insert.mp iv with rfl|iu
    · rwa [zb]
    · rw [zi iu]; exact positive i (us iu)
  have eq := positive_feasible_rows_tight_of_smallRow hq (small K _ (by simpa [bu] using room) safe)
    z pos weak t (mem_insert_of_mem tu)
  exact (lifted t tu tt).ne' (eq.trans zm)

#print axioms merged_budget

private theorem two_erases {V : Finset ℕ} {a b : ℕ} (av : a∈V) (bu : b∈V.erase a)
    (f : ℕ→ℚ) :
    (∑i∈V,f i)=(∑i∈(V.erase a).erase b,f i)+f b+f a := by
  rw [sum_erase_add _ _ bu,sum_erase_add _ _ av]

/-- Every actual arc participates in a quantitatively large family of
    shortest cycles. The first heads are fixed before any admissible deletion
    on the two-label puncture; the last parents are allowed to vary with it. -/
theorem arc_returns {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (w : ℕ→ℚ) (positive : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w < WeightedSD.row q D V w i)
    {b a : V} (ba : D b a=true) :
    let U := (V.erase a.val).erase b.val
    let T := targets q D V U w
    ∃P⊆outN D U a, w b+(WeightedSD.row q D V w a-mass V w)<q*mass P w ∧
      ∀E : CH.Digraph,(∀i j,E i j=true → D i j=true) →
      (∀i∈U,i∉T → mass V w ≤ WeightedSD.row q E U w i) →
      ∀h∈P,∃t∈T,D t a=false ∧ D t b=true ∧
        WeightedSD.row q D V w t-mass V w < q*w b ∧ Walk E U h t (q-2) := by
  classical
  intro U T
  have diff : b.val≠a.val := fun eq => loopfree free (by omega) a.property (eq ▸ ba)
  have bu : b.val∈V.erase a.val := mem_erase.mpr ⟨diff,b.property⟩
  have cardA := card_erase_add_one a.property
  have cardB := card_erase_add_one bu
  have size : U.card+2=V.card := by dsimp [U]; omega
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have aa : D a a=false := Bool.eq_false_iff.mpr (loopfree free (by omega) a.property)
  have ab : D a b=false := Bool.eq_false_iff.mpr fun ed =>
    free b 2 (by decide) hq (.step a.property ba (.step b.property ed (.refl _)))
  have live : U.Nonempty := by
    by_contra! empty
    have zero : outN D V a=∅ := eq_empty_iff_forall_notMem.mpr (fun j hj => by
      obtain ⟨jv,aj⟩ := mem_outN.mp hj
      have ja : j≠a.val := fun eq => Bool.noConfusion (aa.symm.trans (eq ▸ aj))
      have jb : j≠b.val := fun eq => Bool.noConfusion (ab.symm.trans (eq ▸ aj))
      have ju : j∈U := mem_erase.mpr ⟨jb,mem_erase.mpr ⟨ja,jv⟩⟩
      simp [empty] at ju)
    have hi := strict a a.property
    have lo : w a ≤ mass V w := single_le_sum (fun i iv => (positive i iv).le) a.property
    rw [WeightedSD.row,outW_eq_mass,zero,show mass ∅ w=0 by simp [mass],mul_zero,add_zero] at hi
    exact hi.not_ge lo
  let A := layer D U T (offTargets T (demand q V w)) (q-2)
  let N := outN D U a
  let P := N∩A
  let H := U \ A
  have high : q*mass H w < mass U w := merged_budget hq free small us (by omega) live w positive strict
  have both : N⊆P∪H := by
    intro x xm
    by_cases xa : x∈A
    · exact mem_union_left _ (mem_inter.mpr ⟨xm,xa⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_outN.mp xm).1,xa⟩)
  have dis : Disjoint P H := disjoint_left.mpr (fun _ xp xh => (mem_sdiff.mp xh).2 (mem_inter.mp xp).2)
  have weights : mass N w≤mass P w+mass H w := by
    rw [←show mass (P∪H) w=mass P w+mass H w from sum_union dis]
    apply mass_mono both
    intro x xm
    rcases mem_union.mp xm with xp|xh
    · exact (positive x (us (mem_outN.mp (mem_inter.mp xp).1).1)).le
    · exact (positive x (us (mem_sdiff.mp xh).1)).le
  have totals : mass V w=mass U w+w b+w a := two_erases a.property bu w
  have split (i) : outW D V w i=outW D U w i+
      (if D i b=true then w b else 0)+(if D i a=true then w a else 0) :=
    two_erases a.property bu _
  refine ⟨P,inter_subset_left,?_,?_⟩
  · rw [WeightedSD.row,split,totals]
    simp only [aa,ab,Bool.false_eq_true,ite_false,add_zero,outW_eq_mass]
    change w b + (w a + q*mass N w - (mass U w+w b+w a)) < q*mass P w
    have cap := mul_le_mul_of_nonneg_left weights (Nat.cast_nonneg q : (0:ℚ)≤q)
    rw [mul_add] at cap
    linarith
  · intro E sub accept h hp
    have mono (i) (_ : i∈U) (S B : Finset ℕ) (bs : B⊆U) (sb : S⊆B)
        (ok : offTargets T (demand q V w) i S) : offTargets T (demand q V w) i B := by
      rcases ok with it|old
      · exact Or.inl it
      · exact Or.inr (old.trans (add_le_add_right (mul_le_mul_of_nonneg_left
          (mass_mono sb (fun j jb => (positive j (us (bs jb))).le)) (Nat.cast_nonneg q)) _))
    have paid (i) (iu : i∈U) : offTargets T (demand q V w) i (outN E U i) := by
      by_cases it : i∈T
      · exact Or.inl it
      · exact Or.inr (by simpa only [demand,WeightedSD.row,outW_eq_mass] using accept i iu it)
    obtain ⟨t,tt,k,le,p⟩ := forced_return (show T⊆U from filter_subset _ _) mono sub paid
      (q-2) (mem_inter.mp hp).2
    have ah := mem_outN.mp (mem_inter.mp hp).1
    have tv := us (mem_filter.mp tt).1
    have path := (walk_sub sub p).mono us
    have ta : D t a=false := Bool.eq_false_iff.mpr fun ed => free a (k+1+1)
      (by omega) (by omega) (.step (us ah.1) ah.2 (path.snoc a.property ed))
    have low := (mem_filter.mp tt).2
    have tb : D t b=true := by
      cases ed : D t b
      · have hi := strict t tv
        simp only [WeightedSD.row,split t,ta,ed,Bool.false_eq_true,ite_false,add_zero] at hi
        exact (hi.not_ge (show w t + q*outW D U w t ≤ mass V w from low.le)).elim
      · rfl
    have cost : WeightedSD.row q D V w t-mass V w<q*w b := by
      rw [WeightedSD.row,split]
      simp only [ta,tb,ite_true,Bool.false_eq_true,ite_false,add_zero,mul_add]
      change w t+q*outW D U w t<mass V w at low
      linarith
    have len : k=q-2 := by
      by_contra ne
      exact free b (k+1+1+1) (by omega) (by omega)
        (.step a.property ba (.step (us ah.1) ah.2 (path.snoc b.property tb)))
    exact ⟨t,tt,ta,tb,cost,len ▸ p⟩

#print axioms arc_returns

def surplus (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (i : ℕ) :=
  WeightedSD.row q D V w i-mass V w

def closingParents (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (b : ℕ) :=
  (inN D V b).filter (fun t => surplus 3 D V w t<3*w b)

/-- At the triangle cutoff the two-step test uses only the original arc
    table and weights. The same threshold at b serves every arc leaving b. -/
theorem triangle_tensor {D V} (free : QFree D V 3) (small : SmallerSmallRow 3 V.card)
    (w : ℕ→ℚ) (positive : ∀i∈V,0<w i) (strict : ∀i∈V,0<surplus 3 D V w i)
    {b a : V} (ba : D b a=true) :
    let L := closingParents D V w b
    let S := (outN D V a).filter (fun h => surplus 3 D V w h < 3*outW D L w h)
    w b+surplus 3 D V w a < 3*mass S w := by
  classical
  intro L S
  let U := (V.erase a.val).erase b.val
  let T := targets 3 D V U w
  have high (i) (iv : i∈V) := sub_pos.mp (strict i iv)
  obtain ⟨P,ps,bound,returns⟩ := arc_returns (q:=3) (by decide) free small w positive high ba
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have diff : b.val≠a.val := fun eq => loopfree free (by decide) a.property (eq ▸ ba)
  have bu := mem_erase.mpr ⟨diff,b.property⟩
  have ab : D a b=false := Bool.eq_false_iff.mpr fun ed =>
    free b 2 (by decide) (by decide) (.step a.property ba (.step b.property ed (.refl _)))
  have ls : L⊆U := by
    intro t tt
    obtain ⟨tv,tb⟩ := mem_inN.mp (mem_filter.mp tt).1
    exact mem_erase.mpr ⟨fun eq => loopfree free (by decide) b.property (eq ▸ tb),
      mem_erase.mpr ⟨fun eq => Bool.noConfusion (ab.symm.trans (eq ▸ tb)),tv⟩⟩
  have subset : P⊆S := by
    intro h hp
    obtain ⟨hu,ah⟩ := mem_outN.mp (ps hp)
    have ha : D h a=false := Bool.eq_false_iff.mpr fun ed =>
      free a 2 (by decide) (by decide) (.step (us hu) ah (.step a.property ed (.refl _)))
    have hb : D h b=false := Bool.eq_false_iff.mpr fun ed =>
      free b 3 (by decide) le_rfl (.step a.property ba (.step (us hu) ah (.step b.property ed (.refl _))))
    refine mem_filter.mpr ⟨mem_outN.mpr ⟨us hu,ah⟩,?_⟩
    by_contra! low
    let E : CH.Digraph := fun i j => if i=h ∧ j∈L then false else D i j
    have sub (i j) (ed : E i j=true) : D i j=true := by unfold E at ed; split at ed <;> simp_all
    have retain (i) (iu : i∈U) (it : i∉T) : mass V w ≤ WeightedSD.row 3 E U w i := by
      by_cases eq : i=h
      · subst i
        have whole : outW D V w h=outW D U w h := by
          have e := two_erases a.property bu (fun j => if D h j=true then w j else 0)
          simpa only [outW,U,hb,ha,Bool.false_eq_true,ite_false,add_zero] using e
        have zero : outW E L w h=0 := sum_eq_zero (fun j jl => by simp [E,jl])
        have same : outW E (U \ L) w h=outW D (U \ L) w h := by
          apply sum_congr rfl; intro j jm; simp [E,(mem_sdiff.mp jm).2]
        rw [WeightedSD.row,outW_split ls,zero,zero_add,same]
        change WeightedSD.row 3 D V w h-mass V w ≥ 3*outW D L w h at low
        rw [WeightedSD.row,whole,outW_split ls] at low
        norm_num at low ⊢
        linarith
      · have native : mass V w≤WeightedSD.row 3 D U w i :=
          le_of_not_gt (fun lt => it (mem_filter.mpr ⟨iu,lt⟩))
        simpa [WeightedSD.row,outW,E,eq] using native
    obtain ⟨t,tt,_,tb,cost,path⟩ := returns E sub retain h hp
    have tl : t∈L := mem_filter.mpr ⟨mem_inN.mpr ⟨us (mem_filter.mp tt).1,tb⟩,cost⟩
    change Walk E U h t 1 at path
    cases path with
    | step _ ed rest => cases rest; simp [E,tl] at ed
  exact bound.trans_le (mul_le_mul_of_nonneg_left (mass_mono subset
    (fun i hi => (positive i (mem_outN.mp (mem_filter.mp hi).1).1).le)) (by norm_num))

#print axioms triangle_tensor

/-- Blocking all short returns sacrifices every native shortest cycle
    containing the two nonadjacent endpoints, including the proposed attachment. -/
theorem cycle_loss {q D V C h t} (hq : 3≤q) (free : QFree D V q)
    (cyc : ShenCycleSuccessor.Cycle D V q C) (hc : h∈C) (tc : t∈C) (ne : h≠t)
    (off : D t h=false) {K : CH.Digraph} (blocked : ¬StrictReturnLayers.Returns K V {t} (q-1) h) :
    ∃i∈C,∃j∈C,D i j=true ∧ K i j=false := by
  classical
  obtain ⟨lo,hi,front,back⟩ := MandatoryExcursion.segments (by omega : 1≤q) free cyc tc hc
  let d := MandatoryExcursion.span D V q t h
  change Walk D C t h d at front
  change Walk D C h t (q+1-d) at back
  have two : 2≤d := by
    by_contra! low
    change 1≤d at lo
    rw [show d=1 by omega] at front
    cases front with
    | step _ ed tail =>
      cases tail
      exact Bool.noConfusion (off.symm.trans ed)
  by_contra lost
  have lift {i j k} (p : Walk D C i j k) (ic : i∈C) : Walk K V i j k := by
    induction p with
    | refl => exact .refl _
    | @step u v _ _ vc ed rest ih =>
      have kept : K u v=true := by
        cases raw : K u v
        · exact (lost ⟨u,ic,v,vc,ed,raw⟩).elim
        · rfl
      exact .step (cyc.sub vc) kept (ih vc)
  exact blocked ⟨t,mem_singleton_self _,q+1-d,by omega,lift back hc⟩

def peel (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (U : Finset ℕ) :=
  U.filter (fun i => mass V w ≤ WeightedSD.row q D U w i)

def rounds (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (U : Finset ℕ) : ℕ→Finset ℕ
  | 0 => U
  | k+1 => peel q D V w (rounds q D V w U k)

private theorem rounds_sub (q D V w U k) : rounds q D V w U k⊆U := by
  induction k with
  | zero => exact Subset.rfl
  | succ k ih => exact (filter_subset _ _).trans ih

private theorem rounds_add (q D V w U k l) :
    rounds q D V w U (k+l)=rounds q D V w (rounds q D V w U k) l := by
  induction l with
  | zero => rfl
  | succ l ih => exact congrArg (peel q D V w) ih

/-- The outside of the return layers is exactly ordinary iteration of
    the retained-row test at the original mass. -/
theorem surviving (q D V U w k) :
    U \ layer D U (targets q D V U w) (offTargets (targets q D V U w) (demand q V w)) k =
      rounds q D V w U (k+1) := by
  classical
  let T := targets q D V U w
  let A (i) := layer D U T (offTargets T (demand q V w)) i
  change U \ A k=_
  induction k with
  | zero =>
    change U \ targets q D V U w=peel q D V w U
    ext i
    simp only [targets,peel,mem_sdiff,mem_filter]
    exact ⟨fun ⟨iu,keep⟩ => ⟨iu,le_of_not_gt (fun low => keep ⟨iu,low⟩)⟩,
      fun ⟨iu,enough⟩ => ⟨iu,fun hit => enough.not_gt hit.2⟩⟩
  | succ k ih =>
    change U \ A (k+1)=peel q D V w (rounds q D V w U (k+1))
    rw [←ih]
    ext i
    have union : T⊆A k := by
      clear ih
      intro t tt
      induction k with
      | zero => exact tt
      | succ j hj => exact mem_union_left _ hj
    have same : outN D (U \ A k) i = outN D U i \ A k := by
      ext j; simp only [mem_outN,mem_sdiff]; tauto
    change (i∈U \ (A k ∪ U.filter (fun j => ¬offTargets T (demand q V w) j (outN D U j \ A k)))) ↔ _
    simp only [peel,mem_sdiff,mem_union,mem_filter,offTargets,demand,WeightedSD.row,outW_eq_mass,same]
    by_cases it : i∈T
    · simp [it,union it]
    · simp [it]; tauto

/-- Uniform geometric loss after q−1 rounds from every nonempty proper
    carrier omitting at least two labels, for every positive strict weighting. -/
theorem decay {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    {U : Finset ℕ} (us : U⊆V) (room : U.card+1<V.card) (live : U.Nonempty)
    (w : ℕ→ℚ) (positive : ∀i∈V,0<w i) (strict : ∀i∈V,mass V w < WeightedSD.row q D V w i) :
    q*mass (rounds q D V w U (q-1)) w < mass U w := by
  have cap := merged_budget hq free small us room live w positive strict
  dsimp only at cap
  rwa [surviving,show q-2+1=q-1 by omega] at cap

theorem repeated_decay {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    {U : Finset ℕ} (us : U⊆V) (room : U.card+1<V.card) (w : ℕ→ℚ) (positive : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w < WeightedSD.row q D V w i) (k : ℕ) :
    (q:ℚ)^k * mass (rounds q D V w U (k*(q-1))) w ≤ mass U w := by
  induction k with
  | zero => simp [rounds]
  | succ k ih =>
    let S := rounds q D V w U (k*(q-1))
    have su : S⊆U := rounds_sub .. 
    have next : q*mass (rounds q D V w S (q-1)) w ≤ mass S w := by
      by_cases live : S.Nonempty
      · exact (decay hq free small (su.trans us) (by have := card_le_card su; omega) live w positive strict).le
      · have empty := not_nonempty_iff_eq_empty.mp live
        have endSet : rounds q D V w S (q-1)=∅ :=
          subset_empty.mp (empty ▸ rounds_sub q D V w S (q-1))
        rw [endSet,empty]
        simp [mass]
    rw [Nat.succ_mul,rounds_add,pow_succ,mul_assoc]
    exact (mul_le_mul_of_nonneg_left next (pow_nonneg (Nat.cast_nonneg q) k)).trans ih

def MergePays (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃ U⊆V,U.card+1<V.card ∧ U.Nonempty ∧ ∃w : ℕ→ℚ,(∀i∈V,0<w i) ∧
    (∀i∈V,mass V w < WeightedSD.row q D V w i) ∧
    mass U w ≤ q*mass (rounds q D V w U (q-1)) w

/-- A constructive supplier for the capstone exit. Each inner set only
    has to exhibit enough heads in its immediate outer set. -/
theorem pays_of_chain {q D V} (w : ℕ→ℚ) (positive : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w < WeightedSD.row q D V w i)
    (C : ℕ→Finset ℕ) (us : C 0⊆V) (room : (C 0).card+1<V.card) (live : (C 0).Nonempty)
    (step : ∀i<q-1,C (i+1)⊆C i ∧ ∀v∈C (i+1),mass V w≤WeightedSD.row q D (C i) w v)
    (bill : mass (C 0) w ≤ q*mass (C (q-1)) w) : MergePays q D V := by
  have fit (k) (bound : k≤q-1) : C k⊆rounds q D V w (C 0) k := by
    induction k with
    | zero => exact Subset.rfl
    | succ k ih =>
      have sub := ih (by omega)
      have adj := step k (by omega)
      intro v vc
      refine mem_filter.mpr ⟨sub (adj.1 vc), (adj.2 v vc).trans ?_⟩
      simp only [WeightedSD.row,outW_eq_mass]
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
      apply mass_mono (fun j jm => mem_outN.mpr ⟨sub (mem_outN.mp jm).1,(mem_outN.mp jm).2⟩)
      exact fun j jm => (positive j (us (rounds_sub _ _ _ _ _ k (mem_outN.mp jm).1))).le
  refine ⟨C 0,us,room,live,w,positive,strict,bill.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (mass_mono (fit (q-1) le_rfl)
    (fun j jm => (positive j (us (rounds_sub _ _ _ _ _ _ jm))).le)) (Nat.cast_nonneg q)

theorem no_merge {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card) :
    ¬MergePays q D V := by
  rintro ⟨U,us,room,live,w,pos,strict,enough⟩
  exact (decay hq free small us room live w pos strict).not_ge enough

/-- The proposed paid child may use a strict native subgraph in either
    orientation. The payment is a numerical test on the retained labels. -/
def NativeMergePays (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃J : CH.Digraph,(∀i j,J i j=true → D i j=true) ∧
    (MergePays q J V ∨ MergePays q (fun i j => J j i) V)

theorem no_native_merge {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card) :
    ¬NativeMergePays q D V := by
  rintro ⟨J,sub,hit⟩
  have safe := qfree_sub sub free
  exact hit.elim (no_merge hq safe small) (no_merge hq safe.reverse small)

theorem triangle_at {q D V} (three : q=3) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (w : ℕ→ℚ) (positive : ∀i∈V,0<w i) (strict : ∀i∈V,mass V w < WeightedSD.row q D V w i)
    {b a : V} (ba : D b a=true) :
    let L := closingParents D V w b
    w b+surplus 3 D V w a < 3*mass ((outN D V a).filter
      (fun h => surplus 3 D V w h < 3*outW D L w h)) w := by
  subst q
  exact triangle_tensor free small w positive (fun i iv => sub_pos.mpr (strict i iv)) ba

#print axioms cycle_loss
#print axioms no_merge
#print axioms pays_of_chain
#print axioms no_native_merge
#print axioms surviving
#print axioms decay
#print axioms repeated_decay
#print axioms triangle_at
end LeanCH.BR.Closure.ForwardMerge
