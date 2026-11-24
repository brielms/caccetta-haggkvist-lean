import checkpoints.shen_extension.StrictReturnLayers

namespace LeanCH.BR.Closure.StrictReturnLayers
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights
open MarkedCyclePeeling FirstPacketBarrier SharedArcBarrier SharedArcComponentExchange

private theorem native_arc {D F i j} (e : graph D F i j=true) : D i j=true := by
  obtain ⟨_,hit⟩ := active.mp e
  exact (mem_col.mp hit).2.2.2

/-- On an actual stopped pair the first robust return bank is precisely
the selected fresh head. This holds for every strict weight vector of the
paired graph. No cleanliness assumption is needed on its parent. -/
theorem paired {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (many : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {t h : X.V} (ta : Fresh X F (t,a)) (ah : Fresh X F (a,h)) :
    ∃M,Boundary X F M ∧ added X.D F M=SharedArcPivotChoice.pair a t h ∧
      let J := graph X.D (insert M F)
      ∀w : ℕ→ℚ,(∀i∈X.V,0≤w i) → (∀i∈X.V,mass X.V w < WeightedSD.row q J X.V w i) →
        outN J X.V a ∩ layers q J X.V w {t.val} (q-1) = {h.val} ∧
        w t + (WeightedSD.row q J X.V w a - mass X.V w) ≤ q*w h ∧
        WeightedSD.row q J X.V w h - mass X.V w ≤ q*outW J (layers q J X.V w {t.val} (q-2)) w h := by
  classical
  obtain ⟨M,bm,shape⟩ := SharedArcPivotChoice.joint_pair X hq small step least stop many edge no ta ah
  refine ⟨M,bm,shape,?_⟩
  intro J w nn strict
  let U (k) := layers q J X.V w {t.val} k
  let bank := outN J X.V a ∩ U (q-1)
  have taD : X.D t.val a.val=true := ta.2.2.1
  have ahD : X.D a.val h.val=true := ah.2.2.1
  have sub (i j) (ed : J i j=true) : X.D i j=true := native_arc ed
  have ts : ({t.val} : Finset ℕ) ⊆ X.V := singleton_subset_iff.mpr t.property
  have reach {x k} (xm : x∈U k) : ∃l≤k,Walk X.D X.V x t l := by
    obtain ⟨v,vt,l,le,p⟩ := forced (E:=J) ⟨fun _ _ e => e,strict⟩ ts nn k xm
    rw [mem_singleton.mp vt] at p
    exact ⟨l,le,walk_sub sub p⟩
  have at' : a.val≠t.val := fun eq => loopfree X.free (by omega) t.property (eq ▸ taD)
  have cut := bank_bound hq small (PrivateArcEndpoints.graph_free X (insert M F)) ts (singleton_nonempty _) nn strict
    (mem_sdiff.mpr ⟨a.property,by simpa using at'⟩) (fun s hs ed => by
      rw [mem_singleton.mp hs] at ed
      exact X.free t 2 (by decide) hq (.step a.property taD (.step t.property (sub _ _ ed) (.refl _))))
  have lower : w t + (WeightedSD.row q J X.V w a - mass X.V w) ≤ q*mass bank w := by
    simpa only [mass,sum_singleton] using cut
  have upper : bank⊆{h.val} := by
    intro x xb
    by_contra diff
    have ne : x≠h.val := by simpa using diff
    obtain ⟨head,xm⟩ := mem_inter.mp xb
    obtain ⟨xv,ax⟩ := mem_outN.mp head
    have old : graph X.D F a x=true := by
      rcases union_arc.mp ax with yes|hit
      · exact yes
      · rw [shape] at hit
        simp [SharedArcPivotChoice.pair,at',ne] at hit
    have tx := SharedArcPivotPaths.crossed X hq small step least many edge no t ⟨x,xv⟩ ta.2.2.1 (sub _ _ ax)
      (by rw [ta.2.2.2,show graph X.D F a (⟨x,xv⟩ : X.V)=true from old]; decide)
    obtain ⟨l,le,path⟩ := reach xm
    exact X.free t (l+1) (by omega) (by omega) (.step xv tx path)
  have live : bank.Nonempty := by
    by_contra! empty
    rw [empty,show mass ∅ w=0 by simp [mass],mul_zero] at lower
    exact (add_pos_of_nonneg_of_pos (nn t t.property) (sub_pos.mpr (strict a a.property))).not_ge lower
  obtain ⟨x,xb⟩ := live
  have hb : h.val∈bank := (mem_singleton.mp (upper xb)) ▸ xb
  have eq : bank={h.val} := Subset.antisymm upper (singleton_subset_iff.mpr hb)
  rw [eq] at lower
  refine ⟨eq,by simpa only [mass,sum_singleton] using lower,?_⟩
  have outside : h.val∉U (q-2) := by
    intro hit
    obtain ⟨l,le,path⟩ := reach hit
    exact X.free t (l+1+1) (by omega) (by omega) (.step a.property taD (.step h.property ahD path))
  have layer := (mem_inter.mp hb).2
  change h.val∈layers q J X.V w {t.val} (q-1) at layer
  rw [show q-1=(q-2)+1 by omega] at layer
  have weak := (mem_filter.mp ((mem_union.mp layer).resolve_left outside)).2
  rw [WeightedSD.row,outW_split (bounded ts (q-2))]
  linarith

#print axioms paired

/-- Every feasible edit retaining the two new arcs breaks a specific old
    family member, even when the edit is allowed to introduce other arcs. -/
theorem old_cycle_loss {q D V F M a t h K}
    (shape : added D F M=SharedArcPivotChoice.pair a t h)
    (stopped : ¬SmallRow q (graph D (insert M F)) V)
    (inc : K t a=true) (out : K a h=true) (feasible : SmallRow q K V) :
    ∃C∈F,∃i∈V,∃j∈V,Uses D C (i,j) ∧ K i j=false := by
  classical
  by_contra absent
  have sub (i) (iv : i∈V) (j) (jv : j∈V) (ed : graph D (insert M F) i j=true) : K i j=true := by
    rcases union_arc.mp ed with old|fresh
    · obtain ⟨C,c⟩ := active.mp old
      obtain ⟨cf,used⟩ := mem_col.mp c
      cases kij : K i j
      · exact (absent ⟨C,cf,i,iv,j,jv,used,kij⟩).elim
      · rfl
    · rw [shape] at fresh
      simp only [SharedArcPivotChoice.pair,mem_insert,mem_singleton,Prod.mk.injEq] at fresh
      rcases fresh with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact inc
      · exact out
  obtain ⟨w,nn,live,strict⟩ := strict_witness_of_not_smallRow stopped
  obtain ⟨i,iv,low⟩ := feasible w nn live
  exact (strict i iv).not_ge ((add_le_add_right (mul_le_mul_of_nonneg_left
    (outW_mono_graph sub nn iv) (Nat.cast_nonneg q)) _).trans low)

#print axioms old_cycle_loss

/-- The result supplies actual feasible edits. Both fresh arcs survive.
At q=3 the last-parent set is precisely the common intermediates outside L. -/
theorem paired_cuts {q n} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (many : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {t h : X.V} (ta : Fresh X F (t,a)) (ah : Fresh X F (a,h)) :
    ∃M,Boundary X F M ∧ added X.D F M=SharedArcPivotChoice.pair a t h ∧
      let J := graph X.D (insert M F)
      ∀L : Finset ℕ,let K := endCut J h t L (lastParents q J X.V h t L)
                    K t a=true ∧ K a h=true ∧ SmallRow q K X.V ∧
                      ∃C∈F,∃i∈X.V,∃j∈X.V,Uses X.D C (i,j) ∧ K i j=false := by
  classical
  obtain ⟨M,bm,shape,price⟩ := paired X (by omega) small step least stop many edge no ta ah
  refine ⟨M,bm,shape,?_⟩
  intro J L K
  have taD : X.D t.val a.val=true := ta.2.2.1
  have ahD : X.D a.val h.val=true := ah.2.2.1
  have nt : a.val≠t.val := fun eq => loopfree X.free (by omega) t.property (eq ▸ taD)
  have nh : a.val≠h.val := fun eq => loopfree X.free (by omega) h.property (eq ▸ ahD)
  have th : t.val≠h.val := fun eq => X.free t 2 (by decide) (by omega)
    (.step a.property taD (.step t.property (eq.symm ▸ ahD) (.refl _)))
  have inc : J t a=true := union_arc.mpr (Or.inr (shape ▸ mem_insert_self _ _))
  have out : J a h=true := union_arc.mpr (Or.inr (shape ▸ mem_insert_of_mem (mem_singleton_self _)))
  have keepIn : K t a=true := by simp [K,endCut,nt,th,inc]
  have keepOut : K a h=true := by simp [K,endCut,nh,th.symm,out]
  have feasible : SmallRow q K X.V := by
    by_contra bad
    obtain ⟨w,nn,_,rows⟩ := strict_witness_of_not_smallRow bad
    have sub (i j) (ed : K i j=true) : J i j=true := cut_sub ed
    have high (i) (iv : i∈X.V) : mass X.V w < WeightedSD.row q J X.V w i :=
      (rows i iv).trans_le (add_le_add_right (mul_le_mul_of_nonneg_left
        (outW_mono_graph (fun x _ y _ => sub x y) nn iv) (Nat.cast_nonneg q)) _)
    have hit := (price w nn high).1
    have both : h.val∈outN J X.V a ∩ layers q J X.V w {t.val} (q-1) := by rw [hit]; simp
    have hm := (mem_inter.mp both).2
    have path := forced (D:=J) (E:=K) ⟨sub,rows⟩ (singleton_subset_iff.mpr t.property) nn (q-1) hm
    have off : J h t=false := Bool.eq_false_iff.mpr fun yes => X.free t 3 (by decide) hq
      (.step a.property taD (.step h.property ahD (.step t.property (native_arc yes) (.refl _))))
    exact cut_blocks hq th.symm off L path
  exact ⟨keepIn,keepOut,feasible,old_cycle_loss shape (stop M bm) keepIn keepOut feasible⟩

#print axioms paired_cuts
end LeanCH.BR.Closure.StrictReturnLayers
