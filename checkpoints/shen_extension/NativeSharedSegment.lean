import checkpoints.shen_extension.CyclePortNative

namespace LeanCH.BR.Closure.NativeSharedSegment
open Finset BRq2 BRq3 BR45 BRsub ShenCycleSuccessor ShortestCycleWeights

private theorem backwards {D C z} (closed : ∀i∈C,∀j∈C,D i j=true → D j z=true → D i z=true)
    {a b len} (path : Walk D C a b len) (ac : a∈C) (ed : D b z=true) : D a z=true := by
  induction path with
  | refl => exact ed
  | step j e _ ih => exact closed _ ac _ j e (ih j ed)

/-- On each native shortest cycle there is an edge which admits an exterior
continuation as well as the original one. -/
theorem leaves {q n} (X : Model q n) (hq : 2≤q) {C} (c : Cycle X.D X.V q C) :
    ∃u∈C,∃v∈C,∃z∈X.V\C,X.D u v=true ∧ X.D v z=true ∧ X.D u z=false ∧
      ∃N,Cycle X.D X.V q N ∧ u∈N ∧ v∈N ∧ z∈N := by
  classical
  by_contra! no
  have uniform : OutUniform X.D X.V C := by
    intro a ac b bc z zv nz
    have closed (i) (ic : i∈C) (j) (jc : j∈C) (ij : X.D i j=true) (jz : X.D j z=true) : X.D i z=true := by
      cases ez : X.D i z
      · obtain ⟨N,cn,inn,jn,zn⟩ := SaturatedCycleClasses.missing hq X.free X.sat
          (c.sub ic) (c.sub jc) zv ij jz (by simp [ez])
        exact (no i ic j jc z (mem_sdiff.mpr ⟨zv,nz⟩) ij jz ez N cn inn jn zn).elim
      · rfl
    obtain ⟨_,_,ab,ba⟩ := MandatoryExcursion.segments (by omega : 1≤q) X.free c ac bc
    exact Bool.eq_iff_iff.mpr ⟨backwards closed ba bc,backwards closed ab ac⟩
  have sz := c.size
  have other := CyclePhaseFork.support_bound X hq
  have proper : C≠X.V := fun eq => by rw [eq] at sz; omega
  exact X.prime C c.sub (by omega) proper ⟨uniform,outUniform_inUniform X.free X.sat c.sub uniform⟩

/-- The last entrance into the second cycle leaves a suffix lying in both. -/
private theorem last_entrance {D C N i j n} (p : Walk D C i j n) (ic : i∈C) (jn : j∈N) :
    (i∈N ∧ Walk D (C∩N) i j n) ∨
    ∃a∈C∩N,∃k∈C\N,D k a=true ∧ ∃l,l<n ∧ Walk D (C∩N) a j l := by
  classical
  induction p with
  | refl => exact Or.inl ⟨jn,.refl _⟩
  | @step i h j n hc ed _ ih =>
    rcases ih hc jn with ⟨hn,rest⟩ | ⟨a,an,k,kc,ka,l,le,walk⟩
    · by_cases inm : i∈N
      · exact Or.inl ⟨inm,.step (mem_inter.mpr ⟨hc,hn⟩) ed rest⟩
      · exact Or.inr ⟨h,mem_inter.mpr ⟨hc,hn⟩,i,mem_sdiff.mpr ⟨ic,inm⟩,ed,n,by omega,rest⟩
    · exact Or.inr ⟨a,an,k,kc,ka,l,by omega,walk⟩

/-- A shared directed segment with distinct native parents at its entrance
and distinct native heads at its exit. Each exterior label belongs to the
indicated original shortest cycle. -/
structure Segment (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) (C N : Finset ℕ)
    (a v k l s z d : ℕ) : Prop where
  cycle₁ : Cycle D V q C
  cycle₂ : Cycle D V q N
  start : a∈C∩N
  finish : v∈C∩N
  parent₁ : k∈C\N
  parent₂ : l∈N\C
  head₁ : s∈C\N
  head₂ : z∈N\C
  edge₁ : D k a=true
  edge₂ : D l a=true
  exit₁ : D v s=true
  exit₂ : D v z=true
  positive : 1≤d
  bound : d≤q-1
  shared : Walk D (C∩N) a v d

theorem on_cycle {q n} (X : Model q n) (hq : 2≤q) {C} (c : Cycle X.D X.V q C) :
    ∃N a v k l s z d,Segment X.D X.V q C N a v k l s z d := by
  classical
  obtain ⟨u,uc,v,vc,z,zout,uv,vz,_,N,cn,un,vn,zn⟩ := leaves X hq c
  obtain ⟨s,sh⟩ := card_pos.mp (show 0<(outN X.D C v).card by rw [c.heads v vc]; decide)
  obtain ⟨sc,vs⟩ := mem_outN.mp sh
  have sn : s∉N := by
    intro h
    have eq := card_le_one.mp (cn.heads v vn).le _ (mem_outN.mpr ⟨h,vs⟩) _ (mem_outN.mpr ⟨zn,vz⟩)
    exact (mem_sdiff.mp zout).2 (eq ▸ sc)
  obtain ⟨n,np,nq,path,_⟩ := WeightedSD.tight_cycle_complementary_walks (X.free.mono_set c.sub) c.size
    (fun i hi => by obtain ⟨j,hj⟩ := card_pos.mp (show 0<(outN X.D C i).card by rw [c.heads i hi]; decide)
                    exact ⟨j,mem_outN.mp hj⟩) sc vc (fun eq => sn (eq ▸ vn))
  rcases last_entrance (N:=N) path sc vn with ⟨bad,_⟩|⟨a,aa,k,kc,ka,d,lt,walk⟩
  · exact (sn bad).elim
  obtain ⟨l,lh⟩ := card_pos.mp (show 0<(inN X.D N a).card by rw [show (inN X.D N a).card=1 from cn.incoming a (mem_inter.mp aa).2]; decide)
  obtain ⟨ln,la⟩ := mem_inN.mp lh
  have lc : l∉C := by
    intro mem
    have one : (inN X.D C a).card≤1 := (c.incoming a (mem_inter.mp aa).1).le
    have eq := card_le_one.mp one _ (mem_inN.mpr ⟨mem,la⟩) _ (mem_inN.mpr ⟨(mem_sdiff.mp kc).1,ka⟩)
    exact (mem_sdiff.mp kc).2 (eq ▸ ln)
  have ap : a≠v := by
    intro eq
    have one : (inN X.D C v).card≤1 := (c.incoming v vc).le
    have eq' := card_le_one.mp one _ (mem_inN.mpr ⟨(mem_sdiff.mp kc).1,eq ▸ ka⟩) _ (mem_inN.mpr ⟨uc,uv⟩)
    exact (mem_sdiff.mp kc).2 (eq'.symm ▸ un)
  have dp : 1≤d := by
    by_contra! zero
    have e : d=0 := by omega
    rw [e] at walk
    cases walk
    exact ap rfl
  exact ⟨N,a,v,k,l,s,z,d,c,cn,aa,mem_inter.mpr ⟨vc,vn⟩,kc,mem_sdiff.mpr ⟨ln,lc⟩,
    mem_sdiff.mpr ⟨sc,sn⟩,mem_sdiff.mpr ⟨zn,(mem_sdiff.mp zout).2⟩,ka,la,vs,vz,dp,by omega,walk⟩

#print axioms leaves
#print axioms on_cycle
private theorem suffix {D C i j m} (one : ∀i∈C,(outN D C i).card=1)
    (path : Walk D C i j m) (ic : i∈C) {k n} (long : Walk D C i k n) (le : m≤n) :
    Walk D C j k (n-m) := by
  induction path generalizing n with
  | refl => simpa using long
  | @step i h j m hc ed _ ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases long with
      | step gc eg tail =>
        have eq := card_le_one.mp (one i ic).le _ (mem_outN.mpr ⟨hc,ed⟩) _ (mem_outN.mpr ⟨gc,eg⟩)
        subst_vars
        simpa using ih hc tail (by omega)

theorem complement {D V C q i j m} (hq : 1≤q) (free : QFree D V q) (c : Cycle D V q C)
    (ic : i∈C) (path : Walk D C i j m) (le : m≤q+1) : Walk D C j i (q+1-m) := by
  have full := (MandatoryExcursion.segments hq free c ic ic).2.2.1
  simp [MandatoryExcursion.span] at full
  exact suffix c.heads path ic full le

theorem Segment.table {D V q C N a v k l s z d} (g : Segment D V q C N a v k l s z d)
    (hq : 2≤q) (free : QFree D V q) :
    let L := q-1-d
    Walk D C s k L ∧ Walk D N z l L ∧
      ∀o∈({s,z} : Finset ℕ),∀p∈({k,l} : Finset ℕ),∀m<L,¬Walk D V o p m := by
  intro L
  have av := g.cycle₁.sub (mem_inter.mp g.start).1
  have vv := g.cycle₁.sub (mem_inter.mp g.finish).1
  have le := g.bound
  have kpath : Walk D C k s (d+1+1) := .step (mem_inter.mp g.start).1 g.edge₁
    ((g.shared.mono inter_subset_left).snoc (mem_sdiff.mp g.head₁).1 g.exit₁)
  have lpath : Walk D N l z (d+1+1) := .step (mem_inter.mp g.start).2 g.edge₂
    ((g.shared.mono inter_subset_right).snoc (mem_sdiff.mp g.head₂).1 g.exit₂)
  have len : q+1-(d+1+1)=L := by dsimp [L]; omega
  refine ⟨len ▸ complement (by omega) free g.cycle₁ (mem_sdiff.mp g.parent₁).1 kpath (by omega),
    len ▸ complement (by omega) free g.cycle₂ (mem_sdiff.mp g.parent₂).1 lpath (by omega),?_⟩
  intro o ho p hp m bound short
  have pa : D p a=true := by
    simp only [mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl
    · exact g.edge₁
    · exact g.edge₂
  have vo : o∈V ∧ D v o=true := by
    simp only [mem_insert,mem_singleton] at ho
    rcases ho with rfl|rfl
    · exact ⟨g.cycle₁.sub (mem_sdiff.mp g.head₁).1,g.exit₁⟩
    · exact ⟨g.cycle₂.sub (mem_sdiff.mp g.head₂).1,g.exit₂⟩
  have front : Walk D V p o (d+1+1) := .step av pa ((g.shared.mono (inter_subset_left.trans g.cycle₁.sub)).snoc vo.1 vo.2)
  dsimp [L] at bound
  exact free p _ (by omega) (by omega) (front.append short)

/-- Replacing the whole shared segment by one arc is safe at the indicated
smaller cutoff. Both private returns survive and still have minimum length. -/
theorem Segment.shortcut {D V q C N a v k l s z d} (g : Segment D V q C N a v k l s z d)
    (hq : 2≤q) (free : QFree D V q) :
    let Q := q+1-d
    let F := WeightedSD.insertArc D a v
    2≤Q ∧ Q≤q ∧ (1<d → Q<q) ∧ QFree F V Q ∧ F a v=true ∧
      Walk F V s k (Q-2) ∧ Walk F V z l (Q-2) := by
  intro Q F
  have dp := g.positive
  have le := g.bound
  have av := g.cycle₁.sub (mem_inter.mp g.start).1
  have vv := g.cycle₁.sub (mem_inter.mp g.finish).1
  have range : 2≤Q ∧ Q≤q ∧ (1<d → Q<q) := by dsimp [Q]; omega
  have safe : a∉ball D V v (Q-1) := by
    rintro hit
    obtain ⟨_,n,nq,path⟩ := mem_ball.mp hit
    dsimp [Q] at nq
    exact free a (d+n) (by omega) (by omega) ((g.shared.mono (inter_subset_left.trans g.cycle₁.sub)).append path)
  have extend {i j n} (path : Walk D V i j n) : Walk F V i j n := by
    induction path with
    | refl => exact .refl _
    | step hv ed _ ih => exact .step hv (WeightedSD.insertArc_mono D a v _ _ ed) ih
  have t := g.table hq free
  have eq : Q-2=q-1-d := by dsimp [Q]; omega
  exact ⟨range.1,range.2.1,range.2.2,WeightedSD.qfree_insertArc (free.mono_bound range.2.1)
    (⟨a,av⟩ : ↥V) ⟨v,vv⟩ safe,by simp [F,WeightedSD.insertArc],eq ▸ extend (t.1.mono g.cycle₁.sub),
    eq ▸ extend (t.2.1.mono g.cycle₂.sub)⟩

#print axioms Segment.table
#print axioms Segment.shortcut
end LeanCH.BR.Closure.NativeSharedSegment
