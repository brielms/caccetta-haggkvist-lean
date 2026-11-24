import checkpoints.shen_extension.NativeSharedSegment
import checkpoints.shen_extension.PinnedReturn

namespace LeanCH.BR.Closure.CoupledSegmentPorts
open Finset BRq2 BRq3 BR45 WeightedSD ShenReturnCut CyclePortMatching NativeSharedSegment
open ShenCycleSuccessor ShortestCycleWeights

/-- One ordinary unit of u and the entire bonus of t go to h. Removing
exactly these units leaves a bijection that pays every remaining slot. -/
structure Booking (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (y u t h : ℕ)
    (w : ℕ→ℕ) (b : ℕ) : Prop where
  distinct : u≠t
  port : h∈outN E V y
  first : u∈ball E V h (q-1)
  second : t∈ball E V h (q-1)
  capacity : b+1≤supply E w q y h
  demands : ∀i,(PinnedReturn.takeAt w u 1 i)+(if i=u then 1 else 0)+(if i=t then b else 0)=demand w b t i
  rest : ∃f : ↥(slots (V.erase y) (PinnedReturn.takeAt w u 1)) ≃
      ↥(slots (V.erase y) (PinnedReturn.takeAt (supply E w q y) h (b+1))),
    ∀i,E y (f i).val.1=true ∧ i.val.1∈ball E V (f i).val.1 (q-1)

private theorem reserve {q E V} {x : ℕ→ℚ} {c : ℚ} (hq : 2≤q) (high : 1<c)
    (small : SmallerSmallRow q V.card) (free : QFree E V q)
    (pos : ∀i∈V,0<x i) (xm : mass V x=1) (rows : ∀i∈V,WeightedSD.row q E V x i=c)
    {D b : ℕ} (dp : 0<D) (bonus : (b:ℚ)=D*(c-1)) {w : ℕ→ℕ} (scale : ∀i∈V,(w i : ℚ)=D*x i)
    {C N y u t h} (c₁ : Cycle E V q C) (c₂ : Cycle E V q N)
    (yy : y∈C∩N) (hh : h∈C∩N) (uu : u∈C\N) (tt : t∈N\C)
    (uy : E u y=true) (ty : E t y=true) (yh : E y h=true) : Booking q E V y u t h w b := by
  classical
  have uC := (mem_sdiff.mp uu).1
  have hv := c₁.sub (mem_inter.mp hh).1
  have yv := c₁.sub (mem_inter.mp yy).1
  have uv := c₁.sub uC
  have dr : (0:ℚ)<D := by exact_mod_cast dp
  have wp : 0<w u := by exact_mod_cast (scale u uv ▸ mul_pos dr (pos u uv) : (0:ℚ)<w u)
  have turn {K p} (cK : Cycle E V q K) (pk : p∈K) (yk : y∈K) (hk : h∈K) (py : E p y=true) :
      p∈ball E V h (q-1) := by
    have path : Walk E K p h 2 := .step yk py (.step hk yh (.refl _))
    have back := NativeSharedSegment.complement (by omega : 1≤q) free cK pk path (by omega)
    exact mem_ball.mpr ⟨cK.sub pk,_,by omega,back.mono cK.sub⟩
  have uh := turn c₁ uC (mem_inter.mp yy).1 (mem_inter.mp hh).1 uy
  have th := turn c₂ (mem_sdiff.mp tt).1 (mem_inter.mp yy).2 (mem_inter.mp hh).2 ty
  have hu := mem_outN.mpr ⟨hv,yh⟩
  have ku : u∈V.erase y := mem_erase.mpr ⟨fun eq => loopfree free (by omega : 1≤q) yv (eq ▸ uy),uv⟩
  have residual := (PinnedReturn.on_source hq high small free pos xm rows dp bonus scale y yv u ku h hu uh).1
  have eq : PinnedReturn.takeAt (demand w b u) u (b+1)=PinnedReturn.takeAt w u 1 := by
    funext i
    by_cases hit : i=u <;> simp [PinnedReturn.takeAt,demand,hit]; omega
  unfold PinnedReturn.Residual at residual
  rw [eq] at residual
  have atom := strict_atom_floor_of_proper hq free (small.induced free) x (fun i hi => (pos i hi).le)
    c (xm ▸ high) (fun i hi => (rows i hi).ge) h hv
  rw [xm] at atom
  have lt : b<q*w h := by
    have cmp : (b:ℚ)<(q:ℚ)*w h := by
      rw [bonus,scale h hv]
      nlinarith only [mul_lt_mul_of_pos_left atom dr,mul_pos dr (pos h hv)]
    exact_mod_cast cmp
  refine ⟨fun eq => (mem_sdiff.mp tt).2 (eq ▸ uC),hu,uh,th,by simpa [supply,yh] using lt,?_,residual⟩
  intro i
  by_cases hit : i=u <;> simp [PinnedReturn.takeAt,demand,hit]; omega

def ScaledRows (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℕ) (b : ℕ) (c : ℚ) : Prop :=
  ∃(D : ℕ) (x : ℕ→ℚ),0<D ∧ (b:ℚ)=D*(c-1) ∧ (∀i∈V,(w i:ℚ)=D*x i) ∧
    mass V x=1 ∧ (∀i∈V,0<x i) ∧ ∀i∈V,WeightedSD.row q E V x i=c

theorem on_cycle {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {C} (c₁ : Cycle X.D X.V q C) :
    ∃N a v k l s z d h r,∃w p : ℕ→ℕ,∃b e : ℕ,∃c : ℚ,0<b ∧ 0<e ∧ 1<c ∧
      ScaledRows q X.D X.V w b c ∧ ScaledRows q (fun i j => X.D j i) X.V p e c ∧
      Segment X.D X.V q C N a v k l s z d ∧
      Booking q X.D X.V a k l h w b ∧ Booking q (fun i j => X.D j i) X.V v s z r p e ∧
      Walk X.D (C∩N) h v (d-1) ∧ Walk X.D (C∩N) a r (d-1) := by
  classical
  obtain ⟨N,a,v,k,l,s,z,d,g⟩ := NativeSharedSegment.on_cycle X hq c₁
  have dp := g.positive
  obtain ⟨m,em⟩ := Nat.exists_eq_succ_of_ne_zero (show d≠0 by omega)
  have path : Walk X.D (C∩N) a v (m+1) := by simpa only [em] using g.shared
  obtain ⟨r,prior,_,rv⟩ := path.unsnoc
  have rr : r∈C∩N := prior.end_mem_or.elim (fun eq => eq ▸ g.start) id
  obtain ⟨h,hh,ah,tail⟩ : ∃h∈C∩N,X.D a h=true ∧ Walk X.D (C∩N) h v m := by
    cases path with | step hh ah tail => exact ⟨_,hh,ah,tail⟩
  obtain ⟨x,p,c,high,xp,pp,xm,pm,rows,cols⟩ := strict_pair_of_proper_smallRow
    (small.induced X.free) X.live (fun i => (X.weights i : ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  let E := fun i j => X.D j i
  have back : QFree E X.V q := X.free.reverse
  have cr (i) (hi : i∈X.V) : WeightedSD.row q E X.V p i=c := cols i hi
  obtain ⟨_,b,up,bp,bv,w,ws,_⟩ := matching hq high small X.free xp xm rows
  obtain ⟨_,e,vp,ep,ev,t,ts,_⟩ := matching hq high small back pp pm cr
  have rev {K} (ck : Cycle X.D X.V q K) : Cycle E X.V q K := ⟨ck.sub,ck.size,ck.incoming,ck.heads⟩
  exact ⟨N,a,v,k,l,s,z,d,h,r,w,t,b,e,c,bp,ep,high,⟨_,x,up,bv,ws,xm,xp,rows⟩,⟨_,p,vp,ev,ts,pm,pp,cr⟩,g,
    reserve hq high small X.free xp xm rows up bv ws c₁ g.cycle₂ g.start hh g.parent₁ g.parent₂ g.edge₁ g.edge₂ ah,
    reserve hq high small back pp pm cr vp ev ts (rev c₁) (rev g.cycle₂) g.finish rr g.head₁ g.head₂ g.exit₁ g.exit₂ rv,
    by simpa [em] using tail,by simpa [em] using prior⟩

#print axioms on_cycle
end LeanCH.BR.Closure.CoupledSegmentPorts
