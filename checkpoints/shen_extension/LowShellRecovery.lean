import checkpoints.shen_extension.LowShellCycleSelection
namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- This set is determined by the marked cycle in the ambient graph alone. -/
noncomputable def mutualExterior (D : CH.Digraph) (V C : Finset ℕ) : Finset ℕ :=
  (exterior D V C).filter (fun z=>(outN D C z).Nonempty)

/-- A used exception at a one-extra-label origin is recoverable from the
actual cycle, even when a different origin uses the same support. -/
theorem recover_shell {D V q r u C b v} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (dag : QFree D (outN D V u) (outN D V u).card)
    (width : (N2 D V u).card=r) (next : (N3 D V u).card<r) (cy : C⊆N2 D V u)
    (cc : q<C.card) (rc : ∀v∈C,Rooted D V v C) (exceptional : N2 D V u\C={b})
    (vm : v∈C) (hit : D v b=true) (fit : r+1<2*(q-1)) (near : C.card-(q-1)<q-1) :
    N2 D V u=C∪mutualExterior D V C := by
  classical
  let Y := N2 D V u
  let Z := N3 D V u
  have cv : C⊆V := fun _ m=>N2_subV (cy m)
  have bm : b∈Y\C := exceptional.symm ▸ mem_singleton_self b
  have len : (N2 D V u\C).card=1 := by rw [exceptional,card_singleton]
  obtain ⟨d,dm,k,size,road⟩ := exception_returns free hq reg uv dag width next cy cc rc
    (by omega) (by omega) vm bm hit
  have bd : D b d=true := by
    rcases (by omega : k=0 ∨ k=1) with h|h
    · subst k; cases road; exact ((mem_sdiff.mp bm).2 dm).elim
    · subst k; cases road with | step _ arc rest => cases rest; exact arc
  have bOuter : b∈mutualExterior D V C := mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_biUnion.mpr
    ⟨v,vm,mem_outN.mpr ⟨N2_subV (mem_sdiff.mp bm).1,hit⟩⟩,(mem_sdiff.mp bm).2⟩,⟨d,mem_outN.mpr ⟨dm,bd⟩⟩⟩
  have rows := (complete_rows free hq reg uv dag width next cy cc rc (by omega) (by omega)).1
  simp only [len,Nat.one_mul] at rows
  ext z
  constructor
  · intro zm
    by_cases inside : z∈C
    · exact mem_union_left _ inside
    · have exc : z∈N2 D V u\C := mem_sdiff.mpr ⟨zm,inside⟩
      rw [exceptional,mem_singleton] at exc
      exact mem_union_right _ (exc ▸ bOuter)
  · intro zm
    rcases mem_union.mp zm with old|back
    · exact cy old
    obtain ⟨out,⟨c,ch⟩⟩ := mem_filter.mp back
    obtain ⟨sources,_off⟩ := mem_sdiff.mp out
    obtain ⟨a,am,edge⟩ := mem_biUnion.mp sources
    have arc := (mem_outN.mp edge).2
    rcases headY (free.mono_bound hq) uv (cy am) (outN_subset edge) arc with early|late
    · exact (mem_union.mp early).resolve_left (fun xm=>no_back free hq reg uv dag width (by omega) cy cc rc a am z xm arc)
    · have path : Walk D V z c 1 := .step (cv (outN_subset ch)) (mem_outN.mp ch).2 (.refl c)
      have small := exception_parents free cv (fun x xm=>((rc x xm).one x xm).ge)
        (outN_subset edge) (outN_subset ch) path (by omega)
      have sub : C.filter (fun a=>N3 D V u⊆outN D V a)⊆inN D C z := by
        intro a hit
        exact mem_inN.mpr ⟨(mem_filter.mp hit).1,(mem_outN.mp ((mem_filter.mp hit).2 late)).2⟩
      have cap := card_le_card sub
      omega

/-- A low acyclic class has no short origin when the complete-row
bound supplies its next-shell size. Every origin of that class owes
exactly one doubled unit before its own missing pairs are credited. -/
theorem acyclic_class_debit {D V q r Y} (free : QFree D V q) (reg : OutEq r D V) (hr : 0<r)
    (sel : Selection D V q r 3 (3*r)) (ym : Y∈(shellOrigins D V 3 (3*r)).image (N2 D V))
    (regime : Room q r) (dag : QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card)
    (fit : r+(r-(q+1))<2*(q-1)) (dist : (r-(q+1))*(r-q)+3≤q) :
    (∀v∈shellFiber D V 3 (3*r) Y,(ball D V v 3).card=3*r) ∧ shellDebt D V 3 (3*r) Y≤1 := by
  have seed := mem_filter.mp (sel.represents Y ym)
  have low := mem_filter.mp seed.1
  let u := sel.rep Y
  have trivGuard : ScoreRoom q r (r-1) 0 := by
    intro h hm
    have bounds := mem_Icc.mp hm
    by_cases hi : h=0
    · subst h
      exact Or.inl ⟨2,by decide,by omega,by omega⟩
    · omega
  have info := selected_stock free reg hr sel ym regime dag fit dist trivGuard
  obtain ⟨hq,a,b,c,d,_⟩ := regime
  have cap := low_third_second free hq reg low.1 a b c d low.2
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) low.1
  rw [reg _ low.1] at one
  have two := @card_B2 D V u
  have three := @card_B3 D V u
  have cx := reg u low.1
  obtain ⟨s,sm,ss⟩ := exists_sink dag (card_pos.mp (by change 0<(outN D V u).card; omega)) le_rfl
  have sy : outN D V s⊆N2 D V u := fun z hm=>(mem_union.mp (headX (free.mono_bound (by omega : 4≤q))
    low.1 sm (outN_subset hm) (mem_outN.mp hm).2)).resolve_left (fun xm=>ss z xm (mem_outN.mp hm).2)
  have w := card_le_card sy
  rw [reg _ (outN_subset sm)] at w
  have next : (N3 D V u).card+1=r := info.2.1
  change (ball D V u 2).card≤2*r+1 at cap
  change (ball D V u 1).card=r+1 at one
  have repScore : (ball D V u 3).card=3*r := by omega
  have all v (vm : v∈shellFiber D V 3 (3*r) Y) : (ball D V v 3).card=3*r := by
    have least := sel.least Y ym v vm
    have upper := (mem_filter.mp (mem_filter.mp vm).1).2
    change (ball D V u 3).card≤_ at least
    omega
  refine ⟨all,?_⟩
  exact (class_residual (m:=1) (fun v vm=>by rw [all v vm]; simp [debit])).trans (by decide)

/-- A one-extra second shell is determined by the cycle if its one
extra vertex is used. Otherwise the cycle's exterior equals the actual
third shell. The two alternatives have different exterior sizes. -/
theorem one_extra_signature {D V q r u C b} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (dag : QFree D (outN D V u) (outN D V u).card)
    (width : (N2 D V u).card=r) (next : (N3 D V u).card<r) (cy : C⊆N2 D V u)
    (cc : q<C.card) (rc : ∀v∈C,Rooted D V v C) (exc : N2 D V u\C={b})
    (fit : r+1<2*(q-1)) (near : C.card-(q-1)<q-1) :
    ((exterior D V C).card=r ∧ N2 D V u=C∪mutualExterior D V C) ∨
      ((exterior D V C).card=r-1 ∧ exterior D V C=N3 D V u) := by
  classical
  let Z := N3 D V u
  have cv : C⊆V := fun _ cm=>N2_subV (cy cm)
  have bm : b∈N2 D V u\C := exc.symm ▸ mem_singleton_self b
  have len := congrArg card exc
  rw [card_singleton] at len
  have rows := complete_rows free hq reg uv dag width next cy cc rc (by omega) (by omega)
  dsimp only at rows
  rw [len,Nat.one_mul] at rows
  have size := rows.2 (by omega)
  have positive : 0<(C.filter (fun v=>Z⊆outN D V v)).card := by
    have lim := rows.1
    change C.card≤(C.filter (fun v=>Z⊆outN D V v)).card+(C.card-(q-1)) at lim
    omega
  obtain ⟨v,vm⟩ := card_pos.mp positive
  have dis : Disjoint (N2 D V u) Z := disjoint_left.mpr (fun _ h1 h2=>(mem_N3.mp h2).2 (mem_N2.mp h1).1)
  have zsub : Z⊆exterior D V C := by
    intro z zm
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨v,(mem_filter.mp vm).1,(mem_filter.mp vm).2 zm⟩,
      fun zc=>disjoint_left.mp dis (cy zc) zm⟩
  have outer : exterior D V C⊆insert b Z := by
    intro z zm
    obtain ⟨seen,off⟩ := mem_sdiff.mp zm
    obtain ⟨a,am,arc⟩ := mem_biUnion.mp seen
    rcases headY (free.mono_bound hq) uv (cy am) (outN_subset arc) (mem_outN.mp arc).2 with e|late
    · have yy := (mem_union.mp e).resolve_left (fun xx=>no_back free hq reg uv dag width (by omega)
        cy cc rc a am z xx (mem_outN.mp arc).2)
      have rest : z∈N2 D V u\C := mem_sdiff.mpr ⟨yy,off⟩
      rw [exc,mem_singleton] at rest
      exact mem_insert.mpr (Or.inl rest)
    · exact mem_insert_of_mem late
  by_cases used : b∈exterior D V C
  · have eq := Subset.antisymm outer (insert_subset used zsub)
    have sizeOut : (exterior D V C).card=r := by
      rw [eq,card_insert_of_notMem (disjoint_left.mp dis (mem_sdiff.mp bm).1)]
      exact size
    obtain ⟨c,cm,arc⟩ := mem_biUnion.mp (mem_sdiff.mp used).1
    exact .inl ⟨sizeOut,recover_shell free hq reg uv dag width next cy cc rc exc cm (mem_outN.mp arc).2 fit near⟩
  · have eq := Subset.antisymm (show exterior D V C⊆Z from fun z zm=>(mem_insert.mp (outer zm)).resolve_left
        (fun zb=>used (zb ▸ zm))) zsub
    refine .inr ⟨?_,eq⟩
    rw [eq]
    change (N3 D V u).card=r-1
    omega

/-- Distinct one-extra origins on the same physical cycle pay with a
real missed pair. The third layers are inferred from the cycle. -/
theorem collision_holes {D V q r u v C a b} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (vv : v∈V) (distinct : N2 D V u≠N2 D V v)
    (first : C⊆N2 D V u) (second : C⊆N2 D V v)
    (aOnly : N2 D V u\C={a}) (bOnly : N2 D V v\C={b})
    (left : ((exterior D V C).card=r ∧ N2 D V u=C∪mutualExterior D V C) ∨
      ((exterior D V C).card=r-1 ∧ exterior D V C=N3 D V u))
    (right : ((exterior D V C).card=r ∧ N2 D V v=C∪mutualExterior D V C) ∨
      ((exterior D V C).card=r-1 ∧ exterior D V C=N3 D V v)) (hr : 0<r) :
    v∉ball D V u 3 ∧ u∉ball D V v 3 := by
  have decomp (Y : Finset ℕ) z (sub : C⊆Y) (only : Y\C={z}) : Y=insert z C := by
    have union := sdiff_union_of_subset sub
    rw [only,singleton_union] at union
    exact union.symm
  have ay := decomp _ _ first aOnly
  have byy := decomp _ _ second bOnly
  have am : a∈N2 D V u\C := aOnly.symm ▸ mem_singleton_self a
  have bm : b∈N2 D V v\C := bOnly.symm ▸ mem_singleton_self b
  rcases left with ⟨len,lu⟩|⟨len,lu⟩ <;> rcases right with ⟨siz,rv⟩|⟨siz,rv⟩
  · exact (distinct (lu.trans rv.symm)).elim
  · omega
  · omega
  · exact second_side_pairs free hq reg uv vv (fun eq=>distinct (congrArg (N2 D V) eq))
      (fun eq=>distinct (ay.trans ((congrArg (fun z=>insert z C) eq).trans byy.symm))) (mem_sdiff.mp am).2 (mem_sdiff.mp bm).2 ay byy lu.symm rv.symm

#print axioms one_extra_signature
#print axioms collision_holes

#print axioms acyclic_class_debit
#print axioms recover_shell
end LeanCH.BR.LowShellCycleSelection
