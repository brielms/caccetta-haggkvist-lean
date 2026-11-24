import checkpoints.shen_extension.MarkedCyclePeeling

namespace LeanCH.BR.Closure.FirstPacketBarrier
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights MarkedCyclePeeling

noncomputable def graph (D : CH.Digraph) (F : Family) : CH.Digraph := by
  classical exact fun x y => decide (col D F (x,y)).Nonempty

theorem active {D F x y} : graph D F x y=true ↔ (col D F (x,y)).Nonempty := by
  classical simp [graph]

private theorem original {D F x y} (edge : graph D F x y=true) : D x y=true := by
  obtain ⟨A,ha⟩ := active.mp edge
  exact (mem_col.mp ha).2.2.2

theorem retain_cycle {D F V q A} (a : Cycle D V q A) (af : A∈F) : Cycle (graph D F) V q A := by
  have iff (x) (xa : x∈A) (y) (ya : y∈A) : graph D F x y=true ↔ D x y=true :=
    ⟨original,fun xy => active.mpr ⟨A,mem_col.mpr ⟨af,xa,ya,xy⟩⟩⟩
  refine ⟨a.sub,a.size,?_,?_⟩
  · intro x xa
    have eq : outN (graph D F) A x=outN D A x := by
      ext y
      simp only [mem_outN]
      exact and_congr_right fun ya => iff x xa y ya
    rw [eq,a.heads x xa]
  · intro y ya
    change (inN (graph D F) A y).card=1
    have eq : inN (graph D F) A y=inN D A y := by
      ext x
      simp only [mem_inN]
      exact and_congr_right fun xa => iff x xa y ya
    rw [eq]
    exact a.incoming y ya

private theorem score_form (q) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℕ) (x : ℕ) :
    score q D V w x=w x+q*(∑y∈outN D V x,w y) := by simp only [score,outN,sum_filter]

/-- The last cycle cannot support strict rows for any integral allocation. -/
theorem singleton_fails {D V q M} (c : Cycle D V q M) (w : ℕ→ℕ) :
    ¬Strict q (graph D {M}) V w := by
  classical
  obtain ⟨y,ym,minimum⟩ := M.exists_min_image w (card_pos.mp (by rw [c.size]; omega))
  obtain ⟨p,pi⟩ := card_pos.mp (show 0<(inN D M y).card by rw [show (inN D M y).card=1 from c.incoming y ym]; decide)
  obtain ⟨pm,py⟩ := mem_inN.mp pi
  have one : outN (graph D {M}) V p={y} := by
    ext z
    constructor
    · intro hz
      obtain ⟨_,edge⟩ := mem_outN.mp hz
      obtain ⟨A,mem⟩ := active.mp edge
      obtain ⟨ins,_,za,pz⟩ := mem_col.mp mem
      obtain rfl := mem_singleton.mp ins
      exact mem_singleton.mpr (card_le_one.mp (c.heads p pm).le _ (mem_outN.mpr ⟨za,pz⟩) _ (mem_outN.mpr ⟨ym,py⟩))
    · rintro hit
      obtain rfl := mem_singleton.mp hit
      exact mem_outN.mpr ⟨c.sub ym,active.mpr ⟨M,mem_col.mpr ⟨mem_singleton_self _,pm,ym,py⟩⟩⟩
  intro s
  have high := nat_strict.mp s p (c.sub pm)
  rw [score_form,one,sum_singleton] at high
  have low := sum_le_sum (s:=M.erase p) (fun z (hz : z∈M.erase p) => minimum z (mem_of_mem_erase hz))
  have num := card_erase_add_one pm
  rw [c.size] at num
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,show (M.erase p).card=q by omega] at low
  have split := sum_erase_add M w pm
  have total := sum_le_sum_of_subset_of_nonneg (f:=w) c.sub (by intros; omega)
  omega

/-- A cut loses at most one head per row. If an old allocation fails, its
failed row loses exactly one head and the debit is exactly q times its weight. -/
theorem row_bill {D V q M F G} (step : Cut D M F G) {w : ℕ→ℕ}
    (yes : Strict q (graph D F) V w) (no : ¬Strict q (graph D G) V w) :
    ∃p∈V,∃y∈V, graph D F p y=true ∧ graph D G p y=false ∧
      score q (graph D F) V w p=score q (graph D G) V w p+q*w y ∧
      score q (graph D G) V w p≤∑z∈V,w z := by
  classical
  obtain ⟨e,_,_,lost,matching⟩ := step.packet
  rw [nat_strict] at no
  push Not at no
  obtain ⟨p,pv,low⟩ := no
  have high := nat_strict.mp yes p pv
  let O := outN (graph D F) V p
  let S := outN (graph D G) V p
  have sub : S⊆O := by
    intro z zs
    obtain ⟨zv,hit⟩ := mem_outN.mp zs
    obtain ⟨A,ag⟩ := active.mp hit
    obtain ⟨aG,use⟩ := mem_col.mp ag
    exact mem_outN.mpr ⟨zv,active.mpr ⟨A,mem_col.mpr ⟨step.less.subset aG,use⟩⟩⟩
  have live : (O\S).Nonempty := sdiff_nonempty.mpr (fun back => by
    have eq := Subset.antisymm back sub
    rw [score_form] at high low
    change _<w p+q*(∑z∈O,w z) at high
    change w p+q*(∑z∈S,w z)≤_ at low
    rw [eq] at high
    omega)
  obtain ⟨y,yd⟩ := live
  have data {z} (hit : z∈O\S) : z∈V ∧ graph D F p z=true ∧ graph D G p z=false ∧ col D F (p,z)=col D F e := by
    obtain ⟨zo,zs⟩ := mem_sdiff.mp hit
    obtain ⟨zv,has⟩ := mem_outN.mp zo
    have miss : graph D G p z=false := Bool.eq_false_iff.mpr (fun edge => zs (mem_outN.mpr ⟨zv,edge⟩))
    have empty : col D G (p,z)=∅ := not_nonempty_iff_eq_empty.mp (fun pos => by rw [active.mpr pos] at miss; contradiction)
    exact ⟨zv,has,miss,(lost _ (active.mp has)).mp empty⟩
  obtain ⟨yv,yo,yn,ye⟩ := data yd
  have one : O\S={y} := by
    ext z
    constructor
    · intro hit
      exact mem_singleton.mpr (congrArg Prod.snd (matching (p,z) (p,y) (data hit).2.2.2 ye (Or.inl rfl)))
    · intro hit
      exact mem_singleton.mp hit ▸ yd
  have split := sum_sdiff sub (f:=w)
  rw [one,sum_singleton] at split
  refine ⟨p,pv,y,yv,yo,yn,?_,low⟩
  rw [score_form,score_form]
  change w p+q*(∑z∈O,w z)=w p+q*(∑z∈S,w z)+q*w y
  rw [←split,Nat.mul_add]
  omega

/-- Keep the actual order budget, with an existential allocation on each
family. A failed family admits no positive integral reweighting in budget. -/
def Feasible (q n : ℕ) (D : CH.Digraph) (V : Finset ℕ) (F : Family) : Prop :=
  ∃w : ℕ→ℕ,(∀z∈V,0<w z) ∧ (∑z∈V,w z)≤n ∧ Strict q (graph D F) V w

private theorem crossing {α} {R : α→α→Prop} {P : α→Prop} {x y}
    (path : Relation.ReflTransGen R x y) (start : P x) (finish : ¬P y) :
    ∃a b,Relation.ReflTransGen R x a ∧ R a b ∧ P a ∧ ¬P b := by
  induction path with
  | refl => exact (finish start).elim
  | @tail a b path edge ih =>
    by_cases good : P a
    · exact ⟨a,b,path,edge,good,finish⟩
    · exact ih good

noncomputable def family {q n} (X : Model q n) : Family := by
  classical exact X.V.powerset.filter (Cycle X.D X.V q)

theorem full_feasible {q n} (X : Model q n) (hq : 2≤q) : Feasible q n X.D X.V (family X) := by
  classical
  refine ⟨X.weights,X.positive,X.bounded,nat_strict.mpr ?_⟩
  intro p pv
  have same : outN (graph X.D (family X)) X.V p=outN X.D X.V p := by
    ext y
    simp only [mem_outN]
    apply and_congr_right
    intro yv
    refine ⟨original,?_⟩
    intro edge
    obtain ⟨A,a,pa,ya⟩ := edge_cycle X hq pv yv edge
    exact active.mpr ⟨A,mem_col.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr a.sub,a⟩,pa,ya,edge⟩⟩
  have high := nat_strict.mp X.strict p pv
  rwa [score_form,same,←score_form]

/-- Every prescribed shortest cycle in the same normalized source has a
reachable first barrier. The two families differ by a partial matching; all
eligible allocations on the first family fail on the second. -/
theorem first {q n} (X : Model q n) (hq : 2≤q) {M} (c : Cycle X.D X.V q M) :
    ∃F G,Relation.ReflTransGen (Cut X.D M) (family X) F ∧ Cut X.D M F G ∧
      Feasible q n X.D X.V F ∧ ¬Feasible q n X.D X.V G ∧
      (∀w : ℕ→ℕ,(∀z∈X.V,0<w z) → (∑z∈X.V,w z)≤n → Strict q (graph X.D F) X.V w →
        ∃p∈X.V,∃y∈X.V,graph X.D F p y=true ∧ graph X.D G p y=false ∧
          score q (graph X.D F) X.V w p=score q (graph X.D G) X.V w p+q*w y ∧
          score q (graph X.D G) X.V w p≤∑z∈X.V,w z) := by
  classical
  have ac (C) (cf : C∈family X) : Cycle X.D X.V q C := (mem_filter.mp cf).2
  have mf : M∈family X := mem_filter.mpr ⟨mem_powerset.mpr c.sub,c⟩
  have start := full_feasible X hq
  obtain ⟨F,G,path,step,yes,no⟩ := crossing (P:=Feasible q n X.D X.V)
    (peel ac mf) start (fun ⟨w,_,_,s⟩ => singleton_fails c w s)
  exact ⟨F,G,path,step,yes,no,fun w pos budget strict =>
    row_bill step strict (fun win => no ⟨w,pos,budget,win⟩)⟩

#print axioms first
#print axioms row_bill
#print axioms singleton_fails
end LeanCH.BR.Closure.FirstPacketBarrier
