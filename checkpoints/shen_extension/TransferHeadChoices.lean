import checkpoints.shen_extension.PaidCycleFamilyOrbit

namespace LeanCH.BR.Closure.TransferHeadChoices
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights ShenPrimeTransition
open MarkedCyclePeeling FirstPacketBarrier JointCycleFamilyBarrier

/-- Keep one failed row and every head contributing to its debit. Distinct
heads necessarily lead to distinct successor cycles. Every choice still
witnesses the original failed transfer, with its original weights. -/
theorem choices {q n} (X : Model q n) {F w A M} (sub : F⊆family X)
    (wp : ∀v∈X.V,0<w v) (budget : (∑v∈X.V,w v)≤n) (strict : Strict q (graph X.D F) X.V w)
    (af : A∈F) (mf : M∈F) (ne : A≠M) :
    let E := graph X.D F
    let Z := A\M
    let U := X.V\Z
    let g := TwoCycleTransfer.deposit E A M w
    ∃p∈X.V\A, (outN E Z p).Nonempty ∧
      score q E U (fun v => w v+g v) p≤(∑v∈U,(w v+g v)) ∧
      score q E X.V w p+TwoCycleTransfer.unused E A M w+g p+q*(∑v∈outN E U p,g v) ≤
        (∑v∈X.V,w v)+q*(∑v∈outN E Z p,w v) ∧
      ∃dest : ℕ→Finset ℕ,Set.InjOn dest (outN E Z p : Set ℕ) ∧
        ∀z∈outN E Z p,p∈dest z ∧ z∈dest z ∧ ExitTo X F w A M (dest z) := by
  classical
  intro E Z U g
  obtain ⟨N,nf,_,_,p,pa,z,zh,arc,fail,debit⟩ := exit_any X sub wp budget strict af mf ne
  have pv : p∈X.V := (show Cycle X.D X.V q N from (mem_filter.mp (sub nf)).2).sub (mem_sdiff.mp pa).1
  have rows (v) (vz : v∈outN E Z p) : ∃L∈F,p∈L ∧ v∈L := by
    obtain ⟨L,used⟩ := active.mp (mem_outN.mp vz).2
    obtain ⟨lf,pl,vl,_⟩ := mem_col.mp used
    exact ⟨L,lf,pl,vl⟩
  choose! dest df support using rows
  refine ⟨p,mem_sdiff.mpr ⟨pv,(mem_sdiff.mp pa).2⟩,⟨z,mem_outN.mpr ⟨(mem_inter.mp zh).2,arc⟩⟩,
    fail,debit,dest,?_,?_⟩
  · intro x xm y ym same
    have c := retain_cycle (show Cycle X.D X.V q (dest x) from (mem_filter.mp (sub (df x xm))).2) (df x xm)
    exact card_le_one.mp (c.heads p (support x xm).1).le _
      (mem_outN.mpr ⟨(support x xm).2,(mem_outN.mp xm).2⟩) _
      (mem_outN.mpr ⟨same ▸ (support y ym).2,(mem_outN.mp ym).2⟩)
  · intro v vz
    obtain ⟨pl,vl⟩ := support v vz
    obtain ⟨del,pvArc⟩ := mem_outN.mp vz
    exact ⟨pl,vl,df v vz,fun eq => (mem_sdiff.mp pa).2 (eq ▸ pl),fun eq => (mem_sdiff.mp del).2 (eq ▸ vl),
      p,mem_sdiff.mpr ⟨pl,(mem_sdiff.mp pa).2⟩,v,mem_inter.mpr ⟨vl,del⟩,pvArc,fail,debit⟩

abbrev Pair := Finset ℕ × Finset ℕ

/-- A single graph of pairs includes all allocations admitted by the budget. -/
def Move {q n} (X : Model q n) (F : Family) (a b : Pair) : Prop :=
  b.1=a.2 ∧ ∃w : ℕ→ℕ,(∀v∈X.V,0<w v) ∧ (∑v∈X.V,w v)≤n ∧
    Strict q (graph X.D F) X.V w ∧ ExitTo X F w a.2 a.1 b.2

/-- From any initial pair, choose the recurrent class before choosing the
allocation. All successors for all feasible allocations remain inside it.
Strong connectivity is for the union of the permitted transitions. -/
theorem recurrent_class {q n} (X : Model q n) {F : Family} {a : Pair}
    (first : a.1∈F) (second : a.2∈F) (distinct : a.1≠a.2) :
    ∃S : Finset Pair,S.Nonempty ∧
      (∀b∈S,b.1∈F ∧ b.2∈F ∧ b.1≠b.2 ∧ Relation.ReflTransGen (Move X F) a b) ∧
      (∀b∈S,∀d,Move X F b d → d∈S) ∧
      ∀b∈S,∀d∈S,Relation.ReflTransGen (Move X F) b d := by
  classical
  let P := (F ×ˢ F).filter (fun b => b.1≠b.2)
  have legal {p : Pair} : p∈P ↔ p.1∈F ∧ p.2∈F ∧ p.1≠p.2 := by simp [P,and_assoc]
  have start : a∈P := legal.mpr ⟨first,second,distinct⟩
  have stay {b d : Pair} (bl : b∈P) (step : Move X F b d) : d∈P := by
    obtain ⟨link,w,_,_,_,exit⟩ := step
    exact legal.mpr ⟨link.symm ▸ (legal.mp bl).2.1,exit.1,link.symm ▸ Ne.symm exit.2.1⟩
  let R (b : Pair) := P.filter (Relation.ReflTransGen (Move X F) b)
  have mem {b d} : d∈R b ↔ d∈P ∧ Relation.ReflTransGen (Move X F) b d := mem_filter
  obtain ⟨b,ba,least⟩ := (R a).exists_min_image (fun d => (R d).card) ⟨a,mem.mpr ⟨start,.refl⟩⟩
  have nesting {u v : Pair} (walk : Relation.ReflTransGen (Move X F) u v) : R v⊆R u :=
    fun _ inside => mem.mpr ⟨(mem.mp inside).1,walk.trans (mem.mp inside).2⟩
  have all (d) (db : d∈R b) : R d=R b := eq_of_subset_of_card_le
    (nesting (mem.mp db).2) (least d (nesting (mem.mp ba).2 db))
  refine ⟨R b,⟨b,mem.mpr ⟨(mem.mp ba).1,.refl⟩⟩,?_,?_,?_⟩
  · intro d db
    obtain ⟨u,v,diff⟩ := legal.mp (mem.mp db).1
    exact ⟨u,v,diff,(mem.mp ba).2.trans (mem.mp db).2⟩
  · intro d db e step
    exact mem.mpr ⟨stay (mem.mp db).1 step,(mem.mp db).2.tail step⟩
  · intro d db e eb
    exact (mem.mp (show e∈R d from (all d db).symm ▸ eb)).2

/-- An actual successor may be selected on a lost head whose own weight
was not forwarded to a recipient seen by this failing row. -/
theorem uncompensated {q n} (X : Model q n) {F w A M} (sub : F⊆family X)
    (wp : ∀v∈X.V,0<w v) (budget : (∑v∈X.V,w v)≤n) (strict : Strict q (graph X.D F) X.V w)
    (af : A∈F) (mf : M∈F) (ne : A≠M) :
    let E := graph X.D F
    let U := X.V\(A\M)
    let g := TwoCycleTransfer.deposit E A M w
    ∃p∈X.V\A,∃z∈outN E (A\M) p,∃L,p∈L ∧ z∈L ∧ ExitTo X F w A M L ∧
      score q E U (fun v => w v+g v) p≤(∑v∈U,(w v+g v)) ∧
      ∀u∈TwoCycleTransfer.crossing E A M,TwoCycleTransfer.succHead E A u=z →
        E p (TwoCycleTransfer.succHead E M u)=false := by
  classical
  intro E U g
  let B := TwoCycleTransfer.crossing E A M
  let d := TwoCycleTransfer.succHead E A
  let r := TwoCycleTransfer.succHead E M
  obtain ⟨p,pa,_,fail,bill,dest,_,each⟩ := choices X sub wp budget strict af mf ne
  let R := outN E U p
  let H := outN E (A\M) p
  let good := B.filter (fun u => E p (r u)=true)
  have ac : Cycle E X.V q A := retain_cycle (show Cycle X.D X.V q A from (mem_filter.mp (sub af)).2) af
  have mc : Cycle E X.V q M := retain_cycle (show Cycle X.D X.V q M from (mem_filter.mp (sub mf)).2) mf
  have inject {C} (c : Cycle E X.V q C) {u v} (uc : u∈C) (vc : v∈C)
      (eq : TwoCycleTransfer.succHead E C u=TwoCycleTransfer.succHead E C v) : u=v := by
    have hit (a) (az : a∈C) : TwoCycleTransfer.succHead E C a∈outN E C a := by
      have pos : (outN E C a).Nonempty := card_pos.mp (by rw [c.heads a az]; decide)
      simpa only [TwoCycleTransfer.succHead,dite_eq_left pos] using (outN E C a).min'_mem pos
    obtain ⟨zc,uz⟩ := mem_outN.mp (hit u uc)
    have vz := (mem_outN.mp (hit v vc)).2
    rw [←eq] at vz
    exact card_le_one.mp (c.incoming _ zc).le _ (mem_inN.mpr ⟨uc,uz⟩) _ (mem_inN.mpr ⟨vc,vz⟩)
  have both {u} (ug : u∈good) : u∈A∩M := (mem_filter.mp (mem_filter.mp ug).1).1
  have eq : (∑v∈good.image d,w v)=∑v∈good.image r,g v := by
    rw [sum_image (fun u hu v hv same => inject ac (mem_inter.mp (both hu)).1 (mem_inter.mp (both hv)).1 same),
      sum_image (fun u hu v hv same => inject mc (mem_inter.mp (both hu)).2 (mem_inter.mp (both hv)).2 same)]
    exact sum_congr rfl (fun u hu => (TwoCycleTransfer.paired_deposit mc w (mem_filter.mp hu).1).symm)
  have paid : good.image r⊆R := by
    intro v mem
    obtain ⟨u,ug,rfl⟩ := mem_image.mp mem
    have loc := TwoCycleTransfer.recipient_location ac mc (mem_filter.mp ug).1
    exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨mc.sub (mem_sdiff.mp loc).1,
      fun l => (mem_sdiff.mp loc).2 (mem_sdiff.mp l).1⟩,(mem_filter.mp ug).2⟩
  have some : (H\good.image d).Nonempty := sdiff_nonempty.mpr (fun all => by
    have left := sum_le_sum_of_subset_of_nonneg (f:=w) all (by intros;omega)
    rw [eq] at left
    have right := sum_le_sum_of_subset_of_nonneg (f:=g) paid (by intros;omega)
    have cap := Nat.mul_le_mul_left q (left.trans right)
    have old := nat_strict.mp strict p (mem_sdiff.mp pa).1
    change (∑v∈X.V,w v)<score q E X.V w p at old
    change score q E X.V w p+TwoCycleTransfer.unused E A M w+g p+q*(∑z∈R,g z)≤
      (∑v∈X.V,w v)+q*(∑z∈H,w z) at bill
    omega)
  obtain ⟨z,zh⟩ := some
  obtain ⟨hit,miss⟩ := mem_sdiff.mp zh
  obtain ⟨pl,zl,step⟩ := each z hit
  refine ⟨p,pa,z,hit,dest z,pl,zl,step,fail,?_⟩
  intro u ub uz
  exact Bool.eq_false_iff.mpr (fun seen => miss (mem_image.mpr ⟨u,mem_filter.mpr ⟨ub,seen⟩,uz⟩))

#print axioms uncompensated
#print axioms recurrent_class
#print axioms choices
end LeanCH.BR.Closure.TransferHeadChoices
