import checkpoints.shen_extension.PairEscapeTransition
import checkpoints.shen_extension.PairWithdrawal

namespace LeanCH.BR.Closure.ClassPunctureRecurrence
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights MandatoryTwoStep

private noncomputable def column {q n} (X : Model q n) (a : ℕ) : Finset (Finset ℕ) := by
  classical exact X.V.powerset.filter (fun C => Cycle X.D X.V q C ∧ a∈C)

private theorem inclusion {q n} (X : Model q n) {a b} :
    Forces X.D X.V q a b ↔ column X a⊆column X b := by
  classical
  constructor
  · intro ab C ca
    obtain ⟨sub,cycle,ac⟩ := mem_filter.mp ca
    exact mem_filter.mpr ⟨sub,cycle,ab C cycle ac⟩
  · intro ab C c ac
    exact (mem_filter.mp (ab (mem_filter.mpr ⟨mem_powerset.mpr c.sub,c,ac⟩))).2.2

/-- Choose a terminal column below a prescribed anchor; deleting its entire
equivalence class still leaves a shortest cycle through every surviving label. -/
theorem terminal_class {q n} (X : Model q n) {h} (hv : h∈X.V) :
    ∃ a∈X.V,∃ K : Finset ℕ,a∈K ∧ K⊆X.V ∧
      (∀u∈K,Forces X.D X.V q u h) ∧
      (∀u∈K,∀v∈K,Forces X.D X.V q u v) ∧
      (∀z∈X.V\K,∃C,Cycle X.D (X.V\K) q C ∧ z∈C) := by
  classical
  let T := X.V.filter (fun z => Forces X.D X.V q z h)
  have hh : Forces X.D X.V q h h := fun _ _ hit => hit
  obtain ⟨a,atT,least⟩ := T.exists_min_image (fun z => (column X z).card) ⟨h,mem_filter.mpr ⟨hv,hh⟩⟩
  obtain ⟨av,ah⟩ := mem_filter.mp atT
  let K := X.V.filter (fun z => Forces X.D X.V q z a)
  have ka {z} (zk : z∈K) : Forces X.D X.V q z a := (mem_filter.mp zk).2
  have kh {z} (zk : z∈K) : Forces X.D X.V q z h := fun C c zc => ah C c (ka zk C c zc)
  have ak {z} (zk : z∈K) : Forces X.D X.V q a z := by
    have le := least z (mem_filter.mpr ⟨(mem_filter.mp zk).1,kh zk⟩)
    have eq := eq_of_subset_of_card_le ((inclusion X).mp (ka zk)) le
    exact (inclusion X).mpr eq.ge
  refine ⟨a,av,K,mem_filter.mpr ⟨av,fun _ _ hit => hit⟩,filter_subset _ _,fun _ => kh,
    fun _ u _ v C c hit => ak v C c (ka u C c hit),?_⟩
  intro z zu
  obtain ⟨zv,away⟩ := mem_sdiff.mp zu
  have nf : ¬ Forces X.D X.V q z a := fun f => away (mem_filter.mpr ⟨zv,f⟩)
  change ¬(∀C,Cycle X.D X.V q C → z∈C → a∈C) at nf
  push Not at nf
  obtain ⟨C,c,zc,miss⟩ := nf
  exact ⟨C,⟨fun x xc => mem_sdiff.mpr ⟨c.sub xc,fun xk => miss (ka xk C c xc)⟩,
    c.size,c.heads,c.incoming⟩,zc⟩

/-- Exact cost of a stop. A row of the current cycle can point to at most
one deleted chain member, whereas every surviving column can be used once
without creating a transition. These are independent sides of the arc table. -/
theorem stop_cost {q n} (X : Model q n) (hq : 2≤q) {K C} (sub : K⊆X.V)
    (live : K.Nonempty) (chain : ∀u∈K,∀v∈K,Forces X.D X.V q u v)
    (c : Cycle X.D (X.V\K) q C)
    (stop : ∀z∈X.V\K,z∉C → (inN X.D C z).card≤1) :
    ∃a∈K, (∑z∈X.V\C,X.weights z)<q*q*X.weights a := by
  classical
  obtain ⟨a,ak,cap⟩ := K.exists_max_image X.weights live
  let U := X.V\K
  have cv : C⊆X.V := c.sub.trans sdiff_subset
  let W := X.weights
  let T := ∑z∈X.V,W z
  let J (S : Finset ℕ) := ∑x∈C,∑z∈S,if X.D x z=true then W z else 0
  have outside : J U≤∑z∈U,W z := by
    dsimp only [J]
    rw [sum_comm]
    apply sum_le_sum
    intro z zu
    have one : (inN X.D C z).card≤1 := by
      by_cases hit : z∈C
      · exact (c.incoming z hit).le
      · exact stop z zu hit
    calc
      _ = ∑_x∈inN X.D C z,W z := by simp only [inN,sum_filter]
      _ = (inN X.D C z).card*W z := by simp
      _ ≤ W z := by simpa using Nat.mul_le_mul_right (W z) one
  have inside : J K ≤ C.card*W a := by
    have row (x) (xc : x∈C) : (∑z∈K,if X.D x z=true then W z else 0)≤W a := by
      rw [←sum_filter]
      change (∑z∈outN X.D K x,W z)≤W a
      by_cases non : (outN X.D K x).Nonempty
      · obtain ⟨b,bm⟩ := non
        have eq : outN X.D K x={b} := by
          ext z
          constructor
          · intro hit
            exact mem_singleton.mpr (ComparableColumnCut.distinct_heads X hq (cv xc) (sub (mem_outN.mp hit).1)
              (mem_outN.mp hit).2 (mem_outN.mp bm).2 (chain z (mem_outN.mp hit).1 b (mem_outN.mp bm).1))
          · intro e
            exact mem_singleton.mp e ▸ bm
        simpa [eq] using cap b (mem_outN.mp bm).1
      · simp [not_nonempty_iff_eq_empty.mp non]
    simpa [J] using sum_le_sum row
  have table : J U + J K=J X.V := by
    simp only [J,←sum_add_distrib]
    exact sum_congr rfl fun x _ => sum_sdiff sub
  have totals := sum_sdiff sub (f:=W)
  change (∑z∈U,W z)+(∑z∈K,W z)=T at totals
  have pay := single_le_sum (f:=W) (fun _ _ => Nat.zero_le _) ak
  rw [c.size,Nat.succ_mul] at inside
  have bound : J X.V ≤ T+q*W a := by omega
  have pos := sum_lt_sum_of_nonempty (card_pos.mp (show 0<C.card by rw [c.size]; omega))
    (fun x xc => nat_strict.mp X.strict x (cv xc))
  change (∑_x∈C,T)<(∑x∈C,(W x+q*(∑z∈X.V,if X.D x z=true then W z else 0))) at pos
  simp only [sum_const,nsmul_eq_mul,sum_add_distrib,←mul_sum,c.size,Nat.succ_mul,Nat.cast_id] at pos
  change q*T+T < (∑z∈C,W z)+q*J X.V at pos
  have scaled := Nat.mul_le_mul_left q bound
  rw [Nat.mul_add,←Nat.mul_assoc] at scaled
  have comp := sum_sdiff cv (f:=W)
  change (∑z∈X.V\C,W z)+(∑z∈C,W z)=T at comp
  exact ⟨a,ak,by change (∑z∈X.V\C,W z)<q*q*W a; omega⟩

/-- At arbitrary cutoff choose the class before choosing any surviving cycle.
Past the displayed support bound every such cycle has another two-parent
transition in the very same puncture. -/
theorem persistent {q n} (X : Model q n) (hq : 2≤q) {h} (hv : h∈X.V)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q*q*(q-1)+q+1≤X.V.card) :
    ∃K : Finset ℕ,K.Nonempty ∧ K⊆X.V ∧
      (∀u∈K,Forces X.D X.V q u h) ∧
      (∀u∈K,∀v∈K,Forces X.D X.V q u v) ∧
      (∀z∈X.V\K,∃C,Cycle X.D (X.V\K) q C ∧ z∈C) ∧
      (∃C,Cycle X.D (X.V\K) q C) ∧
      ∀C,Cycle X.D (X.V\K) q C →
        ∃N,Cycle X.D (X.V\K) q N ∧ PunctureCycleLoop.Step X.D C N := by
  classical
  obtain ⟨a,_,K,ak,sub,below,chain,cover⟩ := terminal_class X hv
  have live : K.Nonempty := ⟨a,ak⟩
  have length := ComparableColumnCut.chain_size X hq sub
    (fun x xk y yk => Or.inl (chain x xk y yk))
  have distinct : (X.V\K).Nonempty := sdiff_nonempty.mpr (fun all => by
    have := card_le_card all
    omega)
  obtain ⟨z,zu⟩ := distinct
  obtain ⟨seed,cs,_⟩ := cover z zu
  refine ⟨K,live,sub,below,chain,cover,⟨seed,cs⟩,?_⟩
  intro C c
  have oldq : q≤q*q := Nat.le_mul_of_pos_left _ (by omega)
  have small := Nat.mul_le_mul_right (q-1) oldq
  have cap (b) (bk : b∈K) : X.weights b≤(q-1)*X.weights h := by
    by_cases eq : h=b
    · rw [←eq]
      exact Nat.le_mul_of_pos_left _ (by omega)
    · exact (((PunctureReceiverFrontier.classify X hq hv (mem_erase.mpr ⟨Ne.symm eq,sub bk⟩)
        minimum (by omega)).resolve_left (forces_iff.mp (below b bk))).1).le
  by_contra! fail
  have stop (b) (bu : b∈X.V\K) (away : b∉C) : (inN X.D C b).card≤1 := by
    obtain ⟨N,cn,bn⟩ := cover b bu
    by_contra! rich
    exact fail N cn ⟨b,mem_sdiff.mpr ⟨bn,away⟩,rich⟩
  obtain ⟨b,bk,bill⟩ := stop_cost X hq sub live chain c stop
  have upper := Nat.mul_le_mul_left (q*q) (cap b bk)
  rw [←Nat.mul_assoc] at upper
  have cv : C⊆X.V := c.sub.trans sdiff_subset
  have count := card_sdiff_add_card_eq_card cv
  rw [c.size] at count
  have room : q*q*(q-1)≤(X.V\C).card := by omega
  have low := sum_le_sum (s:=X.V\C) (fun z (mem : z∈X.V\C) => minimum z (mem_sdiff.mp mem).1)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at low
  exact bill.not_ge ((upper.trans (Nat.mul_le_mul_right _ room)).trans low)

#print axioms persistent
#print axioms terminal_class
#print axioms stop_cost
end LeanCH.BR.Closure.ClassPunctureRecurrence
