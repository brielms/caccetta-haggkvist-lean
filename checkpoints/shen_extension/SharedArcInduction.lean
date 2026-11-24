import checkpoints.shen_extension.SharedArcBarrier

namespace LeanCH.BR.Closure.SharedArcInduction
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier SharedArcExpansion

/-- The extension problem can be stated on an ordinary digraph. The old
cycles span, and each has been attached through a directed arc. -/
def Next (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) (F : Family) (B : Finset ℕ) : Prop :=
  Cycle D V q B ∧ B∉F ∧ ∃A∈F,Touch D A B

def ExtensionLaw (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀C F,Built D C F → (∀M∈F,Cycle D V q M) → support F=V → SmallRow q (graph D F) V →
    (∃B,Next D V q F B) → ∃B,Next D V q F B ∧ ∃p,RealDual q (graph D F) V 1 p ∧
      ∀u∈B,∀v∈B,D u v=true → graph D F u v=false → realCol q (graph D F) V p v + q*p u ≤ 1

/-- Two cycles containing the same mark never exhaust their available arc-sharing moves. -/
theorem third_cycle {q n} (X : Model q n) (hq : 2≤q) {C B h} (cc : Cycle X.D X.V q C) (cb : Cycle X.D X.V q B)
    (hit : h∈C∩B) : ∃M∈family X,M≠C ∧ M≠B ∧ (Touch X.D C M ∨ Touch X.D B M) := by
  classical
  let F : Family := {C,B}
  have sub : F⊆family X := by
    intro M mf
    have c : Cycle X.D X.V q M := by
      rcases mem_insert.mp mf with rfl|mb
      · exact cc
      · exact mem_singleton.mp mb ▸ cb
    exact mem_filter.mpr ⟨mem_powerset.mpr c.sub,c⟩
  have all (M) (mf : M∈F) : h∈M := by
    rcases mem_insert.mp mf with rfl|mb
    · exact (mem_inter.mp hit).1
    · exact mem_singleton.mp mb ▸ (mem_inter.mp hit).2
  obtain ⟨A,af,M,mf,off,t⟩ := escape X hq (mem_insert_self C {B}) sub all
  have absent : M≠C ∧ M≠B := by simpa [F] using off
  refine ⟨M,mf,absent.1,absent.2,?_⟩
  rcases mem_insert.mp af with rfl|ab
  · exact Or.inl t
  · exact Or.inr (mem_singleton.mp ab ▸ t)

#print axioms third_cycle

/-- Only this one extension law on the normalized graph is required. -/
theorem fails_on_source {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card) :
    ¬ExtensionLaw q X.D X.V := by
  classical
  obtain ⟨u,uv⟩ := X.live
  obtain ⟨C,_,cc,_,_,_,_⟩ := ShortestReturnCertificate.on_model X hq uv
  have cf : C∈family X := mem_filter.mpr ⟨mem_powerset.mpr cc.sub,cc⟩
  obtain ⟨F,built,sub,_,full,good,_,⟨B,b⟩,bar⟩ := SharedArcBarrier.on_source X hq small cf
  have eqv (A) : SharedArcBarrier.Boundary X F A ↔ Next X.D X.V q F A := by
    constructor
    · exact fun e => ⟨(mem_filter.mp e.1).2,e.2⟩
    · exact fun e => ⟨mem_filter.mpr ⟨mem_powerset.mpr e.1.sub,e.1⟩,e.2⟩
  intro law
  obtain ⟨A,step,p,dual,fit⟩ := law C F built (fun M mf => (mem_filter.mp (sub mf)).2) full good ⟨B,(eqv B).mp b⟩
  obtain ⟨i,ia,j,ja,ij,off,high⟩ := (bar A ((eqv A).mpr step)).2 p dual
  exact high.not_ge (fit i ia j ja ij off)

/-- A proof of the column budget for one shared-arc attachment on every
least-support source would imply the literal all-orders CH conjecture. -/
theorem ch_of_extension
    (law : ∀q n,∀X : Model q n,2≤q → SmallerSmallRow q X.V.card → ExtensionLaw q X.D X.V) :
    CH.CaccettaHaggkvistConjecture := by
  intro n s D hn hs loop degree
  let q := CH.ceilDiv n s
  have cover : n≤q*s := by
    have hm := Nat.mod_lt (n+s-1) hs
    have hd := Nat.mod_add_div (n+s-1) s
    rw [Nat.mul_comm s] at hd
    dsimp [q,CH.ceilDiv]
    omega
  have lt : s<n := by
    have sub : outN D (range n) 0⊆(range n).erase 0 := by
      intro i hi
      obtain ⟨iv,ed⟩ := mem_outN.mp hi
      exact mem_erase.mpr ⟨fun eq => by simp [eq,loop 0 hn] at ed,iv⟩
    have bound := (Compose.FloorSix.out_card degree hn).trans (card_le_card sub)
    have card := card_erase_add_one (mem_range.mpr hn)
    rw [card_range] at card
    omega
  have hq : 2≤q := by
    by_contra! low
    have up := Nat.mul_le_mul_right s (show q≤1 by omega)
    simp only [one_mul] at up
    omega
  by_contra bad
  obtain ⟨base⟩ := normalize hq hn cover loop degree bad
  obtain ⟨n',X,_,small⟩ := GlobalFamilyDual.select base hq
  exact fails_on_source X hq small (law q n' X hq small)

#print axioms fails_on_source
#print axioms ch_of_extension
end LeanCH.BR.Closure.SharedArcInduction
