import checkpoints.shen_extension.InversePacketDeletion
import LeanCH.BR.BRFiniteSimplexAlternative

namespace LeanCH.BR.Closure.SharedArcStrictParent
open Finset Matrix BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier SharedArcMinimalPacket FiniteCutInverse
open InverseOffDiagonal
open scoped Matrix

/-- The old spanning graph of a minimum boundary packet with at least two
changed heads admits one probability vector making every column strictly subunit. -/
theorem parent {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (charge : ∀ a b : X.V, (a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false →
      1 ≤ (q:ℝ)*H b a)
    (multi : 1 < (targets X.D X.V F B).card) :
    ∃ p : X.V → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      ∀ j, (p ᵥ* realMatrix q (graph X.D F) X.V) j < 1 := by
  classical
  obtain ⟨b,bt,d,dt,bd⟩ := Finset.one_lt_card.mp multi
  obtain ⟨bv,bb,a,ab,ed,off⟩ := mem_filter.mp bt
  obtain ⟨dv,db,c,cb,ed',off'⟩ := mem_filter.mp dt
  have cyc : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  let u : X.V := ⟨a,cyc.sub ab⟩
  let v : X.V := ⟨b,bv⟩
  let x : X.V := ⟨c,cyc.sub cb⟩
  let y : X.V := ⟨d,dv⟩
  let : Nonempty X.V := ⟨v⟩
  let E := graph X.D F
  let G := graph X.D (insert B F)
  have incl (k l : ℕ) (old : E k l=true) : G k l=true := by
    obtain ⟨M,h⟩ := active.mp old
    obtain ⟨mf,km,lm,kl⟩ := mem_col.mp h
    exact active.mpr ⟨M,mem_col.mpr ⟨mem_insert_of_mem mf,km,lm,kl⟩⟩
  have sub := realMatrix_mono_graph (q:=q) (V:=X.V) (fun k _ l _ old => incl k l old)
  have uv : G u v=true := active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,ab,bb,ed⟩⟩
  have xy : G x y=true := active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,cb,db,ed'⟩⟩
  have h1 := (SharedArcPacketReturns.zero_and_strict X hq small step least inv charge u v
    ab bb ed off cb db ed' off' bd.symm).2
  have h2 := (SharedArcPacketReturns.zero_and_strict X hq small step least inv charge x y
    cb db ed' off' ab bb ed off bd).2
  have omit1 : E u v=false := off
  have omit2 : E x y=false := off'
  apply strict_dual
  apply two_strict inv (fun i j ne => graph_positive hq inv ne) sub (a:=u) (c:=x) (b:=v) (d:=y)
  · intro eq
    exact bd (congrArg Subtype.val eq).symm
  · change 1 < (realMatrix q G X.V u v - realMatrix q E X.V u v)*H v u
    simpa [realMatrix_entry,uv,omit1] using h1
  · change 1 < (realMatrix q G X.V x y - realMatrix q E X.V x y)*H y x
    simpa [realMatrix_entry,xy,omit2] using h2

/-- A superthreshold deletion and an unreachable different label force all
columns strictly below one under a single distribution. -/
theorem separated {q : ℕ} (hq : 2 ≤ q) {D E : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q D V) H)
    (sub : ∀ u∈V, ∀ v∈V, E u v=true → D u v=true)
    (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (a b : V) (edge : D a b=true) (off : E a b=false) (strong : 1 < (q:ℝ)*H b a)
    (i j : V) (different : i ≠ b) (blocked : (i:ℕ) ∉ ball E V j q) :
    ∃ p : V → ℝ, (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧ ∀ k, (p ᵥ* realMatrix q E V) k < 1 := by
  classical
  let : Nonempty V := ⟨a⟩
  let S := WeightedArithmetic.rationalMatrix q (adjacencyMatrix E V)
  have sep := FiniteDual.rational_demand_strict_separator (J:=V) S (fun _ => 1) 1 (by norm_num)
  have impossible : ¬∃ w : V → ℚ, (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
      ∀ k, 1 ≤ ∑ l, S k l * w l := by
    rintro ⟨w,wn,wm,wr⟩
    let W : V → ℝ := fun l => (w l : ℝ)
    have nn (l : V) : 0 ≤ W l := by dsimp [W]; exact_mod_cast wn l
    have mass : ∑ k, W k = 1 := by dsimp [W]; exact_mod_cast wm
    have live : W ≠ 0 := by intro hz; rw [hz] at mass; simp at mass
    have good (k : V) : 0 ≤ (excess (realMatrix q E V) *ᵥ W) k := by
      rw [mulVec_excess,mass,sub_nonneg]
      change 1 ≤ ∑ l, (S k l : ℝ) * (w l : ℝ)
      exact_mod_cast wr k
    have cost : 1 < (realMatrix q D V a b - realMatrix q E V a b)*H b a := by
      simpa [realMatrix_entry,edge,off] using strong
    obtain ⟨_,t,ht,_,ray⟩ := single_strict inv (fun _ _ ne => graph_positive hq inv ne)
      (realMatrix_mono_graph sub) a b cost W nn live good
    have wi : 0 < W i := (ray i) ▸ mul_pos ht (graph_positive hq inv different)
    have pos : 0 < w i := by dsimp [W] at wi; exact_mod_cast wi
    apply blocked
    apply feasible_reach_positive_within hq free small (extendWeight V w) _ _ j.property i.property
    · simpa [extendWeight_on] using pos
    · intro k hk
      rw [extendWeight_on V w ⟨k,hk⟩]; exact wn _
    · intro k hk
      rw [mass_extendWeight,wm,row_extendWeight q E V w ⟨k,hk⟩]
      exact wr _
  obtain ⟨p,pn,pm,pc⟩ := sep impossible
  refine ⟨p,pn,pm,fun k => ?_⟩
  have e := pc k
  simp only [Rat.cast_one,one_mul,mul_one,pm] at e
  exact e

/-- A single deleted arc already gives strict separation when another
changed arc has a tail different from the deleted head. -/
theorem punctured {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (charge : ∀ a b : X.V, (a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false →
      1 ≤ (q:ℝ)*H b a)
    (a b i j : X.V) (ab : (a:ℕ)∈B) (bb : (b:ℕ)∈B) (ed : X.D a b=true) (off : graph X.D F a b=false)
    (ib : (i:ℕ)∈B) (jb : (j:ℕ)∈B) (ij : X.D i j=true) (miss : graph X.D F i j=false)
    (diff : (j:ℕ) ≠ b) (cross : i ≠ b) :
    ∃ p : X.V → ℝ, (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧
      ∀ k, (p ᵥ* realMatrix q (eraseArc (graph X.D (insert B F)) a b) X.V) k < 1 := by
  let G := graph X.D (insert B F)
  have he : G a b=true := active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,ab,bb,ed⟩⟩
  exact separated hq inv (fun u _ v _ e => eraseArc_sub G a b u v e)
    (qfree_sub (eraseArc_sub G a b) (PrivateArcEndpoints.graph_free X (insert B F))) small
    a b he (by simp [eraseArc])
    (SharedArcPacketReturns.zero_and_strict X hq small step least inv charge a b ab bb ed off ib jb ij miss diff).2
    i j cross (SharedArcPacketReturns.no_return X hq step least ab bb ed off ib jb ij miss diff)


end LeanCH.BR.Closure.SharedArcStrictParent

#print axioms LeanCH.BR.Closure.SharedArcStrictParent.parent
#print axioms LeanCH.BR.Closure.SharedArcStrictParent.punctured

