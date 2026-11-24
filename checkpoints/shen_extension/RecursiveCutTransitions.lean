import checkpoints.shen_extension.MinimalCutReturns

namespace LeanCH.BR.ShenReturnCut
open BRq2 BRq3 BR45
open Classical

/-- The child keeps exactly the old boundary columns to which its remaining
rows still point. Its new columns lie in the rows just removed. -/
theorem transition_labels {D : CH.Digraph} {V A B : Finset ℕ} (av : A⊆V) (ba : B⊆A) :
    boundary D V B=(boundary D V A∩image D V B)∪boundary D A B ∧
    Disjoint (boundary D V A∩image D V B) (boundary D A B) := by
  have inside {z} (h : z∈boundary D A B) : z∈A := by
    obtain ⟨w,_,arc⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp h).1
    exact (mem_outN.mp arc).1
  constructor
  · ext z; constructor
    · intro hz
      obtain ⟨im,no⟩ := Finset.mem_sdiff.mp hz
      obtain ⟨w,hw,edge⟩ := Finset.mem_biUnion.mp im
      by_cases za : z∈A
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_biUnion.mpr ⟨w,hw,mem_outN.mpr ⟨za,(mem_outN.mp edge).2⟩⟩,no⟩)
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_biUnion.mpr ⟨w,ba hw,edge⟩,za⟩,im⟩)
    · intro hz; rcases Finset.mem_union.mp hz with old|fresh
      · obtain ⟨hc,im⟩ := Finset.mem_inter.mp old
        exact Finset.mem_sdiff.mpr ⟨im,fun hb => (Finset.mem_sdiff.mp hc).2 (ba hb)⟩
      · obtain ⟨im,no⟩ := Finset.mem_sdiff.mp fresh
        obtain ⟨w,hw,edge⟩ := Finset.mem_biUnion.mp im
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr
          ⟨w,hw,mem_outN.mpr ⟨av (inside fresh),(mem_outN.mp edge).2⟩⟩,no⟩
  · exact Finset.disjoint_left.mpr (fun _ ho hn => (Finset.mem_sdiff.mp (Finset.mem_inter.mp ho).1).2 (inside hn))

theorem transition_count {D : CH.Digraph} {V A B : Finset ℕ} (av : A⊆V) (ba : B⊆A) :
    (boundary D V B).card+(boundary D V A \ image D V B).card=
      (boundary D V A).card+(boundary D A B).card := by
  obtain ⟨eq,dis⟩ := transition_labels av ba
  rw [eq,Finset.card_union_of_disjoint dis]
  have := Finset.card_sdiff_add_card_inter (boundary D V A) (image D V B)
  omega

/-- A given column is active on an interval along any nested sequence.
This holds also when the three states are arbitrarily many steps apart. -/
theorem no_reappearance {D : CH.Digraph} {V A B C : Finset ℕ} (ba : B⊆A) (cb : C⊆B) :
    boundary D V A∩boundary D V C⊆boundary D V B := by
  intro z hz
  obtain ⟨first,last⟩ := Finset.mem_inter.mp hz
  obtain ⟨w,hw,edge⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp last).1
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨w,cb hw,edge⟩,fun h => (Finset.mem_sdiff.mp first).2 (ba h)⟩

/-- Affordability means that even after charging every external column once,
the induced minimum degree suffices for the same q-cutoff problem. -/
def affordable (D : CH.Digraph) (V : Finset ℕ) (q s : ℕ) (A : Finset ℕ) :=
  A.card+q*(boundary D V A).card≤q*s

structure Terminal (D : CH.Digraph) (V : Finset ℕ) (q s : ℕ) (A : Finset ℕ) : Prop where
  inside : A⊆V
  nonempty : A.Nonempty
  paid : affordable D V q s A
  stopped : ∀ B⊆A,B.Nonempty → B≠A → ¬affordable D V q s B

/-- A complete descent from any affordable state; the start and each child
use the same original adjacency data. -/
theorem descend {D : CH.Digraph} {V U : Finset ℕ} {q s} (uv : U⊆V) (un : U.Nonempty)
    (paid : affordable D V q s U) : ∃ A⊆U,Terminal D V q s A := by
  by_cases next : ∃ B⊆U,B.Nonempty ∧ B≠U ∧ affordable D V q s B
  · obtain ⟨B,bu,bn,diff,ok⟩ := next
    have decrease := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨bu,diff⟩)
    obtain ⟨A,ab,term⟩ := descend (bu.trans uv) bn ok
    exact ⟨A,ab.trans bu,term⟩
  · exact ⟨U,Finset.Subset.refl _,uv,un,paid,fun B bu bn diff ok => next ⟨B,bu,bn,diff,ok⟩⟩
termination_by U.card

theorem from_host {D : CH.Digraph} {V : Finset ℕ} {q s} (ne : V.Nonempty) (ord : V.card≤q*s) :
    ∃ A,Terminal D V q s A := by
  have eq : boundary D V V=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z h; obtain ⟨im,no⟩ := Finset.mem_sdiff.mp h
    obtain ⟨_,_,hz⟩ := Finset.mem_biUnion.mp im; exact no (mem_outN.mp hz).1
  obtain ⟨A,_,term⟩ := descend (D:=D) (V:=V) (Finset.Subset.refl _) ne (by simpa [affordable,eq] using ord)
  exact ⟨A,term⟩

/-- The exact price a terminal state imposes on every proper restriction,
including its unused starting margin and the actual retired columns. -/
theorem Terminal.drift {D : CH.Digraph} {V A B : Finset ℕ} {q s} (T : Terminal D V q s A)
    (sub : B⊆A) (ne : B.Nonempty) (proper : B≠A) :
    let slack := q*s-(A.card+q*(boundary D V A).card)
    (A \ B).card+1+slack+q*(boundary D V A \ image D V B).card≤q*(boundary D A B).card := by
  have eq := congrArg (fun n : ℕ => q*n) (transition_count (D:=D) T.inside sub)
  simp only [Nat.mul_add] at eq
  have paid := T.paid
  have fail := T.stopped B sub ne proper
  dsimp only [affordable] at paid fail
  have card := Finset.card_sdiff_add_card_eq_card sub
  dsimp only; omega

/-- Remove all current parents of a set of external columns as a single
transition. At a terminal state the parents must outnumber those columns
by the explicit ratio, whenever any row survives. -/
theorem Terminal.owner_expansion {D : CH.Digraph} {V A Z : Finset ℕ} {q s}
    (T : Terminal D V q s A) (zc : Z⊆boundary D V A) (zn : Z.Nonempty)
    (remains : (A \ Z.biUnion (inN D A)).Nonempty) :
    let P := Z.biUnion (inN D A)
    let slack := q*s-(A.card+q*(boundary D V A).card)
    q*Z.card+P.card+1+slack≤q*P.card := by
  let P := Z.biUnion (inN D A)
  let B := A \ P
  have pa : P⊆A := by
    intro w hw; obtain ⟨_,_,arc⟩ := Finset.mem_biUnion.mp hw
    exact (mem_inN.mp arc).1
  have pn : P.Nonempty := by
    obtain ⟨z,hz⟩ := zn
    obtain ⟨w,hw,arc⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp (zc hz)).1
    exact ⟨w,Finset.mem_biUnion.mpr ⟨z,hz,mem_inN.mpr ⟨hw,(mem_outN.mp arc).2⟩⟩⟩
  have proper : B≠A := by
    intro he
    obtain ⟨w,hw⟩ := pn
    have hb : w∈B := he ▸ pa hw
    exact (Finset.mem_sdiff.mp hb).2 hw
  have eq : A \ B=P := by
    ext x; simp only [B,Finset.mem_sdiff]
    constructor
    · rintro ⟨xa,notB⟩; by_contra h; exact notB ⟨xa,h⟩
    · intro xp; exact ⟨pa xp,fun h => h.2 xp⟩
  have lost : Z⊆boundary D V A \ image D V B := by
    intro z hz
    refine Finset.mem_sdiff.mpr ⟨zc hz,?_⟩
    intro h
    obtain ⟨w,wb,arc⟩ := Finset.mem_biUnion.mp h
    obtain ⟨wa,no⟩ := Finset.mem_sdiff.mp wb
    exact no (Finset.mem_biUnion.mpr ⟨z,hz,mem_inN.mpr ⟨wa,(mem_outN.mp arc).2⟩⟩)
  have fresh : boundary D A B⊆P := by
    intro y hy; rw [← eq]
    obtain ⟨im,no⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨_,_,arc⟩ := Finset.mem_biUnion.mp im
    exact Finset.mem_sdiff.mpr ⟨(mem_outN.mp arc).1,no⟩
  have bill := T.drift Finset.sdiff_subset remains proper
  change (A \ B).card+_+_+q*(boundary D V A \ image D V B).card≤q*(boundary D A B).card at bill
  rw [eq] at bill
  have lo := Nat.mul_le_mul_left q (Finset.card_le_card lost)
  have hi := Nat.mul_le_mul_left q (Finset.card_le_card fresh)
  change q*Z.card+P.card+1+_≤q*P.card
  omega

#print axioms transition_labels
#print axioms no_reappearance
#print axioms descend
#print axioms Terminal.owner_expansion

/-- Run the half-ball argument again in the terminal state's actual induced
graph. A small internal cut must collectively hit old exits; its allowance
for retired labels is divided by q. -/
theorem Terminal.second_cut {D : CH.Digraph} {V A : Finset ℕ} {q s}
    (T : Terminal D V q s A) (hf : QFree D V q) (hq : 2≤q)
    (hm : ∀ x∈V,s≤(outN D V x).card) :
    let d := s-(boundary D V A).card
    0<d ∧ A.card≤q*d ∧
    ∃ u∈A,∃ k,k+1≤(q+1)/2 ∧ ∃ B⊆(ball D A u k).erase u,
      Minimal D A B d ∧ q*(1+(boundary D V A \ image D V B).card)+1≤B.card := by
  let b := (boundary D V A).card
  let d := s-b
  have paid : A.card+q*b≤q*s := T.paid
  have kpos := Finset.card_pos.mpr T.nonempty
  have bs : b<s := by
    by_contra! large
    have := Nat.mul_le_mul_left q large
    omega
  have db : d+b=s := by dsimp [d]; omega
  have scale := congrArg (fun j : ℕ => q*j) db
  simp only [Nat.mul_add] at scale
  have lower (x) (hx : x∈A) : d≤(outN D A x).card := by
    have inc : outN D V x⊆outN D A x∪boundary D V A := by
      intro y hy; by_cases inside : y∈A
      · exact Finset.mem_union_left _ (mem_outN.mpr ⟨inside,(mem_outN.mp hy).2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨x,hx,hy⟩,inside⟩)
    have limit := (hm x (T.inside hx)).trans ((Finset.card_le_card inc).trans (Finset.card_union_le _ _))
    change s≤_+b at limit
    omega
  have inner := hf.mono_set T.inside
  have order : A.card≤q*d := by omega
  obtain ⟨u,hu,k,rad,B,sub,M⟩ := half_ball_cut inner hq lower T.nonempty order
  have gap : (boundary D A B).card+1=d := boundary_size M inner (by omega) lower
  have diff : B≠A := by
    intro eq; have hb : u∈B := eq ▸ hu
    exact (Finset.mem_erase.mp (sub hb)).1 rfl
  have no := T.stopped B M.inside M.nonempty diff
  dsimp [affordable] at no
  have cost := congrArg (fun j : ℕ => q*j) (transition_count (D:=D) T.inside M.inside)
  simp only [Nat.mul_add] at cost
  have fresh := congrArg (fun j : ℕ => q*j) gap
  simp only [Nat.mul_add,Nat.mul_one] at fresh
  have dp : 0<d := by omega
  refine ⟨dp,order,u,hu,k,rad,B,sub,M,?_⟩
  change q*(1+_)+1≤B.card
  rw [Nat.mul_add,Nat.mul_one]
  dsimp only [b] at *
  omega

/-- A distribution of proposals can certify a successful transition. Every
positive-weight child must be proper and nonempty; states of size zero
cannot make the averaged cost appear affordable. -/
theorem affordable_of_average {D : CH.Digraph} {V A : Finset ℕ} {q s}
    (options : Finset (Finset ℕ)) (weight : Finset ℕ → ℕ)
    (positive : 0<∑ B∈options,weight B)
    (valid : ∀ B∈options,0<weight B → B⊆A ∧ B.Nonempty ∧ B≠A)
    (budget : (∑ B∈options,weight B*(B.card+q*(boundary D V B).card))≤
      (∑ B∈options,weight B)*(q*s)) :
    ∃ B∈options,0<weight B ∧ B⊆A ∧ B.Nonempty ∧ B≠A ∧ affordable D V q s B := by
  by_contra! none
  have row (B) (hb : B∈options) :
      weight B*(q*s+1)≤weight B*(B.card+q*(boundary D V B).card) := by
    by_cases zero : weight B=0
    · simp [zero]
    have p : 0<weight B := by omega
    obtain ⟨ba,bn,proper⟩ := valid B hb p
    have fail := none B hb p ba bn proper
    dsimp [affordable] at fail
    exact Nat.mul_le_mul_left _ (by omega)
  have sum := (Finset.sum_le_sum row).trans budget
  rw [← Finset.sum_mul,Nat.mul_add,Nat.mul_one] at sum
  omega

#print axioms Terminal.second_cut
#print axioms affordable_of_average

end LeanCH.BR.ShenReturnCut
