import checkpoints.shen_extension.OneSpareTurns

namespace LeanCH.BR.OneSpareGrowth
open Finset BRq2 BRq3 BR45 BRsGen DotClonePairCompletion

/-- Counting distinct ordered collisions. Two different copies of a vertex
cannot be used as the same ordered pair. -/
theorem collision_budget {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α→β) (S : Finset α) :
    2*S.card ≤ (S.offDiag.filter (fun e=>f e.1=f e.2)).card+2*(S.image f).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S fresh ih =>
    let A := S.offDiag.filter (fun e=>f e.1=f e.2)
    let B := (insert a S).offDiag.filter (fun e=>f e.1=f e.2)
    have inc : A⊆B := by
      intro e em
      obtain ⟨od,same⟩ := mem_filter.mp em
      obtain ⟨p,t,ne⟩ := mem_offDiag.mp od
      exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_insert_of_mem p,mem_insert_of_mem t,ne⟩,same⟩
    change 2*(insert a S).card≤B.card+2*((insert a S).image f).card
    change 2*S.card≤A.card+2*(S.image f).card at ih
    rw [card_insert_of_notMem fresh,image_insert]
    by_cases old : f a∈S.image f
    · rw [insert_eq_of_mem old]
      obtain ⟨b,bs,eq⟩ := mem_image.mp old
      have ne : a≠b := fun s=>fresh (s.symm ▸ bs)
      have ab : (a,b)∈B := mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_insert_self _ _,mem_insert_of_mem bs,ne⟩,eq.symm⟩
      have ba : (b,a)∈B := mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_insert_of_mem bs,mem_insert_self _ _,ne.symm⟩,eq⟩
      have off : (a,b)∉A := fun h=>fresh (mem_offDiag.mp (mem_filter.mp h).1).1
      have off' : (b,a)∉insert (a,b) A := by
        intro h
        rcases mem_insert.mp h with h|h
        · exact ne ((congrArg Prod.fst h).symm)
        · exact fresh (mem_offDiag.mp (mem_filter.mp h).1).2.1
      have count := card_le_card (insert_subset ba (insert_subset ab inc))
      rw [card_insert_of_notMem off',card_insert_of_notMem off] at count
      omega
    · rw [card_insert_of_notMem old]
      have := card_le_card inc
      omega

/-- If two roots can use the same labelled row to cover their respective
second layers, its native heads put the entire second layer of one root
inside the other's two-layer carrier. A two-step reach would force a loop. -/
theorem shared_full_misses {D V q r u v w} (free : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (vv : v∈V) (ne : u≠v) (reg : OutEq r D V)
    (us : (N2 D V u).card+1=r) (vs : (N2 D V v).card+1=r)
    (wu : w∈outN D V u) (wv : w∈outN D V v)
    (coversU : ∀x∈N2 D V u,D w x=true) (coversV : ∀x∈N2 D V v,D w x=true) :
    v∉ball D V u 2 := by
  intro reach
  have f4 := free.mono_bound hq
  have outside : v∉N2 D V u := fun hit=>n2 f4 vv (outN_subset wv) (mem_outN.mp wv).2 (coversU v hit)
  have vx : v∈outN D V u := by
    by_contra miss
    exact outside (mem_sdiff.mpr ⟨reach,fun atOne=>((mem_ball_one uv).mp atOne).elim
      (fun eq=>ne eq.symm) miss⟩)
  let T := outN D V u ∪ N2 D V u
  have yv : N2 D V v⊆T := fun y ym=>headX f4 uv wu (N2_subV ym) (coversV y ym)
  have into : outN D V v⊆T\N2 D V v := by
    intro x xm
    exact mem_sdiff.mpr ⟨headX f4 uv vx (outN_subset xm) (mem_outN.mp xm).2,
      fun ym=>(mem_N2.mp ym).2 (X_B1 xm)⟩
  have tsize : T.card=r+(N2 D V u).card := by rw [show T=_ from rfl,card_union_of_disjoint disjXY,reg u uv]
  have eq := eq_of_subset_of_card_le into (by rw [card_sdiff_of_subset yv,tsize,reg v vv]; omega)
  have contained : v∈T\N2 D V v := mem_sdiff.mpr ⟨mem_union_left _ vx,fun m=>(mem_N2.mp m).2 (self_mem_ball vv)⟩
  exact n1 f4 vv (mem_outN.mp (eq.symm ▸ contained : v∈outN D V v)).2

#print axioms collision_budget
#print axioms shared_full_misses
end LeanCH.BR.OneSpareGrowth
