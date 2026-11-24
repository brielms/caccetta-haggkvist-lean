import checkpoints.shen_extension.SaturatedCycleClasses
import checkpoints.shen_extension.ParentIntersection

namespace LeanCH.BR.Closure.ShortestCycleWeights
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenParentIntersection SaturatedCycleClasses

structure Model (q budget : ℕ) where
  D : CH.Digraph
  V : Finset ℕ
  live : V.Nonempty
  free : QFree D V q
  sat : BRsub.Sat q D V
  weights : ℕ→ℕ
  positive : ∀x∈V,0<weights x
  bounded : (∑x∈V, weights x)≤budget
  strict : Strict q D V weights
  minimal : ∀ (F : CH.Digraph) (U : Finset ℕ) (v : ℕ→ℕ), U.Nonempty → QFree F U q →
    (∀x∈U,0<v x) → (∑x∈U,v x)≤budget → Strict q F U v → V.card≤U.card
  prime : Prime D V
  separated : Separated D V V

/-- Choose the smallest support among all strict integral countermodels of
bounded mass. Saturating the arcs and resolving a module both preserve the
mass budget, so saturation, primeness and separation hold on the same labels. -/
theorem normalize {q n s D} (hq : 2≤q) (hn : 0<n) (ord : n≤q*s) (loop : CH.Loopless D n)
    (deg : CH.MinOutdegreeAtLeast D n s) (no : ¬CH.HasDirectedCycleAtMost D n q) :
    Nonempty (Model q n) := by
  classical
  let Good (k : ℕ) := ∃ (G : CH.Digraph) (U : Finset ℕ) (w : ℕ→ℕ),
    U.card=k ∧ U.Nonempty ∧ QFree G U q ∧ (∀x∈U,0<w x) ∧ (∑x∈U,w x)≤n ∧ Strict q G U w
  obtain ⟨I⟩ := of_input hn ord loop deg
  have ex : ∃k,Good k := ⟨_,D,I.carrier,I.weights,rfl,I.nonempty,
    (qfree_of_noShort loop no).mono_set I.subset,I.positive,I.bounded,I.strict⟩
  obtain ⟨G,U,w,size,live,safe,pos,bound,strict⟩ := Nat.find_spec ex
  obtain ⟨E,extE,ef,sat⟩ := BRsub.exists_satQ safe
  have full : Strict q E U w := by
    apply nat_strict.mpr
    intro x hx
    apply (nat_strict.mp strict x hx).trans_le
    unfold score
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply sum_le_sum
    intro y hy
    by_cases hit : G x y=true
    · simp [hit,extE x hx y hy hit]
    · simp [hit]
  obtain ⟨A⟩ := prime_descent (fun x hx => Bool.eq_false_iff.mpr (loopfree ef (by omega) hx))
    live pos full
  have mincard {F W v} (hne : W.Nonempty) (hf : QFree F W q) (hp : ∀x∈W,0<v x)
      (hb : (∑x∈W,v x)≤n) (hs : Strict q F W v) : U.card≤W.card :=
    size ▸ Nat.find_min' ex (show Good W.card from ⟨F,W,v,rfl,hne,hf,hp,hb,hs⟩)
  have eq := eq_of_subset_of_card_le A.subset
    (mincard A.nonempty (ef.mono_set A.subset) A.positive (A.bounded.trans bound) A.strict)
  have rigid : Rigid A := by
    intro W sub wl v vp vs vm
    rw [eq]
    exact mincard wl (ef.mono_set sub) vp (vm.trans (A.bounded.trans bound)) vs
  exact ⟨⟨E,U,live,ef,sat,w,pos,bound,full,fun _ _ _ => mincard,eq ▸ A.prime,eq ▸ ShenParentIntersection.separated rigid⟩⟩

/-- In the normalized model every actual arc lies on an induced shortest cycle. -/
theorem edge_cycle {q n} (A : Model q n) (hq : 2≤q) {x y} (xv : x∈A.V)
    (yv : y∈A.V) (xy : A.D x y=true) :
    ∃M,ShenCycleSuccessor.Cycle A.D A.V q M ∧ x∈M ∧ y∈M := by
  have ne : y≠x := by rintro rfl; exact loopfree A.free (by omega) xv xy
  obtain ⟨p,pv,px,py⟩ := A.separated x xv y yv ne
  obtain ⟨M,c,_,xm,ym⟩ := missing hq A.free A.sat pv xv yv px xy (by simp [py])
  exact ⟨M,c,xm,ym⟩

/-- When q=3 every distinct pair, including the nonadjacent pairs, lies on
an induced directed four-cycle. The witness is in the normalized support. -/
theorem pair_four {n} (A : Model 3 n) {x y} (xv : x∈A.V) (yv : y∈A.V) (ne : x≠y) :
    ∃M,ShenCycleSuccessor.Cycle A.D A.V 3 M ∧ x∈M ∧ y∈M := by
  by_cases xy : A.D x y=true
  · exact edge_cycle A (by decide) xv yv xy
  by_cases yx : A.D y x=true
  · obtain ⟨M,c,ym,xm⟩ := edge_cycle A (by decide) yv xv yx
    exact ⟨M,c,xm,ym⟩
  obtain ⟨_,k,le,path⟩ := mem_ball.mp (A.sat x xv y yv yx)
  have len : k=2 := by
    cases path with
    | refl => contradiction
    | step zv xz tail =>
      cases tail with
      | refl => contradiction
      | step => omega
  subst k
  obtain ⟨z,first,_,zy⟩ := path.unsnoc
  cases first with
  | step zv xz tail =>
    cases tail
    obtain ⟨M,c,xm,_,ym⟩ := missing (by decide) A.free A.sat xv zv yv xz zy xy
    exact ⟨M,c,xm,ym⟩

#print axioms normalize
#print axioms edge_cycle
#print axioms pair_four
end LeanCH.BR.Closure.ShortestCycleWeights
