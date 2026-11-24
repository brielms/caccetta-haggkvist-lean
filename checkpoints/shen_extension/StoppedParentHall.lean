import checkpoints.shen_extension.SlackBoundaryBanks

namespace LeanCH.BR.Closure.StoppedParentHall
open Finset BRq2 BRq3 BR45 WeightedSD

/-- A walk may enter a parent of y, but cannot then leave it. -/
def stopped (E : CH.Digraph) (y : ℕ) : CH.Digraph := fun i j => E i j && !(E i y)

noncomputable def ancestors (E : CH.Digraph) (V : Finset ℕ) (y : ℕ) (K : Finset ℕ) : Finset ℕ := by
  classical
  exact (V.erase y).filter (fun i => ∃ k∈K,∃ n,Walk (stopped E y) (V.erase y) i k n)

/-- Every target set has enough heads able to reach it before leaving a
parent of the root. The bound even pays for their entire ancestor set.
The excess over target demand is strict on every nonempty proper target set. -/
theorem capacity {q E V z} {c : ℝ} (hq : 2≤q) (high : 1<c) (small : SmallerSmallRow q V.card)
    (free : QFree E V q) (unit : realMass V z=1) (pos : ∀i∈V,0<z i)
    (rows : ∀i∈V,realRow q E V z i=c) {y} (yv : y∈V)
    {K : Finset ℕ} (ks : K⊆V.erase y) (kn : K.Nonempty) :
    let H := ancestors E V y K
    realMass H z+(c-1)≤(q:ℝ)*realOutW E H z y ∧
      (K≠V.erase y → realMass K z+(c-1)<(q:ℝ)*realOutW E H z y) := by
  classical
  intro H
  let U := V.erase y
  let J := U\H
  have hs : H⊆U := filter_subset _ _
  have kh : K⊆H := fun k hk => mem_filter.mpr ⟨ks hk,k,hk,0,.refl k⟩
  have js : J⊆U := sdiff_subset
  have uv : U⊆V := erase_subset _ _
  have hnv := kn.mono kh
  have dj : Disjoint H J := disjoint_sdiff
  have hu : H∪J=U := union_sdiff_of_subset hs
  have jq : J⊂U := Finset.ssubset_iff_subset_ne.mpr ⟨js,fun e => by
    obtain ⟨v,vh⟩ := hnv
    exact (mem_sdiff.mp (show v∈J from e.symm ▸ hs vh)).2 vh⟩
  have cardU : U.card+1=V.card := card_erase_add_one yv
  have room : J.card+1<V.card := by have := card_lt_card jq; omega
  have part : J⊂V := Finset.ssubset_iff_subset_ne.mpr ⟨js.trans uv,fun e => by
    have sz := congrArg Finset.card e
    omega⟩
  have yj : y∉J := fun h => (mem_erase.mp (js h)).1 rfl
  have cut (i) (hi : i∈J) (x) (hx : x∈V\J) (edge : E i x=true) : E i y=true := by
    by_contra no
    have xy : x≠y := fun eq => no (eq ▸ edge)
    have xu : x∈U := mem_erase.mpr ⟨xy,(mem_sdiff.mp hx).1⟩
    have xh : x∈H := by_contra fun h => (mem_sdiff.mp hx).2 (mem_sdiff.mpr ⟨xu,h⟩)
    obtain ⟨_,k,hk,n,walk⟩ := mem_filter.mp xh
    have st : stopped E y i x=true := by cases e : E i y <;> simp_all [stopped]
    exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨js hi,k,hk,n+1,.step xu st walk⟩)
  have bd := SlackBoundaryBanks.fold_bound high.le hq small free (Subset.rfl : V⊆V)
    unit pos rows part yv yj room cut
  have um : realMass H z+realMass J z+z y=1 := by
    rw [←unit,realMass,realMass,←sum_union dj,hu]
    exact sum_erase_add V z yv
  have loop : E y y=false := by
    cases h : E y y
    · rfl
    · exact (free y 1 (by omega) (by omega) (.step yv h (.refl y))).elim
  have disp : realOutW E V z y=realOutW E H z y+realOutW E J z y := by
    unfold realOutW
    rw [←sum_union dj,hu]
    have e := sum_erase_add V (fun i => if E y i=true then z i else 0) yv
    simpa [loop,U] using e.symm
  have total := rows y yv
  rw [realRow,disp,mul_add] at total
  constructor
  · linarith [bd.1]
  · intro properK
    by_cases live : J.Nonempty
    · have strict := lt_of_le_of_ne bd.1 (fun eq => high.ne' ((bd.2 eq).1 live))
      have lower : realMass K z≤realMass H z := sum_le_sum_of_subset_of_nonneg kh (fun i hi _ => (pos i (uv (hs hi))).le)
      linarith
    · have he : H=U := by simpa [not_nonempty_iff_eq_empty.mp live] using hu
      have properKH : K⊂H := Finset.ssubset_iff_subset_ne.mpr ⟨kh,fun eq => properK (eq.trans he)⟩
      obtain ⟨a,ah,ak⟩ := exists_of_ssubset properKH
      have lower : realMass K z≤∑i∈H.erase a,z i := sum_le_sum_of_subset_of_nonneg
        (fun i hi => mem_erase.mpr ⟨fun e => ak (e ▸ hi),kh hi⟩)
        (fun i hi _ => (pos i (uv (hs (mem_erase.mp hi).2))).le)
      have e := sum_erase_add H z ah
      change _=realMass H z at e
      linarith [pos a (uv (hs ah)),bd.1]

#print axioms capacity
end LeanCH.BR.Closure.StoppedParentHall
