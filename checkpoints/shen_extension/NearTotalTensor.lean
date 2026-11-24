import checkpoints.shen_extension.CommonSuccessorTensor

namespace LeanCH.BR.ShenNearTotal
open BRq2 BRq3 BR45 BRsGen ShenFirstStrip
open Classical

/-- Distinct vertices incomparable with x in the indicated directed relation. -/
def missing (F : CH.Digraph) (A : Finset ℕ) (x : ℕ) :=
  A.filter (fun y => y≠x ∧ F x y≠true ∧ F y x≠true)

private theorem partition_bound (F : CH.Digraph) {A W : Finset ℕ} (sub : W⊆A) (x : ℕ) :
    W.card≤1+(outN F W x).card+(inN F W x).card+(missing F A x).card := by
  have h : W ⊆ insert x ((outN F W x ∪ inN F W x) ∪ missing F A x) := by
    intro y hy
    by_cases he : y=x
    · exact Finset.mem_insert.mpr (Or.inl he)
    by_cases hf : F x y=true
    · simp [he,outN,hy,hf]
    by_cases hb : F y x=true
    · simp [he,inN,hy,hb]
    simp [he,missing,sub hy,hf,hb]
  have := Finset.card_le_card h
  have := Finset.card_insert_le x ((outN F W x ∪ inN F W x) ∪ missing F A x)
  have := Finset.card_union_le (outN F W x ∪ inN F W x) (missing F A x)
  have := Finset.card_union_le (outN F W x) (inN F W x)
  omega

private theorem source_bound {F : CH.Digraph} {A : Finset ℕ} {d : ℕ} (ne : A.Nonempty)
    (two : ∀ x∈A, ∀ y∈A, F x y=true → F y x≠true)
    (three : ∀ x∈A, ∀ y∈A, ∀ z∈A, F x y=true → F y z=true → F z x≠true)
    (hm : ∀ x∈A, (missing F A x).card≤d) :
    ∃ x∈A, (inN F A x).card≤3*d+1 := by
  obtain ⟨x,hx,hmax⟩ := A.exists_max_image (fun z => (outN F A z).card) ne
  let I := inN F A x
  have hIA : I⊆A := Finset.filter_subset _ _
  refine ⟨x,hx,?_⟩
  change I.card≤3*d+1
  have deg (y) (hy : y∈I) : (outN F I y).card≤d := by
    have hyx := (mem_inN.mp hy).2
    have dis : Disjoint (outN F A x) (outN F I y) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact two x hx z (mem_outN.mp hz).1 (mem_outN.mp hz).2
        (mem_inN.mp (mem_outN.mp hz').1).2
    have sub : outN F A x ∪ outN F I y ⊆ outN F A y ∪ missing F A y := by
      intro z hz
      rcases Finset.mem_union.mp hz with h|h
      · obtain ⟨hzA,hxz⟩ := mem_outN.mp h
        by_cases hyz : F y z=true
        · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hzA,hyz⟩)
        have hne : z≠y := by rintro rfl; exact two x hx z hzA hxz hyx
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hzA,hne,hyz,three y (hIA hy) x hx z hzA hyx hxz⟩)
      · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hIA (mem_outN.mp h).1,(mem_outN.mp h).2⟩)
    have hc := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
    rw [Finset.card_union_of_disjoint dis] at hc
    have := hmax y (hIA hy)
    have := hm y (hIA hy)
    omega
  by_contra! bad
  have low (y) (hy : y∈I) : d+1≤(inN F I y).card := by
    have := partition_bound F hIA y
    have := deg y hy
    have := hm y (hIA hy)
    omega
  have he : ∑ y∈I, (outN F I y).card = ∑ y∈I, (inN F I y).card :=
    Compose.ThinRigid.sum_out_eq_sum_in F I
  have hi := Finset.sum_le_sum low
  have ho := Finset.sum_le_sum deg
  simp only [Finset.sum_const] at hi ho
  change I.card*(d+1)≤_ at hi
  change _≤I.card*d at ho
  rw [Nat.mul_add,Nat.mul_one] at hi
  omega

/-- A bank of close labelled reach rows forces a root with many
incomparable partners. The pairwise totality hypothesis is replaced by a
per-root allowance of d incomparable partners. -/
theorem row_capacity {D : CH.Digraph} {A V : Finset ℕ} {q l e d : ℕ}
    (hf : QFree D V q) (sub : A⊆V) (ne : A.Nonempty)
    (hr : l+e+1≤q) (htri : 3*e≤q)
    (diff : ∀ x∈A, ∀ y∈A, (ball D V x l \ ball D V y l).card≤e)
    (hm : ∀ x∈A, (A.filter (fun y => y∉ball D V x l ∧ x∉ball D V y l)).card≤d) :
    A.card≤e+7*d+4 := by
  let F : CH.Digraph := fun x y => decide (x≠y ∧ y∈ball D V x l)
  have small (x) (hx : x∈A) (y) (hy : y∈A) (w : F x y=true) :
      ∃ t, 0<t ∧ t≤e ∧ Walk D V x y t := by
    obtain ⟨hne,hb⟩ := of_decide_eq_true w
    obtain ⟨_,t,ht,p⟩ := mem_ball.mp hb
    refine ⟨t,?_,ShenContainerTransfer.walk_length_le_omissions hf (sub hx)
      (Finset.Subset.refl _) ht p hr (diff x hx y hy),p⟩
    cases t with
    | zero => cases p; exact (hne rfl).elim
    | succ t => omega
  have two (x) (hx : x∈A) (y) (hy : y∈A) (a : F x y=true) (b : F y x=true) : False := by
    obtain ⟨i,hi,hi',wi⟩ := small x hx y hy a
    obtain ⟨j,hj,hj',wj⟩ := small y hy x hx b
    exact hf x (i+j) (by omega) (by omega) (wi.append wj)
  have three (x) (hx : x∈A) (y) (hy : y∈A) (z) (hz : z∈A)
      (a : F x y=true) (b : F y z=true) (c : F z x=true) : False := by
    obtain ⟨i,hi,hi',wi⟩ := small x hx y hy a
    obtain ⟨j,hj,hj',wj⟩ := small y hy z hz b
    obtain ⟨k,hk,hk',wk⟩ := small z hz x hx c
    exact hf x (i+j+k) (by omega) (by omega) ((wi.append wj).append wk)
  have miss (x) (hx : x∈A) : (missing F A x).card≤d := by
    apply le_trans (Finset.card_le_card _) (hm x hx)
    intro y hy
    obtain ⟨hyA,hne,ha,hb⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hyA,fun h => ha (by simp [F,hne.symm,h]),
      fun h => hb (by simp [F,hne,h])⟩
  obtain ⟨x,hx,hsmall⟩ := source_bound ne two three miss
  let rev : CH.Digraph := fun x y => F y x
  have revmiss (z) (hz : z∈A) : (missing rev A z).card≤d := by
    simpa only [missing,rev,and_left_comm,and_comm,and_assoc] using miss z hz
  obtain ⟨z,hz,hzsmall⟩ := source_bound (F:=rev) ne
    (fun a ha b hb w => two b hb a ha w)
    (fun a ha b hb c hc w v => three c hc b hb a ha v w) revmiss
  change (outN F A z).card≤3*d+1 at hzsmall
  have cover : outN F A x ⊆ insert z ((ball D V x l \ ball D V z l) ∪ outN F A z) := by
    intro y hy
    obtain ⟨hyA,hedge⟩ := mem_outN.mp hy
    have hxy := (of_decide_eq_true hedge).2
    by_cases he : y=z
    · exact Finset.mem_insert.mpr (Or.inl he)
    by_cases hzy : y∈ball D V z l
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (mem_outN.mpr
        ⟨hyA,by simp [F,Ne.symm he,hzy]⟩))
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxy,hzy⟩))
  have := Finset.card_le_card cover
  have := Finset.card_insert_le z ((ball D V x l \ ball D V z l) ∪ outN F A z)
  have := Finset.card_union_le (ball D V x l \ ball D V z l) (outN F A z)
  have := diff x hx z hz
  have := partition_bound F (Finset.Subset.refl A) x
  have := miss x hx
  omega

#print axioms row_capacity

/-- Every threshold d gives a lower bound on the number of different
ordered incomparable pairs. The discarded roots each pay for their own row. -/
theorem incomparable_cells {D : CH.Digraph} {A V : Finset ℕ} {q l e : ℕ}
    (hf : QFree D V q) (sub : A⊆V) (hr : l+e+1≤q) (htri : 3*e≤q)
    (diff : ∀ x∈A, ∀ y∈A, (ball D V x l \ ball D V y l).card≤e) (d : ℕ) :
    (d+1)*(A.card-(e+7*d+4)) ≤
      ∑ x∈A, (A.filter (fun y => y∉ball D V x l ∧ x∉ball D V y l)).card := by
  let m := fun x => (A.filter (fun y => y∉ball D V x l ∧ x∉ball D V y l)).card
  let B := A.filter (fun x => m x≤d)
  have subB : B⊆A := Finset.filter_subset _ _
  have hb : B.card≤e+7*d+4 := by
    rcases B.eq_empty_or_nonempty with hz|hn
    · simp [hz]
    apply row_capacity hf (subB.trans sub) hn hr htri (fun x hx y hy => diff x (subB hx) y (subB hy))
    intro x hx
    exact (Finset.card_le_card (Finset.filter_subset_filter _ subB)).trans (Finset.mem_filter.mp hx).2
  have he := Finset.card_sdiff_add_card_eq_card subB
  have high (x) (hx : x∈A \ B) : d+1≤m x := by
    obtain ⟨ha,hn⟩ := Finset.mem_sdiff.mp hx
    by_contra! bad
    exact hn (Finset.mem_filter.mpr ⟨ha,by omega⟩)
  have count := Finset.sum_le_sum high
  rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm] at count
  exact ((Nat.mul_le_mul_left (d+1) (show A.card-(e+7*d+4)≤(A \ B).card by omega)).trans count).trans
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.zero_le _))

/-- Couple the selected rows to Shen's complementary-ball budget. A
double failure at radius l consumes a distinct complementary tensor cell. -/
theorem near_total_capacity {D : CH.Digraph} {A V : Finset ℕ} {q i j l e : ℕ}
    (hf : QFree D V q) (sub : A⊆V) (hpair : i+j≤q) (hi : i≤l) (hj : j≤l)
    (hr : l+e+1≤q) (htri : 3*e≤q)
    (diff : ∀ x∈A, ∀ y∈A, (ball D V x l \ ball D V y l).card≤e) (d : ℕ) :
    (d+1)*(A.card-(e+7*d+4)) + (∑ x∈V, (ball D V x i).card) +
      (∑ x∈V, (ball D V x j).card) ≤ V.card*(V.card+1) := by
  let M := fun x => (V \ (ball D V x i ∪ reverseBall D V x j)).card
  have cells (x) (_hx : x∈A) :
      (A.filter (fun y => y∉ball D V x l ∧ x∉ball D V y l)).card≤M x := by
    apply Finset.card_le_card
    intro y hy
    obtain ⟨hyA,hout,hback⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_sdiff.mpr ⟨sub hyA,?_⟩
    intro hz
    rcases Finset.mem_union.mp hz with h|h
    · exact hout (ball_mono_radius hi h)
    · exact hback (ball_mono_radius hj (Finset.mem_filter.mp h).2)
  have h := (incomparable_cells hf sub hr htri diff d).trans (Finset.sum_le_sum cells)
  have h' := h.trans (Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _))
  dsimp only [M] at h'
  have cap := tensor_capacity_identity hf hpair
  omega

#print axioms incomparable_cells
#print axioms near_total_capacity

/-- Ordered pairs paying for a bank, with their two original vertex labels. -/
noncomputable def incomparablePairs (D : CH.Digraph) (V A : Finset ℕ) (l : ℕ) :=
  (A.product A).filter (fun p => p.2∉ball D V p.1 l ∧ p.1∉ball D V p.2 l)

private theorem pair_card (D : CH.Digraph) (V A : Finset ℕ) (l : ℕ) :
    (incomparablePairs D V A l).card =
      ∑ x∈A, (A.filter (fun y => y∉ball D V x l ∧ x∉ball D V y l)).card := by
  simp only [incomparablePairs,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_product A A (fun p => if p.2∉ball D V p.1 l ∧ p.1∉ball D V p.2 l then 1 else 0)

/-- Sum the obstruction over arbitrary banks, controlling reuse at the
actual ordered pair of vertices. Radii are common across the banks, while
private-row thresholds and trimming thresholds may vary from bank to bank. -/
theorem bank_incidence {D : CH.Digraph} {V U : Finset ℕ} {q l : ℕ}
    (A : ℕ → Finset ℕ) (e d : ℕ → ℕ)
    (hf : QFree D V q) (sub : ∀ u∈U, A u⊆V)
    (hr : ∀ u∈U, l+e u+1≤q) (tri : ∀ u∈U, 3*e u≤q)
    (diff : ∀ u∈U, ∀ x∈A u, ∀ y∈A u, (ball D V x l \ ball D V y l).card≤e u) :
    (∑ u∈U, (d u+1)*((A u).card-(e u+7*d u+4))) ≤
      ∑ p∈incomparablePairs D V V l, (U.filter (fun u => p.1∈A u ∧ p.2∈A u)).card := by
  let P := incomparablePairs D V V l
  let bank := fun u => incomparablePairs D V (A u) l
  have hsub (u) (hu : u∈U) : bank u⊆P := by
    intro p hp
    obtain ⟨hmem,hreach⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hmem
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨sub u hu hx,sub u hu hy⟩,hreach⟩
  have row (u) (hu : u∈U) : (d u+1)*((A u).card-(e u+7*d u+4))≤
      ∑ p∈P, (if p∈bank u then 1 else 0) := by
    have eq : P.filter (fun p => p∈bank u) = bank u := by
      ext p
      exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨hsub u hu h,h⟩⟩
    have hc := congrArg Finset.card eq
    rw [Finset.card_eq_sum_ones,Finset.sum_filter] at hc
    rw [hc]
    exact (incomparable_cells hf (sub u hu) (hr u hu) (tri u hu) (diff u hu) (d u)).trans_eq
      (pair_card D V (A u) l).symm
  have col (p : ℕ × ℕ) (_hp : p∈P) : (∑ u∈U, (if p∈bank u then 1 else 0))≤
      (U.filter (fun u => p.1∈A u ∧ p.2∈A u)).card := by
    have h : U.filter (fun u => p∈bank u) ⊆ U.filter (fun u => p.1∈A u ∧ p.2∈A u) := by
      intro u hu
      obtain ⟨hu,hb⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨hu,Finset.mem_product.mp (Finset.mem_filter.mp hb).1⟩
    have hc := Finset.card_le_card h
    conv at hc => lhs; rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    exact hc
  calc
    _ ≤ ∑ u∈U, ∑ p∈P, (if p∈bank u then 1 else 0) := Finset.sum_le_sum row
    _ = ∑ p∈P, ∑ u∈U, (if p∈bank u then 1 else 0) := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum col

/-- Supply a uniform reuse bound when geometry gives one. -/
theorem bank_packing {D : CH.Digraph} {V U : Finset ℕ} {q l m : ℕ}
    (A : ℕ → Finset ℕ) (e d : ℕ → ℕ)
    (hf : QFree D V q) (sub : ∀ u∈U, A u⊆V)
    (hr : ∀ u∈U, l+e u+1≤q) (tri : ∀ u∈U, 3*e u≤q)
    (diff : ∀ u∈U, ∀ x∈A u, ∀ y∈A u, (ball D V x l \ ball D V y l).card≤e u)
    (reuse : ∀ p∈incomparablePairs D V V l, (U.filter (fun u => p.1∈A u ∧ p.2∈A u)).card≤m) :
    (∑ u∈U, (d u+1)*((A u).card-(e u+7*d u+4))) ≤ m*(incomparablePairs D V V l).card := by
  have h := (bank_incidence A e d hf sub hr tri diff).trans (Finset.sum_le_sum reuse)
  rwa [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm] at h

/-- For rows selected from exact forward layers, measure reuse on each
incomparable pair by intersecting its two actual backward layers. -/
theorem layer_pair_budget {D : CH.Digraph} {V U : Finset ℕ} {q k l : ℕ}
    (A : ℕ → Finset ℕ) (e d : ℕ → ℕ) (hf : QFree D V q) (hUV : U⊆V)
    (layer : ∀ u∈U, A u⊆ball D V u (k+1) \ ball D V u k)
    (hr : ∀ u∈U, l+e u+1≤q) (tri : ∀ u∈U, 3*e u≤q)
    (diff : ∀ u∈U, ∀ x∈A u, ∀ y∈A u, (ball D V x l \ ball D V y l).card≤e u) :
    (∑ u∈U, (d u+1)*((A u).card-(e u+7*d u+4))) ≤
      ∑ p∈incomparablePairs D V V l,
        ((reverseBall D V p.1 (k+1) \ reverseBall D V p.1 k) ∩
         (reverseBall D V p.2 (k+1) \ reverseBall D V p.2 k)).card := by
  have sub (u) (hu : u∈U) : A u⊆V := (layer u hu).trans (Finset.sdiff_subset.trans ball_subset)
  apply (bank_incidence A e d hf sub hr tri diff).trans
  apply Finset.sum_le_sum
  intro p _
  apply Finset.card_le_card
  intro u hu
  obtain ⟨hu,hx,hy⟩ := Finset.mem_filter.mp hu
  have back (v) (hv : v∈A u) : u∈reverseBall D V v (k+1) \ reverseBall D V v k := by
    obtain ⟨ho,hi⟩ := Finset.mem_sdiff.mp (layer u hu hv)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hUV hu,ho⟩,
      fun h => hi (Finset.mem_filter.mp h).2⟩
  exact Finset.mem_inter.mpr ⟨back _ hx,back _ hy⟩

#print axioms bank_packing
#print axioms bank_incidence
#print axioms layer_pair_budget

/-- A complementary-ball budget for the global pair set in bank_packing. -/
theorem pair_budget {D : CH.Digraph} {V : Finset ℕ} {q i j l : ℕ}
    (hf : QFree D V q) (hp : i+j≤q) (hi : i≤l) (hj : j≤l) :
    (incomparablePairs D V V l).card + (∑ x∈V, (ball D V x i).card) +
      (∑ x∈V, (ball D V x j).card) ≤ V.card*(V.card+1) := by
  rw [pair_card]
  have row (x) (_hx : x∈V) : (V.filter (fun y => y∉ball D V x l ∧ x∉ball D V y l)).card
      ≤ (V \ (ball D V x i ∪ reverseBall D V x j)).card := by
    apply Finset.card_le_card
    intro y hy
    obtain ⟨hyV,ha,hb⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_sdiff.mpr ⟨hyV, fun h => (Finset.mem_union.mp h).elim
      (fun w => ha (ball_mono_radius hi w)) (fun w => hb (ball_mono_radius hj (Finset.mem_filter.mp w).2))⟩
  have := Finset.sum_le_sum row
  have := tensor_capacity_identity hf hp
  omega

#print axioms pair_budget

/-- A family whose forced pair count exceeds its share of Shen's slack
excludes the host at any cutoff. All balls and all banks lie on one graph. -/
theorem packing_budget {D : CH.Digraph} {V U : Finset ℕ} {q i j l m : ℕ}
    (A : ℕ → Finset ℕ) (e d : ℕ → ℕ) (hf : QFree D V q)
    (hp : i+j≤q) (hi : i≤l) (hj : j≤l) (sub : ∀ u∈U, A u⊆V)
    (hr : ∀ u∈U, l+e u+1≤q) (tri : ∀ u∈U, 3*e u≤q)
    (diff : ∀ u∈U, ∀ x∈A u, ∀ y∈A u, (ball D V x l \ ball D V y l).card≤e u)
    (reuse : ∀ p∈incomparablePairs D V V l, (U.filter (fun u => p.1∈A u ∧ p.2∈A u)).card≤m) :
    (∑ u∈U, (d u+1)*((A u).card-(e u+7*d u+4))) ≤
      m*(V.card*(V.card+1)-((∑ x∈V, (ball D V x i).card)+(∑ x∈V, (ball D V x j).card))) := by
  have cap := pair_budget hf hp hi hj
  exact (bank_packing A e d hf sub hr tri diff reuse).trans (Nat.mul_le_mul_left m (by omega))

#print axioms packing_budget
end LeanCH.BR.ShenNearTotal
