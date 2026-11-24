import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import LeanCH.BR.BR45Base
import checkpoints.shen_extension.dot_tensor_research.PhysicalBankRouting
import checkpoints.shen_extension.MandatoryExcursion
import checkpoints.shen_extension.FirstPacketBarrier

namespace LeanCH.BR.ExteriorPacking
open Finset
variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- Each nontrivial subfamily has an observation whose distinct observed labels
are inside their own members and outside all members with a different answer. -/
def Separates (F : Finset ι) (inside outside : ι→Finset α) : Prop :=
  ∀A⊆F,1<A.card → ∃f : ι→α, (∀i∈A,f i∈inside i) ∧
    (∀i∈A,∀j∈A,f j≠f i → f j∈outside i) ∧ ∃i∈A,∃j∈A,f i≠f j

private theorem power_floor (k : ℕ) : (1:ℚ)≤2^k := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; linarith

/-- Arbitrary prices on distinct labelled members. A binary split spends one
fresh physical exterior label on each branch. Common reservations are free. -/
theorem binary_packing {F : Finset ι} {inside outside : ι→Finset α}
    (sep : Separates F inside outside) (disj : ∀i∈F,Disjoint (inside i) (outside i)) :
    ∀{S : Finset α}, (∀i∈F,S⊆outside i) → ∀w : ι→ℚ, (∀i∈F,0≤w i) →
    (∀i∈F,w i*(2:ℚ)^((outside i\S).card)≤1) → ∑i∈F,w i≤1 := by
  classical
  suffices run : ∀A : Finset ι,A⊆F → ∀S : Finset α, (∀i∈A,S⊆outside i) →
      ∀w : ι→ℚ, (∀i∈A,0≤w i) → (∀i∈A,w i*(2:ℚ)^((outside i\S).card)≤1) → ∑i∈A,w i≤1 by
    intro S
    exact run F Subset.rfl S
  intro A
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    intro af S reserve w pos cap
    by_cases tiny : A.card≤1
    · rcases A.eq_empty_or_nonempty with eq|⟨i,im⟩
      · simp [eq]
      · have eq : A={i} := by
          ext j
          exact ⟨fun jm=>mem_singleton.mpr (card_le_one.mp tiny j jm i im),fun j=>(mem_singleton.mp j).symm ▸ im⟩
        rw [eq,sum_singleton]
        exact (show w i ≤ w i*2^((outside i\S).card) by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (power_floor _) (pos i im)).trans (cap i im)
    obtain ⟨f,inner,outer,i,im,j,jm,diff⟩ := sep A af (by omega)
    let B := A.filter (fun k=>f k=f i)
    let C := A.filter (fun k=>f k≠f i)
    have visit (K : Finset ι) (smaller : K⊂A) (x : α) (newX : x∉S)
        (spent : ∀k∈K,x∈outside k) : 2*(∑k∈K,w k)≤1 := by
      rw [mul_sum]
      apply ih K smaller (smaller.1.trans af) (insert x S)
        (fun k km=>insert_subset (spent k km) (reserve k (smaller.1 km)))
        (fun k=>2*w k) (fun k km=>mul_nonneg (by norm_num) (pos k (smaller.1 km)))
      intro k km
      have old := cap k (smaller.1 km)
      have xm : x∈outside k\S := mem_sdiff.mpr ⟨spent k km,newX⟩
      have erase : outside k\insert x S=(outside k\S).erase x := by
        ext y
        simp only [mem_sdiff,mem_insert,mem_erase]
        tauto
      have count : (outside k\insert x S).card+1=(outside k\S).card := by
        rw [erase,card_erase_of_mem xm]
        have := card_pos.mpr ⟨x,xm⟩
        omega
      rw [←count,pow_succ] at old
      linarith only [old]
    have left : B ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,fun eq=>
      diff ((mem_filter.mp (show j∈B from eq.symm ▸ jm)).2.symm)⟩
    have right : C ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,fun eq=>
      (mem_filter.mp (show i∈C from eq.symm ▸ im)).2 rfl⟩
    have newLabel k (km : k∈A) : f k∉S := fun mem=>
      (Finset.disjoint_left.mp (disj k (af km))) (inner k km) (reserve k km mem)
    have lb := visit B left (f j) (newLabel _ jm) (fun k km=>
      outer k (left.1 km) j jm (by rw [(mem_filter.mp km).2]; exact diff.symm))
    have rb := visit C right (f i) (newLabel _ im) (fun k km=>
      outer k (right.1 km) i im (Ne.symm (mem_filter.mp km).2))
    have apart : Disjoint B C := Finset.disjoint_left.mpr (fun _ bl cr=>(mem_filter.mp cr).2 (mem_filter.mp bl).2)
    have all : B∪C=A := by ext k; simp [B,C]; tauto
    have total : ∑i∈A,w i=(∑i∈B,w i)+(∑i∈C,w i) := by rw [←sum_union apart,all]
    linarith only [lb,rb,total]

theorem reciprocal_packing {F : Finset ι} {inside outside : ι→Finset α}
    (sep : Separates F inside outside) (disj : ∀i∈F,Disjoint (inside i) (outside i))
    {S : Finset α} (reserve : ∀i∈F,S⊆outside i) :
    (∑i∈F,(1:ℚ)/2^((outside i\S).card))≤1 := by
  apply binary_packing sep disj reserve _ (fun _ _=>by positivity)
  intro i _
  rw [div_mul_cancel₀ _ (by positivity)]

#print axioms binary_packing
#print axioms reciprocal_packing
end LeanCH.BR.ExteriorPacking

namespace LeanCH.BR.ExteriorPacking
open Finset
variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- A split with t physical answers reserves all t−1 alternatives in every child. -/
theorem fan_budget {F : Finset ι} {inside outside : ι→Finset α}
    (sep : Separates F inside outside) (disj : ∀i∈F,Disjoint (inside i) (outside i))
    {S : Finset α} (reserve : ∀i∈F,S⊆outside i)
    (f : ι→α) (seen : ∀i∈F,f i∈inside i)
    (alt : ∀i∈F,∀j∈F,f j≠f i → f j∈outside i)
    (w : ι→ℚ) (pos : ∀i∈F,0≤w i) (bill : ∀i∈F,w i*2^((outside i\S).card)≤1) :
    (2:ℚ)^((F.image f).card-1)*(∑i∈F,w i)≤((F.image f).card:ℚ) := by
  classical
  let T := F.image f
  let gain : ℚ := 2^(T.card-1)
  have powPos : 0≤gain := by dsimp [gain]; positivity
  have old : Disjoint S T := by
    apply disjoint_left.mpr
    intro x xs xt
    obtain ⟨i,im,rfl⟩ := mem_image.mp xt
    exact (disjoint_left.mp (disj i im)) (seen i im) (reserve i im xs)
  have per (y) (ym : y∈T) : (∑i∈F.filter (fun i=>f i=y),gain*w i)≤1 := by
    let G := F.filter (fun i=>f i=y)
    have sub : G⊆F := filter_subset _ _
    let R := S∪T.erase y
    have room (i) (im : i∈G) : R⊆outside i := by
      apply union_subset (reserve i (sub im))
      intro x xm
      obtain ⟨ne,xt⟩ := mem_erase.mp xm
      obtain ⟨j,jm,rfl⟩ := mem_image.mp xt
      exact alt i (sub im) j jm (by rw [(mem_filter.mp im).2]; exact ne)
    have dis : Disjoint S (T.erase y) := old.mono_right (erase_subset _ _)
    have rs : R.card=S.card+(T.card-1) := by
      rw [show R=S∪T.erase y by rfl,card_union_of_disjoint dis,card_erase_of_mem ym]
    apply binary_packing (F:=G) (inside:=inside) (outside:=outside)
      (fun A ag=>sep A (ag.trans sub)) (fun i im=>disj i (sub im)) room (fun i=>gain*w i)
      (fun i im=>mul_nonneg powPos (pos i (sub im)))
    intro i im
    have avail := card_le_card (room i im)
    have sizes : (outside i\R).card+(T.card-1)=(outside i\S).card := by
      rw [card_sdiff_of_subset (room i im),card_sdiff_of_subset (reserve i (sub im))]
      omega
    have leaf := bill i (sub im)
    rw [←sizes,pow_add] at leaf
    change 2^(T.card-1)*w i*2^_≤1
    linarith only [leaf]
  have maps (i) (im : i∈F) : f i∈T := mem_image_of_mem f im
  calc
    gain*(∑i∈F,w i) = ∑i∈F,gain*w i := mul_sum ..
    _ = ∑y∈T,∑i∈F.filter (fun i=>f i=y),gain*w i := (sum_fiberwise_of_maps_to maps _).symm
    _ ≤ ∑_y∈T,(1:ℚ) := sum_le_sum per
    _ = _ := by simp [T]

theorem three_way_slack {p : ℚ} {t : ℕ} (wide : 3≤t) (budget : (2:ℚ)^(t-1)*p≤t) : p<1 := by
  have power (k : ℕ) : (k+3:ℚ)<2^(k+2) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show k+1+2=(k+2)+1 by omega,pow_succ]
      push_cast
      linarith
  have size : t-3+3=t := by omega
  have lower := power (t-3)
  rw [show t-3+2=t-1 by omega] at lower
  have co : ((t-3:ℕ):ℚ)+3=t := by exact_mod_cast size
  by_contra! bad
  have nonneg : (0:ℚ)≤2^(t-1) := by positivity
  nlinarith only [co,lower,budget,mul_nonneg nonneg (sub_nonneg.mpr bad)]

#print axioms fan_budget
#print axioms three_way_slack
end LeanCH.BR.ExteriorPacking

namespace LeanCH.BR.ExteriorPacking
open Finset BRq2 BRq3 BR45

/-- Every physical nonsupport head of any row of C. -/
def exterior (D : CH.Digraph) (V C : Finset ℕ) :=
  (C.biUnion (fun a=>outN D V a))\C

/-- Rooted reachable labelled supports with exactly one internal head per row.
Different supports may have different sizes, including tails before a cycle. -/
structure Rooted (D : CH.Digraph) (V : Finset ℕ) (r : ℕ) (C : Finset ℕ) : Prop where
  sub : C⊆V
  root : r∈C
  one : ∀x∈C,(outN D C x).card=1
  reaches : ∀y∈C,∃k,Walk D C r y k

noncomputable def internalHead (D : CH.Digraph) (C : Finset ℕ) (x : ℕ) : ℕ :=
  if p : (outN D C x).Nonempty then (outN D C x).min' p else 0

private theorem chosen {D V r C x} (c : Rooted D V r C) (cx : x∈C) : internalHead D C x∈outN D C x := by
  have non : (outN D C x).Nonempty := card_pos.mp (by rw [c.one x cx]; decide)
  simpa only [internalHead,dite_eq_left non] using (outN D C x).min'_mem non

private theorem specified {D V r C x y} (c : Rooted D V r C) (cx : x∈C) (cy : y∈C) (xy : D x y=true) :
    y=internalHead D C x := card_le_one.mp (c.one x cx).le _ (mem_outN.mpr ⟨cy,xy⟩) _ (chosen c cx)

/-- If all shared rows gave the same internal successor, every walk from
the root would stay in the intersection and all supports would be equal. -/
theorem physical_split {D V r} {F : Finset (Finset ℕ)} (rooted : ∀C∈F,Rooted D V r C) : Separates F id (exterior D V) := by
  classical
  intro A af wide
  have split : ∃x, (∀C∈A,x∈C) ∧ ∃i∈A,∃j∈A,internalHead D i x≠internalHead D j x := by
    by_contra absent
    have equal {x} (common : ∀C∈A,x∈C) {i j} (im : i∈A) (jm : j∈A) : internalHead D i x=internalHead D j x :=
      Classical.byContradiction (fun ne=>absent ⟨x,common,i,im,j,jm,ne⟩)
    have carry {C} (cm : C∈A) {a b k} (w : Walk D C a b k) : (∀K∈A,a∈K)→∀K∈A,b∈K := by
      induction w with
      | refl => exact id
      | @step a y b k cy ay _ ih =>
        intro common
        apply ih
        intro K km
        have eq := (specified (rooted C (af cm)) (common C cm) cy ay).trans (equal common cm km)
        rw [eq]
        exact (mem_outN.mp (chosen (rooted K (af km)) (common K km))).1
    have sub {C K} (cm : C∈A) (km : K∈A) : C⊆K := by
      intro y ym
      obtain ⟨k,walk⟩ := (rooted C (af cm)).reaches y ym
      exact carry cm walk (fun i im=>(rooted i (af im)).root) K km
    exact (not_lt_of_ge (card_le_one.mpr (fun i im j jm=>Subset.antisymm (sub im jm) (sub jm im)))) wide
  obtain ⟨x,common,i,im,j,jm,ne⟩ := split
  refine ⟨fun C=>internalHead D C x,fun C cm=>(mem_outN.mp (chosen (rooted C (af cm)) (common C cm))).1,?_,i,im,j,jm,ne⟩
  intro C cm K km different
  obtain ⟨ky,edge⟩ := mem_outN.mp (chosen (rooted K (af km)) (common K km))
  exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x,common C cm,mem_outN.mpr ⟨(rooted K (af km)).sub ky,edge⟩⟩,
    fun cy=>different (specified (rooted C (af cm)) (common C cm) cy edge)⟩

private theorem turn_reserve {D V r u} {F : Finset (Finset ℕ)} (rooted : ∀C∈F,Rooted D V r C)
    (turn : ∀C∈F,u∈outN D C r) :
    ∀C∈F,(outN D V r).erase u⊆exterior D V C := by
  intro C cm v vm
  obtain ⟨ne,head⟩ := mem_erase.mp vm
  have c := rooted C cm
  exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨r,c.root,head⟩,fun vc=>ne
    (card_le_one.mp (c.one r c.root).le v (mem_outN.mpr ⟨vc,(mem_outN.mp head).2⟩) u (turn C cm))⟩

/-- Kraft bound for all distinct rooted supports on one physical turn, with
the exact per-support omissions beyond the other native heads of the root. -/
theorem turn_packing {D V r u} {F : Finset (Finset ℕ)} (rooted : ∀C∈F,Rooted D V r C) (turn : ∀C∈F,u∈outN D C r) :
    (∑C∈F,(1:ℚ)/2^((exterior D V C\(outN D V r).erase u).card))≤1 :=
  reciprocal_packing (physical_split rooted)
    (fun _ _=>disjoint_left.mpr (fun _ cm ex=>(mem_sdiff.mp ex).2 cm)) (turn_reserve rooted turn)

/-- All supports can share any reserved set of exterior labels. -/
theorem reserve_multiplicity {D V r k} {F : Finset (Finset ℕ)} {S : Finset ℕ}
    (rooted : ∀C∈F,Rooted D V r C) (reserve : ∀C∈F,S⊆exterior D V C)
    (omission : ∀C∈F,(exterior D V C\S).card≤k) : F.card≤2^k := by
  classical
  let w : Finset ℕ→ℚ := fun _=>1/(2:ℚ)^k
  have parts := binary_packing (physical_split rooted)
    (fun _ _=>disjoint_left.mpr (fun _ cm ex=>(mem_sdiff.mp ex).2 cm)) reserve w
    (fun _ _=>by dsimp [w]; positivity) (fun C cm=>by
      change (1/(2:ℚ)^k)*2^_≤1
      rw [one_div,←div_eq_inv_mul]
      exact (div_le_one (by positivity)).mpr (pow_le_pow_right₀ (by norm_num) (omission C cm)))
  simp only [w,sum_const,nsmul_eq_mul,one_div] at parts
  have raw : (F.card:ℚ)≤(2:ℚ)^k := (div_le_one (by positivity)).mp (by simpa [div_eq_mul_inv] using parts)
  exact_mod_cast raw

/-- A physical turn used by cycles with at most k extra exterior labels occurs
in at most 2^k supports. -/
theorem turn_multiplicity {D V r u k} {F : Finset (Finset ℕ)} (rooted : ∀C∈F,Rooted D V r C)
    (turn : ∀C∈F,u∈outN D C r) (omission : ∀C∈F,(exterior D V C\(outN D V r).erase u).card≤k) :
    F.card≤2^k := reserve_multiplicity rooted (turn_reserve rooted turn) omission

/-- For native outdegree d at the root, its reserved set on a fixed turn
contains exactly d−1 physical labels. -/
theorem degree_turn_limit {D V r u d k} {F : Finset (Finset ℕ)}
    (rooted : ∀C∈F,Rooted D V r C) (turn : ∀C∈F,u∈outN D C r)
    (degree : (outN D V r).card=d) (outer : ∀C∈F,(exterior D V C).card≤d-1+k) : F.card≤2^k := by
  apply turn_multiplicity rooted turn
  intro C cm
  obtain ⟨uc,edge⟩ := mem_outN.mp (turn C cm)
  have uv : u∈outN D V r := mem_outN.mpr ⟨(rooted C cm).sub uc,edge⟩
  rw [card_sdiff_of_subset (turn_reserve rooted turn C cm),card_erase_of_mem uv,degree]
  have := outer C cm
  omega

/-- A set of physical root heads avoided by every support can pay the common
reservation even when no internal successor was selected in advance. -/
theorem bank_multiplicity {D V r k} {F : Finset (Finset ℕ)} {S : Finset ℕ}
    (rooted : ∀C∈F,Rooted D V r C) (heads : S⊆outN D V r)
    (away : ∀C∈F,Disjoint S C) (outer : ∀C∈F,(exterior D V C).card≤S.card+k) :
    F.card≤2^k := by
  have reserve (C) (cm : C∈F) : S⊆exterior D V C := fun y ym=>mem_sdiff.mpr
    ⟨mem_biUnion.mpr ⟨r,(rooted C cm).root,heads ym⟩,disjoint_left.mp (away C cm) ym⟩
  apply reserve_multiplicity rooted reserve
  intro C cm
  rw [card_sdiff_of_subset (reserve C cm)]
  have := outer C cm
  omega

/-- Collect every actual turn at a root. The normalized charge is bounded
by the exact number of distinct successor labels used there. -/
theorem root_packing {D V r} {F : Finset (Finset ℕ)} (rooted : ∀C∈F,Rooted D V r C) :
    (∑C∈F,(1:ℚ)/2^((exterior D V C).card-((outN D V r).card-1))) ≤
      ((F.image (fun C=>internalHead D C r)).card:ℚ) := by
  classical
  let f := fun C=>internalHead D C r
  let w := fun C=>(1:ℚ)/2^((exterior D V C).card-((outN D V r).card-1))
  have per (u) (um : u∈F.image f) : (∑C∈F.filter (fun C=>f C=u),w C)≤1 := by
    let A := F.filter (fun C=>f C=u)
    have roots C (cm : C∈A) := rooted C (mem_filter.mp cm).1
    have turn C (cm : C∈A) : u∈outN D C r := (mem_filter.mp cm).2 ▸ chosen (roots C cm) (roots C cm).root
    have single C (cm : C∈A) :
        (exterior D V C\(outN D V r).erase u).card=(exterior D V C).card-((outN D V r).card-1) := by
      obtain ⟨uc,edge⟩ := mem_outN.mp (turn C cm)
      rw [card_sdiff_of_subset (turn_reserve roots turn C cm),
        card_erase_of_mem (mem_outN.mpr ⟨(roots C cm).sub uc,edge⟩)]
    have bound := turn_packing roots turn
    exact (sum_congr rfl (fun C cm=>show w C=_ by dsimp [w]; rw [single C cm])).le.trans bound
  have maps (C) (cm : C∈F) : f C∈F.image f := mem_image_of_mem f cm
  calc
    ∑C∈F,w C = ∑u∈F.image f,∑C∈F.filter (fun C=>f C=u),w C := (sum_fiberwise_of_maps_to maps w).symm
    _ ≤ ∑_u∈F.image f,(1:ℚ) := sum_le_sum per
    _ = _ := by simp [f]

#print axioms root_packing
#print axioms reserve_multiplicity
#print axioms degree_turn_limit
#print axioms bank_multiplicity
#print axioms physical_split
#print axioms turn_packing
#print axioms turn_multiplicity
end LeanCH.BR.ExteriorPacking

namespace LeanCH.BR.ExteriorPacking
open Finset BRq2 BRq3 BR45 ExclusiveBankRouting

/-- Keep the actual parent count and omission count of each support.
The bound is the size of the physical parent pool, with no degree, cutoff,
uniform exterior size, or uniform demand assumption. -/
theorem physical_pool_budget {D V} {F : Finset (Finset ℕ)} {P S : Finset ℕ}
    (parents : Finset ℕ→Finset ℕ) (slots : ∀C∈F,parents C⊆P)
    (roots : ∀C∈F,∀v∈parents C,Rooted D V v C) (reserve : ∀C∈F,S⊆exterior D V C) :
    (∑C∈F,((parents C).card:ℚ)/2^((exterior D V C\S).card))≤(P.card:ℚ) := by
  classical
  let w := fun C=>(1:ℚ)/2^((exterior D V C\S).card)
  have paid (v : ℕ) (_ : v∈P) : (∑C∈F,if v∈parents C then w C else 0)≤1 := by
    rw [←sum_filter]
    have visible (C) (cm : C∈F.filter (fun C=>v∈parents C)) := roots C (mem_filter.mp cm).1 v (mem_filter.mp cm).2
    exact reciprocal_packing (physical_split visible)
      (fun C _=>disjoint_left.mpr (fun _ cm ex=>(mem_sdiff.mp ex).2 cm))
      (fun C cm=>reserve C (mem_filter.mp cm).1)
  have bill C (cm : C∈F) :
      (∑v∈P,if v∈parents C then w C else 0)=((parents C).card:ℚ)*w C := by
    rw [←sum_filter]
    have eq : P.filter (fun v=>v∈parents C)=parents C := by
      ext v
      exact ⟨fun h=>(mem_filter.mp h).2,fun vm=>mem_filter.mpr ⟨slots C cm vm,vm⟩⟩
    simp [eq,nsmul_eq_mul]
  calc
    _ = ∑C∈F,∑v∈P,if v∈parents C then w C else 0 :=
      sum_congr rfl (fun C cm=>by rw [bill C cm]; simp [w,div_eq_mul_inv])
    _ = ∑v∈P,∑C∈F,if v∈parents C then w C else 0 := sum_comm
    _ ≤ ∑_v∈P,(1:ℚ) := sum_le_sum paid
    _ = _ := by simp

#print axioms physical_pool_budget

/-- All quantities are measured on physical digraph labels. The exponent is
the excess exterior size per sponsoring cycle. A separate bound on parent
reuse is unnecessary. -/
theorem routed_cycle_budget {ι : Type*} {F : Finset (Finset ℕ)} {z : ι}
    (step : ι→ι→Prop) (bank : ι→Finset ℕ) (mark : ι→ℕ) (origin : Finset ℕ→ι)
    (parents : Finset ℕ→Finset ℕ) (D : CH.Digraph) (V : Finset ℕ) {q b k m ell : ℕ}
    (hq : 0<q) (free : QFree D V q) (marked : ∀i,mark i∈bank i) (inside : ∀i,mark i∈V)
    (layers : ∀i,m≤(ball D V (mark i) (q-1)).card)
    (size : ∀i,b≤(bank i).card) (apart : ∀i j,i≠j → Disjoint (bank i) (bank j))
    (sends : ∀i j,step i j → bank i⊆inN D V (mark j))
    (two : V.card-m<b+b) (claimSize : ∀C∈F,k≤(parents C).card)
    (roots : ∀C∈F,∀v∈parents C,Rooted D V v C)
    (complete : ∀C∈F,∀v∈parents C,bank (origin C)⊆outN D V v)
    (away : ∀C∈F,Disjoint (bank (origin C)) C)
    (outer : ∀C∈F,(exterior D V C).card≤(bank (origin C)).card+ell)
    (separate : ∀C∈F,∀i,step i (origin C) → Disjoint (parents C) (bank i))
    (noRoom : V.card-m<k+b) (arrive : ∀C∈F,Relation.ReflTransGen step (origin C) z) :
    F.card*k≤(V.card-m)*2^ell := by
  classical
  let cap := V.card-m
  have indeg i : (inN D V (mark i)).card≤cap :=
    (parent_room hq free (inside i)).trans (Nat.sub_le_sub_left (layers i) V.card)
  have incoming C (cm : C∈F) : parents C⊆inN D V (mark (origin C)) := by
    intro v vm
    have cr := roots C cm v vm
    exact mem_inN.mpr ⟨cr.sub cr.root,(mem_outN.mp (complete C cm v vm (marked _))).2⟩
  have unique {i j a} (ia : step i a) (ja : step j a) : i=j := by
    by_contra diff
    have count := (pool_conflict (apart i j diff) (sends i a ia) (sends j a ja)).trans (indeg a)
    have si := size i
    have sj := size j
    dsimp [cap] at count
    omega
  have start C (cm : C∈F) i (edge : step i (origin C)) : False := by
    have count := (pool_conflict (separate C cm i edge) (incoming C cm) (sends i _ edge)).trans (indeg _)
    have ce := claimSize C cm
    have si := size i
    dsimp [cap] at count
    omega
  apply terminal_ball_budget step bank mark origin parents D V hq free inside layers size apart sends
    two claimSize incoming separate noRoom arrive
  intro v
  let G := F.filter (fun C=>v∈parents C)
  rcases G.eq_empty_or_nonempty with none|⟨A,am⟩
  · change G.card≤_; simp [none]
  have af := (mem_filter.mp am).1
  have av := (mem_filter.mp am).2
  have eq {C} (cm : C∈G) : origin C=origin A := by
    have cf := (mem_filter.mp cm).1
    exact same_origin (step:=step) (a:=origin C) (b:=origin A) (z:=z) unique
      (start C cf) (start A af) (arrive C cf) (arrive A af)
  exact bank_multiplicity (S:=bank (origin A)) (fun C cm=>roots C (mem_filter.mp cm).1 v (mem_filter.mp cm).2)
    (complete A af v av) (fun C cm=>by rw [←eq cm]; exact away C (mem_filter.mp cm).1)
    (fun C cm=>by rw [←eq cm]; exact outer C (mem_filter.mp cm).1)

#print axioms routed_cycle_budget
end LeanCH.BR.ExteriorPacking

namespace LeanCH.BR.ExteriorPacking
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor Closure.MandatoryExcursion
open Closure.MarkedCyclePeeling Closure.FirstPacketBarrier Closure.ShortestCycleWeights

theorem rooted_cycle {D V q C a} (hq : 1≤q) (free : QFree D V q)
    (cycle : Cycle D V q C) (member : a∈C) : Rooted D V a C :=
  ⟨cycle.sub,member,cycle.heads,fun y ym=>⟨span D V q a y,(segments hq free cycle member ym).2.2.1⟩⟩

/-- Apply the budget to the entire column of an actual family arc. This includes
all its supporting cycles and counts each distinct support once. -/
theorem arc_budget {D V q} (hq : 1≤q) (free : QFree D V q)
    (F : Family) (cycles : ∀C∈F,Cycle D V q C) (e : Arc) :
    (∑C∈col D F e,(1:ℚ)/2^((exterior D V C\(outN D V e.1).erase e.2).card)) ≤ 1 := by
  apply turn_packing (r:=e.1) (u:=e.2)
  · intro C cm
    obtain ⟨cf,cr,_,_⟩ := mem_col.mp cm
    exact rooted_cycle hq free (cycles C cf) cr
  · intro C cm
    obtain ⟨_,_,cy,edge⟩ := mem_col.mp cm
    exact mem_outN.mpr ⟨cy,edge⟩

/-- Every member of a sequence of native cycle families can be repriced in
its own selected digraph. Its exterior and root degree are recomputed there. -/
theorem selected_arc_budget {q n} (X : Model q n) (hq : 1≤q)
    (F : Family) (native : F⊆family X) (e : Arc) :
    let E := graph X.D F
    (∑C∈col E F e,(1:ℚ)/2^((exterior E X.V C\(outN E X.V e.1).erase e.2).card)) ≤ 1 := by
  classical
  intro E
  have sub {a b} (ab : E a b=true) : X.D a b=true := by
    obtain ⟨C,cm⟩ := active.mp ab
    exact (mem_col.mp cm).2.2.2
  have lift {a b k} (w : Walk E X.V a b k) : Walk X.D X.V a b k := by
    induction w with
    | refl => exact .refl _
    | step hv edge _ ih => exact .step hv (sub edge) ih
  apply arc_budget hq (fun a l pos fit w=>X.free a l pos fit (lift w))
  intro C cm
  exact retain_cycle (mem_filter.mp (native cm)).2 cm

#print axioms rooted_cycle
#print axioms arc_budget
#print axioms selected_arc_budget
end LeanCH.BR.ExteriorPacking
