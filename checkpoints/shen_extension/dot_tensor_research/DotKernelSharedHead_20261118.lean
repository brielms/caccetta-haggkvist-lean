import checkpoints.shen_extension.RootedKernelTransition
import LeanCH.BR.BRShortestCycle
import LeanCH.BR.BRCycleReturn

namespace LeanCH.BR.ShenKernelHead
open BRq2 BRq3 Finset ShenPrimeTransition ShenRootedKernel
open Classical

theorem order_of_sparse {D V q d} (hq : 2≤q) (free : QFree D V q)
    (sparse : Sparse D V) (degree : ∀ v∈V, d≤(outN D V v).card) : q*d<V.card := by
  by_contra! small
  obtain ⟨K,ks,low⟩ := sparse
  have strict : Strict q D V (fun _ => 1) := by
    apply nat_strict.mpr
    intro v hv
    have eq : score q D V (fun _ => 1) v = 1+q*(outN D V v).card := by simp [score,outN]
    have le := Nat.mul_le_mul_left q (degree v hv)
    rw [eq]
    simp only [sum_const,smul_eq_mul,mul_one]
    omega
  have bill := closed_pressure hq free strict ks (Finset.Subset.refl _) (fun _ _ _ hy _ => hy)
  exact low.not_ge (by simpa [wt] using bill)

private theorem automorphism_out {D V e} (a : Symmetry D V e) {x} (hx : x∈V) :
    (outN D V (e x)).card=(outN D V x).card := by
  have eq : outN D V (e x) = (outN D V x).map e.toEmbedding := by
    ext z
    obtain ⟨y,rfl⟩ := e.surjective z
    simp only [mem_map_equiv,e.symm_apply_apply,mem_outN,a.inside]
    by_cases hy : y∈V <;> simp [hy,a.edge x hx y]
  rw [eq,card_map]

def parents (D : CH.Digraph) (U : Finset ℕ) (y : ℕ) := U.filter (fun x => D x y=true)

theorem transitive_regular {D V} (ne : V.Nonempty) (aut : Transitive D V) :
    ∃ d, ∀ x∈V, (outN D V x).card=d ∧ (parents D V x).card=d := by
  obtain ⟨a,ha⟩ := ne
  have counts (x) (hx : x∈V) : (outN D V x).card=(outN D V a).card ∧
      (parents D V x).card=(parents D V a).card := by
    obtain ⟨e,s,rfl⟩ := aut a ha x hx
    have rev : Symmetry (fun i j => D j i) V e := ⟨s.inside,fun i hi j hj => s.edge j hj i hi⟩
    exact ⟨automorphism_out s ha,automorphism_out rev ha⟩
  have eq := Compose.ThinRigid.sum_out_eq_sum_in D V
  change (∑ x∈V, (outN D V x).card)=∑ x∈V,(parents D V x).card at eq
  rw [sum_congr rfl (fun x hx => (counts x hx).1),sum_congr rfl (fun x hx => (counts x hx).2)] at eq
  simp only [sum_const,smul_eq_mul] at eq
  have same := Nat.eq_of_mul_eq_mul_left (card_pos.mpr ⟨a,ha⟩) eq
  exact ⟨_,fun x hx => ⟨(counts x hx).1,(counts x hx).2.trans same.symm⟩⟩

/-- A dual certificate using the uniform distribution on U. The sum over
the actual parents in U is taken before the comparison with the total. -/
theorem common_head {q D V w U} (strict : Strict q D V w) (sub : U⊆V) (ne : U.Nonempty)
    (internal : ∀ y∈U, 1+q*(parents D U y).card≤U.card) :
    ∃ y∈V\U, U.card<q*(parents D U y).card := by
  by_contra! capped
  have high := sum_lt_sum_of_nonempty ne (fun x hx => nat_strict.mp strict x (sub hx))
  have rows : (∑ x∈U,score q D V w x) =
      ∑ y∈V, ((if y∈U then w y else 0)+q*((parents D U y).card*w y)) := by
    have part : ∑ y∈V,(if y∈U then w y else 0) = ∑ y∈U,w y := by
      rw [←sum_filter,show V.filter (fun y => y∈U)=U from ext
        (fun y => ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨sub h,h⟩⟩)]
    simp only [score,sum_add_distrib,←mul_sum,part]
    rw [sum_comm (s:=U) (t:=V)]
    congr 2
    apply sum_congr rfl
    intro y _
    calc
      _ = ∑ _x∈parents D U y, w y := by simp only [parents,sum_filter]
      _ = _ := by simp
  rw [rows] at high
  have low (y) (hy : y∈V) : (if y∈U then w y else 0)+q*((parents D U y).card*w y) ≤ U.card*w y := by
    by_cases yu : y∈U
    · simpa [yu,Nat.add_mul,Nat.mul_assoc] using Nat.mul_le_mul_right (w y) (internal y yu)
    · simpa [yu,Nat.mul_assoc] using Nat.mul_le_mul_right (w y) (capped y (mem_sdiff.mpr ⟨hy,yu⟩))
  have bound := sum_le_sum low
  rw [←mul_sum] at bound
  simp only [sum_const,smul_eq_mul] at high
  omega

theorem symmetric_bank_exit {q D V w U} (hq : 2≤q) (free : QFree D V q)
    (strict : Strict q D V w) (sub : U⊆V) (ne : U.Nonempty) (aut : Transitive D U) :
    ∃ y∈V\U, U.card<q*(parents D U y).card := by
  have fu := free.mono_set sub
  have sparse := sparse_of_transitive ne (fun x hx => loopfree fu (by omega) hx) aut
  obtain ⟨d,reg⟩ := transitive_regular ne aut
  have ord := order_of_sparse hq fu sparse (fun x hx => (reg x hx).1.ge)
  exact common_head strict sub ne (fun x hx => by rw [(reg x hx).2]; omega)

def CappedBank (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃ U⊆V, U.Nonempty ∧ Transitive D U ∧ ∀ y∈V\U, q*(parents D U y).card≤U.card

theorem cycle_of_capped_bank {q n s D} (hq : 2≤q) (order : n≤q*s)
    (loop : CH.Loopless D n) (deg : CH.MinOutdegreeAtLeast D n s)
    (bank : CappedBank q D (range n)) : CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨U,sub,ne,aut,cap⟩ := bank
  have strict : Strict q D (range n) (fun _ => 1) := by
    apply nat_strict.mpr
    intro x hx
    have le := Nat.mul_le_mul_left q (Compose.FloorSix.out_card deg (mem_range.mp hx))
    simp [score] at *
    omega
  obtain ⟨y,hy,more⟩ := symmetric_bank_exit hq (qfree_of_noShort loop no) strict sub ne aut
  exact more.not_ge (cap y hy)

/-- All large samples of the same shortest cycle have a shared head outside
the entire cycle. Even labels in the unsampled part of the cycle are excluded. -/
theorem cycle_samples {q D V w M} (strict : Strict q D V w) (sub : M⊆V)
    (indeg : ∀ y∈M, (parents D M y).card≤1) {S : Finset ℕ} (sm : S⊆M) (big : q<S.card) :
    ∃ y∈V\M, S.card<q*(parents D S y).card := by
  have one (y) (hy : y∈M) : (parents D S y).card≤1 :=
    (card_le_card (filter_subset_filter _ sm)).trans (indeg y hy)
  have upper (y) (hy : y∈M) : q*(parents D S y).card ≤ q := by
    simpa using Nat.mul_le_mul_left q (one y hy)
  obtain ⟨y,yr,rich⟩ := common_head strict (sm.trans sub) (card_pos.mp (by omega))
    (fun y hy => by have := upper y (sm hy); omega)
  exact ⟨y,mem_sdiff.mpr ⟨(mem_sdiff.mp yr).1,fun ym => by have := upper y ym; omega⟩,rich⟩

theorem forced_cycle_bank {q D V w} (hq : 2≤q) (free : QFree D V q)
    (ne : V.Nonempty) (strict : Strict q D V w) :
    ∃ M⊆V, q<M.card ∧ BRq3.OutEq 1 D M ∧ (∀ y∈M,(parents D M y).card=1) ∧
      ∀ S⊆M, q<S.card → ∃ y∈V\M, S.card<q*(parents D S y).card ∧
        M ∩ ball D V y (S.card/q-1)=∅ := by
  have degree (v) (hv : v∈V) : 1≤(outN D V v).card := by
    by_contra! bad
    have emp : outN D V v=∅ := card_eq_zero.mp (by omega)
    have sumz : (∑ y∈V, if D v y=true then w y else 0)=0 := by
      change _=0
      rw [←sum_filter,show V.filter (fun y => D v y=true) = ∅ from emp,sum_empty]
    have high := nat_strict.mp strict v hv
    simp [score,sumz] at high
    exact high.not_ge (single_le_sum (f:=w) (by intros; omega) hv)
  obtain ⟨p,M,pq,pfree,sub,size,out⟩ := BRsGen.exists_minimal_cycle_support (by omega) free degree ne
  have hp : 1≤p := by omega
  have reg := BR45.dt_reg hp (BR45.ball_q_one p hp) (pfree.mono_set sub)
    (fun v hv => (out v hv).ge) (by simpa using size)
  refine ⟨M,sub,by omega,out,reg.2,?_⟩
  intro S sm big
  obtain ⟨y,hy,feed⟩ := cycle_samples strict sub (fun z hz => (reg.2 z hz).le) sm big
  have more := Nat.mul_le_mul_left q (card_le_card (filter_subset_filter (fun z => D z y=true) sm))
  change q*(parents D S y).card≤q*(BR45.inN D M y).card at more
  have ratio : S.card/q < (BR45.inN D M y).card :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.mul_comm]; omega)
  have divpos : 0 < S.card / q := Nat.div_pos (le_of_lt big) (by omega)
  have sizeS := card_le_card sm
  have room : S.card/q≤p := by
    have cmp := Nat.div_lt_self (by omega : 0 < S.card) (by omega : 1 < q)
    omega
  have cap := BRsub.cycle_reachable_card_cap (t:=S.card/q-1) (by omega) pfree sub size out
    (mem_sdiff.mp hy).1 (card_pos.mp (by omega))
  exact ⟨y,hy,feed,card_eq_zero.mp (by omega)⟩

#print axioms forced_cycle_bank
#print axioms common_head
#print axioms symmetric_bank_exit
#print axioms cycle_of_capped_bank
end LeanCH.BR.ShenKernelHead



