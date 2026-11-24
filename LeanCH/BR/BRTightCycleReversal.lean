import LeanCH.BR.BRWalkReplacement

/-! Exact reversal criterion for an actual tight cycle, in an index-free form.
The forward distance is represented by its old internal walk. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem walk_length_of_internal_heads {D : CH.Digraph} {M : Finset ℕ}
    (heads : ∀ x∈M, ∃ y∈M, D x y=true) {x : ℕ} (hx : x∈M) (n : ℕ) :
    ∃ y∈M, Walk D M x y n := by
  induction n with
  | zero => exact ⟨x,hx,.refl _⟩
  | succ n ih =>
    obtain ⟨y,hy,w⟩ := ih
    obtain ⟨z,hz,hyz⟩ := heads y hy
    exact ⟨z,hz,w.snoc hz hyz⟩

/-- At order q+1, q-freeness and internal heads give complementary walks.
No ordered labeling or degree-one hypothesis is required. -/
theorem tight_cycle_complementary_walks {q : ℕ} {D : CH.Digraph} {M : Finset ℕ}
    (hf : QFree D M q) (hc : M.card=q+1)
    (heads : ∀ x∈M, ∃ y∈M, D x y=true)
    {x y : ℕ} (hx : x∈M) (hy : y∈M) (hne : x≠y) :
    ∃ d, 1≤d ∧ d≤q ∧ Walk D M x y d ∧ Walk D M y x (q+1-d) := by
  obtain ⟨z,hz,w⟩ := walk_length_of_internal_heads heads hx (q+1)
  obtain ⟨f,h0,hm,he⟩ := w.toFun
  have hmem : ∀ i, i≤q+1 → f i∈M := by
    intro i hi
    by_cases hi0 : i=0
    · subst i; simpa [h0] using hx
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using (he (i - 1) (by omega)).1
  have hinj : Set.InjOn f (Finset.range (q+1)) := by
    intro i hi j hj heq
    simp only [Finset.coe_range,Set.mem_Iio] at hi hj
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hij | hji
    · have wc := walk_between he hij.le (by omega : j≤q+1)
      rw [←heq] at wc
      exact hf (f i) (j-i) (by omega) (by omega) wc
    · have wc := walk_between he hji.le (by omega : i≤q+1)
      rw [heq] at wc
      exact hf (f j) (i-j) (by omega) (by omega) wc
  have hsub : (Finset.range (q+1)).image f ⊆ M := by
    intro t ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    exact hmem i (by have := Finset.mem_range.mp hi; omega)
  have hspan := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injOn hinj,Finset.card_range,hc])
  obtain ⟨j,hj,hjz⟩ := Finset.mem_image.mp (hspan.symm ▸ hmem (q+1) le_rfl)
  have hjq := Finset.mem_range.mp hj
  have hj0 : j=0 := by
    by_contra hn
    have wc := walk_between he (by omega : j≤q+1) le_rfl
    rw [←hjz] at wc
    exact hf (f j) (q+1-j) (by omega) (by omega) wc
  have hclose : f (q+1)=x := by simpa [hj0,h0] using hjz.symm
  obtain ⟨i,hi,hiy⟩ := Finset.mem_image.mp (hspan.symm ▸ hy)
  have hiq := Finset.mem_range.mp hi
  have hi0 : 0 < i := by
    by_contra hn
    have : i=0 := by omega
    exact hne (by simpa [this,h0] using hiy)
  refine ⟨i,hi0,by omega,?_,?_⟩
  · simpa [h0,hiy] using walk_between he (Nat.zero_le i) (by omega : i≤q+1)
  · simpa [hiy,hclose] using walk_between he (by omega : i≤q+1) le_rfl

def cycleRetained (D : CH.Digraph) (M : Finset ℕ) : CH.Digraph :=
  fun x y => D x y && decide (¬(x∈M ∧ y∈M))

def cycleReverseArcs (D : CH.Digraph) (M : Finset ℕ) : CH.Digraph :=
  fun x y => decide (x∈M ∧ y∈M) && D y x

def reverseCycle (D : CH.Digraph) (M : Finset ℕ) : CH.Digraph :=
  arcUnion (cycleRetained D M) (cycleReverseArcs D M)

theorem cycle_reverse_walk {D : CH.Digraph} {M V : Finset ℕ}
    (hMV : M⊆V) {x y d : ℕ} (hx : x∈M) (w : Walk D M x y d) :
    Walk (cycleReverseArcs D M) V y x d := by
  have hy : y∈M := w.end_mem_or.elim (fun h => h ▸ hx) id
  exact (walk_mono_graph_on (fun a ha b hb hab => by
    simp [cycleReverseArcs,ha,hb,hab]) (w.reverse_of_mem hx) hy).mono hMV

/-- Exact all-cutoff legality test. An internal old x-to-y walk of forward
distance d forbids a retained x-to-y walk of length at most q-d. -/
theorem tight_cycle_reversal_iff {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hf : QFree D V q) (hMV : M⊆V) (hc : M.card=q+1)
    (heads : ∀ x∈M, ∃ y∈M, D x y=true) :
    QFree (reverseCycle D M) V q ↔
      ∀ x∈M, ∀ y∈M, x≠y → ∀ d, d≤q → Walk D M x y d →
        ∀ n, n+d≤q → ¬Walk (cycleRetained D M) V x y n := by
  constructor
  · intro hK x hx y hy hne d hd wd n hn wn
    have wr := cycle_reverse_walk hMV hx wd
    have wnK : Walk (reverseCycle D M) V x y n :=
      walk_sub (fun a b hab => by simp [reverseCycle,arcUnion,hab]) wn
    have wrK : Walk (reverseCycle D M) V y x d :=
      walk_sub (fun a b hab => by simp [reverseCycle,arcUnion,hab]) wr
    have hdpos : 0<d := by
      cases d with
      | zero => cases wd; exact (hne rfl).elim
      | succ d => omega
    exact hK x (n+d) (by omega) hn (wnK.append wrK)
  · intro htest
    apply qfree_union_of_short_replacement (M := M)
    · apply qfree_sub (D := cycleRetained D M) _ hf
      intro a b h
      simp only [cycleRetained, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    · apply qfree_sub (D := cycleReverseArcs D M) _ hf.reverse
      intro a b h
      simp only [cycleReverseArcs, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2
    · intro a ha b hb hab _
      simp only [cycleReverseArcs, Bool.and_eq_true, decide_eq_true_eq] at hab
      exact hab.1
    · intro x hx y hy n hn wn
      by_cases hxy : x=y
      · subst y; exact ⟨0,Nat.zero_le _,.refl _⟩
      obtain ⟨d,hd,hdq,wd,wback⟩ := tight_cycle_complementary_walks
        (hf.mono_set hMV) hc heads hx hy hxy
      have hlong : q<n+d := by
        by_contra h
        exact htest x hx y hy hxy d hdq wd n (by omega) wn
      exact ⟨q+1-d,by omega,cycle_reverse_walk hMV hy wback⟩

end LeanCH.BR.WeightedSD
