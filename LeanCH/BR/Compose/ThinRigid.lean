import LeanCH.BR.Compose.Boundary
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Thin-set rigidity at the boundary (goal: boundary regularity, 11 Nov 2026).

A set `T` is *thin* when no vertex outside `T` has two out-neighbours in `T`.
On `q*s+1` labels with minimum out-degree `s ≥ 1` and no cycle of length at most `q`:

* `thin_rigid`: if `T` is a thin `q`-set and `BoundaryRegular q (s-1)` holds, every vertex outside `T` has
  out-degree exactly `s` and exactly one out-neighbour in `T`.
-/

namespace Compose.ThinRigid

open CH Compose.FloorSix Compose.Boundary


def Thin (G : CH.Digraph) (n : Nat) (T : Finset Nat) : Prop :=
  ∀ x, x < n → x ∉ T → ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ¬ (G x a = true ∧ G x b = true)

/-- Arc double counting inside a finite set. -/
theorem sum_out_eq_sum_in (G : CH.Digraph) (S : Finset Nat) :
    ∑ x ∈ S, (S.filter (fun w => G x w = true)).card = ∑ v ∈ S, (S.filter (fun u => G u v = true)).card := by
  classical
  have hc : ∀ (p : Nat → Prop) [DecidablePred p], (S.filter p).card = ∑ w ∈ S, if p w then 1 else 0 := by
    intro p _; exact Finset.card_filter p S
  rw [Finset.sum_congr rfl (fun x _ => hc (fun w => G x w = true)),
      Finset.sum_congr rfl (fun v _ => hc (fun u => G u v = true))]
  exact Finset.sum_comm

/-- At most one out-neighbour in a thin set. -/
theorem thin_hit_le_one {G : CH.Digraph} {n : Nat} {T : Finset Nat} (thin : Thin G n T)
    {x : Nat} (hx : x < n) (hxT : x ∉ T) : (T.filter (fun w => G x w = true)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  exact thin x hx hxT a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    ⟨(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩

theorem thin_rigid
    {G : CH.Digraph} {q s : Nat} {T : Finset Nat} (hs : 1 ≤ s) (_hq : 1 ≤ q)
    (br : BoundaryRegular q (s - 1))
    (loopless : CH.Loopless G (q * s + 1)) (deg : CH.MinOutdegreeAtLeast G (q * s + 1) s)
    (noShort : ¬ CH.HasDirectedCycleAtMost G (q * s + 1) q)
    (hTsub : T ⊆ Finset.range (q * s + 1)) (hTcard : T.card = q) (thin : Thin G (q * s + 1) T) :
    ∀ x, x < q * s + 1 → x ∉ T →
      (T.filter (fun w => G x w = true)).card = 1 ∧
      ((Finset.range (q * s + 1)).filter (fun w => G x w = true)).card = s := by
  classical
  set n := q * s + 1 with hn
  set K := Finset.range n \ T with hK
  have hKsub : K ⊆ Finset.range n := Finset.sdiff_subset
  have hKcard : K.card = q * (s - 1) + 1 := by
    rw [hK, Finset.card_sdiff_of_subset hTsub, Finset.card_range, hTcard]
    have hqs : q * s = q * (s - 1) + q := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  -- out-degree splits over K and T
  have split : ∀ x, ((Finset.range n).filter (fun w => G x w = true)).card =
      (K.filter (fun w => G x w = true)).card + (T.filter (fun w => G x w = true)).card := by
    intro x
    have hdisj : Disjoint (K.filter (fun w => G x w = true)) (T.filter (fun w => G x w = true)) :=
      Finset.disjoint_filter_filter (Finset.sdiff_disjoint)
    rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union, hK, Finset.sdiff_union_of_subset hTsub]
  -- every vertex of K keeps at least s - 1 out-neighbours in K
  have keep : ∀ x ∈ K, s - 1 ≤ (K.filter (fun w => G x w = true)).card := by
    intro x hxK
    have hxn : x < n := Finset.mem_range.mp (hKsub hxK)
    have hxT : x ∉ T := (Finset.mem_sdiff.mp hxK).2
    have := out_card deg hxn
    rw [split x] at this
    have := thin_hit_le_one thin hxn hxT
    omega
  -- relabel K as range m
  obtain ⟨e, eB, eI, eM, eS⟩ := CH.Side.sc_finset_enumeration hKsub
  set m := K.card with hm
  let H : CH.Digraph := fun a b => if a < m then (if b < m then G (e a) (e b) else false) else false
  have Hval : ∀ a b, a < m → b < m → H a b = G (e a) (e b) := by
    intro a b ha hb; simp [H, ha, hb]
  -- degree transfer through e
  have outT : ∀ a, a < m → ((Finset.range m).filter (fun j => H a j = true)).card =
      (K.filter (fun w => G (e a) w = true)).card := by
    intro a ha
    have himg : ((Finset.range m).filter (fun j => H a j = true)).image e = K.filter (fun w => G (e a) w = true) := by
      ext w; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨j, ⟨hj, hH⟩, rfl⟩; exact ⟨eM j hj, by rwa [Hval a j ha hj] at hH⟩
      · rintro ⟨hwK, hG⟩; obtain ⟨j, hj, rfl⟩ := eS w hwK; exact ⟨j, ⟨hj, by rwa [Hval a j ha hj]⟩, rfl⟩
    rw [← himg, Finset.card_image_of_injOn]
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
    exact eI i j hi.1 hj.1 hij
  have inT : ∀ a, a < m → ((Finset.range m).filter (fun j => H j a = true)).card =
      (K.filter (fun u => G u (e a) = true)).card := by
    intro a ha
    have himg : ((Finset.range m).filter (fun j => H j a = true)).image e = K.filter (fun u => G u (e a) = true) := by
      ext w; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨j, ⟨hj, hH⟩, rfl⟩; exact ⟨eM j hj, by rwa [Hval j a hj ha] at hH⟩
      · rintro ⟨hwK, hG⟩; obtain ⟨j, hj, rfl⟩ := eS w hwK; exact ⟨j, ⟨hj, by rwa [Hval j a hj ha]⟩, rfl⟩
    rw [← himg, Finset.card_image_of_injOn]
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
    exact eI i j hi.1 hj.1 hij
  -- H is a boundary graph for degree s - 1
  have Hloop : CH.Loopless H m := by
    intro a ha; rw [Hval a a ha ha]; exact loopless (e a) (eB a ha)
  have Hmin : CH.MinOutdegreeAtLeast H m (s - 1) := by
    intro a ha
    let Tset := (Finset.range m).filter (fun j => H a j = true)
    have hT : s - 1 ≤ Tset.card := by rw [outT a ha]; exact keep (e a) (eM a ha)
    refine ⟨(Tset.sort (· ≤ ·)).take (s - 1), ?_, ?_, ?_⟩
    · rw [List.length_take, Finset.length_sort]; omega
    · exact (Finset.sort_nodup _ _).sublist (List.take_sublist _ _)
    · intro w hw
      have hwT : w ∈ Tset := (Finset.mem_sort _).mp ((List.take_sublist _ _).subset hw)
      exact ⟨(Finset.mem_range.mp (Finset.mem_filter.mp hwT).1), (Finset.mem_filter.mp hwT).2⟩
  have Hshort : ¬ CH.HasDirectedCycleAtMost H m q := by
    intro h; exact noShort (CH.Side.sc_induced_subgraph_transport eB eI h)
  have hmq : m = q * (s - 1) + 1 := hKcard
  have Hreg := br H (hmq ▸ Hloop) (hmq ▸ Hmin) (hmq ▸ Hshort)
  -- every vertex of K has in-degree exactly s - 1 inside K
  have inK : ∀ v ∈ K, (K.filter (fun u => G u v = true)).card = s - 1 := by
    intro v hvK
    obtain ⟨a, ha, rfl⟩ := eS v hvK
    rw [← inT a ha]
    have := Hreg a (hmq ▸ ha)
    simpa [par, hmq] using this
  -- double counting forces every out-degree inside K to be exactly s - 1
  have total : ∑ x ∈ K, (K.filter (fun w => G x w = true)).card = ∑ x ∈ K, (s - 1) := by
    rw [sum_out_eq_sum_in G K]; exact Finset.sum_congr rfl inK
  have outK : ∀ x ∈ K, (K.filter (fun w => G x w = true)).card = s - 1 := by
    have := (Finset.sum_eq_sum_iff_of_le (fun x hx => keep x hx)).mp total.symm
    exact fun x hx => (this x hx).symm
  intro x hx hxT
  have hxK : x ∈ K := Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hx, hxT⟩
  have h1 := outK x hxK
  have h2 := thin_hit_le_one thin hx hxT
  have h3 := out_card deg hx
  rw [split x] at h3 ⊢
  constructor <;> omega

end Compose.ThinRigid
