/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji, Paul Cadman
-/
module

public import NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminant
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Fin.Tuple
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Preorder.Finite
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# Correctness of the Cached Bird Determinant

This module proves that the matrix recurrence used by the cached and charged
evaluators computes `Matrix.det` over every commutative ring.  The proof is
Bird's bordered-minor invariant: the `p`th recurrence stage is a signed sum of
length-`p` strictly increasing bordered minors.

The argument is adapted to the project's Lean 4.32 matrix recurrence from the
mathlib correctness proof merged after the pinned release.  Keeping it in a
separate module makes the algebraic bridge explicit while leaving the cached
implementation and its arithmetic cost model unchanged.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminant

open Function
open scoped Matrix BigOperators

variable {R : Type*} [CommRing R] {m n p : Nat}

@[simp] private theorem cons_comp_succ {α : Sort*} (x : α) (f : Fin n → α) :
    Fin.cons x f ∘ Fin.succ = f :=
  funext fun _ ↦ Fin.cons_succ ..

@[simp] private theorem cons_zero_succ :
    (Fin.cons 0 Fin.succ : Fin (n + 1) → Fin (n + 1)) = id :=
  Fin.cons_self_tail id

@[simp] private theorem cons_comp_succ_succAbove {β : Type*}
    (x : β) (f : Fin (n + 1) → β) (i : Fin (n + 1)) :
    Fin.cons x f ∘ i.succ.succAbove = Fin.cons x (i.removeNth f) :=
  funext (Fin.cases rfl fun _ ↦ by simp [Fin.removeNth])

private theorem cons_removeNth_eq_comp_cycleRange_symm {α : Type*}
    (x : Fin (n + 1) → α) (q : Fin (n + 1)) :
    Fin.cons (x q) (q.removeNth x) = x ∘ q.cycleRange.symm := by
  ext i
  cases i using Fin.cons <;> simp [Fin.removeNth_apply]

private theorem strictMono_insertNth_iff {α : Type*} [Preorder α]
    (q : Fin (n + 1)) (x : α) (f : Fin n → α) :
    StrictMono (q.insertNth x f) ↔
      StrictMono f ∧ (∀ i, i.castSucc < q → f i < x) ∧
        (∀ i, q ≤ i.castSucc → x < f i) := by
  refine ⟨fun h ↦ ⟨fun a b hab ↦ ?_, ⟨fun i hlt ↦ ?_, fun i hlt ↦ ?_⟩⟩, ?_⟩
  · simpa [hab] using h (a := q.succAbove a) (b := q.succAbove b)
  · have : q.succAbove i < q := by simp [Fin.succAbove_of_castSucc_lt, hlt]
    simpa using h this
  · have : q < q.succAbove i := by
      simp [Fin.succAbove_of_le_castSucc, hlt, ← Fin.le_castSucc_iff]
    simpa using h this
  · rintro ⟨h, hlt, hgt⟩ a b hab
    cases a using Fin.succAboveCases q <;> cases b using Fin.succAboveCases q
    · simp at hab
    · rename_i j
      have : q ≤ j.castSucc := by
        simpa [Fin.lt_succAbove_iff_le_castSucc] using hab
      simpa using hgt _ this
    · rename_i j
      have : j.castSucc < q := by
        simpa [Fin.succAbove_lt_iff_castSucc_lt] using hab
      simpa using hlt _ this
    · simpa using h <| (Fin.strictMono_succAbove _).lt_iff_lt.mp hab

private theorem strictMono_cons {α : Type*} [Preorder α]
    {f : Fin n → α} {a : α} :
    StrictMono (Fin.cons a f) ↔ (∀ j, a < f j) ∧ StrictMono f := by
  cases n with
  | zero => simp [StrictMono]
  | succ n =>
      rw [show Fin.cons a f = Matrix.vecCons a f from rfl]
      rw [strictMono_vecCons]
      constructor
      · rintro ⟨ha, hf⟩
        exact ⟨fun j ↦ ha.trans_le (hf.monotone (Fin.zero_le j)), hf⟩
      · rintro ⟨ha, hf⟩
        exact ⟨ha 0, hf⟩

private theorem strictMono_cons_zero_succ {f : Fin n → Fin (n + 1)} :
    StrictMono (Fin.cons 0 f) ↔ f = Fin.succ := by
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ by
    subst h
    rw [show (Fin.cons 0 Fin.succ : Fin (n + 1) → Fin (n + 1)) = id from
      Fin.cons_self_tail id]
    exact strictMono_id⟩
  have key (g : Fin (n + 1) → Fin (n + 1)) (hg : StrictMono g) : g = id := by
    refine funext fun x ↦ le_antisymm ?_ (hg.id_le x)
    simpa using
      ((Fin.rev_strictAnti.comp_strictMono hg).comp Fin.rev_strictAnti).id_le (Fin.rev x)
  simpa using congrFun (key _ h) i.succ

private theorem strictMono_removeNth {α : Type*} [Preorder α]
    {f : Fin (n + 1) → α} (hf : StrictMono f) (i : Fin (n + 1)) :
    StrictMono (i.removeNth f) :=
  hf.comp (Fin.strictMono_succAbove i)

private theorem range_insertNth {α : Type*} (q : Fin (n + 1))
    (x : α) (f : Fin n → α) :
    Set.range (q.insertNth x f) = Set.insert x (Set.range f) := by
  ext y
  simp [Fin.exists_iff_succAbove q, Set.insert, eq_comm]

theorem upperIndices_sum_eq (i : Fin n) (f : Fin n → R) :
    ((upperIndices i).map f).sum = ∑ k ∈ Finset.Ioi i, f k := by
  rw [← List.sum_toFinset f]
  · congr 1
    ext k
    simp [upperIndices]
  · exact (List.nodup_finRange n).filter _

/-- Bird's bordered minor. -/
abbrev bminor (A : Matrix (Fin n) (Fin n) R) (i j : Fin n)
    (α : Fin p → Fin n) : R :=
  (A.submatrix (Fin.cons i α) (Fin.cons j α)).det

/-- Bird's principal minor. -/
abbrev pminor (A : Matrix (Fin n) (Fin n) R)
    (α : Fin p → Fin n) : R :=
  (A.submatrix α α).det

lemma det_submatrix_removeNth_eq_sign_mul_bminor
    (A : Matrix (Fin n) (Fin n) R)
    (α : Fin (p + 1) → Fin n) (i : Fin n) (s : Fin (p + 1)) :
    (A.submatrix (Fin.cons i (s.removeNth α)) α).det =
      (-1 : R) ^ s.val * bminor A i (α s) (s.removeNth α) :=
  calc
    _ = (-1 : R) ^ s.val * ((A.submatrix (Fin.cons i (s.removeNth α)) α)
        |>.submatrix id (Fin.cycleRange s).symm).det := by
      rw [Matrix.det_permute']
      simp [← mul_assoc, ← pow_add]
    _ = (-1 : R) ^ s.val * bminor A i (α s) (s.removeNth α) := by
      congrm _ * Matrix.det ?_
      simp [cons_removeNth_eq_comp_cycleRange_symm]

/-- First-column Laplace expansion of a bordered minor. -/
theorem det_bordered_expand (A : Matrix (Fin n) (Fin n) R)
    (α : Fin (p + 1) → Fin n) (i j : Fin n) :
    bminor A i j α =
      pminor A α * A i j -
        ∑ s : Fin (p + 1),
          bminor A i (α s) (s.removeNth α) * A (α s) j := calc
  _ = A i j * pminor A α +
        ∑ s : Fin (p + 1), (-1 : R) ^ (s.val + 1) * A (α s) j *
          (A.submatrix (Fin.cons i (s.removeNth α)) α).det := by
      rw [bminor, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp
  _ = pminor A α * A i j +
        ∑ s : Fin (p + 1),
          ((-1 : R) ^ (s.val + 1) *
            (A.submatrix (Fin.cons i (s.removeNth α)) α).det) * A (α s) j := by
      simp only [mul_comm (A i j), mul_right_comm]
  _ = pminor A α * A i j +
      ∑ s : Fin (p + 1),
        -(bminor A i (α s) (s.removeNth α) * A (α s) j) := by
      simp only [det_submatrix_removeNth_eq_sign_mul_bminor, ← mul_assoc,
        ← pow_add]
      aesop
  _ = pminor A α * A i j -
      ∑ s : Fin (p + 1),
        bminor A i (α s) (s.removeNth α) * A (α s) j := by
      simp only [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- A bordered minor is zero when its border column already occurs. -/
theorem bminor_eq_zero_of_mem_range
    (A : Matrix (Fin n) (Fin n) R) {k : Fin n}
    (α : Fin p → Fin n) (i : Fin n) (hk : k ∈ Set.range α) :
    bminor A i k α = 0 := by
  obtain ⟨q, rfl⟩ := hk
  exact Matrix.det_zero_of_column_eq q.succ_ne_zero <| by simp

/-- Strictly increasing words of length `p` above `i`. -/
def S (p : Nat) (i : Fin n) : Finset (Fin p → Fin n) :=
  {α : Fin p → Fin n | StrictMono (Fin.cons i α)}

theorem mem_S_iff {i : Fin n} {α : Fin p → Fin n} :
    α ∈ S p i ↔ StrictMono (Fin.cons i α) :=
  Finset.mem_filter_univ α

theorem S_zero (i : Fin n) : S 0 i = {![]} := by
  ext
  simp [mem_S_iff, Fin.strictMono_iff_lt_succ,
    eq_iff_true_of_subsingleton]

@[simp] theorem S_zero_eq_singleton {p : Nat} :
    S p (0 : Fin (p + 1)) = {Fin.succ} := by
  ext
  simp [mem_S_iff, strictMono_cons_zero_succ]

theorem S_succ_eq_biUnion (i : Fin n) :
    S (p + 1) i =
      (Finset.Ioi i).biUnion fun k ↦ (S p k).image (Fin.cons k) := by
  ext α
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ioi,
    mem_S_iff]
  refine ⟨fun hα ↦
    ⟨α 0, (strictMono_cons.mp hα).1 0, Fin.tail α, ?_,
      Fin.cons_self_tail α⟩, ?_⟩
  · simp only [Fin.cons_self_tail]
    exact hα.comp Fin.strictMono_succ
  · rintro ⟨k, hk, u, hu, rfl⟩
    exact StrictMono.vecCons hu hk

lemma exists_insertNth_mem_S {i : Fin n} {α : Fin p → Fin n} {k : Fin n}
    (hα : α ∈ S p i) (hik : i < k) (hk : k ∉ Set.range α) :
    ∃ t : Fin (p + 1), t.insertNth k α ∈ S (p + 1) i := by
  set t := ⨅ j ∈ {j | k < α j}, j.castSucc with t_eq
  use t
  simp only [mem_S_iff, strictMono_cons] at ⊢ hα
  refine ⟨fun j ↦ Fin.succAboveCases t ?_ ?_ j, ?_⟩
  · simp only [t_eq, strictMono_insertNth_iff, hα.2,
      lt_iInf_iff, le_iInf_iff, forall_exists_index, and_imp,
      iInf_le_iff_forall_lt, iInf_lt_iff, exists_prop, true_and]
    refine ⟨fun j x hjx h ↦ ?_, fun j h ↦ ?_⟩
    · contrapose! h
      have k_ne (j : Fin p) : k ≠ α j := fun hj ↦ hk ⟨j, hj.symm⟩
      exact ⟨j, h.lt_of_ne (k_ne _), hjx⟩
    · obtain ⟨q, hkq, hqj⟩ := h j.succ j.castSucc_lt_succ
      exact hkq.trans_le <|
        hα.2.monotone <| Fin.castSucc_lt_succ_iff.mp hqj
  · simpa
  · simpa using hα.1

theorem matrixStep_eq_finset
    (A F : Matrix (Fin n) (Fin n) R) :
    matrixStep A F = Matrix.of fun i j ↦
      (-∑ k ∈ Finset.Ioi i, F k k) * A i j +
        ∑ k ∈ Finset.Ioi i, F i k * A k j := by
  ext i j
  simp only [matrixStep, entry, Matrix.of_apply]
  rw [upperIndices_sum_eq, upperIndices_sum_eq]

abbrev Eq1 (A : Matrix (Fin n) (Fin n) R) (p : Nat) : Prop :=
  matrixIterate A p = Matrix.of fun i j ↦
    (-1) ^ p * ∑ α ∈ S p i, bminor A i j α

theorem paper_eq2 (A : Matrix (Fin n) (Fin n) R)
    (i : Fin n) (hEq1 : Eq1 A p) :
    (-∑ k ∈ Finset.Ioi i, matrixIterate A p k k) =
      (-1) ^ (p + 1) * ∑ α ∈ S (p + 1) i, pminor A α := by
  calc
    (-∑ k ∈ Finset.Ioi i, matrixIterate A p k k) =
        (-1) ^ (p + 1) *
          ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p k, bminor A k k α := by
      simp only [hEq1, Matrix.of_apply, ← Finset.mul_sum]
      ring
    _ = (-1) ^ (p + 1) * ∑ α ∈ S (p + 1) i, pminor A α := by
      rw [S_succ_eq_biUnion, Finset.sum_biUnion]
      · congrm (((-1) ^ (p + 1) * ∑ k ∈ Finset.Ioi i, ?_))
        symm
        exact Finset.sum_image fun _ _ _ _ hαβ ↦ (Fin.cons_inj.mp hαβ).2
      · grind [Set.PairwiseDisjoint, Set.Pairwise, Finset.disjoint_left,
          Fin.cons_inj]

theorem paper_eq3 (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) (hEq1 : Eq1 A p) :
    matrixIterate A (p + 1) i j =
      (-1) ^ (p + 1) *
        (∑ α ∈ S (p + 1) i, pminor A α * A i j -
          ∑ k ∈ Finset.Ioi i,
            ∑ α ∈ S p i, bminor A i k α * A k j) := by
  rw [matrixIterate]
  rw [matrixStep_eq_finset]
  simp_rw [Matrix.of_apply, paper_eq2 A i hEq1, hEq1,
    Matrix.of_apply, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem paper_eq5 (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ∑ α ∈ S (p + 1) i, bminor A i j α =
      ∑ α ∈ S (p + 1) i, pminor A α * A i j -
        ∑ α ∈ S (p + 1) i,
          ∑ t : Fin (p + 1),
            bminor A i (α t) (t.removeNth α) * A (α t) j := calc
  _ = ∑ α ∈ S (p + 1) i,
      (pminor A α * A i j -
        ∑ t : Fin (p + 1),
          bminor A i (α t) (t.removeNth α) * A (α t) j) := by
      exact Finset.sum_congr rfl <| by simp [det_bordered_expand]
  _ = ∑ α ∈ S (p + 1) i, pminor A α * A i j -
      ∑ α ∈ S (p + 1) i,
        ∑ t : Fin (p + 1),
          bminor A i (α t) (t.removeNth α) * A (α t) j := by
      rw [Finset.sum_sub_distrib]

theorem paper_eq3_eq5_off_diag
    (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ∑ k ∈ Finset.Ioi i,
        ∑ α ∈ S p i, bminor A i k α * A k j =
      ∑ α' ∈ S (p + 1) i,
        ∑ t : Fin (p + 1),
          bminor A i (α' t) (t.removeNth α') * A (α' t) j := by
  rw [Finset.sum_comm, ← Finset.sum_product', ← Finset.sum_product']
  symm
  refine Finset.sum_of_injOn
    (fun ⟨α, k⟩ ↦ ⟨k.removeNth α, α k⟩) ?_ ?_ ?_ ?_
  · simp only [Set.InjOn, Finset.coe_product, Finset.coe_univ,
      Set.mem_prod, Set.mem_univ, and_true, Finset.mem_coe, Prod.mk.injEq,
      and_imp, Prod.forall, mem_S_iff, strictMono_cons]
    intros α k hi hiα α' k' hj hiα' hremove hvalue
    suffices hrange : Set.range α = Set.range α' by
      rw [hiα.range_inj hiα'] at hrange
      subst α'
      exact ⟨rfl, hiα.injective hvalue⟩
    calc
      _ = Set.insert (α k) (Set.range (k.removeNth α)) := by
        rw [← range_insertNth, Fin.insertNth_self_removeNth]
      _ = Set.insert (α' k') (Set.range (k'.removeNth α')) := by
        rw [hvalue, hremove]
      _ = Set.range α' := by
        rw [← range_insertNth, Fin.insertNth_self_removeNth]
  · rintro ⟨α, t⟩ hα
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod,
      Set.mem_univ, and_true, Finset.mem_coe, Finset.coe_Ioi,
      Set.mem_Ioi, mem_S_iff, strictMono_cons] at hα ⊢
    obtain ⟨hbound, hmono⟩ := hα
    exact ⟨⟨fun q ↦ hbound (t.succAbove q),
      strictMono_removeNth hmono t⟩, hbound t⟩
  · rintro ⟨α, k⟩ htarget hnotmem
    simp only [Finset.mem_product, Finset.mem_Ioi] at htarget
    obtain ⟨hα, hk⟩ := htarget
    by_cases hoccurs : k ∈ Set.range α
    · rw [bminor_eq_zero_of_mem_range A α i hoccurs, zero_mul]
    · contrapose hnotmem
      obtain ⟨t, ht⟩ := exists_insertNth_mem_S hα hk hoccurs
      exact ⟨(t.insertNth k α, t), by simpa, by simp⟩
  · simp

theorem paper_eq1 (A : Matrix (Fin n) (Fin n) R) : Eq1 A p := by
  induction p with
  | zero =>
      ext i j
      simp [matrixIterate, S_zero, bminor]
  | succ p ih =>
      ext i j
      rw [Matrix.of_apply, paper_eq3 A i j ih, paper_eq5 A,
        paper_eq3_eq5_off_diag A]

public theorem matrixBirdDet_eq_det (A : Matrix (Fin n) (Fin n) R) :
    matrixBirdDet A = Matrix.det A := by
  cases n with
  | zero => simp [matrixBirdDet]
  | succ k =>
      have hsum : ∑ α ∈ S k (0 : Fin (k + 1)), bminor A 0 0 α = A.det := by
        simp [bminor]
      rw [matrixBirdDet, paper_eq1, Matrix.of_apply, hsum, ← mul_assoc,
        ← pow_add]
      simp

public theorem cachedBirdDet_eq_det (A : DenseMatrix n R) :
    cachedBirdDet A = Matrix.det A.toMatrix := by
  rw [cachedBirdDet_eq_matrixBirdDet, matrixBirdDet_eq_det]

public theorem evaluate_eq_det (A : Matrix (Fin n) (Fin n) R) :
    evaluate A = Matrix.det A := by
  rw [evaluate_eq_matrixBirdDet, matrixBirdDet_eq_det]

end NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminant
