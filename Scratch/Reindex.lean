import NormalForms.Matrix.Smith

open scoped Matrix

theorem reindex_fin_fin_eq {m n : Nat} {R : Type} [DecidableEq R]
    (A : Matrix (Fin m) (Fin n) R) :
    Matrix.reindex (Fintype.equivFin (Fin m)) (Fintype.equivFin (Fin n)) A =
      (by
        simpa using
          (A : Matrix (Fin m) (Fin n) R) :
            Matrix (Fin (Fintype.card (Fin m))) (Fin (Fintype.card (Fin n))) R) := by
  ext i j
  simp [Fintype.equivFin]
