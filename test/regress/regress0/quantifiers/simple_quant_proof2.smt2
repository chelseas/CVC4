(set-logic BV)
(set-info :status unsat)
(declare-fun x0 () (_ BitVec 2))
(assert
   (forall
    ((A (_ BitVec 2)) (B (_ BitVec 2)))
      (= A B)))
(check-sat)
