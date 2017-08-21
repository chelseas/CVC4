(set-logic BV)
(set-info :status unsat)
(declare-fun x0 () (_ BitVec 2))
(assert
   (forall
    ((A (_ BitVec 2)) (B (_ BitVec 2)))
      (and (= A B) (= A (bvadd B #b01)))))
(check-sat)
