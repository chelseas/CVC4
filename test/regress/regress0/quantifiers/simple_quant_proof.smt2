(set-logic BV)
(set-info :status unsat)
(declare-fun x0 () (_ BitVec 2))
(assert
   (forall
    ((A (_ BitVec 2)))
      (= #b11 (bvadd A #b01))))
(check-sat)
