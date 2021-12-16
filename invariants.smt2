(declare-fun Invar (Int Int) Bool)
; invariant de boucle
(assert (forall (( i Int ) ( v Int ))
  (=> (and (Invar i v) (< i 3)) (Invar (+ i 1) (+ v 3)))))
; initialisation
(assert (Invar 0 0))
; assertion finale
(assert (forall (( i Int ) ( v Int ))
  (=> (and (Invar i v) (>= i 3)) (= v 9))))
; appel au solveur
(check-sat-using (then qe smt))
(get-model)
(exit)