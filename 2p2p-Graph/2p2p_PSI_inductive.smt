;Encoding of NON-INTERF-2

;Declaration of data-types
(declare-sort A)
(declare-sort Ae)
(declare-sort I)
(declare-sort S)
(declare-sort Se)
(declare-sort E)
(declare-datatypes () ((OpType (AV) (RV) (AE) (RE) )))

(declare-fun op (E) OpType)
(declare-fun arg (E) A)
(declare-fun arge (E) Ae)
(declare-fun src (E) S)
(declare-fun srct (E) S)
(declare-fun srce (E) Se)
(declare-fun srcet (E) Se)

(declare-fun eid (E) I)
(declare-fun eo (E E) Bool)
(declare-fun sV (Ae) A)
(declare-fun eV (Ae) A)
(declare-const s0 S)
(declare-const s0e Se)
(declare-const s0t S)
(declare-const s0et Se)

(declare-fun c (S A) Bool)
(declare-fun ce (Se Ae) Bool)

(assert (forall ((e1 Ae)(e2 Ae)) (=> (and (= (sV e1) (sV e2)) (= (eV e1) (eV e2)) ) (= e1 e2) ) ))

;Encoding 2p2p graph CRDT
(declare-fun addV (S S Se Se S S Se Se A S S Se Se) Bool)
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) )
  (=> (addV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (and (= s1t s2t) (= s1e s2e) (= s1et s2et)  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) (x A) )
  (=> (addV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (= (c s2 x) (ite (= x a) true (c s1 x) )  )  )  ))

(declare-fun addE (S S Se Se S S Se Se Ae S S Se Se) Bool)
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (ae Ae) )
  (=> (addE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (and (= s1t s2t) (= s1 s2) (= s1et s2et)  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (ae Ae) (xe Ae) )
  (=> (and (addE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (c s3 (sV ae)) (c s3 (eV ae)) (not (c s3t (sV ae))) (not (c s3t (eV ae)))  )  (= (ce s2e xe) (ite (= xe ae) true (ce s1e xe) )  )    )))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (ae Ae) )
  (=> (and (addE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (or (not (c s3 (sV ae))) (not (c s3 (eV ae)))  (c s3t (sV ae))  (c s3t (eV ae))  ))  (= s1e s2e  )    )))

(declare-fun removeV (S S Se Se S S Se Se A S S Se Se) Bool)
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) )
  (=> (removeV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (and (= s1 s2) (= s1e s2e) (= s1et s2et)  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) (x A) ) (exists ((ae Ae))
   (=> (and (removeV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (=> (and (ce s3e ae) (not (ce s3et ae))) (and (not (= (sV ae) a)) (not (= (eV ae) a)) )) (c s1 a) (c s3 a) (not (c s3t a)) ) (= (c s2t x) (ite (= x a) true (c s1t x) )  )  )  )))
; (assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) (x A) )
;    (=> (and (removeV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (isolated s3e s3et a) (c s1 a) (c s3 a) (not (c s3t a)) ) (= (c s2t x) (ite (= x a) true (c s1t x) )  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (a A) (ae Ae) )
  (=> (and (removeV s3 s3t s3e s3et s1 s1t s1e s1et a s2 s2t s2e s2et) (or (not (c s3 a)) (c s3t a) (not (c s1 a)) (and (ce s3e ae)
    (not (ce s3et ae)) (or (= (sV ae) a) (= (eV ae) a) ) ) ) ) (= s1t s2t )  )  ))

(declare-fun removeE (S S Se Se S S Se Se Ae S S Se Se) Bool)
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (ae Ae) )
  (=> (removeE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (and (= s1t s2t) (= s1 s2) (= s1e s2e)  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (xe Ae) (ae Ae) )
  (=> (and (removeE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (ce s3e ae) (not (ce s3et ae)) ) (= (ce s2et xe) (ite (= xe ae) true (ce s1et xe) )  )  )  ))
(assert (forall ((s3 S) (s3t S) (s1 S) (s1t S) (s2 S) (s2t S) (s3e Se) (s3et Se) (s1e Se) (s1et Se) (s2e Se) (s2et Se) (ae Ae) )
  (=> (and (removeE s3 s3t s3e s3et s1 s1t s1e s1et ae s2 s2t s2e s2et) (or (not (ce s3e ae)) (ce s3et ae) (not (ce s1e ae)) )  ) (= s1et s2et )  )  ))

(declare-fun lookupV (S S Se Se A) Bool)
(assert (forall ((s S) (st S) (se Se) (set Se) (a A) ) (= (lookupV s st se set a) (and (c s a) (not (c st a)) ) ) ))

(declare-fun lookupE (S S Se Se Ae) Bool)
(assert (forall ((s S) (st S) (se Se) (set Se) (ae Ae) ) (= (lookupE s st se set ae) (and (ce se ae) (not (ce set ae))
  (lookupV s st se set (sV ae)) (lookupV s st se set (eV ae)) ) ) ))

;Encoding NON-INTERF-2 begins
;Encoding antecedent
(declare-const e1 E)
(declare-const e2 E)
(declare-const ss1 S)
(declare-const ss1t S)
(declare-const ss2 S)
(declare-const ss2t S)
(declare-const ss1e Se)
(declare-const ss2e Se)
(declare-const ss1et Se)
(declare-const ss2et Se)
(assert (not (= e1 e2)))

(assert (not (= ss1 ss1t)))
(assert (not (= ss1e ss1et)))
(assert (not (= ss2 ss2t)))
(assert (not (= ss2e ss2et)))

(declare-fun apply (E S S Se Se S S Se Se) Bool)
(assert (forall ( (s1 S) (s1e Se) (s1t S) (s1et Se)  (s2 S) (s2e Se) (s2t S) (s2et Se) (e E)) (= (apply e s1 s1t s1e s1et s2 s2t s2e s2et) (
  ite (= (op e) AV) (addV (src e) (srct e) (srce e) (srcet e) s1 s1t s1e s1et (arg e) s2 s2t s2e s2et) (ite (= (op e) RV) (removeV (src e) (srct e) (srce e) (srcet e) s1 s1t s1e s1et (arg e) s2 s2t s2e s2et) (ite (= (op e) AE) (addE (src e) (srct e) (srce e) (srcet e) s1 s1t s1e s1et (arge e) s2 s2t s2e s2et) (removeE (src e) (srct e) (srce e) (srcet e) s1 s1t s1e s1et (arge e) s2 s2t s2e s2et) ) )
  ) ) ))

(declare-fun vis1 (E E) Bool)
(assert  (ite (vis1 e2 e1) (apply e2 ss1 ss1t ss1e ss1et  (src e1) (srct e1) (srce e1) (srcet e1) ) (and (= (src e1) ss1) (= (srct e1) ss1t) (= (srce e1) ss1e) (= (srcet e1) ss1et) ) ))
(assert  (ite (vis1 e1 e2) (apply e1 ss2 ss2t ss2e ss2et  (src e2) (srct e2) (srce e2) (srcet e2)) (and (= (src e2) ss2) (= (srct e2) ss2t) (= (srce e2) ss2e) (= (srcet e2) ss2et) ) ))
(declare-fun eo1 (E E) Bool)
(declare-fun eo2 (E E) Bool)




(declare-const s11 S)
(declare-const s12 S)

(declare-const s11e Se)
(declare-const s12e Se)

(declare-const s11t S)
(declare-const s12t S)

(declare-const s11et Se)
(declare-const s12et Se)

(assert (apply e1 s0 s0t s0e s0et s11 s11t s11e s11et) )
(assert (apply e2 s11 s11t s11e s11et s12 s12t s12e s12et) )
(assert (eo1 e1 e2))
(assert (not (eo1 e2 e1)))

(declare-const s21 S)
(declare-const s22 S)

(declare-const s21e Se)
(declare-const s22e Se)

(declare-const s21t S)
(declare-const s22t S)

(declare-const s21et Se)
(declare-const s22et Se)

(assert (apply e2 s0 s0t s0e s0et s21 s21t s21e s21et) )
(assert (apply e1 s21 s21t s21e s21et s22 s22t s22e s22et) )
(assert (eo2 e2 e1))
(assert (not (eo2 e1 e2)))

(assert (forall ((a A) (ae Ae)) (=> (and (=> (vis1 e1 e2) (not (vis1 e2 e1)))  (=> (vis1 e2 e1) (not (vis1 e1 e2))) (=> (vis1 e1 e2) (eo1 e1 e2)) (=> (vis1 e2 e1) (eo1 e2 e1)) (=> (vis1 e1 e2) (eo2 e1 e2)) (=> (vis1 e2 e1) (eo2 e2 e1)) (=> (eo1 e1 e2) (not (eo1 e2 e1))) (=> (eo1 e2 e1) (not (eo1 e1 e2))) (=> (eo2 e2 e1) (not (eo2 e1 e2))) (=> (eo2 e1 e2) (not (eo2 e2 e1))) ) (and (= (lookupV s12 s12t s12e s12et a) (lookupV s22 s22t s22e s22et a)) (= (lookupE s12 s12t s12e s12et ae) (lookupE s22 s22t s22e s22et ae)) ) )))

;Encoding consequent

(declare-const e3 E)
(declare-const ss3 S)
(declare-const ss3e Se)
(declare-const ss3t S)
(declare-const ss3et Se)
(declare-const e1p E)
(declare-const e2p E)
(assert (= (op e1) (op e1p)))
(assert (= (op e2) (op e2p)))
(assert (= (arg e1) (arg e1p)))
(assert (= (arg e2) (arg e2p)))
(assert (= (arge e1) (arge e1p)))
(assert (= (arge e2) (arge e2p)))
(assert (= (eid e1) (eid e1p)))
(assert (= (eid e2) (eid e2p)))
(assert (not (= e1p e3)))
(assert (not (= e2p e3)))

(assert (not (= (eid e1p) (eid e2p))))
(assert (not (= (eid e1p) (eid e3))))
(assert (not (= (eid e3) (eid e2p))))

(declare-fun vis (E E) Bool)
(assert (= (src e3) ss3))
(assert (= (srce e3) ss3e))
(assert (= (srct e3) ss3t))
(assert (= (srcet e3) ss3et))

(assert (= (vis1 e1 e2) (vis e1p e2p) ))
(assert (= (vis1 e2 e1) (vis e2p e1p) ))
(assert (not (vis e1p e3)))
(assert (not (vis e2p e3)))

(assert (=> (and (not (vis e3 e1p)) (not (vis e2p e1p))) (and (= (src e1p) ss1) (= (srct e1p) ss1t) (= (srce e1p) ss1e) (= (srcet e1p) ss1et)) ))
(assert (=> (and (not (vis e3 e2p)) (not (vis e1p e2p))) (and (= (src e2p) ss2) (= (srct e2p) ss2t) (= (srce e2p) ss2e) (= (srcet e2p) ss2et)) ))

(assert (=> (and (vis e3 e1p) (not (vis e2p e1p)) ) (apply e3 ss1 ss1t ss1e ss1et (src e1p) (srct e1p) (srce e1p) (srcet e1p) )   ) )
(assert (=> (and (not (vis e3 e1p)) (vis e2p e1p)) (apply e2p ss1 ss1t ss1e ss1et (src e1p) (srct e1p) (srce e1p) (srcet e1p))   ) )
(assert (exists ((ns S) (nst S) (nse Se) (nset Se) )(=> (and (vis e3 e1p) (vis e2p e1p)) (and (apply e3 ss1 ss1t ss1e ss1et ns nst nse nset) (apply e2p ns nst nse nset (src e1p) (srct e1p) (srce e1p) (srcet e1p) ) )  ) ))

(assert (=> (and (vis e3 e2p) (not (vis e1p e2p)) ) (apply e3 ss2 ss2t ss2e ss2et (src e2p) (srct e2p) (srce e2p) (srcet e2p))   ) )
(assert (=> (and (not (vis e3 e2p)) (vis e1p e2p)) (apply e1p ss2 ss2t ss2e ss2et (src e2p) (srct e2p) (srce e2p) (srcet e2p))   ) )
(assert (exists ((ns S) (nst S) (nse Se) (nset Se))(=> (and (vis e3 e2p) (vis e1p e2p)) (and (apply e3 ss2 ss2t ss2e ss2et ns nst nse nset) (apply e1p ns nst nse nset (src e2p) (srct e2p) (srce e2p) (srcet e2p)) )  ) ))


(declare-const pe11 E)
(declare-const pe12 E)
(declare-fun eoe1 (E E) Bool)
(declare-const se11 S)
(declare-const se12 S)
(declare-const se21 S)
(declare-const se22 S)
(declare-const se11e Se)
(declare-const se12e Se)
(declare-const se21e Se)
(declare-const se22e Se)
(declare-const se11t S)
(declare-const se12t S)
(declare-const se21t S)
(declare-const se22t S)
(declare-const se11et Se)
(declare-const se12et Se)
(declare-const se21et Se)
(declare-const se22et Se)
(declare-fun next1 (E E) Bool)

(assert (not (= ss3 ss3t)))
(assert (not (= ss3e ss3et)))
(assert (or (= pe11 e1p) (= pe11 e2p)))
(assert (or (= pe12 e1p) (= pe12 e2p)))
(assert (not (= pe11 pe12)))




(assert (apply pe11 s0 s0t s0e s0et se11 se11t se11e se11et) )
(assert (apply pe12 se11 se11t se11e se11et se12 se12t se12e se12et))
(assert (eoe1 pe11 pe12))

(assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe1 e1 e2) (eoe1 e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe1 e1 e2)) ))

(declare-const pe21 E)
(declare-const pe22 E)
(declare-fun next2 (E E) Bool)
(declare-fun eoe2 (E E) Bool)

(assert (or (= pe21 e1p) (= pe21 e2p)))
(assert (or (= pe22 e1p) (= pe22 e2p)))
(assert (not (= pe21 pe22)))



(assert (apply pe21 s0 s0t s0e s0et se21 se21t se21e se21et))
(assert (apply pe22 se21 se21t se21e se21et se22 se22t se22e se22et))
(assert (eoe2 pe21 pe22))

(assert (forall ((e1 E) (e2 E)) (=> (not (= e1 e2)) (xor (eoe2 e1 e2) (eoe2 e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (eo e1 e2) (eoe2 e1 e2)) ))

(declare-const aval A)
(declare-const ae Ae)

(assert  (or (not (= (lookupV se12 se12t se12e se12et aval) (lookupV se22 se22t se22e se22et aval))) (not (= (lookupE se12 se12t se12e se12et ae) (lookupE se22 se22t se22e se22et ae)))  ))

;Consistency Policy-PSI
(assert (forall ((e1 E) (e2 E)) (=> (vis e1 e2) (not (vis e2 e1)) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (arg e1) (arg e2))  ) (or (vis e1 e2) (vis e2 e1) ) )))
(assert (forall ((e1 E) (e2 E)) (=> (and (not (= e1 e2)) (= (arg e1) (arg e2))  (vis e1 e2)) (eo e1 e2) ) ))


(check-sat)
(get-model)
